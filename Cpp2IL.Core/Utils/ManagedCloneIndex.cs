using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Cpp2IL.Core.Model.Contexts;
using Iced.Intel;

namespace Cpp2IL.Core.Utils;

/// <summary>
/// Finds which managed method an unregistered native function really is, for two common cases on x64:
/// <list type="bullet">
/// <item>Out-of-line copies of methods il2cpp marks for inlining (Mathf.Approximately, Vector3 operators, ...).
/// MSVC emits these as private functions with code identical to the registered method body, so they're matched
/// by their normalized machine code (absolute addresses for anything outside the function).</item>
/// <item>The native function a managed method is nothing but a jmp to (Math.Sin is <c>jmp sin</c>), where code
/// that calls the native function directly has inlined the managed one.</item>
/// </list>
/// </summary>
public class ManagedCloneIndex
{
    private const int MaxInstructions = 96;

    private readonly ApplicationAnalysisContext _app;
    private readonly Dictionary<string, List<MethodAnalysisContext>> _bySignature = new();
    private readonly Dictionary<ulong, List<MethodAnalysisContext>> _byThunkTarget = new();

    private ManagedCloneIndex(ApplicationAnalysisContext app)
    {
        _app = app;

        foreach (var (address, methods) in app.MethodsByAddress)
        {
            if (address == 0)
                continue;

            List<Instruction> body;
            try
            {
                body = Decode(address);
            }
            catch
            {
                continue;
            }

            if (body.Count == 0)
                continue;

            // A method that's just a jump elsewhere
            if (body[0] is { Mnemonic: Mnemonic.Jmp, Op0Kind: OpKind.NearBranch64 } jump && !app.MethodsByAddress.ContainsKey(jump.NearBranchTarget))
            {
                if (!_byThunkTarget.TryGetValue(jump.NearBranchTarget, out var thunkList))
                    _byThunkTarget[jump.NearBranchTarget] = thunkList = [];
                thunkList.AddRange(methods);
            }

            if (body.Count < 4 || body.Count >= MaxInstructions)
                continue; // tiny bodies are too generic to identify anything by; big ones don't get cloned

            var signature = Signature(body, address);
            if (!_bySignature.TryGetValue(signature, out var list))
                _bySignature[signature] = list = [];
            list.AddRange(methods);
        }
    }

    public static ManagedCloneIndex For(ApplicationAnalysisContext app)
    {
        if (app.CloneIndex != null)
            return app.CloneIndex;

        lock (app)
            return app.CloneIndex ??= new ManagedCloneIndex(app);
    }

    /// <summary>
    /// The managed method(s) the native function at the address stands for, if it's recognisably one.
    /// </summary>
    public List<MethodAnalysisContext>? Lookup(ulong address)
    {
        if (_byThunkTarget.TryGetValue(address, out var thunked))
            return thunked;

        List<Instruction> body;
        try
        {
            body = Decode(address);
        }
        catch
        {
            return null;
        }

        if (body.Count < 4 || body.Count >= MaxInstructions)
            return null;

        return _bySignature.TryGetValue(Signature(body, address), out var clones) ? clones : null;
    }

    // Decodes a function linearly up to the int3 padding after it (or the next known function)
    private List<Instruction> Decode(ulong address)
    {
        var binary = _app.Binary;
        var raw = binary.MapVirtualAddressToRaw(address);
        var content = binary.GetRawBinaryContent();

        if (raw <= 0 || raw >= content.Length)
            return [];

        var next = _app.GetAddressOfNextFunctionStart(address);
        var maxLength = (int)Math.Min(Math.Min(content.Length - raw, 4096), next > address ? (long)(next - address) : 4096);
        var decoder = Iced.Intel.Decoder.Create(64, new ByteArrayCodeReader(content.Slice((int)raw, maxLength).ToArray()), address);

        var result = new List<Instruction>();
        while (decoder.IP < address + (ulong)maxLength && result.Count <= MaxInstructions)
        {
            var instruction = decoder.Decode();
            if (instruction.IsInvalid || instruction.Code == Code.Int3)
                break;

            result.Add(instruction);
        }

        return result;
    }

    private static string Signature(List<Instruction> body, ulong start)
    {
        var end = body[^1].NextIP;
        var sb = new StringBuilder();

        foreach (var instruction in body)
        {
            sb.Append((int)instruction.Code).Append('(');

            for (var i = 0; i < instruction.OpCount; i++)
            {
                switch (instruction.GetOpKind(i))
                {
                    case OpKind.Register:
                        sb.Append('r').Append((int)instruction.GetOpRegister(i));
                        break;
                    case OpKind.NearBranch16 or OpKind.NearBranch32 or OpKind.NearBranch64:
                        var target = instruction.NearBranchTarget;
                        if (target >= start && target < end)
                            sb.Append('L').Append(target - start);
                        else
                            sb.Append('@').Append(target);
                        break;
                    case OpKind.Memory:
                        // Each copy of an inlinable method checks/sets its own per-translation-unit "metadata initialised"
                        // byte flag (cmp byte ptr [flag],0 / mov byte ptr [flag],1), so those addresses don't count
                        if (instruction.IsIPRelativeMemoryOperand && instruction.MemorySize is MemorySize.UInt8 or MemorySize.Int8
                            && instruction.Mnemonic is Mnemonic.Cmp or Mnemonic.Mov && instruction.OpCount == 2 && instruction.Op1Kind == OpKind.Immediate8)
                            sb.Append("[flag]");
                        else if (instruction.IsIPRelativeMemoryOperand)
                            sb.Append("[@").Append(instruction.IPRelativeMemoryAddress).Append(']');
                        else
                            sb.Append('[').Append((int)instruction.MemoryBase).Append(',').Append((int)instruction.MemoryIndex).Append(',')
                                .Append(instruction.MemoryIndexScale).Append(',').Append(instruction.MemoryDisplacement64).Append(']');
                        break;
                    default:
                        if (instruction.GetOpKind(i) is OpKind.Immediate8 or OpKind.Immediate16 or OpKind.Immediate32 or OpKind.Immediate64
                            or OpKind.Immediate8to16 or OpKind.Immediate8to32 or OpKind.Immediate8to64 or OpKind.Immediate32to64)
                            sb.Append('#').Append(instruction.GetImmediate(i));
                        else
                            sb.Append('?').Append((int)instruction.GetOpKind(i));
                        break;
                }

                sb.Append(',');
            }

            sb.Append(')');
        }

        return sb.ToString();
    }
}
