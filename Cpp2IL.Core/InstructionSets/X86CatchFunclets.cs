using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Iced.Intel;
using LibCpp2IL.PE;

namespace Cpp2IL.Core.InstructionSets;

/// <summary>
/// The catch blocks of a method compiled by MSVC live in separate functions, catch funclets, that the C++ runtime calls with
/// the method's frame when one of its try blocks throws. IL2CPP catches every managed exception as an
/// <c>Il2CppExceptionWrapper&amp;</c>: its funclet tests the exception's type, stores it into one of the method's locals and
/// returns to a continuation in the method, where the C# catch body is, or rethrows when the type doesn't match.
///
/// Each funclet is lifted onto the end of the method, as if it were part of it: the frame register it is given becomes the
/// method's own stack pointer, reading the exception out of the wrapper becomes <see cref="ISIL.OpCode.CatchException"/>,
/// its return a jump to the continuation, and its rethrow a <see cref="ISIL.OpCode.Throw"/>. The method's analysis then
/// links the calls in the try block to the funclet's entry.
/// </summary>
public partial class X86InstructionSet
{
    // registers the funclet's own saved ones are renamed to, so that the method's values in them are untouched after it
    private static readonly Register[] SpareRegisters = [Register.R10, Register.R11, Register.R9, Register.R8];

    private static readonly string[] VolatileRegisters = ["rax", "rcx", "rdx", "r8", "r9", "r10", "r11", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5"];

    private void AppendCatchFunclets(MethodAnalysisContext context, List<ISIL.Instruction> instructions, List<ulong> addresses)
    {
        if (context.AppContext.Binary is not PE pe)
            return;

        var info = pe.GetCxxExceptionInfo(context.UnderlyingPointer);
        if (info is not { TryBlocks.Count: > 0, FrameRegister: 0 } || info.FunctionStart != context.UnderlyingPointer)
            return;

        // the return added at the end has no address
        while (addresses.Count < instructions.Count)
            addresses.Add(0);

        var rethrow = NativeThrow(context.AppContext);
        var handlers = new List<CatchHandler>();
        var known = addresses.ToHashSet();

        foreach (var tryBlock in info.TryBlocks)
        {
            foreach (var handler in tryBlock.Handlers)
            {
                if (handler is not { Continuations: [var continuation], FuncletEnd: > 0, CatchObjectOffset: { } catchObject }
                    || !known.Contains(continuation) || known.Contains(handler.FuncletStart))
                    continue;

                var body = Decode(context, handler.FuncletStart, handler.FuncletEnd);
                if (body == null || Translate(body, catchObject, rethrow, continuation) is not { } steps)
                    continue;

                var first = instructions.Count;
                foreach (var step in steps)
                {
                    switch (step.Kind)
                    {
                        case StepKind.Convert:
                            ConvertInstructionStatement(step.Source, instructions, addresses, context);
                            break;
                        case StepKind.Anchor:
                            Append(step.Source.IP, ISIL.OpCode.Nop);
                            break;
                        case StepKind.Entry:
                            // the volatile registers hold nothing of the method's on the way in: without these, what the
                            // funclet's calls appear to read from them would be merged from every call in the try block
                            foreach (var register in VolatileRegisters)
                                Append(step.Source.IP, ISIL.OpCode.Move, new ISIL.Register(null, register), Imm(0));
                            break;
                        case StepKind.Jump:
                            Append(step.Source.IP, ISIL.OpCode.Jump, Imm(step.Target));
                            break;
                        case StepKind.CatchException:
                            Append(step.Source.IP, ISIL.OpCode.CatchException, new ISIL.Register(null, X86Utils.GetRegisterName(step.Register)));
                            break;
                        case StepKind.Rethrow:
                            // the wrapper thrown again is a copy of the caught one, made in the slot the throw is given
                            ConvertInstructionStatement(Instruction.Create(Code.Mov_r64_rm64, Register.RCX, new MemoryOperand(Register.RSP, step.Slot)), instructions, addresses, context);
                            addresses[^1] = instructions[^1].Address = step.Source.IP;
                            Append(step.Source.IP, ISIL.OpCode.Throw, new ISIL.Register(null, "rcx"));
                            break;
                    }
                }

                if (instructions.Count == first)
                    continue;

                foreach (var address in addresses.Skip(first))
                    known.Add(address);

                // a C# catch tests the exception's type and rethrows what it doesn't take; a finally doesn't, it only saves
                // the exception (sometimes through a little helper) for the rethrow after the finally code
                var isFinally = steps.All(s => s.Kind != StepKind.Rethrow);
                handlers.Add(new CatchHandler(tryBlock, handler, instructions[first], instructions.Skip(first).ToHashSet(), isFinally));
            }
        }

        if (handlers.Count > 0)
        {
            context.ExceptionInfo = info;
            context.CatchHandlers = handlers;
        }

        void Append(ulong address, ISIL.OpCode opCode, params List<ISIL.IOperand> operands)
        {
            addresses.Add(address);
            instructions.Add(new ISIL.Instruction(instructions.Count, opCode, operands) { Address = address });
        }
    }

    private static ulong NativeThrow(ApplicationAnalysisContext app)
    {
        var raise = app.GetOrCreateKeyFunctionAddresses().il2cpp_vm_exception_raise;
        return raise == 0 ? 0 : app.InstructionSet.InspectPotentialThrowHelper(app, raise).CallTargets.LastOrDefault();
    }

    private static List<Instruction>? Decode(MethodAnalysisContext context, ulong start, ulong end)
    {
        var binary = context.AppContext.Binary;
        if (end <= start || end - start > 4096 || !binary.TryMapVirtualAddressToRaw(start, out var raw))
            return null;

        var bytes = binary.GetRawBinaryContent();
        if (raw + (long)(end - start) > bytes.Length)
            return null;

        var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes.Slice((int)raw, (int)(end - start)).ToArray()), start);
        var result = new List<Instruction>();
        while (decoder.IP < end)
        {
            var instruction = decoder.Decode();
            if (instruction.IsInvalid)
                return null;
            result.Add(instruction);
        }

        return result;
    }

    private enum StepKind
    {
        Convert,
        Anchor,
        Entry,
        Jump,
        CatchException,
        Rethrow,
    }

    private readonly record struct Step(StepKind Kind, Instruction Source, ulong Target = 0, Register Register = Register.None, long Slot = 0);

    /// <summary>
    /// The funclet as instructions on the method's frame, or null if it does anything that can't be expressed that way.
    /// </summary>
    private static List<Step>? Translate(List<Instruction> body, int catchObject, ulong rethrow, ulong continuation)
    {
        var steps = new List<Step>();

        // the prolog: home the arguments, save registers, allocate, and take the method's frame (passed in rdx)
        var saved = new List<Register>();
        var frame = Register.None;
        var index = 0;
        for (; index < body.Count && frame == Register.None; index++)
        {
            var instruction = body[index];
            switch (instruction)
            {
                case { Mnemonic: Mnemonic.Mov, Op0Kind: OpKind.Memory, MemoryBase: Register.RSP, Op1Kind: OpKind.Register }:
                    break;
                case { Mnemonic: Mnemonic.Push, Op0Kind: OpKind.Register }:
                    saved.Add(instruction.Op0Register);
                    break;
                case { Mnemonic: Mnemonic.Sub, Op0Register: Register.RSP }:
                    break;
                case { Mnemonic: Mnemonic.Mov, Op0Kind: OpKind.Register, Op1Kind: OpKind.Register, Op1Register: Register.RDX } when saved.Contains(instruction.Op0Register):
                    frame = instruction.Op0Register;
                    break;
                default:
                    return null;
            }

            steps.Add(new(StepKind.Anchor, instruction));
        }

        if (frame == Register.None)
            return null;

        steps.Add(new(StepKind.Entry, body[index - 1]));

        // what the funclet keeps in the registers it saved goes in spare volatile ones instead
        var used = body.Skip(index).SelectMany(Registers).Select(r => r.GetFullRegister()).ToHashSet();
        var renames = new Dictionary<Register, Register>();
        var spares = SpareRegisters.Where(r => !used.Contains(r)).ToList();
        foreach (var register in saved.Where(r => r != frame && used.Contains(r)))
        {
            if (spares.Count == 0)
                return null;
            renames[register] = spares[0];
            spares.RemoveAt(0);
        }

        var wrappers = new HashSet<Register>(); // registers pointing at the caught Il2CppExceptionWrapper
        Instruction? previous = null;
        for (; index < body.Count; index++)
        {
            var instruction = body[index];
            var last = previous;
            previous = instruction;

            switch (instruction)
            {
                // the epilog
                case { Mnemonic: Mnemonic.Add, Op0Kind: OpKind.Register, Op0Register: Register.RSP }:
                case { Mnemonic: Mnemonic.Pop, Op0Kind: OpKind.Register } when saved.Contains(instruction.Op0Register):
                case { Mnemonic: Mnemonic.Nop or Mnemonic.Int3 }:
                    steps.Add(new(StepKind.Anchor, instruction));
                    continue;
                case { Mnemonic: Mnemonic.Ret }:
                    steps.Add(new(StepKind.Jump, instruction, continuation));
                    continue;

                // mov reg, [frame + catch object]: a reference to the wrapper
                case { Mnemonic: Mnemonic.Mov, Op0Kind: OpKind.Register, Op1Kind: OpKind.Memory, MemoryIndex: Register.None } when instruction.MemoryBase == frame
                                                                                                                                 && (long)instruction.MemoryDisplacement64 == catchObject
                                                                                                                                 && instruction.Op0Register.GetSize() == 8:
                    wrappers.Add(instruction.Op0Register);
                    steps.Add(new(StepKind.Anchor, instruction));
                    continue;

                // mov reg, [wrapper]: the exception
                case { Mnemonic: Mnemonic.Mov, Op0Kind: OpKind.Register, Op1Kind: OpKind.Memory, MemoryIndex: Register.None, MemoryDisplacement64: 0 } when wrappers.Contains(instruction.MemoryBase)
                                                                                                                                                         && instruction.Op0Register.GetSize() == 8:
                    wrappers.Remove(instruction.Op0Register);
                    steps.Add(new(StepKind.CatchException, instruction, Register: Rename(instruction.Op0Register, renames)));
                    continue;

                // lea rcx, [frame + slot] / call _CxxThrowException: throws the exception put in the slot
                case { Mnemonic: Mnemonic.Call, Op0Kind: OpKind.NearBranch64 } when rethrow != 0 && instruction.NearBranchTarget == rethrow
                                                                                     && last is { Mnemonic: Mnemonic.Lea, Op0Register: Register.RCX, MemoryIndex: Register.None } lea
                                                                                     && lea.MemoryBase == frame:
                    steps.Add(new(StepKind.Rethrow, instruction, Slot: (long)lea.MemoryDisplacement64));
                    continue;

                // the funclet's own jumps stay within it
                case { Mnemonic: Mnemonic.Jmp, Op0Kind: OpKind.NearBranch64 }:
                    if (instruction.NearBranchTarget < body[0].IP || instruction.NearBranchTarget >= body[^1].NextIP)
                        return null;
                    steps.Add(new(StepKind.Jump, instruction, instruction.NearBranchTarget));
                    continue;
            }

            if (instruction.FlowControl is FlowControl.ConditionalBranch && (instruction.NearBranchTarget < body[0].IP || instruction.NearBranchTarget >= body[^1].NextIP))
                return null;

            if (instruction.FlowControl is FlowControl.IndirectBranch or FlowControl.IndirectCall or FlowControl.Return or FlowControl.Interrupt or FlowControl.Exception or FlowControl.UnconditionalBranch)
                return null;

            // anything else may only reach the method's frame through the frame register, and not use the stack itself
            var rewritten = instruction;
            for (var i = 0; i < instruction.OpCount; i++)
            {
                if (instruction.GetOpKind(i) != OpKind.Register)
                    continue;

                var register = instruction.GetOpRegister(i);
                // (writing over the register that held the wrapper, like setting the return value, isn't using it)
                var overwritten = i == 0 && instruction.Mnemonic is Mnemonic.Mov or Mnemonic.Lea or Mnemonic.Movzx or Mnemonic.Movsx or Mnemonic.Movsxd
                                  && register.GetSize() >= 4;
                if (register.GetFullRegister() is Register.RSP || register.GetFullRegister() == frame || wrappers.Contains(register.GetFullRegister()) && !overwritten)
                    return null;

                rewritten.SetOpRegister(i, Rename(register, renames));
            }

            if (instruction.Op0Kind == OpKind.Register)
                wrappers.Remove(instruction.Op0Register.GetFullRegister());

            if (HasMemoryOperand(instruction))
            {
                if (instruction.MemoryBase == Register.RSP || instruction.MemoryIndex is Register.RSP || instruction.MemoryIndex == frame || wrappers.Contains(instruction.MemoryBase) || wrappers.Contains(instruction.MemoryIndex))
                    return null;

                rewritten.MemoryBase = instruction.MemoryBase == frame ? Register.RSP : Rename(instruction.MemoryBase, renames);
                rewritten.MemoryIndex = Rename(instruction.MemoryIndex, renames);
            }

            if (rewritten.Op0Kind == OpKind.Register && rewritten.Op0Register == Register.None)
                return null; // a high byte register that can't be renamed

            steps.Add(new(StepKind.Convert, rewritten));
        }

        return steps.Any(s => s.Kind == StepKind.CatchException) ? steps : null;
    }

    private static bool HasMemoryOperand(Instruction instruction)
    {
        for (var i = 0; i < instruction.OpCount; i++)
            if (instruction.GetOpKind(i) == OpKind.Memory)
                return true;
        return false;
    }

    private static IEnumerable<Register> Registers(Instruction instruction)
    {
        for (var i = 0; i < instruction.OpCount; i++)
        {
            if (instruction.GetOpKind(i) == OpKind.Register)
                yield return instruction.GetOpRegister(i);
            else if (instruction.GetOpKind(i) == OpKind.Memory)
            {
                if (instruction.MemoryBase != Register.None)
                    yield return instruction.MemoryBase;
                if (instruction.MemoryIndex != Register.None)
                    yield return instruction.MemoryIndex;
            }
        }
    }

    private static Register Rename(Register register, Dictionary<Register, Register> renames)
    {
        if (register == Register.None || !renames.TryGetValue(register.GetFullRegister(), out var replacement))
            return register;

        var number = replacement - Register.RAX;
        return register.GetSize() switch
        {
            8 => replacement,
            4 => Register.EAX + number,
            2 => Register.AX + number,
            1 when register is not (Register.AH or Register.BH or Register.CH or Register.DH) => Register.R8L + (number - 8),
            _ => Register.None,
        };
    }
}

/// <summary>
/// A catch funclet lifted onto the end of a method: its entry, every instruction it became, and whether it is the catch-all
/// IL2CPP turns a finally into (saving the exception for the finally code to rethrow) rather than a C# catch.
/// </summary>
public sealed record CatchHandler(CxxTryBlock TryBlock, CxxCatchHandler Handler, ISIL.Instruction Entry, HashSet<ISIL.Instruction> Instructions, bool IsFinally);
