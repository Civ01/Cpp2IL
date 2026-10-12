using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Float code reads 16 byte constants out of .rdata: masks for abs (andps with 0x7FFFFFFF lanes) and negation (xorps
/// with 0x80000000 lanes), and splatted vectors (1,1,1,1). This turns the mask operations into Math.Abs/negation and
/// a constant vector used as a scalar into its first lane, rather than leaving unexplained memory loads. Runs in SSA
/// form, before types are resolved.
/// </summary>
public static class VectorConstantRecovery
{
    private enum ConstantKind { None, AbsSingle, AbsDouble, SignSingle, SignDouble, Floats }

    public static void Run(MethodAnalysisContext method)
    {
        var app = method.AppContext;
        if (app.Binary.PointerSizeBytes != 8 || app.InstructionSet is not InstructionSets.X86InstructionSet)
            return;

        var math = app.GetAssemblyByName("mscorlib")?.GetTypeByFullName("System.Math");
        var absSingle = math?.Methods.FirstOrDefault(m => m.Name == "Abs" && m.Parameters is [{ ParameterType.FullName: "System.Single" }]);
        var absDouble = math?.Methods.FirstOrDefault(m => m.Name == "Abs" && m.Parameters is [{ ParameterType.FullName: "System.Double" }]);

        var constants = new Dictionary<LocalVariable, (ConstantKind Kind, float FirstLane)>();
        var graph = method.ControlFlowGraph!;

        foreach (var instruction in graph.Instructions)
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable destination, MemoryOperand { Base: null, Index: null, Size: 16 } constant] }
                && Classify(app, (ulong)constant.Addend) is { Kind: not ConstantKind.None } classified)
                constants[destination] = classified;
            else if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable literalDestination, FloatLiteral or DoubleLiteral] } literalMove
                     && ConstantOfLiteral(literalMove.Operands[1]) is { } literalKind)
                constants[literalDestination] = literalKind;
        }

        (ConstantKind Kind, float FirstLane)? ConstantOf(IOperand operand) => operand switch
        {
            LocalVariable local when constants.TryGetValue(local, out var known) => known,
            // a mask whose low lane was already split off into a literal
            FloatLiteral { Value: var single } when BitConverter.SingleToInt32Bits(single) == unchecked((int)0x80000000) => (ConstantKind.SignSingle, 0),
            FloatLiteral { Value: var single } when BitConverter.SingleToInt32Bits(single) == 0x7FFFFFFF => (ConstantKind.AbsSingle, 0),
            DoubleLiteral { Value: var @double } when BitConverter.DoubleToInt64Bits(@double) == long.MinValue => (ConstantKind.SignDouble, 0),
            DoubleLiteral { Value: var @double } when BitConverter.DoubleToInt64Bits(@double) == long.MaxValue => (ConstantKind.AbsDouble, 0),
            MemoryOperand { Base: null, Index: null, Size: 16 } memory when Classify(app, (ulong)memory.Addend) is { Kind: not ConstantKind.None } inline => inline,
            _ => null
        };

        foreach (var instruction in graph.Instructions)
        {
            switch (instruction.OpCode)
            {
                case OpCode.And when instruction.Operands.Count == 3:
                {
                    var (mask, value) = ConstantOf(instruction.Operands[2]) is { } right ? (right, instruction.Operands[1])
                        : ConstantOf(instruction.Operands[1]) is { } left ? (left, instruction.Operands[2]) : default;

                    var abs = mask.Kind switch
                    {
                        ConstantKind.AbsSingle => absSingle,
                        ConstantKind.AbsDouble => absDouble,
                        _ => null
                    };

                    if (abs == null || value == null)
                        break;

                    instruction.OpCode = OpCode.Call;
                    instruction.SetOperands(abs, instruction.Operands[0], value);
                    break;
                }
                case OpCode.Xor when instruction.Operands.Count == 3:
                {
                    var (mask, value) = ConstantOf(instruction.Operands[2]) is { } right ? (right, instruction.Operands[1])
                        : ConstantOf(instruction.Operands[1]) is { } left ? (left, instruction.Operands[2]) : default;

                    if (mask.Kind is not (ConstantKind.SignSingle or ConstantKind.SignDouble) || value == null)
                        break;

                    instruction.OpCode = OpCode.Negate;
                    instruction.SetOperands(instruction.Operands[0], value);
                    break;
                }
            }
        }

        // What's left of the plain vector constants is used as a scalar float, i.e. its first lane - unless it's stored
        // whole somewhere (struct initialisation, which StructCopyRecovery expands field by field)
        var storedWhole = new HashSet<LocalVariable>();
        foreach (var instruction in graph.Instructions)
            if (instruction is { OpCode: OpCode.Move, Operands: [MemoryOperand { Size: > 4 } or StackOffset, LocalVariable stored] })
                storedWhole.Add(stored);

        foreach (var instruction in graph.Instructions)
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable destination, MemoryOperand] }
                && !storedWhole.Contains(destination)
                && constants.TryGetValue(destination, out var known) && known.Kind == ConstantKind.Floats)
                instruction.SetOperand(1, new FloatLiteral(known.FirstLane));
        }
    }

    private static (ConstantKind Kind, float FirstLane)? ConstantOfLiteral(IOperand literal) => literal switch
    {
        FloatLiteral { Value: var single } when BitConverter.SingleToInt32Bits(single) == unchecked((int)0x80000000) => (ConstantKind.SignSingle, 0),
        FloatLiteral { Value: var single } when BitConverter.SingleToInt32Bits(single) == 0x7FFFFFFF => (ConstantKind.AbsSingle, 0),
        DoubleLiteral { Value: var @double } when BitConverter.DoubleToInt64Bits(@double) == long.MinValue => (ConstantKind.SignDouble, 0),
        DoubleLiteral { Value: var @double } when BitConverter.DoubleToInt64Bits(@double) == long.MaxValue => (ConstantKind.AbsDouble, 0),
        _ => null
    };

    private static (ConstantKind Kind, float FirstLane) Classify(ApplicationAnalysisContext app, ulong address)
    {
        var binary = app.Binary;
        if (!binary.TryMapVirtualAddressToRaw(address, out var raw))
            return (ConstantKind.None, 0);

        var content = binary.GetRawBinaryContent();
        if (raw < 0 || raw + 16 > content.Length)
            return (ConstantKind.None, 0);

        var bytes = content.Slice((int)raw, 16).ToArray();
        var lanes = Enumerable.Range(0, 4).Select(i => BitConverter.ToUInt32(bytes, i * 4)).ToArray();
        var quads = new[] { BitConverter.ToUInt64(bytes, 0), BitConverter.ToUInt64(bytes, 8) };

        if (lanes.All(l => l == 0x7FFFFFFF))
            return (ConstantKind.AbsSingle, 0);
        if (quads.All(q => q == 0x7FFFFFFFFFFFFFFF))
            return (ConstantKind.AbsDouble, 0);
        if (lanes.All(l => l == 0x80000000))
            return (ConstantKind.SignSingle, 0);
        if (quads.All(q => q == 0x8000000000000000))
            return (ConstantKind.SignDouble, 0);

        // Only call it floats if every lane looks like a sensible float (not a pointer or an int pattern)
        var floats = Enumerable.Range(0, 4).Select(i => BitConverter.ToSingle(bytes, i * 4)).ToArray();
        if (floats.All(f => f == 0 || !float.IsNaN(f) && !float.IsInfinity(f) && Math.Abs(f) is > 1e-10f and < 1e10f) && lanes.Any(l => l != 0))
            return (ConstantKind.Floats, floats[0]);

        return (ConstantKind.None, 0);
    }
}
