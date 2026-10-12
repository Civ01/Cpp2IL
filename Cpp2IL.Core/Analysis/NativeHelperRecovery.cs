using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Lowers calls to the native helpers <see cref="NativeHelpers"/> recognises into what they mean:
/// calls to empty functions and stack probes disappear, memset/memcpy become sized moves (so struct
/// recovery can type them), IsInst becomes <see cref="OpCode.IsInst"/>, and the castclass failure
/// path becomes a throw of InvalidCastException.
/// </summary>
public static class NativeHelperRecovery
{
    /// <summary>
    /// Runs on ISIL registers with absolute stack offsets (between StackAnalyzer.CorrectOffsets and
    /// InlineMemcpyRecovery), so the stack slots memset/memcpy work on are known.
    /// </summary>
    public static void RunEarly(MethodAnalysisContext method, ISILControlFlowGraph graph)
    {
        var app = method.AppContext;

        foreach (var block in graph.Blocks)
        {
            if (block.Instructions.Count == 0)
                continue;

            var call = block.Instructions[^1];
            if (!call.IsCall || call.Operands.Count == 0 || call.Operands[0] is not Immediate target)
                continue;

            var kind = NativeHelpers.Classify(app, target.UnsignedValue);
            if (kind == NativeHelperKind.Unknown)
                continue;

            var callIndex = block.Instructions.Count - 1;

            switch (kind)
            {
                case NativeHelperKind.Empty:
                case NativeHelperKind.StackProbe:
                    // Changes nothing (an empty function even leaves rax as it was)
                    call.OpCode = OpCode.Nop;
                    call.SetOperands();
                    block.BlockType = BlockType.Fall;
                    break;

                case NativeHelperKind.Memset:
                {
                    if (RegisterConstant(block, callIndex, "rdx") is not 0
                        || RegisterConstant(block, callIndex, "r8") is not { } length
                        || length is <= 0 or >= 0x10000)
                        break;

                    // only zeroing a stack slot is understood well enough to be worth it
                    if (AddressedSlot(block, callIndex, "rcx") is not { } slot)
                        break;

                    call.OpCode = OpCode.Move;
                    call.SetOperands(new StackOffset(slot, (int)length), new Immediate(0));
                    block.Instructions.Add(new Instruction(call.Index, OpCode.Move, new Register(null, "rax"), new AddressOf(new StackOffset(slot)))); // memset hands back its destination
                    block.BlockType = BlockType.Fall;
                    break;
                }

                case NativeHelperKind.Memcpy:
                {
                    if (RegisterConstant(block, callIndex, "r8") is not { } length || length is <= 0 or >= 0x10000)
                        break;

                    var destination = SizedTarget(block, callIndex, "rcx", (int)length);
                    var source = SizedTarget(block, callIndex, "rdx", (int)length);

                    call.OpCode = OpCode.Move;
                    call.SetOperands(destination, source);
                    block.Instructions.Add(new Instruction(call.Index, OpCode.Move, new Register(null, "rax"), new Register(null, "rcx")));
                    block.BlockType = BlockType.Fall;
                    break;
                }

                case NativeHelperKind.IsInst:
                    if (call.OpCode != OpCode.Call || call.Operands.Count < 4)
                        break;

                    // Unmanaged calls carry every argument register: [target, rax, rcx (object), rdx (klass), ...]
                    call.OpCode = OpCode.IsInst;
                    call.SetOperands(call.Operands[1], call.Operands[3], call.Operands[2]);
                    block.BlockType = BlockType.Fall;
                    break;

                case NativeHelperKind.RaiseInvalidCast:
                    if (app.LibCpp2IlContext.ReflectionCache.GetType("InvalidCastException") is { } invalidCast
                        && app.ResolveContextForType(invalidCast) is { } exceptionType)
                    {
                        call.OpCode = OpCode.Throw;
                        call.SetOperands(exceptionType);
                    }

                    break;
            }
        }
    }

    /// <summary>
    /// Once types are known, names the class an IsInst checks against directly, so the class pointer load feeding
    /// it can die.
    /// </summary>
    public static void RunLate(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.IsInst)
                continue;

            if (instruction.Operands[1] is LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } checkedType } })
                instruction.SetOperand(1, checkedType);
        }
    }

    // What the register holds, as a sized location: the stack slot whose address it holds, or what it points at
    private static IOperand SizedTarget(Block block, int beforeIndex, string register, int size)
    {
        if (AddressedSlot(block, beforeIndex, register) is { } slot)
            return new StackOffset(slot, size);

        return new MemoryOperand(new Register(null, register), size: size);
    }

    private static long? RegisterConstant(Block block, int beforeIndex, string registerName)
    {
        for (var i = beforeIndex - 1; i >= 0; i--)
        {
            var instruction = block.Instructions[i];
            if (instruction.Destination is not Register written || written.Name != registerName)
                continue;

            return instruction is { OpCode: OpCode.Move, Operands: [_, Immediate value] } ? value.Value : null;
        }

        return null;
    }

    private static int? AddressedSlot(Block block, int beforeIndex, string registerName)
    {
        for (var i = beforeIndex - 1; i >= 0; i--)
        {
            var instruction = block.Instructions[i];
            if (instruction.Destination is not Register written || written.Name != registerName)
                continue;

            return instruction is { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: StackOffset slot }] } ? slot.Offset : null;
        }

        return null;
    }
}
