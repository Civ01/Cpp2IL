using System.Collections.Generic;
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

                // the stack of exceptions being handled: a catch or finally handles one at a time, so its only element (an
                // array of one at the start of the slot, as the inlined pushes and reads of it see it) is the exception
                case NativeHelperKind.ExceptionStackPush or NativeHelperKind.ExceptionStackPop or NativeHelperKind.ExceptionStackTop:
                {
                    if (AddressedSlot(block, callIndex, "rcx") is not { } stack)
                        break;

                    var element = new StackOffset(stack, 8);
                    if (kind == NativeHelperKind.ExceptionStackPush)
                        call.SetOperands(element, new Register(null, "rdx"));
                    else
                        call.SetOperands(new Register(null, "rax"), element);
                    call.OpCode = OpCode.Move;
                    block.BlockType = BlockType.Fall;
                    break;
                }

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

    /// <summary>
    /// Class/rgctx initialisation calls the init guards didn't account for hand back the class they're given: say so.
    /// </summary>
    public static void LowerIdentityHelpers(MethodAnalysisContext method)
    {
        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable defined)
                definitions[defined] = instruction;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction is { OpCode: OpCode.Call, Operands: [Immediate fieldHelper, LocalVariable address, LocalVariable owner, LocalVariable fieldInfo, ..] }
                && NativeHelpers.Classify(method.AppContext, fieldHelper.UnsignedValue) == NativeHelperKind.FieldAddress
                && FieldFromInfo(owner, fieldInfo, definitions) is { } field)
            {
                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(address, new AddressOf(new FieldReference(field, owner, 0)));
                address.Type = new ByRefTypeAnalysisContext(field.FieldType);
                continue;
            }

            if (instruction is not { OpCode: OpCode.Call or OpCode.CallVoid, Operands: [Immediate target, ..] }
                || NativeHelpers.Classify(method.AppContext, target.UnsignedValue) != NativeHelperKind.ReturnsFirstArgument)
                continue;

            if (instruction.OpCode == OpCode.Call && instruction.Operands.Count > 2)
                instruction.SetOperands(instruction.Operands[1], instruction.Operands[2]);
            else
            {
                instruction.SetOperands();
                instruction.OpCode = OpCode.Nop;
                continue;
            }

            instruction.OpCode = OpCode.Move;
        }
    }

    // FieldInfo* as klass->fields + n * sizeof(FieldInfo): the nth field of the object's type
    private static FieldAnalysisContext? FieldFromInfo(LocalVariable owner, LocalVariable fieldInfo, Dictionary<LocalVariable, Instruction> definitions)
    {
        const int fieldInfoSize = 0x20;
        const long fieldsOffset = 0x80;
        var index = 0L;
        var current = fieldInfo;

        for (var depth = 0; depth < 6; depth++)
        {
            if (!definitions.TryGetValue(current, out var definition))
                return null;

            switch (definition)
            {
                case { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] }:
                    current = copied;
                    continue;
                case { OpCode: OpCode.Add, Operands: [_, LocalVariable added, Immediate { Value: var by }] } when by % fieldInfoSize == 0:
                    index += by / fieldInfoSize;
                    current = added;
                    continue;
                case { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Addend: fieldsOffset }] }:
                    var ownerType = owner.Type is GenericInstanceTypeAnalysisContext generic ? generic.GenericType : owner.Type;
                    if (ownerType == null || index >= ownerType.Fields.Count)
                        return null;
                    var field = ownerType.Fields[(int)index];
                    return owner.Type is GenericInstanceTypeAnalysisContext instance ? new ConcreteGenericFieldAnalysisContext(field, instance) : field;
                default:
                    return null;
            }
        }

        return null;
    }
}
