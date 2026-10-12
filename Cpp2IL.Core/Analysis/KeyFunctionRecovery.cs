using Cpp2IL.Core.Graphs;
using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Maps calls to KeyFunctionAddresses to their underlying IL opcodes. E.g. il2cpp_codegen_object_new => newobj.
/// Eventually will include box/unbox/throw/etc
/// </summary>
public static class KeyFunctionRecovery
{
    //All of these have the same params in the same order so we treat them as equal.
    private static readonly HashSet<string> ObjectNewFunctions =
    [
        "il2cpp_object_new",
        "il2cpp_vm_object_new",
        "il2cpp_codegen_object_new",
    ];

    //These all take the exception to throw as their only real argument.
    private static readonly HashSet<string> RaiseExceptionFunctions =
    [
        nameof(BaseKeyFunctionAddresses.il2cpp_raise_exception),
        nameof(BaseKeyFunctionAddresses.il2cpp_vm_exception_raise),
        nameof(BaseKeyFunctionAddresses.il2cpp_codegen_raise_exception),
    ];

    //Both take the class to box as and a pointer to the value.
    private static readonly HashSet<string> BoxFunctions =
    [
        nameof(BaseKeyFunctionAddresses.il2cpp_value_box),
        nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_box),
    ];

    public static void Run(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions))
        {
            if (instruction.Operands is not [StringLiteral { Value: var keyFunction }, ..])
                continue;

            if (ObjectNewFunctions.Contains(keyFunction))
                RewriteObjectNew(instruction);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.il2cpp_codegen_write_barrier))
                RemoveWriteBarrier(instruction);
            else if (RaiseExceptionFunctions.Contains(keyFunction))
                RewriteRaiseException(instruction);
            else if (BoxFunctions.Contains(keyFunction))
                RewriteBox(instruction);

            else if (keyFunction == nameof(BaseKeyFunctionAddresses.il2cpp_vm_reflection_get_type_object))
                RewriteTypeObject(instruction);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.InternalCalls_Resolve))
                RewriteInternalCallResolve(instruction, method);
        }
    }

    private static void RemoveWriteBarrier(Instruction instruction)
    {
        instruction.OpCode = OpCode.Nop;
        instruction.SetOperands();
    }
    
    private static void RewriteRaiseException(Instruction instruction)
    {
        // A void call has no return value operand, so the exception is one slot earlier
        var exceptionIndex = instruction.OpCode == OpCode.CallVoid ? 1 : 2;

        if (!instruction.IsCall || instruction.Operands.Count <= exceptionIndex)
            return;

        var exception = instruction.Operands[exceptionIndex];

        instruction.OpCode = OpCode.Throw;
        instruction.SetOperands(exception);
    }

    private static void RewriteBox(Instruction instruction)
    {
        // function name, result, class, address of value.
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, TypeAnalysisContext boxedType, var value, ..])
            return;

        instruction.OpCode = OpCode.Box;
        instruction.SetOperands(result, boxedType, value);
    }

    private static readonly HashSet<string> UnboxFunctions =
    [
        nameof(BaseKeyFunctionAddresses.il2cpp_object_unbox),
        nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_unbox),
    ];

    /// <summary>
    /// Rewrites unbox calls once the class they unbox as is known (it is typed along with everything else).
    /// </summary>
    public static bool RewriteUnboxes(MethodAnalysisContext method)
    {
        var changed = false;
        var graph = method.ControlFlowGraph!;
        foreach (var block in graph.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction is not { OpCode: OpCode.Call, Operands: [StringLiteral { Value: var name }, ..] } || !UnboxFunctions.Contains(name)
                    || !RewriteUnbox(instruction))
                    continue;

                changed = true;
                AssumeElementClassCheckPasses(graph, block);
            }
        }
        return changed;
    }

    // Before unboxing, il2cpp compares obj->klass->element_class (Il2CppClass+0x40) with the target class's and raises
    // InvalidCastException if they differ. IL's unbox does that check itself, so the branch is always taken towards it.
    private static void AssumeElementClassCheckPasses(ISILControlFlowGraph graph, Block unboxBlock)
    {
        if (unboxBlock.Predecessors is not [{ Instructions: [.., { OpCode: OpCode.ConditionalJump, Operands: [var target, LocalVariable condition] } jump] } guard])
            return;

        var check = guard.Instructions.LastOrDefault(i => i.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual && ReferenceEquals(i.Destination, condition));
        if (check == null || !check.Operands.Skip(1).Any(o => o is MemoryOperand { Index: null, Addend: 0x40, Size: 8 }))
            return;

        var targetBlock = target switch
        {
            Block b => b,
            Instruction i => graph.FindBlockByInstruction(i),
            _ => null,
        };
        if (targetBlock == null)
            return;

        jump.SetOperand(1, new Immediate(targetBlock == unboxBlock ? 1 : 0));
    }

    // unbox(obj) -> pointer to the value inside. The class it's unboxed as isn't an argument, but the inlined type check
    // before the call leaves it in one of the following argument registers
    private static bool RewriteUnbox(Instruction instruction)
    {
        if (instruction.OpCode != OpCode.Call || instruction.Operands.Count < 4 || instruction.Operands[1] is not LocalVariable result)
            return false;

        var obj = instruction.Operands[2];
        var unboxedClass = instruction.Operands.Skip(3).Take(2).FirstOrDefault(o => o switch
        {
            LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType.IsValueType: true } } => true,
            RuntimeClassTypeAnalysisContext { RepresentedType.IsValueType: true } => true,
            _ => false,
        });
        if (unboxedClass == null)
            return false;

        var valueType = unboxedClass is LocalVariable { Type: RuntimeClassTypeAnalysisContext local } ? local.RepresentedType : ((RuntimeClassTypeAnalysisContext)unboxedClass).RepresentedType;

        instruction.OpCode = OpCode.Unbox;
        instruction.SetOperands(result, unboxedClass, obj);
        result.Type = valueType.MakeByReferenceType();
        return true;
    }

    private static void RewriteTypeObject(Instruction instruction)
    {
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, TypeAnalysisContext type, ..])
            return;

        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(result, type);
    }

    private static void RewriteInternalCallResolve(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, Immediate nameAddress, ..])
            return;

        if (ThrowHelperRecovery.ReadCStringAtVirtualAddress(method.AppContext, nameAddress.UnsignedValue, 256) is not { } name)
            return;

        if (ResolveInternalCallName(method.AppContext, name) is not { DeclaringType.DeclaringAssembly: { } assembly } resolved)
            return;

        var pointer = new RuntimeMethodInfoAnalysisContext(resolved, assembly);

        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(result, pointer);

        RewriteCachedPointerLoads(method, result, pointer);
    }

    private static void RewriteCachedPointerLoads(MethodAnalysisContext method, IOperand result, RuntimeMethodInfoAnalysisContext pointer)
    {
        var cache = method.ControlFlowGraph!.Instructions
            .Where(i => i is { OpCode: OpCode.Move, Operands: [MemoryOperand { IsConstant: true }, _] })
            .Where(i => ReferenceEquals(i.Operands[1], result))
            .Select(i => ((MemoryOperand)i.Operands[0]).Addend)
            .Distinct()
            .ToList();

        if (cache.Count != 1)
            return;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable destination, MemoryOperand { IsConstant: true } load] }
                && load.Addend == cache[0])
                instruction.SetOperands(destination, pointer);
        }
    }

    internal static MethodAnalysisContext? ResolveInternalCallName(ApplicationAnalysisContext appContext, string name)
    {
        var separator = name.IndexOf("::", StringComparison.Ordinal);

        if (separator < 0)
            return null;

        var typeName = name[..separator];
        var signature = name[(separator + 2)..];
        var parenthesis = signature.IndexOf('(');
        var methodName = parenthesis < 0 ? signature : signature[..parenthesis];

        if (appContext.LibCpp2IlContext.ReflectionCache.GetTypeByFullName(typeName) is not { } typeDefinition
            || appContext.ResolveContextForType(typeDefinition) is not { } type)
            return null;

        var candidates = type.Methods.Where(m => m.Name == methodName).ToList();

        if (candidates.Count <= 1)
            return candidates.FirstOrDefault();

        // Overloaded, so fall back on the parameter list in the name
        var parameters = parenthesis < 0 ? "" : signature[(parenthesis + 1)..].TrimEnd(')');
        var count = parameters.Length == 0 ? 0 : parameters.Split(',').Length;

        var byParameterCount = candidates.Where(m => m.Parameters.Count == count).ToList();

        return byParameterCount.Count == 1 ? byParameterCount[0] : null;
    }

    private static void RewriteObjectNew(Instruction instruction)
    {
        // Needs the function name, the result, and the class argument.
        if (instruction.OpCode != OpCode.Call || instruction.Operands.Count < 3)
            return;

        var result = instruction.Operands[1];
        var klass = instruction.Operands[2];

        instruction.OpCode = OpCode.Newobj;
        instruction.SetOperands(result, klass);
    }
}
