using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Recognises what IL2CPP generates for a catch, in the catch funclets lifted onto the end of the method:
/// <code>
/// catch (Il2CppExceptionWrapper&amp; e)
/// {
///     if (il2cpp_codegen_class_is_assignable_from(T_il2cpp_TypeInfo_var, il2cpp_codegen_object_class(e.ex)))
///     {
///         __exception_local = e.ex;
///         goto CATCH_;
///     }
///     throw e;
/// }
/// </code>
/// The type test becomes <c>e.ex is T</c>, and goes altogether when T is System.Exception or System.Object, which every
/// managed exception is. Each read of e.ex is the one exception.
///
/// Runs in SSA form, once calls and types are resolved.
/// </summary>
public static class CatchRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        if (method is not { CatchHandlers: { Count: > 0 } handlers, ControlFlowGraph: { } cfg })
            return;

        var instructions = cfg.Blocks.SelectMany(b => b.Instructions).ToList();
        var uses = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var instruction in instructions)
            foreach (var source in instruction.Sources.Concat(instruction.Operands.OfType<MemoryOperand>().Select(m => m.Base)))
                if (source is LocalVariable local)
                    (uses.TryGetValue(local, out var list) ? list : uses[local] = []).Add(instruction);

        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in instructions)
            if (instruction.Destination is LocalVariable defined)
                definitions[defined] = instruction;

        // what a local was copied from
        IOperand Through(IOperand operand)
        {
            for (var depth = 0; depth < 8 && operand is LocalVariable local && definitions.TryGetValue(local, out var definition)
                                && definition is { OpCode: OpCode.Move, Operands: [_, var source] }; depth++)
                operand = source;
            return operand;
        }

        foreach (var handler in handlers)
        {
            var catches = instructions.Where(i => i.OpCode == OpCode.CatchException && handler.Instructions.Contains(i)).ToList();
            if (catches is not [{ Destination: LocalVariable exception } first, ..])
                continue;

            // every read of the exception out of the wrapper is the same value
            foreach (var other in catches.Skip(1))
            {
                if (other.Destination is not LocalVariable copy)
                    continue;

                var replacement = new Dictionary<LocalVariable, IOperand> { [copy] = exception };
                foreach (var user in uses.GetValueOrDefault(copy) ?? [])
                    SsaSimplifier.ReplaceUses(user, replacement);
                other.OpCode = OpCode.Nop;
                other.SetOperands();
            }

            foreach (var test in instructions.Where(i => handler.Instructions.Contains(i)).ToList())
            {
                // result = class_is_assignable_from(typeof(T), exception->klass)
                if (test is not { OpCode: OpCode.Call, Operands: [Immediate, LocalVariable result, var classArgument, var klassArgument, ..] }
                    || Through(classArgument) is not TypeAnalysisContext caught
                    || Through(klassArgument) is not MemoryOperand { Base: LocalVariable klassOf, Index: null, Addend: 0 }
                    || !ReferenceEquals(klassOf, exception)
                    || !uses.TryGetValue(result, out var resultUses) || resultUses.Any(u => u.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual)))
                    continue;

                first.SetOperands(exception, caught); // keep the caught type with the exception, for the handler region to come

                if (caught.FullName is "System.Exception" or "System.Object")
                {
                    // always true: assignable is 1
                    test.OpCode = OpCode.Move;
                    test.SetOperands(result, new Immediate(1));
                }
                else
                {
                    // exception as T, tested against null the same way
                    test.OpCode = OpCode.IsInst;
                    test.SetOperands(result, caught, exception);
                    result.Type = caught;
                }
            }
        }
    }
}
