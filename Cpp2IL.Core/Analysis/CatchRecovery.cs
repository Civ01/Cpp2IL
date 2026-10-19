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
    /// <summary>
    /// What a catch is handed is an exception, before anything else is known of it: typed so from the start, calls on it
    /// (its virtual methods, through its class's vtable) resolve like any other's. <see cref="Run"/> narrows it to the type caught.
    /// </summary>
    public static void SeedExceptionTypes(MethodAnalysisContext method)
    {
        if (method is not { CatchHandlers.Count: > 0, ControlFlowGraph: { } cfg })
            return;

        foreach (var instruction in cfg.Blocks.SelectMany(b => b.Instructions))
            if (instruction is { OpCode: OpCode.CatchException, Operands: [LocalVariable { Type: null } caught, ..] })
                caught.Type = method.AppContext.SystemTypes.SystemExceptionType;
    }

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

        // the class tested against: typeof(T), or a local holding T's runtime class
        static TypeAnalysisContext? CaughtType(IOperand operand) => operand switch
        {
            RuntimeClassTypeAnalysisContext runtimeClass => runtimeClass.RepresentedType,
            TypeAnalysisContext type => type,
            LocalVariable { Type: RuntimeClassTypeAnalysisContext runtimeClass } => runtimeClass.RepresentedType,
            _ => null,
        };

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

            // result = class_is_assignable_from(typeof(T), exception->klass), one per C# catch clause
            var tests = new List<(Instruction Test, LocalVariable Result, TypeAnalysisContext Caught)>();
            foreach (var test in instructions.Where(i => handler.Instructions.Contains(i)))
            {
                if (test is not { OpCode: OpCode.Call, Operands: [Immediate, LocalVariable result, var classArgument, var klassArgument, ..] }
                    || CaughtType(Through(classArgument)) is not { } caught
                    || Through(klassArgument) is not MemoryOperand { Base: LocalVariable klassOf, Index: null, Addend: 0 }
                    || !ReferenceEquals(klassOf, exception)
                    || !uses.TryGetValue(result, out var resultUses)
                    // (tested against 0; the copy into xmm0 the lifter makes after every call, in case the result is a float, doesn't count)
                    || resultUses.Any(u => u.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual)
                                           && !(u is { OpCode: OpCode.Move, Destination: LocalVariable { Register.Name: var copyRegister } } && copyRegister.StartsWith("xmm"))))
                    continue;

                tests.Add((test, result, caught));
            }

            if (tests is [var only])
            {
                // the handler catches just that type, so the test always holds
                first.SetOperands(exception, only.Caught);
                exception.Type = only.Caught;
                only.Test.OpCode = OpCode.Move;
                only.Test.SetOperands(only.Result, new Immediate(1));
                continue;
            }

            // several catch clauses: the handler takes any exception, and tests which clause it's for (rethrowing the rest)
            foreach (var (test, result, caught) in tests)
            {
                test.OpCode = OpCode.IsInst;
                test.SetOperands(result, caught, exception);
                result.Type = caught;
            }
        }
    }
}
