using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// <c>if (feature is CameraImpulseFeedbackFeature impulse) { ... impulse.direction ... }</c> compiles to an inlined
/// type check on the original pointer, after which the code keeps reading through that same pointer, still typed as
/// the base class, so the subclass's fields can't be resolved. Where the cast is known to have succeeded (the
/// non-null branch of its result), the original value is the cast result: uses of it there are replaced with the
/// cast result, which carries the derived type. Runs in SSA form, as part of type resolution.
/// </summary>
public static class CastNarrowing
{
    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var casts = graph.Instructions.Where(i => i is { OpCode: OpCode.IsInst, Operands: [LocalVariable, _, LocalVariable] }).ToList();
        if (casts.Count == 0)
            return false;

        DominatorInfo? dominance = null;
        var changed = false;

        foreach (var cast in casts)
        {
            var result = (LocalVariable)cast.Operands[0];
            var original = (LocalVariable)cast.Operands[2];
            if (ReferenceEquals(result, original) || CastType(cast.Operands[1]) is not { } castType
                || castType.IsInterface || castType.IsValueType
                || original.Type != null && !LocalVariables.IsStrictlyMoreDerived(castType, original.Type))
                continue;

            if (NonNullSuccessor(graph, result) is not { Predecessors.Count: 1 } succeeded)
                continue;

            dominance ??= new DominatorInfo(graph);

            foreach (var block in graph.Blocks)
            {
                if (dominance.Dominates(succeeded, block))
                {
                    foreach (var instruction in block.Instructions)
                        changed |= Replace(instruction, original, result);
                    continue;
                }

                // a phi reads each input at the end of the matching predecessor (x = cast succeeded ? original : null)
                foreach (var phi in block.Instructions)
                {
                    if (phi.OpCode != OpCode.Phi)
                        continue;

                    for (var input = 1; input < phi.Operands.Count && input - 1 < block.Predecessors.Count; input++)
                    {
                        if (phi.Operands[input] is LocalVariable incoming && ReferenceEquals(incoming, original)
                            && dominance.Dominates(succeeded, block.Predecessors[input - 1]))
                        {
                            phi.SetOperand(input, result);
                            changed = true;
                        }
                    }
                }
            }
        }

        return changed;
    }

    private static TypeAnalysisContext? CastType(IOperand operand) => operand switch
    {
        LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var represented } } => represented,
        RuntimeClassTypeAnalysisContext { RepresentedType: var represented } => represented,
        _ => null,
    };

    // The block reached when the cast result is not null: a branch on (result == null) / (result != null), possibly
    // through boolean tests of that (flag != 0, flag == 0)
    private static Block? NonNullSuccessor(ISILControlFlowGraph graph, LocalVariable result)
    {
        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in graph.Instructions)
            if (instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual && instruction.Destination is LocalVariable defined)
                definitions[defined] = instruction;

        foreach (var block in graph.Blocks)
        {
            if (block is not { Instructions: [.., { OpCode: OpCode.ConditionalJump, Operands: [var target, LocalVariable condition] }], Successors.Count: 2 })
                continue;

            // whether the jump is taken when the cast result is non-null
            bool? takenWhenNonNull = null;
            var current = condition;
            var whenTrue = true; // the jump is taken when `current` is true
            for (var depth = 0; depth < 4 && definitions.TryGetValue(current, out var check); depth++)
            {
                if (check is not { Operands: [_, var left, var right] })
                    break;

                var tested = right is Immediate { Value: 0 } ? left : left is Immediate { Value: 0 } ? right : null;
                if (tested is not LocalVariable testedLocal)
                    break;

                // check == (tested != 0) or check == (tested == 0)
                var sameSense = check.OpCode == OpCode.CheckNotEqual;
                if (ReferenceEquals(testedLocal, result))
                {
                    takenWhenNonNull = sameSense == whenTrue;
                    break;
                }

                if (!sameSense)
                    whenTrue = !whenTrue;
                current = testedLocal;
            }

            if (takenWhenNonNull == null)
                continue;

            var taken = target switch
            {
                Block b => b,
                Instruction i => graph.FindBlockByInstruction(i),
                _ => null,
            };
            if (taken == null || !block.Successors.Contains(taken))
                continue;

            return takenWhenNonNull.Value ? taken : block.Successors.FirstOrDefault(s => s != taken);
        }

        return null;
    }

    private static bool Replace(Instruction instruction, LocalVariable original, LocalVariable result)
    {
        var changed = false;
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            var operand = instruction.Operands[i];
            IOperand? replacement = operand switch
            {
                LocalVariable local when ReferenceEquals(local, original) && !(i == 0 && ReferenceEquals(instruction.Destination, local)) => result,
                MemoryOperand { Base: LocalVariable memoryBase } memory when ReferenceEquals(memoryBase, original) => memory with { Base = result },
                FieldReference { Local: { } fieldLocal } field when ReferenceEquals(fieldLocal, original) => new FieldReference(field.Field, result, field.Offset) { Path = field.Path },
                _ => null,
            };

            if (replacement == null)
                continue;

            instruction.SetOperand(i, replacement);
            changed = true;
        }

        return changed;
    }
}
