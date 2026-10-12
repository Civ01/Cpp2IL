using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// <c>if (feature is CameraImpulseFeedbackFeature impulse) { ... impulse.direction ... }</c> compiles to an inlined
/// type check on the original pointer, after which the code keeps reading through that same pointer, still typed as
/// the base class, so the subclass's fields can't be resolved. Where the cast is known to have succeeded, the original
/// value is the cast result: uses of it there are replaced with the cast result, which carries the derived type.
/// <para/>
/// "Known to have succeeded" follows branches on the null test of the result, through boolean tests of it and through
/// the 1/0 flag a <c>x as T</c> is often compiled into (<c>flag = x is T ? 1 : 0; y = flag != 0 ? x : null</c>).
/// Runs in SSA form, as part of type resolution.
/// </summary>
public static class CastNarrowing
{
    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var casts = graph.Instructions.Where(i => i is { OpCode: OpCode.IsInst, Operands: [LocalVariable, _, LocalVariable] }).ToList();
        if (casts.Count == 0)
            return false;

        var changed = false;
        Analysis? analysis = null;

        foreach (var cast in casts)
        {
            var result = (LocalVariable)cast.Operands[0];
            var original = (LocalVariable)cast.Operands[2];
            if (ReferenceEquals(result, original) || CastType(cast.Operands[1]) is not { } castType
                || castType.IsInterface || castType.IsValueType
                || original.Type != null && !LocalVariables.IsStrictlyMoreDerived(castType, original.Type))
                continue;

            analysis ??= new Analysis(graph);
            analysis.Begin(result);

            // the blocks entered only along an edge on which the cast is known to have succeeded
            var succeeded = new List<Block>();
            foreach (var block in graph.Blocks)
                if (block.Predecessors.Count == 1 && analysis.EdgeFact(block.Predecessors[0], block) == true)
                    succeeded.Add(block);

            if (succeeded.Count == 0)
                continue;

            foreach (var block in graph.Blocks)
            {
                if (succeeded.Any(s => analysis.Dominance.Dominates(s, block)))
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
                        var predecessor = block.Predecessors[input - 1];
                        if (phi.Operands[input] is LocalVariable incoming && ReferenceEquals(incoming, original)
                            && (succeeded.Any(s => analysis.Dominance.Dominates(s, predecessor)) || analysis.EdgeFact(predecessor, block) == true))
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

    /// <summary>What is known about one cast's result (non-null: true, null: false) along edges and from values.</summary>
    private sealed class Analysis
    {
        private readonly ISILControlFlowGraph _graph;
        private readonly Dictionary<LocalVariable, Instruction> _definitions = new();
        private readonly Dictionary<Instruction, Block> _blockOf = new();
        private LocalVariable _result = null!;
        private readonly Dictionary<LocalVariable, bool?> _valueFacts = new();
        public readonly DominatorInfo Dominance;

        public Analysis(ISILControlFlowGraph graph)
        {
            _graph = graph;
            Dominance = new DominatorInfo(graph);
            foreach (var block in graph.Blocks)
            {
                foreach (var instruction in block.Instructions)
                {
                    _blockOf[instruction] = block;
                    if (instruction.OpCode != OpCode.Nop && instruction.Destination is LocalVariable defined)
                        _definitions[defined] = instruction;
                }
            }
        }

        public void Begin(LocalVariable result)
        {
            _result = result;
            _valueFacts.Clear();
            _blockFacts.Clear();
        }

        private readonly Dictionary<Block, bool?> _blockFacts = new();
        private readonly HashSet<Block> _inProgress = new();

        /// <summary>
        /// What following the edge from <paramref name="from"/> to <paramref name="to"/> says about the cast: true if it
        /// is only taken when the cast succeeded, false if only when it failed, null if neither. Edges that are never
        /// taken (a branch on a constant) are reported as <paramref name="never"/>.
        /// </summary>
        public bool? EdgeFact(Block from, Block to, int depth = 0) => EdgeFact(from, to, depth, out _);

        private bool? EdgeFact(Block from, Block to, int depth, out bool never)
        {
            never = false;
            if (from is { Instructions: [.., { OpCode: OpCode.ConditionalJump, Operands: [var target, var condition] }], Successors.Count: 2 })
            {
                var taken = target switch
                {
                    Block b => b,
                    Instruction i => _graph.FindBlockByInstruction(i),
                    _ => null,
                };
                if (taken == null || !from.Successors.Contains(taken))
                    return null;

                if (ConstantCondition(condition) is { } always)
                {
                    never = always != (to == taken);
                    if (never)
                        return null;
                }
                else if (condition is LocalVariable conditionLocal && WhenTrue(conditionLocal, 0) is { } whenTrue)
                    return to == taken ? whenTrue : !whenTrue;
            }

            // a branch that doesn't test the cast passes on what was known before it
            return depth < 64 ? BlockFact(from, depth + 1) : null;
        }

        // What holds throughout a block: what every edge into it agrees on
        private bool? BlockFact(Block block, int depth)
        {
            if (_blockFacts.TryGetValue(block, out var cached))
                return cached;
            if (!_inProgress.Add(block))
                return null; // around a loop: nothing

            bool? agreed = null;
            var any = false;
            foreach (var predecessor in block.Predecessors)
            {
                var fact = EdgeFact(predecessor, block, depth + 1, out var never);
                if (never)
                    continue;
                if (fact == null || any && agreed != fact)
                {
                    agreed = null;
                    any = true;
                    break;
                }

                agreed = fact;
                any = true;
            }

            _inProgress.Remove(block);
            _blockFacts[block] = agreed;
            return agreed;
        }

        // A condition computed from two constants (what's left of a check another pass made always pass or fail)
        private bool? ConstantCondition(IOperand condition)
        {
            if (condition is Immediate { Value: var immediate })
                return immediate != 0;
            if (condition is not LocalVariable local || !_definitions.TryGetValue(local, out var check)
                || check is not { Operands: [_, Immediate { Value: var a }, Immediate { Value: var b }] })
                return null;

            return check.OpCode switch
            {
                OpCode.CheckEqual => a == b,
                OpCode.CheckNotEqual => a != b,
                OpCode.CheckLess => a < b,
                OpCode.CheckGreater => a > b,
                OpCode.CheckLessOrEqual => a <= b,
                OpCode.CheckGreaterOrEqual => a >= b,
                _ => null,
            };
        }

        /// <summary>When <paramref name="value"/> is true (nonzero): true if the cast then succeeded, false if it failed.</summary>
        private bool? WhenTrue(LocalVariable value, int depth)
        {
            if (ReferenceEquals(value, _result))
                return true;
            if (depth > 32 || !_definitions.TryGetValue(value, out var definition))
                return null;
            if (_valueFacts.TryGetValue(value, out var cached))
                return cached;

            _valueFacts[value] = null; // cycles through phis know nothing
            var fact = Evaluate(definition, depth + 1);
            _valueFacts[value] = fact;
            return fact;
        }

        private bool? Evaluate(Instruction definition, int depth)
        {
            switch (definition)
            {
                // (tested != 0) / (tested == 0)
                case { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var left, var right] }:
                {
                    var tested = right is Immediate { Value: 0 } ? left : left is Immediate { Value: 0 } ? right : null;
                    if (tested is not LocalVariable testedLocal || WhenTrue(testedLocal, depth) is not { } testedFact)
                        return null;
                    return definition.OpCode == OpCode.CheckNotEqual ? testedFact : !testedFact;
                }

                case { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] }:
                    return WhenTrue(copied, depth);

                // a flag set to constants on the way in: nonzero exactly along the edges where the cast succeeded
                case { OpCode: OpCode.Phi }:
                {
                    var block = _blockOf[definition];
                    bool? whenNonZero = null;
                    for (var input = 1; input < definition.Operands.Count; input++)
                    {
                        if (input - 1 >= block.Predecessors.Count || Constant(definition.Operands[input]) is not { } constant
                            || EdgeFact(block.Predecessors[input - 1], block, depth) is not { } edge)
                            return null;

                        var implied = constant != 0 ? edge : !edge;
                        if (whenNonZero != null && whenNonZero != implied)
                            return null;
                        whenNonZero = implied;
                    }

                    return whenNonZero;
                }

                default:
                    return null;
            }
        }

        private long? Constant(IOperand operand)
        {
            for (var hops = 0; hops < 4; hops++)
            {
                switch (operand)
                {
                    case Immediate { Value: var value }:
                        return value;
                    case LocalVariable local when _definitions.TryGetValue(local, out var definition) && definition is { OpCode: OpCode.Move, Operands: [_, var source] }:
                        operand = source;
                        continue;
                    default:
                        return null;
                }
            }

            return null;
        }
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
