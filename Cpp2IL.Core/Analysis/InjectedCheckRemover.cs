using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Remove null and bounds checks which are explicit in il2cpp but implicit in IL
public static class InjectedCheckRemover
{
    public static void Run(MethodAnalysisContext method) => Run(method.ControlFlowGraph!);

    public static void Run(ISILControlFlowGraph cfg)
    {
        var defOf = BuildDefMap(cfg);
        var removedAny = EndBlocksAtThrows(cfg);

        foreach (var block in cfg.Blocks)
        {
            if (block.BlockType != BlockType.TwoWay || block.Instructions.Count == 0)
                continue;

            var terminator = block.Instructions[^1];

            if (terminator.OpCode != OpCode.ConditionalJump)
                continue;

            if (terminator.Operands[1] is not LocalVariable condition || !defOf.TryGetValue(condition, out var definition))
                continue;

            // if (x == null) throw ...; or, with the branch the other way round, if (x != null) goto ok; throw ...
            var jumpTarget = terminator.Operands[0] as Block;
            var fallthrough = block.Successors.FirstOrDefault(s => s != jumpTarget);

            string? removedType;
            if (jumpTarget != null && GetInjectedThrowType(jumpTarget) is { } thrownType && IsInjectedCheck(definition, thrownType, false, defOf))
            {
                removedType = thrownType;
                terminator.OpCode = OpCode.Nop;
                terminator.SetOperands();
                RemoveEdge(block, jumpTarget);
            }
            else if (jumpTarget != null && fallthrough != null && GetInjectedThrowType(fallthrough) is { } invertedType && IsInjectedCheck(definition, invertedType, true, defOf))
            {
                removedType = invertedType;
                terminator.OpCode = OpCode.Jump;
                terminator.SetOperands(jumpTarget);
                RemoveEdge(block, fallthrough);
            }
            else
                continue;

            // the element class test only served the check
            if (removedType == "System.ArrayTypeMismatchException" && definition.Operands[1] is LocalVariable tested && defOf.TryGetValue(tested, out var testDefinition) && testDefinition.OpCode == OpCode.IsInst
                && cfg.Instructions.Count(i => i.Operands.Any(o => ReferenceEquals(o, tested))) == 2)
            {
                testDefinition.OpCode = OpCode.Nop;
                testDefinition.SetOperands();
            }

            block.CalculateBlockType();
            removedAny = true;
        }

        if (!removedAny)
            return;

        // delete any throw blocks
        cfg.RemoveUnreachableBlocks();
        DeadCodeEliminator.Run(cfg);
    }

    // Whether the condition is that of an injected check; inverted when it's the condition for skipping the throw
    private static bool IsInjectedCheck(Instruction definition, string thrownType, bool inverted, Dictionary<LocalVariable, Instruction> defOf) =>
        thrownType switch
        {
            "System.NullReferenceException" => IsNullTest(definition, inverted),
            "System.IndexOutOfRangeException" => definition.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual,
            // storing into an array of a reference type: the value must be an instance of the element class
            // (IsInst(value, array->klass->element_class) == null)
            "System.ArrayTypeMismatchException" => IsNullTest(definition, inverted) && definition.Operands[1] is LocalVariable cast
                                                   && defOf.TryGetValue(cast, out var castDefinition) && castDefinition.OpCode == OpCode.IsInst,
            _ => false
        };

    private static bool IsNullTest(Instruction definition, bool inverted) =>
        definition is { OpCode: var test, Operands: [_, _, Immediate { Value: 0 }] } && test == (inverted ? OpCode.CheckNotEqual : OpCode.CheckEqual);

    // A predecessor and the phi inputs it supplied go together
    private static void RemoveEdge(Block from, Block to)
    {
        from.Successors.Remove(to);
        for (var i = to.Predecessors.Count - 1; i >= 0; i--)
        {
            if (to.Predecessors[i] != from)
                continue;

            foreach (var phi in to.Instructions)
                if (phi.OpCode == OpCode.Phi && 1 + i < phi.Operands.Count)
                    phi.RemoveOperandAt(1 + i);

            to.Predecessors.RemoveAt(i);
            break;
        }
    }

    /// <summary>
    /// The exception raising helpers never return, but the lifter can't know that and lets the block fall into whatever
    /// comes next - often the next check's throw, which then looks reachable from this one. A throw ends its block.
    /// </summary>
    private static bool EndBlocksAtThrows(ISILControlFlowGraph cfg)
    {
        var changed = false;

        foreach (var block in cfg.Blocks)
        {
            var thrown = block.Instructions.FindIndex(i => i.OpCode == OpCode.Throw);
            if (thrown < 0)
                continue;

            // what the lifter put after it (the return the call was followed by) never runs
            foreach (var dead in block.Instructions.Skip(thrown + 1).Where(i => i.OpCode is not (OpCode.Nop or OpCode.Interrupt)))
            {
                dead.OpCode = OpCode.Nop;
                dead.SetOperands();
                changed = true;
            }

            if (block.Successors.All(s => s == cfg.ExitBlock))
                continue;

            foreach (var successor in block.Successors.Where(s => s != cfg.ExitBlock).ToList())
                while (successor.Predecessors.Contains(block))
                    RemoveEdge(block, successor);

            block.Successors.Clear();
            block.Successors.Add(cfg.ExitBlock);
            cfg.ExitBlock.Predecessors.Add(block);
            changed = true;
        }

        return changed;
    }

    // The full name of the exception if this block does nothing but throw an injected check's exception, else null.
    private static string? GetInjectedThrowType(Block block)
    {
        string? thrown = null;

        foreach (var instruction in block.Instructions)
        {
            switch (instruction.OpCode)
            {
                // (phis are left by the paths that used to fall in from a previous throw)
                case OpCode.Nop or OpCode.Interrupt or OpCode.Phi:
                case OpCode.Return when thrown != null:
                    continue;

                case OpCode.Throw when thrown == null
                    && instruction.Operands is [TypeAnalysisContext { FullName: "System.NullReferenceException" or "System.IndexOutOfRangeException" or "System.ArrayTypeMismatchException" } exception]:
                    thrown = exception.FullName;
                    continue;

                default:
                    return null;
            }
        }

        return thrown;
    }

    private static Dictionary<LocalVariable, Instruction> BuildDefMap(ISILControlFlowGraph cfg)
    {
        var defs = new Dictionary<LocalVariable, Instruction>();

        foreach (var instruction in cfg.Instructions)
            if (instruction.Destination is LocalVariable local)
                defs[local] = instruction;

        return defs;
    }
}
