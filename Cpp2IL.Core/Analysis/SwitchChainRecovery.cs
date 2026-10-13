using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A run of equality compares of one local, one case per block, for IL generation to emit as a single IL switch from
/// <see cref="First"/> (whose own compare it replaces): Targets[i] is where Minimum + i goes, Default the rest. The other
/// blocks of <see cref="Chain"/> are then not reached any more.
/// </summary>
public sealed record SwitchTable(Block First, LocalVariable Value, long Minimum, List<Block> Targets, Block Default, List<Block> Chain);

/// <summary>
/// A switch is lifted as a chain of compares, one case per block. Copy propagation puts the switched-on value (a field,
/// usually) back into each of them, and a decompiler only makes a switch statement out of compares of a single local.
/// So a chain of three or more compares of the same field gets that field read into a local once, ahead of it.
/// Runs out of SSA, after the block layout is final.
/// </summary>
public static class SwitchChainRecovery
{
    private const int MinimumCases = 3;

    public static void Run(MethodAnalysisContext method)
    {
        method.SwitchTables = null;
        var graph = method.ControlFlowGraph!;
        var counter = 0;
        var used = new HashSet<Block>();

        // a compare's result that anything else reads (the flag reused further on) has to stay where it is
        var mentions = new Dictionary<LocalVariable, int>();
        foreach (var instruction in graph.Instructions)
            foreach (var operand in instruction.Operands)
                if (operand is LocalVariable mentioned)
                    mentions[mentioned] = mentions.GetValueOrDefault(mentioned) + 1;

        IOperand? Compared(Block block) => SwitchChainRecovery.Compared(block, mentions);

        foreach (var start in graph.Blocks.ToList())
        {
            if (used.Contains(start) || Compared(start) is not { } switched)
                continue;

            var key = switched.ToString();

            // the start of a chain, not the middle of one
            if (start.Predecessors.Distinct().ToList() is [var previous] && Compared(previous)?.ToString() == key && previous.Successors.Contains(start))
                continue;

            var chain = new List<Block> { start };
            for (var current = start; ;)
            {
                var next = current.Successors.Distinct().FirstOrDefault(s => !chain.Contains(s) && s.Predecessors.Distinct().Count() == 1
                                                                              && Compared(s)?.ToString() == key);
                if (next == null)
                    break;

                chain.Add(next);
                current = next;
            }

            if (chain.Count(b => b.Instructions.Any(i => i.OpCode == OpCode.CheckEqual)) < MinimumCases)
                continue;

            if (switched is LocalVariable already)
            {
                used.UnionWith(chain);
                if (Table(graph, chain, already) is { } direct)
                    (method.SwitchTables ??= []).Add(direct);
                continue;
            }

            var type = switched switch
            {
                FieldReference field => field.Field.FieldType,
                ArrayAccess { Array.Type: SzArrayTypeAnalysisContext { ElementType: var element } } => element,
                _ => null
            };
            if (type == null)
                continue;

            var local = new LocalVariable($"switched{counter}", new Register(null, $"SWITCH_{counter}", 0), type);
            counter++;
            method.Locals.Add(local);

            var compares = chain.Select(b => b.Instructions.First(IsCompare)).ToList();
            start.Instructions.Insert(start.Instructions.IndexOf(compares[0]), new Instruction(compares[0].Index, OpCode.Move, local, switched));
            foreach (var compare in compares)
                compare.SetOperand(1, local);

            used.UnionWith(chain);

            if (Table(graph, chain, local) is { } table)
                (method.SwitchTables ??= []).Add(table);
        }
    }

    // The longest run of equality compares in the chain, as a table, if it is dense enough to be one
    private static SwitchTable? Table(Graphs.ISILControlFlowGraph graph, List<Block> chain, LocalVariable local)
    {
        // only what is known to be a number (a value of the wrong type would need a cast to switch on)
        if (local.Type is not { } type || !(type.IsEnumType || type.Namespace == "System" && type.Name is "Int32" or "UInt32" or "Int16" or "UInt16" or "Byte" or "SByte" or "Char"))
            return null;

        var cases = new List<(long Value, Block Target)>();
        var run = new List<Block>();
        Block? next = null;
        foreach (var block in chain)
        {
            var compare = block.Instructions.First(IsCompare);
            var jump = block.Instructions.Last(i => i.OpCode == OpCode.ConditionalJump);
            var jumpTarget = jump.Operands[0] as Block;
            var other = block.Successors.FirstOrDefault(s => s != jumpTarget);
            if (compare.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual) || jumpTarget == null || other == null || other == graph.ExitBlock)
            {
                if (run.Count > 0)
                    break; // only the first run
                continue;
            }

            var (target, onward) = compare.OpCode == OpCode.CheckEqual ? (jumpTarget, other) : (other, jumpTarget);
            if (run.Count > 0 && run[^1] != block.Predecessors.FirstOrDefault())
                break;

            cases.Add((((Immediate)compare.Operands[2]).Value, target));
            run.Add(block);
            next = onward;
        }

        if (run.Count < MinimumCases || next == null || cases.Select(c => c.Value).Distinct().Count() != cases.Count)
            return null;

        var minimum = cases.Min(c => c.Value);
        var span = cases.Max(c => c.Value) - minimum + 1;
        if (span > 256 || span > 2 * cases.Count)
            return null;

        // the default: what the last compare falls through to; it can't be one of the run's own blocks
        if (run.Contains(next))
            return null;

        var targets = Enumerable.Range(0, (int)span).Select(i => cases.FirstOrDefault(c => c.Value == minimum + i).Target ?? next).ToList();
        return new SwitchTable(run[0], local, minimum, targets, next, run);
    }

    private static bool IsCompare(Instruction instruction) => instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual or OpCode.CheckGreater or OpCode.CheckLess
        or OpCode.CheckGreaterOrEqual or OpCode.CheckLessOrEqual;

    // The value a block that's only a compare of something with a constant and a branch on it compares
    private static IOperand? Compared(Block block, Dictionary<LocalVariable, int> mentions)
    {
        var real = block.Instructions.Where(i => i.OpCode != OpCode.Nop).ToList();
        if (real is not [var compare, { OpCode: OpCode.ConditionalJump, Operands: [_, LocalVariable condition] }]
            || !IsCompare(compare) || compare.Operands is not [LocalVariable flag, var value, Immediate] || flag != condition
            || mentions.GetValueOrDefault(flag) != 2)
            return null;

        return value is FieldReference or ArrayAccess or LocalVariable ? value : null;
    }
}
