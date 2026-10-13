using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Undoes what full generic sharing (Unity 2022+) expands a shared method's handling of a T into:
/// <list type="bullet">
/// <item>Boxing a T: the value is copied into a temporary from its address (a value type, which shared code passes by
/// pointer) or from itself (a reference), picked by the value type bit of T's class (<c>[klass+28]:4 &gt;= 0</c>), and the
/// temporary is boxed. That is just <c>(object)value</c>.</item>
/// <item>Branches whose two ways reach the same code without doing anything (what's left of the above, and the overflow
/// checks of sizing stack space for a T: <c>if (size + 15 &gt; size)</c>).</item>
/// </list>
/// Runs out of SSA, late.
/// </summary>
public static class SharedGenericCleanup
{
    public static void Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        if (RecoverBoxes(graph))
            DeadCodeEliminator.Run(graph); // the copies picked by the value type check go, emptying its branches

        if (FoldEmptyBranches(graph))
        {
            graph.RemoveUnreachableBlocks();
            DeadCodeEliminator.Run(graph);
        }
    }

    private static bool RecoverBoxes(ISILControlFlowGraph graph)
    {
        var changed = false;
        var instructions = graph.Instructions.ToList();

        foreach (var block in graph.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                if (block.Instructions[i] is not { OpCode: OpCode.Box, Operands: [_, _, AddressOf { Target: LocalVariable temporary }] } box)
                    continue;

                // the copy into the temporary straight before it
                var copyAt = i == 0 ? -1 : block.Instructions.FindLastIndex(i - 1, i, x => x.OpCode != OpCode.Nop);
                if (copyAt < 0 || block.Instructions[copyAt] is not { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: "MemCpy" }, AddressOf { Target: LocalVariable into }, LocalVariable source, ..] } copy
                    || into != temporary)
                    continue;

                // what it copies from: the value's address, or the value itself
                var sources = instructions.Where(x => x.Destination is LocalVariable d && d == source).ToList();
                var value = sources.Select(x => x.Operands[1]).OfType<LocalVariable>().FirstOrDefault(v => v.Type is not PointerTypeAnalysisContext && v.Type?.FullName != "System.Void*");
                if (sources.Count is 0 or > 2 || value == null
                    || sources.Any(x => x is not { OpCode: OpCode.Move } || x.Operands[1] is not (LocalVariable or AddressOf { Target: LocalVariable })))
                    continue;

                box.SetOperand(2, value);
                copy.OpCode = OpCode.Nop;
                copy.SetOperands();
                changed = true;
            }
        }

        return changed;
    }

    // A conditional branch whose two ways reach the same block through nothing but jumps does nothing
    private static bool FoldEmptyBranches(ISILControlFlowGraph graph)
    {
        var changed = false;
        for (var progress = true; progress;)
        {
            progress = false;
            foreach (var block in graph.Blocks)
            {
                if (block.Instructions.LastOrDefault(i => i.OpCode != OpCode.Nop) is not { OpCode: OpCode.ConditionalJump, Operands: [Block taken, _] } jump)
                    continue;

                var successors = block.Successors.Distinct().ToList();

                // one way left (the other, an overflow check's throw, already gone): it's just a jump
                if (successors is [var only] && only != graph.ExitBlock)
                {
                    jump.OpCode = OpCode.Jump;
                    jump.SetOperands(only);
                    progress = changed = true;
                    continue;
                }

                if (successors.Count != 2)
                    continue;

                var other = successors.First(s => s != taken);
                if (Landing(taken) is not { } landing || Landing(other) != landing)
                    continue;

                jump.OpCode = OpCode.Jump;
                jump.SetOperands(taken);
                block.Successors.RemoveAll(s => s == other);
                other.Predecessors.RemoveAll(p => p == block);
                progress = changed = true;
            }
        }

        return changed;

        // the first block with something in it, following jumps from here
        Block? Landing(Block start)
        {
            var block = start;
            for (var hops = 0; hops < 8; hops++)
            {
                if (block == graph.ExitBlock || block.Instructions.Any(i => i.OpCode is not (OpCode.Nop or OpCode.Jump)))
                    return block;

                if (block.Successors.Distinct().ToList() is not [var next])
                    return null;

                block = next;
            }

            return null;
        }
    }
}
