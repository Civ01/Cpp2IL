using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// MSVC merges calls that only differ in which virtual method they call (<c>if (b) c.Hide(); else c.Show();</c> at the
/// end of a method): each branch loads its vtable slot into rax, and both go to one <c>call rax</c>. With the target a
/// merge of two slots, neither call can be resolved. So a call block reached from several blocks that each load the call
/// target from memory is copied into each of them; the copies return, or go on to where it went. Runs on registers,
/// before SSA.
/// </summary>
public static class CallTailDuplication
{
    private const int MaxInstructions = 40;
    private const int MaxPredecessors = 4;

    public static void Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;

        foreach (var tail in graph.Blocks.ToList())
        {
            var real = tail.Instructions.Where(i => i.OpCode != OpCode.Nop).ToList();
            // the block ends the method, or goes on to one place (which the copies then go on to as well)
            if (real.Count is 0 or > MaxInstructions
                || real[^1].OpCode != OpCode.Return && tail.Successors.Distinct().Count() != 1
                || tail.Successors.Contains(tail)
                || real.Count(i => i.OpCode == OpCode.IndirectCall) != 1
                || real.First(i => i.OpCode == OpCode.IndirectCall).Operands is not [Register target, ..]
                || real.Any(i => i.OpCode is OpCode.ConditionalJump or OpCode.IndirectJump))
                continue;

            var callAt = real.FindIndex(i => i.OpCode == OpCode.IndirectCall);
            if (real.Take(callAt).Any(i => i.Destination is Register written && written.Name == target.Name))
                continue;

            var predecessors = tail.Predecessors.Distinct().ToList();
            if (predecessors.Count is < 2 or > MaxPredecessors
                || predecessors.Any(p => p == graph.EntryBlock || p.Successors.Distinct().Count() != 1 || !LoadsTarget(p, target.Name)))
                continue;

            // the first keeps the original; each of the others gets a copy
            foreach (var predecessor in predecessors.Skip(1))
            {
                var copy = new Block
                {
                    ID = graph.Blocks.Max(b => b.ID) + 1,
                    BlockType = tail.BlockType,
                    Instructions = tail.Instructions.Select(Clone).ToList(),
                };

                copy.Successors.AddRange(tail.Successors);
                foreach (var successor in tail.Successors)
                    successor.Predecessors.Add(copy);

                predecessor.Successors = predecessor.Successors.Select(s => s == tail ? copy : s).ToList();
                tail.Predecessors.RemoveAll(p => p == predecessor);
                copy.Predecessors.Add(predecessor);

                // a jump to it goes to the copy now
                foreach (var instruction in predecessor.Instructions)
                    if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump && instruction.Operands.Count > 0 && instruction.Operands[0] == tail)
                        instruction.SetOperand(0, copy);

                graph.Blocks.Add(copy);
            }
        }
    }

    // the last thing the block does to the register is load it from memory: a vtable slot, a delegate's method pointer
    private static bool LoadsTarget(Block block, string register)
    {
        var last = block.Instructions.LastOrDefault(i => i.Destination is Register written && written.Name == register);
        return last is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: Register, Index: null }] };
    }

    private static Instruction Clone(Instruction instruction)
        => new(instruction.Index, instruction.OpCode, instruction.Operands.Select(o => o is AddressOf addressOf ? new AddressOf(addressOf.Target) : o).ToList());
}
