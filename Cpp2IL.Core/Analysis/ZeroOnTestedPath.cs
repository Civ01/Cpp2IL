using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// <c>return list == null ? 0 : list.Count</c> compiles to returning the list's register itself on the null path, as it
/// is 0 there: one value that is both a list and an int, which types it as neither properly. Where a value was just tested
/// for 0, it is the constant 0 on the way the test was true: in the block only that way reaches, and as what flows into
/// a merge from that edge. Runs in SSA form, before types are resolved.
/// </summary>
public static class ZeroOnTestedPath
{
    public static void Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable).GroupBy(i => (LocalVariable)i.Destination!).ToDictionary(g => g.Key, g => g.First());

        foreach (var block in graph.Blocks)
        {
            if (block.Instructions.LastOrDefault(i => i.OpCode != OpCode.Nop) is not { OpCode: OpCode.ConditionalJump, Operands: [Block taken, LocalVariable flag] }
                || !definitions.TryGetValue(flag, out var test)
                || test is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, LocalVariable tested, Immediate { Value: 0 }] }
                || block.Successors.Distinct().Count() != 2)
                continue;

            // the way the value is 0
            var zeroWay = test.OpCode == OpCode.CheckEqual ? taken : block.Successors.First(s => s != taken);
            if (zeroWay == graph.ExitBlock)
                continue;

            // into a merge: the phi's input from this edge
            var edge = zeroWay.Predecessors.IndexOf(block);
            if (zeroWay.Predecessors.Count(p => p == block) == 1)
                foreach (var phi in zeroWay.Instructions.Where(i => i.OpCode == OpCode.Phi))
                    if (1 + edge < phi.Operands.Count && phi.Operands[1 + edge] is LocalVariable input && input == tested)
                        phi.SetOperand(1 + edge, new Immediate(0));

            // a block only this way reaches: the returned value there
            if (zeroWay.Predecessors.Distinct().Count() == 1)
                foreach (var instruction in zeroWay.Instructions)
                    if (instruction is { OpCode: OpCode.Return, Operands: [LocalVariable returned] } && returned == tested)
                        instruction.SetOperand(0, new Immediate(0));
        }
    }
}
