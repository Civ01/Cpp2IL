using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A register zeroed once (xor ecx,ecx) is often used for several unrelated things: a null stored into a field, the
/// start of a loop counter, a false flag. In SSA they're all one local, which can only have one type, so whichever use
/// types it first wins and the others read as nonsense (an int loop counter typed as a List). This gives every use of
/// a small integer constant its own copy of it, so each can be typed on its own. Runs in SSA form, before typing.
/// </summary>
public static class ConstantSplitter
{
    public static void Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;

        var constants = new Dictionary<LocalVariable, (Instruction Definition, Immediate Value)>();
        foreach (var instruction in graph.Instructions)
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable local, Immediate { Value: >= -0x10000 and <= 0x10000 } value] } && local.Type == null
                && !local.IsReturn && !method.ParameterLocals.Contains(local))
                constants[local] = (instruction, value);

        if (constants.Count == 0)
            return;

        var uses = new Dictionary<LocalVariable, List<(Graphs.Block Block, Instruction Use)>>();
        foreach (var block in graph.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                foreach (var operand in instruction.Operands)
                {
                    if (operand is LocalVariable used && constants.ContainsKey(used) && !ReferenceEquals(instruction.Destination, used))
                    {
                        if (!uses.TryGetValue(used, out var list))
                            uses[used] = list = [];
                        list.Add((block, instruction));
                    }
                }
            }
        }

        var counter = 0;
        foreach (var (constant, constantUses) in uses)
        {
            if (constantUses.Count < 2)
                continue;

            // anything that isn't a plain operand use (memory bases etc.) keeps the original
            var (_, value) = constants[constant];

            foreach (var (block, use) in constantUses.Skip(1))
            {
                if (use.OpCode == OpCode.Phi)
                {
                    // the copy goes at the end of the predecessor the value comes in from
                    for (var input = 1; input < use.Operands.Count; input++)
                    {
                        if (!ReferenceEquals(use.Operands[input], constant) || input - 1 >= block.Predecessors.Count)
                            continue;

                        var predecessor = block.Predecessors[input - 1];
                        var copy = NewLocal(method, ref counter);
                        var at = predecessor.Instructions.Count > 0 && predecessor.Instructions[^1].OpCode is OpCode.Jump or OpCode.ConditionalJump
                            ? predecessor.Instructions.Count - 1
                            : predecessor.Instructions.Count;
                        predecessor.Instructions.Insert(at, new Instruction(use.Index, OpCode.Move, copy, value));
                        use.SetOperand(input, copy);
                    }

                    continue;
                }

                var replacement = NewLocal(method, ref counter);
                for (var i = 0; i < use.Operands.Count; i++)
                    if (ReferenceEquals(use.Operands[i], constant) && !ReferenceEquals(use.Destination, constant))
                        use.SetOperand(i, replacement);

                block.Instructions.Insert(block.Instructions.IndexOf(use), new Instruction(use.Index, OpCode.Move, replacement, value));
            }
        }
    }

    private static LocalVariable NewLocal(MethodAnalysisContext method, ref int counter)
    {
        var local = new LocalVariable($"constant{counter}", new Register(null, $"CONST_{counter}", 0));
        counter++;
        method.Locals.Add(local);
        return local;
    }
}
