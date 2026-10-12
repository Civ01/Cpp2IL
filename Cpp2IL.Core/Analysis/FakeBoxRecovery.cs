using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Boxing a value only to call a method on it (an enum's ToString) doesn't allocate: il2cpp builds a fake box on the
/// stack - klass, a monitor of -1, then the value - and passes its address as the object:
/// <code>
///   lea rcx,[rsp+20h] / mov [rsp+20h],klass / mov [rsp+30h],value / mov qword ptr [rsp+28h],-1 / call Enum.ToString
/// </code>
/// That address is a boxed value, so it becomes a Box of the value. Runs on stack offsets, before slots become
/// registers.
/// </summary>
public static class FakeBoxRecovery
{
    public static void Run(MethodAnalysisContext method, ISILControlFlowGraph graph)
    {
        if (method.AppContext.Binary.PointerSizeBytes != 8)
            return;

        var counter = 0;
        foreach (var block in graph.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                if (block.Instructions[i] is not { OpCode: OpCode.Move, Operands: [Register addressRegister, AddressOf { Target: StackOffset box }] } addressMove)
                    continue;

                int? klassStore = null, monitorStore = null, valueStore = null;
                for (var j = 0; j < block.Instructions.Count; j++)
                {
                    if (block.Instructions[j] is not { OpCode: OpCode.Move, Operands: [StackOffset { } stored, var source] })
                        continue;

                    if (stored.Offset == box.Offset && source is Register or MemoryOperand)
                        klassStore = j;
                    else if (stored.Offset == box.Offset + 8 && source is Immediate { Value: -1 })
                        monitorStore = j;
                    else if (stored.Offset == box.Offset + 16 && source is Register or Immediate)
                        valueStore = j;
                }

                if (klassStore is not { } k || monitorStore is not { } m || valueStore is not { } v || !OnlyUses(graph, box.Offset, addressMove, [block.Instructions[k], block.Instructions[m], block.Instructions[v]]))
                    continue;

                // the box is complete at the last of its stores; the address register must still hold it there
                var at = new[] { i, k, m, v }.Max();
                if (block.Instructions.Skip(i + 1).Take(at - i).Any(x => x.Destination is Register { } written && written.Name == addressRegister.Name))
                    continue;

                var klass = new Register(null, $"FAKEBOX_KLASS_{counter}");
                var value = new Register(null, $"FAKEBOX_VALUE_{counter}");
                counter++;

                var klassInstruction = block.Instructions[k];
                var valueInstruction = block.Instructions[v];
                var monitorInstruction = block.Instructions[m];
                var lastInstruction = block.Instructions[at];

                klassInstruction.SetOperands(klass, klassInstruction.Operands[1]);
                valueInstruction.SetOperands(value, valueInstruction.Operands[1]);
                monitorInstruction.OpCode = OpCode.Nop;
                monitorInstruction.SetOperands();

                var boxInstruction = new Instruction(lastInstruction.Index, OpCode.Box, addressRegister, klass, value);
                block.Instructions.Insert(block.Instructions.IndexOf(lastInstruction) + 1, boxInstruction);

                addressMove.OpCode = OpCode.Nop;
                addressMove.SetOperands();
            }
        }
    }

    // Nothing but the box's own stores and the one address-take touch the 24 bytes of the box
    private static bool OnlyUses(ISILControlFlowGraph graph, int start, Instruction addressMove, Instruction[] stores)
    {
        foreach (var instruction in graph.Instructions)
        {
            if (instruction == addressMove || stores.Contains(instruction))
                continue;

            foreach (var operand in instruction.Operands)
            {
                var offset = operand switch
                {
                    StackOffset direct => direct.Offset,
                    AddressOf { Target: StackOffset addressed } => addressed.Offset,
                    _ => (int?)null,
                };

                if (offset is { } touched && touched >= start && touched < start + 24)
                    return false;
            }
        }

        return true;
    }
}
