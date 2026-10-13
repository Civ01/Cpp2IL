using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// MSVC uses a struct's stack slot as scratch before it builds the struct there (spilling a pair of floats into the slot a
/// Color is later assembled in), which reads as stores to the struct's fields that are overwritten before anything looks
/// at them. A store to a field of a struct local that is stored again before the local is read (in the same block) is
/// dropped. Runs out of SSA, before IL generation.
/// </summary>
public static class DeadFieldStoreEliminator
{
    public static void Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;

        // a block continues the straight line of the one before it when that's its only way in and its only way on
        static bool Continues(Block block) => block.Predecessors.Distinct().ToList() is [{ } only] && only.Successors.Distinct().Count() == 1 && only != block;

        foreach (var start in graph.Blocks.Where(b => !Continues(b)))
        {
            // (local, field chain) -> the last store to it nothing has read since
            var pending = new Dictionary<(LocalVariable, string), Instruction>();
            var visited = new HashSet<Block>();

            for (var block = start; block != null && visited.Add(block);
                 block = block.Successors.Distinct().ToList() is [{ } next] && Continues(next) ? next : null)
            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode == OpCode.Nop)
                    continue;

                // what the instruction reads of a local clears that local's pending stores (conservatively, the whole local)
                for (var i = 0; i < instruction.Operands.Count; i++)
                {
                    if (i == 0 && instruction is { OpCode: OpCode.Move, Operands: [FieldReference, _] })
                        continue;

                    var read = instruction.Operands[i] switch
                    {
                        LocalVariable local => local,
                        FieldReference field => field.Local,
                        AddressOf { Target: LocalVariable addressed } => addressed,
                        AddressOf { Target: FieldReference addressedField } => addressedField.Local,
                        MemoryOperand { Base: LocalVariable memoryBase } => memoryBase,
                        ArrayAccess access => access.Array,
                        _ => null,
                    };

                    if (read != null)
                        foreach (var key in pending.Keys.Where(k => ReferenceEquals(k.Item1, read)).ToList())
                            pending.Remove(key);
                }

                if (instruction is not { OpCode: OpCode.Move, Operands: [FieldReference { Local: { Type: { IsValueType: true } and not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext) } owner, RootField.IsStatic: false } stored, _] })
                    continue;

                var chain = string.Join(".", stored.Chain.Select(f => f.Name));
                if (pending.TryGetValue((owner, chain), out var overwritten))
                {
                    overwritten.OpCode = OpCode.Nop;
                    overwritten.SetOperands();
                }

                pending[(owner, chain)] = instruction;
            }
        }
    }
}
