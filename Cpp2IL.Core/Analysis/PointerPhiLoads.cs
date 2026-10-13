using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// <c>v = flag ? Vector3.zero : animator.deltaPosition</c> compiles to picking one of two pointers - the class's static
/// fields (zero is the first of them) or the buffer the getter returned into - and reading the struct through whichever
/// it was. Nothing can type such a pointer, so the read is pushed back along each incoming edge, where it reads a
/// static field or a returned value, and the values are merged instead.
/// Runs in SSA form once types are known.
/// </summary>
public static class PointerPhiLoads
{
    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var changed = false;

        var uses = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var instruction in graph.Instructions)
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var used = instruction.Operands[i] switch
                {
                    LocalVariable local when i > 0 || instruction.OpCode != OpCode.Move && instruction.OpCode != OpCode.Phi => local,
                    MemoryOperand { Base: LocalVariable memoryBase } => memoryBase,
                    MemoryOperand { Index: LocalVariable memoryIndex } => memoryIndex,
                    FieldReference { Local: var fieldBase } => fieldBase,
                    AddressOf { Target: LocalVariable addressed } => addressed,
                    AddressOf { Target: FieldReference { Local: var addressedBase } } => addressedBase,
                    _ => null,
                };

                if (used == null)
                    continue;

                if (!uses.TryGetValue(used, out var list))
                    uses[used] = list = [];
                list.Add(instruction);
            }

        var pointerSize = method.AppContext.Binary.PointerSizeBytes;

        foreach (var block in graph.Blocks)
        {
            foreach (var phi in block.Instructions.Where(i => i.OpCode == OpCode.Phi).ToList())
            {
                if (phi.Operands[0] is not LocalVariable merged
                    || phi.Operands.Count - 1 != block.Predecessors.Count
                    || !phi.Operands.Skip(1).All(o => o is LocalVariable)
                    || !phi.Operands.Skip(1).Any(o => o is LocalVariable { Type: StaticFieldStorageTypeAnalysisContext })
                    || !uses.TryGetValue(merged, out var mergedUses))
                    continue;

                // every use reads a piece of what it points at: (load, offset, size)
                var reads = new List<(Instruction Load, long Offset, int Size)>();
                foreach (var use in mergedUses.Distinct())
                {
                    switch (use)
                    {
                        case { OpCode: OpCode.Move, Operands: [LocalVariable, MemoryOperand { Base: LocalVariable memoryBase, Index: null, Size: > 0 } memory] } when ReferenceEquals(memoryBase, merged):
                            reads.Add((use, memory.Addend, memory.Size));
                            break;
                        case { OpCode: OpCode.Move, Operands: [LocalVariable, FieldReference { Local: var fieldBase, Field.IsStatic: false } field] } when ReferenceEquals(fieldBase, merged)
                                                                                                                   && Utils.TypeSizes.StorageSize(field.Field.FieldType, pointerSize) is > 0 and var fieldSize:
                            reads.Add((use, field.Offset, (int)fieldSize));
                            break;
                        default:
                            reads.Clear();
                            goto done;
                    }
                }

                done:
                if (reads.Count == 0 || reads.Count != mergedUses.Count)
                    continue;

                var pointers = phi.Operands.Skip(1).Cast<LocalVariable>().ToList();
                var replaced = false;
                foreach (var (load, offset, size) in reads)
                {
                    var values = new List<IOperand>();
                    for (var i = 0; i < block.Predecessors.Count; i++)
                    {
                        var predecessor = block.Predecessors[i];
                        var pointer = pointers[i];
                        var value = NewLocal(method, "through", null);

                        var at = predecessor.Instructions.Count;
                        if (at > 0 && predecessor.Instructions[^1].OpCode is OpCode.Jump or OpCode.ConditionalJump)
                            at--;

                        predecessor.Instructions.Insert(at, new Instruction(load.Index, OpCode.Move, value, new MemoryOperand(pointer, addend: offset, size: size)));
                        values.Add(value);
                    }

                    var mergedValue = NewLocal(method, "merged", null);
                    if (!replaced)
                    {
                        phi.SetOperands([mergedValue, ..values]);
                        replaced = true;
                    }
                    else
                        block.Instructions.Insert(block.Instructions.IndexOf(phi) + 1, new Instruction(-1, OpCode.Phi, [mergedValue, ..values]));

                    load.SetOperand(1, mergedValue);
                }

                changed = true;
            }
        }

        return changed;
    }

    private static LocalVariable NewLocal(MethodAnalysisContext method, string name, TypeAnalysisContext? type)
    {
        var local = new LocalVariable($"{name}{method.Locals.Count}", new Register(null, $"{name.ToUpperInvariant()}_{method.Locals.Count}", 0), type);
        method.Locals.Add(local);
        return local;
    }
}
