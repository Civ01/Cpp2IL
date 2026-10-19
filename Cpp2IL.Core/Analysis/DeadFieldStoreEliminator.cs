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

    /// <summary>
    /// MSVC zeroes a struct's slot before building the struct in it (an async state machine before its fields are set,
    /// say), which reads as stores of zero to the struct or its fields. IL locals start out zeroed, so while nothing else
    /// has touched the local on any way here from the start, such a store changes nothing and goes. (A compiler's
    /// kickoff of a state machine is just the field stores, which is what the decompiler looks for.)
    /// </summary>
    public static void DropPristineZeroing(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;

        static LocalVariable? Owner(IOperand operand) => operand switch
        {
            LocalVariable local => local,
            FieldReference field => field.Local,
            MemoryOperand { Base: LocalVariable memoryBase, Index: null } => memoryBase,
            _ => null,
        };

        static bool IsZero(IOperand operand) => operand is DefaultValue or Immediate { Value: 0 };

        bool IsZeroStore(Instruction instruction, LocalVariable local)
            => instruction is { OpCode: OpCode.Move, Operands: [var destination, var value] } && IsZero(value) && ReferenceEquals(Owner(destination), local)
               && destination is not FieldReference { RootField.IsStatic: true };

        static bool Mentions(Instruction instruction, LocalVariable local)
            => instruction.Operands.Any(o => o switch
            {
                LocalVariable l => ReferenceEquals(l, local),
                FieldReference f => ReferenceEquals(f.Local, local),
                AddressOf { Target: var target } => target is LocalVariable al && ReferenceEquals(al, local) || target is FieldReference af && ReferenceEquals(af.Local, local),
                MemoryOperand m => ReferenceEquals(m.Base, local) || ReferenceEquals(m.Index, local),
                ArrayAccess a => ReferenceEquals(a.Array, local) || a.Index is LocalVariable ai && ReferenceEquals(ai, local),
                ArrayLength { Array: var array } => ReferenceEquals(array, local),
                _ => false,
            });

        // whether only zero stores to the local can come before this point
        bool Pristine(Block block, int before, LocalVariable local)
        {
            var seen = new HashSet<Block> { block };
            var pending = new Stack<(Block Block, int Before)>();
            pending.Push((block, before));
            while (pending.Count > 0)
            {
                var (current, end) = pending.Pop();
                for (var i = 0; i < end; i++)
                    if (Mentions(current.Instructions[i], local) && !IsZeroStore(current.Instructions[i], local))
                        return false;

                if (current == graph.EntryBlock)
                    continue;
                if (current.Predecessors.Count == 0)
                    return false; // (somewhere it can't be told how it got to)

                foreach (var predecessor in current.Predecessors)
                {
                    if (predecessor == block)
                        return false; // round a loop: whatever the rest of it does comes first
                    if (seen.Add(predecessor))
                        pending.Push((predecessor, predecessor.Instructions.Count));
                }
            }

            return true;
        }

        foreach (var block in graph.Blocks)
            for (var index = 0; index < block.Instructions.Count; index++)
            {
                var instruction = block.Instructions[index];
                if (instruction is not { OpCode: OpCode.Move, Operands: [var destination, var value] } || !IsZero(value)
                    || Owner(destination) is not { Type.IsValueType: true } local || local.Type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                    || local.IsThis || method.ParameterLocals.Contains(local) || !IsZeroStore(instruction, local)
                    || !Pristine(block, index, local))
                    continue;

                instruction.OpCode = OpCode.Nop;
                instruction.SetOperands();
            }
    }

    /// <summary>
    /// A struct field zeroed a field at a time (MSVC clearing an async state machine's hoisted local, say) is that field set
    /// to default: <c>x.handle.a = null; x.handle.b = null</c> becomes <c>x.handle = default</c>, when the stores, one after
    /// the other, cover every field of it.
    /// </summary>
    public static void MergeFieldZeroing(MethodAnalysisContext method)
    {
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            var instructions = block.Instructions;
            for (var start = 0; start < instructions.Count; start++)
            {
                if (ZeroedField(instructions[start]) is not { Path.Count: > 0 } first)
                    continue;

                var parentField = first.Path[^1];
                var parentType = parentField.FieldType;
                if (!parentType.IsValueType)
                    continue;

                var definition = (parentType as GenericInstanceTypeAnalysisContext)?.GenericType ?? parentType;
                var wanted = definition.Fields.Where(f => !f.IsStatic).Select(f => f.Name).ToHashSet();
                if (wanted.Count == 0)
                    continue;

                // the run of zero stores to fields of the same struct field
                var run = new List<Instruction>();
                var covered = new HashSet<string>();
                for (var i = start; i < instructions.Count; i++)
                {
                    var instruction = instructions[i];
                    if (instruction.OpCode == OpCode.Nop)
                        continue;
                    if (ZeroedField(instruction) is not { } field || !ReferenceEquals(field.Local, first.Local) || field.Path.Count != first.Path.Count
                        || !field.Path.Select(f => f.Name).SequenceEqual(first.Path.Select(f => f.Name)) || !covered.Add(field.Field.Name))
                        break;
                    run.Add(instruction);
                }

                if (!covered.SetEquals(wanted))
                    continue;

                var whole = new FieldReference(parentField, first.Local, run.Select(r => ((FieldReference)r.Operands[0]).Offset).Min()) { Path = first.Path.GetRange(0, first.Path.Count - 1) };
                run[0].SetOperands(whole, new DefaultValue(parentType));
                foreach (var merged in run.Skip(1))
                {
                    merged.OpCode = OpCode.Nop;
                    merged.SetOperands();
                }
            }
        }

        static FieldReference? ZeroedField(Instruction instruction)
            => instruction is { OpCode: OpCode.Move, Operands: [FieldReference { RootField.IsStatic: false } field, DefaultValue or Immediate { Value: 0 }] } ? field : null;
    }
}
