using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// <c>var a = flag ? this.accelerationA : this.accelerationB</c> compiles to picking the field's offset in each branch
/// (mov eax,34h / mov eax,4Ch) and one load of <c>[this + offset]</c> where they meet. That load, at the start of the
/// block the offsets merge in, becomes a phi of loads of each field at the end of each branch, which then resolve as
/// ordinary field reads. Runs in SSA form, before types and fields are resolved.
/// </summary>
public static class SelectedFieldLoads
{
    public static void Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var definitions = new Dictionary<LocalVariable, Instruction>();
        var blockOf = new Dictionary<Instruction, Block>();
        foreach (var block in graph.Blocks)
            foreach (var instruction in block.Instructions)
            {
                blockOf[instruction] = block;
                if (instruction.Destination is LocalVariable defined)
                    definitions[defined] = instruction;
            }

        var counter = 0;
        foreach (var block in graph.Blocks)
        {
            var predecessors = block.Predecessors;
            if (predecessors.Count < 2 || predecessors.Any(p => p.Successors.Contains(block) == false))
                continue;

            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var load = block.Instructions[i];
                if (load is not { OpCode: OpCode.Move, Operands: [LocalVariable loaded, MemoryOperand { Scale: 0 or 1 } memory] })
                {
                    // only loads before anything that could change memory
                    if (load.IsCall || load.Destination is MemoryOperand or FieldReference or ArrayAccess)
                        break;
                    continue;
                }

                if (Split(memory, definitions) is not { } candidates
                    || candidates.Select(c => (c.Selector, c.Owner, Offsets: Offsets(c.Selector, block, predecessors, definitions)))
                        .FirstOrDefault(c => c.Offsets != null && !(definitions.TryGetValue(c.Owner, out var ownerDefinition) && blockOf.GetValueOrDefault(ownerDefinition) == block))
                        is not { Offsets: { } offsets, Owner: var owner })
                    continue;

                // a load of each field at the end of each branch, merged where the load was
                var phi = new Instruction(load.Index, OpCode.Phi, loaded);
                for (var k = 0; k < predecessors.Count; k++)
                {
                    var predecessor = predecessors[k];
                    var field = new LocalVariable($"selected{counter}_{k}", new Register(null, $"SELECTED_{counter}_{k}", 0));
                    method.Locals.Add(field);

                    var read = new Instruction(load.Index, OpCode.Move, field, new MemoryOperand(owner, null, memory.Addend + offsets[k], 0, memory.Size));
                    var jumpAt = predecessor.Instructions.FindIndex(x => x.OpCode is OpCode.Jump or OpCode.ConditionalJump);
                    var end = jumpAt >= 0 ? jumpAt : predecessor.Instructions.Count;
                    predecessor.Instructions.Insert(end, read);
                    phi.AddOperands([field]);
                }

                block.Instructions.RemoveAt(i);
                block.Instructions.Insert(block.Instructions.TakeWhile(x => x.OpCode is OpCode.Phi or OpCode.Nop).Count(), phi);
                definitions[loaded] = phi;
                counter++;
            }
        }
    }

    // [offset + obj] or [obj + offset], or [address] with address = offset + obj: the ways round it may be the selector
    // and the object
    private static List<(LocalVariable Selector, LocalVariable Owner)>? Split(MemoryOperand memory, Dictionary<LocalVariable, Instruction> definitions)
    {
        if (memory is { Base: LocalVariable first, Index: LocalVariable second })
            return [(first, second), (second, first)];

        if (memory is { Base: LocalVariable address, Index: null } && definitions.TryGetValue(address, out var sum)
            && sum is { OpCode: OpCode.Add, Operands: [_, LocalVariable left, LocalVariable right] })
            return [(left, right), (right, left)];

        return null;
    }

    // the selector is a phi here of a constant from each branch
    private static List<long>? Offsets(LocalVariable selector, Block block, List<Block> predecessors, Dictionary<LocalVariable, Instruction> definitions)
    {
        if (!definitions.TryGetValue(selector, out var phi) || phi.OpCode != OpCode.Phi || !block.Instructions.Contains(phi)
            || phi.Operands.Count != predecessors.Count + 1)
            return null;

        var offsets = new List<long>();
        foreach (var operand in phi.Operands.Skip(1))
        {
            var value = operand;
            for (var depth = 0; depth < 4 && value is LocalVariable local && definitions.TryGetValue(local, out var definition)
                                && definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable or Immediate] }; depth++)
                value = definition.Operands[1];

            if (value is not Immediate { Value: > 0 and < 0x10000 } constant)
                return null;
            offsets.Add(constant.Value);
        }

        return offsets;
    }
}
