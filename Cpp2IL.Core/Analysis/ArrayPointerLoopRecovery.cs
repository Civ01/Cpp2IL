using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// MSVC strength-reduces a loop over an array's elements into a pointer that walks them alongside the index:
/// <code>
///   lea r8,[array+20h]          ; &amp;array[0]
/// loop:
///   ... [r8+4] ...              ; array[i].field
///   add r8,18h / inc ecx        ; next element
/// </code>
/// In SSA that's a pair of phis in the loop header, the pointer starting at the first element and stepping by the
/// element size while the index starts at 0 and steps by 1. Accesses through the pointer become accesses to
/// array[index] (for a struct element, through a by-ref local holding its address), and the pointer goes away.
/// Runs in SSA form, as part of the type/field fixpoint (it needs the array's type).
/// </summary>
public static class ArrayPointerLoopRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var elementsOffset = 4L * pointerSize;

        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in graph.Instructions)
            if (instruction.Destination is LocalVariable defined)
                definitions[defined] = instruction;

        var changed = false;

        foreach (var block in graph.Blocks)
        {
            var phis = block.Instructions.Where(i => i.OpCode == OpCode.Phi && i.Operands[0] is LocalVariable).ToList();
            if (phis.Count < 2)
                continue;

            foreach (var pointerPhi in phis)
            {
                var pointer = (LocalVariable)pointerPhi.Operands[0];
                if (pointer.Type is ByRefTypeAnalysisContext)
                    continue;

                SzArrayTypeAnalysisContext? arrayType = null;
                LocalVariable? array = null;
                long elementSize = 0;
                var initialInputs = new List<int>();
                var steps = new List<Instruction>();
                var valid = true;

                for (var input = 1; input < pointerPhi.Operands.Count && valid; input++)
                {
                    if (pointerPhi.Operands[input] is not LocalVariable incoming || !definitions.TryGetValue(incoming, out var definition))
                    {
                        valid = false;
                        break;
                    }

                    switch (definition)
                    {
                        // &array[0]
                        case { OpCode: OpCode.Add, Operands: [_, LocalVariable { Type: SzArrayTypeAnalysisContext type } source, Immediate { Value: var offset }] }
                            when offset == elementsOffset && (array == null || ReferenceEquals(array, source)):
                            array = source;
                            arrayType = type;
                            initialInputs.Add(input);
                            break;
                        // pointer += element size
                        case { OpCode: OpCode.Add, Operands: [_, LocalVariable stepped, Immediate { Value: > 0 and < 0x1000 and var step }] }
                            when ReferenceEquals(stepped, pointer) && (elementSize == 0 || elementSize == step):
                            elementSize = step;
                            steps.Add(definition);
                            break;
                        default:
                            valid = false;
                            break;
                    }
                }

                if (!valid || array == null || arrayType == null || initialInputs.Count == 0 || steps.Count == 0)
                    continue;

                var elementType = arrayType.ElementType;
                var expectedSize = elementType.IsValueType ? TypeSizes.StorageSize(elementType, pointerSize) : pointerSize;
                if (expectedSize != elementSize)
                    continue;

                // the matching index: 0 where the pointer starts, +1 where it steps
                var index = phis.Where(p => p != pointerPhi).Select(p => (LocalVariable?)p.Operands[0]).FirstOrDefault(candidate =>
                {
                    var indexPhi = phis.First(p => ReferenceEquals(p.Operands[0], candidate));
                    if (indexPhi.Operands.Count != pointerPhi.Operands.Count)
                        return false;

                    for (var input = 1; input < indexPhi.Operands.Count; input++)
                    {
                        var operand = indexPhi.Operands[input];
                        if (initialInputs.Contains(input))
                        {
                            if (!(operand is Immediate { Value: 0 } || operand is LocalVariable zero && definitions.TryGetValue(zero, out var zeroDefinition)
                                    && zeroDefinition is { OpCode: OpCode.Move, Operands: [_, Immediate { Value: 0 }] }))
                                return false;
                        }
                        else if (operand is not LocalVariable next || !definitions.TryGetValue(next, out var nextDefinition)
                                 || nextDefinition is not { OpCode: OpCode.Add, Operands: [_, LocalVariable incremented, Immediate { Value: 1 }] }
                                 || !ReferenceEquals(incremented, candidate))
                            return false;
                    }

                    return true;
                });

                if (index == null)
                    continue;

                if (Rewrite(method, block, pointerPhi, pointer, array, elementType, index, steps))
                    changed = true;
            }
        }

        return changed;
    }

    private static bool Rewrite(MethodAnalysisContext method, Graphs.Block header, Instruction pointerPhi, LocalVariable pointer, LocalVariable array,
        TypeAnalysisContext elementType, LocalVariable index, List<Instruction> steps)
    {
        var graph = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        LocalVariable? elementAddress = null;
        var rewritten = false;

        foreach (var instruction in graph.Instructions.ToList())
        {
            if (steps.Contains(instruction) || instruction == pointerPhi)
                continue;

            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.Operands[i] is not MemoryOperand { Base: LocalVariable @base, Index: null } memory || !ReferenceEquals(@base, pointer))
                    continue;

                if (!elementType.IsValueType)
                {
                    if (memory.Addend != 0 || memory.Size is not (0 or 8) || pointerSize != 8)
                        continue;

                    instruction.SetOperand(i, new ArrayAccess(array, index));
                    rewritten = true;
                    continue;
                }

                if (elementAddress == null)
                {
                    elementAddress = new LocalVariable($"element{method.Locals.Count}", new Register(null, $"ELEMENT_{method.Locals.Count}", 0),
                        new ByRefTypeAnalysisContext(elementType));
                    method.Locals.Add(elementAddress);

                    var insertAt = header.Instructions.FindLastIndex(x => x.OpCode == OpCode.Phi) + 1;
                    header.Instructions.Insert(insertAt, new Instruction(pointerPhi.Index, OpCode.Move, elementAddress, new AddressOf(new ArrayAccess(array, index))));
                }

                memory.Base = elementAddress;
                instruction.SetOperand(i, memory);
                rewritten = true;
            }
        }

        if (!rewritten)
            return false;

        // it indexes an array, so it's an int whatever it got guessed as
        if (index.Type?.FullName is not ("System.Int32" or "System.Int64" or "System.UInt32" or "System.IntPtr"))
            index.Type = method.AppContext.SystemTypes.SystemInt32Type;

        // the pointer is dead if all that's left is its own stepping
        var stillUsed = graph.Instructions.Any(instruction => instruction != pointerPhi && !steps.Contains(instruction)
                                                              && instruction.Operands.Any(operand => Mentions(operand, pointer)));
        if (!stillUsed && steps.All(step => !graph.Instructions.Any(other => other != pointerPhi && other.Operands.Any(operand => Mentions(operand, step.Operands[0])))))
        {
            foreach (var step in steps)
            {
                step.OpCode = OpCode.Nop;
                step.SetOperands();
            }

            pointerPhi.OpCode = OpCode.Nop;
            pointerPhi.SetOperands();
        }

        return true;
    }

    private static bool Mentions(IOperand operand, IOperand local) => operand switch
    {
        LocalVariable direct => ReferenceEquals(direct, local),
        MemoryOperand memory => ReferenceEquals(memory.Base, local) || ReferenceEquals(memory.Index, local),
        AddressOf { Target: var target } => Mentions(target, local),
        _ => false
    };
}
