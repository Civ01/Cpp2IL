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
    public static System.Action<string>? Debug;

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
                long? startOffset = null;

                for (var input = 1; input < pointerPhi.Operands.Count && valid; input++)
                {
                    if (pointerPhi.Operands[input] is not LocalVariable incoming || !definitions.TryGetValue(incoming, out var definition))
                    {
                        valid = false;
                        break;
                    }

                    switch (definition)
                    {
                        // &array[k]
                        case { OpCode: OpCode.Add, Operands: [_, LocalVariable { Type: SzArrayTypeAnalysisContext type } source, Immediate { Value: var offset }] }
                            when offset >= elementsOffset && (array == null || ReferenceEquals(array, source)) && (startOffset == null || startOffset == offset):
                            array = source;
                            arrayType = type;
                            startOffset = offset;
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

                Debug?.Invoke($"pointer phi {pointerPhi}: valid={valid} array={array} steps={steps.Count} size={elementSize}");
                if (!valid || array == null || arrayType == null || initialInputs.Count == 0 || steps.Count == 0)
                    continue;

                var elementType = arrayType.ElementType;
                var expectedSize = elementType.IsValueType ? TypeSizes.StorageSize(elementType, pointerSize) : pointerSize;
                if (expectedSize != elementSize || startOffset == null || (startOffset.Value - elementsOffset) % elementSize != 0)
                    continue;

                // the element the pointer starts at
                var startIndex = (startOffset.Value - elementsOffset) / elementSize;

                // the matching index: the start element where the pointer starts, +1 where it steps
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
                            if (!(operand is Immediate { Value: var immediate } && immediate == startIndex
                                  || operand is LocalVariable first && ChaseCopies(definitions, first) is { OpCode: OpCode.Move, Operands: [_, Immediate { Value: var copied }] } && copied == startIndex))
                                return false;
                        }
                        else if (operand is not LocalVariable next || !definitions.TryGetValue(next, out var nextDefinition)
                                 || nextDefinition is not { OpCode: OpCode.Add, Operands: [_, LocalVariable incremented, Immediate { Value: 1 }] }
                                 || !ReferenceEquals(incremented, candidate))
                            return false;
                    }

                    return true;
                });

                Debug?.Invoke($"  index {index}");

                // no counter alongside it (the loop compares against an end pointer): make one
                if (index == null)
                {
                    if (steps.Count != 1 || !UsedOnlyAsElementPointer(graph, pointer, pointerPhi, steps))
                        continue;

                    var int32 = method.AppContext.SystemTypes.SystemInt32Type;
                    var synthesized = NewLocal(method, "index", int32);
                    var next = NewLocal(method, "nextIndex", int32);
                    var operands = new List<IOperand> { synthesized };
                    for (var input = 1; input < pointerPhi.Operands.Count; input++)
                    {
                        if (initialInputs.Contains(input))
                        {
                            var zero = NewLocal(method, "startIndex", int32);
                            var startDefinition = definitions[(LocalVariable)pointerPhi.Operands[input]];
                            var startBlock = graph.Blocks.First(b => b.Instructions.Contains(startDefinition));
                            startBlock.Instructions.Insert(startBlock.Instructions.IndexOf(startDefinition) + 1, new Instruction(startDefinition.Index, OpCode.Move, zero, new Immediate(startIndex)));
                            operands.Add(zero);
                        }
                        else
                            operands.Add(next);
                    }

                    block.Instructions.Insert(block.Instructions.IndexOf(pointerPhi) + 1, new Instruction(pointerPhi.Index, OpCode.Phi, operands));
                    var stepBlock = graph.Blocks.First(b => b.Instructions.Contains(steps[0]));
                    stepBlock.Instructions.Insert(stepBlock.Instructions.IndexOf(steps[0]) + 1, new Instruction(steps[0].Index, OpCode.Add, next, synthesized, new Immediate(1)));
                    index = synthesized;
                }

                if (Rewrite(method, block, pointerPhi, pointer, array, elementType, index, steps))
                    changed = true;
            }
        }

        changed |= RecoverOffsetLoops(method, definitions);
        changed |= RecoverScaledOffsets(method, definitions);
        return changed;
    }

    /// <summary>
    /// An element whose size isn't a scale x86 addressing has (12, 56, ...) is reached through a byte offset computed
    /// separately: <c>off = i * 56; [array + off + 0x20 + k]</c>. That's element i (plus however many whole elements k
    /// spans), or a field of it.
    /// </summary>
    private static bool RecoverScaledOffsets(MethodAnalysisContext method, Dictionary<LocalVariable, Instruction> definitions)
    {
        var graph = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var elementsOffset = 4L * pointerSize;
        var changed = false;

        foreach (var block in graph.Blocks)
        {
            for (var at = 0; at < block.Instructions.Count; at++)
            {
                var instruction = block.Instructions[at];
                for (var operandIndex = 0; operandIndex < instruction.Operands.Count; operandIndex++)
                {
                    if (instruction.Operands[operandIndex] is not MemoryOperand { Scale: 0 or 1, Base: LocalVariable first, Index: LocalVariable second } memory)
                        continue;

                    var (array, offset) = first.Type is SzArrayTypeAnalysisContext ? (first, second) : second.Type is SzArrayTypeAnalysisContext ? (second, first) : (null, null);
                    if (array?.Type is not SzArrayTypeAnalysisContext { ElementType: var elementType } || offset == null
                        || ScaledIndex(offset, definitions) is not var (index, scale))
                        continue;

                    var elementSize = elementType.IsValueType ? TypeSizes.StorageSize(elementType, pointerSize) : pointerSize;
                    if (elementSize <= 0 || scale != elementSize)
                        continue;

                    var position = memory.Addend - elementsOffset;
                    var element = FloorDiv(position, elementSize);
                    var inner = position - element * elementSize;
                    var whole = inner == 0 && (memory.Size == 0 || memory.Size == elementSize);
                    var field = elementType.IsValueType && memory.Size > 0 && inner + memory.Size <= elementSize && !whole;
                    if (!whole && !field)
                        continue;

                    IOperand elementIndex = index;
                    if (element != 0)
                    {
                        var shifted = NewLocal(method, "elementIndex", method.AppContext.SystemTypes.SystemInt32Type);
                        block.Instructions.Insert(at++, new Instruction(instruction.Index, OpCode.Add, shifted, index, new Immediate(element)));
                        elementIndex = shifted;
                    }

                    var access = new ArrayAccess(array, elementIndex);
                    if (whole)
                        instruction.SetOperand(operandIndex, access);
                    else
                    {
                        var reference = NewLocal(method, "element", elementType.MakeByReferenceType());
                        block.Instructions.Insert(at++, new Instruction(instruction.Index, OpCode.Move, reference, new AddressOf(access)));
                        instruction.SetOperand(operandIndex, new MemoryOperand(reference, null, inner, 0, memory.Size));
                    }

                    changed = true;
                }
            }
        }

        return changed;
    }

    // offset = index * scale (or index << n), possibly through copies or a widening
    private static (IOperand Index, long Scale)? ScaledIndex(LocalVariable offset, Dictionary<LocalVariable, Instruction> definitions)
    {
        var definition = definitions.GetValueOrDefault(offset);
        for (var hops = 0; hops < 4 && definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] }; hops++)
            definition = definitions.GetValueOrDefault(copied);

        return definition switch
        {
            { OpCode: OpCode.Multiply, Operands: [_, LocalVariable index, Immediate { Value: > 1 and < 0x10000 and var by }] } => (index, by),
            { OpCode: OpCode.Multiply, Operands: [_, Immediate { Value: > 1 and < 0x10000 and var by }, LocalVariable index] } => (index, by),
            { OpCode: OpCode.ShiftLeft, Operands: [_, LocalVariable index, Immediate { Value: > 0 and < 16 and var shift }] } => (index, 1L << (int)shift),
            _ => null,
        };
    }

    /// <summary>
    /// The other strength reduction: a byte offset that starts at the first element (0x20) and steps by the element size,
    /// added to the array at each access (<c>mov rax,[rdi+rcx]</c> with rdi = 20h, 28h, ...). Works for every array the
    /// loop indexes in step. The accesses become array[i] with a fresh index counting 0, 1, ...
    /// </summary>
    private static bool RecoverOffsetLoops(MethodAnalysisContext method, Dictionary<LocalVariable, Instruction> definitions)
    {
        var graph = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var elementsOffset = 4L * pointerSize;
        var changed = false;

        foreach (var block in graph.Blocks.ToList())
        {
            foreach (var phi in block.Instructions.Where(i => i.OpCode == OpCode.Phi && i.Operands[0] is LocalVariable).ToList())
            {
                var offset = (LocalVariable)phi.Operands[0];
                long? step = null, start = null;
                var steps = new List<(Instruction Step, int Input)>();
                var starts = new List<int>();
                var startDefinitions = new Dictionary<int, Instruction>();
                var valid = true;

                for (var input = 1; input < phi.Operands.Count && valid; input++)
                {
                    var incoming = phi.Operands[input];
                    var definition = incoming is LocalVariable local ? definitions.GetValueOrDefault(local) : null;
                    for (var hops = 0; hops < 4 && definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] }; hops++)
                        definition = definitions.GetValueOrDefault(copied);
                    switch (definition)
                    {
                        // the element header (0x20) is in the start, or in each access ([offset + array + 0x20])
                        case { OpCode: OpCode.Move, Operands: [_, Immediate { Value: var value }] } when value >= 0 && (start == null || start == value):
                            start = value;
                            starts.Add(input);
                            startDefinitions[input] = definition;
                            break;
                        case { OpCode: OpCode.Add, Operands: [_, LocalVariable stepped, Immediate { Value: > 0 and < 0x1000 and var by }] }
                            when ReferenceEquals(stepped, offset) && (step == null || step == by):
                            step = by;
                            steps.Add((definition, input));
                            break;
                        default:
                            valid = false;
                            break;
                    }
                }

                if (!valid || start == null || step == null || starts.Count == 0 || steps.Count == 0
                    || steps.Select(s => s.Step).Distinct().Count() > 1)
                    continue;

                // the element the offset starts at, and how far into it
                var firstElement = FloorDiv(start.Value - elementsOffset, step.Value);
                var firstRemainder = start.Value - elementsOffset - firstElement * step.Value;

                // every access through it must be [array + offset + k] over an array whose elements are that size: the whole of
                // element (i + n), or a field inside it when the elements are structs
                var accesses = new List<(Instruction Instruction, int Operand, LocalVariable Array, long Element, long Inner, int Size)>();
                var otherUse = false;
                foreach (var instruction in graph.Instructions)
                {
                    if (instruction == phi || steps.Any(s => s.Step == instruction))
                        continue;

                    for (var i = 0; i < instruction.Operands.Count; i++)
                    {
                        if (instruction.Operands[i] is not MemoryOperand { Scale: 0 or 1 } memory)
                            continue;

                        LocalVariable? array = null;
                        if (ReferenceEquals(memory.Base, offset) && memory.Index is LocalVariable { Type: SzArrayTypeAnalysisContext } indexArray)
                            array = indexArray;
                        else if (ReferenceEquals(memory.Index, offset) && memory.Base is LocalVariable { Type: SzArrayTypeAnalysisContext } baseArray)
                            array = baseArray;

                        // relative to the element the offset is at: rel bytes on (an access may also reach back, a[i - 1])
                        var rel = firstRemainder + memory.Addend;
                        var delta = FloorDiv(rel, step.Value);
                        var inner = rel - delta * step.Value;
                        var elementType = (array?.Type as SzArrayTypeAnalysisContext)?.ElementType;
                        var elementSize = elementType == null ? 0 : elementType.IsValueType ? TypeSizes.StorageSize(elementType, pointerSize) : pointerSize;
                        var whole = inner == 0 && (memory.Size == 0 || memory.Size == step);
                        var field = elementType is { IsValueType: true } && memory.Size > 0 && inner + memory.Size <= step && !whole;

                        if (array == null || elementSize != step || !(whole || field))
                        {
                            if (Mentions(memory, offset))
                                otherUse = true; // used some other way: leave it all alone
                            continue;
                        }

                        accesses.Add((instruction, i, array, delta, whole ? -1 : inner, memory.Size));
                    }
                }

                if (accesses.Count == 0 || otherUse)
                    continue;

                // the index: phi(first, index + 1) alongside the offset. When every access is to the same element, the index
                // starts there; otherwise at 0, with each access adding its own element number
                // the index counts from the element most accesses are to, the others reaching relative to it
                var usual = accesses.GroupBy(a => a.Element).OrderByDescending(g => g.Count()).ThenBy(g => System.Math.Abs(g.Key)).First().Key;
                var firstIndex = firstElement + usual;
                for (var k = 0; k < accesses.Count; k++)
                    accesses[k] = accesses[k] with { Element = accesses[k].Element - usual };
                var sameElement = accesses.All(a => a.Element == 0);
                var index = NewLocal(method, "index", method.AppContext.SystemTypes.SystemInt32Type);
                var indexOperands = new List<IOperand> { index };
                var nextIndex = NewLocal(method, "nextIndex", method.AppContext.SystemTypes.SystemInt32Type);
                for (var input = 1; input < phi.Operands.Count; input++)
                {
                    if (starts.Contains(input))
                    {
                        var startLocal = NewLocal(method, "startIndex", method.AppContext.SystemTypes.SystemInt32Type);
                        var startDefinition = startDefinitions[input];
                        var startBlock = graph.Blocks.First(b => b.Instructions.Contains(startDefinition));
                        startBlock.Instructions.Insert(startBlock.Instructions.IndexOf(startDefinition) + 1,
                            new Instruction(startDefinition.Index, OpCode.Move, startLocal, new Immediate(firstIndex)));
                        indexOperands.Add(startLocal);
                    }
                    else
                        indexOperands.Add(nextIndex);
                }

                block.Instructions.Insert(block.Instructions.IndexOf(phi) + 1, new Instruction(phi.Index, OpCode.Phi, indexOperands));

                var stepInstruction = steps[0].Step;
                var stepBlock = graph.Blocks.First(b => b.Instructions.Contains(stepInstruction));
                stepBlock.Instructions.Insert(stepBlock.Instructions.IndexOf(stepInstruction) + 1,
                    new Instruction(stepInstruction.Index, OpCode.Add, nextIndex, index, new Immediate(1)));

                foreach (var (instruction, operand, array, element, inner, size) in accesses)
                {
                    var accessBlock = graph.Blocks.First(b => b.Instructions.Contains(instruction));
                    var at = accessBlock.Instructions.IndexOf(instruction);

                    IOperand elementIndex = index;
                    if (!sameElement && element != 0)
                    {
                        var shifted = NewLocal(method, "elementIndex", method.AppContext.SystemTypes.SystemInt32Type);
                        accessBlock.Instructions.Insert(at++, new Instruction(instruction.Index, OpCode.Add, shifted, index, new Immediate(element)));
                        elementIndex = shifted;
                    }

                    var access = new ArrayAccess(array, elementIndex);
                    if (inner < 0)
                    {
                        instruction.SetOperand(operand, access);
                        continue;
                    }

                    // a field of a struct element, through a reference to the element
                    var elementType = ((SzArrayTypeAnalysisContext)array.Type!).ElementType;
                    var reference = NewLocal(method, "element", elementType.MakeByReferenceType());
                    accessBlock.Instructions.Insert(at, new Instruction(instruction.Index, OpCode.Move, reference, new AddressOf(access)));
                    instruction.SetOperand(operand, new MemoryOperand(reference, null, inner, 0, size));
                }

                // the offset is dead if all that's left is its own stepping
                var steppedOffset = (LocalVariable)stepInstruction.Operands[0];
                if (!graph.Instructions.Any(other => other != phi && other != stepInstruction
                                                     && other.Operands.Any(o => Mentions(o, offset) || Mentions(o, steppedOffset))))
                {
                    stepInstruction.OpCode = OpCode.Nop;
                    stepInstruction.SetOperands();
                    phi.OpCode = OpCode.Nop;
                    phi.SetOperands();
                }

                changed = true;
            }
        }

        return changed;
    }

    // The pointer is only dereferenced (so it can be replaced wholesale) - an end-of-loop compare against another pointer
    // would still need it
    private static bool UsedOnlyAsElementPointer(Graphs.ISILControlFlowGraph graph, LocalVariable pointer, Instruction phi, List<Instruction> steps)
    {
        var stepped = steps.Select(s => (LocalVariable)s.Operands[0]).ToList();
        foreach (var instruction in graph.Instructions)
        {
            if (instruction == phi || steps.Contains(instruction))
                continue;

            foreach (var operand in instruction.Operands)
            {
                if (operand is MemoryOperand { Base: var memoryBase, Index: null } && ReferenceEquals(memoryBase, pointer))
                    continue;
                if (Mentions(operand, pointer) || stepped.Any(n => Mentions(operand, n)))
                    return false;
            }
        }

        return true;
    }

    private static Instruction? ChaseCopies(Dictionary<LocalVariable, Instruction> definitions, LocalVariable local)
    {
        var definition = definitions.GetValueOrDefault(local);
        for (var hops = 0; hops < 4 && definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] }; hops++)
            definition = definitions.GetValueOrDefault(copied);
        return definition;
    }

    private static long FloorDiv(long value, long by) => value >= 0 ? value / by : -((-value + by - 1) / by);

    private static LocalVariable NewLocal(MethodAnalysisContext method, string name, TypeAnalysisContext type)
    {
        var local = new LocalVariable($"{name}{method.Locals.Count}", new Register(null, $"{name.ToUpperInvariant()}_{method.Locals.Count}", 0), type);
        method.Locals.Add(local);
        return local;
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
