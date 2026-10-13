using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Turns the raw Il2CppArray layout (header, then length, then inline elements) back into array ops
public static class ArrayRecovery
{
    internal static readonly HashSet<string> ArrayNewFunctions =
    [
        "SzArrayNew",
        "il2cpp_vm_array_new_specific",
        "il2cpp_array_new_specific",
    ];

    // Il2CppArray is {Il2CppObject obj; void* bounds; il2cpp_array_size_t max_length;} then the elements, on all versions(?)
    private static long LengthOffset(int pointerSize) => 3L * pointerSize;
    private static long ElementsOffset(int pointerSize) => 4L * pointerSize;

    public static void Run(MethodAnalysisContext method)
    {
        RecoverElementCopies(method);
        RecoverAccesses(method);
        RecoverStructElementFields(method);
        RecoverStructElementAddresses(method);
        GroupInitialisers(method.ControlFlowGraph!);
    }

    private static void RecoverAccesses(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            RecoverAllocation(instruction);

            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.Operands[i] is not MemoryOperand memory
                    || memory.Base is not LocalVariable { Type: SzArrayTypeAnalysisContext arrayType } array)
                    continue;

                if (memory.Index == null && memory.Scale == 0 && memory.Addend == LengthOffset(pointerSize))
                {
                    instruction.SetOperand(i, new ArrayLength(array));
                    continue;
                }

                if (ElementIndex(memory, arrayType, pointerSize) is { } index)
                    instruction.SetOperand(i, new ArrayAccess(array, index));
                // a whole struct element at a constant index (array initialisers)
                else if (memory is { Index: null, Scale: 0 } && arrayType.ElementType is { IsValueType: true } structElement
                         && MetadataElementSize(structElement, pointerSize) is > 0 and var structSize && memory.Size == structSize
                         && memory.Addend - ElementsOffset(pointerSize) is >= 0 and var structOffset && structOffset % structSize == 0)
                    instruction.SetOperand(i, new ArrayAccess(array, new Immediate(structOffset / structSize)));
            }
        }
    }

    // A field of a struct element whose size isn't an addressing scale: [arr + (i*3)*4 + 0x20 + 8] is arr[i].z of a Vector3[].
    // The element's address goes in a temporary, and the field is read or written through it.
    private static void RecoverStructElementFields(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var definitions = SingleDefinitions(method.ControlFlowGraph!);

        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            for (var at = 0; at < block.Instructions.Count; at++)
            {
                var instruction = block.Instructions[at];
                for (var i = 0; i < instruction.Operands.Count; i++)
                {
                    if (instruction.Operands[i] is not MemoryOperand { Base: LocalVariable { Type: SzArrayTypeAnalysisContext { ElementType: { IsValueType: true } elementType } } array, Size: > 0 } memory
                        || MetadataResolver.IsPrimitiveOrEnum(elementType))
                        continue;
                    var elementSize = MetadataElementSize(elementType, pointerSize);
                    if (elementSize <= 0)
                        continue;

                    var indexAffine = memory.Index is LocalVariable indexLocal
                        ? ScaleBy(Evaluate(indexLocal, definitions, 0), Math.Max(memory.Scale, 1))
                        : new Affine(null, 0, 0);
                    if (Sum(indexAffine, new Affine(null, 0, memory.Addend)) is not { } address || ReferenceEquals(address.Root, array))
                        continue;

                    var offset = address.Offset - ElementsOffset(pointerSize);
                    IOperand index;
                    long fieldOffset;
                    if (address.Root != null)
                    {
                        if (address.Multiplier != elementSize || offset < 0 || offset >= elementSize)
                            continue;
                        index = address.Root;
                        fieldOffset = offset;
                    }
                    else
                    {
                        // a store at a constant index is an initialiser, made of chunked copies of a struct built elsewhere,
                        // which don't line up with the element's fields
                        if (offset < 0 || i == 0 && instruction.OpCode == OpCode.Move)
                            continue;
                        index = new Immediate(offset / elementSize);
                        fieldOffset = offset % elementSize;
                    }

                    var chain = elementType is GenericInstanceTypeAnalysisContext generic
                        ? GenericInstanceFieldLayout.FindFieldChain(generic, fieldOffset, memory.Size, pointerSize)
                        : MetadataResolver.FindFieldChain(elementType, false, fieldOffset, memory.Size, pointerSize);
                    if (chain == null)
                        continue;

                    var element = new LocalVariable($"element{method.Locals.Count}", new Register(null, $"ELEMENT_{method.Locals.Count}", 0), elementType.MakeByReferenceType());
                    method.Locals.Add(element);
                    block.Instructions.Insert(at, new Instruction(instruction.Index, OpCode.Move, element, new AddressOf(new ArrayAccess(array, index))));
                    at++;
                    instruction.SetOperand(i, new FieldReference(chain[^1], element, (int)fieldOffset) { Path = chain.GetRange(0, chain.Count - 1) });
                }
            }
        }
    }

    // keys[0] = keyframe for a 28 byte Keyframe is copied in chunks (16 + 8 + 4 bytes) from the local into the element.
    // Chunks from one struct local that together cover exactly one element become that one element store.
    private static void RecoverElementCopies(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var elementsOffset = ElementsOffset(pointerSize);

        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            for (var start = 0; start < block.Instructions.Count; start++)
            {
                if (ElementChunk(block.Instructions[start], pointerSize, elementsOffset) is not var (array, element, source, elementSize, _, _))
                    continue;

                var covered = new SortedDictionary<long, long>();
                var chunks = new List<Instruction>();
                for (var at = start; at < block.Instructions.Count && at < start + 12; at++)
                {
                    var instruction = block.Instructions[at];
                    if (ElementChunk(instruction, pointerSize, elementsOffset) is var (chunkArray, chunkElement, chunkSource, _, offset, size)
                        && ReferenceEquals(chunkArray, array) && chunkElement == element && ReferenceEquals(chunkSource, source))
                    {
                        if (covered.ContainsKey(offset))
                            break;
                        covered[offset] = size;
                        chunks.Add(instruction);
                        continue;
                    }

                    // anything else touching the struct or the array ends the run
                    if (instruction.Operands.Any(o => ReferencesLocal(o, source) || ReferencesLocal(o, array)) || instruction.IsCall)
                        break;
                }

                // the chunks tile the element exactly
                long position = 0;
                foreach (var (offset, size) in covered)
                {
                    if (offset != position)
                        break;
                    position += size;
                }
                if (position != elementSize || covered.Values.Sum() != elementSize)
                    continue;

                chunks[0].SetOperands(new ArrayAccess(array, new Immediate(element)), source);
                foreach (var chunk in chunks.Skip(1))
                {
                    chunk.OpCode = OpCode.Nop;
                    chunk.SetOperands();
                }
            }
        }
    }

    private static bool ReferencesLocal(IOperand operand, LocalVariable local) => operand switch
    {
        LocalVariable l => ReferenceEquals(l, local),
        MemoryOperand m => ReferenceEquals(m.Base, local) || ReferenceEquals(m.Index, local),
        FieldReference f => ReferenceEquals(f.Local, local),
        AddressOf { Target: var target } => ReferencesLocal(target, local),
        _ => false,
    };

    // Move [arr + 0x20 + k*size + offset]:n, (a piece of) struct local: (arr, k, local, element size, offset, n)
    private static (LocalVariable Array, long Element, LocalVariable Source, long ElementSize, long Offset, long Size)? ElementChunk(Instruction instruction, int pointerSize, long elementsOffset)
    {
        if (instruction is not { OpCode: OpCode.Move, Operands: [MemoryOperand { Base: LocalVariable { Type: SzArrayTypeAnalysisContext { ElementType: { IsValueType: true } elementType } } array, Index: null, Size: > 0 } destination, var value] }
            || MetadataResolver.IsPrimitiveOrEnum(elementType))
            return null;

        var elementSize = MetadataElementSize(elementType, pointerSize);
        if (elementSize <= 0 || destination.Addend < elementsOffset)
            return null;

        var element = (destination.Addend - elementsOffset) / elementSize;
        var offset = (destination.Addend - elementsOffset) % elementSize;

        switch (value)
        {
            case MemoryOperand { Base: LocalVariable { Type: { } sourceType } source, Index: null } piece
                when sourceType == elementType && piece.Addend == offset && piece.Size == destination.Size:
                return (array, element, source, elementSize, offset, destination.Size);
            case FieldReference { Local: { Type: { } fieldOwner } source, Path.Count: 0 } field
                when fieldOwner == elementType && field.Offset == offset && TypeSizes.StorageSize(field.Field.FieldType, pointerSize) == destination.Size:
                return (array, element, source, elementSize, offset, destination.Size);
            default:
                return null;
        }
    }

    // Group initializers after an array allocation together so ILSpy decompiles them better
    private static void GroupInitialisers(ISILControlFlowGraph cfg)
    {
        var movedAny = false;

        foreach (var block in cfg.Blocks.ToList())
        {
            foreach (var allocation in block.Instructions.ToList())
            {
                if (allocation.OpCode != OpCode.NewArr || allocation.Operands[0] is not LocalVariable array)
                    continue;

                var stores = new List<(Block Block, Instruction Instruction)>();
                var current = block;
                var index = current.Instructions.IndexOf(allocation) + 1;

                while (true)
                {
                    if (index >= current.Instructions.Count)
                    {
                        // only a straight-line run can be regrouped without changing what runs when
                        if (current.Successors.Count != 1 || current.Successors[0].Predecessors.Count != 1)
                            break;

                        current = current.Successors[0];
                        index = 0;
                        continue;
                    }

                    var instruction = current.Instructions[index];

                    if (IsElementStore(instruction, array))
                    {
                        stores.Add((current, instruction));
                        index++;
                        continue;
                    }

                    if (!ReadsArray(instruction, array))
                    {
                        index++;
                        continue;
                    }

                    // Found the first read. Move the allocation and its stores immediately in front, so the whole array is built in one chain with the elements already computed.
                    if (stores.Count > 1)
                    {
                        foreach (var (storeBlock, store) in stores)
                            storeBlock.Instructions.Remove(store);

                        block.Instructions.Remove(allocation);

                        var moved = new List<Instruction> { allocation };
                        moved.AddRange(stores.Select(s => s.Instruction));

                        // a constructor call is emitted where its object was allocated (newobj): in front of that
                        var insertAt = current.Instructions.IndexOf(instruction);
                        if (instruction is { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor" }, LocalVariable constructed, ..] })
                        {
                            var allocationIndex = current.Instructions.FindLastIndex(insertAt, i => i is { OpCode: OpCode.Newobj, Operands: [LocalVariable allocated, ..] } && ReferenceEquals(allocated, constructed));
                            if (allocationIndex >= 0)
                                insertAt = allocationIndex;
                        }

                        current.Instructions.InsertRange(insertAt, moved);
                        movedAny = true;
                    }

                    break;
                }
            }
        }

        // Emptying a block out entirely leaves branches pointing at nothing to jump to
        if (movedAny)
            cfg.RemoveEmptyBlocks();
    }

    private static bool IsElementStore(Instruction instruction, LocalVariable array) =>
        instruction.OpCode == OpCode.Move && instruction.Operands[0] is ArrayAccess { Index: Immediate } stored
                                          && ReferenceEquals(stored.Array, array)
                                          && !ReadsArray(instruction, array);

    private static bool ReadsArray(Instruction instruction, LocalVariable array)
    {
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            if (i == 0 && instruction.OpCode == OpCode.Move)
                continue;

            var reads = instruction.Operands[i] switch
            {
                LocalVariable local => ReferenceEquals(local, array),
                ArrayAccess access => ReferenceEquals(access.Array, array),
                ArrayLength length => ReferenceEquals(length.Array, array),
                MemoryOperand memory => ReferenceEquals(memory.Base, array) || ReferenceEquals(memory.Index, array),
                AddressOf { Target: LocalVariable addressed } => ReferenceEquals(addressed, array),
                _ => false
            };

            if (reads)
                return true;
        }

        return false;
    }

    private static void RecoverAllocation(Instruction instruction)
    {
        // Call "SzArrayNew", result, typeof(T[]), length, ...
        if (!instruction.IsCall || instruction.Operands is not [StringLiteral { Value: var name }, LocalVariable result, TypeAnalysisContext type, { } length, ..]
            || !ArrayNewFunctions.Contains(name))
            return;

        instruction.OpCode = OpCode.NewArr;
        instruction.SetOperands(result, type, length);

        if (result.Type is not SzArrayTypeAnalysisContext)
            result.Type = type;
    }

    private static IOperand? ElementIndex(MemoryOperand memory, SzArrayTypeAnalysisContext arrayType, int pointerSize)
    {
        var elementSize = ElementSize(arrayType.ElementType, pointerSize);
        var offset = memory.Addend - ElementsOffset(pointerSize);

        if (offset < 0 || elementSize == 0 || offset % elementSize != 0)
            return null;

        if (memory.Index == null)
            return memory.Scale == 0 ? new Immediate(offset / elementSize) : null;

        return memory.Scale == elementSize && offset == 0 ? memory.Index : null;
    }

    private static long ElementSize(TypeAnalysisContext elementType, int pointerSize)
    {
        if (!elementType.IsValueType)
            return pointerSize;

        return elementType.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => 1,
            "System.Int16" or "System.UInt16" or "System.Char" => 2,
            "System.Int32" or "System.UInt32" or "System.Single" => 4,
            "System.Int64" or "System.UInt64" or "System.Double" => 8,
            "System.IntPtr" or "System.UIntPtr" => pointerSize,
            _ => 0 // struct arrays are handled by the element-address path, which sizes them from metadata
        };
    }

    // Recovers &array[i] over struct arrays. Struct elements are never loaded outright, the compiler
    // computes their address via lea chains and calls through it. We solve the index as a linear function
    // of a local and demand an exact hit on the metadata stride, so a real load can't match by accident.
    private static void RecoverStructElementAddresses(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var cfg = method.ControlFlowGraph!;

        var definitions = SingleDefinitions(cfg);
        var uses = CollectUses(cfg);

        foreach (var instruction in cfg.Instructions)
        {
            if (instruction.IsCall)
            {
                for (var i = 1; i < instruction.Operands.Count; i++)
                {
                    if (MatchElementAddress(instruction.Operands[i], pointerSize, definitions) is { } inlined)
                        instruction.SetOperand(i, inlined);
                }

                continue;
            }

            // a Move from memory could be a load or a lifted lea, and only the uses tell them apart
            if (instruction is not { OpCode: OpCode.Move, Operands: [LocalVariable destination, MemoryOperand] })
                continue;

            if (definitions.TryGetValue(destination, out var single) && single == null)
                continue;

            if (!uses.TryGetValue(destination, out var destinationUses) || destinationUses.Count == 0
                || !destinationUses.All(u => u.Instruction.IsCall || IsMemoryBase(u.Instruction.Operands[u.OperandIndex], destination)))
                continue;

            if (MatchElementAddress(instruction.Operands[1], pointerSize, definitions) is { } address)
                instruction.SetOperand(1, address);
        }
    }

    private static AddressOf? MatchElementAddress(IOperand operand, int pointerSize, Dictionary<LocalVariable, Instruction?> definitions)
    {
        if (operand is not MemoryOperand memory
            || memory.Base is not LocalVariable { Type: SzArrayTypeAnalysisContext arrayType } array)
            return null;

        var elementType = arrayType.ElementType;
        if (!elementType.IsValueType || ElementSize(elementType, pointerSize) != 0)
            return null;

        var elementSize = MetadataElementSize(elementType, pointerSize);
        if (elementSize <= 0)
            return null;

        return StructElementIndex(memory, array, elementSize, pointerSize, definitions) is { } index
            ? new AddressOf(new ArrayAccess(array, index))
            : null;
    }

    private static bool IsMemoryBase(IOperand operand, LocalVariable local)
        => operand is MemoryOperand { Base: LocalVariable baseLocal } && ReferenceEquals(baseLocal, local);

    private static long MetadataElementSize(TypeAnalysisContext elementType, int pointerSize)
        => TypeSizes.UnboxedSize(elementType, pointerSize);

    private static IOperand? StructElementIndex(MemoryOperand memory, LocalVariable array, long elementSize, int pointerSize,
        Dictionary<LocalVariable, Instruction?> definitions)
    {
        var indexAffine = memory.Index is LocalVariable indexLocal
            ? ScaleBy(Evaluate(indexLocal, definitions, 0), Math.Max(memory.Scale, 1))
            : new Affine(null, 0, 0);

        if (Sum(indexAffine, new Affine(null, 0, memory.Addend)) is not { } address)
            return null;

        if (ReferenceEquals(address.Root, array))
            return null;

        var offset = address.Offset - ElementsOffset(pointerSize);

        if (address.Root != null)
            return address.Multiplier == elementSize && offset == 0 ? address.Root : null;

        return offset >= 0 && offset % elementSize == 0 ? new Immediate(offset / elementSize) : null;
    }

    // value = Multiplier * Root + Offset (a null Root means it's just a constant)
    private readonly record struct Affine(IOperand? Root, long Multiplier, long Offset);

    private static Affine? Evaluate(IOperand operand, Dictionary<LocalVariable, Instruction?> definitions, int depth)
    {
        if (depth > 8)
            return null;

        switch (operand)
        {
            case Immediate { Value: var value }:
                return new Affine(null, 0, value);

            // a field read forwarded into the arithmetic: a value of its own
            case FieldReference field:
                return new Affine(field, 1, 0);

            case LocalVariable local:
            {
                if (!definitions.TryGetValue(local, out var definition) || definition == null)
                    return new Affine(local, 1, 0);

                return definition switch
                {
                    { OpCode: OpCode.Move, Operands: [_, MemoryOperand lea] } => EvaluateLea(lea, definitions, depth + 1),
                    { OpCode: OpCode.Move, Operands: [_, LocalVariable or Immediate] } => Evaluate(definition.Operands[1], definitions, depth + 1),
                    { OpCode: OpCode.Move } => new Affine(local, 1, 0), // loaded from somewhere: a value of its own
                    { OpCode: OpCode.Add, Operands: [_, var left, var right] } => Sum(Evaluate(left, definitions, depth + 1), Evaluate(right, definitions, depth + 1)),
                    { OpCode: OpCode.ShiftLeft, Operands: [_, var left, Immediate { Value: >= 0 and < 32 } shift] } => ScaleBy(Evaluate(left, definitions, depth + 1), 1L << (int)shift.Value),
                    { OpCode: OpCode.Multiply, Operands: [_, var left, Immediate factor] } => ScaleBy(Evaluate(left, definitions, depth + 1), factor.Value),
                    _ => new Affine(local, 1, 0)
                };
            }

            default:
                return null;
        }
    }

    private static Affine? EvaluateLea(MemoryOperand lea, Dictionary<LocalVariable, Instruction?> definitions, int depth)
    {
        var result = (Affine?)new Affine(null, 0, lea.Addend);

        if (lea.Base != null)
            result = Sum(result, Evaluate(lea.Base, definitions, depth));

        if (lea.Index != null)
            result = Sum(result, ScaleBy(Evaluate(lea.Index, definitions, depth), Math.Max(lea.Scale, 1)));

        return result;
    }

    private static Affine? Sum(Affine? left, Affine? right)
    {
        if (left is not { } l || right is not { } r)
            return null;

        if (l.Root != null && r.Root != null && !SameRoot(l.Root, r.Root))
            return null;

        return new Affine(l.Root ?? r.Root, l.Multiplier + r.Multiplier, l.Offset + r.Offset);
    }

    private static bool SameRoot(IOperand a, IOperand b) => (a, b) switch
    {
        (FieldReference x, FieldReference y) => x.Field == y.Field && ReferenceEquals(x.Local, y.Local) && x.Path.SequenceEqual(y.Path),
        _ => ReferenceEquals(a, b),
    };

    private static Affine? ScaleBy(Affine? value, long factor)
        => value is { } affine ? new Affine(affine.Root, affine.Multiplier * factor, affine.Offset * factor) : null;

    // null means the local has more than one definition
    private static Dictionary<LocalVariable, Instruction?> SingleDefinitions(ISILControlFlowGraph cfg)
    {
        var definitions = new Dictionary<LocalVariable, Instruction?>();

        foreach (var instruction in cfg.Instructions)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = definitions.ContainsKey(destination) ? null : instruction;

        return definitions;
    }

    private static Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>> CollectUses(ISILControlFlowGraph cfg)
    {
        var uses = new Dictionary<LocalVariable, List<(Instruction, int)>>();

        foreach (var instruction in cfg.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (ReferenceEquals(operand, instruction.Destination))
                    continue;

                foreach (var local in OperandLocals(operand))
                {
                    if (!uses.TryGetValue(local, out var sites))
                        uses[local] = sites = [];
                    sites.Add((instruction, i));
                }
            }
        }

        return uses;
    }

    private static IEnumerable<LocalVariable> OperandLocals(IOperand operand)
    {
        switch (operand)
        {
            case LocalVariable direct:
                yield return direct;
                break;
            case MemoryOperand memory:
                if (memory.Base is LocalVariable baseLocal)
                    yield return baseLocal;
                if (memory.Index is LocalVariable indexLocal)
                    yield return indexLocal;
                break;
            case AddressOf { Target: LocalVariable addressed }:
                yield return addressed;
                break;
        }
    }
}
