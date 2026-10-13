using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Compilers copy (and zero) structs in register-sized chunks that don't line up with the fields - a Vector3
/// is typically moved as an 8 byte x+y chunk plus a 4 byte z. This pass finds groups of such chunk moves that
/// together copy exactly one whole struct (a local, or a possibly nested struct-typed field) and replaces them
/// with a single struct-valued move, e.g. <c>componentData.targetPosition = targetPos</c>.
///
/// Runs in SSA form, after types and fields have been resolved.
/// </summary>
public static class StructCopyRecovery
{
    private readonly record struct Access(LocalVariable Base, long Offset, int Size)
    {
        // Static storage is reached through a fresh local per load of the class's static fields pointer, but it's
        // all the same storage, so compare those by the type they belong to
        public object Key => Base.Type is StaticFieldStorageTypeAnalysisContext storage ? storage.OwnerType : Base;
    }

    private sealed class Chunk
    {
        public required Instruction Store;
        public required Access Destination;
        public Instruction? Load; // null for a zeroing store
        public Access? Source;
    }

    public static void Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;

        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in graph.Instructions)
            if (instruction.Destination is LocalVariable defined)
                definitions[defined] = instruction;

        foreach (var block in graph.Blocks)
        {
            var chunks = new List<Chunk>();

            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode != OpCode.Move || Locate(instruction.Operands[0], pointerSize) is not { } destination)
                    continue;

                var value = instruction.Operands[1];

                if (IsZero(value, definitions))
                {
                    chunks.Add(new Chunk { Store = instruction, Destination = destination });
                    continue;
                }

                // a run of chunks already merged into one memory to memory move
                if (value is MemoryOperand or FieldReference && Locate(value, pointerSize) is { } direct && direct.Size == destination.Size)
                {
                    chunks.Add(new Chunk { Store = instruction, Destination = destination, Load = instruction, Source = direct });
                    continue;
                }

                if (value is not LocalVariable temporary
                    || !definitions.TryGetValue(temporary, out var load)
                    || load.OpCode != OpCode.Move
                    || Locate(load.Operands[1], pointerSize) is not { } source
                    || source.Size != destination.Size)
                    continue;

                chunks.Add(new Chunk { Store = instruction, Destination = destination, Load = load, Source = source });
            }

            if (chunks.Count < 1)
                continue;

            // Group by destination object and, for copies, by source object and relative displacement
            var groups = chunks.GroupBy(c => (c.Destination.Key, SourceKey: c.Source?.Key, Delta: c.Source is { } s ? s.Offset - c.Destination.Offset : long.MinValue));

            foreach (var group in groups)
                TryCombine(method, block, group.OrderBy(c => c.Destination.Offset).ToList(), pointerSize);
        }

        ExpandConstantChunks(method, definitions, pointerSize);
    }

    /// <summary>
    /// A chunk store of a constant (zero, or a vector out of .rdata) that isn't a whole struct still sets each field
    /// it covers to a known value, e.g. the 16 byte store that initialises a Rect field to (0, 0, 1, 1). Expand those
    /// into one store per field.
    /// </summary>
    private static void ExpandConstantChunks(MethodAnalysisContext method, Dictionary<LocalVariable, Instruction> definitions, int pointerSize)
    {
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var store = block.Instructions[i];
                if (store is not { OpCode: OpCode.Move, Operands: [var target, var value] })
                    continue;

                // What's being written: a sized chunk of something, or a whole struct-typed field
                LocalVariable baseLocal;
                TypeAnalysisContext owner;
                bool isStatic;
                long rangeStart, leafBase;
                int rangeSize;
                List<FieldAnalysisContext> prefix;

                switch (target)
                {
                    case MemoryOperand { Index: null, Scale: 0, Base: LocalVariable { Type: { } baseType } chunkBase, Size: > 4 } chunk:
                    {
                        var pointee = baseType is ByRefTypeAnalysisContext { ElementType: { } element } ? element : baseType;
                        baseLocal = chunkBase;
                        isStatic = pointee is StaticFieldStorageTypeAnalysisContext;
                        owner = (pointee as StaticFieldStorageTypeAnalysisContext)?.OwnerType ?? pointee;
                        rangeStart = chunk.Addend;
                        rangeSize = chunk.Size;
                        leafBase = 0;
                        prefix = [];
                        break;
                    }
                    case FieldReference { Field.FieldType: var fieldType } wholeField when StackStructRecovery.IsStruct(fieldType)
                                                                                         && TypeSizes.StorageSize(fieldType, pointerSize) is > 4 and < 0x1000 and var fieldSize:
                        baseLocal = wholeField.Local;
                        owner = fieldType;
                        isStatic = false;
                        rangeStart = 0;
                        rangeSize = (int)fieldSize;
                        leafBase = wholeField.Offset;
                        prefix = wholeField.Chain.ToList();
                        break;
                    default:
                        continue;
                }

                byte[]? bytes;
                if (IsZero(value, definitions))
                    bytes = new byte[rangeSize];
                else if (value is LocalVariable temporary && definitions.TryGetValue(temporary, out var load)
                         && load is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: null, Index: null } constant] } && constant.Size == rangeSize)
                    bytes = ReadConstant(method.AppContext, (ulong)constant.Addend, rangeSize);
                else
                    continue;

                if (bytes == null)
                    continue;

                if (owner is GenericInstanceTypeAnalysisContext || owner.GenericParameters.Count > 0 || owner is RuntimeClassTypeAnalysisContext)
                    continue;

                var leaves = new List<(List<FieldAnalysisContext> Chain, long Offset, long Size)>();
                CollectLeaves(owner, isStatic, 0, [], leaves, pointerSize, prefix.Count > 0 ? 1 : 0);

                var covered = leaves.Where(l => l.Offset >= rangeStart && l.Offset + l.Size <= rangeStart + rangeSize).ToList();
                if (covered.Count == 0)
                    continue;

                // The covered fields must account for every non-zero byte, and none may stick out of the chunk
                if (leaves.Any(l => l.Offset < rangeStart + rangeSize && l.Offset + l.Size > rangeStart && !covered.Contains(l)))
                    continue;

                var accounted = new bool[rangeSize];
                foreach (var leaf in covered)
                    for (var b = 0; b < leaf.Size; b++)
                        accounted[leaf.Offset - rangeStart + b] = true;

                if (Enumerable.Range(0, rangeSize).Any(b => !accounted[b] && bytes[b] != 0))
                    continue;

                var replacements = new List<Instruction>();
                foreach (var leaf in covered.OrderBy(l => l.Offset))
                {
                    var literal = Literal(leaf.Chain[^1].FieldType, bytes, (int)(leaf.Offset - rangeStart), (int)leaf.Size);
                    if (literal == null)
                    {
                        replacements = null;
                        break;
                    }

                    var chain = prefix.Concat(leaf.Chain).ToList();
                    var reference = new FieldReference(chain[^1], baseLocal, (int)(leafBase + leaf.Offset)) { Path = chain.GetRange(0, chain.Count - 1) };
                    replacements.Add(new Instruction(store.Index, OpCode.Move, reference, literal));
                }

                if (replacements == null)
                    continue;

                block.Instructions.RemoveAt(i);
                block.Instructions.InsertRange(i, replacements);
                i += replacements.Count - 1;
            }
        }
    }

    // Every primitive (non-struct) field of a type, with its offset, looking inside struct fields
    internal static void CollectLeaves(TypeAnalysisContext type, bool isStatic, long baseOffset, List<FieldAnalysisContext> path,
        List<(List<FieldAnalysisContext> Chain, long Offset, long Size)> leaves, int pointerSize, int depth)
    {
        if (depth > 6)
            return;

        for (var current = type; current != null; current = isStatic || depth > 0 ? null : current.BaseType)
        {
            foreach (var field in current.Fields)
            {
                if (field.IsStatic != isStatic || (field.Attributes & System.Reflection.FieldAttributes.Literal) != 0 || field.BackingData?.FieldOffset is not { } offset)
                    continue;

                var chain = new List<FieldAnalysisContext>(path) { field };

                if (StackStructRecovery.IsStruct(field.FieldType))
                    CollectLeaves(field.FieldType, false, baseOffset + offset, chain, leaves, pointerSize, depth + 1);
                else if (TypeSizes.StorageSize(field.FieldType, pointerSize) is > 0 and var size)
                    leaves.Add((chain, baseOffset + offset, size));
            }
        }
    }

    private static IOperand? Literal(TypeAnalysisContext type, byte[] bytes, int offset, int size)
    {
        var target = type.IsEnumType ? type.Fields.FirstOrDefault(f => !f.IsStatic)?.FieldType ?? type : type;

        return target.FullName switch
        {
            "System.Single" when size == 4 => new FloatLiteral(System.BitConverter.ToSingle(bytes, offset)),
            "System.Double" when size == 8 => new DoubleLiteral(System.BitConverter.ToDouble(bytes, offset)),
            "System.Boolean" or "System.Byte" when size == 1 => new Immediate(bytes[offset]),
            "System.SByte" when size == 1 => new Immediate((sbyte)bytes[offset]),
            "System.Int16" when size == 2 => new Immediate(System.BitConverter.ToInt16(bytes, offset)),
            "System.UInt16" or "System.Char" when size == 2 => new Immediate(System.BitConverter.ToUInt16(bytes, offset)),
            "System.Int32" when size == 4 => new Immediate(System.BitConverter.ToInt32(bytes, offset)),
            "System.UInt32" when size == 4 => new Immediate(System.BitConverter.ToUInt32(bytes, offset)),
            "System.Int64" or "System.UInt64" when size == 8 => new Immediate(System.BitConverter.ToInt64(bytes, offset)),
            // a reference (or pointer) can only be set to null like this
            _ when !target.IsValueType && bytes.Skip(offset).Take(size).All(b => b == 0) => new Immediate(0),
            _ => null
        };
    }

    private static byte[]? ReadConstant(ApplicationAnalysisContext app, ulong address, int size)
    {
        if (!app.Binary.TryMapVirtualAddressToRaw(address, out var raw))
            return null;

        var content = app.Binary.GetRawBinaryContent();
        if (raw < 0 || raw + size > content.Length)
            return null;

        return content.Slice((int)raw, size).ToArray();
    }

    private static void TryCombine(MethodAnalysisContext method, Block block, List<Chunk> group, int pointerSize)
    {
        // Split the group into runs of contiguous, non-overlapping chunks, and try each run as one struct
        var start = 0;
        while (start < group.Count)
        {
            var end = start + 1;
            while (end < group.Count && group[end].Destination.Offset == group[end - 1].Destination.Offset + group[end - 1].Destination.Size)
                end++;

            // Find the longest prefix of what's left of the run that forms a whole struct, combine that, and carry on
            // after it. If none does, drop the first chunk and retry from the next.
            var advanced = false;
            for (var stop = end; stop > start; stop--)
            {
                if (!TryCombineRun(method, block, group.GetRange(start, stop - start), pointerSize))
                    continue;

                start = stop;
                advanced = true;
                break;
            }

            if (!advanced)
                start++;
        }
    }

    private static bool TryCombineRun(MethodAnalysisContext method, Block block, List<Chunk> run, int pointerSize)
    {
        var first = run[0];
        var lo = first.Destination.Offset;
        var hi = run[^1].Destination.Offset + run[^1].Destination.Size;

        // A single chunk that already maps onto a single primitive field is just an ordinary move
        if (run.Count == 1 && first.Store.Operands[0] is FieldReference { Field.FieldType: var single } && !StackStructRecovery.IsStruct(single))
            return false;

        // Try the widest struct covering the run first, then narrower sub-runs aren't attempted (keeps it simple)
        if (Location(first.Destination.Base, lo, hi - lo, pointerSize) is not var (destinationOperand, destinationType))
            return false;

        IOperand sourceOperand;
        if (first.Source is { } firstSource)
        {
            var delta = firstSource.Offset - lo;
            if (Location(firstSource.Base, lo + delta, hi - lo, pointerSize) is not var (foundSource, sourceType))
                return false;

            if (sourceType.FullName != destinationType.FullName)
                return false;

            sourceOperand = foundSource;
        }
        else
        {
            sourceOperand = new DefaultValue(destinationType);
        }

        // The combined move goes where the last chunk store was. Make sure nothing in between could have changed
        // the source after its chunks were read.
        var stores = run.Select(c => c.Store).ToHashSet();
        var lastStore = block.Instructions.Last(stores.Contains);
        var firstIndex = block.Instructions.FindIndex(i => stores.Contains(i) || run.Any(c => ReferenceEquals(c.Load, i)));
        var lastIndex = block.Instructions.IndexOf(lastStore);

        if (firstIndex < 0)
            return false;

        if (first.Source is { } source)
        {
            for (var i = firstIndex; i < lastIndex; i++)
            {
                var between = block.Instructions[i];
                if (stores.Contains(between))
                    continue;

                if (between.IsCall || between.OpCode == OpCode.IndirectCall)
                    return false;

                if (Locate(between.Destination, pointerSize) is { } written && Equals(written.Key, source.Key))
                    return false;
            }

            // Every load must happen in this block, before the combined move
            foreach (var chunk in run)
            {
                var loadIndex = block.Instructions.IndexOf(chunk.Load!);
                if (loadIndex < 0 || loadIndex > lastIndex)
                    return false;
            }
        }

        foreach (var store in stores)
        {
            if (ReferenceEquals(store, lastStore))
                continue;

            store.OpCode = OpCode.Nop;
            store.SetOperands();
        }

        lastStore.SetOperands(destinationOperand, sourceOperand);
        return true;
    }

    // A struct-typed location of exactly the given size at the given offset from the base local
    private static (IOperand Operand, TypeAnalysisContext Type)? Location(LocalVariable baseLocal, long offset, long size, int pointerSize)
    {
        if (baseLocal.Type is not { } baseType)
            return null;

        var pointee = baseType is ByRefTypeAnalysisContext { ElementType: { } element } ? element : baseType;

        // The whole local (a struct value, or what a struct pointer points at)
        if (offset == 0 && StackStructRecovery.IsStruct(pointee) && TypeSizes.StorageSize(pointee, pointerSize) == size)
            return (new MemoryOperand(baseLocal, size: (int)size), pointee);

        var isStatic = pointee is StaticFieldStorageTypeAnalysisContext;
        var owner = (pointee as StaticFieldStorageTypeAnalysisContext)?.OwnerType ?? pointee;

        if (owner is GenericInstanceTypeAnalysisContext || owner.GenericParameters.Count > 0)
            return null;

        if (MetadataResolver.FindFieldChain(owner, isStatic, offset, (int)size, pointerSize) is not { } chain)
            return null;

        var field = chain[^1];
        if (!StackStructRecovery.IsStruct(field.FieldType) || TypeSizes.StorageSize(field.FieldType, pointerSize) != size)
            return null;

        return (new FieldReference(field, baseLocal, (int)offset) { Path = chain.GetRange(0, chain.Count - 1) }, field.FieldType);
    }

    private static Access? Locate(IOperand? operand, int pointerSize) => operand switch
    {
        MemoryOperand { Index: null, Scale: 0, Base: LocalVariable baseLocal, Size: > 0 } memory => new Access(baseLocal, memory.Addend, memory.Size),
        FieldReference { Local: { } fieldLocal } field when TypeSizes.StorageSize(field.Field.FieldType, pointerSize) is > 0 and var fieldSize
            => new Access(fieldLocal, field.Offset, (int)fieldSize),
        _ => null
    };

    private static bool IsZero(IOperand value, Dictionary<LocalVariable, Instruction> definitions) => value switch
    {
        Immediate { Value: 0 } => true,
        LocalVariable local => definitions.TryGetValue(local, out var definition)
                               && definition is { OpCode: OpCode.Move, Operands: [_, Immediate { Value: 0 }] },
        _ => false
    };
}
