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
    private readonly record struct Access(LocalVariable Base, long Offset, int Size);

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
            var groups = chunks.GroupBy(c => (c.Destination.Base, SourceBase: c.Source?.Base, Delta: c.Source is { } s ? s.Offset - c.Destination.Offset : long.MinValue));

            foreach (var group in groups)
                TryCombine(method, block, group.OrderBy(c => c.Destination.Offset).ToList(), pointerSize);
        }
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

                if (Locate(between.Destination, pointerSize) is { } written && ReferenceEquals(written.Base, source.Base))
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
