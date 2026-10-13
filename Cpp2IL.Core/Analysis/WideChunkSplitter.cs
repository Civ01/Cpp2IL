using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// MSVC copies structs in 8 and 16 byte chunks (movsd/movups) that don't line up with any one field: the x and y of
/// Vector3.up in one 8 byte load, its z separately. When such a chunk is only ever stored somewhere else (possibly after
/// passing through a phi, as when a ternary picks Vector3.up or Vector3.right) or read as its first float, it can be
/// split into one value per field it covers, each of which then resolves as a normal field access.
/// Runs in SSA form once types are known, before still-untyped locals are given default types.
/// </summary>
public static class WideChunkSplitter
{
    private sealed record Piece(long Offset, int Size, TypeAnalysisContext Type);

    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        if (pointerSize != 8)
            return false;

        var definitions = new Dictionary<LocalVariable, Instruction>();
        var uses = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var instruction in graph.Instructions)
        {
            if (instruction.Destination is LocalVariable defined)
                definitions[defined] = instruction;

            foreach (var used in Reads(instruction))
            {
                if (!uses.TryGetValue(used, out var list))
                    uses[used] = list = [];
                list.Add(instruction);
            }
        }

        var leafCache = new Dictionary<(TypeAnalysisContext, bool), List<(List<FieldAnalysisContext> Chain, long Offset, long Size)>>();
        var done = new HashSet<LocalVariable>();
        var changed = false;

        foreach (var load in graph.Instructions.ToList())
        {
            if (load is not { OpCode: OpCode.Move, Operands: [LocalVariable loaded, MemoryOperand { Base: LocalVariable, Index: null, Size: 8 or 16 } memory] }
                || done.Contains(loaded)
                || Pieces(memory, pointerSize, leafCache) is not { Count: > 1 } pieces)
                continue;

            // gather everything the chunk flows to
            var members = new List<LocalVariable>();
            var stores = new List<Instruction>();
            if (!Collect(loaded, pieces, memory.Size, members, stores, definitions, uses, pointerSize, leafCache))
                continue;

            foreach (var member in members)
                done.Add(member);

            Rewrite(method, members, stores, pieces, definitions);
            changed = true;
        }

        changed |= SplitConstantStores(method, pointerSize, leafCache);
        changed |= SplitMemoryCopies(method, pointerSize, leafCache);

        return changed;
    }

    /// <summary>
    /// MSVC initialises neighbouring fields with one wide store of a constant: <c>mov qword ptr [rbx+70h], 3F99999Ah</c>
    /// sets a float to 1.2 and the next one to 0, <c>mov word ptr [rcx+18h], 101h</c> two bools to true. Each field gets
    /// its own store of its share of the bits.
    /// </summary>
    private static bool SplitConstantStores(MethodAnalysisContext method, int pointerSize,
        Dictionary<(TypeAnalysisContext, bool), List<(List<FieldAnalysisContext> Chain, long Offset, long Size)>> leafCache)
    {
        var changed = false;

        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var store = block.Instructions[i];
                // (zeroing 8 bytes or more is left whole, for StructCopyRecovery to make default(T) of or expand)
                if (store is not { OpCode: OpCode.Move, Operands: [MemoryOperand { Base: LocalVariable, Index: null, Size: 2 or 4 or 8 } destination, Immediate immediate] }
                    || immediate.Value == 0 && destination.Size == 8)
                    continue;

                var bitsStored = unchecked((ulong)immediate.Value);

                if (Pieces(destination, pointerSize, leafCache) is not { Count: > 1 } pieces)
                    continue;

                List<Instruction>? replacements = [];
                foreach (var piece in pieces)
                {
                    var bits = bitsStored >> (int)(8 * piece.Offset);
                    if (piece.Size < 8)
                        bits &= (1UL << (8 * piece.Size)) - 1;

                    IOperand? pieceValue = piece.Type.FullName switch
                    {
                        "System.Single" => new FloatLiteral(System.BitConverter.Int32BitsToSingle(unchecked((int)bits))),
                        "System.Double" => new DoubleLiteral(System.BitConverter.Int64BitsToDouble(unchecked((long)bits))),
                        "System.Int32" => new Immediate(unchecked((int)bits)),
                        "System.Int16" => new Immediate(unchecked((short)bits)),
                        "System.SByte" => new Immediate(unchecked((sbyte)bits)),
                        "System.Boolean" when bits > 1 => null,
                        _ when piece.Type.IsEnumType && piece.Type.EnumUnderlyingType?.FullName is "System.Int32" => new Immediate(unchecked((int)bits)),
                        _ => new Immediate(unchecked((long)bits)),
                    };

                    if (pieceValue == null)
                    {
                        replacements = null;
                        break;
                    }

                    replacements.Add(new Instruction(store.Index, OpCode.Move, new MemoryOperand(destination.Base, null, destination.Addend + piece.Offset, 0, piece.Size), pieceValue));
                }

                if (replacements == null)
                    continue;

                block.Instructions.RemoveAt(i);
                block.Instructions.InsertRange(i, replacements);
                i += replacements.Count - 1;
                changed = true;
            }
        }

        return changed;
    }

    /// <summary>
    /// A run of 16 byte chunks copied straight from one struct to another (merged into one memory to memory move when
    /// the struct was built for a call) that is only part of the struct: one move per field it covers.
    /// </summary>
    private static bool SplitMemoryCopies(MethodAnalysisContext method, int pointerSize,
        Dictionary<(TypeAnalysisContext, bool), List<(List<FieldAnalysisContext> Chain, long Offset, long Size)>> leafCache)
    {
        var changed = false;

        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var copy = block.Instructions[i];
                if (copy is not { OpCode: OpCode.Move, Operands: [MemoryOperand { Base: LocalVariable, Index: null, Size: >= 8 } destination, MemoryOperand { Base: LocalVariable, Index: null } source] }
                    || source.Size != destination.Size
                    || Pieces(destination, pointerSize, leafCache) is not { Count: > 1 } pieces
                    || Pieces(source, pointerSize, leafCache) is not { } sourcePieces
                    || !pieces.Select(p => (p.Offset, p.Size)).SequenceEqual(sourcePieces.Select(p => (p.Offset, p.Size))))
                    continue;

                var replacements = pieces.Select(piece => new Instruction(copy.Index, OpCode.Move,
                    new MemoryOperand(destination.Base, null, destination.Addend + piece.Offset, 0, piece.Size),
                    new MemoryOperand(source.Base, null, source.Addend + piece.Offset, 0, piece.Size))).ToList();

                block.Instructions.RemoveAt(i);
                block.Instructions.InsertRange(i, replacements);
                i += replacements.Count - 1;
                changed = true;
            }
        }

        return changed;
    }

    /// <summary>
    /// An 8 byte read of two adjacent 4 byte integer fields used as one 64 bit integer: MSVC folds
    /// <c>((long)b << 32) | (uint)a</c> over neighbouring fields into a single load. Becomes exactly that expression.
    /// </summary>
    public static bool SplitIntegerPairs(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var types = method.AppContext.SystemTypes;
        var changed = false;

        foreach (var block in graph.Blocks)
        {
            for (var index = 0; index < block.Instructions.Count; index++)
            {
                var load = block.Instructions[index];
                if (load is not { OpCode: OpCode.Move, Operands: [LocalVariable { Type: var resultType } result, MemoryOperand { Base: LocalVariable { Type: { } baseType }, Index: null, Size: 8 } memory] }
                    || resultType != types.SystemInt64Type && resultType != types.SystemUInt64Type
                    && resultType != types.SystemIntPtrType && resultType != types.SystemUIntPtrType) // a 64 bit integer, defaulted to nint if nothing said more
                    continue;

                var owner = baseType is ByRefTypeAnalysisContext { ElementType: { } element } ? element : baseType;
                if (owner is GenericInstanceTypeAnalysisContext or GenericParameterTypeAnalysisContext or RuntimeClassTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext
                        or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext or PointerTypeAnalysisContext or SzArrayTypeAnalysisContext
                    || MetadataResolver.FindFieldChain(owner, false, memory.Addend, 4, pointerSize) is not { } low
                    || MetadataResolver.FindFieldChain(owner, false, memory.Addend + 4, 4, pointerSize) is not { } high
                    || !IsFourByteInteger(low[^1].FieldType) || !IsFourByteInteger(high[^1].FieldType))
                    continue;

                LocalVariable Temp(string name, TypeAnalysisContext type)
                {
                    var local = new LocalVariable($"{name}{method.Locals.Count}", new Register(null, $"{name.ToUpperInvariant()}_{method.Locals.Count}", 0), type);
                    method.Locals.Add(local);
                    return local;
                }

                var lowValue = Temp("low", low[^1].FieldType);
                var highValue = Temp("high", high[^1].FieldType);
                var lowWide = Temp("lowWide", types.SystemInt64Type);
                var lowBits = Temp("lowBits", types.SystemInt64Type);
                var highWide = Temp("highWide", types.SystemInt64Type);
                var highBits = Temp("highBits", types.SystemInt64Type);

                block.Instructions.InsertRange(index, [
                    new Instruction(load.Index, OpCode.Move, lowValue, new MemoryOperand(memory.Base, null, memory.Addend, 0, 4)),
                    new Instruction(load.Index, OpCode.Move, highValue, new MemoryOperand(memory.Base, null, memory.Addend + 4, 0, 4)),
                    new Instruction(load.Index, OpCode.Move, lowWide, lowValue),
                    new Instruction(load.Index, OpCode.And, lowBits, lowWide, new Immediate(0xFFFFFFFF)),
                    new Instruction(load.Index, OpCode.Move, highWide, highValue),
                    new Instruction(load.Index, OpCode.ShiftLeft, highBits, highWide, new Immediate(32)),
                ]);
                load.OpCode = OpCode.Or;
                load.SetOperands(result, highBits, lowBits);
                index += 6;
                changed = true;
            }
        }

        return changed;
    }

    private static bool IsFourByteInteger(TypeAnalysisContext type) =>
        type.IsEnumType ? type.Fields.FirstOrDefault(f => !f.IsStatic) is { FieldType: var underlying } && IsFourByteInteger(underlying)
            : type.Namespace == "System" && type.Name is "Int32" or "UInt32";

    private static IEnumerable<LocalVariable> Reads(Instruction instruction)
    {
        var destination = instruction.Destination;
        foreach (var operand in instruction.Operands)
        {
            switch (operand)
            {
                case LocalVariable local when !ReferenceEquals(local, destination):
                    yield return local;
                    break;
                case MemoryOperand { Base: LocalVariable memoryBase } memory:
                    yield return memoryBase;
                    if (memory.Index is LocalVariable memoryIndex)
                        yield return memoryIndex;
                    break;
                case FieldReference { Local: { } fieldLocal }:
                    yield return fieldLocal;
                    break;
            }
        }
    }

    // The fields exactly covering a chunk of memory
    private static List<Piece>? Pieces(MemoryOperand memory, int pointerSize,
        Dictionary<(TypeAnalysisContext, bool), List<(List<FieldAnalysisContext> Chain, long Offset, long Size)>> cache)
    {
        if (memory.Base is not LocalVariable { Type: { } baseType })
            return null;

        var pointee = baseType is ByRefTypeAnalysisContext { ElementType: { } element } ? element : baseType;
        var isStatic = pointee is StaticFieldStorageTypeAnalysisContext;
        var owner = (pointee as StaticFieldStorageTypeAnalysisContext)?.OwnerType ?? pointee;

        if (owner is GenericInstanceTypeAnalysisContext genericOwner && !isStatic)
            return GenericPieces(genericOwner, memory, pointerSize);

        if (owner is GenericInstanceTypeAnalysisContext or GenericParameterTypeAnalysisContext or RuntimeClassTypeAnalysisContext
                or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext or PointerTypeAnalysisContext
            || owner.GenericParameters.Count > 0 || owner.Definition == null)
            return null;

        if (!cache.TryGetValue((owner, isStatic), out var leaves))
        {
            leaves = [];
            StructCopyRecovery.CollectLeaves(owner, isStatic, 0, [], leaves, pointerSize, 0);
            cache[(owner, isStatic)] = leaves;
        }

        var pieces = new List<Piece>();
        var position = memory.Addend;
        var end = memory.Addend + memory.Size;
        while (position < end)
        {
            var leaf = leaves.FirstOrDefault(l => l.Offset == position);
            if (leaf.Chain == null && !leaves.Any(l => l.Offset < position && l.Offset + l.Size > position))
            {
                position++; // padding
                continue;
            }
            if (leaf.Chain == null || position + leaf.Size > end)
                return null;

            pieces.Add(new Piece(position - memory.Addend, (int)leaf.Size, leaf.Chain[^1].FieldType));
            position += leaf.Size;
        }

        return pieces;
    }

    private static List<Piece>? GenericPieces(GenericInstanceTypeAnalysisContext owner, MemoryOperand memory, int pointerSize)
    {
        var pieces = new List<Piece>();
        var position = memory.Addend;
        var end = memory.Addend + memory.Size;

        while (position < end)
        {
            Piece? piece = null;
            foreach (var size in new[] { 8, 4, 2, 1 })
            {
                if (position + size > end
                    || GenericInstanceFieldLayout.FindFieldChain(owner, position, size, pointerSize) is not { } chain
                    || StackStructRecovery.IsStruct(chain[^1].FieldType)
                    || TypeSizes.StorageSize(chain[^1].FieldType, pointerSize) != size)
                    continue;

                piece = new Piece(position - memory.Addend, size, chain[^1].FieldType);
                break;
            }

            if (piece == null)
            {
                // padding between fields (or after the last one), which gets copied along with them: skip to the next
                // field, as long as nothing straddles this byte
                if (GenericInstanceFieldLayout.FindFieldChain(owner, position, 0, pointerSize) != null)
                    return null;

                position++;
                continue;
            }

            pieces.Add(piece);
            position += piece.Size;
        }

        return pieces.Count > 0 ? pieces : null;
    }

    private static bool SameLayout(List<Piece> a, List<Piece> b) =>
        a.Count == b.Count && a.Zip(b, (x, y) => x.Offset == y.Offset && x.Size == y.Size).All(same => same);

    private static bool Collect(LocalVariable start, List<Piece> pieces, int size, List<LocalVariable> members, List<Instruction> stores,
        Dictionary<LocalVariable, Instruction> definitions, Dictionary<LocalVariable, List<Instruction>> uses, int pointerSize,
        Dictionary<(TypeAnalysisContext, bool), List<(List<FieldAnalysisContext> Chain, long Offset, long Size)>> cache)
    {
        var pending = new Stack<LocalVariable>();
        pending.Push(start);

        while (pending.Count > 0)
        {
            var member = pending.Pop();
            if (members.Contains(member))
                continue;

            // a member is one of: the wide load, a phi of wide loads/members, a copy of a member
            if (!definitions.TryGetValue(member, out var definition))
                return false;

            switch (definition)
            {
                case { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable, Index: null } memory] }
                    when memory.Size == size && Pieces(memory, pointerSize, cache) is { } layout && SameLayout(layout, pieces):
                    break;
                case { OpCode: OpCode.Phi }:
                    for (var input = 1; input < definition.Operands.Count; input++)
                    {
                        if (definition.Operands[input] is not LocalVariable incoming)
                            return false;
                        pending.Push(incoming);
                    }
                    break;
                case { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] }:
                    pending.Push(copied);
                    break;
                default:
                    return false;
            }

            members.Add(member);
            if (members.Count > 32)
                return false;

            foreach (var use in uses.GetValueOrDefault(member) ?? [])
            {
                switch (use)
                {
                    // stored whole
                    case { OpCode: OpCode.Move, Operands: [MemoryOperand { Base: LocalVariable { Type: not SzArrayTypeAnalysisContext }, Index: null } destination, LocalVariable stored] }
                        when ReferenceEquals(stored, member) && destination.Size == size:
                        if (!stores.Contains(use))
                            stores.Add(use);
                        break;
                    // into a phi or a copy, which become members too
                    case { OpCode: OpCode.Phi, Operands: [LocalVariable joined, ..] }:
                        pending.Push(joined);
                        break;
                    case { OpCode: OpCode.Move, Operands: [LocalVariable copy, LocalVariable copied] } when ReferenceEquals(copied, member):
                        pending.Push(copy);
                        break;
                    // only its first float read
                    case { ScalarSingle: true } when pieces[0].Size == 4 && use.OpCode is not (OpCode.Phi or OpCode.VectorShuffle):
                        break;
                    default:
                        return false;
                }
            }
        }

        return true;
    }

    private static void Rewrite(MethodAnalysisContext method, List<LocalVariable> members, List<Instruction> stores, List<Piece> pieces,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        var graph = method.ControlFlowGraph!;
        var pieceLocals = new Dictionary<LocalVariable, LocalVariable[]>();

        foreach (var member in members)
        {
            var locals = new LocalVariable[pieces.Count];
            locals[0] = member;
            for (var k = 1; k < pieces.Count; k++)
            {
                var register = new Register(null, $"PIECE_{method.Locals.Count}", 0);
                locals[k] = new LocalVariable($"piece{method.Locals.Count}", register, pieces[k].Type);
                method.Locals.Add(locals[k]);
            }

            member.Type = pieces[0].Type;
            pieceLocals[member] = locals;
        }

        foreach (var member in members)
        {
            var definition = definitions[member];
            var block = graph.Blocks.First(b => b.Instructions.Contains(definition));
            var index = block.Instructions.IndexOf(definition);
            var added = new List<Instruction>();

            switch (definition)
            {
                case { OpCode: OpCode.Move, Operands: [_, MemoryOperand memory] }:
                    for (var k = 1; k < pieces.Count; k++)
                        added.Add(new Instruction(definition.Index, OpCode.Move, pieceLocals[member][k],
                            new MemoryOperand(memory.Base, null, memory.Addend + pieces[k].Offset, 0, pieces[k].Size)));
                    definition.SetOperand(1, new MemoryOperand(memory.Base, null, memory.Addend, 0, pieces[0].Size));
                    break;
                case { OpCode: OpCode.Phi }:
                    for (var k = 1; k < pieces.Count; k++)
                    {
                        var operands = new List<IOperand> { pieceLocals[member][k] };
                        for (var input = 1; input < definition.Operands.Count; input++)
                            operands.Add(pieceLocals[(LocalVariable)definition.Operands[input]][k]);
                        added.Add(new Instruction(definition.Index, OpCode.Phi, operands));
                    }
                    break;
                case { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] }:
                    for (var k = 1; k < pieces.Count; k++)
                        added.Add(new Instruction(definition.Index, OpCode.Move, pieceLocals[member][k], pieceLocals[copied][k]));
                    break;
            }

            block.Instructions.InsertRange(index + 1, added);
        }

        foreach (var store in stores)
        {
            var block = graph.Blocks.First(b => b.Instructions.Contains(store));
            var destination = (MemoryOperand)store.Operands[0];
            var value = (LocalVariable)store.Operands[1];
            var added = new List<Instruction>();

            for (var k = 1; k < pieces.Count; k++)
                added.Add(new Instruction(store.Index, OpCode.Move,
                    new MemoryOperand(destination.Base, null, destination.Addend + pieces[k].Offset, 0, pieces[k].Size), pieceLocals[value][k]));

            store.SetOperand(0, new MemoryOperand(destination.Base, null, destination.Addend, 0, pieces[0].Size));
            block.Instructions.InsertRange(block.Instructions.IndexOf(store) + 1, added);
        }
    }
}
