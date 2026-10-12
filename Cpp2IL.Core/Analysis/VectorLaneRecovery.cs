using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// ISIL treats an xmm register as the scalar in its low lane. MSVC keeps Vector2/Vector3 components packed in the other
/// lanes too: <c>movsd xmm1,[rax+18h]</c> loads x and y at once, <c>shufps xmm0,xmm0,55h</c> then pulls y down to lane 0,
/// and <c>unpcklps xmm6,xmm7 / movsd [rbp-51h],xmm6</c> packs two floats up to store them together.
/// <para/>
/// This tracks, per register, a scalar for each lane, lowers every <see cref="OpCode.VectorShuffle"/> to a move of the
/// lane its low lane ends up holding, and splits wide stores of tracked lanes into one 4 byte store per lane. A wide load
/// is only split (narrowed to its first float, with the other lanes loaded into temporaries) once some lane of it is
/// actually read, so plain 8/16 byte copies through xmm registers, and doubles, are left alone.
/// Runs on ISIL registers, before SSA.
/// </summary>
public static class VectorLaneRecovery
{
    private const int Zero = 8;

    /// <summary>Suffix of the register carrying the high half of a GPR filled from two packed floats.</summary>
    public const string HighSuffix = "_hi";

    // The scalar some lane holds, made available as a temporary register the first time it's needed
    private sealed class Lane
    {
        public required Block Block;
        public required Instruction Anchor;
        public bool After;
        public required IOperand Value;
        public WideLoad? Load;
        public Register? Materialized;
        public bool HighHalf; // the high 4 bytes of the general register in Value
        public List<(Block Predecessor, Lane Source)>? MergeOf; // at a join: whichever lane each predecessor had
        public bool WholeRegisterZero; // an upper lane of a register zeroed as a whole (xorps x,x), so the low lane is 0 too
    }

    // A wide load into an xmm register, which might yet turn out to be packed floats
    private sealed class WideLoad
    {
        public required Block Block;
        public required Instruction Instruction;
        public bool Split;
        public readonly List<(Block Block, Instruction Store)> PendingStores = [];
        public readonly Lane?[] Lanes = new Lane?[4];
    }

    // In lane 0 of a register's state: its low lane holds something we couldn't follow (null there means the register
    // itself, as usual). Only an error if it's read before being overwritten.
    private static readonly Lane UnknownLow = new() { Block = null!, Anchor = null!, Value = new FloatLiteral(0) };

    private sealed class Context(MethodAnalysisContext method)
    {
        public readonly MethodAnalysisContext Method = method;
        public int Temporaries;

        // stack slots holding a wide copy of a load not yet known to be floats
        public readonly Dictionary<int, (int Size, WideLoad Load)> PendingStackCopies = new();

        public readonly List<WideLoad> Loads = [];
    }

    public static void Run(MethodAnalysisContext method, ISILControlFlowGraph graph)
    {
        if (method.AppContext.Binary.PointerSizeBytes != 8 || method.AppContext.InstructionSet is not InstructionSets.X86InstructionSet)
            return;

        SplitPackedSpills(graph);

        if (!graph.Blocks.Any(b => b.Instructions.Any(i => i.OpCode == OpCode.VectorShuffle)))
            return;

        var context = new Context(method);
        var endStates = new Dictionary<Block, Dictionary<string, Lane?[]>>();

        foreach (var block in graph.Blocks)
        {
            var predecessors = block.Predecessors.Distinct().ToList();
            var singlePredecessor = predecessors is [{ } only] && endStates.ContainsKey(only) ? only : null;
            var state = singlePredecessor != null
                ? endStates[singlePredecessor].ToDictionary(kv => kv.Key, kv => (Lane?[])kv.Value.Clone())
                : predecessors.Count > 1 && predecessors.All(endStates.ContainsKey)
                    ? Merge(block, predecessors.Select(p => (p, endStates[p])).ToList())
                    : new Dictionary<string, Lane?[]>();
            if (singlePredecessor == null)
                context.PendingStackCopies.Clear();

            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var instruction = block.Instructions[i];
                Process(context, block, instruction, state);
                i = block.Instructions.IndexOf(instruction);
            }

            // an unknown low lane flowing somewhere we won't follow it
            if (block.Successors.Any(successor => successor.Predecessors.Distinct().Count() != 1))
            {
                foreach (var lanes in state.Values.Where(lanes => lanes[0] == UnknownLow))
                {
                    var at = block.Instructions.Count > 0 && block.Instructions[^1].OpCode is OpCode.Jump or OpCode.ConditionalJump or OpCode.Return
                        ? block.Instructions.Count - 1
                        : block.Instructions.Count;
                    block.Instructions.Insert(at, new Instruction(block.Instructions.Count > 0 ? block.Instructions[^1].Index : 0, OpCode.NotImplemented,
                        new StringLiteral("vector lane of an unknown value")));
                    lanes[0] = null;
                }
            }

            endStates[block] = state;
        }

        // movsd xmm0,[rdx+0Ch] / subss xmm1,xmm0: a wide load of which only the low float is ever used is a float load
        foreach (var load in context.Loads)
            if (!load.Split && OnlyLowFloatUsed(load))
                Split(context, load);

        // Anything not lowered (shouldn't happen) must not reach later passes
        foreach (var instruction in graph.Blocks.SelectMany(b => b.Instructions))
            if (instruction.OpCode == OpCode.VectorShuffle)
                instruction.Rewrite(OpCode.NotImplemented, new StringLiteral("vector shuffle"));
    }

    private static void Rewrite(this Instruction instruction, OpCode opCode, params IOperand[] operands)
    {
        instruction.OpCode = opCode;
        instruction.SetOperands([.. operands]);
    }

    private static bool IsVector(IOperand operand, out string name)
    {
        if (operand is Register { Name: { } registerName } && registerName.StartsWith("xmm", StringComparison.Ordinal))
        {
            name = registerName;
            return true;
        }

        name = "";
        return false;
    }

    private static void Process(Context context, Block block, Instruction instruction, Dictionary<string, Lane?[]> state)
    {
        // a float read out of a spilled wide copy: the copy was of packed floats
        if (instruction is { OpCode: OpCode.Move, Operands: [_, StackOffset { Size: 4 } read] })
            foreach (var (offset, (size, load)) in context.PendingStackCopies.ToList())
                if (read.Offset >= offset && read.Offset < offset + size)
                    Split(context, load);

        // reading a register whose low lane is unknown
        if (instruction.OpCode != OpCode.VectorShuffle)
        {
            foreach (var (name, lanes) in state)
            {
                if (lanes[0] != UnknownLow || !instruction.Sources.Any(source => source is Register { } read && read.Name == name))
                    continue;

                block.Instructions.Insert(block.Instructions.IndexOf(instruction),
                    new Instruction(instruction.Index, OpCode.NotImplemented, new StringLiteral("vector lane of an unknown value")));
                lanes[0] = null;
            }
        }

        if (instruction.Destination is StackOffset { } overwritten)
            foreach (var (offset, (size, _)) in context.PendingStackCopies.ToList())
                if (overwritten.Offset < offset + size && offset < overwritten.Offset + Math.Max(overwritten.Size, 1))
                    context.PendingStackCopies.Remove(offset);

        switch (instruction)
        {
            case { OpCode: OpCode.VectorShuffle, Operands: [var destination, var first, var second, Immediate { Value: var selectors }] }:
                LowerShuffle(context, block, instruction, destination, first, second, (int)selectors, state);
                return;

            // wide load into a vector register
            case { OpCode: OpCode.Move, Operands: [var destination, var source] } when IsVector(destination, out var name)
                                                                                     && WideLoadSource(source) is { } wide:
            {
                var load = new WideLoad { Block = block, Instruction = instruction };
                context.Loads.Add(load);
                var lanes = new Lane?[4];
                for (var lane = 1; lane < 4; lane++)
                {
                    lanes[lane] = lane * 4 < wide.Size
                        ? new Lane { Block = block, Anchor = instruction, After = true, Value = LaneOf(context, wide.Source, lane, wide.Size), Load = load }
                        : new Lane { Block = block, Anchor = instruction, Value = new FloatLiteral(0), Load = load };
                    load.Lanes[lane] = lanes[lane];
                }

                state[name] = lanes;
                return;
            }

            // register copy: the same lanes
            case { OpCode: OpCode.Move, Operands: [var destination, var source] } when IsVector(destination, out var name) && IsVector(source, out var sourceName):
                state[name] = state.TryGetValue(sourceName, out var copied) ? (Lane?[])copied.Clone() : new Lane?[4];
                return;

            // wide store of a vector register
            case { OpCode: OpCode.Move, Operands: [var destination, var source] } when IsVector(source, out var sourceName)
                                                                                     && StoreSize(destination) is 8 or 16 && state.TryGetValue(sourceName, out var stored):
                StoreLanes(context, block, instruction, destination, stored);
                return;

            // movq rax,xmm1 with two floats packed in it (a Vector2 being returned or passed in a register): the high one
            // goes along in rax_hi, for whoever turns out to need the pair (SmallStructRecovery)
            case { OpCode: OpCode.Move, Operands: [Register { Name: var gprName }, var source] } when !gprName.StartsWith("xmm", StringComparison.Ordinal)
                                                                                                    && !gprName.EndsWith(HighSuffix, StringComparison.Ordinal)
                                                                                                    && IsVector(source, out var packedName)
                                                                                                    && state.TryGetValue(packedName, out var packed)
                                                                                                    && packed[1] is { } high && high != UnknownLow
                                                                                                    && high.Load is not { Split: false }:
            {
                var highValue = Materialize(context, high);
                block.Instructions.Insert(block.Instructions.IndexOf(instruction) + 1,
                    new Instruction(instruction.Index, OpCode.Move, new Register(null, gprName + HighSuffix), highValue) { KeepAlive = true });
                return;
            }
        }

        if (instruction.IsCall || instruction.OpCode == OpCode.IndirectCall)
        {
            // xmm0-5 are volatile on Win64
            foreach (var key in state.Keys.ToList())
                if (key is "xmm0" or "xmm1" or "xmm2" or "xmm3" or "xmm4" or "xmm5")
                    state.Remove(key);
        }

        if (instruction.Destination is { } written && IsVector(written, out var writtenName))
        {
            // a scalar load (movss/movd) zeroes the rest; anything computed, we only know the low lane of (it's the register itself)
            var zeroesUpper = instruction is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Size: 4 } or StackOffset { Size: 4 } or FloatLiteral or Immediate] }
                              || instruction is { OpCode: OpCode.Move, Operands: [_, Register { Name: var fromRegister }] } && !fromRegister.StartsWith("xmm", StringComparison.Ordinal);
            var lanes = new Lane?[4];
            var wholeZero = instruction is { OpCode: OpCode.Move, Operands: [_, Immediate { Value: 0 } or FloatLiteral { Value: 0 }] };
            if (zeroesUpper)
                for (var lane = 1; lane < 4; lane++)
                    lanes[lane] = new Lane { Block = block, Anchor = instruction, Value = new FloatLiteral(0), WholeRegisterZero = wholeZero };
            if (instruction is { OpCode: OpCode.Move, Operands: [_, Register { Name: var gpr } gprRegister] } && !gpr.StartsWith("xmm", StringComparison.Ordinal))
            {
                // movq: the high half of the GPR (what it is - the y of a Vector2, say - is worked out once types are known)
                lanes[1] = new Lane { Block = block, Anchor = instruction, After = true, Value = gprRegister, HighHalf = true };
                instruction.ReadsLowHalf = true;
            }
            state[writtenName] = lanes;
        }
    }

    private static (IOperand Source, int Size)? WideLoadSource(IOperand source) => source switch
    {
        MemoryOperand { Size: 8 or 16 } memory => (memory, memory.Size),
        StackOffset { Size: 8 or 16 } stack => (stack, stack.Size),
        DoubleLiteral literal => (literal, 8),
        _ => null
    };

    private static int StoreSize(IOperand destination) => destination switch
    {
        MemoryOperand memory => memory.Size,
        StackOffset stack => stack.Size,
        _ => 0
    };

    private static bool OnlyLowFloatUsed(WideLoad load)
    {
        if (load.Instruction.Operands[0] is not Register { Name: var name })
            return false;

        var instructions = load.Block.Instructions;
        var uses = 0;

        for (var i = instructions.IndexOf(load.Instruction) + 1; i < instructions.Count; i++)
        {
            var instruction = instructions[i];

            if (instruction.Sources.Any(source => source is Register { } read && read.Name == name))
            {
                if (!instruction.ScalarSingle || instruction.OpCode is OpCode.VectorShuffle or OpCode.NotImplemented)
                    return false;

                uses++;
            }

            if (instruction.Destination is Register { } written && written.Name == name)
                return uses > 0;
        }

        return false; // might live on into another block
    }

    private static IOperand? Offset(IOperand operand, int by, int size) => operand switch
    {
        MemoryOperand memory => new MemoryOperand(memory.Base, memory.Index, memory.Addend + by, memory.Scale, size),
        StackOffset stack => new StackOffset(stack.Offset + by, size),
        _ => null
    };

    // Lane n of a wide value: the 4 bytes at +4n, or for a constant, the constant
    private static IOperand LaneOf(Context context, IOperand wide, int lane, int size)
    {
        if (wide is DoubleLiteral literal)
        {
            var bits = BitConverter.DoubleToInt64Bits(literal.Value);
            return new FloatLiteral(BitConverter.Int32BitsToSingle((int)(lane == 0 ? bits : bits >> 32)));
        }

        if (wide is MemoryOperand { Base: null, Index: null } constant && ReadConstantLane(context, (ulong)constant.Addend + (ulong)(lane * 4)) is { } value)
            return value;

        return Offset(wide, lane * 4, 4)!;
    }

    private static IOperand? ReadConstantLane(Context context, ulong address)
    {
        var binary = context.Method.AppContext.Binary;
        if (!binary.TryMapVirtualAddressToRaw(address, out var raw))
            return null;

        var content = binary.GetRawBinaryContent();
        if (raw < 0 || raw + 4 > content.Length)
            return null;

        var bits = BitConverter.ToInt32(content.Slice((int)raw, 4).ToArray(), 0);
        var single = BitConverter.Int32BitsToSingle(bits);

        return single == 0 || !float.IsNaN(single) && !float.IsInfinity(single) && Math.Abs(single) is > 1e-10f and < 1e10f
            ? new FloatLiteral(single)
            : new Immediate(bits);
    }

    // The wide load is packed floats after all: it becomes a load of the first one, the rest go into temporaries
    private static void Split(Context context, WideLoad load)
    {
        if (load.Split)
            return;

        load.Split = true;

        var source = load.Instruction.Operands[1];
        load.Instruction.SetOperand(1, source switch
        {
            DoubleLiteral => LaneOf(context, source, 0, 8),
            MemoryOperand { Base: null, Index: null } => LaneOf(context, source, 0, ((MemoryOperand)source).Size),
            _ => Offset(source, 0, 4) ?? source
        });

        // copies made before we knew
        foreach (var (block, store) in load.PendingStores)
        {
            var size = StoreSize(store.Operands[0]);
            if (IsVector(store.Operands[1], out _))
                SplitStore(context, block, store, store.Operands[0], size, lane => load.Lanes[lane]);
        }

        load.PendingStores.Clear();
        foreach (var (offset, (_, pending)) in context.PendingStackCopies.ToList())
            if (pending == load)
                context.PendingStackCopies.Remove(offset);
    }

    // A join's lanes: what every predecessor agrees on, or (lazily) a temporary each of them sets
    private static Dictionary<string, Lane?[]> Merge(Block block, List<(Block Predecessor, Dictionary<string, Lane?[]> State)> incoming)
    {
        var merged = new Dictionary<string, Lane?[]>();
        foreach (var name in incoming[0].State.Keys)
        {
            if (!incoming.All(i => i.State.ContainsKey(name)))
                continue;

            var lanes = new Lane?[4];
            for (var lane = 1; lane < 4; lane++)
            {
                var sources = incoming.Select(i => i.State[name][lane]).ToList();
                if (sources.Any(source => source == null || source == UnknownLow))
                    continue;

                // part of a wide load not (yet) known to be floats: a whole copy, which a join doesn't take apart
                if (sources.Any(source => source!.Load is { Split: false }) && sources.Distinct().Count() > 1)
                    continue;

                if (sources.Distinct().Count() == 1)
                    lanes[lane] = sources[0];
                else if (sources.All(source => source!.Load == null && source.Value is FloatLiteral or Immediate) && sources.Select(source => source!.Value).Distinct().Count() == 1)
                    lanes[lane] = sources[0]; // the same constant everywhere (a zeroed lane, typically)
                else
                    lanes[lane] = new Lane
                    {
                        Block = block, Anchor = null!, Value = new FloatLiteral(0),
                        MergeOf = incoming.Select((i, n) => (i.Predecessor, sources[n]!)).ToList(),
                    };
            }

            // the low lane is the register itself: SSA joins it
            merged[name] = lanes;
        }

        return merged;
    }

    // An 8 byte general register spilled to the stack and only ever read back as two 4 byte halves is a small struct
    // (a Vector2 argument, say) being taken apart: the halves are stored separately so each read finds its own,
    // and SmallStructRecovery names them once the register's type is known
    private static void SplitPackedSpills(ISILControlFlowGraph graph)
    {
        var instructions = graph.Instructions.ToList();
        foreach (var block in graph.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                if (block.Instructions[i] is not { OpCode: OpCode.Move, Operands: [StackOffset { Size: 8 } slot, Register { } value] } store
                    || value.Name.StartsWith("xmm", StringComparison.Ordinal) || value.Name.EndsWith(HighSuffix, StringComparison.Ordinal))
                    continue;

                var lowReads = 0;
                var highReads = 0;
                var usable = true;
                foreach (var other in instructions)
                {
                    if (ReferenceEquals(other, store))
                        continue;

                    foreach (var operand in other.Operands)
                    {
                        switch (operand)
                        {
                            case StackOffset access when access.Offset >= slot.Offset && access.Offset < slot.Offset + 8:
                                if (other.Destination is StackOffset written && written.Offset == access.Offset)
                                    usable = false; // written again
                                else if (access.Size == 4 && access.Offset == slot.Offset)
                                    lowReads++;
                                else if (access.Size == 4 && access.Offset == slot.Offset + 4)
                                    highReads++;
                                else
                                    usable = false;
                                break;
                            case StackOffset wide when wide.Offset < slot.Offset && wide.Offset + Math.Max(wide.Size, 1) > slot.Offset:
                                usable = false;
                                break;
                            case AddressOf { Target: StackOffset addressed } when addressed.Offset <= slot.Offset + 8 && addressed.Offset > slot.Offset - 64:
                                usable = false; // part of something addressed as a whole
                                break;
                        }
                    }

                    if (!usable)
                        break;
                }

                if (!usable || lowReads == 0 || highReads == 0)
                    continue;

                store.SetOperand(0, new StackOffset(slot.Offset, 4));
                store.ReadsLowHalf = true;
                block.Instructions.Insert(i + 1, new Instruction(store.Index, OpCode.Move, new StackOffset(slot.Offset + 4, 4), value) { ReadsHighHalf = true });
                i++;
            }
        }
    }

    private static Register Materialize(Context context, Lane lane)
    {
        if (lane.Materialized is { } done)
            return done;

        if (lane.MergeOf is { } merges)
        {
            var joined = new Register(null, $"LANE_{context.Temporaries++}");
            lane.Materialized = joined;
            foreach (var (predecessor, source) in merges)
            {
                var value = Materialize(context, source);
                var instructions = predecessor.Instructions;
                var at = instructions.Count > 0 && instructions[^1].OpCode is OpCode.Jump or OpCode.ConditionalJump or OpCode.Return
                    ? instructions.Count - 1
                    : instructions.Count;
                instructions.Insert(at, new Instruction(at > 0 ? instructions[at - 1].Index : 0, OpCode.Move, joined, value));
            }

            return joined;
        }

        if (lane.Load != null)
            Split(context, lane.Load);

        var temporary = new Register(null, $"LANE_{context.Temporaries++}");
        var index = lane.Block.Instructions.IndexOf(lane.Anchor);
        lane.Block.Instructions.Insert(lane.After ? index + 1 : index, new Instruction(lane.Anchor.Index, OpCode.Move, temporary, lane.Value) { ReadsHighHalf = lane.HighHalf });
        lane.Materialized = temporary;
        return temporary;
    }

    private static void StoreLanes(Context context, Block block, Instruction store, IOperand destination, Lane?[] lanes)
    {
        var size = StoreSize(destination);
        var count = size / 4;

        if (Enumerable.Range(1, count - 1).Any(lane => lanes[lane] == null))
            return; // something we can't account for

        // storing a register zeroed as a whole is zeroing that memory, which is clearer left as one store
        if (Enumerable.Range(1, count - 1).All(lane => lanes[lane]!.WholeRegisterZero))
            return;

        // only lanes of a load not yet known to be floats: an ordinary copy, unless it turns out otherwise
        var loads = Enumerable.Range(1, count - 1).Select(lane => lanes[lane]!.Load).ToList();
        if (loads.All(l => l != null && !l.Split) && loads.Distinct().Count() == 1)
        {
            loads[0]!.PendingStores.Add((block, store));
            if (destination is StackOffset slot)
                context.PendingStackCopies[slot.Offset] = (size, loads[0]!);
            return;
        }

        SplitStore(context, block, store, destination, size, lane => lanes[lane]);
    }

    private static void SplitStore(Context context, Block block, Instruction store, IOperand destination, int size, Func<int, Lane?> laneOf)
    {
        var count = size / 4;
        var stores = new List<Instruction>();

        for (var lane = 1; lane < count; lane++)
        {
            if (laneOf(lane) is not { } known || Offset(destination, lane * 4, 4) is not { } target)
                return;

            stores.Add(new Instruction(store.Index, OpCode.Move, target, Materialize(context, known)));
        }

        store.SetOperand(0, Offset(destination, 0, 4)!);
        block.Instructions.InsertRange(block.Instructions.IndexOf(store) + 1, stores);
    }

    // How wide the first use of a shuffled register reads it: a move to a GPR is a movq, a store has its size
    private static int UseWidth(Block block, Instruction shuffle, IOperand destination)
    {
        if (!IsVector(destination, out var name))
            return 4;

        for (var i = block.Instructions.IndexOf(shuffle) + 1; i < block.Instructions.Count; i++)
        {
            var instruction = block.Instructions[i];
            if (!instruction.Sources.Any(source => source is Register { } read && read.Name == name))
            {
                if (instruction.Destination is Register { } written && written.Name == name)
                    return 4;
                continue;
            }

            return instruction switch
            {
                { OpCode: OpCode.Move, Operands: [Register { Name: var to }, _] } when !to.StartsWith("xmm", StringComparison.Ordinal) => 8,
                { OpCode: OpCode.Move, Operands: [var store, _] } when StoreSize(store) is 8 or 16 => StoreSize(store),
                _ => 4
            };
        }

        return 4;
    }

    // Lanes 0..count-1 (lane 0 given separately) are consecutive 4 byte pieces of one memory load: that memory, wide
    private static IOperand? ContiguousRun(Lane low, Lane?[] lanes, int count)
    {
        if (low.Value is not (MemoryOperand { Size: 4 } or StackOffset { Size: 4 }))
            return null;

        for (var lane = 1; lane < count; lane++)
        {
            if (lanes[lane] is not { } next || next.Block != low.Block || next.Anchor != low.Anchor || next.After != low.After
                || !Equals(next.Value, Offset(low.Value, lane * 4, 4)))
                return null;
        }

        return Offset(low.Value, 0, count * 4);
    }

    private static void LowerShuffle(Context context, Block block, Instruction shuffle, IOperand destination, IOperand first, IOperand second, int selectors,
        Dictionary<string, Lane?[]> state)
    {
        var firstLanes = IsVector(first, out var firstName) ? state.GetValueOrDefault(firstName) ?? new Lane?[4] : null;
        var secondLanes = IsVector(second, out var secondName) ? state.GetValueOrDefault(secondName) ?? new Lane?[4] : null;

        // what lane n of a source holds, before the shuffle writes anything
        Lane? SourceLane(int selector)
        {
            var (operand, lanes, lane) = selector < 4 ? (first, firstLanes, selector) : (second, secondLanes, selector - 4);

            if (lane == 0 && lanes != null)
                return lanes[0] == UnknownLow ? null : new Lane { Block = block, Anchor = shuffle, Value = operand }; // the register itself, as it is here

            if (lanes != null)
                return lanes[lane];

            // a memory operand: the vector's in memory
            return Offset(operand, lane * 4, 4) is { } memory ? new Lane { Block = block, Anchor = shuffle, Value = memory } : null;
        }

        var result = new Lane?[4];
        for (var lane = 1; lane < 4; lane++)
        {
            var selector = (selectors >> (lane * 4)) & 0xF;
            result[lane] = selector == Zero ? new Lane { Block = block, Anchor = shuffle, Value = new FloatLiteral(0) } : SourceLane(selector);
        }

        // and the low lane, which the register itself stands for
        var low = selectors & 0xF;

        // psrldq 8 / movq rdx,xmm0: a qword (or more) out of a wide load
        if ((selectors & 0x10000) != 0 && low != Zero && UseWidth(block, shuffle, destination) is > 4 and var width
            && SourceLane(low) is { } first0 && ContiguousRun(first0, result, width / 4) is { } wideValue)
        {
            var wideLane = new Lane { Block = first0.Block, Anchor = first0.Anchor, After = first0.After, Value = wideValue };
            if (IsVector(destination, out var wideDestination))
                state[wideDestination] = result;
            shuffle.Rewrite(OpCode.Move, destination, Materialize(context, wideLane));
            return;
        }
        IOperand? lowValue = low switch
        {
            Zero => new FloatLiteral(0),
            0 when firstLanes != null => firstLanes[0] == UnknownLow ? null : first,
            4 when secondLanes != null => secondLanes[0] == UnknownLow ? null : second,
            _ => SourceLane(low) is { } known
                ? known.Value is MemoryOperand or StackOffset or FloatLiteral or Immediate && known.Load == null ? known.Value : Materialize(context, known)
                : null
        };

        if (IsVector(destination, out var destinationName))
            state[destinationName] = result;

        if (lowValue == null)
        {
            shuffle.Rewrite(OpCode.Nop);
            if (IsVector(destination, out _))
                result[0] = UnknownLow;
            else
                shuffle.Rewrite(OpCode.NotImplemented, new StringLiteral("vector lane of an unknown value"));
            return;
        }

        if (lowValue.Equals(destination))
            shuffle.Rewrite(OpCode.Nop);
        else
            shuffle.Rewrite(OpCode.Move, destination, lowValue);
    }
}
