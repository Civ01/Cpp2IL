using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Copies of big structs are inlined by MSVC as an unrolled loop moving 128 bytes per iteration with pairs of
/// 16 byte loads/stores through two advancing pointers, followed by a straight-line tail for the remainder:
/// <code>
///   mov edx, 4
/// loop:
///   movups xmm0,[rax]      movups [rcx],xmm0   ...   lea rcx,[rcx+80h]   lea rax,[rax+80h]
///   sub rdx,1              jne loop
///   movups xmm0,[rax]      movups [rcx],xmm0   ...   mov rax,[rax+30h]   mov [rcx+30h],rax
/// </code>
/// This pass replaces the loop and tail with a single sized memory-to-memory move of the whole thing, which the
/// later struct passes can then type. It also resolves pointers to stack slots held in registers within a block
/// (lea rcx,[rsp+80h] ... mov [rcx+8],eax), so those stores are seen as stack slot accesses.
///
/// Runs on ISIL registers with absolute stack offsets, between StackAnalyzer.CorrectOffsets and
/// StackStructRecovery.
/// </summary>
public static class InlineMemcpyRecovery
{
    /// <summary>Debugging aid: receives a reason whenever a candidate loop is rejected.</summary>
    public static System.Action<string>? Debug;

    private static readonly HashSet<string> FlagRegisters = ["CF", "OF", "SF", "ZF", "PF", "TEMP", "TEMP1", "TEMP2", "TEMP3", "TEMP4", "TEMP5"];

    private static readonly HashSet<string> VolatileRegisters = ["rax", "rcx", "rdx", "r8", "r9", "r10", "r11"];

    private sealed class CopyParse
    {
        public readonly Dictionary<string, long> Displacement = [];
        public readonly Dictionary<string, (string Base, long Offset, int Size)> Loaded = [];
        public readonly List<(string Source, long SourceOffset, string Destination, long DestinationOffset, int Size, Instruction Load, Instruction Store)> Pairs = [];
        public readonly Dictionary<string, Instruction> LoadInstructions = [];

        public long DisplacementOf(string register) => Displacement.GetValueOrDefault(register);

        // Tries to consume a chunk load or store. Returns false if the instruction is neither.
        public bool TryConsumeCopy(Instruction instruction)
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [Register target, MemoryOperand { Base: Register loadBase, Index: null, Scale: 0, Size: > 0 } load] })
            {
                Loaded[target.Name] = (loadBase.Name, DisplacementOf(loadBase.Name) + load.Addend, load.Size);
                LoadInstructions[target.Name] = instruction;
                return true;
            }

            if (instruction is { OpCode: OpCode.Move, Operands: [MemoryOperand { Base: Register storeBase, Index: null, Scale: 0, Size: > 0 } store, Register value] }
                && Loaded.TryGetValue(value.Name, out var source) && source.Size == store.Size)
            {
                Pairs.Add((source.Base, source.Offset, storeBase.Name, DisplacementOf(storeBase.Name) + store.Addend, store.Size, LoadInstructions[value.Name], instruction));
                return true;
            }

            return false;
        }

        // The pairs copy [0, length) from one base to the same offsets of another, contiguously
        public bool IsContiguousCopy(out string source, out string destination, out long length)
        {
            source = destination = "";
            length = 0;

            if (Pairs.Count == 0)
                return false;

            source = Pairs[0].Source;
            destination = Pairs[0].Destination;

            if (source == destination)
                return false;

            var expected = 0L;
            foreach (var pair in Pairs.OrderBy(p => p.DestinationOffset))
            {
                if (pair.Source != source || pair.Destination != destination || pair.SourceOffset != pair.DestinationOffset || pair.DestinationOffset != expected)
                    return false;

                expected += pair.Size;
            }

            length = expected;
            return true;
        }
    }

    public static void Run(MethodAnalysisContext method, ISILControlFlowGraph graph)
    {
        // Collapsing one loop can make an earlier constant reachable for the next, so go until nothing changes
        bool collapsed;
        var rounds = 0;
        do
        {
            collapsed = false;
            foreach (var loop in graph.Blocks.ToList())
                collapsed |= TryCollapseLoop(graph, loop);
        } while (collapsed && ++rounds < 8);

        ResolvePointersToStack(graph);
    }

    private static bool TryCollapseLoop(ISILControlFlowGraph graph, Block loop)
    {
        if (!loop.Successors.Contains(loop) || loop.Instructions.Count < 3)
            return false;

        var jump = loop.Instructions[^1];
        if (jump.OpCode != OpCode.ConditionalJump)
            return false;

        var jumpsToSelf = jump.Operands[0] switch
        {
            Block targetBlock => ReferenceEquals(targetBlock, loop),
            Instruction targetInstruction => ReferenceEquals(targetInstruction, loop.Instructions[0]),
            _ => false
        };

        if (!jumpsToSelf)
            { Debug?.Invoke($"memcpy loop B{loop.ID} rejected at check 1"); return false; }

        // Body: chunk copies, pointer increments, one counter decrement and its flag computation
        var body = new CopyParse();
        string? counter = null;

        for (var i = 0; i < loop.Instructions.Count - 1; i++)
        {
            var instruction = loop.Instructions[i];

            if (body.TryConsumeCopy(instruction))
                continue;

            switch (instruction)
            {
                case { OpCode: OpCode.Add, Operands: [Register sum, Register addend, Immediate step] } when sum.Name == addend.Name:
                    body.Displacement[sum.Name] = body.DisplacementOf(sum.Name) + step.Value;
                    continue;
                case { OpCode: OpCode.Subtract, Operands: [Register difference, Register minuend, Immediate { Value: 1 }] } when difference.Name == minuend.Name && counter == null:
                    counter = difference.Name;
                    continue;
                case { Destination: Register flag } when FlagRegisters.Contains(flag.Name)
                                                       && instruction.Operands.Skip(1).All(o => IsFlagInput(o, counter ?? PendingCounter(loop, i))):
                    continue;
            }

            { Debug?.Invoke($"memcpy loop B{loop.ID} rejected at check 2"); return false; }
        }

        if (counter == null || !body.IsContiguousCopy(out var source, out var destination, out var stride))
            { Debug?.Invoke($"memcpy loop B{loop.ID} rejected at check 3"); return false; }

        if (body.DisplacementOf(source) != stride || body.DisplacementOf(destination) != stride)
            { Debug?.Invoke($"memcpy loop B{loop.ID} rejected at check 4"); return false; }

        // Exactly one way in (the preheader) and one way out (straight into the tail)
        var preheaders = loop.Predecessors.Where(p => p != loop).Distinct().ToList();
        var exits = loop.Successors.Where(s => s != loop).Distinct().ToList();
        if (preheaders is not [{ } preheader] || exits is not [{ } tail] || tail.Predecessors.Distinct().Count() != 1)
            { Debug?.Invoke($"memcpy loop B{loop.ID} rejected at check 5"); return false; }

        if (FindConstant(preheader, counter) is not { } iterations || iterations <= 0)
            { Debug?.Invoke($"memcpy loop B{loop.ID} rejected at check 6"); return false; }

        // The tail carries on with the same pointers, from where the loop left them. The compiler interleaves
        // unrelated setup for whatever comes next into it, which is fine as long as it stays clear of the copy.
        var rest = new CopyParse();
        var consumed = new List<Instruction>();
        var sourceAlive = true;
        var tailEnd = 0;

        for (; tailEnd < tail.Instructions.Count; tailEnd++)
        {
            var instruction = tail.Instructions[tailEnd];

            var isSourceLoad = instruction is { OpCode: OpCode.Move, Operands: [Register, MemoryOperand { Base: Register { } loadBase }] } && loadBase.Name == source;
            var isDestinationStore = instruction is { OpCode: OpCode.Move, Operands: [MemoryOperand { Base: Register { } storeBase }, Register] } && storeBase.Name == destination;

            if ((isSourceLoad && sourceAlive || isDestinationStore) && rest.TryConsumeCopy(instruction))
            {
                consumed.Add(instruction);
                continue;
            }

            if (isSourceLoad || isDestinationStore)
                break;

            if (instruction.IsCall || instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump or OpCode.Return or OpCode.IndirectCall or OpCode.IndirectJump or OpCode.Nop)
                break;

            // Something else touching the destination pointer, or writing memory, ends the tail
            if (Touches(instruction, destination) || instruction.Operands.Count > 0 && instruction.Operands[0] is MemoryOperand or StackOffset)
                break;

            // Reading the source pointer other than to copy from it ends it too
            if (instruction.Sources.Any(o => o is Register r && r.Name == source || o is MemoryOperand { Base: Register { } b } && b.Name == source))
                break;

            // Clobbering a chunk that's been loaded but not yet stored would lose it
            if (instruction.Destination is Register written)
            {
                if (rest.Loaded.ContainsKey(written.Name) && !rest.Pairs.Any(p => ReferenceEquals(p.Load, rest.LoadInstructions[written.Name])))
                    break;

                if (written.Name == source)
                    sourceAlive = false;

                rest.Loaded.Remove(written.Name);
            }
        }

        // Only keep tail chunks that were actually stored (a dangling load isn't part of the copy)
        long remainder = 0;
        if (rest.Pairs.Count > 0)
        {
            if (!rest.IsContiguousCopy(out var tailSource, out var tailDestination, out remainder) || tailSource != source || tailDestination != destination)
                { Debug?.Invoke($"memcpy loop B{loop.ID} rejected at check 7"); return false; }
        }

        var pairedInstructions = rest.Pairs.SelectMany(p => new[] { p.Load, p.Store }).ToHashSet();
        if (consumed.Any(c => !pairedInstructions.Contains(c)))
            return false; // a load that was not stored, cannot reason about it

        // After the copy the advanced pointers must be dead
        if (sourceAlive && !DeadAfter(tail, tailEnd, source) || !DeadAfter(tail, tailEnd, destination))
            { Debug?.Invoke($"memcpy loop B{loop.ID} rejected at check 8"); return false; }

        var total = (int)(iterations * stride + remainder);

        var copy = new Instruction(loop.Instructions[0].Index, OpCode.Move,
            SizedOperand(preheader, destination, total),
            SizedOperand(preheader, source, total));

        loop.Instructions.Clear();
        loop.Instructions.Add(copy);
        loop.Successors.RemoveAll(s => s == loop);
        loop.Predecessors.RemoveAll(p => p == loop);
        loop.BlockType = BlockType.Fall;

        foreach (var instruction in consumed)
        {
            instruction.OpCode = OpCode.Nop;
            instruction.SetOperands();
        }

        return true;
    }

    private static bool IsFlagInput(IOperand operand, string? counter) => operand switch
    {
        Immediate => true,
        Register register => FlagRegisters.Contains(register.Name) || register.Name == counter,
        _ => false
    };

    // The counter's decrement is in the body after its flags are computed from it (sub sets flags like cmp)
    private static string? PendingCounter(Block loop, int fromIndex)
    {
        for (var i = fromIndex; i < loop.Instructions.Count; i++)
            if (loop.Instructions[i] is { OpCode: OpCode.Subtract, Operands: [Register difference, Register minuend, Immediate { Value: 1 }] } && difference.Name == minuend.Name)
                return difference.Name;

        return null;
    }

    // The value a register holds at the end of the block, if it's (a copy of) a constant set in this block or, failing
    // that, in the chain of single predecessors leading to it
    private static long? FindConstant(Block block, string register) => FindConstant(block, block.Instructions.Count, register, 0);

    private static long? FindConstant(Block block, int before, string register, int depth)
    {
        while (depth++ < 16)
        {
            for (var i = before - 1; i >= 0; i--)
            {
                var instruction = block.Instructions[i];

                if ((instruction.IsCall || instruction.OpCode == OpCode.IndirectCall) && VolatileRegisters.Contains(register))
                    return null;

                if (instruction.Destination is not Register written || written.Name != register)
                    continue;

                return instruction switch
                {
                    { OpCode: OpCode.Move, Operands: [_, Immediate value] } => value.Value,
                    { OpCode: OpCode.Move, Operands: [_, Register copied] } => FindConstant(block, i, copied.Name, depth),
                    _ => null
                };
            }

            var predecessors = block.Predecessors.Distinct().ToList();
            if (predecessors is not [{ } only] || only == block)
                return null;

            block = only;
            before = block.Instructions.Count;
        }

        return null;
    }

    // What the pointer register held on entry to the loop, as a sized memory operand at that address
    private static IOperand SizedOperand(Block preheader, string register, int size)
    {
        for (var i = preheader.Instructions.Count - 1; i >= 0; i--)
        {
            var instruction = preheader.Instructions[i];
            if (instruction.Destination is not Register written || written.Name != register)
                continue;

            if (instruction is { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: StackOffset slot }] })
                return new StackOffset(slot.Offset, size);

            break;
        }

        return new MemoryOperand(new Register(null, register), size: size);
    }

    private static bool Touches(Instruction instruction, string register)
        => instruction.Operands.Any(o => o switch
        {
            Register r => r.Name == register,
            MemoryOperand m => m.Base is Register { Name: var b } && b == register || m.Index is Register { Name: var x } && x == register,
            _ => false
        });

    // Is the register overwritten (or clobbered by a call) before it's next read, on every path from the given point?
    private static bool DeadAfter(Block block, int index, string register)
    {
        var visited = new HashSet<Block>();
        var pending = new Queue<(Block Block, int From)>();
        pending.Enqueue((block, index));

        while (pending.Count > 0)
        {
            var (current, from) = pending.Dequeue();
            var pathEnded = false;

            for (var i = from; i < current.Instructions.Count && !pathEnded; i++)
            {
                var instruction = current.Instructions[i];

                // A call to something unmanaged lists every argument register, used or not. Nothing sane hands a
                // copy loop's leftover pointer to one, so take it as clobbering rather than reading them.
                if (instruction.IsCall && instruction.Operands[0] is Immediate && instruction.Operands.Count >= (instruction.OpCode == OpCode.CallVoid ? 1 : 2) + 8)
                {
                    if (VolatileRegisters.Contains(register))
                    {
                        pathEnded = true;
                        continue;
                    }
                }

                if (instruction.Sources.Any(s => s is Register r && r.Name == register)
                    || instruction.Operands.Any(o => o is MemoryOperand m && (m.Base is Register { Name: var b } && b == register || m.Index is Register { Name: var x } && x == register)))
                    return false;

                if (instruction.Destination is Register written && written.Name == register)
                    pathEnded = true;
                else if (instruction.IsCall || instruction.OpCode == OpCode.IndirectCall)
                {
                    if (!VolatileRegisters.Contains(register))
                        continue;

                    pathEnded = true;
                }
                else if (instruction.OpCode == OpCode.Return)
                    pathEnded = true; // Return's value operand was checked as a read above
            }

            if (pathEnded)
                continue;

            foreach (var successor in current.Successors)
            {
                if (successor.BlockType == BlockType.Exit)
                    continue;

                if (visited.Add(successor))
                    pending.Enqueue((successor, 0));
            }

            if (visited.Count > 256)
                return false; // give up rather than walk a huge method
        }

        return true;
    }

    /// <summary>
    /// Within a block (and on into a block with no other way in), [reg+x] where reg was set to the address of a
    /// stack slot is just that slot plus x.
    /// </summary>
    private static void ResolvePointersToStack(ISILControlFlowGraph graph)
    {
        var outStates = new Dictionary<Block, Dictionary<string, int>>();

        foreach (var block in graph.Blocks)
        {
            if (outStates.ContainsKey(block))
                continue;

            // Walk chains of single-predecessor blocks starting here
            var current = block;
            var state = new Dictionary<string, int>();

            while (current != null && !outStates.ContainsKey(current))
            {
                ApplyToBlock(current, state);
                outStates[current] = state;

                var next = current.Successors.Count == 1 ? current.Successors[0] : null;
                if (next == null || next.Predecessors.Distinct().Count() != 1 || current.BlockType is BlockType.Call or BlockType.TailCall)
                    break;

                state = new Dictionary<string, int>(state);
                current = next;
            }
        }
    }

    private static void ApplyToBlock(Block block, Dictionary<string, int> pointers)
    {
        foreach (var instruction in block.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.Operands[i] is MemoryOperand { Base: Register pointer, Index: null, Scale: 0 } memory
                    && pointers.TryGetValue(pointer.Name, out var slot))
                    instruction.SetOperand(i, new StackOffset((int)(slot + memory.Addend), memory.Size));
            }

            if (instruction.IsCall)
            {
                foreach (var clobbered in VolatileRegisters)
                    pointers.Remove(clobbered);
            }

            if (instruction.Destination is Register written)
            {
                if (instruction is { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: StackOffset addressed }] })
                    pointers[written.Name] = addressed.Offset;
                else
                    pointers.Remove(written.Name);
            }
        }
    }
}
