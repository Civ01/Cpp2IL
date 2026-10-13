using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public class StackAnalyzer
{
    [DebuggerDisplay("Size = {Size}")]
    private class StackState
    {
        public int Size;
        public StackState Copy() => new() { Size = this.Size };
    }

    private Dictionary<Block, StackState> _inComingState = [];
    private Dictionary<Block, StackState> _outGoingState = [];
    private Dictionary<Instruction, StackState> _instructionState = [];

    /// <summary>
    /// Max allowed count of blocks to visit (-1 for no limit).
    /// </summary>
    public static int MaxBlockVisitCount = 500000; //High enough to not be legitimately hit, but still give up if something loops infinitely.

    public static void Analyze(MethodAnalysisContext method)
    {
        var analyzer = new StackAnalyzer();

        var graph = method.ControlFlowGraph!;
        graph.RemoveUnreachableBlocks(); // Without this indirect jumps (in try catch i think) cause some weird stuff

        analyzer._inComingState = new Dictionary<Block, StackState> { { graph.EntryBlock, new StackState() } };

        analyzer.TraverseGraph(graph.EntryBlock);

        // The exit block has no outgoing state if it was never reached (e.g. every path loops or
        // throws). That's fine - just skip the end-of-method stack balance check in that case.
        if (analyzer._outGoingState.TryGetValue(graph.ExitBlock, out var outDelta) && outDelta.Size != 0)
        {
            var outText = outDelta.Size < 0 ? "-" + (-outDelta.Size).ToString("X") : outDelta.Size.ToString("X");
            method.AddWarning($"Method ends with non empty stack ({outText}), the output could be wrong!");
        }

        analyzer.ResolveFrameAliases(graph);
        analyzer.CorrectOffsets(graph);
        NativeHelperRecovery.RunEarly(method, graph);
        InlinedIsInstRecovery.Run(method, graph);
        InlinedInterfaceLookupRemoval.Run(method, graph);
        InlineMemcpyRecovery.Run(method, graph);
        FakeBoxRecovery.Run(method, graph);
        VectorLaneRecovery.Run(method, graph);
        StackStructRecovery.Run(method, graph);
        ReplaceStackWithRegisters(method);

        graph.RemoveNops();
        graph.RemoveEmptyBlocks();
    }

    // consider mov [reg], [stack pointer]
    // now we need to handle [reg] as if it were a stack pointer, forever.
    private void ResolveFrameAliases(ISILControlFlowGraph graph)
    {
        var aliases = new Dictionary<string, int>();
        var aliasDefinitions = new HashSet<Instruction>();

        foreach (var instruction in graph.EntryBlock.Successors.SelectMany(b => b.Instructions))
        {
            if (!_instructionState.TryGetValue(instruction, out var atCopy))
                continue;

            // mov reg, rsp
            if (instruction is { OpCode: OpCode.Move, Operands: [Register destination, Register { Name: "rsp" }] })
            {
                aliases[destination.Name] = atCopy.Size;
                aliasDefinitions.Add(instruction);
            }
            // lea reg, [rsp+x] - MSVC sets up rbp as a frame pointer this way (lea rbp,[rsp-98h]) in larger methods
            // (not into an argument register: lea rdx,[rsp+20h] is the address of a struct being passed, and that register
            // held something else before it, which treating it as the frame everywhere would replace)
            else if (instruction is { OpCode: OpCode.Move, Operands: [Register { Name: not ("rsp" or "rax" or "rcx" or "rdx" or "r8" or "r9") } leaDestination, AddressOf { Target: StackOffset frameSlot }] })
            {
                aliases[leaDestination.Name] = atCopy.Size + frameSlot.Offset;
                aliasDefinitions.Add(instruction);
            }
            // mov rax,rsp / lea rbp,[rax-87h]: a frame register derived from another alias
            else if (instruction is { OpCode: OpCode.Add or OpCode.Subtract, Operands: [Register derived, Register derivedFrom, Immediate derivedBy] }
                     && derived.Name != derivedFrom.Name && derived.Name != "rsp" && aliases.TryGetValue(derivedFrom.Name, out var fromOffset))
            {
                aliases[derived.Name] = (int)(fromOffset + (instruction.OpCode == OpCode.Add ? derivedBy.Value : -derivedBy.Value));
                aliasDefinitions.Add(instruction);
            }
        }

        if (aliases.Count == 0)
            return;

        // Up to its first reassignment in the block that set it up, an alias is certainly the frame: the prologue's
        // mov rax,rsp / mov [rax+10h],rdx (spilling arguments to their home slots) uses it before rax is reused
        foreach (var definition in aliasDefinitions)
        {
            if (definition.Operands[0] is not Register { Name: var aliasName } || !aliases.TryGetValue(aliasName, out var aliasOffset))
                continue;
            var block = graph.EntryBlock.Successors.FirstOrDefault(b => b.Instructions.Contains(definition));
            if (block == null)
                continue;

            for (var at = block.Instructions.IndexOf(definition) + 1; at < block.Instructions.Count; at++)
            {
                var instruction = block.Instructions[at];
                if (aliasDefinitions.Contains(instruction) || !_instructionState.TryGetValue(instruction, out var here))
                    continue;

                for (var i = 0; i < instruction.Operands.Count; i++)
                    if (instruction.Operands[i] is MemoryOperand { Index: null, Scale: 0, Base: Register { } frameBase } memory && frameBase.Name == aliasName)
                        instruction.SetOperand(i, new StackOffset((int)(aliasOffset + memory.Addend - here.Size), memory.Size));

                if (instruction.Destination is Register written && written.Name == aliasName)
                    break;
            }
        }

        // Following a register that gets reassigned would need flow analysis, so stop trusting it entirely.
        // The exception is the epilogue restoring the caller's value from the stack (pop rbp), after which
        // the register is never used as a frame base again.
        foreach (var instruction in graph.Instructions)
        {
            if (aliasDefinitions.Contains(instruction))
                continue;

            if (instruction is { OpCode: OpCode.Move, Operands: [Register, StackOffset] })
                continue;

            if (instruction.Destination is Register written)
                aliases.Remove(written.Name);
        }

        if (aliases.Count == 0)
            return;

        foreach (var instruction in graph.Instructions)
        {
            if (!_instructionState.TryGetValue(instruction, out var state))
                continue;

            if (aliasDefinitions.Contains(instruction))
                continue;

            // lea reg, [frame+x] - lowered to an add/sub/move of the frame register - is the address of a stack slot
            if (instruction is { OpCode: OpCode.Add or OpCode.Subtract, Operands: [Register addressDestination, Register { } addressBase, Immediate displacement] }
                && aliases.TryGetValue(addressBase.Name, out var addressFrame))
            {
                var delta = instruction.OpCode == OpCode.Add ? displacement.Value : -displacement.Value;
                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(addressDestination, new AddressOf(new StackOffset((int)(addressFrame + delta - state.Size))));
                continue;
            }

            if (instruction is { OpCode: OpCode.Move, Operands: [Register copyDestination, Register { } copySource] }
                && aliases.TryGetValue(copySource.Name, out var copyFrame) && !aliases.ContainsKey(copyDestination.Name))
            {
                instruction.SetOperands(copyDestination, new AddressOf(new StackOffset((int)(copyFrame - state.Size))));
                continue;
            }

            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.Operands[i] is not MemoryOperand { Index: null, Scale: 0, Base: Register frameBase } memory)
                    continue;

                if (!aliases.TryGetValue(frameBase.Name, out var frameOffset))
                    continue;

                instruction.SetOperand(i, new StackOffset((int)(frameOffset + memory.Addend - state.Size), memory.Size));
            }
        }

        // The frame register itself is now dead; drop its setup so it doesn't linger as a bogus local
        foreach (var definition in aliasDefinitions)
        {
            if (definition.Operands[0] is Register { Name: not "rsp" } frameRegister && definition.Operands[1] is AddressOf
                && aliases.ContainsKey(frameRegister.Name)
                && !graph.Instructions.Any(other => !ReferenceEquals(other, definition) && other.OpCode != OpCode.ShiftStack
                    && (other.Sources.Any(source => source is Register used && used.Name == frameRegister.Name)
                        || other.Operands.Any(operand => operand is MemoryOperand memory
                            && (memory.Base is Register { } b && b.Name == frameRegister.Name || memory.Index is Register { } x && x.Name == frameRegister.Name)))))
            {
                definition.OpCode = OpCode.Nop;
                definition.SetOperands();
            }
        }
    }

    private void CorrectOffsets(ISILControlFlowGraph graph)
    {
        foreach (var block in graph.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction is { OpCode: OpCode.ShiftStack })
                {
                    // Nop the shift stack instruction
                    instruction.OpCode = OpCode.Nop;
                    instruction.SetOperands();
                    continue;
                }

                int? state = null;

                // Correct offset for stack operands.
                for (var i = 0; i < instruction.Operands.Count; i++)
                {
                    var op = instruction.Operands[i];

                    var slot = op switch
                    {
                        StackOffset direct => direct,
                        AddressOf { Target: StackOffset addressed } => addressed,
                        _ => (StackOffset?)null
                    };

                    if (slot is { } offset)
                    {
                        // This can only be done before modifying any of the instruction operands,
                        // as doing so will make the dictionary lookup impossible.
                        state ??= _instructionState[instruction].Size;

                        var actual = new StackOffset(state.Value + offset.Offset, offset.Size);
                        instruction.SetOperand(i, op is AddressOf ? new AddressOf(actual) : actual);
                    }
                }
            }
        }
    }

    // Traverse the graph and calculate the stack state for each block and instruction
    private void TraverseGraph(Block initialBlock, int initialVisitedBlockCount = 0)
    {
        var blockLevelState = new Stack<(Block, int)>();
        blockLevelState.Push((initialBlock, initialVisitedBlockCount));

        while (blockLevelState.Count > 0)
        {
            var (block, visitedBlockCount) = blockLevelState.Pop();

            // Copy current state
            var incomingState = _inComingState[block];
            var currentState = incomingState.Copy();

            // Process instructions
            foreach (var instruction in block.Instructions)
            {
                _instructionState[instruction] = currentState;

                if (instruction.OpCode == OpCode.ShiftStack)
                {
                    var offset = (int)((Immediate)instruction.Operands[0]).Value;
                    currentState = currentState.Copy();
                    currentState.Size += offset;
                }
                else if (block.Instructions[^1] == instruction && block.BlockType == BlockType.TailCall)
                {
                    // Tail calls clear stack
                    currentState = currentState.Copy();
                    currentState.Size = 0;
                }
            }

            // Tail calls clear stack
            if (block.BlockType == BlockType.TailCall)
                currentState.Size = 0;

            _outGoingState[block] = currentState;

            visitedBlockCount++;

            if (MaxBlockVisitCount != -1 && visitedBlockCount > MaxBlockVisitCount)
                throw new DecompilerException($"Stack state not settling! ({visitedBlockCount} blocks already visited)");

            // Visit successors
            foreach (var successor in block.Successors)
            {
                // Already visited
                if (_inComingState.TryGetValue(successor, out var existingState))
                {
                    if (existingState.Size != currentState.Size)
                    {
                        _inComingState[successor] = currentState.Copy();
                        blockLevelState.Push((successor, visitedBlockCount + 1));
                    }
                }
                else
                {
                    // Set incoming delta and add to queue
                    _inComingState[successor] = currentState.Copy();
                    blockLevelState.Push((successor, visitedBlockCount + 1));
                }
            }
        }
    }

    private static void ReplaceStackWithRegisters(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;

        // Replace stack offset operands
        foreach (var instruction in instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (operand is StackOffset offset)
                    instruction.SetOperand(i, new Register(null, NameForSlot(offset)));

                if (operand is AddressOf { Target: StackOffset addressed })
                    instruction.SetOperand(i, new AddressOf(new Register(null, NameForSlot(addressed))));
            }
        }

        // Replace params
        for (var i = 0; i < method.ParameterOperands.Count; i++)
        {
            var parameter = method.ParameterOperands[i];

            if (parameter is StackOffset offset)
                method.ParameterOperands[i] = new Register(null, NameForSlot(offset));
        }
    }

    internal static string NameForSlot(StackOffset offset) => offset.Offset < 0 ? $"stack_-{-offset.Offset:X}" : $"stack_{offset.Offset:X}";
}
