using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.PE;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Finds stack regions that hold a whole struct and folds every access within them into a field access on
/// one struct-typed slot, rather than leaving one unrelated slot per 4/8/16 byte chunk.
///
/// A region is identified by its address being handed to a call as something the callee treats as a
/// struct: a by-value struct parameter the ABI passes by pointer (anything not 1/2/4/8 bytes on win64),
/// a by-ref struct parameter (ref/out), the receiver of a value type's instance method, or the hidden
/// return buffer of a struct-returning call.
///
/// Runs on absolute stack offsets (after StackAnalyzer.CorrectOffsets), before slots become registers.
/// </summary>
public static class StackStructRecovery
{
    public static Action<string>? Debug;

    public static void Run(MethodAnalysisContext method, ISILControlFlowGraph graph)
    {
        var app = method.AppContext;
        if (app.Binary.PointerSizeBytes != 8 || app.Binary is not PE)
            return; // Only implemented for the win64 ABI so far

        var resolver = app.InstructionSet.CallingConventionResolver;
        if (resolver == null)
            return;

        var roots = new List<Root>();
        var bufferCalls = new List<(Block Block, Instruction Call, Root Root)>();

        void AddRoot(Block block, Instruction call, (int Offset, Instruction Definition)? addressed, TypeAnalysisContext type, bool calleeReads, bool calleeWrites)
        {
            if (addressed is not { } found || !IsStruct(type))
                return;

            roots.Add(new Root(found.Offset, type, call, found.Definition, calleeReads, calleeWrites));
        }

        foreach (var block in graph.Blocks)
        {
            if (block.Instructions.Count == 0)
                continue;

            var call = block.Instructions[^1];
            if (!call.IsCall || call.Operands.Count == 0 || call.Operands[0] is not Immediate target)
                continue;

            if (!app.TryGetManagedMethodsAt(target.UnsignedValue, out var candidates) || candidates.Count == 0)
                continue;

            var callee = candidates[0];

            // shared generic code is told which instantiation it's running as by the MethodInfo it's passed, which also
            // picks between folded instantiations
            var passed = PassedMethodInfo(app, resolver, block, callee);
            if (passed != null && candidates.Any(c => c.Name == passed.Name && c.Parameters.Count == passed.Parameters.Count && c.IsStatic == passed.IsStatic))
                callee = passed;
            // folded duplicates are fine as long as they agree on where structs go (the receiver only matters when it is a
            // struct itself)
            else if (candidates.Count > 1 && !candidates.All(c => SameLayout(c, callee)
                                                                  && (ReferenceEquals(c.DeclaringType, callee.DeclaringType) || c.DeclaringType is { IsValueType: false } && callee.DeclaringType is { IsValueType: false })))
                continue;

            // Only trust the operand layout if it's the managed one for this callee (not the raw unmanaged register dump)
            var expected = resolver.ResolveForManaged(callee);
            var argBase = call.OpCode == OpCode.CallVoid ? 1 : 2;
            if (call.Operands.Count != argBase + expected.Length)
                continue;

            var last = block.Instructions.Count - 1;

            // a small struct comes back in rax; spilled straight to the stack, that slot is the struct
            if (!resolver.ReturnsViaHiddenBuffer(callee) && IsStruct(callee.ReturnType) && TypeSizes.UnboxedSize(callee.ReturnType, 8) is 1 or 2 or 4 or 8
                && block.NormalSuccessors is [var after] && after.Predecessors.Count == 1
                && after.Instructions.TakeWhile(i => !(i.Destination is Register { Name: "rax" })).FirstOrDefault(i => i is { OpCode: OpCode.Move, Operands: [StackOffset, Register { Name: "rax" }] }) is { } spill
                && ((StackOffset)spill.Operands[0]).Offset < 0) // not the home of an incoming parameter, which MSVC reuses as scratch
                AddRoot(after, call, (((StackOffset)spill.Operands[0]).Offset, spill), callee.ReturnType, false, true);

            if (resolver.ReturnsViaHiddenBuffer(callee) && AddressedSlot(block, last, "rcx") is { } buffer)
            {
                AddRoot(block, call, buffer, callee.ReturnType, false, true);
                if (call.OpCode == OpCode.Call && call.Operands[1] is Register && roots.Count > 0 && roots[^1].Call == call)
                    bufferCalls.Add((block, call, roots[^1]));
            }

            var slot = argBase;
            if (!callee.IsStatic)
            {
                if (callee.DeclaringType is { IsValueType: true } declaringType)
                    AddRoot(block, call, AddressedSlot(block, last, call.Operands[slot]), declaringType, true, true);

                slot++;
            }

            foreach (var parameter in callee.Parameters)
            {
                if (slot >= call.Operands.Count)
                    break;

                var parameterType = parameter.ParameterType;
                if (parameterType is ByRefTypeAnalysisContext { ElementType: { } element })
                    AddRoot(block, call, AddressedSlot(block, last, call.Operands[slot]), element, true, true);
                else if (IsStruct(parameterType) && TypeSizes.UnboxedSize(parameterType, 8) is not (1 or 2 or 4 or 8))
                    AddRoot(block, call, AddressedSlot(block, last, call.Operands[slot]), parameterType, true, false);

                slot++;
            }
        }

        // A call through an interface (the slow path: GetInterfaceInvokeData(obj, interface, slot), then call [rax]) has
        // no callee yet, but the interface and slot it looks up name it: struct arguments to it are passed by pointer too
        foreach (var block in graph.Blocks)
        {
            var last = block.Instructions.FindLastIndex(i => i is { OpCode: OpCode.IndirectCall or OpCode.Call or OpCode.CallVoid, Operands: [Register, ..] });
            if (last < 0 || block.Instructions[last] is not { Operands: [Register target, ..] } call
                || InterfaceCallee(app, block, target.Name, last) is not { } callee)
                continue;

            string[] registers = ["rdx", "r8", "r9"];
            for (var i = 0; i < callee.Parameters.Count && i < registers.Length; i++)
            {
                var parameterType = callee.Parameters[i].ParameterType;
                if (parameterType is ByRefTypeAnalysisContext { ElementType: { } element })
                    AddRoot(block, call, AddressedSlot(block, last, registers[i]), element, true, true);
                else if (IsStruct(parameterType) && TypeSizes.UnboxedSize(parameterType, 8) is not (1 or 2 or 4 or 8))
                    AddRoot(block, call, AddressedSlot(block, last, registers[i]), parameterType, true, false);
            }
        }

        CollapseVectorCopies(graph);
        AddParameterCopyRoots(method, graph, roots);
        AddReturnCopyRoots(method, resolver, graph, roots);

        if (roots.Count == 0)
            return;

        // Each slot holds one struct, or - when MSVC reuses it for different struct types - one per call it's handed to
        var slots = new List<Slot>();
        foreach (var group in roots.GroupBy(r => r.Offset))
        {
            var types = group.Select(r => r.Type).Distinct().ToList();
            var instances = types.Count == 1
                ? [new Instance(StackAnalyzer.NameForSlot(new StackOffset(group.Key)), types[0], group.Key, group.Key + (int)TypeSizes.UnboxedSize(types[0], 8), group.ToList())]
                : PerUse(group.Key, group.OrderBy(r => r.Call.Index).ToList());

            if (instances.Any(i => i.End <= i.Start))
                continue;

            slots.Add(new Slot(group.Key, instances.Max(i => i.End), instances));
        }

        slots = slots.OrderBy(r => r.Start).ToList();
        Debug?.Invoke("slots: " + string.Join(", ", slots.Select(r => $"{r.Start:X}-{r.End:X} " + string.Join("|", r.Instances.Select(i => i.Type.ToString())))));

        // a struct inside another's slot as one of its fields (an async state machine's builder, Start(ref builder)) is
        // that field
        slots = slots.Where(inner => !slots.Any(outer => !ReferenceEquals(outer, inner) && outer.Instances.Count == 1 && inner.Instances.Count == 1
                                                          && outer.Start <= inner.Start && inner.End <= outer.End && outer.End - outer.Start > inner.End - inner.Start
                                                          && IsFieldAt(outer.Instances[0].Type, inner.Start - outer.Start, inner.Instances[0].Type, app.Binary.PointerSizeBytes)))
            .ToList();

        var accepted = new List<Slot>();
        for (var i = 0; i < slots.Count; i++)
        {
            var overlapsPrevious = i > 0 && slots[i - 1].End > slots[i].Start;
            var overlapsNext = i + 1 < slots.Count && slots[i].End > slots[i + 1].Start;
            if (!overlapsPrevious && !overlapsNext)
                accepted.Add(slots[i]);
        }

        // A slot only ever filled for us (a returned struct, a struct parameter copied in) and only read by us holds the
        // struct from where it's filled until anything else is written there: MSVC reuses it for other spills before that
        // and once it's dead (in a loop, too), which aren't the struct's
        var holding = new Dictionary<Slot, HashSet<Instruction>>();
        foreach (var slot in accepted.Where(s => s.Instances.All(i => i.Roots.All(r => r is { CalleeReads: false, CalleeWrites: true }))))
            holding[slot] = HoldingAt(graph, slot);

        bool NotTheStruct(Slot slot, Instruction instruction, bool isWrite)
            => holding.TryGetValue(slot, out var held)
               && !slot.Instances.Any(i => i.Roots.Any(r => ReferenceEquals(r.Call, instruction) || ReferenceEquals(r.Definition, instruction)))
               && (isWrite || !held.Contains(instruction));
        // A slot several structs take turns in: each access is the struct whose fill reaches it
        var webs = new Dictionary<Slot, Dictionary<(Instruction, int), Instance?>>();
        // (and a slot of one struct that's also used for something bigger: a Color built there and copied out before
        // the Vector3 argument goes in, which would otherwise reject the slot)
        bool Outgrown(Slot slot) => slot.Instances.Count == 1 && graph.Instructions.Any(i => i.Operands.Any(o =>
            o is StackOffset access && access.Offset < slot.End && access.Offset + Math.Max(access.Size, 1) > slot.Start
            && (access.Offset < slot.Start || access.Offset + Math.Max(access.Size, 1) > slot.End)));
        foreach (var slot in accepted.Where(s => s.Instances.Count > 1 || Outgrown(s)))
            if (Webs(graph, slot) is { } owners)
                webs[slot] = owners;
            else
                Debug?.Invoke($"no webs for {slot.Start:X}");

        // Which instance each access belongs to. An access straddling a slot boundary means our idea of the layout is
        // wrong, as does taking the address of the middle of one (we can't represent that yet)
        var assignments = new List<(Instruction Instruction, int Operand, Instance Instance, int Start)>();
        var interiors = new List<(Instruction Instruction, Instance Instance, int Start, int Offset)>();
        var partlyOther = new HashSet<Slot>();
        foreach (var instruction in graph.Instructions)
        {
            for (var operandIndex = 0; operandIndex < instruction.Operands.Count; operandIndex++)
            {
                switch (instruction.Operands[operandIndex])
                {
                    case StackOffset access:
                    {
                        var accessEnd = access.Offset + (access.Size > 0 ? access.Size : 1);
                        foreach (var slot in accepted.Where(r => access.Offset < r.End && accessEnd > r.Start).ToList())
                        {
                            if (webs.TryGetValue(slot, out var owners))
                            {
                                // not any struct's: a spill sharing the slot, left as it is
                                if (owners.GetValueOrDefault((instruction, operandIndex)) is not { } owned)
                                    partlyOther.Add(slot);
                                else
                                    assignments.Add((instruction, operandIndex, owned, slot.Start));
                                continue;
                            }

                            var isWrite = operandIndex == 0 && instruction.OpCode == OpCode.Move;
                            if (NotTheStruct(slot, instruction, isWrite))
                            {
                                partlyOther.Add(slot);
                                continue;
                            }

                            var instance = slot.Instances.Count == 1 ? slot.Instances[0] : Choose(slot, instruction, isWrite, access.Offset, accessEnd);
                            if (instance == null || access.Offset < instance.Start || accessEnd > instance.End)
                            {
                                Debug?.Invoke($"reject {slot.Start:X} by {instruction} (instance {instance?.Type} {instance?.Start:X}-{instance?.End:X}; roots {string.Join(",", slot.Instances.Select(i => i.Type + "@" + i.Roots[0].Call.Index + (i.Roots[0].CalleeReads ? "r" : "") + (i.Roots[0].CalleeWrites ? "w" : "")))})");
                                accepted.Remove(slot);
                                continue;
                            }

                            assignments.Add((instruction, operandIndex, instance, slot.Start));
                        }

                        break;
                    }
                    case AddressOf { Target: StackOffset addressed }:
                    {
                        foreach (var slot in accepted.Where(r => addressed.Offset >= r.Start && addressed.Offset < r.End).ToList())
                        {
                            if (addressed.Offset > slot.Start)
                            {
                                // the address of a field of the one struct there (lea rcx,[rsp+48h] for &sm.builder, or a
                                // reference field's for the write barrier): the struct's address, then the field's offset added
                                if (slot.Instances.Count == 1 && instruction is { OpCode: OpCode.Move, Operands: [Register, AddressOf] }
                                    && FieldChainAt(slot.Instances[0].Type, addressed.Offset - slot.Start, app.Binary.PointerSizeBytes) is { Count: > 0 })
                                {
                                    interiors.Add((instruction, slot.Instances[0], slot.Start, addressed.Offset - slot.Start));
                                    continue;
                                }

                                accepted.Remove(slot);
                                continue;
                            }

                            if (webs.TryGetValue(slot, out var owners))
                            {
                                if (owners.GetValueOrDefault((instruction, operandIndex)) is not { } owned)
                                    partlyOther.Add(slot);
                                else
                                    assignments.Add((instruction, operandIndex, owned, slot.Start));
                                continue;
                            }

                            if (slot.Instances.Count == 1)
                            {
                                assignments.Add((instruction, operandIndex, slot.Instances[0], slot.Start));
                                continue;
                            }

                            var owner = slot.Instances.FirstOrDefault(i => i.Roots.Any(r => r.Definition == instruction));
                            // an address nothing uses (handed to a call to an empty method, since removed) is no one's
                            if (owner == null && IsDeadTake(graph, instruction))
                                continue;

                            if (owner == null)
                            {
                                Debug?.Invoke($"reject {slot.Start:X}: unowned address {instruction}");
                                accepted.Remove(slot);
                                continue;
                            }

                            assignments.Add((instruction, operandIndex, owner, slot.Start));
                        }

                        break;
                    }
                }
            }
        }

        if (accepted.Count == 0)
            return;

        // the slot's own name stays with those other uses of it
        var renamed = new Dictionary<Instance, Instance>();
        foreach (var slot in accepted.Where(partlyOther.Contains))
            for (var i = 0; i < slot.Instances.Count; i++)
                if (slot.Instances[i].Name == StackAnalyzer.NameForSlot(new StackOffset(slot.Start)))
                    slot.Instances[i] = renamed[slot.Instances[i]] = slot.Instances[i] with { Name = slot.Instances[i].Name + "_0" };

        if (renamed.Count > 0)
            assignments = assignments.Select(a => renamed.TryGetValue(a.Instance, out var to) ? a with { Instance = to } : a).ToList();

        foreach (var (instruction, instance, slotStart, offset) in interiors)
        {
            if (!accepted.Any(r => r.Start == slotStart) || graph.Blocks.FirstOrDefault(b => b.Instructions.Contains(instruction)) is not { } block)
                continue;

            var holder = (Register)instruction.Operands[0];
            instruction.SetOperand(1, new AddressOf(new Register(null, renamed.TryGetValue(instance, out var to) ? to.Name : instance.Name)));
            block.Instructions.Insert(block.Instructions.IndexOf(instruction) + 1, new Instruction(instruction.Index, OpCode.Add, holder, holder, new Immediate(offset)));
        }

        foreach (var (instruction, operandIndex, instance, slotStart) in assignments)
        {
            if (!accepted.Any(r => r.Start == slotStart))
                continue;

            var structSlot = new Register(null, instance.Name);
            switch (instruction.Operands[operandIndex])
            {
                case StackOffset access:
                    instruction.SetOperand(operandIndex, new MemoryOperand(structSlot, addend: access.Offset - instance.Start, size: access.Size));
                    break;
                case AddressOf:
                    instruction.SetOperand(operandIndex, new AddressOf(structSlot));
                    break;
            }
        }

        foreach (var instance in accepted.SelectMany(r => r.Instances))
            method.StackStructTypes[instance.Name] = instance.Type;

        // A struct returned via hidden buffer is written into that buffer by the callee, which we otherwise don't see.
        // Model it as a copy of the returned value into the slot, right after the call.
        foreach (var (block, call, root) in bufferCalls)
        {
            if (accepted.SelectMany(r => r.Instances).FirstOrDefault(i => i.Roots.Contains(root) && ReferenceEquals(i.Type, root.Type)) is not { } instance)
                continue;

            var successors = block.NormalSuccessors.Distinct().ToList();
            if (successors is not [{ } next] || next == graph.ExitBlock || next.Predecessors.Distinct().Count() != 1)
                continue;

            var size = (int)TypeSizes.UnboxedSize(root.Type, 8);
            var structSlot = new Register(null, instance.Name);
            var returned = (Register)call.Operands[1];

            next.Instructions.Insert(0, new Instruction(call.Index, OpCode.Move,
                new MemoryOperand(structSlot, size: size),
                new MemoryOperand(returned, size: size)));
        }
    }

    // The method a call's hidden MethodInfo argument (the last one) names, when it's loaded from a metadata global
    private static MethodAnalysisContext? PassedMethodInfo(ApplicationAnalysisContext app, BaseCallingConventionResolver resolver, Block block, MethodAnalysisContext layout)
    {
        var expected = resolver.ResolveForManaged(layout);
        Debug?.Invoke("  expected " + string.Join(", ", expected.Select(e => e.ToString())));
        if (expected.Length == 0 || expected[^1] is not Register methodInfoRegister)
            return null;

        for (var i = block.Instructions.Count - 2; i >= 0; i--)
        {
            var instruction = block.Instructions[i];
            if (instruction.Destination is not Register { } written || written.Name != methodInfoRegister.Name)
                continue;

            if (instruction is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: null, Index: null } global] })
                return null;

            var usage = app.LibCpp2IlContext.GetMethodGlobalByAddress((ulong)global.Addend);
            Debug?.Invoke($"  methodinfo global {global.Addend:X}: {usage?.Type}");
            if (usage?.Type is not (LibCpp2IL.MetadataUsageType.MethodDef or LibCpp2IL.MetadataUsageType.MethodRef))
                return null;

            try
            {
                return app.ResolveContextForMethod(usage);
            }
            catch (Exception e)
            {
                Debug?.Invoke("  resolve failed " + e.Message);
                return null;
            }
        }

        return null;
    }

    // A struct parameter passed by pointer that the method copies into its frame (MSVC copies a by-value struct
    // argument it modifies or keeps): the copy is that struct
    // movups xmm0,[r9] / movups xmm1,[r9+10h] / lea r9,[rsp+50h] / movaps [rsp+50h],xmm0 / movaps [rsp+60h],xmm1: a 32 byte
    // copy whose source register is reused before the stores. It becomes one copy where the loads are, as long as
    // nothing else touches the destination in between.
    private static void CollapseVectorCopies(ISILControlFlowGraph graph)
    {
        foreach (var block in graph.Blocks)
        {
            var instructions = block.Instructions;
            for (var first = 0; first < instructions.Count; first++)
            {
                if (instructions[first] is not { OpCode: OpCode.Move, Operands: [Register { Name: var firstVector }, MemoryOperand { Base: Register sourceBase, Index: null, Size: 16 } firstLoad] }
                    || !firstVector.StartsWith("xmm", System.StringComparison.Ordinal))
                    continue;

                // the loads from that base (before it's reassigned), then each one's store to the stack
                var loads = new Dictionary<string, (int Index, long Offset)>();
                var stores = new List<(int Index, int Slot, long Offset)>();
                var baseIntact = true;
                for (var at = first; at < instructions.Count && at < first + 16; at++)
                {
                    var instruction = instructions[at];
                    if (baseIntact && instruction is { OpCode: OpCode.Move, Operands: [Register { Name: var vector }, MemoryOperand { Base: Register b, Index: null, Size: 16 } load] }
                        && vector.StartsWith("xmm", System.StringComparison.Ordinal) && b.Name == sourceBase.Name && !loads.ContainsKey(vector))
                    {
                        loads[vector] = (at, load.Addend);
                        continue;
                    }

                    if (instruction is { OpCode: OpCode.Move, Operands: [StackOffset { Size: 16 } slot, Register { Name: var stored }] } && loads.TryGetValue(stored, out var loaded))
                    {
                        stores.Add((at, slot.Offset, loaded.Offset));
                        loads.Remove(stored);
                        continue;
                    }

                    if (instruction.Destination is Register { Name: var written })
                    {
                        if (written == sourceBase.Name)
                            baseIntact = false;
                        if (loads.ContainsKey(written))
                            break; // a loaded value replaced before it was stored
                    }

                    if (instruction.IsCall || instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump or OpCode.Return)
                        break;
                }

                if (stores.Count < 2 || loads.Count != 0)
                    continue;

                // one contiguous source range onto one contiguous destination range
                var ordered = stores.OrderBy(st => st.Offset).ToList();
                var sourceStart = ordered[0].Offset;
                var destinationStart = ordered[0].Slot;
                if (ordered.Select((st, n) => st.Offset == sourceStart + 16 * n && st.Slot == destinationStart + 16 * n).Any(ok => !ok))
                    continue;

                var size = 16 * ordered.Count;
                var lastStore = stores.Max(st => st.Index);
                var storeIndices = stores.Select(st => st.Index).ToHashSet();
                var touched = false;
                for (var at = first; at <= lastStore && !touched; at++)
                {
                    if (storeIndices.Contains(at))
                        continue;
                    // (taking its address in between is fine: that's how it gets passed)
                    touched = instructions[at].Operands.Any(o => o is StackOffset other && other.Offset < destinationStart + size && other.Offset + Math.Max(other.Size, 1) > destinationStart);
                }
                if (touched)
                    continue;

                foreach (var index in storeIndices)
                {
                    instructions[index].OpCode = OpCode.Nop;
                    instructions[index].SetOperands();
                }

                instructions.Insert(first, new Instruction(instructions[first].Index, OpCode.Move, new StackOffset(destinationStart, size),
                    new MemoryOperand(sourceBase, null, sourceStart, 0, size)));
                first += stores.Count;
            }
        }
    }

    private static void AddParameterCopyRoots(MethodAnalysisContext method, ISILControlFlowGraph graph, List<Root> roots)
    {
        var parameterRegisters = new Dictionary<string, TypeAnalysisContext>();
        var operandIndex = method.IsStatic ? 0 : 1;
        foreach (var parameter in method.Parameters)
        {
            if (operandIndex < method.ParameterOperands.Count && method.ParameterOperands[operandIndex] is Register register
                && IsStruct(parameter.ParameterType) && TypeSizes.UnboxedSize(parameter.ParameterType, 8) is not (1 or 2 or 4 or 8))
                parameterRegisters[register.Name] = parameter.ParameterType;
            operandIndex++;
        }

        if (parameterRegisters.Count == 0)
            return;

        // follow the registers from the entry, as long as there's a single path
        var live = new Dictionary<string, TypeAnalysisContext>(parameterRegisters);
        var block = graph.EntryBlock.Successors.Distinct().ToList() is [{ } first] ? first : null;
        var visited = new HashSet<Block>();
        while (block != null && visited.Add(block))
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction is { OpCode: OpCode.Move, Operands: [StackOffset destination, MemoryOperand { Base: Register from, Index: null, Addend: 0 } source] }
                    && live.TryGetValue(from.Name, out var copied) && source.Size == destination.Size && destination.Size == TypeSizes.UnboxedSize(copied, 8))
                {
                    roots.Add(new Root(destination.Offset, copied, instruction, instruction, false, true));
                    continue;
                }

                if (instruction is { OpCode: OpCode.Move, Operands: [Register to, Register copiedFrom] } && live.TryGetValue(copiedFrom.Name, out var carried))
                {
                    live[to.Name] = carried;
                    continue;
                }

                if (instruction.Destination is Register overwritten)
                    live.Remove(overwritten.Name);

                if (instruction.IsCall || instruction.OpCode is OpCode.IndirectCall)
                    foreach (var volatileRegister in new[] { "rax", "rcx", "rdx", "r8", "r9", "r10", "r11" })
                        live.Remove(volatileRegister);
            }

            block = block.NormalSuccessors.Distinct().ToList() is [{ } next] && next.Predecessors.Distinct().Count() == 1 ? next : null;
        }
    }

    /// <summary>
    /// A struct returned through the hidden buffer is usually built on the stack first, then copied into the buffer in
    /// chunks (<c>movups xmm0,[rsp+40h]; movups [rbx],xmm0; mov eax,[rsp+50h]; mov [rbx+10h],eax</c>), with the buffer
    /// pointer kept in a callee-saved register across the calls building it. The stack region so copied is the struct.
    /// </summary>
    private static void AddReturnCopyRoots(MethodAnalysisContext method, BaseCallingConventionResolver resolver, ISILControlFlowGraph graph, List<Root> roots)
    {
        if (resolver.HiddenReturnBufferRegister(method) is not { } bufferRegister || !IsStruct(method.ReturnType))
            return;

        var size = (int)TypeSizes.UnboxedSize(method.ReturnType, 8);
        if (size <= 0)
            return;

        // registers holding the buffer: any the incoming one is copied into before the first call, and never otherwise
        // assigned (but for restoring the caller's value from the stack on the way out)
        var holders = new HashSet<string>();
        var first = graph.EntryBlock.Successors.Distinct().ToList() is [{ } entry] ? entry : null;
        if (first == null)
            return;

        foreach (var instruction in first.Instructions)
        {
            if (instruction.IsCall || instruction.OpCode is OpCode.IndirectCall)
                break;
            if (instruction is { OpCode: OpCode.Move, Operands: [Register copy, Register { } original] } && original.Name == bufferRegister.Name)
                holders.Add(copy.Name);
            else if (instruction.Destination is Register { } clobbered && clobbered.Name == bufferRegister.Name)
                break;
        }

        holders.RemoveWhere(h => graph.Instructions.Count(i => i.Destination is Register { } written && written.Name == h
                                                             && i is not { OpCode: OpCode.Move, Operands: [_, StackOffset] }) != 1);
        if (holders.Count == 0)
            return;

        foreach (var block in graph.Blocks)
        {
            // chunk loads from the stack and their stores into the buffer, in this block
            var loaded = new Dictionary<string, StackOffset>();
            var copies = new List<(int SourceOffset, long DestinationOffset, int Size, Instruction Store)>();

            foreach (var instruction in block.Instructions)
            {
                if (instruction is { OpCode: OpCode.Move, Operands: [Register target, StackOffset { Size: > 0 } source] })
                {
                    loaded[target.Name] = source;
                    continue;
                }

                if (instruction is { OpCode: OpCode.Move, Operands: [MemoryOperand { Base: Register { } bufferBase, Index: null, Size: > 0 } destination, Register value] }
                    && holders.Contains(bufferBase.Name) && loaded.TryGetValue(value.Name, out var chunk) && chunk.Size == destination.Size)
                {
                    copies.Add((chunk.Offset, destination.Addend, destination.Size, instruction));
                    continue;
                }

                if (instruction.Destination is Register overwritten)
                    loaded.Remove(overwritten.Name);
            }

            if (copies.Count == 0)
                continue;

            // the chunks must tile the whole struct, all from one stack region
            var start = copies[0].SourceOffset - (int)copies[0].DestinationOffset;
            var covered = 0L;
            foreach (var copy in copies.OrderBy(c => c.DestinationOffset))
            {
                if (copy.SourceOffset - copy.DestinationOffset != start || copy.DestinationOffset != covered)
                {
                    covered = -1;
                    break;
                }

                covered += copy.Size;
            }

            if (covered < size || start >= 0)
                continue;

            Debug?.Invoke($"return copy root {start:X} {method.ReturnType}");
            roots.Add(new Root(start, method.ReturnType, copies[0].Store, copies[0].Store, true, false));
        }
    }

    // The instructions before which the slot holds what its roots filled it with: on every path there, one of them filled
    // it and nothing wrote to it since
    private static HashSet<Instruction> HoldingAt(ISILControlFlowGraph graph, Slot slot)
    {
        var fills = slot.Instances.SelectMany(i => i.Roots).SelectMany(r => new[] { r.Call, r.Definition }).ToHashSet();

        bool Overwrites(Instruction instruction)
            => instruction.Destination is StackOffset written && written.Offset < slot.End && written.Offset + Math.Max(written.Size, 1) > slot.Start;

        bool Transfer(Block block, bool holds, HashSet<Instruction>? record)
        {
            foreach (var instruction in block.Instructions)
            {
                if (holds)
                    record?.Add(instruction);

                if (fills.Contains(instruction))
                    holds = true;
                else if (Overwrites(instruction))
                    holds = false;
            }

            return holds;
        }

        // must-hold, so start from everything holding and only ever drop
        var holdsOut = graph.Blocks.ToDictionary(b => b, _ => true);
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var block in graph.Blocks)
            {
                var holdsIn = block.Predecessors.Count > 0 && block.Predecessors.All(p => holdsOut[p]);
                var after = Transfer(block, holdsIn, null);
                if (after != holdsOut[block])
                {
                    holdsOut[block] = after;
                    changed = true;
                }
            }
        }

        var holding = new HashSet<Instruction>();
        foreach (var block in graph.Blocks)
            Transfer(block, block.Predecessors.Count > 0 && block.Predecessors.All(p => holdsOut[p]), holding);

        return holding;
    }

    // A slot reused for several structs: one instance per use, except that consecutive uses as the same type are the same
    // value (a struct parameter copied into the slot, then passed on)
    private static List<Instance> PerUse(int offset, List<Root> ordered)
    {
        var instances = new List<Instance>();
        foreach (var root in ordered)
        {
            if (instances.Count > 0 && ReferenceEquals(instances[^1].Type, root.Type))
            {
                instances[^1].Roots.Add(root);
                continue;
            }

            instances.Add(new Instance($"{StackAnalyzer.NameForSlot(new StackOffset(offset))}_{instances.Count}", root.Type, offset,
                offset + (int)TypeSizes.UnboxedSize(root.Type, 8), [root]));
        }

        return instances;
    }

    private sealed record Root(int Offset, TypeAnalysisContext Type, Instruction Call, Instruction Definition, bool CalleeReads, bool CalleeWrites);

    private sealed record Instance(string Name, TypeAnalysisContext Type, int Start, int End, List<Root> Roots);

    private sealed record Slot(int Start, int End, List<Instance> Instances);

    // A slot reused for several structs: our write is building the next call's argument, our read is of what the last
    // call left there (a returned struct), or else of an argument we're building
    private static Instance? Choose(Slot slot, Instruction access, bool isWrite, int accessStart, int accessEnd)
    {
        // the access that is itself the root (a copy of a struct parameter into the slot)
        if (slot.Instances.FirstOrDefault(i => i.Roots.Any(r => ReferenceEquals(r.Call, access) || ReferenceEquals(r.Definition, access))) is { } own)
            return own;

        // only an instance the access fits in can be the one it's to
        var fitting = slot.Instances.Where(i => accessStart >= i.Start && accessEnd <= i.End).ToList();
        if (fitting.Count == 1)
            return fitting[0];

        var ordered = (fitting.Count > 0 ? fitting : slot.Instances).OrderBy(i => i.Roots[0].Call.Index).ToList();
        var next = ordered.FirstOrDefault(i => i.Roots.Any(r => r.Call.Index > access.Index && r.CalleeReads));
        var previous = ordered.LastOrDefault(i => i.Roots.Any(r => r.Call.Index < access.Index));

        if (isWrite)
            return next ?? (previous != null && previous.Roots.Any(r => r.CalleeWrites) ? previous : null);

        if (previous != null && previous.Roots.Any(r => r.CalleeWrites))
            return previous;

        return next ?? previous;
    }

    private sealed class Event(Instruction instruction, int operand, int start, int end, bool use, bool def)
    {
        public readonly Instruction Instruction = instruction;
        public readonly int Operand = operand;
        public readonly int Start = start, End = end;
        public readonly bool Use = use, Def = def;
        public Instance? Owner;
        public int Parent = -1;
    }

    /// <summary>
    /// MSVC gives structs whose lifetimes don't overlap the same stack slot (one enumerator after another, a returned
    /// struct, then an argument being built), and uses it for spills in between. Which struct an access is to follows
    /// from which writes reach it: reaching definitions over the slot's bytes, where a read joins every write of its bytes
    /// reaching it, and a call handed the slot as a struct reads (and maybe writes) all of it. Each group so joined is one
    /// value; the struct is the one a call takes it as. A group with none is a spill (null); one with two different structs
    /// means we can't tell (no answer at all).
    /// </summary>
    private static Dictionary<(Instruction, int), Instance?>? Webs(ISILControlFlowGraph graph, Slot slot)
    {
        bool Overlaps(int start, int end) => start < slot.End && end > slot.Start;

        // what the roots are: an address taken for a call, or a fill of the slot itself (a spilled return, a copy in)
        var rootsAt = new Dictionary<Instruction, List<(Root Root, Instance Instance)>>();
        foreach (var instance in slot.Instances)
            foreach (var root in instance.Roots)
            {
                foreach (var at in new[] { root.Call, root.Definition }.Distinct())
                {
                    if (!rootsAt.TryGetValue(at, out var list))
                        rootsAt[at] = list = [];
                    list.Add((root, instance));
                }
            }

        bool FillsSlot(Instruction instruction)
            => instruction is { Destination: StackOffset written, Operands: [StackOffset, ..] } && Overlaps(written.Offset, written.Offset + Math.Max(written.Size, 1));

        var events = new List<Event>();
        var perBlock = new Dictionary<Block, List<int>>();
        var rootEvents = new Dictionary<Root, List<int>>();

        int Add(Block block, Event e, Root? root = null, Instance? owner = null)
        {
            e.Owner = owner;
            events.Add(e);
            perBlock[block].Add(events.Count - 1);
            if (root != null)
            {
                if (!rootEvents.TryGetValue(root, out var list))
                    rootEvents[root] = list = [];
                list.Add(events.Count - 1);
            }

            return events.Count - 1;
        }

        foreach (var block in graph.Blocks)
        {
            perBlock[block] = [];
            // an address handed to a call is read by it, not where it's taken (lea rdx,[rsp+50h] / movaps [rsp+50h],xmm0
            // / call: filled in between)
            var atCall = new Dictionary<Instruction, List<Event>>();
            foreach (var instruction in block.Instructions)
            {
                rootsAt.TryGetValue(instruction, out var roots);
                if (atCall.Remove(instruction, out var deferred))
                    foreach (var e in deferred)
                        Add(block, e);

                // reads first
                for (var i = 0; i < instruction.Operands.Count; i++)
                {
                    switch (instruction.Operands[i])
                    {
                        case StackOffset read when !(i == 0 && instruction.Destination is StackOffset):
                        {
                            var end = read.Offset + Math.Max(read.Size, 1);
                            if (Overlaps(read.Offset, end))
                                Add(block, new Event(instruction, i, read.Offset, end, true, false));
                            break;
                        }
                        case AddressOf { Target: StackOffset addressed } when Overlaps(addressed.Offset, addressed.Offset + 1):
                        {
                            var owner = roots?.FirstOrDefault(r => ReferenceEquals(r.Root.Definition, instruction));
                            if (owner is { Root: { } root, Instance: { } instance })
                                Add(block, new Event(instruction, i, instance.Start, instance.End, false, false), root, instance);
                            else if (!IsDeadTake(graph, instruction))
                            {
                                // taken for something we don't know of: it may read any of it, or what's written there for it
                                // since the call before (mov [rsp+40h],r12d / lea rdx,[rsp+40h] / call: those bytes)
                                var at = block.Instructions.IndexOf(instruction);
                                var call = block.Instructions.Skip(at + 1).FirstOrDefault(x => x.IsCall || x.OpCode == OpCode.IndirectCall);
                                var since = block.Instructions.FindLastIndex(at, x => x.IsCall || x.OpCode == OpCode.IndirectCall) + 1;
                                var built = call == null ? [] : block.Instructions.Skip(since).TakeWhile(x => x != call)
                                    .Select(x => x.Destination as StackOffset?).Where(w => w is { } written && Overlaps(written.Offset, written.Offset + Math.Max(written.Size, 1)))
                                    .Select(w => w!.Value).ToList();
                                var e = built.Count == 0
                                    ? new Event(instruction, i, slot.Start, slot.End, true, false)
                                    : new Event(instruction, i, Math.Max(slot.Start, built.Min(w => w.Offset)), Math.Min(slot.End, built.Max(w => w.Offset + Math.Max(w.Size, 1))), true, false);
                                if (call != null)
                                {
                                    if (!atCall.TryGetValue(call, out var list))
                                        atCall[call] = list = [];
                                    list.Add(e);
                                }
                                else
                                    Add(block, e);
                            }
                            break;
                        }
                    }
                }

                // a call handed the slot reads it, then fills it if it's a ref/out argument or the return buffer
                if (roots != null)
                    foreach (var (root, instance) in roots.Where(r => ReferenceEquals(r.Root.Call, instruction) && !FillsSlot(r.Root.Definition)))
                        if (root.CalleeReads)
                            Add(block, new Event(instruction, -1, instance.Start, instance.End, true, false), root, instance);

                if (instruction.Destination is StackOffset written && instruction.Operands.Count > 0 && instruction.Operands[0] is StackOffset)
                {
                    var end = written.Offset + Math.Max(written.Size, 1);
                    if (Overlaps(written.Offset, end))
                    {
                        var owner = roots?.FirstOrDefault(r => ReferenceEquals(r.Root.Definition, instruction));
                        Add(block, new Event(instruction, 0, written.Offset, end, false, true), owner?.Root, owner?.Instance);
                    }
                }

                if (roots != null)
                    foreach (var (root, instance) in roots.Where(r => ReferenceEquals(r.Root.Call, instruction) && !FillsSlot(r.Root.Definition)))
                        if (root.CalleeWrites)
                            Add(block, new Event(instruction, -2, instance.Start, instance.End, false, true), root, instance);
            }
        }

        // what's there on entry, in an incoming argument's home (in a local's, nothing yet: reading that is no one value)
        if (slot.Start >= 0)
        {
            perBlock[graph.EntryBlock].Insert(0, events.Count);
            events.Add(new Event(new Instruction(-1, OpCode.Nop), -3, slot.Start, slot.End, false, true));
        }

        int Find(int x)
        {
            while (events[x].Parent >= 0)
                x = events[x].Parent;
            return x;
        }

        void Union(int a, int b)
        {
            a = Find(a);
            b = Find(b);
            if (a != b)
                events[a].Parent = b;
        }

        foreach (var list in rootEvents.Values)
            for (var i = 1; i < list.Count; i++)
                Union(list[0], list[i]);

        // reaching definitions, per piece of the slot (between any two places an access starts or ends): a write replaces
        // what reached the pieces it covers
        var bounds = events.SelectMany(e => new[] { Math.Max(e.Start, slot.Start), Math.Min(e.End, slot.End) }).Distinct().OrderBy(x => x).ToList();
        var pieces = bounds.Count - 1;
        if (pieces <= 0)
            return null;

        (int First, int Last) PiecesOf(Event e)
            => (bounds.IndexOf(Math.Max(e.Start, slot.Start)), bounds.IndexOf(Math.Min(e.End, slot.End)) - 1);

        HashSet<int>[] Merge(Block block, Dictionary<Block, HashSet<int>[]> outs)
        {
            var merged = new HashSet<int>[pieces];
            for (var k = 0; k < pieces; k++)
                merged[k] = [];
            foreach (var predecessor in block.Predecessors)
                if (outs.TryGetValue(predecessor, out var state))
                    for (var k = 0; k < pieces; k++)
                        merged[k].UnionWith(state[k]);
            return merged;
        }

        void Transfer(Block block, HashSet<int>[] reaching, bool join)
        {
            foreach (var index in perBlock[block])
            {
                var e = events[index];
                var (first, last) = PiecesOf(e);
                if (e.Use && join)
                    for (var k = first; k <= last; k++)
                        foreach (var def in reaching[k])
                            Union(index, def);

                if (e.Def)
                    for (var k = first; k <= last; k++)
                        reaching[k] = [index];
            }
        }

        var outs = new Dictionary<Block, HashSet<int>[]>();
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var block in graph.Blocks)
            {
                var reaching = Merge(block, outs);
                Transfer(block, reaching, false);
                if (!outs.TryGetValue(block, out var previous) || Enumerable.Range(0, pieces).Any(k => !previous[k].SetEquals(reaching[k])))
                {
                    outs[block] = reaching;
                    changed = true;
                }
            }
        }

        foreach (var block in graph.Blocks)
            Transfer(block, Merge(block, outs), true);

        // the struct of each group: one type only (several uses of the same type, joined, are one value)
        var owners = new Dictionary<int, Instance>();
        for (var i = 0; i < events.Count; i++)
        {
            if (events[i].Owner is not { } owner)
                continue;

            var set = Find(i);
            if (owners.TryGetValue(set, out var existing))
            {
                if (!ReferenceEquals(existing.Type, owner.Type) && existing.Type.FullName != owner.Type.FullName)
                {
                    Debug?.Invoke($"web of {slot.Start:X} mixes {existing.Type} and {owner.Type} at {events[i].Instruction}: "
                                  + string.Join(" | ", Enumerable.Range(0, events.Count).Where(k => Find(k) == set).Select(k => $"{events[k].Instruction.Index}{(events[k].Use ? "u" : "")}{(events[k].Def ? "d" : "")}{events[k].Operand}[{events[k].Start - slot.Start:X}-{events[k].End - slot.Start:X}]{events[k].Owner?.Type.Name}")));
                    return null;
                }

                if (owner.Roots[0].Call.Index < existing.Roots[0].Call.Index)
                    owners[set] = owner;
            }
            else
                owners[set] = owner;
        }

        // a slot only ever one struct: what else is kept there between its uses is another of the same (a struct
        // argument's slot then holding what came back), unless it's only ever filled for us and so may be any spill
        var single = slot.Instances.Select(i => i.Type.FullName).Distinct().Count() == 1 && !slot.Instances.SelectMany(i => i.Roots).All(r => r is { CalleeReads: false, CalleeWrites: true })
            ? slot.Instances[0] : null;

        // one variable per group: the struct's own name for the first, then fresh ones
        var fresh = new Dictionary<int, Instance>();
        var named = new HashSet<Instance>();
        var counter = 0;
        var groups = Enumerable.Range(0, events.Count).GroupBy(Find).ToDictionary(g => g.Key, g => g.Select(i => events[i]).ToList());
        foreach (var (set, members) in groups.OrderBy(g => g.Value.Min(e => e.Instruction.Index)))
        {
            var template = owners.GetValueOrDefault(set);
            var spill = template == null;
            // (one only ever written is dead, and left for dead code elimination)
            // (one whose address is handed to something we couldn't tell the parameters of may be any struct)
            template ??= !members.Any(e => e.Use) || members.Any(e => e.Operand >= 0 && e.Instruction.Operands[e.Operand] is AddressOf) ? null : single;
            if (template == null)
                continue;

            // a part of the slot outside the struct it's joined to: the layout is wrong (or, for a spill, it's not one)
            if (members.Any(e => e.Start < template.Start || e.End > template.End))
            {
                if (spill)
                    continue;
                Debug?.Invoke($"web of {slot.Start:X}: {members.First(e => e.Start < template.Start || e.End > template.End).Instruction} outside {template.Type}");
                return null;
            }

            var roots = rootEvents.Where(r => Find(r.Value[0]) == set).Select(r => r.Key).ToList();
            var name = named.Add(template) && !spill ? template.Name : $"{StackAnalyzer.NameForSlot(new StackOffset(slot.Start))}_w{counter++}";
            fresh[set] = template with { Name = name, Roots = roots };
        }

        var result = new Dictionary<(Instruction, int), Instance?>();
        for (var i = 0; i < events.Count; i++)
            if (events[i].Operand >= 0)
                result[(events[i].Instruction, events[i].Operand)] = fresh.GetValueOrDefault(Find(i));

        // the slot's structs are now these (roots no use reached keep theirs)
        var used = fresh.Values.ToList();
        foreach (var instance in slot.Instances)
            if (!used.Any(u => u.Name == instance.Name))
                used.Add(instance with { Roots = instance.Roots.Where(r => !used.Any(u => u.Roots.Contains(r))).ToList() });
        slot.Instances.Clear();
        slot.Instances.AddRange(used.Where(u => u.Roots.Count > 0 || fresh.ContainsValue(u)));

        return result;
    }

    // The register an address is taken into is never read before it's overwritten (or clobbered by a call)
    private static bool IsDeadTake(ISILControlFlowGraph graph, Instruction take)
    {
        if (take is not { OpCode: OpCode.Move, Operands: [Register holder, AddressOf] })
            return false;

        var start = graph.Blocks.FirstOrDefault(b => b.Instructions.Contains(take));
        if (start == null)
            return false;

        bool Reads(Instruction instruction)
            => instruction.Operands.Skip(instruction.Destination is Register ? 1 : 0).Any(o => o is Register r && r.Name == holder.Name
                                                                                          || o is MemoryOperand m && (m.Base is Register b && b.Name == holder.Name || m.Index is Register x && x.Name == holder.Name))
               || instruction.Destination is MemoryOperand { } written && (written.Base is Register wb && wb.Name == holder.Name || written.Index is Register wx && wx.Name == holder.Name);

        var visited = new HashSet<Block>();
        var pending = new Stack<(Block Block, int From)>();
        pending.Push((start, start.Instructions.IndexOf(take) + 1));
        while (pending.Count > 0)
        {
            var (block, from) = pending.Pop();
            var ended = false;
            for (var i = from; i < block.Instructions.Count && !ended; i++)
            {
                var instruction = block.Instructions[i];
                if (Reads(instruction) || instruction.OpCode is OpCode.IndirectJump)
                    return false;
                ended = instruction.Destination is Register written && written.Name == holder.Name
                        || instruction.IsCall && Volatile.Contains(holder.Name);
            }

            if (ended)
                continue;
            foreach (var successor in block.Successors)
                if (visited.Add(successor))
                    pending.Push((successor, 0));
        }

        return true;
    }

    private static List<FieldAnalysisContext>? FieldChainAt(TypeAnalysisContext type, int offset, int pointerSize)
    {
        try
        {
            return type is GenericInstanceTypeAnalysisContext generic
                ? GenericInstanceFieldLayout.FindFieldChain(generic, offset, 0, pointerSize)
                : MetadataResolver.FindFieldChain(type, false, offset, 0, pointerSize);
        }
        catch
        {
            return null;
        }
    }

    // whether a field of the type (or of its struct fields) of that type starts at that offset
    private static bool IsFieldAt(TypeAnalysisContext outer, int offset, TypeAnalysisContext inner, int pointerSize)
    {
        if (FieldChainAt(outer, offset, pointerSize) is not { } chain)
            return false;

        return chain.Any(field => field.FieldType.FullName == inner.FullName);
    }

    private static readonly HashSet<string> PrimitiveNames =
        ["Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64", "Single", "Double", "IntPtr", "UIntPtr"];

    internal static bool IsStruct(TypeAnalysisContext type)
    {
        if (type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext or GenericParameterTypeAnalysisContext)
            return false;

        if (!type.IsValueType || type.IsEnumType)
            return false;

        if (type.Namespace == "System" && PrimitiveNames.Contains(type.Name))
            return false;

        return TypeSizes.UnboxedSize(type, 8) > 0;
    }

    private static bool SameLayout(MethodAnalysisContext a, MethodAnalysisContext b)
    {
        if (a.IsStatic != b.IsStatic || a.Parameters.Count != b.Parameters.Count || !ReferenceEquals(a.ReturnType, b.ReturnType))
            return false;

        for (var i = 0; i < a.Parameters.Count; i++)
            if (!ReferenceEquals(a.Parameters[i].ParameterType, b.Parameters[i].ParameterType))
                return false;

        return true;
    }

    // call r9 where r9 = [rax] and rax came back from the interface lookup called just before, with rdx = the
    // interface's class and r8 = the slot
    private static MethodAnalysisContext? InterfaceCallee(ApplicationAnalysisContext app, Block block, string targetRegister, int callIndex)
    {
        var definition = block.Instructions.Take(callIndex).LastOrDefault(i => i.Destination is Register { } written && written.Name == targetRegister);
        if (definition is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: Register { Name: "rax" }, Index: null, Addend: 0 }] }
            || block.Instructions.Take(block.Instructions.IndexOf(definition)).Any(i => i.Destination is Register { Name: "rax" }))
            return null;

        // up through blocks that don't touch rax to the one ending in the lookup call
        Block? lookup = null;
        for (var (current, hops) = (block, 0); hops < 3 && current.Predecessors is [var predecessor]; current = predecessor, hops++)
        {
            if (predecessor.Instructions is [.., { IsCall: true, Operands: [Immediate, ..] }])
            {
                lookup = predecessor;
                break;
            }

            if (predecessor.Instructions.Any(i => i.Destination is Register { Name: "rax" }))
                return null;
        }

        if (lookup == null)
            return null;

        var lookupCall = lookup.Instructions.Count - 1;
        var interfaceAddress = LastWrite(lookup, lookupCall, "rdx") is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: null, Index: null } global] } ? (ulong?)global.Addend : null;
        var slot = LastWrite(lookup, lookupCall, "r8") is { OpCode: OpCode.Move, Operands: [_, Immediate { Value: var value }] } ? (long?)value : null;

        if (interfaceAddress is null or 0 || slot is null or < 0
            || app.LibCpp2IlContext.GetTypeGlobalByAddress(interfaceAddress.Value) is not { } typeGlobal)
            return null;

        try
        {
            return app.ResolveIl2CppType(typeGlobal) is { IsInterface: true } declaringInterface
                ? InterfaceDispatchRecovery.ResolveInterfaceSlot(declaringInterface, (int)slot.Value)
                : null;
        }
        catch
        {
            return null;
        }
    }

    // The write of a register reaching a point: within the block, else the same one along every path into it
    private static Instruction? LastWrite(Block block, int before, string register, int depth = 0, HashSet<Block>? visited = null)
    {
        for (var i = before - 1; i >= 0; i--)
            if (block.Instructions[i].Destination is Register { } written && written.Name == register)
                return block.Instructions[i];

        visited ??= [];
        if (depth > 8 || !visited.Add(block) || block.Predecessors.Count == 0)
            return null;

        Instruction? found = null;
        foreach (var predecessor in block.Predecessors)
        {
            if (visited.Contains(predecessor))
                continue; // a loop back edge: whatever reaches the loop

            var write = LastWrite(predecessor, predecessor.Instructions.Count, register, depth + 1, visited);
            if (write == null || found != null && found != write)
                return null;
            found = write;
        }

        return found;
    }

    private static (int Offset, Instruction Definition)? AddressedSlot(Block block, int callIndex, IOperand argument)
        => argument is Register register ? AddressedSlot(block, callIndex, register.Name)
            : argument is AddressOf { Target: StackOffset direct } ? (direct.Offset, block.Instructions[callIndex])
            : null;

    // Walks back from the call to the last write of the register (through copies of it, and into the blocks before when
    // every path there agrees), and returns the stack slot whose address it holds, if that's what it was set to.
    private static (int Offset, Instruction Definition)? AddressedSlot(Block block, int callIndex, string registerName)
    {
        for (var depth = 0; depth < 4; depth++)
        {
            var write = WriteReaching(block, callIndex, registerName);
            switch (write?.Instruction)
            {
                case { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: StackOffset slot }] } take:
                    return (slot.Offset, take);
                case { OpCode: OpCode.Move, Operands: [_, Register { } copied] }:
                    (block, callIndex, registerName) = (write.Value.Block, write.Value.Block.Instructions.IndexOf(write.Value.Instruction), copied.Name);
                    continue;
                default:
                    return null;
            }
        }

        return null;
    }

    private static readonly HashSet<string> Volatile = ["rax", "rcx", "rdx", "r8", "r9", "r10", "r11"];

    // The write of a register reaching a point: within the block, else the same one along every path into it. A call
    // in between clobbers the volatile registers.
    private static (Block Block, Instruction Instruction)? WriteReaching(Block block, int before, string register, int depth = 0, HashSet<Block>? visited = null)
    {
        for (var i = before - 1; i >= 0; i--)
        {
            var instruction = block.Instructions[i];
            if (instruction.Destination is Register { } written && written.Name == register)
                return (block, instruction);
            if (instruction.IsCall && Volatile.Contains(register))
                return null;
        }

        visited ??= [];
        if (depth > 8 || !visited.Add(block) || block.Predecessors.Count == 0)
            return null;

        (Block Block, Instruction Instruction)? found = null;
        foreach (var predecessor in block.Predecessors)
        {
            if (visited.Contains(predecessor))
            {
                // a loop back edge: whatever reaches the loop (unless a call in the loop may have clobbered it)
                if (Volatile.Contains(register))
                    return null;
                continue;
            }

            var write = WriteReaching(predecessor, predecessor.Instructions.Count, register, depth + 1, visited);
            if (write == null || found != null && found.Value.Instruction != write.Value.Instruction)
                return null;
            found = write;
        }

        return found;
    }
}
