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
            else if (candidates.Count > 1 && !candidates.All(c => SameLayout(c, callee) && ReferenceEquals(c.DeclaringType, callee.DeclaringType)))
                continue;

            // Only trust the operand layout if it's the managed one for this callee (not the raw unmanaged register dump)
            var expected = resolver.ResolveForManaged(callee);
            var argBase = call.OpCode == OpCode.CallVoid ? 1 : 2;
            if (call.Operands.Count != argBase + expected.Length)
                continue;

            var last = block.Instructions.Count - 1;

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

        AddParameterCopyRoots(method, graph, roots);

        if (roots.Count == 0)
            return;

        // Each slot holds one struct, or - when MSVC reuses it for different struct types - one per call it's handed to
        var slots = new List<Slot>();
        foreach (var group in roots.GroupBy(r => r.Offset))
        {
            var types = group.Select(r => r.Type).Distinct().ToList();
            var instances = types.Count == 1
                ? [new Instance(StackAnalyzer.NameForSlot(new StackOffset(group.Key)), types[0], group.Key, group.Key + (int)TypeSizes.UnboxedSize(types[0], 8), group.ToList())]
                : group.OrderBy(r => r.Call.Index).Select((r, n) => new Instance($"{StackAnalyzer.NameForSlot(new StackOffset(group.Key))}_{n}", r.Type, group.Key,
                    group.Key + (int)TypeSizes.UnboxedSize(r.Type, 8), [r])).ToList();

            if (instances.Any(i => i.End <= i.Start))
                continue;

            slots.Add(new Slot(group.Key, instances.Max(i => i.End), instances));
        }

        slots = slots.OrderBy(r => r.Start).ToList();
        Debug?.Invoke("slots: " + string.Join(", ", slots.Select(r => $"{r.Start:X}-{r.End:X} " + string.Join("|", r.Instances.Select(i => i.Type.ToString())))));

        var accepted = new List<Slot>();
        for (var i = 0; i < slots.Count; i++)
        {
            var overlapsPrevious = i > 0 && slots[i - 1].End > slots[i].Start;
            var overlapsNext = i + 1 < slots.Count && slots[i].End > slots[i + 1].Start;
            if (!overlapsPrevious && !overlapsNext)
                accepted.Add(slots[i]);
        }

        // Which instance each access belongs to. An access straddling a slot boundary means our idea of the layout is
        // wrong, as does taking the address of the middle of one (we can't represent that yet)
        var assignments = new List<(Instruction Instruction, int Operand, Instance Instance, int Start)>();
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
                            var isWrite = operandIndex == 0 && instruction.OpCode == OpCode.Move;
                            var instance = slot.Instances.Count == 1 ? slot.Instances[0] : Choose(slot, instruction, isWrite);
                            if (instance == null || access.Offset < instance.Start || accessEnd > instance.End)
                            {
                                Debug?.Invoke($"reject {slot.Start:X} by {instruction}");
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
                                accepted.Remove(slot);
                                continue;
                            }

                            if (slot.Instances.Count == 1)
                                continue; // becomes the address of the slot register as usual

                            var owner = slot.Instances.FirstOrDefault(i => i.Roots.Any(r => r.Definition == instruction));
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

            var successors = block.Successors.Distinct().ToList();
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

            block = block.Successors.Distinct().ToList() is [{ } next] && next.Predecessors.Distinct().Count() == 1 ? next : null;
        }
    }

    private sealed record Root(int Offset, TypeAnalysisContext Type, Instruction Call, Instruction Definition, bool CalleeReads, bool CalleeWrites);

    private sealed record Instance(string Name, TypeAnalysisContext Type, int Start, int End, List<Root> Roots);

    private sealed record Slot(int Start, int End, List<Instance> Instances);

    // A slot reused for several structs: our write is building the next call's argument, our read is of what the last
    // call left there (a returned struct), or else of an argument we're building
    private static Instance? Choose(Slot slot, Instruction access, bool isWrite)
    {
        var ordered = slot.Instances.OrderBy(i => i.Roots[0].Call.Index).ToList();
        var next = ordered.FirstOrDefault(i => i.Roots[0].Call.Index > access.Index && i.Roots[0].CalleeReads);
        var previous = ordered.LastOrDefault(i => i.Roots[0].Call.Index < access.Index);

        if (isWrite)
            return next ?? (previous is { Roots: [{ CalleeWrites: true }] } ? previous : null);

        if (previous is { Roots: [{ CalleeWrites: true }] })
            return previous;

        return next ?? previous;
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

    private static (int Offset, Instruction Definition)? AddressedSlot(Block block, int callIndex, IOperand argument)
        => argument is Register register ? AddressedSlot(block, callIndex, register.Name)
            : argument is AddressOf { Target: StackOffset direct } ? (direct.Offset, block.Instructions[callIndex])
            : null;

    // Walks back from the call to the last write of the register in this block, and returns the stack
    // slot whose address it holds, if that's what it was set to.
    private static (int Offset, Instruction Definition)? AddressedSlot(Block block, int callIndex, string registerName)
    {
        for (var i = callIndex - 1; i >= 0; i--)
        {
            var instruction = block.Instructions[i];

            if (instruction.Destination is not Register { } written || written.Name != registerName)
                continue;

            return instruction is { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: StackOffset slot }] } ? (slot.Offset, instruction) : null;
        }

        return null;
    }
}
