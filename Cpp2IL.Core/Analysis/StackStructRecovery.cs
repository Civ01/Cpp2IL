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
    public static void Run(MethodAnalysisContext method, ISILControlFlowGraph graph)
    {
        var app = method.AppContext;
        if (app.Binary.PointerSizeBytes != 8 || app.Binary is not PE)
            return; // Only implemented for the win64 ABI so far

        var resolver = app.InstructionSet.CallingConventionResolver;
        if (resolver == null)
            return;

        var roots = new Dictionary<int, TypeAnalysisContext>();
        var rejected = new HashSet<int>();
        var bufferCalls = new List<(Block Block, Instruction Call, int Slot, TypeAnalysisContext Type)>();

        void AddRoot(int offset, TypeAnalysisContext type)
        {
            if (rejected.Contains(offset))
                return;

            if (!IsStruct(type))
                return;

            if (roots.TryGetValue(offset, out var existing) && !ReferenceEquals(existing, type))
            {
                // Slot reused for different struct types, can't give it one type
                roots.Remove(offset);
                rejected.Add(offset);
                return;
            }

            roots[offset] = type;
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
            if (candidates.Count > 1 && !candidates.All(c => SameLayout(c, callee)))
                continue;

            // Only trust the operand layout if it's the managed one for this callee (not the raw unmanaged register dump)
            var expected = resolver.ResolveForManaged(callee);
            var argBase = call.OpCode == OpCode.CallVoid ? 1 : 2;
            if (call.Operands.Count != argBase + expected.Length)
                continue;

            if (resolver.ReturnsViaHiddenBuffer(callee) && AddressedSlot(block, block.Instructions.Count - 1, "rcx") is { } bufferSlot)
            {
                AddRoot(bufferSlot, callee.ReturnType);
                if (call.OpCode == OpCode.Call && call.Operands[1] is Register)
                    bufferCalls.Add((block, call, bufferSlot, callee.ReturnType));
            }

            var slot = argBase;
            if (!callee.IsStatic)
            {
                if (callee.DeclaringType is { IsValueType: true } declaringType && AddressedSlot(block, block.Instructions.Count - 1, call.Operands[slot]) is { } receiverSlot)
                    AddRoot(receiverSlot, declaringType);

                slot++;
            }

            foreach (var parameter in callee.Parameters)
            {
                if (slot >= call.Operands.Count)
                    break;

                var parameterType = parameter.ParameterType;
                var structType = parameterType switch
                {
                    ByRefTypeAnalysisContext { ElementType: { } element } => element,
                    _ when IsStruct(parameterType) && TypeSizes.UnboxedSize(parameterType, 8) is not (1 or 2 or 4 or 8) => parameterType,
                    _ => null
                };

                if (structType != null && AddressedSlot(block, block.Instructions.Count - 1, call.Operands[slot]) is { } argumentSlot)
                    AddRoot(argumentSlot, structType);

                slot++;
            }
        }

        if (roots.Count == 0)
            return;

        // Turn roots into regions, dropping any that overlap each other
        var regions = roots
            .Select(r => (Start: r.Key, End: r.Key + (int)TypeSizes.UnboxedSize(r.Value, 8), Type: r.Value))
            .Where(r => r.End > r.Start)
            .OrderBy(r => r.Start)
            .ToList();

        var accepted = new List<(int Start, int End, TypeAnalysisContext Type)>();
        for (var i = 0; i < regions.Count; i++)
        {
            var overlapsPrevious = i > 0 && regions[i - 1].End > regions[i].Start;
            var overlapsNext = i + 1 < regions.Count && regions[i].End > regions[i + 1].Start;
            if (!overlapsPrevious && !overlapsNext)
                accepted.Add(regions[i]);
        }

        // An access straddling a region boundary means our idea of the layout is wrong, as does taking the
        // address of the middle of one (we can't represent that yet)
        foreach (var instruction in graph.Instructions)
        {
            foreach (var operand in instruction.Operands)
            {
                switch (operand)
                {
                    case StackOffset access:
                        var accessEnd = access.Offset + (access.Size > 0 ? access.Size : 1);
                        accepted.RemoveAll(r => access.Offset < r.End && accessEnd > r.Start && (access.Offset < r.Start || accessEnd > r.End));
                        break;
                    case AddressOf { Target: StackOffset addressed }:
                        accepted.RemoveAll(r => addressed.Offset > r.Start && addressed.Offset < r.End);
                        break;
                }
            }
        }

        if (accepted.Count == 0)
            return;

        foreach (var instruction in graph.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.Operands[i] is not StackOffset access)
                    continue;

                foreach (var region in accepted)
                {
                    if (access.Offset < region.Start || access.Offset >= region.End)
                        continue;

                    var structSlot = new Register(null, StackAnalyzer.NameForSlot(new StackOffset(region.Start)));
                    instruction.SetOperand(i, new MemoryOperand(structSlot, addend: access.Offset - region.Start, size: access.Size));
                    break;
                }
            }
        }

        foreach (var region in accepted)
            method.StackStructTypes[StackAnalyzer.NameForSlot(new StackOffset(region.Start))] = region.Type;

        // A struct returned via hidden buffer is written into that buffer by the callee, which we otherwise don't see.
        // Model it as a copy of the returned value into the slot, right after the call.
        foreach (var (block, call, slot, type) in bufferCalls)
        {
            if (!accepted.Any(r => r.Start == slot && ReferenceEquals(r.Type, type)))
                continue;

            var successors = block.Successors.Distinct().ToList();
            if (successors is not [{ } next] || next == graph.ExitBlock || next.Predecessors.Distinct().Count() != 1)
                continue;

            var size = (int)TypeSizes.UnboxedSize(type, 8);
            var structSlot = new Register(null, StackAnalyzer.NameForSlot(new StackOffset(slot)));
            var returned = (Register)call.Operands[1];

            next.Instructions.Insert(0, new Instruction(call.Index, OpCode.Move,
                new MemoryOperand(structSlot, size: size),
                new MemoryOperand(returned, size: size)));
        }
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

    private static int? AddressedSlot(Block block, int callIndex, IOperand argument)
        => argument is Register register ? AddressedSlot(block, callIndex, register.Name)
            : argument is AddressOf { Target: StackOffset direct } ? direct.Offset
            : null;

    // Walks back from the call to the last write of the register in this block, and returns the stack
    // slot whose address it holds, if that's what it was set to.
    private static int? AddressedSlot(Block block, int callIndex, string registerName)
    {
        for (var i = callIndex - 1; i >= 0; i--)
        {
            var instruction = block.Instructions[i];

            if (instruction.Destination is not Register { } written || written.Name != registerName)
                continue;

            return instruction is { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: StackOffset slot }] } ? slot.Offset : null;
        }

        return null;
    }
}
