using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Win64 returns (and passes) an 8 byte struct in a general register, so a Vector2 being returned is two floats packed
/// into rax: <c>unpcklps xmm1,xmm0 / movq rax,xmm1 / ret</c>. VectorLaneRecovery leaves the low float in rax and the
/// high one in rax_hi; where rax turns out to be such a struct (it's returned, passed as one, or stored into a field of
/// that type), the struct is built from the two.
/// Runs in SSA form, once types are known.
/// </summary>
public static class SmallStructRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;

        var uses = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var instruction in graph.Instructions)
        {
            foreach (var operand in instruction.Operands)
            {
                if (operand is not LocalVariable used || ReferenceEquals(used, instruction.Destination))
                    continue;
                if (!uses.TryGetValue(used, out var list))
                    uses[used] = list = [];
                list.Add(instruction);
            }
        }

        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in graph.Instructions)
            if (instruction.Destination is LocalVariable defined)
                definitions[defined] = instruction;

        var changed = false;
        // first the other way (before pairs are rebuilt, which retypes the halves' sources): movq xmm0,rax with rax a Vector2 is its x, and the lane above it its y
        foreach (var block in graph.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var instruction = block.Instructions[i];
                if (!instruction.ReadsLowHalf && !instruction.ReadsHighHalf
                    || instruction is not { OpCode: OpCode.Move, Operands: [_, LocalVariable source] })
                    continue;

                if (source.Type is { } sourceType && Halves(sourceType, pointerSize) is var (first, second))
                {
                    var half = instruction.ReadsHighHalf ? second : first;
                    instruction.SetOperand(1, FieldOf(half, source));
                    // a copy typed as the whole struct before it was known to be half of it
                    if (instruction.Operands[0] is LocalVariable { } halfCopy && halfCopy.Type == sourceType)
                        halfCopy.Type = half[^1].FieldType;
                    changed = true;
                }
                else if (instruction.ReadsHighHalf)
                {
                    // as before: the high half of something we can't take apart
                    instruction.OpCode = OpCode.NotImplemented;
                    instruction.SetOperands(new StringLiteral("vector lane of an unknown value"));
                }
            }
        }

        foreach (var block in graph.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                if (block.Instructions[i] is not { OpCode: OpCode.Move, Operands: [LocalVariable packed, var low] } lowMove)
                    continue;

                var highIndex = -1;
                for (var j = i + 1; j < block.Instructions.Count && j <= i + 3; j++)
                {
                    if (block.Instructions[j] is { OpCode: OpCode.Move, Operands: [LocalVariable highLocal, _] }
                        && highLocal.Register.Name == packed.Register.Name + VectorLaneRecovery.HighSuffix)
                    {
                        highIndex = j;
                        break;
                    }
                }

                if (highIndex < 0 || StructUse(method, packed, uses, 0) is not { } structType
                    || Halves(structType, pointerSize) is not var (first, second))
                    continue;

                var highMove = block.Instructions[highIndex];
                var high = highMove.Operands[1];

                // the two halves of one struct of that type, taken apart and put back together: that struct
                if (WholeOf(low, first, structType, definitions) is { } lowOwner && SameWhole(lowOwner, WholeOf(high, second, structType, definitions)))
                {
                    highMove.OpCode = OpCode.Nop;
                    highMove.SetOperands();
                    lowMove.SetOperand(1, lowOwner);
                    packed.Type = structType;
                    changed = true;
                    continue;
                }

                // the halves may have been typed backwards from the register as a whole before it was known to be a pair
                FixHalfType(low, first[^1].FieldType, definitions);
                FixHalfType(high, second[^1].FieldType, definitions);

                var built = new LocalVariable($"packed{method.Locals.Count}", new Register(null, $"PACKED_{method.Locals.Count}", 0), structType);
                method.Locals.Add(built);

                highMove.OpCode = OpCode.Nop;
                highMove.SetOperands();

                // Unity's math structs read best built the way the source did: new Vector2(x, y)
                var constructor = structType.Namespace.StartsWith("UnityEngine", System.StringComparison.Ordinal) && first.Count == 1 && second.Count == 1
                    ? structType.Methods.FirstOrDefault(m => m is { Name: ".ctor", IsStatic: false, Parameters.Count: 2 }
                                                          && m.Parameters[0].ParameterType.FullName == first[0].FieldType.FullName
                                                          && m.Parameters[1].ParameterType.FullName == second[0].FieldType.FullName)
                    : null;

                if (constructor != null)
                    block.Instructions.Insert(i, new Instruction(lowMove.Index, OpCode.CallVoid, constructor, new AddressOf(built), low, high));
                else
                    block.Instructions.InsertRange(i, [
                        new Instruction(lowMove.Index, OpCode.Move, FieldOf(first, built), low),
                        new Instruction(lowMove.Index, OpCode.Move, FieldOf(second, built), high),
                    ]);
                lowMove.SetOperand(1, built);
                packed.Type = structType;
                i += constructor != null ? 1 : 2;
                changed = true;
            }
        }

        // arithmetic on the halves was typed as the whole struct while the halves were still the struct: it's a float
        if (changed)
            RetypeHalfArithmetic(graph, pointerSize);

        // whatever wasn't needed is free to go now
        foreach (var instruction in graph.Instructions)
            instruction.KeepAlive = false;
        DeadCodeEliminator.Run(graph);

        return changed;
    }

    // The struct a half was taken from: owner (a local) for owner.x, or owner.a.b for owner.a.b.x, as long as it is of
    // the given type; null otherwise
    private static IOperand? WholeOf(IOperand half, List<FieldAnalysisContext> chain, TypeAnalysisContext structType, Dictionary<LocalVariable, Instruction> definitions)
    {
        for (var hops = 0; hops < 4; hops++)
        {
            switch (half)
            {
                case FieldReference { Local: { } owner } field when field.Field == chain[^1] && field.Path.Count == chain.Count - 1:
                    return owner.Type == structType ? owner : null;
                case FieldReference { Local: { } owner } field when field.Field == chain[^1] && field.Path.Count >= chain.Count
                                                                     && field.Path[field.Path.Count - chain.Count] is { } container
                                                                     && container.FieldType == structType:
                    var outer = field.Path.Count - chain.Count;
                    return new FieldReference(container, owner, 0) { Path = field.Path.GetRange(0, outer) };
                case LocalVariable local when definitions.TryGetValue(local, out var definition) && definition is { OpCode: OpCode.Move, Operands: [_, var from] }:
                    half = from;
                    continue;
            }
            return null;
        }
        return null;
    }

    private static bool SameWhole(IOperand? a, IOperand? b) => (a, b) switch
    {
        (LocalVariable x, LocalVariable y) => ReferenceEquals(x, y),
        (FieldReference x, FieldReference y) => x.Field == y.Field && ReferenceEquals(x.Local, y.Local) && x.Path.SequenceEqual(y.Path),
        _ => false,
    };

    private static void RetypeHalfArithmetic(Graphs.ISILControlFlowGraph graph, int pointerSize)
    {
        static TypeAnalysisContext? TypeOf(IOperand operand) => operand switch
        {
            LocalVariable local => local.Type,
            FieldReference field => field.Field.FieldType,
            _ => null,
        };

        for (var round = 0; round < 4; round++)
        {
            var any = false;
            foreach (var instruction in graph.Instructions)
            {
                if (instruction.OpCode is not (OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Move or OpCode.Phi or OpCode.Negate)
                    || instruction.Destination is not LocalVariable { Type: { } wholeType } destination
                    || Halves(wholeType, pointerSize) == null)
                    continue;

                var sources = instruction.Operands.Skip(1).ToList();
                var types = sources.Select(TypeOf).ToList();
                var known = types.Where(t => t != null).ToList();
                if (known.Count == 0 || known.Any(t => t!.FullName != "System.Single")
                    || sources.Any(o => o is not (LocalVariable or FieldReference or FloatLiteral)))
                    continue;

                destination.Type = known[0];
                any = true;
            }

            if (!any)
                break;
        }
    }

    private static void FixHalfType(IOperand half, TypeAnalysisContext fieldType, Dictionary<LocalVariable, Instruction> definitions)
    {
        for (var hops = 0; hops < 4 && half is LocalVariable local; hops++)
        {
            if (local.Type is { } current && current != fieldType
                && (TypeSizes.StorageSize(current, 8) != 4 || current.FullName is "System.Int32" or "System.UInt32" && fieldType.FullName == "System.Single"))
                local.Type = fieldType;

            // and what it's a copy (or the negation, the absolute value...) of
            if (!definitions.TryGetValue(local, out var definition)
                || definition is not { OpCode: OpCode.Move or OpCode.Negate, Operands: [_, LocalVariable from] })
                break;
            half = from;
        }
    }

    private static FieldReference FieldOf(List<FieldAnalysisContext> chain, LocalVariable owner)
        => new(chain[^1], owner, 0) { Path = chain.GetRange(0, chain.Count - 1) };

    // An 8 byte struct made of two 4 byte values, the halves of the register
    private static (List<FieldAnalysisContext>, List<FieldAnalysisContext>)? Halves(TypeAnalysisContext type, int pointerSize)
    {
        if (!type.IsValueType || type.IsEnumType || MetadataResolver.IsPrimitiveOrEnum(type) || TypeSizes.UnboxedSize(type, pointerSize) != 8)
            return null;

        var first = type is GenericInstanceTypeAnalysisContext generic
            ? GenericInstanceFieldLayout.FindFieldChain(generic, 0, 4, pointerSize)
            : MetadataResolver.FindFieldChain(type, false, 0, 4, pointerSize);
        var second = type is GenericInstanceTypeAnalysisContext generic2
            ? GenericInstanceFieldLayout.FindFieldChain(generic2, 4, 4, pointerSize)
            : MetadataResolver.FindFieldChain(type, false, 4, 4, pointerSize);

        if (first == null || second == null
            || TypeSizes.StorageSize(first[^1].FieldType, pointerSize) != 4 || TypeSizes.StorageSize(second[^1].FieldType, pointerSize) != 4)
            return null;

        return (first, second);
    }

    // The struct type a value is used as: returned, stored into a field, passed as an argument (or the same for a copy)
    private static TypeAnalysisContext? StructUse(MethodAnalysisContext method, LocalVariable value, Dictionary<LocalVariable, List<Instruction>> uses, int depth)
    {
        if (depth > 3 || !uses.TryGetValue(value, out var users))
            return null;

        foreach (var use in users)
        {
            var type = use switch
            {
                { OpCode: OpCode.Return } => method.ReturnType,
                { OpCode: OpCode.Move, Operands: [FieldReference field, LocalVariable stored] } when ReferenceEquals(stored, value) && field.Offset >= 0 => field.Field.FieldType,
                { OpCode: OpCode.Move, Operands: [LocalVariable copy, LocalVariable copied] } when ReferenceEquals(copied, value) => StructUse(method, copy, uses, depth + 1),
                { OpCode: OpCode.Phi, Operands: [LocalVariable joined, ..] } => StructUse(method, joined, uses, depth + 1),
                { OpCode: OpCode.Call or OpCode.CallVoid } => ArgumentType(use, value),
                _ => null,
            };

            if (type is { IsValueType: true } && !MetadataResolver.IsPrimitiveOrEnum(type))
                return type;
        }

        return null;
    }

    private static TypeAnalysisContext? ArgumentType(Instruction call, LocalVariable value)
    {
        if (call.Operands[0] is not MethodAnalysisContext callee)
            return null;

        var first = (call.OpCode == OpCode.Call ? 2 : 1) + (callee.IsStatic ? 0 : 1);
        for (var i = first; i < call.Operands.Count; i++)
            if (ReferenceEquals(call.Operands[i], value) && i - first < callee.Parameters.Count)
                return callee.Parameters[i - first].ParameterType;

        return null;
    }
}
