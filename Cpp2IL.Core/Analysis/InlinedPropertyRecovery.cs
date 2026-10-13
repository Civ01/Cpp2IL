using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// il2cpp inlines the trivial getters of the class libraries, so game code reads their private fields: a list's
/// <c>_size</c>, an enumerator's <c>_current</c>, a nullable's <c>hasValue</c>. Each read of one of those fields is
/// turned back into a call of the member that returns it (<c>Count</c>, <c>Current</c>, <c>HasValue</c>).
/// Runs out of SSA, once fields are resolved, before IL generation.
/// </summary>
public static class InlinedPropertyRecovery
{
    // declaring type (definition) -> field -> the getter (or method) that returns just that field
    private static readonly Dictionary<string, Dictionary<string, string>> Getters = new()
    {
        ["System.Collections.Generic.List`1"] = new() { ["_size"] = "get_Count" },
        ["System.Collections.Generic.Queue`1"] = new() { ["_size"] = "get_Count" },
        ["System.Collections.Generic.Stack`1"] = new() { ["_size"] = "get_Count" },
        ["System.Collections.Generic.List`1+Enumerator"] = new() { ["_current"] = "get_Current" },
        ["System.Collections.Generic.HashSet`1+Enumerator"] = new() { ["_current"] = "get_Current" },
        ["System.Collections.Generic.Dictionary`2+Enumerator"] = new() { ["_current"] = "get_Current" },
        ["System.Collections.Generic.Dictionary`2+KeyCollection+Enumerator"] = new() { ["_currentKey"] = "get_Current" },
        ["System.Collections.Generic.Dictionary`2+ValueCollection+Enumerator"] = new() { ["_currentValue"] = "get_Current" },
        ["System.Collections.Generic.Queue`1+Enumerator"] = new() { ["_currentElement"] = "get_Current" },
        ["System.Collections.Generic.Stack`1+Enumerator"] = new() { ["_currentElement"] = "get_Current" },
        ["System.Collections.Generic.KeyValuePair`2"] = new() { ["key"] = "get_Key", ["value"] = "get_Value" },
        ["System.Nullable`1"] = new() { ["hasValue"] = "get_HasValue", ["value"] = "GetValueOrDefault" },
        ["System.String"] = new() { ["_stringLength"] = "get_Length" },
    };

    public static void Run(MethodAnalysisContext method)
    {
        CollapseFieldwiseCopies(method);

        var graph = method.ControlFlowGraph!;
        var counter = 0;

        foreach (var block in graph.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var instruction = block.Instructions[i];
                if (instruction.OpCode is OpCode.Phi or OpCode.Nop)
                    continue;

                for (var operandIndex = 0; operandIndex < instruction.Operands.Count; operandIndex++)
                {
                    if (instruction.Operands[operandIndex] is not FieldReference whole || IsWritten(instruction, operandIndex))
                        continue;

                    // a field copied into the same field of another instance is part of copying the whole struct
                    if (instruction is { OpCode: OpCode.Move, Operands: [FieldReference copyDestination, _] }
                        && copyDestination.Chain.FirstOrDefault()?.Name == whole.Chain.First().Name)
                        continue;

                    // enumerator._current.priority: the getter gives the outer field, whose own field is then read
                    var read = whole.Path.Count > 0
                        ? new FieldReference(whole.Path[0], whole.Local, whole.Offset)
                        : whole;
                    if (Getter(read) is not { } getter || Receiver(read) is not { } receiver)
                        continue;

                    if (whole.Path.Count > 0)
                    {
                        var outer = new LocalVariable($"property{counter}", new Register(null, $"PROPERTY_{counter}", 0), read.Field.FieldType);
                        counter++;
                        method.Locals.Add(outer);

                        block.Instructions.Insert(i, new Instruction(instruction.Index, OpCode.Call, getter, outer, receiver));
                        i++;
                        instruction.SetOperand(operandIndex, new FieldReference(whole.Field, outer, whole.Offset) { Path = whole.Path.Skip(1).ToList() });
                        continue;
                    }

                    // (the field's type is the getter's, instantiated: the getter of a generic type only knows its T)
                    var resultType = read.Field.FieldType;

                    // a plain copy of the value becomes the call itself, anything else reads it from a temporary
                    if (instruction is { OpCode: OpCode.Move } && operandIndex == 1 && instruction.Operands[0] is LocalVariable or FieldReference)
                    {
                        if (instruction.Operands[0] is LocalVariable { Type: null } untyped)
                            untyped.Type = resultType;

                        instruction.OpCode = OpCode.Call;
                        instruction.SetOperands(getter, instruction.Operands[0], receiver);
                        break;
                    }

                    var temporary = new LocalVariable($"property{counter}", new Register(null, $"PROPERTY_{counter}", 0), resultType);
                    counter++;
                    method.Locals.Add(temporary);

                    block.Instructions.Insert(i, new Instruction(instruction.Index, OpCode.Call, getter, temporary, receiver));
                    i++;
                    instruction.SetOperand(operandIndex, temporary);
                }
            }
        }
    }

    /// <summary>
    /// A struct copied from one local to another field by field (an enumerator, as it comes back from GetEnumerator):
    /// once every field is copied, with nothing else touching either local in between, it's one copy of the struct.
    /// </summary>
    private static void CollapseFieldwiseCopies(MethodAnalysisContext method)
    {
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            for (var start = 0; start < block.Instructions.Count; start++)
            {
                if (block.Instructions[start] is not { OpCode: OpCode.Move, Operands: [FieldReference { Local: var destination } first, FieldReference { Local: var source } firstSource] }
                    || ReferenceEquals(destination, source) || destination.Type is not { } structType || !StackStructRecovery.IsStruct(structType)
                    || source.Type?.FullName != structType.FullName || !SameChain(first, firstSource))
                    continue;

                var expected = Leaves(structType, [], 0);
                if (expected == null || expected.Count == 0)
                    continue;

                var copied = new HashSet<string>();
                var copies = new List<Instruction>();
                for (var j = start; j < block.Instructions.Count && copied.Count < expected.Count; j++)
                {
                    var instruction = block.Instructions[j];
                    if (instruction is { OpCode: OpCode.Move, Operands: [FieldReference into, FieldReference from] }
                        && ReferenceEquals(into.Local, destination) && ReferenceEquals(from.Local, source) && SameChain(into, from))
                    {
                        copied.Add(ChainKey(into));
                        copies.Add(instruction);
                        continue;
                    }

                    if (instruction.OpCode != OpCode.Nop && Mentions(instruction, destination, source))
                        break;
                }

                if (!expected.SetEquals(copied))
                    continue;

                copies[0].SetOperands(destination, source);
                foreach (var redundant in copies.Skip(1))
                {
                    redundant.OpCode = OpCode.Nop;
                    redundant.SetOperands();
                }
            }
        }
    }

    private static bool SameChain(FieldReference a, FieldReference b) => ChainKey(a) == ChainKey(b);

    private static string ChainKey(FieldReference reference) => string.Join(".", reference.Chain.Select(f => f.Name));

    private static bool Mentions(Instruction instruction, LocalVariable a, LocalVariable b) => instruction.Operands.Any(o => o switch
    {
        LocalVariable local => ReferenceEquals(local, a) || ReferenceEquals(local, b),
        FieldReference field => ReferenceEquals(field.Local, a) || ReferenceEquals(field.Local, b),
        AddressOf { Target: LocalVariable addressed } => ReferenceEquals(addressed, a) || ReferenceEquals(addressed, b),
        AddressOf { Target: FieldReference addressedField } => ReferenceEquals(addressedField.Local, a) || ReferenceEquals(addressedField.Local, b),
        MemoryOperand { Base: LocalVariable memoryBase } => ReferenceEquals(memoryBase, a) || ReferenceEquals(memoryBase, b),
        _ => false,
    });

    // Every primitive (or reference) field of a struct, as name chains through its struct fields
    private static HashSet<string>? Leaves(TypeAnalysisContext type, List<string> prefix, int depth)
    {
        if (depth > 4)
            return null;

        var instance = type as GenericInstanceTypeAnalysisContext;
        var definition = instance?.GenericType ?? type;
        var leaves = new HashSet<string>();

        foreach (var field in definition.Fields)
        {
            if (field.IsStatic || (field.Attributes & System.Reflection.FieldAttributes.Literal) != 0)
                continue;

            var fieldType = instance != null ? GenericInstantiation.Instantiate(field.FieldType, instance.GenericArguments, []) : field.FieldType;
            List<string> chain = [..prefix, field.Name];

            if (StackStructRecovery.IsStruct(fieldType))
            {
                if (Leaves(fieldType, chain, depth + 1) is not { } inner)
                    return null;
                leaves.UnionWith(inner);
            }
            else
                leaves.Add(string.Join(".", chain));
        }

        return leaves;
    }

    // (a field as destination isn't one to Instruction.Destination, which only counts locals)
    private static bool IsWritten(Instruction instruction, int operandIndex) => instruction.OpCode switch
    {
        OpCode.Call or OpCode.IndirectCall => operandIndex == 1,
        OpCode.CallVoid or OpCode.Return or OpCode.ConditionalJump or OpCode.Jump or OpCode.Throw => false,
        _ => operandIndex == 0,
    };

    private static MethodAnalysisContext? Getter(FieldReference read)
    {
        var field = read.Field;
        if (field.IsStatic)
            return null;

        var owner = field.DeclaringType;
        var instance = owner as GenericInstanceTypeAnalysisContext;
        var definition = instance?.GenericType ?? owner;

        if (!Getters.TryGetValue(definition.FullName, out var byField) || !byField.TryGetValue(field.Name, out var getterName))
            return null;

        if (definition.Methods.FirstOrDefault(m => m.Name == getterName && !m.IsStatic && m.Parameters.Count == 0) is not { } baseGetter)
            return null; // stripped

        if (instance == null)
            return definition.GenericParameters.Count == 0 ? baseGetter : null;

        return new ConcreteGenericMethodAnalysisContext(baseGetter, instance.GenericArguments, []);
    }

    // What the getter is called on: the object itself, or for a struct the address of the local holding it
    private static IOperand? Receiver(FieldReference read)
    {
        if (read.Path.Count > 0)
            return null; // a struct inside a struct field: would need the field's address, which isn't worth it yet

        var local = read.Local;
        if (!read.Field.DeclaringType.IsValueType)
            return local;

        return local.Type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext ? local : new AddressOf(local);
    }
}
