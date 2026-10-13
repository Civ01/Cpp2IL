using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// il2cpp inlines <c>List&lt;T&gt;.Add</c> into its callers:
/// <code>
///   list._version++;
///   T[] items = list._items; int size = list._size;
///   if ((uint)size &lt; (uint)items.Length) { list._size = size + 1; items[size] = item; }
///   else list.AddWithResize(item);
/// </code>
/// The out-of-line half names the list and the item, so the whole diamond becomes <c>list.Add(item)</c>.
/// Likewise <c>List&lt;T&gt;.Clear</c>: <c>list._version++; int size = list._size; list._size = 0; if (size &gt; 0)
/// Array.Clear(list._items, 0, size);</c> (without the Array.Clear when T holds no references) becomes <c>list.Clear()</c>.
/// Runs out of SSA, before IL generation.
/// </summary>
public static class InlinedListAddRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;

        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var slow in graph.Blocks.ToList())
            {
                if (TryRecover(graph, slow) || TryRecoverClear(graph, slow))
                {
                    changed = true;
                    break;
                }
            }
        }
    }

    private static bool TryRecover(ISILControlFlowGraph graph, Block slow)
    {
        var resize = slow.Instructions.FirstOrDefault(i => i is { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: "AddWithResize" }, LocalVariable, _, ..] });
        if (resize == null || resize.Operands[0] is not MethodAnalysisContext addWithResize || resize.Operands[1] is not LocalVariable list)
            return false;

        if (slow.Predecessors.Distinct().ToList() is not [{ } test] || test.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump } branch
            || test.Successors.Distinct().Count() != 2)
            return false;

        // the slow path computes the item and calls AddWithResize, nothing else
        var slowTerminator = Terminator(slow);
        if (slow.Instructions.Any(i => i != resize && i != slowTerminator && !IsPure(i)))
            return false;

        var fast = test.Successors.First(s => s != slow);

        // the fast path: list._size = size + 1; items[size] = item; possibly over a few blocks
        var fastBlocks = new List<Block>();
        var current = fast;
        while (true)
        {
            if (current.Predecessors.Distinct().Count() != 1 || fastBlocks.Contains(current) || fastBlocks.Count > 4)
                return false;

            fastBlocks.Add(current);
            if (SameExit(current, slow))
                break;

            if (current.Successors.Distinct().ToList() is not [{ } next] || Terminator(current) is { OpCode: not OpCode.Jump })
                return false;
            current = next;
        }

        var sizeStores = 0;
        var elementStores = 0;
        foreach (var instruction in fastBlocks.SelectMany(b => b.Instructions))
        {
            if (instruction == Terminator(fastBlocks[^1]) || IsPure(instruction))
                continue;

            if (instruction is { OpCode: OpCode.Move, Operands: [FieldReference { Field.Name: "_size", Local: var sizeOwner }, _] } && ReferenceEquals(sizeOwner, list))
                sizeStores++;
            // the element, whole or (a struct) field by field
            else if (instruction is { OpCode: OpCode.Move, Operands: [ArrayAccess or MemoryOperand, _] }
                     || instruction is { OpCode: OpCode.Move, Operands: [FieldReference { Local: var elementOwner }, _] } && !ReferenceEquals(elementOwner, list))
                elementStores++;
            else
                return false;
        }

        if (sizeStores != 1 || elementStores == 0)
            return false;

        if (FindAdd(addWithResize) is not { } add)
            return false;

        // list._version++, just before
        var versionBump = FindVersionBump(test, list);

        // the test block runs the slow path's code, with Add in place of AddWithResize, then carries on the way both did
        test.Instructions.Remove(branch);
        foreach (var instruction in slow.Instructions)
        {
            if (instruction == resize)
                test.Instructions.Add(new Instruction(resize.Index, OpCode.CallVoid, add, list, resize.Operands[2]));
            else if (instruction != slowTerminator)
                test.Instructions.Add(instruction);
        }

        var successors = slow.Successors.Distinct().ToList();
        if (slowTerminator != null)
            test.Instructions.Add(slowTerminator);
        else if (successors is [{ } fallInto])
            test.Instructions.Add(new Instruction(resize.Index, OpCode.Jump, fallInto));

        foreach (var removed in fastBlocks.Append(slow))
        {
            foreach (var successor in removed.Successors)
                successor.Predecessors.Remove(removed);
            removed.Successors.Clear();
            removed.Predecessors.Clear();
            graph.Blocks.Remove(removed);
        }

        test.Successors.Clear();
        foreach (var successor in successors)
        {
            test.Successors.Add(successor);
            successor.Predecessors.Add(test);
        }

        test.CalculateBlockType();

        foreach (var bump in versionBump)
        {
            bump.OpCode = OpCode.Nop;
            bump.SetOperands();
        }

        return true;
    }

    private static bool TryRecoverClear(ISILControlFlowGraph graph, Block block)
    {
        var storeIndex = block.Instructions.FindIndex(i => i is { OpCode: OpCode.Move, Operands: [FieldReference { Field.Name: "_size", Local: { } }, Immediate { Value: 0 }] });
        if (storeIndex < 0)
            return false;

        var store = block.Instructions[storeIndex];
        var sizeField = (FieldReference)store.Operands[0];
        var list = sizeField.Local;
        if (!IsList(sizeField.Field.DeclaringType) || FindMethod(sizeField.Field.DeclaringType, "Clear", 0) is not { } clear)
            return false;

        // list._version++ before it (in this block, or the straight line before)
        var versionBump = FindVersionBump(block, list, storeIndex);
        if (versionBump.Count == 0)
            return false;

        // for a T holding references, the elements are cleared too: if (size > 0) Array.Clear(list._items, 0, size)
        var sizeRead = block.Instructions.Take(storeIndex).LastOrDefault(i => i is { OpCode: OpCode.Move, Operands: [LocalVariable, FieldReference { Field.Name: "_size", Local: var owner }] } && ReferenceEquals(owner, list));
        if (sizeRead != null && block.Instructions.LastOrDefault() is { OpCode: OpCode.ConditionalJump } branch && block.Successors.Distinct().Count() == 2)
        {
            var size = (LocalVariable)sizeRead.Operands[0];
            var clearing = block.Successors.FirstOrDefault(s => s.Predecessors.Distinct().Count() == 1
                                                                && s.Instructions.Any(i => i is { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: "Clear", DeclaringType.FullName: "System.Array" }, _, _, var cleared, ..] } && ReferenceEquals(cleared, size)));
            if (clearing == null)
                return false;

            var after = block.Successors.First(s => s != clearing);
            if (clearing.Successors.Distinct().ToList() is not [{ } rejoin] || rejoin != after
                || clearing.Instructions.Any(i => !IsPure(i) && i.OpCode is not (OpCode.Jump or OpCode.CallVoid)))
                return false;

            branch.OpCode = OpCode.Jump;
            branch.SetOperands(after);

            foreach (var successor in clearing.Successors)
                successor.Predecessors.Remove(clearing);
            clearing.Successors.Clear();
            block.Successors.Remove(clearing);
            clearing.Predecessors.Clear();
            graph.Blocks.Remove(clearing);
            block.CalculateBlockType();
        }

        store.OpCode = OpCode.CallVoid;
        store.SetOperands(clear, list);

        foreach (var bump in versionBump)
        {
            bump.OpCode = OpCode.Nop;
            bump.SetOperands();
        }

        return true;
    }

    private static bool IsList(TypeAnalysisContext type) =>
        ((type as GenericInstanceTypeAnalysisContext)?.GenericType ?? type).FullName == "System.Collections.Generic.List`1";

    private static MethodAnalysisContext? FindMethod(TypeAnalysisContext owner, string name, int parameters)
    {
        var instance = owner as GenericInstanceTypeAnalysisContext;
        var definition = instance?.GenericType ?? owner;
        if (definition.Methods.FirstOrDefault(m => m.Name == name && !m.IsStatic && m.Parameters.Count == parameters) is not { } found)
            return null;

        return instance != null ? new ConcreteGenericMethodAnalysisContext(found, instance.GenericArguments, []) : found;
    }

    private static Instruction? Terminator(Block block) =>
        block.Instructions.LastOrDefault() is { OpCode: OpCode.Jump or OpCode.Return } last ? last : null;

    // Leaves the same way the slow path does: jumping to (or falling into) the same block, or returning
    private static bool SameExit(Block candidate, Block slow)
    {
        var a = Terminator(candidate);
        var b = Terminator(slow);

        if (a is { OpCode: OpCode.Return } || b is { OpCode: OpCode.Return })
            return a is { OpCode: OpCode.Return } && b is { OpCode: OpCode.Return } && a.Operands.Count == 0 && b.Operands.Count == 0;

        var candidateNext = candidate.Successors.Distinct().ToList();
        var slowNext = slow.Successors.Distinct().ToList();
        return candidateNext is [{ } x] && slowNext is [{ } y] && x == y;
    }

    // Computes a value into a local, nothing more
    private static bool IsPure(Instruction instruction) => instruction.OpCode switch
    {
        OpCode.Nop => true,
        OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.And or OpCode.Or
            or OpCode.Xor or OpCode.Not or OpCode.Negate or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual) => instruction.Operands[0] is LocalVariable,
        _ => false,
    };

    private static MethodAnalysisContext? FindAdd(MethodAnalysisContext addWithResize)
    {
        var baseMethod = (addWithResize as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext ?? addWithResize;
        if (baseMethod.DeclaringType?.Methods.FirstOrDefault(m => m is { Name: "Add", IsStatic: false } && m.Parameters.Count == 1) is not { } baseAdd)
            return null;

        return addWithResize is ConcreteGenericMethodAnalysisContext concrete
            ? new ConcreteGenericMethodAnalysisContext(baseAdd, concrete.TypeGenericParameters, [])
            : baseAdd;
    }

    // list._version = list._version + 1 (directly, or through a temporary) in the test block or the straight line before it
    private static List<Instruction> FindVersionBump(Block test, LocalVariable list, int before = -1)
    {
        var block = test;
        for (var depth = 0; depth < 3 && block != null; depth++)
        {
            for (var i = (depth == 0 && before >= 0 ? before : block.Instructions.Count) - 1; i >= 0; i--)
            {
                var instruction = block.Instructions[i];
                if (instruction is { OpCode: OpCode.Add, Operands: [FieldReference { Field.Name: "_version", Local: var owner }, FieldReference, Immediate { Value: 1 }] } && ReferenceEquals(owner, list))
                    return [instruction];

                if (instruction is { OpCode: OpCode.Move, Operands: [FieldReference { Field.Name: "_version", Local: var storeOwner }, LocalVariable bumped] } && ReferenceEquals(storeOwner, list))
                {
                    var increment = block.Instructions.Take(i).LastOrDefault(d => d is { OpCode: OpCode.Add, Operands: [LocalVariable sum, FieldReference { Field.Name: "_version" }, Immediate { Value: 1 }] } && ReferenceEquals(sum, bumped));
                    return increment != null ? [instruction, increment] : [instruction];
                }
            }

            block = block.Predecessors.Distinct().ToList() is [{ } only] ? only : null;
        }

        return [];
    }
}
