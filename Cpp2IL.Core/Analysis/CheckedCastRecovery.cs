using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// IL2CPP compiles castclass as an isinst whose null result (for a non-null value) branches to a throw of
/// InvalidCastException, which came out as <c>T t = x as T; if (t == null) throw new InvalidCastException();</c> followed
/// by uses of x itself. Here that becomes one checked cast, <c>(T)x</c>, whose result the code past the check uses.
/// Runs in SSA form, after types are resolved.
/// </summary>
public static class CheckedCastRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var defOf = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in graph.Instructions)
            if (instruction.Destination is LocalVariable defined)
                defOf.TryAdd(defined, instruction);

        foreach (var block in graph.Blocks.ToList())
        {
            var last = block.Instructions.FindLastIndex(i => i.OpCode != OpCode.Nop);
            if (last < 0 || block.Instructions[last] is not { OpCode: OpCode.ConditionalJump, Operands: [Block thrower, LocalVariable condition] } jump
                || !ThrowsInvalidCast(thrower)
                || Through(condition, defOf) is not { } test
                || test is not { OpCode: OpCode.CheckEqual, Operands: [_, LocalVariable cast, Immediate { Value: 0 }] }
                || !defOf.TryGetValue(cast, out var isInst)
                || block.Successors.Distinct().ToList() is not [_, _]
                || block.Successors.FirstOrDefault(s => s != thrower) is not { } past)
                continue;

            // a sealed class is checked by comparing the object's class with it: the cast value is the object where
            // they're the same, else null, merged where the null check is
            if (isInst.OpCode == OpCode.Phi && SealedCast(isInst, block, defOf) is { } sealedCast)
            {
                isInst.OpCode = OpCode.IsInst;
                isInst.SetOperands(cast, sealedCast.Type, sealedCast.Value);
            }

            if (isInst is not { OpCode: OpCode.IsInst, Operands: [_, _, LocalVariable value] })
                continue;

            isInst.Checked = true;
            jump.OpCode = OpCode.Jump;
            jump.SetOperands(past);
            block.Successors.RemoveAll(s => s == thrower);
            thrower.Predecessors.RemoveAll(p => p == block);

            // past the check, the value is the cast one
            var dominance = new DominatorInfo(graph);
            // (and every other copy of what was cast)
            var root = Root(value, defOf);
            var replace = new Dictionary<LocalVariable, IOperand>();
            foreach (var local in defOf.Keys.Append(root).Distinct())
                if (Root(local, defOf) == root)
                    replace[local] = cast;
            foreach (var reached in graph.Blocks.Where(b => dominance.Dominates(past, b)))
                foreach (var instruction in reached.Instructions.Where(i => i.OpCode != OpCode.Phi))
                    SsaSimplifier.ReplaceUses(instruction, replace);
        }
    }

    // Phi(x, null) whose null comes from the branch taken when x's class isn't T: (T)x
    private static (TypeAnalysisContext Type, LocalVariable Value)? SealedCast(Instruction phi, Block block, Dictionary<LocalVariable, Instruction> defOf)
    {
        if (phi.Operands.Count != 3 || block.Predecessors.Count != 2)
            return null;

        LocalVariable? value = null;
        Block? nullFrom = null;
        for (var k = 0; k < 2; k++)
        {
            var input = phi.Operands[1 + k];
            if (input is Immediate { Value: 0 } || input is LocalVariable zero && Through(zero, defOf) is { OpCode: OpCode.Move, Operands: [_, Immediate { Value: 0 }] })
                nullFrom = block.Predecessors[k];
            else if (input is LocalVariable local)
                value = Root(local, defOf);
        }

        if (value == null || nullFrom == null)
            return null;

        // the block deciding: if (x->klass != T) goto (null)
        var deciding = nullFrom.Instructions.LastOrDefault(i => i.OpCode != OpCode.Nop) is { OpCode: OpCode.ConditionalJump, Operands: [_, LocalVariable condition] }
            ? nullFrom
            : nullFrom.Predecessors.Count == 1 ? nullFrom.Predecessors[0] : null;
        if (deciding?.Instructions.LastOrDefault(i => i.OpCode != OpCode.Nop) is not { OpCode: OpCode.ConditionalJump, Operands: [_, LocalVariable decided] }
            || Through(decided, defOf) is not { OpCode: OpCode.CheckNotEqual or OpCode.CheckEqual, Operands: [_, var left, var right] })
            return null;

        foreach (var (klassRead, klass) in new[] { (left, right), (right, left) })
            if (klassRead is MemoryOperand { Base: LocalVariable owner, Index: null, Addend: 0, Size: 8 } && Root(owner, defOf) == value
                && ClassOf(klass, defOf) is { IsValueType: false } type)
                return (type, value);

        return null;
    }

    private static TypeAnalysisContext? ClassOf(IOperand operand, Dictionary<LocalVariable, Instruction> defOf)
    {
        for (var hops = 0; hops < 4; hops++)
        {
            switch (operand)
            {
                case TypeAnalysisContext type and not (RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext):
                    return type is RuntimeClassTypeAnalysisContext { RepresentedType: var classOf } ? classOf : type;
                case LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var represented } }:
                    return represented;
                case LocalVariable local when defOf.TryGetValue(local, out var definition) && definition is { OpCode: OpCode.Move, Operands: [_, var source] }:
                    operand = source;
                    continue;
                default:
                    return null;
            }
        }

        return null;
    }

    private static LocalVariable Root(LocalVariable local, Dictionary<LocalVariable, Instruction> defOf)
    {
        for (var hops = 0; hops < 8 && defOf.TryGetValue(local, out var definition) && definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] }; hops++)
            local = source;
        return local;
    }

    // the definition of a condition, through copies of it
    private static Instruction? Through(LocalVariable local, Dictionary<LocalVariable, Instruction> defOf)
    {
        for (var hops = 0; hops < 4 && defOf.TryGetValue(local, out var definition); hops++)
        {
            if (definition is not { OpCode: OpCode.Move, Operands: [_, LocalVariable source] })
                return definition;
            local = source;
        }

        return null;
    }

    private static bool ThrowsInvalidCast(Block block)
        => block.Instructions.Where(i => i.OpCode is not (OpCode.Nop or OpCode.Interrupt)).ToList()
            is [{ OpCode: OpCode.Throw, Operands: [TypeAnalysisContext { FullName: "System.InvalidCastException" }] }];
}
