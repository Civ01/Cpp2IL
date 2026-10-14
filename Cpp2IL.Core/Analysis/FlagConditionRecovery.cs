using System.Collections.Generic;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Recovers high-level relational conditions from the explicit EFLAGS computations the lifter emits.
///
/// The x86 lifter models a <c>cmp</c>/<c>test</c> as a cluster of flag pseudo-registers
/// (ZF = (a-b)==0, SF = (a-b)&lt;0, OF = signed overflow, ...) and lowers each <c>jcc</c> into a
/// boolean expression over those flags. This pass recognises those canonical shapes for every
/// <see cref="OpCode.ConditionalJump"/> condition and rewrites the condition's defining instruction
/// into a single relational comparison (==, !=, &lt;, &lt;=, &gt;, &gt;=) on the original compare
/// operands. The now-orphaned flag arithmetic is removed by the dead-code pass that runs next.
///
/// Runs in SSA form, where each flag/temporary has a single, version-stable definition, so the
/// operands referenced at the branch are provably the ones captured at the compare.
///
/// Note: the lifter lowers the unsigned conditions (ja/jae/jb/jbe) with the same flag expressions as
/// their signed counterparts, so they are recovered as signed comparisons too - matching the
/// existing (signed) behaviour rather than introducing a new inaccuracy.
/// </summary>
public static class FlagConditionRecovery
{
    public static void Run(MethodAnalysisContext method) => Run(method.ControlFlowGraph!);

    public static void Run(ISILControlFlowGraph cfg)
    {
        var defOf = BuildDefMap(cfg);

        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode != OpCode.ConditionalJump)
                    continue;

                if (instruction.Operands[1] is not LocalVariable condition)
                    continue;

                if (!TryClassify(condition, defOf, out var relop, out var op0, out var op1))
                    continue;

                // Rewrite the condition's defining instruction in place into a single comparison.
                // Its destination (the condition local the branch reads) is preserved.
                // unsigned against zero is (in)equality: x >u 0 is x != 0, x <=u 0 is x == 0 (a null test, typically)
                if (instruction.Unsigned)
                {
                    if (IsZero(op1, defOf))
                        relop = relop switch { OpCode.CheckGreater => OpCode.CheckNotEqual, OpCode.CheckLessOrEqual => OpCode.CheckEqual, _ => relop };
                    else if (IsZero(op0, defOf))
                        relop = relop switch { OpCode.CheckLess => OpCode.CheckNotEqual, OpCode.CheckGreaterOrEqual => OpCode.CheckEqual, _ => relop };
                }

                var definition = defOf[condition];
                definition.OpCode = relop;
                definition.SetOperands(definition.Operands[0], op0!, op1!);
            }
        }

        // A zero flag kept as a value rather than branched on (cmp a,b / setne cl: bool changed = a != b) is the
        // comparison itself, not a test of the difference: ZF := (a - b) == 0 is ZF := a == b
        foreach (var instruction in cfg.Instructions)
            if (instruction is { OpCode: OpCode.CheckEqual, Operands: [LocalVariable, LocalVariable difference, Immediate { Value: 0 }] }
                && Def(difference, defOf) is { OpCode: OpCode.Subtract, Operands: [_, var left, var right] })
                instruction.SetOperands(instruction.Operands[0], left, right);

        // setne after it: (a == b) == 0 is a != b
        foreach (var instruction in cfg.Instructions)
            if (instruction is { OpCode: OpCode.CheckEqual, Operands: [LocalVariable, LocalVariable tested, Immediate { Value: 0 }] }
                && Def(tested, defOf) is { Operands: [_, var a, var b] } comparison
                && Negated(comparison.OpCode) is { } negated)
            {
                instruction.OpCode = negated;
                instruction.SetOperands(instruction.Operands[0], a, b);
            }
    }

    private static OpCode? Negated(OpCode relational) => relational switch
    {
        OpCode.CheckEqual => OpCode.CheckNotEqual,
        OpCode.CheckNotEqual => OpCode.CheckEqual,
        OpCode.CheckLess => OpCode.CheckGreaterOrEqual,
        OpCode.CheckGreaterOrEqual => OpCode.CheckLess,
        OpCode.CheckGreater => OpCode.CheckLessOrEqual,
        OpCode.CheckLessOrEqual => OpCode.CheckGreater,
        _ => null,
    };

    private static bool IsZero(IOperand? operand, Dictionary<LocalVariable, Instruction> defOf)
    {
        for (var hops = 0; hops < 4; hops++)
        {
            switch (operand)
            {
                case Immediate { Value: 0 }:
                    return true;
                case LocalVariable local when defOf.TryGetValue(local, out var definition):
                    if (definition is { OpCode: OpCode.Xor, Operands: [_, var left, var right] } && left.Equals(right))
                        return true;
                    if (definition is not { OpCode: OpCode.Move, Operands: [_, var source] })
                        return false;
                    operand = source;
                    continue;
                default:
                    return false;
            }
        }

        return false;
    }

    private static Dictionary<LocalVariable, Instruction> BuildDefMap(ISILControlFlowGraph cfg)
    {
        var defs = new Dictionary<LocalVariable, Instruction>();

        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                if (instruction.Destination is LocalVariable destination)
                    defs[destination] = instruction;

        return defs;
    }

    private static bool TryClassify(LocalVariable condition, Dictionary<LocalVariable, Instruction> defOf,
        out OpCode relop, out IOperand? op0, out IOperand? op1)
    {
        relop = default;

        // ZF on its own  =>  a == b   (je)
        if (IsZeroFlag(condition, defOf, out op0, out op1)) { relop = OpCode.CheckEqual; return true; }
        // SF on its own  =>  a < b    (js; exact for the common test-against-self case)
        if (IsSignFlag(condition, defOf, out op0, out op1)) { relop = OpCode.CheckLess; return true; }

        var definition = Def(condition, defOf);
        if (definition == null)
            return false;

        switch (definition.OpCode)
        {
            case OpCode.Not:
                var inner = AsLocal(definition.Operands[1]);
                if (IsZeroFlag(inner, defOf, out op0, out op1)) { relop = OpCode.CheckNotEqual; return true; }          // !ZF        => !=  (jne)
                if (IsSignFlag(inner, defOf, out op0, out op1)) { relop = OpCode.CheckGreaterOrEqual; return true; }    // !SF        => >=  (jns)
                if (IsSignEqualsOverflow(inner, defOf, out op0, out op1)) { relop = OpCode.CheckLess; return true; }    // !(SF==OF)  => <   (jl/jb)
                return false;

            case OpCode.CheckEqual:
                // SF == OF  =>  a >= b   (jge/jae)
                if (IsSignFlag(AsLocal(definition.Operands[1]), defOf, out op0, out op1)) { relop = OpCode.CheckGreaterOrEqual; return true; }
                return false;

            case OpCode.And:
                // (SF==OF) && !ZF  =>  a > b   (jg/ja)
                if (IsSignGreater(definition, defOf, out op0, out op1)) { relop = OpCode.CheckGreater; return true; }
                return false;

            case OpCode.Or:
                // !(SF==OF) || ZF  =>  a <= b   (jle/jbe)
                if (IsSignLessOrEqual(definition, defOf, out op0, out op1)) { relop = OpCode.CheckLessOrEqual; return true; }
                return false;

            default:
                return false;
        }
    }

    // ZF: local := CheckEqual(t, 0) where t := Subtract(a, b)
    private static bool IsZeroFlag(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.CheckEqual } || !IsZeroConstant(def.Operands[2]))
            return false;
        return IsSubtraction(AsLocal(def.Operands[1]), defOf, out op0, out op1);
    }

    // SF: local := CheckLess(t, 0) where t := Subtract(a, b)
    private static bool IsSignFlag(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.CheckLess } || !IsZeroConstant(def.Operands[2]))
            return false;
        return IsSubtraction(AsLocal(def.Operands[1]), defOf, out op0, out op1);
    }

    // local := Subtract(a, b) - a cmp's flags describe a against b. Any other value the flags were computed from
    // (a test's a & b, or an add/and/or/... result) is compared against zero instead.
    private static bool IsSubtraction(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def == null)
            return false;

        if (def.OpCode == OpCode.Subtract && def.Operands.Count == 3)
        {
            op0 = def.Operands[1];
            op1 = def.Operands[2];
            return true;
        }

        if (def.OpCode is OpCode.And or OpCode.Or or OpCode.Xor or OpCode.Add or OpCode.Subtract or OpCode.Negate or OpCode.Move
            or OpCode.Multiply or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.Phi)
        {
            op0 = local;
            op1 = new Immediate(0);
            return true;
        }

        return false;
    }

    // local := CheckEqual(SF, OF) - the signed "not less" test. Operands are taken from the SF side.
    private static bool IsSignEqualsOverflow(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.CheckEqual })
            return false;
        return IsSignFlag(AsLocal(def.Operands[1]), defOf, out op0, out op1);
    }

    // local := Not(CheckEqual(SF, OF))
    private static bool IsNotSignEqualsOverflow(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.Not })
            return false;
        return IsSignEqualsOverflow(AsLocal(def.Operands[1]), defOf, out op0, out op1);
    }

    // local := Not(ZF)
    private static bool IsNotZeroFlag(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf)
    {
        var def = Def(local, defOf);
        return def is { OpCode: OpCode.Not } && IsZeroFlag(AsLocal(def.Operands[1]), defOf, out _, out _);
    }

    // And((SF==OF), !ZF), in either operand order
    private static bool IsSignGreater(Instruction and, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        var left = AsLocal(and.Operands[1]);
        var right = AsLocal(and.Operands[2]);

        if (IsSignEqualsOverflow(left, defOf, out op0, out op1) && IsNotZeroFlag(right, defOf))
            return true;
        if (IsSignEqualsOverflow(right, defOf, out op0, out op1) && IsNotZeroFlag(left, defOf))
            return true;

        op0 = op1 = null;
        return false;
    }

    // Or(!(SF==OF), ZF), in either operand order
    private static bool IsSignLessOrEqual(Instruction or, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        var left = AsLocal(or.Operands[1]);
        var right = AsLocal(or.Operands[2]);

        if (IsNotSignEqualsOverflow(left, defOf, out op0, out op1) && IsZeroFlag(right, defOf, out _, out _))
            return true;
        if (IsNotSignEqualsOverflow(right, defOf, out op0, out op1) && IsZeroFlag(left, defOf, out _, out _))
            return true;

        op0 = op1 = null;
        return false;
    }

    private static Instruction? Def(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf)
        => local != null && defOf.TryGetValue(local, out var def) ? def : null;

    private static LocalVariable? AsLocal(IOperand operand) => operand as LocalVariable;

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };
}
