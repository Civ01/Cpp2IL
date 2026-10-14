using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Fixes the compare-a-flag-against-zero pairs the we get for every conditional: <c>bool != 0</c>
/// is the bool itself, and <c>bool == 0</c> is its negation.
/// </summary>
public static class BooleanFlagSimplifier
{
    public static void Run(MethodAnalysisContext method)
    {
        var booleanType = method.AppContext.SystemTypes.SystemBooleanType;

        bool IsBool(IOperand operand) => operand is LocalVariable { Type: { } type } && type == booleanType;
        bool IsInteger(LocalVariable local) => local.Type is { Namespace: "System", Name: "Int32" or "UInt32" or "Int64" or "UInt64" or "Byte" };

        // mov eax,eax (and eax,0FFFFFFFFh) or and al,1 on a bool is the bool; and/or/xor of two bools is a bool
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var instruction in method.ControlFlowGraph!.Instructions)
            {
                if (instruction is not { OpCode: OpCode.And or OpCode.Or or OpCode.Xor, Operands: [LocalVariable destination, var left, var right] }
                    || !IsInteger(destination) && destination.Type != null)
                    continue;

                if (instruction.OpCode == OpCode.And && IsBool(left) && right is Immediate { Value: 1 or 0xFF or 0xFFFFFFFF })
                {
                    instruction.OpCode = OpCode.Move;
                    instruction.SetOperands(destination, left);
                    destination.Type = booleanType;
                    changed = true;
                }
                else if (IsBool(left) && IsBool(right))
                {
                    destination.Type = booleanType;
                    changed = true;
                }
            }
        }

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual) || instruction.Operands.Count < 3)
                continue;

            if (!IsZeroConstant(instruction.Operands[2]))
                continue;

            if (instruction.Operands[1] is not LocalVariable { Type: { } type } || type != booleanType)
                continue;

            instruction.OpCode = instruction.OpCode == OpCode.CheckNotEqual ? OpCode.Move : OpCode.Not;
            instruction.SetOperands(instruction.Operands[0], instruction.Operands[1]);
        }
    }

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };
}
