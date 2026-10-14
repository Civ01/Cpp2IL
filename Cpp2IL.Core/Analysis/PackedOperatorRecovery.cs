using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// An 8 byte struct of two ints or floats (Vector2Int, Vector2) lives in one register, and its operators inline as one
/// packed instruction (psubd, addps) on the whole value: <c>(long)(coord - offset)</c>. Arithmetic on such a struct is its
/// operator, <c>coord - offset</c>, when the struct has one. Runs in SSA form, once types are known.
/// </summary>
public static class PackedOperatorRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;

        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var instruction in method.ControlFlowGraph!.Instructions)
            {
                if (instruction is not { OpCode: OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide, ScalarSingle: false, Operands: [LocalVariable destination, var left, var right] })
                    continue;

                var type = PackedStruct(left, pointerSize) ?? PackedStruct(right, pointerSize);
                if (type == null || !Fits(left, type) || !Fits(right, type))
                    continue;

                var name = instruction.OpCode switch
                {
                    OpCode.Add => "op_Addition",
                    OpCode.Subtract => "op_Subtraction",
                    OpCode.Multiply => "op_Multiply",
                    _ => "op_Division",
                };

                var op = type.Methods.FirstOrDefault(m => m.IsStatic && m.Name == name && m.Parameters.Count == 2
                                                          && m.Parameters.All(p => ReferenceEquals(p.ParameterType, type)) && ReferenceEquals(m.ReturnType, type));
                if (op == null)
                    continue;

                instruction.OpCode = OpCode.Call;
                instruction.SetOperands(op, destination, left, right);
                destination.Type = type;
                changed = true;
            }
        }
    }

    // the operand's type, if it's a whole struct of 8 bytes with an operator to use
    private static TypeAnalysisContext? PackedStruct(IOperand operand, int pointerSize)
    {
        var type = operand switch
        {
            LocalVariable { Type: { } localType } => localType,
            FieldReference field => field.Field.FieldType,
            _ => null,
        };

        return type is { IsValueType: true, IsEnumType: false } && type.Namespace != "System" && type is not (PointerTypeAnalysisContext or ByRefTypeAnalysisContext)
               && TypeSizes.StorageSize(type, pointerSize) == 8 && type.Fields.Count(f => !f.IsStatic) == 2
            ? type
            : null;
    }

    // the other operand is the same struct (the result of another such operation is, once that's recovered)
    private static bool Fits(IOperand operand, TypeAnalysisContext type) => operand switch
    {
        LocalVariable { Type: var localType } => ReferenceEquals(localType, type),
        FieldReference field => ReferenceEquals(field.Field.FieldType, type),
        _ => false,
    };
}
