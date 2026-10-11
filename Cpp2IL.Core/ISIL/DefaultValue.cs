using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

/// <summary>
/// The zero value of a type, i.e. <c>default(T)</c>. Produced when a struct is zeroed in chunks.
/// </summary>
public class DefaultValue(TypeAnalysisContext type) : IOperand
{
    public TypeAnalysisContext Type = type;

    public override string ToString() => $"default({Type.FullName})";
}
