using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

public class FieldReference(FieldAnalysisContext field, LocalVariable local, int offset) : IOperand
{
    public FieldAnalysisContext Field = field;
    public LocalVariable Local = local;
    public int Offset = offset;

    /// <summary>
    /// For a field nested inside value-type fields (local.a.b.Field), the enclosing fields from outermost
    /// inwards (a, b). Empty for a direct field of the local.
    /// </summary>
    public List<FieldAnalysisContext> Path = [];

    /// <summary>
    /// The outermost field accessed on the local, i.e. the one whose static-ness/ownership matters.
    /// </summary>
    public FieldAnalysisContext RootField => Path.Count > 0 ? Path[0] : Field;

    public IEnumerable<FieldAnalysisContext> Chain => Path.Append(Field);

    public override string ToString() => $"{Local.Name}.{string.Join(".", Chain.Select(f => f.Name))} ({Field.FieldType.FullName})";
}
