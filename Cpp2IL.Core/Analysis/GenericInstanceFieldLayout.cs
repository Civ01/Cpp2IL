using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

//Resolves field offsets on generic types, which are all 0 in the metadata.
public static class GenericInstanceFieldLayout
{
    public static FieldAnalysisContext? FindFieldAtOffset(TypeAnalysisContext definition, long targetOffset)
    {
        var pointerSize = definition.AppContext.Binary.PointerSizeBytes;

        // TODO Support anything outside the trivial case.
        for (var baseType = definition.BaseType; baseType != null; baseType = baseType.BaseType)
            if (baseType.Fields.Any(f => !f.IsStatic))
                return null;

        var offset = 2L * pointerSize;

        foreach (var field in definition.Fields)
        {
            if (field.IsStatic)
                continue;

            if (GetSizeAndAlignment(field.FieldType, pointerSize) is not var (size, alignment))
                return null;

            offset = (offset + alignment - 1) & ~(alignment - 1);

            if (offset == targetOffset)
                return field;

            offset += size;
        }

        return null;
    }

    /// <summary>
    /// The (possibly nested) field a <paramref name="size"/>-byte access at <paramref name="targetOffset"/> into an instance
    /// of a generic type touches, outermost first, each one the field of the concrete instantiation. Lays the type out
    /// sequentially with its type arguments substituted, since the metadata has no offsets for generic types.
    /// </summary>
    public static List<FieldAnalysisContext>? FindFieldChain(GenericInstanceTypeAnalysisContext owner, long targetOffset, int size, int pointerSize, int depth = 0)
    {
        if (depth > 6)
            return null;

        var definition = owner.GenericType;
        for (var baseType = definition.BaseType; baseType != null; baseType = baseType.BaseType)
            if (baseType.Fields.Any(f => !f.IsStatic))
                return null;

        var offset = definition.IsValueType ? 0L : 2L * pointerSize;

        foreach (var field in definition.Fields)
        {
            if (field.IsStatic || (field.Attributes & System.Reflection.FieldAttributes.Literal) != 0)
                continue;

            if (TypeSizes.SizeAndAlignment(field.FieldType, pointerSize, owner.GenericArguments, 0) is not var (fieldSize, alignment))
                return null;

            offset = (offset + alignment - 1) & ~(alignment - 1);

            if (targetOffset >= offset && targetOffset < offset + fieldSize)
            {
                var concrete = new ConcreteGenericFieldAnalysisContext(field, owner);
                var fieldType = concrete.FieldType;
                var inner = targetOffset - offset;

                // the whole field
                if (inner == 0 && (size == 0 || size == fieldSize || !Analysis.StackStructRecovery.IsStruct(fieldType)))
                    return [concrete];

                // inside a struct field
                if (!Analysis.StackStructRecovery.IsStruct(fieldType))
                    return null;

                var nested = fieldType is GenericInstanceTypeAnalysisContext genericField
                    ? FindFieldChain(genericField, inner, size, pointerSize, depth + 1)
                    : MetadataResolver.FindFieldChain(fieldType, false, inner, size, pointerSize);

                return nested == null ? null : [concrete, ..nested];
            }

            offset += fieldSize;
        }

        return null;
    }

    private static (long Size, long Alignment)? GetSizeAndAlignment(TypeAnalysisContext fieldType, int pointerSize)
    {
        // TODO support user-defined value types
        if (fieldType is GenericParameterTypeAnalysisContext or PointerTypeAnalysisContext || !fieldType.IsValueType)
            return (pointerSize, pointerSize);

        if (fieldType.IsEnumType && fieldType.Fields.FirstOrDefault(f => !f.IsStatic) is { } underlying)
            return GetSizeAndAlignment(underlying.FieldType, pointerSize);

        return fieldType.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => (1, 1),
            "System.Int16" or "System.UInt16" or "System.Char" => (2, 2),
            "System.Int32" or "System.UInt32" or "System.Single" => (4, 4),
            "System.Int64" or "System.UInt64" or "System.Double" => (8, 8),
            "System.IntPtr" or "System.UIntPtr" => (pointerSize, pointerSize),
            _ => null // an arbitrary struct needs its own layout computed, bail rather than guess
        };
    }
}
