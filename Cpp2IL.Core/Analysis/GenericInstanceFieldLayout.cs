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
        => FindFieldChain(owner.GenericType, owner.GenericArguments, owner, targetOffset, size, pointerSize, depth);

    /// <summary>
    /// The same for an open generic type, as seen by its own (shared) code: its type parameters are references.
    /// </summary>
    public static List<FieldAnalysisContext>? FindFieldChainOpen(TypeAnalysisContext definition, long targetOffset, int size, int pointerSize)
        => FindFieldChain(definition, null, null, targetOffset, size, pointerSize, 0);

    private static List<FieldAnalysisContext>? FindFieldChain(TypeAnalysisContext definition, List<TypeAnalysisContext>? arguments, GenericInstanceTypeAnalysisContext? concreteOwner,
        long targetOffset, int size, int pointerSize, int depth)
    {
        if (depth > 6)
            return null;

        long offset;
        if (definition.IsValueType)
            offset = 0;
        else if (definition.BaseType is not { } baseType || !HasInstanceFields(baseType))
            offset = 2L * pointerSize;
        else if (BaseAsSeenBy(baseType, arguments) is { } genericBase)
        {
            // a generic base is laid out the same way, with this type's arguments substituted into it
            if (InstanceEnd(genericBase.GenericType, SizingArguments(genericBase, arguments == null), pointerSize, depth + 1) is not { } baseEnd)
                return null;

            if (targetOffset < baseEnd)
                return FindFieldChain(genericBase.GenericType, SizingArguments(genericBase, arguments == null), genericBase, targetOffset, size, pointerSize, depth + 1);

            offset = baseEnd;
        }
        else
        {
            // fields of the base class come first; a non-generic base has real offsets in the metadata
            if (baseType.GenericParameters.Count > 0 || baseType.Definition?.RawSizes is not { instance_size: var baseSize and > 0 })
                return null;

            if (targetOffset < baseSize)
                return MetadataResolver.FindFieldChain(baseType, false, targetOffset, size, pointerSize);

            offset = baseSize;
        }

        foreach (var field in definition.Fields)
        {
            if (field.IsStatic || (field.Attributes & System.Reflection.FieldAttributes.Literal) != 0)
                continue;

            // shared code sees its type parameters as references
            var sizing = arguments == null && field.FieldType is GenericParameterTypeAnalysisContext
                ? ((long)pointerSize, (long)pointerSize)
                : TypeSizes.SizeAndAlignment(field.FieldType, pointerSize, arguments, 0);
            if (sizing is not var (fieldSize, alignment))
                return null;

            offset = (offset + alignment - 1) & ~(alignment - 1);

            if (targetOffset >= offset && targetOffset < offset + fieldSize)
            {
                FieldAnalysisContext resolved = concreteOwner != null ? new ConcreteGenericFieldAnalysisContext(field, concreteOwner) : field;
                var fieldType = resolved.FieldType;
                var inner = targetOffset - offset;

                // the whole field
                if (inner == 0 && (size == 0 || size == fieldSize || !Analysis.StackStructRecovery.IsStruct(fieldType)))
                    return [resolved];

                // inside a struct field
                if (!Analysis.StackStructRecovery.IsStruct(fieldType))
                    return null;

                var nested = fieldType is GenericInstanceTypeAnalysisContext genericField
                    ? FindFieldChain(genericField, inner, size, pointerSize, depth + 1)
                    : MetadataResolver.FindFieldChain(fieldType, false, inner, size, pointerSize);

                return nested == null ? null : [resolved, ..nested];
            }

            offset += fieldSize;
        }

        return null;
    }

    // The base type of a generic definition is written in terms of the definition's own parameters
    private static GenericInstanceTypeAnalysisContext? BaseAsSeenBy(TypeAnalysisContext baseType, List<TypeAnalysisContext>? arguments)
    {
        if (baseType is not GenericInstanceTypeAnalysisContext genericBase)
            return null;

        if (arguments == null || !genericBase.GenericArguments.Any(MentionsTypeParameter))
            return genericBase;

        try
        {
            return GenericInstantiation.Instantiate(genericBase, arguments, []) as GenericInstanceTypeAnalysisContext;
        }
        catch
        {
            return null;
        }
    }

    private static bool MentionsTypeParameter(TypeAnalysisContext type) => type switch
    {
        GenericParameterTypeAnalysisContext => true,
        GenericInstanceTypeAnalysisContext instance => instance.GenericArguments.Any(MentionsTypeParameter),
        _ => false,
    };

    // shared code sees its type parameters as references, which object sizes as
    private static List<TypeAnalysisContext> SizingArguments(GenericInstanceTypeAnalysisContext instance, bool shared) =>
        shared
            ? instance.GenericArguments.Select(a => a is GenericParameterTypeAnalysisContext ? a.AppContext.SystemTypes.SystemObjectType : a).ToList()
            : instance.GenericArguments;

    /// <summary>
    /// Where the fields of a type deriving from this generic class instance start: the end of its own fields, padded to
    /// the object's alignment (il2cpp lays a derived class out as a C++ struct deriving from the base's).
    /// </summary>
    public static long? InstanceEnd(GenericInstanceTypeAnalysisContext instance, int pointerSize)
        => InstanceEnd(instance.GenericType, instance.GenericArguments, pointerSize, 0);

    private static long? InstanceEnd(TypeAnalysisContext definition, List<TypeAnalysisContext> arguments, int pointerSize, int depth)
    {
        if (depth > 6 || definition.IsValueType)
            return null;

        long offset;
        if (definition.BaseType is not { } baseType || !HasInstanceFields(baseType))
            offset = 2L * pointerSize;
        else if (BaseAsSeenBy(baseType, arguments) is { } genericBase)
        {
            if (InstanceEnd(genericBase.GenericType, genericBase.GenericArguments, pointerSize, depth + 1) is not { } baseEnd)
                return null;
            offset = baseEnd;
        }
        else if (baseType.GenericParameters.Count == 0 && baseType.Definition?.RawSizes is { instance_size: var baseSize and > 0 })
            offset = baseSize;
        else
            return null;

        long alignment = pointerSize;
        foreach (var field in definition.Fields)
        {
            if (field.IsStatic || (field.Attributes & System.Reflection.FieldAttributes.Literal) != 0)
                continue;

            if (TypeSizes.SizeAndAlignment(field.FieldType, pointerSize, arguments, 0) is not var (fieldSize, fieldAlignment))
                return null;

            offset = (offset + fieldAlignment - 1) & ~(fieldAlignment - 1);
            offset += fieldSize;
            alignment = System.Math.Max(alignment, fieldAlignment);
        }

        return (offset + alignment - 1) & ~(alignment - 1);
    }

    private static bool HasInstanceFields(TypeAnalysisContext type)
    {
        for (var current = type; current != null; current = current.BaseType)
            if (current.Fields.Any(f => !f.IsStatic))
                return true;
        return false;
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
