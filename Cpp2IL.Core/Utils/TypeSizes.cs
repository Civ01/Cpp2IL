using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

public static class TypeSizes
{
    // Unboxed size of a value type, so the metadata's boxed size - the two pointer fields in the header. 0 if we
    // don't know (no definition, e.g. an open generic).
    public static long UnboxedSize(TypeAnalysisContext type, int pointerSize)
    {
        var header = 2L * pointerSize;

        if (type.Definition?.RawSizes is { instance_size: var boxed } && boxed > header)
            return boxed - header;

        // a generic struct instance (List<T>.Enumerator) has no sizes in the metadata: lay it out ourselves
        if (type is GenericInstanceTypeAnalysisContext { IsValueType: true } && SizeAndAlignment(type, pointerSize, null, 0) is var (size, _))
            return size;

        return 0;
    }

    /// <summary>
    /// Size and alignment of a value of the type as stored in a field, laying out generic struct instances sequentially
    /// with their type arguments substituted. Null if unknown.
    /// </summary>
    public static (long Size, long Alignment)? SizeAndAlignment(TypeAnalysisContext type, int pointerSize, List<TypeAnalysisContext>? typeArguments, int depth)
    {
        if (depth > 8)
            return null;

        switch (type)
        {
            case GenericParameterTypeAnalysisContext parameter:
                return parameter.Type == LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR && typeArguments != null && parameter.Index < typeArguments.Count
                    ? SizeAndAlignment(typeArguments[parameter.Index], pointerSize, null, depth + 1)
                    : null;
            case ByRefTypeAnalysisContext or PointerTypeAnalysisContext:
                return (pointerSize, pointerSize);
            case GenericInstanceTypeAnalysisContext instance when typeArguments != null && instance.GenericArguments.Any(a => a is GenericParameterTypeAnalysisContext):
                // a field of type Foo<T> inside Bar<T>: substitute first
                var substituted = instance.GenericArguments.Select(a => a is GenericParameterTypeAnalysisContext { Type: LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR } p && p.Index < typeArguments.Count ? typeArguments[p.Index] : a).ToList();
                return SizeAndAlignment(new GenericInstanceTypeAnalysisContext(instance.GenericType, substituted), pointerSize, null, depth + 1);
        }

        if (!type.IsValueType)
            return (pointerSize, pointerSize);

        if (type.IsEnumType)
            return type.Fields.FirstOrDefault(f => !f.IsStatic) is { } underlying ? SizeAndAlignment(underlying.FieldType, pointerSize, null, depth + 1) : (4, 4);

        if (type.Namespace == "System")
        {
            switch (type.Name)
            {
                case "Boolean" or "Byte" or "SByte":
                    return (1, 1);
                case "Int16" or "UInt16" or "Char":
                    return (2, 2);
                case "Int32" or "UInt32" or "Single":
                    return (4, 4);
                case "Int64" or "UInt64" or "Double":
                    return (8, 8);
                case "IntPtr" or "UIntPtr":
                    return (pointerSize, pointerSize);
            }
        }

        var definition = type is GenericInstanceTypeAnalysisContext generic ? generic.GenericType : type;
        var arguments = type is GenericInstanceTypeAnalysisContext withArguments ? withArguments.GenericArguments : null;

        // a non-generic struct's size is in the metadata; its alignment is its widest field's
        long offset = 0, alignment = 1;
        foreach (var field in definition.Fields)
        {
            if (field.IsStatic || (field.Attributes & System.Reflection.FieldAttributes.Literal) != 0)
                continue;

            if (SizeAndAlignment(field.FieldType, pointerSize, arguments, depth + 1) is not var (fieldSize, fieldAlignment))
                return null;

            offset = (offset + fieldAlignment - 1) & ~(fieldAlignment - 1);
            offset += fieldSize;
            alignment = Math.Max(alignment, fieldAlignment);
        }

        if (arguments == null && type.Definition?.RawSizes is { instance_size: var boxed } && boxed > 2L * pointerSize)
            return (boxed - 2L * pointerSize, alignment);

        if (offset == 0)
            return null;

        return ((offset + alignment - 1) & ~(alignment - 1), alignment);
    }

    /// <summary>
    /// Size in bytes a value of this type occupies when stored in a field or local, or 0 if unknown.
    /// </summary>
    public static long StorageSize(TypeAnalysisContext type, int pointerSize)
    {
        if (type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext)
            return pointerSize;

        if (type is GenericParameterTypeAnalysisContext)
            return 0;

        if (!type.IsValueType)
            return pointerSize;

        if (type.IsEnumType)
        {
            foreach (var field in type.Fields)
                if (!field.IsStatic)
                    return StorageSize(field.FieldType, pointerSize);

            return 4;
        }

        if (type.Namespace == "System")
        {
            switch (type.Name)
            {
                case "Boolean" or "Byte" or "SByte":
                    return 1;
                case "Int16" or "UInt16" or "Char":
                    return 2;
                case "Int32" or "UInt32" or "Single":
                    return 4;
                case "Int64" or "UInt64" or "Double":
                    return 8;
                case "IntPtr" or "UIntPtr":
                    return pointerSize;
            }
        }

        return UnboxedSize(type, pointerSize);
    }
}
