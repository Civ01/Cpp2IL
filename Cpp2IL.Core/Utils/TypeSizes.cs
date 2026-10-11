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

        return 0;
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
