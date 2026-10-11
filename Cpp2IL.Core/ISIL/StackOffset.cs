namespace Cpp2IL.Core.ISIL;

public struct StackOffset(int offset, int size = 0) : IOperand, System.IEquatable<StackOffset>
{
    public int Offset = offset;

    /// <summary>
    /// Width of the access in bytes, or 0 if unknown. Not part of equality.
    /// </summary>
    public int Size = size;

    public bool Equals(StackOffset other) => Offset == other.Offset;

    public override bool Equals(object? obj) => obj is StackOffset other && Equals(other);

    public override int GetHashCode() => Offset;

    public override string ToString() => $"stack[{(Offset < 0 ? ("-" + (-Offset).ToString("X")) : Offset.ToString("X"))}]" + (Size > 0 ? $":{Size}" : "");
}
