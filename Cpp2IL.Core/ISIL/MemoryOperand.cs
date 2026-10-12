using System;
using System.Text;

namespace Cpp2IL.Core.ISIL;

/// <summary>
/// Memory operand in the format of [base+addend+index*scale]
/// </summary>
public struct MemoryOperand(IOperand? baseRegister = null, IOperand? indexRegister = null, long addend = 0, int scale = 0, int size = 0) : IOperand, IEquatable<MemoryOperand>
{
    public IOperand? Base = baseRegister;
    public IOperand? Index = indexRegister;
    public long Addend = addend;
    public int Scale = scale;

    /// <summary>
    /// Width of the access in bytes, or 0 if unknown. Deliberately not part of equality, so the same
    /// location accessed at different widths is still the same location.
    /// </summary>
    public int Size = size;

    public bool Equals(MemoryOperand other) => Equals(Base, other.Base) && Equals(Index, other.Index) && Addend == other.Addend && Scale == other.Scale;

    public override bool Equals(object? obj) => obj is MemoryOperand other && Equals(other);

    public override int GetHashCode() => HashCode.Combine(Base, Index, Addend, Scale);

    public bool IsConstant => Base == null && Index == null && Scale == 0;

    public override string ToString()
    {
        var sb = new StringBuilder("[");
        var needsPlus = false;

        if (Base != null)
        {
            sb.Append(Base);
            needsPlus = true;
        }

        if (Addend != 0)
        {
            if (needsPlus || Addend < 0)
                sb.Append(Addend > 0 ? '+' : '-');
            sb.Append($"{Math.Abs(Addend):X}");
            needsPlus = true;
        }

        if (Index != null)
        {
            if (needsPlus)
                sb.Append('+');
            sb.Append(Index);

            if (Scale > 1)
            {
                sb.Append('*');
                sb.Append(Scale);
            }
        }

        sb.Append(']');

        if (Size > 0)
            sb.Append(':').Append(Size);

        return sb.ToString();
    }
}
