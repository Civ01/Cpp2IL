using System;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Model.Contexts;
using Iced.Intel;

namespace Cpp2IL.Core.Utils;

public enum NativeHelperKind
{
    Unknown,

    /// <summary>Just returns. Calling it does nothing (often many identical empty managed methods folded together).</summary>
    Empty,

    /// <summary>__chkstk, which probes the stack for big frames and changes nothing else.</summary>
    StackProbe,

    /// <summary>The C runtime's memset(dest, value, count).</summary>
    Memset,

    /// <summary>The C runtime's memcpy/memmove(dest, source, count).</summary>
    Memcpy,

    /// <summary>il2cpp's IsInst(object, klass): the object if it's an instance of klass, otherwise null. The isinst opcode.</summary>
    IsInst,

    /// <summary>Raises an InvalidCastException for casting the object to klass. The failure path of castclass.</summary>
    RaiseInvalidCast,

    /// <summary>
    /// An interface method invoker: (slot, declaringInterface, obj, args...) - looks the method up in obj's class and
    /// tail-calls it with (obj, args..., methodInfo).
    /// </summary>
    InterfaceInvoker,
}

/// <summary>
/// Recognises the small set of native (C runtime and il2cpp codegen) helpers that managed code calls directly,
/// by the shape of their machine code. x86-64 (MSVC) only.
/// </summary>
public static class NativeHelpers
{
    public static NativeHelperKind Classify(ApplicationAnalysisContext app, ulong address)
    {
        if (address == 0 || app.Binary.PointerSizeBytes != 8 || app.InstructionSet is not InstructionSets.X86InstructionSet)
            return NativeHelperKind.Unknown;

        return app.NativeHelperKindsByAddress.GetOrAdd(address, a =>
        {
            try
            {
                return ClassifyUncached(app, a);
            }
            catch
            {
                return NativeHelperKind.Unknown;
            }
        });
    }

    private static NativeHelperKind ClassifyUncached(ApplicationAnalysisContext app, ulong address)
    {
        var body = X86Utils.GetMethodBodyAtVirtAddressNew(address, true, app, 128);
        if (body.Count == 0)
            return NativeHelperKind.Unknown;

        var first = body[0];

        if (first.Mnemonic == Mnemonic.Ret || first.Mnemonic is Mnemonic.Nop or Mnemonic.Xchg && body.Count > 1 && body[1].Mnemonic == Mnemonic.Ret)
            return NativeHelperKind.Empty;

        // Everything else is never a managed method
        if (app.MethodsByAddress.ContainsKey(address))
            return NativeHelperKind.Unknown;

        // A write barrier variant taking the field address in rdx (mov rcx,rdx / jmp the barrier's target): no effect
        // on what the code means
        if (body.Count >= 2 && first is { Mnemonic: Mnemonic.Mov, Op0Register: Register.RCX, Op1Register: Register.RDX }
            && body[1] is { Mnemonic: Mnemonic.Jmp, Op0Kind: OpKind.NearBranch64 } barrierJump
            && WriteBarrierTarget(app) is { } barrierTarget && barrierJump.NearBranchTarget == barrierTarget)
            return NativeHelperKind.Empty;

        if (body.Count >= 3
            && first is { Mnemonic: Mnemonic.Sub, Op0Register: Register.RSP, Op1Kind: OpKind.Immediate8to64 or OpKind.Immediate32to64 or OpKind.Immediate8 }
            && body[1] is { Mnemonic: Mnemonic.Mov, Op0Kind: OpKind.Memory, MemoryBase: Register.RSP, Op1Register: Register.R10 }
            && body[2] is { Mnemonic: Mnemonic.Mov, Op0Kind: OpKind.Memory, MemoryBase: Register.RSP, Op1Register: Register.R11 })
            return NativeHelperKind.StackProbe;

        if (body.Take(10).Any(i => i.Mnemonic == Mnemonic.Mov && i.Op1Kind == OpKind.Immediate64 && i.Immediate64 == 0x0101010101010101UL))
            return NativeHelperKind.Memset;

        // mov rax,rcx / lea r10,[__ImageBase] / cmp r8,0Fh - the CRT memcpy/memmove dispatching on size
        if (body.Count >= 3
            && first is { Mnemonic: Mnemonic.Mov, Op0Register: Register.RAX, Op1Register: Register.RCX }
            && body.Take(4).Any(i => i is { Mnemonic: Mnemonic.Cmp, Op0Register: Register.R8, Op1Kind: OpKind.Immediate8to64 or OpKind.Immediate32to64 }))
            return NativeHelperKind.Memcpy;

        // A thunk to vm::Object::IsInst, which null-checks the object then reads its klass
        if (first.Mnemonic == Mnemonic.Jmp && first.Op0Kind is OpKind.NearBranch64 && LooksLikeIsInst(app, first.NearBranchTarget))
            return NativeHelperKind.IsInst;

        // Interface invokers scan klass->interfaceOffsets (count at 0x12E) and finish with a register tail-jump
        if (body.Take(16).Any(i => i is { Mnemonic: Mnemonic.Movzx, Op1Kind: OpKind.Memory, MemoryDisplacement64: 0x12E, MemorySize: MemorySize.UInt16 })
            && body.Take(8).Any(i => i is { Mnemonic: Mnemonic.Movzx, Op1Kind: OpKind.Register, Op1Register: Register.CX })
            && body.Any(i => i is { Mnemonic: Mnemonic.Jmp, Op0Kind: OpKind.Register }))
            return NativeHelperKind.InterfaceInvoker;

        // RaiseInvalidCastException(obj, klass): reads the object's klass for the message, then raises
        if (body.Take(4).Any(i => i is { Mnemonic: Mnemonic.Mov, Op0Register: Register.RDX, Op1Kind: OpKind.Memory, MemoryBase: Register.RCX, MemoryDisplacement64: 0 })
            && !body.Any(i => i.Mnemonic == Mnemonic.Ret)
            && body.LastOrDefault(i => i.Mnemonic == Mnemonic.Call) is { Op0Kind: OpKind.NearBranch64 } raise
            && ThrowHelperRecovery.IsExceptionRaiser(app, raise.NearBranchTarget))
            return NativeHelperKind.RaiseInvalidCast;

        return NativeHelperKind.Unknown;
    }

    private static ulong? WriteBarrierTarget(ApplicationAnalysisContext app)
    {
        var barrier = app.GetOrCreateKeyFunctionAddresses().il2cpp_codegen_write_barrier;
        if (barrier == 0)
            return null;

        var body = X86Utils.GetMethodBodyAtVirtAddressNew(barrier, true, app, 4);
        return body is [{ Mnemonic: Mnemonic.Jmp, Op0Kind: OpKind.NearBranch64 } jump, ..] ? jump.NearBranchTarget : barrier;
    }

    /// <summary>
    /// Whether a native function can't return (it has no ret, e.g. it always raises an exception).
    /// </summary>
    public static bool NeverReturns(ApplicationAnalysisContext app, ulong address)
    {
        if (address == 0 || app.InstructionSet is not InstructionSets.X86InstructionSet)
            return false;

        return app.NoReturnByAddress.GetOrAdd(address, a =>
        {
            try
            {
                var body = X86Utils.GetMethodBodyAtVirtAddressNew(a, false, app);
                return body.Count > 0 && !body.Any(i => i.Mnemonic == Mnemonic.Ret) && body.Any(i => i.Mnemonic is Mnemonic.Call or Mnemonic.Jmp);
            }
            catch
            {
                return false;
            }
        });
    }

    private static bool LooksLikeIsInst(ApplicationAnalysisContext app, ulong address)
    {
        if (app.MethodsByAddress.ContainsKey(address))
            return false;

        var body = X86Utils.GetMethodBodyAtVirtAddressNew(address, true, app, 96);
        var start = body.Take(12).ToList();

        var nullCheck = start.FindIndex(i => i is { Mnemonic: Mnemonic.Test, Op0Register: Register.RCX, Op1Register: Register.RCX });
        if (nullCheck < 0 || nullCheck + 1 >= start.Count || start[nullCheck + 1].Mnemonic != Mnemonic.Je)
            return false;

        // the klass load, from the object pointer
        return start.Skip(nullCheck + 2).Any(i => i is { Mnemonic: Mnemonic.Mov, Op1Kind: OpKind.Memory, MemoryBase: Register.RCX, MemoryDisplacement64: 0, MemoryIndex: Register.None })
               && start.Skip(nullCheck + 2).Any(i => i.Mnemonic == Mnemonic.Call);
    }
}
