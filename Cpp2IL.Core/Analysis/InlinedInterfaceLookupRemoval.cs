using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// il2cpp inlines the lookup of an interface method's vtable slot:
/// <code>
///   movzx edx,word ptr [klass+12Eh]   ; interface_offsets_count
///   cmp si,dx / jae slow
///   mov r8,[klass+0B0h]               ; interfaceOffsets
/// scan: cmp [r8+rax*8],iface / je found / inc cx / ... jb scan
/// slow: GetInterfaceInvokeDataFromVTableSlowPath(obj, iface, slot) / call [rax]
/// found: call klass->vtable[offset + slot]
/// </code>
/// and MSVC usually duplicates the call itself into both paths, so there's no merge to find. Both paths call the same
/// method, so this sends the lookup straight to the slow path, which names the interface and slot as plain arguments
/// (InterfaceDispatchRecovery then turns it into the call), and drops the scan. Runs on ISIL registers, before SSA.
/// </summary>
public static class InlinedInterfaceLookupRemoval
{
    private const long InterfaceOffsetsCountOffset = 0x12E;
    private const long InterfaceOffsetsOffset = 0xB0;

    public static void Run(MethodAnalysisContext method, ISILControlFlowGraph graph)
    {
        if (method.AppContext.Binary.PointerSizeBytes != 8 || method.AppContext.InstructionSet is not InstructionSets.X86InstructionSet)
            return;

        var changed = false;

        foreach (var head in graph.Blocks.ToList())
        {
            if (head.Instructions.Count < 2 || head.Instructions[^1] is not { OpCode: OpCode.ConditionalJump, Operands: [Block taken, ..] } branch)
                continue;

            var countLoad = head.Instructions.FirstOrDefault(i => i is
                { OpCode: OpCode.Move, Operands: [Register, MemoryOperand { Base: Register, Index: null, Addend: InterfaceOffsetsCountOffset }] });
            if (countLoad == null)
                continue;

            var klass = (Register)((MemoryOperand)countLoad.Operands[1]).Base!;
            var successors = head.Successors.Distinct().ToList();
            if (successors.Count != 2 || !successors.Contains(taken))
                continue;

            var other = successors.First(s => s != taken);

            Block? scan = null, slow = null;
            if (LoadsInterfaceOffsets(other, klass))
                (scan, slow) = (other, taken);
            else if (LoadsInterfaceOffsets(taken, klass))
                (scan, slow) = (taken, other);

            if (scan == null || slow == null || !CallsSoon(slow))
                continue;

            branch.OpCode = OpCode.Jump;
            branch.SetOperands(slow);

            head.Successors.Clear();
            head.Successors.Add(slow);
            scan.Predecessors.RemoveAll(p => p == head);
            head.CalculateBlockType();
            changed = true;
        }

        if (changed)
            graph.RemoveUnreachableBlocks();
    }

    private static bool LoadsInterfaceOffsets(Block block, Register klass) =>
        block.Instructions.Take(3).Any(i => i is { OpCode: OpCode.Move, Operands: [Register, MemoryOperand { Base: Register @base, Index: null, Addend: InterfaceOffsetsOffset }] }
                                            && @base.Name == klass.Name);

    private static bool CallsSoon(Block block)
    {
        foreach (var instruction in block.Instructions.Take(8))
        {
            if (instruction.OpCode is OpCode.Call or OpCode.CallVoid)
                return true;
            if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump or OpCode.Return or OpCode.IndirectCall or OpCode.IndirectJump)
                return false;
        }

        return false;
    }
}
