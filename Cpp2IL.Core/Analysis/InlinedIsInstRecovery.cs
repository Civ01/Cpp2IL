using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// il2cpp inlines isinst/castclass against a non-sealed class as a walk of the object's class hierarchy:
/// <code>
///   mov r9,[obj]                      ; klass
///   movzx eax,byte ptr [T+130h]       ; T->typeHierarchyDepth
///   cmp [r9+130h],al  /  jb fail      ; klass->typeHierarchyDepth &lt; it: not a T
///   movzx ecx,al
///   mov rax,[r9+0C8h]                 ; klass->typeHierarchy
///   cmp [rax+rcx*8-8],r8  /  je ok    ; typeHierarchy[depth - 1] == T
/// </code>
/// This pass turns the hierarchy comparison into an <see cref="OpCode.IsInst"/> null test, and makes the depth
/// comparison (which the isinst subsumes) always pass, so the class structure reads disappear and the condition
/// reads as a type test. Runs on ISIL registers before SSA.
/// </summary>
public static class InlinedIsInstRecovery
{
    // 64-bit Il2CppClass layout (Unity 2021+)
    private const long TypeHierarchyDepthOffset = 0x130;
    private const long TypeHierarchyOffset = 0xC8;

    public static void Run(MethodAnalysisContext method, ISILControlFlowGraph graph)
    {
        if (method.AppContext.Binary.PointerSizeBytes != 8 || method.AppContext.InstructionSet is not InstructionSets.X86InstructionSet)
            return;

        var temporaryCounter = 0;

        foreach (var block in graph.Blocks)
        {
            for (var i = 0; i + 1 < block.Instructions.Count; i++)
            {
                // A compare cluster starts: CheckLess CF, a, b / Subtract TEMP1, a, b
                if (block.Instructions[i] is not { OpCode: OpCode.CheckLess, Operands: [Register { Name: "CF" }, var left, var right] }
                    || block.Instructions[i + 1] is not { OpCode: OpCode.Subtract, Operands: [Register { Name: "TEMP1" }, var subtractLeft, var subtractRight] }
                    || !subtractLeft.Equals(left) || !subtractRight.Equals(right))
                    continue;

                // the hierarchy check: [hierarchy + depth*8 - 8] == T
                if (left is MemoryOperand { Base: Register hierarchy, Index: Register, Scale: 8, Addend: -8 }
                    && right is Register targetClass
                    && Trace(graph, block, i, hierarchy.Name) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: Register klassRegister, Index: null, Addend: TypeHierarchyOffset }] } hierarchyLoad
                    && Trace(graph, block, i, klassRegister.Name) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: Register objectRegister, Index: null, Addend: 0 }] } klassLoad
                    && !RedefinedBetween(graph, klassLoad, block, i, objectRegister.Name)
                    && !RedefinedBetween(graph, klassLoad, block, i, targetClass.Name))
                {
                    var instance = new Register(null, $"ISINST_{temporaryCounter}");
                    var notInstance = new Register(null, $"ISINST_NULL_{temporaryCounter}");
                    temporaryCounter++;

                    ReplaceInCluster(block, i, left, right, notInstance, new Immediate(0));
                    block.Instructions.Insert(i, new Instruction(block.Instructions[i].Index, OpCode.CheckEqual, notInstance, instance, new Immediate(0)));
                    block.Instructions.Insert(i, new Instruction(block.Instructions[i].Index, OpCode.IsInst, instance, targetClass, objectRegister));
                    i += 2;
                    continue;
                }

                // the depth check: klass->typeHierarchyDepth vs T->typeHierarchyDepth. The hierarchy check does the job.
                if (left is MemoryOperand { Base: Register, Index: null, Addend: TypeHierarchyDepthOffset, Size: 1 }
                    && right is Register depth
                    && Trace(graph, block, i, depth.Name) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: Register, Index: null, Addend: TypeHierarchyDepthOffset, Size: 1 }] })
                {
                    ReplaceInCluster(block, i, left, right, new Immediate(1), new Immediate(0));
                }
            }
        }
    }

    // Substitutes the compared operands throughout the flag computation the lifter emitted for one cmp
    private static void ReplaceInCluster(Block block, int start, IOperand left, IOperand right, IOperand newLeft, IOperand newRight)
    {
        for (var j = start; j < block.Instructions.Count && j < start + 10; j++)
        {
            var instruction = block.Instructions[j];
            for (var k = 1; k < instruction.Operands.Count; k++)
            {
                if (instruction.Operands[k].Equals(left))
                    instruction.SetOperand(k, newLeft);
                else if (instruction.Operands[k].Equals(right))
                    instruction.SetOperand(k, newRight);
            }
        }
    }

    // The last write to a register before the given point, in this block or back through single predecessors
    private static Instruction? Trace(ISILControlFlowGraph graph, Block block, int before, string register)
    {
        for (var depth = 0; depth < 4; depth++)
        {
            for (var i = before - 1; i >= 0; i--)
                if (block.Instructions[i].Destination is Register written && written.Name == register)
                    return block.Instructions[i];

            var predecessors = block.Predecessors.Distinct().ToList();
            if (predecessors is not [{ } only] || only == block)
                return null;

            block = only;
            before = block.Instructions.Count;
        }

        return null;
    }

    // Whether the register is written anywhere on the (single-predecessor) path from 'from' up to the point
    private static bool RedefinedBetween(ISILControlFlowGraph graph, Instruction from, Block block, int before, string register)
    {
        for (var depth = 0; depth < 4; depth++)
        {
            for (var i = before - 1; i >= 0; i--)
            {
                var instruction = block.Instructions[i];
                if (ReferenceEquals(instruction, from))
                    return false;

                if (instruction.Destination is Register written && written.Name == register)
                    return true;
            }

            var predecessors = block.Predecessors.Distinct().ToList();
            if (predecessors is not [{ } only] || only == block)
                return true;

            block = only;
            before = block.Instructions.Count;
        }

        return true;
    }
}
