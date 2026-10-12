using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Compilers sometimes read a 4 byte field as the upper half of an 8 byte load (mov rax,[rcx+8] / shr rax,20h for the
/// int at +0xC). This turns <c>t = [b+o]:8; d = t >> 32</c> into <c>d = [b+o+4]:4</c> so the field resolves. Runs in
/// SSA form, before types and fields are resolved.
/// </summary>
public static class WideLoadSplitter
{
    public static void Run(MethodAnalysisContext method)
    {
        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable defined)
                definitions[defined] = instruction;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            // movups xmm1,[rbp+10h] / movq rax,xmm1 - the low part of a vector load, moved into a general register, is
            // the field at its start
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable { Register.Name: var target }, LocalVariable vector] }
                && !target.StartsWith("xmm") && vector.Register.Name.StartsWith("xmm")
                && definitions.TryGetValue(vector, out var vectorLoad)
                && vectorLoad is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Size: >= 8 } vectorSource] })
            {
                instruction.SetOperand(1, new MemoryOperand(vectorSource.Base, null, vectorSource.Addend, 0, 0));
                continue;
            }

            if (instruction is not { OpCode: OpCode.ShiftRight, Operands: [LocalVariable, LocalVariable shifted, Immediate { Value: 32 }] })
                continue;

            if (!definitions.TryGetValue(shifted, out var load)
                || load is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Size: 8 } wide] })
                continue;

            instruction.OpCode = OpCode.Move;
            instruction.SetOperands(instruction.Operands[0], new MemoryOperand(wide.Base, null, wide.Addend + 4, 0, 4));
        }
    }
}
