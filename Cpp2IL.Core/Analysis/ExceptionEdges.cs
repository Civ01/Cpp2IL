using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Links the code in each try block to the catch funclets lifted onto the end of the method, so that the catch code, and
/// the continuation in the method it goes on to, are reachable and see the values the try block left.
///
/// An IL2CPP exception is always a C++ throw out of a call (null checks, bounds checks and the like call a raise helper),
/// so the edges go from the calls made in the try block's states. A call in a catch funclet is in the states of its
/// catch, which a try block around the whole try/catch covers.
/// </summary>
public static class ExceptionEdges
{
    public static void Run(MethodAnalysisContext method)
    {
        if (method is not { CatchHandlers: { Count: > 0 } handlers, ExceptionInfo: { } info, ControlFlowGraph: { } cfg })
            return;

        var entries = new List<(CatchHandler Handler, Block Entry)>();
        // a finally's catch-all isn't linked yet: MSVC gives each path its own copy of the finally code, so the only effect
        // here would be the copy on the exception path (which rethrows) joining the method's, until the finally is emitted as one
        foreach (var handler in handlers.Where(h => !h.IsFinally))
        {
            var entry = cfg.BlockStartingAt(handler.Entry);
            if (entry == null)
                continue;

            entry.IsCatchEntry = true;
            entries.Add((handler, entry));
        }

        foreach (var block in cfg.Blocks.ToList())
        {
            var call = block.Instructions.LastOrDefault(i => i.OpCode is OpCode.Call or OpCode.CallVoid or OpCode.IndirectCall && CanThrow(method, i));
            if (call == null)
                continue;

            var funclet = handlers.FirstOrDefault(h => h.Instructions.Contains(call));
            var state = funclet != null ? funclet.TryBlock.CatchHigh : info.StateAt(call.Address);
            if (state < 0)
                continue;

            foreach (var (handler, entry) in entries)
            {
                if (handler == funclet || !handler.TryBlock.Covers(state) || block.Successors.Contains(entry))
                    continue;

                cfg.AddDirectedEdge(block, entry);
            }
        }
    }

    /// <summary>
    /// Takes the catch funclets, and the code only they lead to, out again once the analysis is done. Nothing in the IL
    /// branches to a catch until it is emitted as a handler region, so all it would leave behind are the values the
    /// method keeps for it (MSVC's copies of locals in the frame, for the catch to read).
    /// </summary>
    public static void DetachForIl(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } cfg || !cfg.Blocks.Any(b => b.IsCatchEntry))
            return;

        foreach (var entry in cfg.Blocks.Where(b => b.IsCatchEntry).ToList())
            foreach (var predecessor in entry.Predecessors.ToList())
                ISILControlFlowGraph.RemoveEdge(predecessor, entry);

        cfg.RemoveUnreachableBlocks();
    }

    /// <summary>
    /// Whether the call may raise a managed exception, as far as it matters: the runtime's init and write barrier
    /// boilerplate and the C runtime's helpers are left out, so that the passes taking that boilerplate out find it in one piece.
    /// </summary>
    private static bool CanThrow(MethodAnalysisContext method, Instruction call)
    {
        if (call.OpCode == OpCode.IndirectCall || call.Operands.Count == 0 || call.Operands[0] is not Immediate { UnsignedValue: var target })
            return true;

        var app = method.AppContext;
        if (IsBoilerplate(app, target))
            return false;

        // boilerplate is often reached through a jmp thunk
        var thunked = app.InstructionSet.GetThunkTarget(app, target);
        return thunked == 0 || !IsBoilerplate(app, thunked);
    }

    private static bool IsBoilerplate(ApplicationAnalysisContext app, ulong target)
    {
        var keys = app.GetOrCreateKeyFunctionAddresses();
        if (target == keys.il2cpp_codegen_initialize_method || target == keys.il2cpp_codegen_initialize_runtime_metadata
            || target == keys.il2cpp_codegen_initialize_runtime_metadata_inline || target == keys.il2cpp_vm_metadatacache_initializemethodmetadata
            || target == keys.il2cpp_runtime_class_init_export || target == keys.il2cpp_runtime_class_init_actual
            || target == keys.il2cpp_codegen_runtime_class_init || target == keys.il2cpp_codegen_write_barrier)
            return true;

        return NativeHelpers.Classify(app, target) is NativeHelperKind.Empty or NativeHelperKind.StackProbe or NativeHelperKind.Memset
            or NativeHelperKind.Memcpy or NativeHelperKind.IsInst or NativeHelperKind.ReturnsFirstArgument or NativeHelperKind.FieldAddress;
    }
}
