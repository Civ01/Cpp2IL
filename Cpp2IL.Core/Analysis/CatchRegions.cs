using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>A try/catch to emit: the blocks of the try, the blocks of the catch, and what it catches into which local.</summary>
public sealed class CatchRegion
{
    public required Block TryEntry;
    public required HashSet<Block> Try;
    public required Block HandlerEntry;
    public required HashSet<Block> Handler;
    public required TypeAnalysisContext CatchType;
    public LocalVariable? Exception;

    public IEnumerable<Block> Blocks => Try.Concat(Handler);
}

/// <summary>
/// Turns the catch funclets linked into the method into try/catch regions for the IL, once the block layout is final.
///
/// The catch is everything its entry dominates: nothing else leads into it but the calls that throw to it. The try is
/// worked out from those calls rather than from the EH states, as MSVC gives code that can't throw whatever state is
/// convenient: it starts at the nearest block dominating all of them, and takes in every block from there that leads to one
/// of them. That is entered only through its start, and code after the last call that can throw is left after the try,
/// which changes nothing as it can't throw.
///
/// Regions have to nest in the IL, so a try reaching into an inner try/catch takes all of it, and a foreach that doesn't fit
/// goes back to a plain loop. What still doesn't fit is detached again, as before there were regions.
/// </summary>
public static class CatchRegions
{
    public static void Build(MethodAnalysisContext method)
    {
        method.CatchRegions = null;
        if (method.ControlFlowGraph is not { } cfg || !cfg.Blocks.Any(b => b.IsCatchEntry))
            return;

        // a branch folded into a jump leaves its other way behind (a catch's rethrow when its type test always holds)
        foreach (var block in cfg.Blocks)
            if (block.Instructions.Count > 0 && block.Instructions[^1] is { OpCode: OpCode.Jump, Operands: [Block target] })
                foreach (var stale in block.NormalSuccessors.Where(s => s != target).ToList())
                    ISILControlFlowGraph.RemoveEdge(block, stale);

        // a block that only jumps on would come between a try and what leads into it
        foreach (var block in cfg.Blocks)
            if (block.Instructions.Count > 0 && block.Instructions.All(i => i.OpCode is OpCode.Nop or OpCode.Jump) && block.NormalSuccessors.Count == 1 && !block.IsCatchEntry)
                block.Instructions.Clear();
        cfg.RemoveEmptyBlocks();

        cfg.RemoveUnreachableBlocks();
        (Block? Prologue, HashSet<Block> Tails)? async = IsAsyncMoveNext(method) ? ShapeAsync(cfg) : null;
        var dominators = new DominatorInfo(cfg);
        var handlers = method.CatchHandlers ?? [];
        var regions = new List<CatchRegion>();
        var failed = new List<Block>();

        foreach (var entry in cfg.Blocks.Where(b => b.IsCatchEntry).ToList())
        {
            if (Find(method, cfg, dominators, entry, handlers) is { } region)
                regions.Add(region);
            else
                failed.Add(entry);
        }

        // an async MoveNext is one try around the whole body, between the loads of its fields and the SetResult()
        if (async is var (prologue, tails) && regions.FirstOrDefault(r => r.Handler.SelectMany(b => b.Instructions).Any(i => CallsMethod(i, "SetException"))) is { } main
            && (prologue == null ? cfg.EntryBlock.NormalSuccessors.FirstOrDefault() : prologue.NormalSuccessors is [var afterPrologue] ? afterPrologue : null) is { } bodyStart
            && !main.Handler.Contains(bodyStart))
        {
            main.TryEntry = bodyStart;
            main.Try = cfg.Blocks.Where(b => b != cfg.EntryBlock && b != cfg.ExitBlock && b != prologue && !tails.Contains(b) && !main.Handler.Contains(b) && !Returns(b)).ToHashSet();
        }

        // nest: a try that has part of another try/catch in it takes all of it
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var outer in regions)
            foreach (var inner in regions)
            {
                // (the other way round when the outer's catch is inside the inner; a try can start where another does)
                if (inner == outer || !inner.Blocks.Any(outer.Try.Contains) || inner.Blocks.All(outer.Try.Contains) || inner.Blocks.Contains(outer.HandlerEntry))
                    continue;

                var missing = inner.Blocks.Where(b => !outer.Try.Contains(b)).ToList();
                if (missing.Any(b => outer.Handler.Contains(b) || !dominators.Dominates(outer.TryEntry, b)))
                    continue;

                outer.Try.UnionWith(missing);
                changed = true;
            }
        }

        // what still doesn't nest, or isn't entered only at its start, goes
        foreach (var region in regions.OrderByDescending(r => r.Try.Count + r.Handler.Count).ToList())
        {
            if (Entered(region.Try, region.TryEntry) && Entered(region.Handler, region.HandlerEntry)
                && regions.All(other => other == region || Nests(region, other)))
                continue;

            regions.Remove(region);
            failed.Add(region.HandlerEntry);
        }

        if (failed.Count > 0)
        {
            foreach (var entry in failed)
                foreach (var predecessor in entry.Predecessors.ToList())
                    ISILControlFlowGraph.RemoveEdge(predecessor, entry);

            cfg.RemoveUnreachableBlocks();
            DeadCodeEliminator.Run(cfg);
            LocalVariables.RemoveUnused(method);
            regions.RemoveAll(r => !cfg.Blocks.Contains(r.HandlerEntry));

            // (a try that took in a catch that went loses its blocks too)
            var remaining = cfg.Blocks.ToHashSet();
            foreach (var region in regions)
            {
                region.Try.IntersectWith(remaining);
                region.Handler.IntersectWith(remaining);
            }
        }

        // a foreach is a region of its own (try/finally), so it has to fit in a part of a try/catch as well
        if (method.ForeachRegions is { } loops)
        {
            loops.RemoveAll(loop =>
            {
                var blocks = loop.Blocks.Append(loop.Before).ToList();
                return regions.Any(r => !FitsIn(blocks, r.Try) && !FitsIn(blocks, r.Handler) && blocks.Any(r.Blocks.Contains)
                                        && !(r.Blocks.All(loop.Blocks.Contains)));
            });
            if (loops.Count == 0)
                method.ForeachRegions = null;
        }

        if (regions.Count > 0)
            method.CatchRegions = regions;
    }

    private static CatchRegion? Find(MethodAnalysisContext method, ISILControlFlowGraph cfg, DominatorInfo dominators, Block entry, List<CatchHandler> handlers)
    {
        var throwing = entry.Predecessors.Distinct().ToList();
        if (throwing.Count == 0)
            return null;

        var handler = cfg.Blocks.Where(b => dominators.Dominates(entry, b)).ToHashSet();
        var lifted = handlers.FirstOrDefault(h => handler.Any(b => b.Instructions.Any(h.Instructions.Contains)));

        // the deepest block dominating every call that throws here
        var common = throwing.Select(t => dominators.Dominators.TryGetValue(t, out var d) ? d : []).Aggregate((a, b) => a.Intersect(b).ToHashSet());
        var tryEntry = common.Where(c => c != cfg.EntryBlock && !handler.Contains(c)).OrderByDescending(c => dominators.Dominators[c].Count).FirstOrDefault();
        if (tryEntry == null)
            return null;

        // and what leads from it to them
        var tryBlocks = new HashSet<Block>();
        var pending = new Stack<Block>(throwing);
        while (pending.Count > 0)
        {
            var block = pending.Pop();
            if (handler.Contains(block) || !dominators.Dominates(tryEntry, block) || !tryBlocks.Add(block) || block == tryEntry)
                continue;
            foreach (var predecessor in block.Predecessors)
                pending.Push(predecessor);
        }

        if (!tryBlocks.Contains(tryEntry))
            return null;

        // and on to where its ways out meet, as the code up to there is inside it in the source (it only can't throw)
        while (true)
        {
            // (a return is a way out wherever it is)
            var exits = tryBlocks.SelectMany(b => b.NormalSuccessors)
                .Where(s => !tryBlocks.Contains(s) && !handler.Contains(s) && s != cfg.ExitBlock && !Returns(s)).Distinct().ToList();
            if (exits.Count <= 1)
                break;

            // one only the try leads to, on the way to another of its ways out
            var next = exits.FirstOrDefault(x => !x.IsCatchEntry && x.NormalPredecessors.All(tryBlocks.Contains) && dominators.Dominates(tryEntry, x)
                                                 && x.NormalSuccessors.Any(n => n != x && exits.Contains(n)));
            if (next == null)
                break;

            tryBlocks.Add(next);
        }

        var catchException = handler.SelectMany(b => b.Instructions).FirstOrDefault(i => i.OpCode == OpCode.CatchException);
        var caught = catchException?.Operands.Count > 1 && catchException.Operands[1] is TypeAnalysisContext type
            ? type
            : method.AppContext.SystemTypes.SystemExceptionType;

        return new CatchRegion
        {
            TryEntry = tryEntry,
            Try = tryBlocks,
            HandlerEntry = entry,
            Handler = handler,
            CatchType = caught,
            Exception = catchException?.Operands[0] as LocalVariable,
        };
    }

    private static bool IsAsyncMoveNext(MethodAnalysisContext method) =>
        method.Name == "MoveNext" && method.DeclaringType?.InterfaceContexts.Any(i => i.FullName == "System.Runtime.CompilerServices.IAsyncStateMachine") == true;

    private static bool CallsMethod(Instruction instruction, string name) =>
        instruction.OpCode is OpCode.Call or OpCode.CallVoid && instruction.Operands.Count > 0 && instruction.Operands[0] is MethodAnalysisContext { Name: var called } && called == name;

    private static bool IsStateStore(Instruction instruction) =>
        instruction is { OpCode: OpCode.Move, Operands: [FieldReference { Path.Count: 0, Local.IsThis: true, Field.Name: "<>1__state" }, Immediate] };

    // The blocks of an async MoveNext laid out as the C# compiler does around its try: the loads of the state machine's
    // fields into locals before it (the prologue), and from the final state store on to SetResult() after it (the tails)
    private static (Block? Prologue, HashSet<Block> Tails) ShapeAsync(ISILControlFlowGraph cfg)
    {
        var tails = new HashSet<Block>();
        foreach (var block in cfg.Blocks.ToList())
        {
            var setResult = block.Instructions.FindIndex(i => CallsMethod(i, "SetResult"));
            if (setResult < 0)
                continue;

            // the final state is set in this block or one straight before it (a merge of the ways to the end)
            var chain = new List<Block> { block };
            var holder = block;
            var stateStore = block.Instructions.FindLastIndex(setResult, IsStateStore);
            while (stateStore < 0 && chain.Count < 4 && holder.NormalPredecessors.Distinct().ToList() is [var previous] && previous.NormalSuccessors is [_])
            {
                holder = previous;
                chain.Add(holder);
                stateStore = holder.Instructions.FindLastIndex(IsStateStore);
            }

            if (stateStore < 0)
                continue;

            // what comes before the final state goes in the try
            var tail = holder.Instructions.Take(stateStore).Any(i => i.OpCode != OpCode.Nop) ? cfg.BlockStartingAt(holder.Instructions[stateStore]) : holder;
            if (tail == null)
                continue;
            tails.Add(tail);
            tails.UnionWith(chain.Where(b => b != holder));
        }

        var first = cfg.EntryBlock.NormalSuccessors.FirstOrDefault(s => s != cfg.ExitBlock);
        if (first == null)
            return (null, tails);

        // field loads (locals of this.<>4__this, this.<>1__state...) and nothing else
        var loads = first.Instructions.TakeWhile(i => i.OpCode == OpCode.Nop || i is { OpCode: OpCode.Move, Operands: [LocalVariable, FieldReference { Path.Count: 0, Local.IsThis: true }] }).Count();
        if (loads == 0 || loads == first.Instructions.Count || !first.Instructions.Take(loads).Any(i => i.OpCode == OpCode.Move))
            return (null, tails);

        cfg.BlockStartingAt(first.Instructions[loads]);
        return (first, tails);
    }

    private static bool Returns(Block block) => block.Instructions.Count > 0 && block.Instructions.All(i => i.OpCode is OpCode.Return or OpCode.Nop);

    // nothing but the entry is reached from outside (a catch is only reached by throwing, which isn't a way in here)
    private static bool Entered(HashSet<Block> part, Block entry) =>
        part.Contains(entry) && part.All(b => b == entry || b.NormalPredecessors.All(part.Contains));

    private static bool FitsIn(IEnumerable<Block> blocks, HashSet<Block> part) => blocks.All(part.Contains);

    // one is inside a part of the other, or they have nothing to do with each other
    private static bool Nests(CatchRegion a, CatchRegion b)
    {
        var aBlocks = a.Blocks.ToList();
        var bBlocks = b.Blocks.ToList();
        if (!aBlocks.Any(bBlocks.Contains))
            return true;
        return FitsIn(aBlocks, b.Try) || FitsIn(aBlocks, b.Handler) || FitsIn(bBlocks, a.Try) || FitsIn(bBlocks, a.Handler);
    }
}
