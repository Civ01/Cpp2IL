using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A loop over a struct enumerator in the shape a foreach compiles to, recorded for IL generation to wrap in the
/// try/finally that disposes the enumerator (which il2cpp keeps only on the exception path, and for the collection
/// enumerators inlines away altogether). <see cref="Blocks"/> are the try region: the loop and whatever only it leads
/// to (a return from inside the loop), entered only at <see cref="Header"/>, from <see cref="Before"/>.
/// </summary>
/// <see cref="AsDisposable"/>: the enumerator's type isn't disposable itself (IEnumerator), so the finally disposes of it
/// only if it turns out to be (<c>(enumerator as IDisposable)?.Dispose()</c>).
public sealed record ForeachRegion(LocalVariable Enumerator, Block Before, Block Header, List<Block> Blocks, bool AsDisposable = false);

/// <summary>
/// Puts foreach loops over struct enumerators back into the shape a C# compiler gives them, so that the decompiler
/// recognises them:
/// <code>
/// enumerator = collection.GetEnumerator();      // the only store to it, right before the loop
/// while (enumerator.MoveNext()) {
///     current = enumerator.Current;             // the only use of Current, first in the body
///     ...
/// }
/// </code>
/// and records the loop so IL generation can put it in a try/finally disposing the enumerator. The loop gets an
/// enumerator local of its own, as MSVC shares the stack slot with other values outside the loop; the GetEnumerator()
/// call is traced back through the copies of its return buffer; il2cpp's pointer to the enumerator for the finally and
/// the explicit Dispose() calls on the normal paths go. Loops inside loops are done first. Runs last.
/// </summary>
public static class ForeachRecovery
{
    public static System.Action<string>? Debug;

    private static ForeachRegion? Reject(Block header, string why)
    {
        Debug?.Invoke($"foreach at B{header.ID}: {why}");
        return null;
    }

    public static void Run(MethodAnalysisContext method)
    {
        method.ForeachRegions = null;

        var graph = method.ControlFlowGraph!;
        var disposable = method.AppContext.GetAssemblyByName("mscorlib")?.GetTypeByFullName("System.IDisposable");
        if (disposable == null)
            return;

        var counter = 0;
        var regions = new List<ForeachRegion>();

        // inner loops first: an outer one waits until those inside it are done with
        var candidates = graph.Blocks.Where(b => b.Instructions.FirstOrDefault(i => i.OpCode != OpCode.Nop) is
            { OpCode: OpCode.Call, Operands: [MethodAnalysisContext { Name: "MoveNext" }, _, AddressOf { Target: LocalVariable } or LocalVariable, ..] }).ToList();
        var pending = candidates.ToHashSet();
        for (var progress = true; progress && pending.Count > 0;)
        {
            progress = false;
            foreach (var header in candidates.Where(pending.Contains).ToList())
            {
                var region = Match(method, graph, header, regions, pending, ref counter, out var deferred);
                if (deferred)
                    continue;

                pending.Remove(header);
                progress = true;
                if (region != null)
                    regions.Add(region);
            }
        }

        if (regions.Count > 0)
            method.ForeachRegions = regions;
    }

    private static ForeachRegion? Match(MethodAnalysisContext method, ISILControlFlowGraph graph, Block header, List<ForeachRegion> done, HashSet<Block> pending,
        ref int counter, out bool deferred)
    {
        deferred = false;
        // the condition: just enumerator.MoveNext(), maybe negated, and the branch on it
        // (a struct enumerator is called through its address, a class or interface one directly)
        var real = header.Instructions.Where(i => i.OpCode != OpCode.Nop).ToList();
        if (real is not [{ OpCode: OpCode.Call, Operands: [MethodAnalysisContext { Name: "MoveNext", Parameters.Count: 0 }, LocalVariable moved, var receiverOperand, ..] }, .. var rest]
            || ReceiverOf(receiverOperand) is not { } enumerator
            || enumerator.Type is not { } enumeratorType
            || (receiverOperand is AddressOf) != enumeratorType.IsValueType)
            return null;
        var byRef = enumeratorType.IsValueType;
        // one that isn't disposable has to be an interface or open class, which the finally tests for IDisposable
        var asDisposable = !IsDisposable(enumeratorType);
        if (asDisposable && (byRef || enumeratorType.IsSealed))
            return null;

        Instruction jumpInstruction;
        bool jumpsOut;
        if (rest is [{ OpCode: OpCode.ConditionalJump, Operands: [Block, LocalVariable c] } plainJump] && c == moved)
            (jumpInstruction, jumpsOut) = (plainJump, false);
        else if (rest is [{ OpCode: OpCode.Not, Operands: [LocalVariable negated, LocalVariable source] }, { OpCode: OpCode.ConditionalJump, Operands: [Block, LocalVariable n] } negatedJump]
                 && source == moved && n == negated)
            (jumpInstruction, jumpsOut) = (negatedJump, true);
        else
            return Reject(header, "condition is not just MoveNext()");

        if (header.NormalSuccessors.Distinct().Count() != 2)
            return Reject(header, "condition does not branch two ways");

        var jumpTarget = (Block)jumpInstruction.Operands[0];
        var other = header.NormalSuccessors.First(s => s != jumpTarget);
        var (body, exit) = jumpsOut ? (other, jumpTarget) : (jumpTarget, other);
        if (body == graph.ExitBlock || body.Predecessors.Distinct().Count() != 1)
            return Reject(header, "loop body has other entries");

        // the loop: what the body dominates and reaches, without going round, that gets back round (not an enclosing loop
        // that comes back to it from after it)
        var notDominated = Reach(graph.EntryBlock, b => b.NormalSuccessors, body);
        var forward = Reach(body, b => b.NormalSuccessors, header);
        var backward = Reach(header, b => b.NormalPredecessors, header, includeStart: false);
        var region = new HashSet<Block>(forward.Where(b => backward.Contains(b) && !notDominated.Contains(b))) { header };
        if (!region.Contains(body))
            return Reject(header, "no loop back to the condition");

        var loop = region.ToHashSet();

        // and what's only reached from inside it without rejoining the code after it (a return from the loop)
        var reachesExit = Reach(exit, b => b.NormalPredecessors, null);
        for (var grown = true; grown;)
        {
            grown = false;
            foreach (var block in graph.Blocks)
            {
                if (region.Contains(block) || block.IsCatchEntry || block == graph.ExitBlock || block == graph.EntryBlock || reachesExit.Contains(block) || notDominated.Contains(block)
                    || block.Predecessors.Count == 0 || !block.Predecessors.All(region.Contains))
                    continue;

                region.Add(block);
                grown = true;
            }
        }

        if (region.Any(b => b != header && pending.Contains(b)))
        {
            deferred = true;
            return null;
        }

        // a loop already done is either entirely inside this one, set up and all, or nowhere in it
        foreach (var inner in done)
            if (inner.Blocks.Any(region.Contains) && !(inner.Blocks.All(region.Contains) && region.Contains(inner.Before))
                || region.Contains(inner.Before) && !inner.Blocks.All(region.Contains))
                return Reject(header, "overlaps another loop partially");

        if (region.Any(b => b.Instructions.Any(i => i.OpCode == OpCode.IndirectJump)))
            return Reject(header, "contains an indirect jump");

        // entered only at the condition, and only from straight before the loop
        if (region.Any(b => b != header && !b.Predecessors.All(region.Contains)))
            return Reject(header, "loop entered other than at its condition");
        var outside = header.Predecessors.Where(p => !region.Contains(p)).Distinct().ToList();
        if (outside is not [var before] || before == graph.EntryBlock || before.NormalSuccessors.Distinct().Count() != 1
            || done.Any(r => r.Blocks.Contains(before) || r.Before == before))
            return Reject(header, "not entered from a single block before it");

        // Every use of the enumerator: the GetEnumerator() before the loop, MoveNext and Current in it, and the Dispose()
        // after it or before a return from it (the finally, outside of exceptions). C# can't touch the enumerator anywhere
        // else, so whatever else there is outside the loop is something else MSVC put in the same stack slot - which can
        // stay where it is, as the loop gets an enumerator of its own.
        var allInstructions = graph.Blocks.SelectMany(b => b.Instructions.Select(i => (Block: b, Instruction: i))).ToList();
        var uses = allInstructions.Where(x => x.Instruction.Operands.Any(o => Mentions(o, enumerator))).ToList();

        // the straight line of code leading into the loop, where the enumerator is set up
        var chain = new List<Block> { before };
        while (chain.Count < 8 && chain[^1].Predecessors.Distinct().ToList() is [var previous] && previous != graph.EntryBlock
               && previous.NormalSuccessors.Distinct().Count() == 1 && !region.Contains(previous) && !chain.Contains(previous)
               && !done.Any(r => r.Blocks.Contains(previous) || r.Before == previous))
            chain.Add(previous);
        chain.Reverse();
        var setup = chain.SelectMany(b => b.Instructions).Where(i => i.OpCode != OpCode.Nop).ToList();

        var currentCalls = new List<Instruction>();
        var disposals = new List<Instruction>();
        var guards = new List<(Block Block, Instruction Test)>();
        var foreign = new List<Instruction>();
        var casts = new List<Instruction>();
        foreach (var (block, instruction) in uses)
        {
            if (chain.Contains(block))
                continue; // the setup, below
            else if (block == header && instruction == real[0])
                continue;
            else if (region.Contains(block) && instruction is { OpCode: OpCode.Call, Operands: [MethodAnalysisContext { Name: "get_Current", Parameters.Count: 0 }, LocalVariable, var currentReceiver] }
                     && ReceiverOf(currentReceiver) == enumerator)
                currentCalls.Add(instruction);
            else if (IsDispose(instruction, enumerator))
                disposals.Add(instruction);
            // (one that may not be: (enumerator as IDisposable)?.Dispose())
            else if (asDisposable && !loop.Contains(block) && instruction is { OpCode: OpCode.IsInst, Operands: [LocalVariable, TypeAnalysisContext { FullName: "System.IDisposable" }, var cast] }
                     && ReferenceEquals(cast, enumerator))
                casts.Add(instruction);
            // (a class one is disposed of if it's there: if (enumerator != null) enumerator.Dispose())
            else if (!byRef && !loop.Contains(block) && instruction is { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [LocalVariable, var tested, Immediate { Value: 0 }] }
                     && ReferenceEquals(tested, enumerator))
                guards.Add((block, instruction));
            else if (!loop.Contains(block))
                foreign.Add(instruction);
            else
                return Reject(header, $"enumerator used in the loop by {instruction}");
        }

        // the as IDisposable: what it gives is only tested for null and disposed of
        if (asDisposable)
        {
            if (casts.Count == 0)
                return Reject(header, "not disposable, and not tested for IDisposable");

            foreach (var asCast in casts.Select(c => (LocalVariable)c.Operands[0]).Distinct())
                foreach (var (block, instruction) in allInstructions.Where(x => x.Instruction.Operands.Any(o => Mentions(o, asCast))))
                {
                    if (casts.Contains(instruction))
                        continue;
                    if (IsDispose(instruction, asCast))
                        disposals.Add(instruction);
                    else if (!loop.Contains(block) && instruction is { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [LocalVariable, var tested, Immediate { Value: 0 }] }
                             && ReferenceEquals(tested, asCast))
                        guards.Add((block, instruction));
                    else
                        return Reject(header, $"enumerator as IDisposable used by {instruction}");
                }
        }

        if (FindGetEnumerator(setup, enumerator) is not var (getEnumerator, copying))
            return Reject(header, "no GetEnumerator() found for the enumerator");

        // what's between it and the loop has to be able to go before it, as it has to end up last
        var callAt = setup.IndexOf(getEnumerator);
        var arguments = getEnumerator.Operands.Skip(2).SelectMany(Locals).ToHashSet();
        var buffer = (LocalVariable)getEnumerator.Operands[1];
        var unneeded = new List<Instruction>();
        foreach (var instruction in setup.Skip(callAt + 1))
        {
            if (copying.Contains(instruction) || instruction.OpCode == OpCode.Jump)
                continue;

            // il2cpp's finally keeps a pointer to the enumerator; and what's left in the return buffer is nobody's
            if (instruction is { OpCode: OpCode.Move, Operands: [MemoryOperand or FieldReference, AddressOf { Target: LocalVariable captured }] } && captured == enumerator
                || instruction is { OpCode: OpCode.Move, Operands: [var into, _] } && Inside(into) == buffer
                || instruction is { OpCode: OpCode.Move, Operands: [LocalVariable spare, LocalVariable returned] } && returned == buffer && spare != enumerator)
            {
                unneeded.Add(instruction);
                continue;
            }

            if (instruction.Destination is LocalVariable written && arguments.Contains(written)
                || instruction.Destination is FieldReference { Local: var fieldOwner } && arguments.Contains(fieldOwner)
                || instruction.IsCall && instruction.Operands.Skip(1).Any(o => Locals(o).Any(arguments.Contains))
                || instruction.Operands.Any(o => Mentions(o, enumerator) || Mentions(o, buffer)))
                return Reject(header, $"{instruction} cannot go before GetEnumerator()");
        }

        // the same for what's set up before it
        foreach (var instruction in setup.Take(callAt))
            if (instruction.Operands.Any(o => Mentions(o, enumerator)) && !copying.Contains(instruction)
                && instruction is not { OpCode: OpCode.Move, Operands: [LocalVariable, DefaultValue] })
                return Reject(header, $"enumerator used before GetEnumerator() by {instruction}");

        // Current: one call first in the body, which the rest read
        var getCurrent = currentCalls.Select(c => (MethodAnalysisContext)c.Operands[0]).FirstOrDefault() ?? CurrentGetter(enumeratorType);
        if (getCurrent == null)
            return Reject(header, "no get_Current");

        var currentType = currentCalls.Select(c => ((LocalVariable)c.Operands[1]).Type).FirstOrDefault(t => t != null) ?? getCurrent.ReturnType;
        if (currentType is GenericParameterTypeAnalysisContext)
            return Reject(header, "Current is of an open type");

        // each null test guards a dispose: it goes straight on to the way around it
        var unguard = new List<(Block Guard, Instruction Test, Instruction Jump, Block Skip, Block Disposing)>();
        foreach (var (guardBlock, test) in guards)
        {
            var disposing = guardBlock.NormalSuccessors.FirstOrDefault(s => s.Instructions.Any(disposals.Contains));
            var skip = guardBlock.NormalSuccessors.FirstOrDefault(s => s != disposing);
            if (guardBlock.Instructions is not [.., { OpCode: OpCode.ConditionalJump, Operands: [Block, LocalVariable condition] } jump] || !ReferenceEquals(condition, test.Operands[0])
                || disposing == null || skip == null || guardBlock.NormalSuccessors.Distinct().Count() != 2)
                return Reject(header, $"{test} doesn't guard the dispose");
            unguard.Add((guardBlock, test, jump, skip, disposing));
        }

        // ---- committed ----

        var own = new LocalVariable($"enumerator{counter}", new Register(null, $"ENUMERATOR_{counter}", 0), enumeratorType);
        method.Locals.Add(own);
        IOperand ownReceiver = byRef ? new AddressOf(own) : own;
        real[0].SetOperand(2, ownReceiver);
        foreach (var call in currentCalls)
            call.SetOperand(2, ownReceiver);

        foreach (var disposal in disposals.Concat(casts))
        {
            disposal.OpCode = OpCode.Nop;
            disposal.SetOperands();
        }

        foreach (var (guardBlock, test, jump, skip, disposing) in unguard)
        {
            test.OpCode = OpCode.Nop;
            test.SetOperands();
            jump.OpCode = OpCode.Jump;
            jump.SetOperands(skip);
            ISILControlFlowGraph.RemoveEdge(guardBlock, disposing);
            guardBlock.CalculateBlockType();
        }

        // nothing left of the old one but its zero init: that goes too
        var setupZeroInits = setup.Where(i => i is { OpCode: OpCode.Move, Operands: [LocalVariable zeroed, DefaultValue] } && zeroed == enumerator);
        if (foreign.All(i => i is { OpCode: OpCode.Move, Operands: [LocalVariable, DefaultValue] }))
            foreach (var zeroInit in foreign.Concat(setupZeroInits).ToList())
            {
                zeroInit.OpCode = OpCode.Nop;
                zeroInit.SetOperands();
            }

        var current = new LocalVariable($"current{counter}", new Register(null, $"CURRENT_{counter}", 0), currentType);
        counter++;
        method.Locals.Add(current);

        foreach (var call in currentCalls)
        {
            var destination = (LocalVariable)call.Operands[1];

            // a local that's only ever this value is the foreach variable itself
            var definedOnce = allInstructions.Count(x => x.Instruction.Destination is LocalVariable d && d == destination) == 1;
            var addressed = allInstructions.Any(x => x.Instruction.Operands.Any(o => o is AddressOf addressOf && Mentions(addressOf, destination)));
            if (definedOnce && !addressed && (destination.Type == null || destination.Type == current.Type))
            {
                foreach (var (_, user) in allInstructions)
                    if (user != call)
                        Substitute(user, destination, current);

                // (an index, say, it can't stand in for, which still needs the copy)
                if (!allInstructions.Any(x => x.Instruction != call && x.Instruction.Operands.Any(o => Mentions(o, destination))))
                {
                    call.OpCode = OpCode.Nop;
                    call.SetOperands();
                    continue;
                }
            }

            call.OpCode = OpCode.Move;
            call.SetOperands(destination, current);
        }

        body.Instructions.Insert(0, new Instruction(body.Instructions.FirstOrDefault()?.Index ?? 0, OpCode.Call, getCurrent, current, byRef ? new AddressOf(own) : own));

        foreach (var instruction in copying.Concat(unneeded))
        {
            instruction.OpCode = OpCode.Nop;
            instruction.SetOperands();
        }

        // GetEnumerator() straight into the enumerator, last before the loop
        chain.First(b => b.Instructions.Contains(getEnumerator)).Instructions.Remove(getEnumerator);
        getEnumerator.SetOperand(1, own);
        var jumpIndex = before.Instructions.FindIndex(i => i.OpCode == OpCode.Jump);
        before.Instructions.Insert(jumpIndex >= 0 ? jumpIndex : before.Instructions.Count, getEnumerator);

        var ordered = graph.Blocks.Where(region.Contains).ToList();
        ordered.Remove(header);
        ordered.Insert(0, header);
        return new ForeachRegion(own, before, header, ordered, asDisposable);
    }

    // The local a memory or field operand is part of
    private static LocalVariable? Inside(IOperand operand) => operand switch
    {
        MemoryOperand { Base: LocalVariable memoryBase } => memoryBase,
        FieldReference field => field.Local,
        _ => null
    };

    private static bool IsDispose(Instruction instruction, LocalVariable enumerator)
        => instruction is { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: "Dispose", Parameters.Count: 0 }, var disposed, ..] } && ReceiverOf(disposed) == enumerator
           // (through the interface the call may not be known to return nothing)
           || instruction is { OpCode: OpCode.Call, Operands: [MethodAnalysisContext { Name: "Dispose", Parameters.Count: 0 }, LocalVariable or Register, var disposedToo, ..] } && ReceiverOf(disposedToo) == enumerator;

    // the enumerator a call is made on: a struct one by its address, a class or interface one itself
    private static LocalVariable? ReceiverOf(IOperand operand) => operand switch
    {
        AddressOf { Target: LocalVariable byAddress } => byAddress,
        LocalVariable direct => direct,
        _ => null,
    };

    // a foreach disposes of its enumerator if it can be disposed of (IEnumerator<T> is IDisposable, IEnumerator isn't)
    private static bool IsDisposable(TypeAnalysisContext type)
    {
        var definition = (type as GenericInstanceTypeAnalysisContext)?.GenericType ?? type;
        if (definition.FullName is "System.IDisposable" or "System.Collections.Generic.IEnumerator`1" || definition.Methods.Any(m => m.Name == "Dispose"))
            return true;
        for (var current = definition; current != null; current = current.BaseType)
            if (current.InterfaceContexts.Any(i => i.FullName is "System.IDisposable" || i.FullName.StartsWith("System.Collections.Generic.IEnumerator`1")))
                return true;
        return false;
    }

    // The GetEnumerator() call the enumerator is the result of, and the copies that got it there: straight into it,
    // through temporaries (the return buffer, rax pointing at it), or a piece at a time from the buffer
    private static (Instruction Call, List<Instruction> Copying)? FindGetEnumerator(List<Instruction> setup, LocalVariable enumerator)
    {
        var copying = new List<Instruction>();

        // the last whole write of the enumerator, or the pieces written since its zero init
        var last = setup.FindLastIndex(i => i.Destination is LocalVariable written && written == enumerator);
        var pieces = setup.Select((instruction, index) => (instruction, index))
            .Where(x => x.index > last && x.instruction is { OpCode: OpCode.Move, Operands: [var into, LocalVariable] } && Inside(into) == enumerator)
            .ToList();

        LocalVariable? source = null;
        var at = last;
        if (pieces.Count > 0)
        {
            // each piece read from the same place in the same buffer, and only for this
            foreach (var (piece, index) in pieces)
            {
                var value = (LocalVariable)piece.Operands[1];
                var read = setup.Take(index).LastOrDefault(i => i.Destination is LocalVariable d && d == value);
                if (read is not { OpCode: OpCode.Move } || setup.Count(i => i.Operands.Any(o => Mentions(o, value))) != 2)
                    return null;

                var from = (read.Operands[1], piece.Operands[0]) switch
                {
                    (MemoryOperand { Base: LocalVariable b, Index: null } r, MemoryOperand { Index: null } w) when r.Addend == w.Addend && r.Size == w.Size => b,
                    (FieldReference r, FieldReference w) when r.Chain.Select(f => f.Name).SequenceEqual(w.Chain.Select(f => f.Name)) => r.Local,
                    _ => null
                };
                if (from == null || source != null && from != source)
                    return null;

                source = from;
                copying.Add(piece);
                copying.Add(read);
                at = System.Math.Min(at < 0 ? index : at, setup.IndexOf(read));
            }
        }
        else if (last >= 0)
        {
            switch (setup[last])
            {
                case { OpCode: OpCode.Call, Operands: [MethodAnalysisContext { Name: "GetEnumerator" }, ..] } direct:
                    return (direct, copying);
                case { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] } copy:
                    source = copied;
                    copying.Add(copy);
                    break;
                // a whole copy read as its first field (the low half of a vector load)
                case { OpCode: OpCode.Move, Operands: [_, FieldReference { Path.Count: 0, Local: var whole } first] } copy
                    when whole.Type == enumerator.Type && first.Field.DeclaringType.Fields.Where(f => !f.IsStatic).OrderBy(f => f.Offset).FirstOrDefault() == first.Field:
                    source = whole;
                    copying.Add(copy);
                    break;
                default:
                    return null;
            }
        }
        else
            return null;

        // back through copies of the buffer (or of a pointer to it) to the call that filled it
        for (var hops = 0; hops < 4 && source != null; hops++)
        {
            var definition = setup.Take(at).LastOrDefault(i => i.Destination is LocalVariable d && d == source);
            switch (definition)
            {
                case { OpCode: OpCode.Call, Operands: [MethodAnalysisContext { Name: "GetEnumerator" }, ..] }:
                    return (definition, copying);
                case { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] }:
                    source = copied;
                    break;
                case { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable pointer, Index: null, Addend: 0 }] }:
                    source = pointer;
                    break;
                default:
                    return null;
            }

            copying.Add(definition);
            at = setup.IndexOf(definition);
        }

        return null;
    }

    private static MethodAnalysisContext? CurrentGetter(TypeAnalysisContext enumeratorType)
    {
        var instance = enumeratorType as GenericInstanceTypeAnalysisContext;
        var definition = instance?.GenericType ?? enumeratorType;
        if (definition.Methods.FirstOrDefault(m => m is { Name: "get_Current", IsStatic: false, Parameters.Count: 0 }) is not { } getter)
            return null;

        if (instance == null)
            return definition.GenericParameters.Count == 0 ? getter : null;

        return new ConcreteGenericMethodAnalysisContext(getter, instance.GenericArguments, []);
    }

    // The blocks reachable from start (itself included unless asked not to) along next, not going through stop
    private static HashSet<Block> Reach(Block start, System.Func<Block, IEnumerable<Block>> next, Block? stop, bool includeStart = true)
    {
        var seen = new HashSet<Block>();
        var pending = new Stack<Block>(includeStart ? [start] : next(start));
        while (pending.Count > 0)
        {
            var block = pending.Pop();
            if (block == stop || !seen.Add(block))
                continue;

            foreach (var following in next(block))
                pending.Push(following);
        }

        return seen;
    }

    private static bool Mentions(IOperand operand, LocalVariable local) => Locals(operand).Contains(local);

    private static void Substitute(Instruction instruction, LocalVariable from, LocalVariable to)
    {
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            IOperand? replacement = instruction.Operands[i] switch
            {
                LocalVariable local when local == from => to,
                MemoryOperand { Base: LocalVariable memoryBase } memory when memoryBase == from => memory with { Base = to },
                FieldReference { Local: var fieldLocal } field when fieldLocal == from => new FieldReference(field.Field, to, field.Offset) { Path = field.Path },
                ArrayLength { Array: var array } when array == from => new ArrayLength(to),
                _ => null,
            };

            if (replacement != null)
                instruction.SetOperand(i, replacement);
        }
    }

    private static IEnumerable<LocalVariable> Locals(IOperand operand)
    {
        switch (operand)
        {
            case LocalVariable direct:
                yield return direct;
                break;
            case MemoryOperand memory:
                if (memory.Base is LocalVariable baseLocal)
                    yield return baseLocal;
                if (memory.Index is LocalVariable indexLocal)
                    yield return indexLocal;
                break;
            case AddressOf { Target: var target }:
                foreach (var inner in Locals(target))
                    yield return inner;
                break;
            case FieldReference field:
                yield return field.Local;
                break;
            case ArrayAccess access:
                yield return access.Array;
                foreach (var inner in Locals(access.Index))
                    yield return inner;
                break;
            case ArrayLength length:
                yield return length.Array;
                break;
        }
    }
}
