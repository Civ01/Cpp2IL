using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Late clean-ups of what MSVC's scheduling leaves around struct locals, for the shapes a C# compiler emits:
/// <list type="bullet">
/// <item>The address of a struct local, or of a field of one, kept in a register before it's used
/// (<c>ref var b = ref sm.&lt;&gt;t__builder; sm.&lt;&gt;1__state = -1; b.Start(ref sm);</c>) is that address wherever it's used: a local
/// in the frame doesn't move, so <c>sm.&lt;&gt;t__builder.Start(ref sm)</c>.</item>
/// <item>IL2CPP zeroes every local on entry, as <c>.locals init</c> does: a compiler-generated state machine is zeroed again
/// by nothing in the source, so its zeroing at the start goes.</item>
/// </list>
/// Runs after the field addresses are resolved, out of SSA.
/// </summary>
public static class AddressForwarding
{
    public static void Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } cfg)
            return;

        var instructions = cfg.Blocks.SelectMany(b => b.Instructions).ToList();
        var definitions = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var instruction in instructions)
            if (instruction.Destination is LocalVariable defined)
                (definitions.TryGetValue(defined, out var list) ? list : definitions[defined] = []).Add(instruction);

        // every mention of a local, and whether it's one an address can take the place of
        var mentions = new Dictionary<LocalVariable, List<(Instruction Instruction, int Operand, bool Direct)>>();
        foreach (var instruction in instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];
                foreach (var local in LocalsIn(operand))
                {
                    var direct = ReferenceEquals(operand, local) && !(i == 0 && instruction.Destination == local);
                    (mentions.TryGetValue(local, out var list) ? list : mentions[local] = []).Add((instruction, i, direct));
                }
            }
        }

        // A struct's method keeps 'this' (a pointer to the struct) in its frame for its catches to find: that copy is 'this'
        // itself, not another struct (an async state machine's MoveNext reading and writing its fields through it)
        if (method.DeclaringType is { IsValueType: true } && !method.IsStatic)
            foreach (var (local, defining) in definitions)
            {
                if (defining is not [{ OpCode: OpCode.Move, Operands: [_, LocalVariable { IsThis: true } self] } definition]
                    || local.IsThis || method.ParameterLocals.Contains(local) || !mentions.TryGetValue(local, out var uses))
                    continue;

                foreach (var (user, _, _) in uses)
                    if (!ReferenceEquals(user, definition))
                        SubstituteLocal(user, local, self);

                definition.OpCode = OpCode.Nop;
                definition.SetOperands();
            }

        // p = &x; ... *p: the value of x then (it's the same storage, whatever was stored in it in between), as IL2CPP's
        // finally lambdas read their captured locals
        foreach (var (local, defining) in definitions)
        {
            if (defining is not [{ OpCode: OpCode.Move, Operands: [_, AddressOf { Target: LocalVariable pointee }] } definition]
                || method.ParameterLocals.Contains(local) || !mentions.TryGetValue(local, out var uses))
                continue;

            // (an earlier forward may have changed an instruction since the uses were gathered)
            var reads = uses.Where(u => !ReferenceEquals(u.Instruction, definition)).ToList();
            if (reads.Count == 0 || reads.Any(u => u.Instruction.OpCode is OpCode.Phi || u.Operand >= u.Instruction.Operands.Count
                                                   || u.Instruction.Operands[u.Operand] is not MemoryOperand { Index: null, Addend: 0, Base: var through } || !ReferenceEquals(through, local)))
                continue;

            foreach (var (user, operand, _) in reads)
                user.SetOperand(operand, pointee);

            definition.OpCode = OpCode.Nop;
            definition.SetOperands();
        }

        foreach (var (local, defining) in definitions)
        {
            if (defining is not [{ OpCode: OpCode.Move, Operands: [_, AddressOf address] } definition] || !IsFixedAddress(address, method)
                || !mentions.TryGetValue(local, out var uses))
                continue;

            var reads = uses.Where(u => !ReferenceEquals(u.Instruction, definition)).ToList();
            if (definition.OpCode != OpCode.Move || reads.Count == 0
                || reads.Any(u => !u.Direct || u.Instruction.OpCode is OpCode.Phi || u.Operand >= u.Instruction.Operands.Count || !ReferenceEquals(u.Instruction.Operands[u.Operand], local)))
                continue;

            foreach (var (user, operand, _) in reads)
                user.SetOperand(operand, address);

            definition.OpCode = OpCode.Nop;
            definition.SetOperands();
        }

        WholeStructMoves(cfg);
        RetargetCopies(method, cfg);
        DropStateMachineZeroing(cfg);
        DropDeadZeroing(method, cfg);
    }

    // IL2CPP zeroes a local before the code that sets it, as .locals init would: when nothing can read the zero (every way on
    // from it sets the whole local first), it goes. Followed along the edges into catches too.
    private static void DropDeadZeroing(MethodAnalysisContext method, ISILControlFlowGraph cfg)
    {
        foreach (var block in cfg.Blocks)
        {
            for (var index = 0; index < block.Instructions.Count; index++)
            {
                var instruction = block.Instructions[index];
                if (instruction is not { OpCode: OpCode.Move, Operands: [LocalVariable local, DefaultValue or Immediate { Value: 0 }] }
                    || method.ParameterLocals.Contains(local) || local.IsThis || ReadBeforeSet(block, index + 1, local))
                    continue;

                instruction.OpCode = OpCode.Nop;
                instruction.SetOperands();
            }
        }
    }

    // whether some way on from here reads the local (or hands out its address, or writes part of it) before setting all of it
    private static bool ReadBeforeSet(Block start, int from, LocalVariable local)
    {
        var seen = new HashSet<Block>();
        var pending = new Stack<(Block Block, int From)>();
        pending.Push((start, from));
        while (pending.Count > 0)
        {
            var (block, index) = pending.Pop();
            var set = false;
            for (var i = index; i < block.Instructions.Count && !set; i++)
            {
                var instruction = block.Instructions[i];
                for (var o = 0; o < instruction.Operands.Count; o++)
                {
                    var operand = instruction.Operands[o];
                    if (o == 0 && ReferenceEquals(operand, local) && ReferenceEquals(instruction.Destination, local) && instruction.OpCode != OpCode.Phi)
                        continue;
                    if (LocalsIn(operand).Contains(local))
                        return true;
                }

                set = ReferenceEquals(instruction.Destination, local);
            }

            if (set)
                continue;

            foreach (var successor in block.Successors)
                if (seen.Add(successor))
                    pending.Push((successor, 0));
        }

        return false;
    }

    // t = x.GetAwaiter(); awaiter = t; with t read nowhere else: awaiter = x.GetAwaiter()
    private static void RetargetCopies(MethodAnalysisContext method, ISILControlFlowGraph cfg)
    {
        var instructions = cfg.Blocks.SelectMany(b => b.Instructions).ToList();
        var mentions = new Dictionary<LocalVariable, int>();
        foreach (var instruction in instructions)
            foreach (var operand in instruction.Operands)
                foreach (var local in LocalsIn(operand))
                    mentions[local] = mentions.GetValueOrDefault(local) + 1;

        foreach (var block in cfg.Blocks)
        {
            var real = block.Instructions.Where(i => i.OpCode != OpCode.Nop).ToList();
            for (var i = 1; i < real.Count; i++)
            {
                if (real[i] is not { OpCode: OpCode.Move, Operands: [LocalVariable target, LocalVariable temporary] } copy
                    || real[i - 1] is not { Destination: LocalVariable defined } definition || !ReferenceEquals(defined, temporary)
                    || ReferenceEquals(target, temporary) || method.ParameterLocals.Contains(temporary)
                    || mentions.GetValueOrDefault(temporary) != 2 || !SameType(target.Type, temporary.Type)
                    || definition.Operands.Skip(1).Any(o => LocalsIn(o).Contains(target)))
                    continue;

                definition.Destination = target;
                copy.OpCode = OpCode.Nop;
                copy.SetOperands();
            }
        }
    }

    // A struct of one field (an awaiter, which only holds its task) is moved as that field: awaiter.m_task = (Task)other,
    // where other is an awaiter too, is awaiter = other
    private static void WholeStructMoves(ISILControlFlowGraph cfg)
    {
        foreach (var instruction in cfg.Blocks.SelectMany(b => b.Instructions))
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count != 2)
                continue;

            switch (instruction.Operands[0], instruction.Operands[1])
            {
                // into the only field of a struct local
                case (FieldReference { Path.Count: 0, Local: { Type: { IsValueType: true } structType } owner } field, var source)
                    when OnlyField(structType) is { } onlyField && onlyField.Name == field.Field.Name:
                    if (SameType(TypeOf(source), structType))
                        instruction.SetOperands(owner, source);
                    else if (source is Immediate { Value: 0 } || source is DefaultValue)
                        instruction.SetOperands(owner, new DefaultValue(structType));
                    break;

                // out of it, into a local of the struct's type
                case (LocalVariable { Type: { IsValueType: true } destinationType } destination, FieldReference { Path.Count: 0, Local: { Type: { } sourceType } sourceOwner } sourceField)
                    when SameType(destinationType, sourceType) && OnlyField(sourceType) is { } onlySourceField && onlySourceField.Name == sourceField.Field.Name:
                    instruction.SetOperands(destination, sourceOwner);
                    break;
            }
        }
    }

    // (a generic instance's fields are its definition's)
    private static FieldAnalysisContext? OnlyField(TypeAnalysisContext type)
        => (type is GenericInstanceTypeAnalysisContext generic ? generic.GenericType : type).Fields.Where(f => !f.IsStatic).ToList() is [var only] ? only : null;

    private static TypeAnalysisContext? TypeOf(IOperand operand) => operand switch
    {
        LocalVariable local => local.Type,
        FieldReference field => field.Field.FieldType,
        DefaultValue value => value.Type,
        _ => null,
    };

    private static bool SameType(TypeAnalysisContext? a, TypeAnalysisContext? b) => a != null && b != null && (ReferenceEquals(a, b) || a.FullName == b.FullName);

    // the address of a struct local or parameter, or a field of one (a struct's this included): it's in the frame (or the
    // caller's), and doesn't move, whatever is stored there in between
    private static bool IsFixedAddress(AddressOf address, MethodAnalysisContext method) => address.Target switch
    {
        LocalVariable { Type: { IsValueType: true } } => true,
        FieldReference { Local: { Type: { IsValueType: true } } } field => !field.RootField.IsStatic,
        _ => false,
    };

    // every mention of one local in the instruction's operands made a mention of another
    private static void SubstituteLocal(Instruction instruction, LocalVariable from, LocalVariable to)
    {
        IOperand? Replace(IOperand operand) => operand switch
        {
            LocalVariable local when ReferenceEquals(local, from) => to,
            MemoryOperand memory when ReferenceEquals(memory.Base, from) || ReferenceEquals(memory.Index, from)
                => memory with { Base = ReferenceEquals(memory.Base, from) ? to : memory.Base, Index = ReferenceEquals(memory.Index, from) ? to : memory.Index },
            FieldReference field when ReferenceEquals(field.Local, from) => new FieldReference(field.Field, to, field.Offset) { Path = field.Path },
            AddressOf address when Replace(address.Target) is { } target => new AddressOf(target),
            ArrayLength length when ReferenceEquals(length.Array, from) => new ArrayLength(to),
            ArrayAccess access when ReferenceEquals(access.Array, from) || Replace(access.Index) != null
                => new ArrayAccess(ReferenceEquals(access.Array, from) ? to : access.Array, Replace(access.Index) ?? access.Index),
            _ => null,
        };

        for (var i = 0; i < instruction.Operands.Count; i++)
            if (Replace(instruction.Operands[i]) is { } replaced)
                instruction.SetOperand(i, replaced);
    }

    private static IEnumerable<LocalVariable> LocalsIn(IOperand operand)
    {
        switch (operand)
        {
            case LocalVariable local:
                yield return local;
                break;
            case MemoryOperand memory:
                if (memory.Base is LocalVariable memoryBase)
                    yield return memoryBase;
                if (memory.Index is LocalVariable memoryIndex)
                    yield return memoryIndex;
                break;
            case FieldReference { Local: { } owner }:
                yield return owner;
                break;
            case AddressOf { Target: LocalVariable addressed }:
                yield return addressed;
                break;
            case AddressOf { Target: FieldReference { Local: { } addressedOwner } }:
                yield return addressedOwner;
                break;
            case ArrayAccess access:
                yield return access.Array;
                if (access.Index is LocalVariable arrayIndex)
                    yield return arrayIndex;
                break;
            case ArrayLength { Array: { } lengthArray }:
                yield return lengthArray;
                break;
        }
    }

    private static void DropStateMachineZeroing(ISILControlFlowGraph cfg)
    {
        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction is not { OpCode: OpCode.Move, Operands: [LocalVariable { Type: { IsValueType: true } type } local, DefaultValue] }
                    || !type.InterfaceContexts.Any(i => i.FullName == "System.Runtime.CompilerServices.IAsyncStateMachine")
                    || InCycle(block))
                    continue;

                // the zeroing has to come before anything else does anything with it
                var before = cfg.Blocks.Where(b => b != block && Reaches(b, block)).SelectMany(b => b.Instructions)
                    .Concat(block.Instructions.TakeWhile(i => !ReferenceEquals(i, instruction)));
                if (before.Any(i => i.Operands.Any(o => LocalsIn(o).Contains(local))))
                    continue;

                instruction.OpCode = OpCode.Nop;
                instruction.SetOperands();
            }
        }
    }

    private static bool InCycle(Block block) => block.Successors.Any(s => Reaches(s, block));

    private static bool Reaches(Block from, Block to)
    {
        var seen = new HashSet<Block>();
        var pending = new Stack<Block>();
        pending.Push(from);
        while (pending.Count > 0)
        {
            var current = pending.Pop();
            if (current == to)
                return true;
            if (seen.Add(current))
                foreach (var successor in current.Successors)
                    pending.Push(successor);
        }

        return false;
    }
}
