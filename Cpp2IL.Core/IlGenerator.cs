using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;

namespace Cpp2IL.Core;

public static class IlGenerator
{
    private const string HelpersNamespace = "Cpp2ILInjected";
    private const string HelpersTypeName = "Cpp2ILHelpers";
    private const string NoteIssueMethodName = "NoteDecompilerIssue";

    public static void InjectHelpersType(ApplicationAnalysisContext appContext)
    {
        var helpersType = appContext.InjectTypeIntoAllAssemblies(
            HelpersNamespace,
            HelpersTypeName,
            null,
            TypeAttributes.Public | TypeAttributes.Class | TypeAttributes.Abstract | TypeAttributes.Sealed);

        helpersType.InjectMethodToAllAssemblies(
            NoteIssueMethodName,
            appContext.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static,
            [appContext.SystemTypes.SystemStringType]);
    }

    public static void GenerateIl(MethodAnalysisContext context, MethodDefinition definition)
    {
        var assembly = context.DeclaringType!.DeclaringAssembly;
        var module = definition.DeclaringModule!;
        var factory = module.CorLibTypeFactory;

        var noteIssueContext = assembly
            .GetTypeByFullName($"{HelpersNamespace}.{HelpersTypeName}")?.Methods.FirstOrDefault(m => m.Name == NoteIssueMethodName);

        var writeLine = noteIssueContext != null
            ? noteIssueContext.ToMethodDescriptor()
            : factory.CorLibScope
                .CreateTypeReference("System", "Console")
                .CreateMemberReference("WriteLine", MethodSignature.CreateStatic(factory.Void, [factory.String]));

        // Change branch targets to instructions
        foreach (var instruction in context.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions))
        {
            if (instruction.Operands.Count > 0 && instruction.Operands[0] is Block target)
            {
                if (target.Instructions.Count > 0)
                    instruction.SetOperand(0, target.Instructions[0]);
            }
        }

        var body = new CilMethodBody()
        {
            InitializeLocals = true, // Without this ILSpy does: CompilerServices.Unsafe.SkipInit(out object obj);
            ComputeMaxStackOnBuild = false // There's stack imbalance somewhere, but this works for now
        };

        definition.CilMethodBody = body;

        // Make sure context.Locals actually has all locals (idk why it doesn't sometimes)
        foreach (var operand in context.ControlFlowGraph.Instructions.SelectMany(i => i.Operands))
        {
            LocalVariable? local = null;

            if (operand is FieldReference field)
                local = field.Local;

            if (operand is LocalVariable local2)
                local = local2;

            if (operand is MemoryOperand memory && memory.Base is LocalVariable local3)
                local = local3;

            var elementOperand = operand is AddressOf { Target: ArrayAccess elementAddress } ? elementAddress : operand;

            if (elementOperand is ArrayAccess arrayAccess)
            {
                local = arrayAccess.Array;

                if (arrayAccess.Index is LocalVariable index && !context.Locals.Contains(index))
                    context.Locals.Add(index);
            }

            if (operand is ArrayLength arrayLength)
                local = arrayLength.Array;

            if (operand is AddressOf { Target: LocalVariable addressed })
                local = addressed;

            if (operand is AddressOf { Target: FieldReference addressedField })
                local = addressedField.Local;

            if (local != null && !context.Locals.Contains(local))
                context.Locals.Add(local);
        }

        // Map ISIL locals to IL
        Dictionary<LocalVariable, CilLocalVariable> locals = [];
        foreach (var local in context.Locals)
        {
            TypeSignature ilType;

            // Use object if type couldn't be determined, or if it's void, which no locals sig can hold
            if (local.Type != null && local.Type != context.AppContext.SystemTypes.SystemVoidType && !LocalVariables.HasForeignGenericParameters(local.Type, context))
                ilType = local.Type.ToTypeSignature();
            else
                ilType = module.CorLibTypeFactory.Object;

            // a generic parameter in a method that has none (a call resolved to an open generic definition) isn't a type here
            if (MentionsGenericParameter(ilType, 0) && context.GenericParameters.Count == 0 && context.DeclaringType is { GenericParameters.Count: 0, DeclaringType: null or { GenericParameters.Count: 0 } })
                ilType = module.CorLibTypeFactory.Object;

            var ilLocal = new CilLocalVariable(ilType);
            body.LocalVariables.Add(ilLocal);
            locals.Add(local, ilLocal);
        }

        /* foreach (var instruction in context.ControlFlowGraph!.Instructions)
        {
            body.Instructions.Add(CilOpCodes.Ldstr, instruction.ToString());
            body.Instructions.Add(CilOpCodes.Call, _importer!.ImportMethod(_writeLine!));
        }
        body.Instructions.Add(CilOpCodes.Ldstr, "-------------------------------------------------------------------------");
        body.Instructions.Add(CilOpCodes.Call, _importer!.ImportMethod(_writeLine!)); */

        _constructorCalls = null;
        PairConstructorCalls(context);

        // Generate IL
        Dictionary<Instruction, List<CilInstruction>> instructionMap = [];
        Dictionary<Block, CilInstruction> blockEntryMap = [];
        List<(CilInstruction BranchInstruction, Block TargetBlock)> pendingBlockBranchFixups = [];

        // IL starts executing at the first block emitted, which isn't necessarily where the method starts (a pass may
        // have replaced the start with a block that sits later in the list, like a collapsed copy loop): jump there
        var cfg = context.ControlFlowGraph!;
        var firstEmitted = cfg.Blocks.FirstOrDefault(b => b != cfg.EntryBlock && b != cfg.ExitBlock && b.Instructions.Count > 0);
        var realStart = cfg.EntryBlock.Successors.FirstOrDefault(s => s != cfg.ExitBlock);
        if (realStart != null && firstEmitted != null && realStart != firstEmitted)
        {
            var startBridge = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel());
            definition.CilMethodBody!.Instructions.Add(startBridge);
            pendingBlockBranchFixups.Add((startBridge, realStart));
        }

        // a foreach's try region has to be contiguous, and is best straight after the GetEnumerator() before it; one
        // inside another goes inside its region the same way
        var regions = context.ForeachRegions ?? [];
        var regionSets = regions.ToDictionary(r => r, r => r.Blocks.ToHashSet());
        bool Encloses(Analysis.ForeachRegion outer, Analysis.ForeachRegion inner) => outer != inner && inner.Blocks.All(regionSets[outer].Contains);
        List<Analysis.ForeachRegion> ChildrenOf(Analysis.ForeachRegion? scope) => regions
            .Where(c => c != scope && (scope == null || Encloses(scope, c)) && !regions.Any(m => m != scope && Encloses(m, c) && (scope == null || Encloses(scope, m))))
            .ToList();

        var emissionOrder = new List<(Block Block, List<Analysis.ForeachRegion> Within)>();
        void Order(IEnumerable<Block> blocks, Analysis.ForeachRegion? scope, List<Analysis.ForeachRegion> within)
        {
            var children = ChildrenOf(scope);
            var inChildren = children.SelectMany(c => c.Blocks).ToHashSet();
            foreach (var block in blocks)
            {
                if (inChildren.Contains(block))
                    continue;

                emissionOrder.Add((block, within));
                foreach (var child in children.Where(c => c.Before == block))
                    Order(child.Blocks, child, [..within, child]);
            }
        }

        Order(context.ControlFlowGraph!.Blocks, null, []);

        var regionIl = regions.ToDictionary(r => r, _ => new List<CilInstruction>());

        // a switch is emitted from its first compare; the rest of its compares aren't reached any more
        var switches = (context.SwitchTables ?? []).ToDictionary(t => t.First);
        var replacedBySwitch = switches.Values.SelectMany(t => t.Chain.Skip(1)).ToHashSet();
        var pendingSwitchFixups = new List<(CilInstruction Switch, List<Block> Targets)>();

        foreach (var (block, within) in emissionOrder)
        {
            if (block == context.ControlFlowGraph.EntryBlock || block == context.ControlFlowGraph.ExitBlock)
                continue;

            if (block.Instructions.Count == 0 || replacedBySwitch.Contains(block))
                continue;

            var blockStart = definition.CilMethodBody!.Instructions.Count;
            EmitBlock(block);

            foreach (var region in within)
                regionIl[region].AddRange(definition.CilMethodBody!.Instructions.Skip(blockStart));
        }

        void EmitSwitch(Block block, Analysis.SwitchTable table)
        {
            var compareAt = block.Instructions.FindLastIndex(i => i.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual);
            foreach (var instruction in block.Instructions.Take(compareAt))
            {
                var generated = GenerateInstructions(instruction, context, definition, locals, writeLine);
                instructionMap.Add(instruction, generated);
            }

            var il = definition.CilMethodBody!.Instructions;
            var start = il.Count;
            LoadLocal(table.Value, definition, locals);
            if (table.Minimum != 0)
            {
                il.Add(CilOpCodes.Ldc_I4, unchecked((int)table.Minimum));
                il.Add(CilOpCodes.Sub);
            }

            var switchInstruction = new CilInstruction(CilOpCodes.Switch, new List<ICilLabel>());
            il.Add(switchInstruction);
            pendingSwitchFixups.Add((switchInstruction, table.Targets));

            var toDefault = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel());
            il.Add(toDefault);
            pendingBlockBranchFixups.Add((toDefault, table.Default));

            if (!blockEntryMap.ContainsKey(block))
                blockEntryMap[block] = il[instructionMap.Where(kv => block.Instructions.Contains(kv.Key)).SelectMany(kv => kv.Value).Select(i => IndexOf(il, i)).DefaultIfEmpty(start).Min()];
        }

        void EmitBlock(Block block)
        {
            if (switches.TryGetValue(block, out var table) && locals.ContainsKey(table.Value))
            {
                EmitSwitch(block, table);
                return;
            }

            foreach (var instruction in block.Instructions)
            {
                var generated = GenerateInstructions(instruction, context, definition, locals, writeLine);
                instructionMap.Add(instruction, generated);

                if (!blockEntryMap.ContainsKey(block) && generated.Count > 0)
                    blockEntryMap[block] = generated[0];
            }

            var lastInstruction = block.Instructions.Last();
            
            if (lastInstruction.OpCode == OpCode.ConditionalJump)
            {
                var trueTarget = TryResolveJumpTargetBlock(lastInstruction, context.ControlFlowGraph);
                var falseSuccessor = block.Successors.FirstOrDefault(s => s != trueTarget && s != context.ControlFlowGraph.ExitBlock);
                if (falseSuccessor == null) return;
                var bridge = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel());
                definition.CilMethodBody!.Instructions.Add(bridge);
                pendingBlockBranchFixups.Add((bridge, falseSuccessor));
            }

            else if (lastInstruction.OpCode != OpCode.Jump && lastInstruction.OpCode != OpCode.Return && lastInstruction.OpCode != OpCode.IndirectJump)
            {
                var successor = block.Successors.FirstOrDefault(s => s != context.ControlFlowGraph.ExitBlock);
                if (successor == null) return;
                var bridge = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel());
                definition.CilMethodBody!.Instructions.Add(bridge);
                pendingBlockBranchFixups.Add((bridge, successor));
            }
        }
        // Set IL branch targets
        foreach (var kvp in instructionMap)
        {
            var instruction = kvp.Key;
            var il = kvp.Value;

            if (instruction.OpCode == OpCode.Jump || instruction.OpCode == OpCode.ConditionalJump)
            {
                var ilBranch = il.First(i => i.OpCode == CilOpCodes.Br || i.OpCode == CilOpCodes.Brtrue);

                if (instruction.Operands[0] is Block targetBlock)
                {
                    context.AddWarning($"Branch target block not in cfg: {instruction} ({targetBlock})");
                    ilBranch.OpCode = CilOpCodes.Nop;
                    ilBranch.Operand = null;
                    continue;
                }

                var target = (Instruction)instruction.Operands[0];

                if (!instructionMap.ContainsKey(target))
                {
                    context.AddWarning($"Branch target not in ISIL to IL map: {instruction} --- {target}");
                    ilBranch.OpCode = CilOpCodes.Nop;
                    ilBranch.Operand = null;
                    continue;
                }

                ilBranch.Operand = new CilInstructionLabel(instructionMap[target][0]);
            }
        }
        
        foreach (var (branchInstruction, targetBlock) in pendingBlockBranchFixups)
        {
            var target = ResolveBlockEntryInstruction(targetBlock, blockEntryMap);
            if (target == null)
            {
                context.AddWarning($"Unable to resolve branch target block: {targetBlock}");
                branchInstruction.OpCode = CilOpCodes.Nop;
                branchInstruction.Operand = null;
                continue;
            }

            branchInstruction.Operand = new CilInstructionLabel(target);
        }

        foreach (var (switchInstruction, targets) in pendingSwitchFixups)
        {
            var labels = (List<ICilLabel>)switchInstruction.Operand!;
            foreach (var target in targets)
            {
                var entry = ResolveBlockEntryInstruction(target, blockEntryMap);
                if (entry == null)
                {
                    context.AddWarning($"Unable to resolve switch target block: {target}");
                    switchInstruction.OpCode = CilOpCodes.Pop; // still takes the value off the stack, then on to the default
                    switchInstruction.Operand = null;
                    break;
                }

                labels.Add(entry.CreateLabel());
            }
        }

        // innermost first, as what wrapping one adds is part of those around it
        foreach (var region in regions.OrderBy(r => r.Blocks.Count))
        {
            var added = WrapForeach(context, definition, locals, region, regionIl[region]);
            foreach (var outer in regions.Where(o => Encloses(o, region)))
                regionIl[outer].AddRange(added);
        }

        _constructorCalls = null;

        // Add analysis warnings
        var instructions = body.Instructions;
        foreach (var warning in context.AnalysisWarnings)
        {
            instructions.Add(CilOpCodes.Ldstr, Diagnostic("Warning: " + warning));
            instructions.Add(CilOpCodes.Call, writeLine);
        }
    }

    // Puts a foreach loop's code into try { ... } finally { enumerator.Dispose(); }: jumps out of it become leaves (a
    // conditional one through a leave right after the loop), and returns from inside it leave to a return after it
    private static List<CilInstruction> WrapForeach(MethodAnalysisContext context, MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals,
        Analysis.ForeachRegion region, List<CilInstruction> il)
    {
        var body = method.CilMethodBody!;
        if (il.Count == 0 || !locals.TryGetValue(region.Enumerator, out var enumerator)
            || context.AppContext.GetAssemblyByName("mscorlib")?.GetTypeByFullName("System.IDisposable")?.Methods.FirstOrDefault(m => m.Name == "Dispose") is not { } dispose)
            return [];

        var inside = il.ToHashSet(ReferenceEqualityComparer.Instance);
        var exits = new List<CilInstruction>();
        var returnPath = new List<CilInstruction>();
        CilLocalVariable? returned = null;

        foreach (var instruction in il)
        {
            if (instruction.OpCode == CilOpCodes.Ret)
            {
                if (returnPath.Count == 0)
                {
                    if (!context.IsVoid)
                    {
                        returned = new CilLocalVariable(context.ReturnType.ToTypeSignature());
                        body.LocalVariables.Add(returned);
                        returnPath.Add(new CilInstruction(CilOpCodes.Ldloc, returned));
                    }

                    returnPath.Add(new CilInstruction(CilOpCodes.Ret));
                }

                if (returned != null)
                {
                    // the value is on the stack: store it, and leave right after
                    var leave = new CilInstruction(CilOpCodes.Leave, returnPath[0].CreateLabel());
                    exits.Add(leave);
                    instruction.OpCode = CilOpCodes.Stloc;
                    instruction.Operand = returned;
                    body.Instructions.Insert(IndexOf(body.Instructions, instruction) + 1, leave);
                }
                else
                {
                    instruction.OpCode = CilOpCodes.Leave;
                    instruction.Operand = returnPath[0].CreateLabel();
                }

                continue;
            }

            if (instruction.Operand is not CilInstructionLabel { Instruction: { } target } || inside.Contains(target))
                continue;

            if (instruction.OpCode == CilOpCodes.Br)
                instruction.OpCode = CilOpCodes.Leave;
            else if (instruction.OpCode.FlowControl == CilFlowControl.ConditionalBranch)
            {
                var stub = new CilInstruction(CilOpCodes.Leave, target.CreateLabel());
                exits.Add(stub);
                instruction.Operand = stub.CreateLabel();
            }
        }

        // after everything of the region, including the leaves just put in
        var end = il.Concat(exits).Select(i => IndexOf(body.Instructions, i)).Max() + 1;

        var stubs = exits.Where(e => IndexOf(body.Instructions, e) < 0).ToList();
        var handler = new List<CilInstruction>
        {
            new(CilOpCodes.Ldloca, enumerator),
            new(CilOpCodes.Constrained, region.Enumerator.Type!.ToTypeSignature().ToTypeDefOrRef()),
            new(CilOpCodes.Callvirt, dispose.ToMethodDescriptor()),
            new(CilOpCodes.Endfinally),
        };

        body.Instructions.InsertRange(end, stubs.Concat(handler).Concat(returnPath));

        var afterHandler = end + stubs.Count + handler.Count;
        if (afterHandler >= body.Instructions.Count)
            body.Instructions.Add(CilOpCodes.Nop); // never reached, but the handler has to end before something

        body.ExceptionHandlers.Add(new CilExceptionHandler
        {
            HandlerType = CilExceptionHandlerType.Finally,
            TryStart = il[0].CreateLabel(),
            TryEnd = handler[0].CreateLabel(),
            HandlerStart = handler[0].CreateLabel(),
            HandlerEnd = body.Instructions[afterHandler].CreateLabel(),
        });

        return [..exits, ..handler, ..returnPath];
    }

    // CilInstruction compares by value, which two "br IL_0010" are as well
    private static int IndexOf(CilInstructionCollection instructions, CilInstruction instruction)
    {
        for (var i = 0; i < instructions.Count; i++)
            if (ReferenceEquals(instructions[i], instruction))
                return i;

        return -1;
    }

    // Limit so we don't run into the 16mb limit (see AsmResolver issue #775)
    private static string Diagnostic(string message) 
        => message.Length <= 250 ? message : message[..250] + "…";
    
    private static Block? TryResolveJumpTargetBlock(Instruction jumpInstruction, ISILControlFlowGraph cfg)
    {
        if (jumpInstruction.Operands.Count == 0)
            return null;

        if (jumpInstruction.Operands[0] is Block targetBlock)
            return targetBlock;

        if (jumpInstruction.Operands[0] is Instruction targetInstruction)
            return cfg.FindBlockByInstruction(targetInstruction);

        return null;
    }

    private static CilInstruction? ResolveBlockEntryInstruction(Block block,
        Dictionary<Block, CilInstruction> blockEntryMap, HashSet<Block>? visited = null)
    {
        if (blockEntryMap.TryGetValue(block, out var target))
            return target;

        visited ??= [];
        if (!visited.Add(block))
            return null;

        foreach (var successor in block.Successors)
        {
            var resolved = ResolveBlockEntryInstruction(successor, blockEntryMap, visited);
            if (resolved != null)
                return resolved;
        }
        return null;
    }

    private static List<CilInstruction> GenerateInstructions(Instruction instruction, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var body = method.CilMethodBody!;
        var instructions = body.Instructions;
        var currentCount = instructions.Count;
        var startIndex = instructions.Count;

        var module = method.DeclaringModule!;

        switch (instruction.OpCode)
        {
            case OpCode.Invalid:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Invalid instruction: {instruction}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.NotImplemented:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Not implemented instruction: {instruction.Operands[0]}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Interrupt:
            case OpCode.Nop:
                instructions.Add(CilOpCodes.Nop);
                break;

            case OpCode.Move:
                // a class or its static storage, as runtime pointers: IL reaches statics and types by name, so there's
                // nothing to keep (what reads them handles the type themselves)
                if (instruction.Operands[0] is LocalVariable { Type: RuntimeClassTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext }
                    && instruction.Operands[1] is TypeAnalysisContext
                        or LocalVariable { Type: RuntimeClassTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext }
                        or MemoryOperand { Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext or RgctxTableTypeAnalysisContext or MethodRgctxTableTypeAnalysisContext } })
                {
                    instructions.Add(CilOpCodes.Nop);
                    break;
                }

                if (instruction.Operands[0] is FieldReference field) // stfld takes instance before value so LoadOperand StoreToOperand doesn't work
                {
                    var isStaticStore = LoadFieldContainer(field, method, locals);

                    LoadOperand(instruction.Operands[1], method, locals, writeLine, field.Field.FieldType);
                    instructions.Add(isStaticStore ? CilOpCodes.Stsfld : CilOpCodes.Stfld, field.Field.ToFieldDescriptor());
                    break;
                }

                // stelem needs array and index before the value, so like stfld it can't go through LoadOperand/StoreToOperand.
                // This also lets ILSpy handle it as a proper array initializer
                if (instruction.Operands[0] is ArrayAccess { Array.Type: SzArrayTypeAnalysisContext { ElementType: { } stored } } target)
                {
                    LoadLocal(target.Array, method, locals);
                    LoadOperand(target.Index, method, locals, writeLine);
                    LoadOperand(instruction.Operands[1], method, locals, writeLine, stored);
                    instructions.Add(CilOpCodes.Stelem, stored.ToTypeSignature().ToTypeDefOrRef());
                    break;
                }

                LoadOperand(instruction.Operands[1], method, locals, writeLine, DestinationType(instruction.Operands[0]));
                if (NumericConversion(SourceType(instruction.Operands[1], context), DestinationType(instruction.Operands[0])) is { } conversion)
                    instructions.Add(conversion);
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.NewArr:
                if (instruction.Operands is [_, SzArrayTypeAnalysisContext { ElementType: { } newArrayElement }, { } length])
                {
                    LoadOperand(length, method, locals, writeLine);
                    instructions.Add(CilOpCodes.Newarr, newArrayElement.ToTypeSignature().ToTypeDefOrRef());
                }
                else
                    instructions.Add(CilOpCodes.Ldnull);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Newobj:
                // Try and fuse our Newobj + the follow up constructor CallVoid into one IL newobj.
                // If we can't, just fall back to an Ldnull.
                if (FindConstructorCall(context, instruction) is { Operands: [MethodAnalysisContext constructor, _, ..] } constructorCall)
                {
                    // Operands run [ctor, newObject, arguments..., methodInfo], so take only as many as
                    // the constructor declares (i.e. drop methodInfo)
                    // the constructor may be the shared one (Foo<object>..ctor) while the allocation knows the instantiation
                    if (instruction.Operands is [_, GenericInstanceTypeAnalysisContext allocatedGeneric]
                        && (constructor as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext is { DeclaringType: { } constructorOwner } sharedBase
                        && ReferenceEquals(constructorOwner, allocatedGeneric.GenericType)
                        && constructor.DeclaringType is GenericInstanceTypeAnalysisContext constructorGeneric
                        && !constructorGeneric.GenericArguments.Select(a => a.FullName).SequenceEqual(allocatedGeneric.GenericArguments.Select(a => a.FullName)))
                        constructor = new ConcreteGenericMethodAnalysisContext(sharedBase, allocatedGeneric.GenericArguments, []);

                    var constructorArgs = constructorCall.Operands.Skip(ConstructorReceiverIndex(constructorCall) + 1).Take(constructor.Parameters.Count).ToList();
                    for (var i = 0; i < constructorArgs.Count; i++)
                        LoadOperand(constructorArgs[i], method, locals, writeLine, constructor.Parameters[i].ParameterType);

                    instructions.Add(CilOpCodes.Newobj, constructor.ToMethodDescriptor());
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);

                    constructorCall.OpCode = OpCode.Nop;
                    constructorCall.SetOperands();
                }
                else if (instruction.Operands is [_, TypeAnalysisContext allocatedType] && allocatedType.Methods.FirstOrDefault(m => m is { Name: ".ctor", Parameters.Count: 0 }) is { } parameterlessCtor)
                {
                    // Nothing to fuse with, so the allocation was self-contained. The type is still right, so construct it bare.
                    instructions.Add(CilOpCodes.Newobj, parameterlessCtor.ToMethodDescriptor());
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                }
                else
                {
                    instructions.Add(CilOpCodes.Ldnull);
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                }
                break;

            case OpCode.Box:
                if (instruction.Operands is [_, var boxedClass, var boxedValue] && boxedClass switch
                    {
                        RuntimeClassTypeAnalysisContext { RepresentedType: var represented } => represented,
                        LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var represented } } => represented,
                        TypeAnalysisContext type and not (RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext) => type,
                        _ => null,
                    } is { } boxedType)
                {
                    // il2cpp_value_box takes the value by address, but IL boxes it by value
                    LoadOperand(boxedValue is AddressOf { Target: LocalVariable byRef } ? byRef : boxedValue, method, locals, writeLine, boxedType);
                    instructions.Add(CilOpCodes.Box, boxedType.ToTypeSignature().ToTypeDefOrRef());
                }
                else
                    instructions.Add(CilOpCodes.Ldnull);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Unbox:
            {
                var unboxedType = instruction.Operands[1] switch
                {
                    LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var represented } } => represented,
                    RuntimeClassTypeAnalysisContext { RepresentedType: var represented } => represented,
                    _ => null,
                };

                LoadOperand(instruction.Operands[2], method, locals, writeLine);
                if (unboxedType != null)
                    instructions.Add(CilOpCodes.Unbox, unboxedType.ToTypeSignature().ToTypeDefOrRef());
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;
            }

            case OpCode.IsInst:
            {
                var checkedType = instruction.Operands[1] switch
                {
                    LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var represented } } => represented,
                    RuntimeClassTypeAnalysisContext { RepresentedType: var represented } => represented,
                    TypeAnalysisContext type and not (RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext) => type,
                    _ => null
                };

                LoadOperand(instruction.Operands[2], method, locals, writeLine, context.AppContext.SystemTypes.SystemObjectType);
                if (checkedType != null)
                    instructions.Add(instruction.Checked ? CilOpCodes.Castclass : CilOpCodes.Isinst, checkedType.ToTypeSignature().ToTypeDefOrRef());
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;
            }

            case OpCode.Throw:
                if (instruction.Operands is [TypeAnalysisContext exceptionType]
                    && exceptionType.Methods.FirstOrDefault(m => m.Name == ".ctor" && m.Parameters.Count == 0) is { } exceptionCtor)
                    instructions.Add(CilOpCodes.Newobj, exceptionCtor.ToMethodDescriptor());
                else if (instruction.Operands is [LocalVariable or FieldReference])
                    LoadOperand(instruction.Operands[0], method, locals, writeLine); // an already-constructed exception
                else
                    instructions.Add(CilOpCodes.Ldnull);

                instructions.Add(CilOpCodes.Throw);
                break;

            case OpCode.Phi:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Phi opcodes should not exist at this point in decompilation ({instruction})"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Call:
            case OpCode.CallVoid:
                if (instruction.Operands[0] is not MethodAnalysisContext targetMethod)
                {
                    if (instruction.Operands[0] is Immediate targetAddress)
                        instructions.Add(CilOpCodes.Ldstr, $"Method not found @{targetAddress.UnsignedValue:X}");
                    else // Probably key function. Just the target, the full operand dump is huge and blows the 16MB #US heap limit
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unknown call target operand: {instruction.Operands[0]}"));

                    instructions.Add(CilOpCodes.Call, writeLine);
                    break;
                }

                var importedMethod = targetMethod.ToMethodDescriptor();

                var thisParamIndex = instruction.OpCode == OpCode.Call ? 2 : 1;
                TypeAnalysisContext? constrainedTo = null;

                if (!targetMethod.IsStatic) // Load 'this' param
                {
                    if ((instruction.Operands.Count - 1) >= thisParamIndex)
                    {
                        // a struct's address handed to a method of object/Enum/an interface (ToString on an enum, MoveNext through
                        // IEnumerator): that's a constrained virtual call on the struct
                        if (targetMethod.DeclaringType is { IsValueType: false } && instruction.Operands[thisParamIndex] switch
                            {
                                AddressOf { Target: LocalVariable { Type: { IsValueType: true } addressedType } } when addressedType is not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext) => addressedType,
                                AddressOf { Target: FieldReference { Field.FieldType: { IsValueType: true } fieldType } } => fieldType,
                                _ => null,
                            } is { } valueReceiverType)
                        {
                            if (instruction.Operands[thisParamIndex] is AddressOf { Target: FieldReference constrainedField })
                                LoadFieldAddress(constrainedField, method, locals);
                            else
                                LoadLocalAddress((LocalVariable)((AddressOf)instruction.Operands[thisParamIndex]).Target, method, locals);
                            constrainedTo = valueReceiverType;
                            goto receiverLoaded;
                        }

                        // A value type's instance method takes 'this' as a managed pointer
                        if (targetMethod.DeclaringType is { IsValueType: true } && instruction.Operands[thisParamIndex] is AddressOf { Target: FieldReference receiverField })
                        {
                            LoadFieldAddress(receiverField, method, locals);
                            goto receiverLoaded;
                        }

                        var receiverLocal = instruction.Operands[thisParamIndex] switch
                        {
                            AddressOf { Target: LocalVariable addressedReceiver } => addressedReceiver,
                            LocalVariable { Type: { IsValueType: true } receiverType } valueReceiver when receiverType is not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext) => valueReceiver,
                            _ => null
                        };

                        if (targetMethod.DeclaringType is { IsValueType: true } && receiverLocal != null)
                            LoadLocalAddress(receiverLocal, method, locals);
                        else
                            LoadOperand(instruction.Operands[thisParamIndex], method, locals, writeLine, targetMethod.DeclaringType);

                        receiverLoaded: ;
                    }
                    else
                    {
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Non static method called without 'this' param ({instruction})"));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        instructions.Add(CilOpCodes.Ldnull);
                    }
                }

                // Load normal params
                var callParamIndex = instruction.OpCode == OpCode.Call ? (targetMethod.IsStatic ? 2 : 3) : (targetMethod.IsStatic ? 1 : 2);
                // A call whose target was only identified after lifting still carries the operands the
                // unknown-callee convention gave it, which may be fewer than the method actually takes.
                // The stack still has to match the signature, so anything missing gets a placeholder.
                var availableArgs = instruction.Operands.Count - callParamIndex;
                for (var i = 0; i < targetMethod.Parameters.Count; i++)
                {
                    var parameterType = targetMethod.Parameters[i].ParameterType;

                    if (i < availableArgs)
                        LoadOperand(instruction.Operands[callParamIndex + i], method, locals, writeLine, parameterType);
                    else
                        PushDefaultOf(parameterType, instructions);
                }

                if (constrainedTo != null)
                {
                    instructions.Add(CilOpCodes.Constrained, constrainedTo.ToTypeSignature().ToTypeDefOrRef());
                    instructions.Add(CilOpCodes.Callvirt, importedMethod);
                }
                else
                    instructions.Add(CilOpCodes.Call, importedMethod);

                // the lifter's guess at whether the callee returns anything can disagree with the
                // signature we later resolved, so go by the signature and balance the stack
                if (!targetMethod.IsVoid)
                {
                    if (instruction.OpCode == OpCode.Call)
                        StoreToOperand(instruction.Operands[1], method, locals, writeLine);
                    else
                        instructions.Add(CilOpCodes.Pop);
                }

                break;

            case OpCode.IndirectCall:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Indirect call: {instruction.Operands[0]} (should have been resolved before IL gen)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Return:
                if (!context.IsVoid)
                {
                    if (instruction.Operands.Count == 1)
                        LoadOperand(instruction.Operands[0], method, locals, writeLine, context.ReturnType);
                    else
                        instructions.Add(CilOpCodes.Ldnull); // ret still pops a value even if we lost track of it
                }
                instructions.Add(CilOpCodes.Ret);
                break;

            case OpCode.Jump:
                instructions.Add(CilOpCodes.Br, new CilInstructionLabel());
                break;

            case OpCode.ConditionalJump:
                LoadOperand(instruction.Operands[1], method, locals, writeLine);
                instructions.Add(CilOpCodes.Brtrue, new CilInstructionLabel());
                break;

            case OpCode.IndirectJump:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Indirect jump: {instruction.Operands[0]} (should have been resolved before IL gen)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.ShiftStack:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Stack shift: {instruction} (stack analysis should have removed these)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.CheckEqual:
            case OpCode.CheckGreater:
            case OpCode.CheckLess:
            case OpCode.CheckNotEqual:
            case OpCode.CheckGreaterOrEqual:
            case OpCode.CheckLessOrEqual:

            case OpCode.Add:
            case OpCode.Subtract:
            case OpCode.Multiply:
            case OpCode.Divide:
            case OpCode.Modulo:

            case OpCode.ShiftLeft:
            case OpCode.ShiftRight:

            case OpCode.And:
            case OpCode.Or:
            case OpCode.Xor:
                // klass pointer read => GetType
                if (instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
                    && TryEmitExactTypeComparison(instruction, method, locals, writeLine))
                    break;

                // Float arithmetic on a promoted integer operand needs an explicit conversion, so both
                // operands are coerced to the (float) result type. A no-op when they already match.
                var floatConversion = FloatArithmeticConversion(instruction);

                // a 32 bit mask or constant against a 32 bit value (x & 0xFFFFFFFC, the lifter reads it unsigned) is a 32 bit
                // constant; and a 32 bit operand of an operation with a 64 bit result is widened first (or a shift wraps)
                var wideResult = instruction.OpCode is not (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
                                 && DestinationType(instruction.Operands[0]) is { Namespace: "System", Name: "Int64" or "UInt64" };
                for (var operandIndex = 1; operandIndex <= 2; operandIndex++)
                {
                    var operand = instruction.Operands[operandIndex];
                    var other = instruction.Operands[3 - operandIndex];
                    var otherNarrow = Narrow32(SourceType(other, context));

                    if (operand is Immediate { Value: > int.MaxValue and <= uint.MaxValue } wrapped && otherNarrow && !wideResult)
                        instructions.Add(CilOpCodes.Ldc_I4, unchecked((int)(uint)wrapped.Value));
                    else
                        LoadOperand(operand, method, locals, writeLine);

                    if (floatConversion is { } operandConversion)
                        instructions.Add(operandConversion);
                    else if (wideResult && instruction.OpCode is OpCode.ShiftLeft or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.And or OpCode.Or or OpCode.Xor
                             && (operandIndex == 1 || instruction.OpCode != OpCode.ShiftLeft)
                             && SourceType(operand, context) is { Namespace: "System", Name: "Int32" or "UInt32" or "Int16" or "UInt16" or "Byte" or "SByte" } narrow)
                        instructions.Add(narrow.Name.StartsWith("U") || narrow.Name == "Byte" ? CilOpCodes.Conv_U8 : CilOpCodes.Conv_I8);
                }

                switch (instruction.OpCode)
                {
                    case OpCode.CheckEqual: instructions.Add(CilOpCodes.Ceq); break;
                    case OpCode.CheckGreater: instructions.Add(CilOpCodes.Cgt); break;
                    case OpCode.CheckLess: instructions.Add(CilOpCodes.Clt); break;

                    // a != b  ==  (a == b) == 0
                    case OpCode.CheckNotEqual:
                        instructions.Add(CilOpCodes.Ceq);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;
                    // a >= b  ==  !(a < b)
                    case OpCode.CheckGreaterOrEqual:
                        instructions.Add(CilOpCodes.Clt);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;
                    // a <= b  ==  !(a > b)
                    case OpCode.CheckLessOrEqual:
                        instructions.Add(CilOpCodes.Cgt);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;

                    case OpCode.Add: instructions.Add(CilOpCodes.Add); break;
                    case OpCode.Subtract: instructions.Add(CilOpCodes.Sub); break;
                    case OpCode.Multiply: instructions.Add(CilOpCodes.Mul); break;
                    case OpCode.Divide: instructions.Add(CilOpCodes.Div); break;
                    case OpCode.Modulo: instructions.Add(CilOpCodes.Rem); break;

                    case OpCode.ShiftLeft: instructions.Add(CilOpCodes.Shl); break;
                    case OpCode.ShiftRight: instructions.Add(CilOpCodes.Shr); break;

                    case OpCode.And: instructions.Add(CilOpCodes.And); break;
                    case OpCode.Or: instructions.Add(CilOpCodes.Or); break;
                    case OpCode.Xor: instructions.Add(CilOpCodes.Xor); break;
                }

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Not:
            case OpCode.Negate:
                LoadOperand(instruction.Operands[1], method, locals, writeLine);

                if (instruction.OpCode == OpCode.Negate)
                    instructions.Add(CilOpCodes.Neg);
                else if (IsBoolean(instruction.Operands[1], context))
                {
                    instructions.Add(CilOpCodes.Ldc_I4_0);
                    instructions.Add(CilOpCodes.Ceq);
                }
                else
                    instructions.Add(CilOpCodes.Not);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unknown instruction: {instruction}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;
        }

        return instructions.ToList().GetRange(startIndex, instructions.Count - startIndex); // Return added IL
    }
    
    private static int ConstructorReceiverIndex(Instruction constructorCall) => constructorCall.OpCode == OpCode.CallVoid ? 1 : 2;

    // Try find the follow up CallVoid for a constructor, after a Newobj.
    // Each allocation's constructor call, taken out of the code before any IL is emitted (it may well be in a block that
    // is emitted before the allocation's own)
    [System.ThreadStatic] private static Dictionary<Instruction, Instruction>? _constructorCalls;

    private static void PairConstructorCalls(MethodAnalysisContext context)
    {
        _constructorCalls = [];
        foreach (var newobj in context.ControlFlowGraph!.Instructions.Where(i => i.OpCode == OpCode.Newobj).ToList())
        {
            if (FindConstructorCall(context, newobj) is not { } call)
                continue;

            _constructorCalls[newobj] = new Instruction(call.Index, call.OpCode, call.Operands.ToList());
            call.OpCode = OpCode.Nop;
            call.SetOperands();
        }
    }

    private static Instruction? FindConstructorCall(MethodAnalysisContext context, Instruction newobj)
    {
        if (_constructorCalls != null && _constructorCalls.TryGetValue(newobj, out var paired))
            return paired;

        var newObject = newobj.Operands[0];

        // The allocation and the constructor call routinely end up in different blocks
        var instructions = context.ControlFlowGraph!.Instructions;
        var index = instructions.IndexOf(newobj);

        if (index < 0)
            return null;

        for (var i = index + 1; i < instructions.Count; i++)
        {
            var candidate = instructions[i];

            if (candidate is not { OpCode: OpCode.Call or OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor" }, ..] })
                continue;

            var receiver = ConstructorReceiverIndex(candidate);

            if (candidate.Operands.Count > receiver && ReferenceEquals(candidate.Operands[receiver], newObject))
                return candidate;
        }

        return null;
    }

    private static CilOpCode? FloatArithmeticConversion(Instruction instruction)
    {
        if (instruction.OpCode is not (OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo))
            return null;

        return (instruction.Operands[0] as LocalVariable)?.Type?.FullName switch
        {
            "System.Single" => CilOpCodes.Conv_R4,
            "System.Double" => CilOpCodes.Conv_R8,
            _ => null,
        };
    }

    /// <summary>
    /// Loads a constant the compiler placed in read-only data and reads at an absolute address: a float or integer, or
    /// a small struct of them (a Color or Vector4 literal, read as one 16 byte vector), built with the struct's
    /// constructor when it has one taking every field in order, else field by field. The value is only knowable from
    /// what it's used as, so needs <paramref name="expectedType"/>.
    /// </summary>
    private static bool TryLoadReadOnlyConstant(MemoryOperand memory, TypeAnalysisContext? expectedType, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        if (memory is not { Base: null, Index: null } || expectedType == null || expectedType is ByRefTypeAnalysisContext or PointerTypeAnalysisContext)
            return false;

        var binary = expectedType.AppContext.Binary;
        var address = (ulong)memory.Addend;

        if (!binary.IsReadOnlyDataAddress(address))
            return false;

        byte[] Read(long offset, int count)
        {
            var raw = binary.MapVirtualAddressToRaw(address + (ulong)offset, false);
            var content = binary.GetRawBinaryContent();
            return raw <= 0 || raw + count > content.Length ? [] : content.Slice((int)raw, count).ToArray();
        }

        if (ReadOnlyScalar(expectedType, 0, Read) is { } scalar)
        {
            // the read must cover the value (a 16 byte vector read used as a float is its first lane)
            if (memory.Size > 0 && memory.Size < Utils.TypeSizes.StorageSize(expectedType, binary.PointerSizeBytes))
                return false;

            LoadOperand(scalar, method, locals, writeLine, expectedType);
            return true;
        }

        if (!StackStructRecovery.IsStruct(expectedType) || expectedType is GenericInstanceTypeAnalysisContext)
            return false;

        var pointerSize = binary.PointerSizeBytes;
        var size = Utils.TypeSizes.StorageSize(expectedType, pointerSize);
        if (size <= 0 || size > 16 || memory.Size > 0 && memory.Size < size)
            return false;

        var fields = expectedType.Fields.Where(f => !f.IsStatic && (f.Attributes & FieldAttributes.Literal) == 0).ToList();
        var values = new List<IOperand>();
        foreach (var field in fields)
        {
            if (field.BackingData?.FieldOffset is not { } offset || ReadOnlyScalar(field.FieldType, offset, Read) is not { } value)
                return false;
            values.Add(value);
        }

        if (values.Count == 0)
            return false;

        var instructions = method.CilMethodBody!.Instructions;
        var constructor = expectedType.Methods.FirstOrDefault(m => m is { IsStatic: false, Name: ".ctor" } && m.Parameters.Count == fields.Count
            && m.Parameters.Select(p => p.ParameterType.FullName).SequenceEqual(fields.Select(f => f.FieldType.FullName)));

        if (constructor != null)
        {
            for (var i = 0; i < values.Count; i++)
                LoadOperand(values[i], method, locals, writeLine, fields[i].FieldType);
            instructions.Add(CilOpCodes.Newobj, constructor.ToMethodDescriptor());
            return true;
        }

        var structType = expectedType.ToTypeSignature().ToTypeDefOrRef();
        var temporary = new CilLocalVariable(expectedType.ToTypeSignature());
        method.CilMethodBody.LocalVariables.Add(temporary);
        instructions.Add(CilOpCodes.Ldloca, temporary);
        instructions.Add(CilOpCodes.Initobj, structType);
        for (var i = 0; i < values.Count; i++)
        {
            instructions.Add(CilOpCodes.Ldloca, temporary);
            LoadOperand(values[i], method, locals, writeLine, fields[i].FieldType);
            instructions.Add(CilOpCodes.Stfld, fields[i].ToFieldDescriptor());
        }
        instructions.Add(CilOpCodes.Ldloc, temporary);
        return true;
    }

    private static IOperand? ReadOnlyScalar(TypeAnalysisContext type, long offset, System.Func<long, int, byte[]> read)
    {
        var underlying = type.IsEnumType ? type.EnumUnderlyingType : type;
        if (underlying is not { Namespace: "System" })
            return null;

        var size = underlying.Name switch
        {
            "Single" or "Int32" or "UInt32" => 4,
            "Double" or "Int64" or "UInt64" => 8,
            "Int16" or "UInt16" or "Char" => 2,
            "Byte" or "SByte" or "Boolean" => 1,
            _ => 0,
        };

        if (size == 0 || read(offset, size) is not { Length: > 0 } bytes)
            return null;

        return underlying.Name switch
        {
            "Single" => new FloatLiteral(System.BitConverter.ToSingle(bytes, 0)),
            "Double" => new DoubleLiteral(System.BitConverter.ToDouble(bytes, 0)),
            "Int32" => new Immediate(System.BitConverter.ToInt32(bytes, 0)),
            "UInt32" => new Immediate(System.BitConverter.ToUInt32(bytes, 0)),
            "Int64" or "UInt64" => new Immediate(System.BitConverter.ToInt64(bytes, 0)),
            "Int16" => new Immediate(System.BitConverter.ToInt16(bytes, 0)),
            "UInt16" or "Char" => new Immediate(System.BitConverter.ToUInt16(bytes, 0)),
            "SByte" => new Immediate((sbyte)bytes[0]),
            _ => new Immediate(bytes[0]),
        };
    }

    private static bool Narrow32(TypeAnalysisContext? type) =>
        type is { IsEnumType: true } ? type.EnumUnderlyingType?.FullName is "System.Int32" or "System.UInt32"
            : type?.FullName is "System.Int32" or "System.UInt32";

    private static void LoadOperand(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        TypeAnalysisContext? expectedType = null)
    {
        var instructions = method.CilMethodBody!.Instructions;

        var module = method.DeclaringModule!;

        // A null reference reaches us as an integer zero, which would otherwise be emitted as a literal 0
        // and read back as a cast from a number.
        // (a type parameter could be a struct: that zero is default(T))
        if (expectedType is GenericParameterTypeAnalysisContext && IsZeroConstant(operand))
        {
            LoadOperand(new DefaultValue(expectedType), method, locals, writeLine);
            return;
        }

        if (expectedType is { IsValueType: false } && IsZeroConstant(operand))
        {
            instructions.Add(CilOpCodes.Ldnull);
            return;
        }

        // Likewise a zeroed struct (a null float? passed in a register, a cleared Color) is default(T), not a number
        if (expectedType is { IsValueType: true, IsEnumType: false } and not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext or GenericParameterTypeAnalysisContext)
            && !MetadataResolver.IsPrimitiveOrEnum(expectedType) && IsZeroConstant(operand))
        {
            LoadOperand(new DefaultValue(expectedType), method, locals, writeLine);
            return;
        }

        switch (operand)
        {
            // a 32 bit store of 0xFFFFFFFF into an int is -1 (the lifter reads the immediate unsigned)
            case Immediate { Value: > int.MaxValue and <= uint.MaxValue } wrapped when expectedType is { FullName: "System.Int32" or "System.UInt32" } or { IsEnumType: true, EnumUnderlyingType.FullName: "System.Int32" or "System.UInt32" }:
                instructions.Add(CilOpCodes.Ldc_I4, unchecked((int)(uint)wrapped.Value));
                break;
            case Immediate { Value: >= int.MinValue and <= int.MaxValue } immediate:
                instructions.Add(CilOpCodes.Ldc_I4, (int)immediate.Value);
                break;
            case Immediate immediate:
                instructions.Add(CilOpCodes.Ldc_I8, immediate.Value);
                break;
            case FloatLiteral f:
                instructions.Add(CilOpCodes.Ldc_R4, f.Value);
                break;
            case DoubleLiteral d:
                instructions.Add(CilOpCodes.Ldc_R8, d.Value);
                break;
            case StringLiteral s:
                instructions.Add(CilOpCodes.Ldstr, s.Value);
                break;
            // a class held in a local, where a type handle or a Type is wanted: typeof(T)
            case LocalVariable { Type: RuntimeClassTypeAnalysisContext classLocal } when expectedType?.FullName is "System.RuntimeTypeHandle" or "System.Type":
                LoadOperand(classLocal, method, locals, writeLine, expectedType);
                break;
            case LocalVariable local:
                LoadLocal(local, method, locals);
                break;
            case ArrayLength arrayLength:
                LoadLocal(arrayLength.Array, method, locals);
                instructions.Add(CilOpCodes.Ldlen);
                instructions.Add(CilOpCodes.Conv_I4);
                break;
            // A struct passed by value travels as a pointer to a copy (win64), but IL wants the value itself
            case AddressOf { Target: LocalVariable addressedValue } when expectedType is { IsValueType: true } and not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext)
                                                                         && addressedValue.Type is { } addressedType && addressedType.FullName == expectedType.FullName:
                LoadLocal(addressedValue, method, locals);
                break;
            case AddressOf { Target: LocalVariable addressed }:
                LoadLocalAddress(addressed, method, locals);
                break;
            // Likewise the address of a struct field, passed by value
            case AddressOf { Target: FieldReference addressedFieldValue } when expectedType is { IsValueType: true } and not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext)
                                                                               && addressedFieldValue.Field.FieldType.FullName == expectedType.FullName:
                LoadOperand(addressedFieldValue, method, locals, writeLine);
                break;
            case AddressOf { Target: FieldReference addressedField }:
                LoadFieldAddress(addressedField, method, locals);
                break;
            case DefaultValue defaultValue:
            {
                var defaultTemp = new CilLocalVariable(defaultValue.Type.ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(defaultTemp);
                instructions.Add(CilOpCodes.Ldloca, defaultTemp);
                instructions.Add(CilOpCodes.Initobj, defaultValue.Type.ToTypeSignature().ToTypeDefOrRef());
                instructions.Add(CilOpCodes.Ldloc, defaultTemp);
                break;
            }
            case AddressOf { Target: ArrayAccess elementAddress }:
                LoadLocal(elementAddress.Array, method, locals);
                LoadOperand(elementAddress.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelema,
                    ((SzArrayTypeAnalysisContext)elementAddress.Array.Type!).ElementType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case ArrayAccess arrayAccess:
                LoadLocal(arrayAccess.Array, method, locals);
                LoadOperand(arrayAccess.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelem,
                    ((SzArrayTypeAnalysisContext)arrayAccess.Array.Type!).ElementType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case FieldReference field:
            {
                var first = true;
                foreach (var link in field.Chain)
                {
                    if (first && link.IsStatic)
                        instructions.Add(CilOpCodes.Ldsfld, link.ToFieldDescriptor());
                    else
                    {
                        if (first)
                            LoadLocal(field.Local, method, locals);
                        instructions.Add(CilOpCodes.Ldfld, link.ToFieldDescriptor());
                    }

                    first = false;
                }

                break;
            }
            case MemoryOperand memory:
                if (memory.Index == null && memory.Addend == 0 && memory.Scale == 0
                    && memory.Base is LocalVariable local2)
                {
                    LoadLocal(local2, method, locals);

                    // A load through a managed pointer (byref) dereferences it to yield the referent.
                    if (local2.Type is ByRefTypeAnalysisContext { ElementType: { } referent })
                        instructions.Add(referent.IsValueType || referent is GenericParameterTypeAnalysisContext
                            ? new CilInstruction(CilOpCodes.Ldobj, referent.ToTypeSignature().ToTypeDefOrRef())
                            : new CilInstruction(CilOpCodes.Ldind_Ref));
                    break;
                }
                // Il2CppClass::stack_slot_size (2022+ full generic sharing): what shared code sizes the storage for a T
                // with, the size of a value type or of a reference, exactly sizeof(T)
                if (memory is { Index: null, Addend: 0xFC, Size: 4, Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } sized } } }
                    && sized.AppContext.MetadataVersion >= 29 && sized.AppContext.Binary.PointerSizeBytes == 8)
                {
                    instructions.Add(CilOpCodes.Sizeof, sized.ToTypeSignature().ToTypeDefOrRef());
                    break;
                }
                // a read of read-only data (.rdata) is a constant the compiler pooled: a float, or a whole struct literal
                if (TryLoadReadOnlyConstant(memory, expectedType, method, locals, writeLine))
                    break;
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unmanaged memory load: " + operand));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeMethodInfoAnalysisContext runtimeMethod:
                // A delegate constructor takes its target as a native pointer, which is exactly ldftn.
                if (expectedType?.FullName == "System.IntPtr")
                {
                    instructions.Add(CilOpCodes.Ldftn, runtimeMethod.RepresentedMethod.ToMethodDescriptor());
                    break;
                }

                //Not fully implemented, these basically shouldn't actually ever exist in the final IL.
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeFieldInfoAnalysisContext runtimeField:
                // fieldof(F), e.g. the handle InitializeArray takes.
                if (expectedType?.FullName == "System.RuntimeFieldHandle")
                {
                    instructions.Add(CilOpCodes.Ldtoken, runtimeField.RepresentedField.ToFieldDescriptor());
                    break;
                }

                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            // a class where a type handle (Type.GetTypeFromHandle's argument) or a Type is wanted is typeof(T)
            case RuntimeClassTypeAnalysisContext { RepresentedType: { } handled } when expectedType?.FullName is "System.RuntimeTypeHandle" or "System.Type":
                instructions.Add(CilOpCodes.Ldtoken, handled.ToTypeSignature().ToTypeDefOrRef());
                if (expectedType.FullName == "System.Type")
                {
                    var scope = module.CorLibTypeFactory.CorLibScope;
                    instructions.Add(CilOpCodes.Call, scope.CreateTypeReference("System", "Type").CreateMemberReference("GetTypeFromHandle", MethodSignature.CreateStatic(
                        scope.CreateTypeReference("System", "Type").ToTypeSignature(false), [scope.CreateTypeReference("System", "RuntimeTypeHandle").ToTypeSignature(true)])));
                }
                break;
            case RuntimeClassTypeAnalysisContext or RgctxTableTypeAnalysisContext
                or MethodRgctxTableTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext:
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case TypeAnalysisContext type:
                //typeof(T)
                var corLibScope = module.CorLibTypeFactory.CorLibScope;
                var typeFromHandle = corLibScope
                    .CreateTypeReference("System", "Type")
                    .CreateMemberReference("GetTypeFromHandle", MethodSignature.CreateStatic(
                        corLibScope.CreateTypeReference("System", "Type").ToTypeSignature(false),
                        [corLibScope.CreateTypeReference("System", "RuntimeTypeHandle").ToTypeSignature(true)]));

                instructions.Add(CilOpCodes.Ldtoken, type.ToTypeSignature().ToTypeDefOrRef());
                instructions.Add(CilOpCodes.Call, typeFromHandle);
                break;
            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unknown operand: " + operand));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Ldnull);
                break;
        }
    }
    
    private static bool TryEmitExactTypeComparison(Instruction instruction, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var left = instruction.Operands[1];
        var right = instruction.Operands[2];

        IOperand typeOperand;
        LocalVariable objLocal;

        if (left is TypeAnalysisContext && IsKlassPointerLoad(right, out var rightLocal))
            (typeOperand, objLocal) = (left, rightLocal);
        else if (right is TypeAnalysisContext && IsKlassPointerLoad(left, out var leftLocal))
            (typeOperand, objLocal) = (right, leftLocal);
        else
            return false;

        var module = method.DeclaringModule!;
        var instructions = method.CilMethodBody!.Instructions;

        var getType = module.CorLibTypeFactory.CorLibScope
            .CreateTypeReference("System", "Object")
            .CreateMemberReference("GetType", MethodSignature.CreateInstance(
                module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "Type").ToTypeSignature(false)));

        LoadLocal(objLocal, method, locals);
        instructions.Add(CilOpCodes.Callvirt, getType);
        LoadOperand(typeOperand, method, locals, writeLine); // emits typeof(T)
        instructions.Add(CilOpCodes.Ceq);

        if (instruction.OpCode == OpCode.CheckNotEqual)
        {
            instructions.Add(CilOpCodes.Ldc_I4_0);
            instructions.Add(CilOpCodes.Ceq);
        }

        StoreToOperand(instruction.Operands[0], method, locals, writeLine);
        return true;
    }
    
    private static bool IsKlassPointerLoad(IOperand operand, out LocalVariable local)
    {
        if (operand is MemoryOperand { Index: null, Addend: 0, Scale: 0, Base: LocalVariable { Type.IsValueType: false } baseLocal })
        {
            local = baseLocal;
            return true;
        }

        local = null!;
        return false;
    }

    private static void PushDefaultOf(TypeAnalysisContext type, CilInstructionCollection instructions)
    {
        //TODO Remove this, we should be handling arguments correctly in ISIL resolution, this is a hack to emit balanced stacks.
        //TODO At the *very* least we should emit a console.writeline saying that we did this.
        if (!type.IsValueType)
        {
            instructions.Add(CilOpCodes.Ldnull);
            return;
        }

        switch (type.FullName)
        {
            case "System.Single": instructions.Add(CilOpCodes.Ldc_R4, 0f); break;
            case "System.Double": instructions.Add(CilOpCodes.Ldc_R8, 0d); break;
            case "System.Int64" or "System.UInt64": instructions.Add(CilOpCodes.Ldc_I8, 0L); break;
            default: instructions.Add(CilOpCodes.Ldc_I4_0); break;
        }
    }

    private static bool IsBoolean(IOperand operand, MethodAnalysisContext context) =>
        operand is LocalVariable { Type: { } type } && type == context.AppContext.SystemTypes.SystemBooleanType;

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };
    
    private enum NumericKind { None, Int32, Int64, Single, Double }

    private static NumericKind KindOf(TypeAnalysisContext? type) => type?.FullName switch
    {
        "System.Single" => NumericKind.Single,
        "System.Double" => NumericKind.Double,
        "System.Int64" or "System.UInt64" => NumericKind.Int64,
        "System.Int32" or "System.UInt32" or "System.Int16" or "System.UInt16" or "System.Byte" or "System.SByte" or "System.Char" => NumericKind.Int32,
        _ => NumericKind.None
    };

    private static TypeAnalysisContext? SourceType(IOperand source, MethodAnalysisContext context) => source switch
    {
        LocalVariable local => local.Type,
        FieldReference field => field.Field.FieldType,
        FloatLiteral => context.AppContext.SystemTypes.SystemSingleType,
        DoubleLiteral => context.AppContext.SystemTypes.SystemDoubleType,
        Immediate { Value: >= int.MinValue and <= int.MaxValue } => context.AppContext.SystemTypes.SystemInt32Type,
        Immediate => context.AppContext.SystemTypes.SystemInt64Type,
        _ => null
    };

    // The lifter treats cvtsi2ss/cvtss2sd/etc as moves, and integer zero as the float zero, so a move between
    // numeric types of different kinds needs the conversion making explicit
    private static CilOpCode? NumericConversion(TypeAnalysisContext? from, TypeAnalysisContext? to)
    {
        var source = KindOf(from);
        var destination = KindOf(to);

        if (source == NumericKind.None || destination == NumericKind.None || source == destination)
            return null;

        return destination switch
        {
            NumericKind.Single => CilOpCodes.Conv_R4,
            NumericKind.Double => CilOpCodes.Conv_R8,
            NumericKind.Int32 when source is NumericKind.Single or NumericKind.Double => CilOpCodes.Conv_I4,
            NumericKind.Int64 => CilOpCodes.Conv_I8,
            _ => null
        };
    }

    private static TypeAnalysisContext? DestinationType(IOperand destination) =>
        destination switch
        {
            LocalVariable local => local.Type,
            FieldReference field => field.Field.FieldType,
            ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } => array.ElementType,
            // a store through a managed pointer writes its referent
            MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable { Type: ByRefTypeAnalysisContext { ElementType: { } referent } } } => referent,
            _ => null
        };

    /// <summary>
    /// Pushes whatever a stfld of <paramref name="field"/>'s innermost field needs underneath the value: the
    /// object reference, or the address of the struct holding it. Returns true if the store is instead a stsfld
    /// (a direct static field, which needs nothing pushed).
    /// </summary>
    private static bool LoadFieldContainer(FieldReference field, MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals)
    {
        var instructions = method.CilMethodBody!.Instructions;
        var chain = field.Chain.ToList();

        if (chain.Count == 1 && chain[0].IsStatic)
            return true;

        if (chain[0].IsStatic)
            instructions.Add(CilOpCodes.Ldsflda, chain[0].ToFieldDescriptor());
        else
        {
            // Writing into a struct needs its address, not a copy of it
            if (field.Local.Type is { IsValueType: true } and not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext))
                LoadLocalAddress(field.Local, method, locals);
            else
                LoadLocal(field.Local, method, locals);

            if (chain.Count > 1)
                instructions.Add(CilOpCodes.Ldflda, chain[0].ToFieldDescriptor());
        }

        for (var i = 1; i < chain.Count - 1; i++)
            instructions.Add(CilOpCodes.Ldflda, chain[i].ToFieldDescriptor());

        return false;
    }

    private static void StoreLocal(LocalVariable local, MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals)
    {
        var instructions = method.CilMethodBody!.Instructions;

        if (local.IsThis)
        {
            // Assigning to 'this' only makes sense in a struct, where it means overwriting the value
            if (method.DeclaringType is { IsValueType: true } declaringType)
            {
                var thisValue = new CilLocalVariable(declaringType.ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(thisValue);
                instructions.Add(CilOpCodes.Stloc, thisValue);
                instructions.Add(CilOpCodes.Ldarg_0);
                instructions.Add(CilOpCodes.Ldloc, thisValue);
                instructions.Add(CilOpCodes.Stobj, declaringType);
            }
            else
                instructions.Add(CilOpCodes.Starg, method.Parameters.ThisParameter!);
            return;
        }

        var parameter = method.Parameters.FirstOrDefault(p => p.Name == local.Name);

        if (parameter != null)
            instructions.Add(CilOpCodes.Starg, parameter);
        else
            instructions.Add(CilOpCodes.Stloc, locals[local]);
    }

    // The address of a (possibly nested) field: ldflda/ldsflda down the chain
    private static void LoadFieldAddress(FieldReference field, MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals)
    {
        var instructions = method.CilMethodBody!.Instructions;
        var chain = field.Chain.ToList();

        if (chain[0].IsStatic)
            instructions.Add(CilOpCodes.Ldsflda, chain[0].ToFieldDescriptor());
        else
        {
            if (field.Local.Type is { IsValueType: true } and not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext))
                LoadLocalAddress(field.Local, method, locals);
            else
                LoadLocal(field.Local, method, locals);

            instructions.Add(CilOpCodes.Ldflda, chain[0].ToFieldDescriptor());
        }

        for (var i = 1; i < chain.Count; i++)
            instructions.Add(CilOpCodes.Ldflda, chain[i].ToFieldDescriptor());
    }

    private static void LoadLocalAddress(LocalVariable local, MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals)
    {
        var instructions = method.CilMethodBody!.Instructions;

        if (local.IsThis)
        {
            instructions.Add(CilOpCodes.Ldarg_0); // a value type's 'this' is already a managed pointer
            return;
        }

        var parameter = method.Parameters.FirstOrDefault(p => p.Name == local.Name);

        if (parameter != null)
            instructions.Add(CilOpCodes.Ldarga, parameter);
        else
            instructions.Add(CilOpCodes.Ldloca, locals[local]);
    }

    private static void LoadLocal(LocalVariable local, MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals)
    {
        var instructions = method.CilMethodBody!.Instructions;

        if (local.IsThis)
        {
            instructions.Add(CilOpCodes.Ldarg_0);
            return;
        }

        var parameter = method.Parameters.FirstOrDefault(p => p.Name == local.Name);

        if (parameter != null)
            instructions.Add(CilOpCodes.Ldarg, parameter);
        else
            instructions.Add(CilOpCodes.Ldloc, locals[local]);
    }

    private static void StoreToOperand(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var instructions = method.CilMethodBody!.Instructions;

        switch (operand)
        {
            case LocalVariable local:
                StoreLocal(local, method, locals);
                break;

            case FieldReference field:
                var fieldDescriptor = field.Field.ToFieldDescriptor();

                if (field.Field.IsStatic && field.Path.Count == 0)
                {
                    instructions.Add(CilOpCodes.Stsfld, fieldDescriptor);
                    break;
                }

                // stfld wants the object underneath the value, but the value is already on the stack, so
                // park it in a temporary while we load the object.
                var scratch = new CilLocalVariable(fieldDescriptor.Signature!.FieldType);
                method.CilMethodBody!.LocalVariables.Add(scratch);

                instructions.Add(CilOpCodes.Stloc, scratch);
                var isStaticStore = LoadFieldContainer(field, method, locals);
                instructions.Add(CilOpCodes.Ldloc, scratch);
                instructions.Add(isStaticStore ? CilOpCodes.Stsfld : CilOpCodes.Stfld, fieldDescriptor);
                break;

            case ArrayAccess arrayAccess:
                // stelem needs array and index before the value, so the same trick as stfld
                var elementType = ((SzArrayTypeAnalysisContext)arrayAccess.Array.Type!).ElementType;
                var elementScratch = new CilLocalVariable(elementType.ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(elementScratch);

                instructions.Add(CilOpCodes.Stloc, elementScratch);
                LoadLocal(arrayAccess.Array, method, locals);
                LoadOperand(arrayAccess.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldloc, elementScratch);
                instructions.Add(CilOpCodes.Stelem, elementType.ToTypeSignature().ToTypeDefOrRef());
                break;

            case MemoryOperand memory:
                if (memory.Index == null && memory.Addend == 0 && memory.Scale == 0
                    && memory.Base is LocalVariable local2)
                {
                    // A store through a managed pointer writes the referent, not the pointer
                    if (local2.Type is ByRefTypeAnalysisContext { ElementType: { } storedReferent })
                    {
                        var storedValue = new CilLocalVariable(storedReferent.ToTypeSignature());
                        method.CilMethodBody!.LocalVariables.Add(storedValue);
                        instructions.Add(CilOpCodes.Stloc, storedValue);
                        LoadLocal(local2, method, locals);
                        instructions.Add(CilOpCodes.Ldloc, storedValue);
                        instructions.Add(storedReferent.IsValueType || storedReferent is GenericParameterTypeAnalysisContext
                            ? new CilInstruction(CilOpCodes.Stobj, storedReferent.ToTypeSignature().ToTypeDefOrRef())
                            : new CilInstruction(CilOpCodes.Stind_Ref));
                        break;
                    }

                    // Can pointer assignments just be ignored because it's C#? (Move [local], 123)
                    StoreLocal(local2, method, locals);
                    break;
                }
                instructions.Add(CilOpCodes.Pop);
                break;

            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Store into unknown operand: {operand}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Pop);
                break;
        }
    }

    private static bool MentionsGenericParameter(TypeSignature signature, int depth) => depth < 8 && signature switch
    {
        GenericParameterSignature => true,
        GenericInstanceTypeSignature instance => instance.TypeArguments.Any(a => MentionsGenericParameter(a, depth + 1)),
        TypeSpecificationSignature specification => MentionsGenericParameter(specification.BaseType, depth + 1),
        _ => false
    };
}
