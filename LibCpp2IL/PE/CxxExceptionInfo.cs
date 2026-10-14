using System;
using System.Collections.Generic;

namespace LibCpp2IL.PE;

/// <summary>
/// The C++ exception handling tables MSVC x64 emits for a function using <c>__CxxFrameHandler4</c> (FH4): which try
/// blocks it has, which states its code is in, and the catch funclets that handle each try block. Addresses are
/// virtual addresses.
/// </summary>
public sealed class CxxExceptionInfo
{
    public ulong FunctionStart;
    public ulong FunctionEnd;

    /// <summary>The frame register the function establishes (0 for none, so its frame is rsp after the prolog), and its offset from rsp.</summary>
    public int FrameRegister, FrameOffset;

    /// <summary>The EH state each address range of the function is in, as (start address, state); -1 is outside every try block.</summary>
    public List<(ulong Address, int State)> IpStates = [];

    public List<CxxTryBlock> TryBlocks = [];

    /// <summary>The state the instruction at the given address is in.</summary>
    public int StateAt(ulong address)
    {
        var state = -1;
        foreach (var (start, s) in IpStates)
        {
            if (start > address)
                break;
            state = s;
        }

        return state;
    }
}

public sealed class CxxTryBlock
{
    /// <summary>The states covered by the try block, inclusive.</summary>
    public int TryLow, TryHigh;

    /// <summary>The highest state of its catch blocks' code, which is above TryHigh.</summary>
    public int CatchHigh;

    public List<CxxCatchHandler> Handlers = [];

    public bool Covers(int state) => state >= TryLow && state <= TryHigh;
}

public sealed class CxxCatchHandler
{
    public uint Adjectives;

    /// <summary>The RVA of the TypeDescriptor of the caught type, or 0 for catch (...).</summary>
    public int TypeDescriptorRva;

    /// <summary>The establisher frame offset the caught object (or a reference to it) is stored at, if any.</summary>
    public int? CatchObjectOffset;

    public ulong FuncletStart;
    public ulong FuncletEnd;

    /// <summary>Where the function continues after the catch funclet returns; the funclet's return value picks one.</summary>
    public List<ulong> Continuations = [];
}

internal static class CxxExceptionInfoReader
{
    private const int ExceptionDirectory = 3;

    private static readonly byte[] CompressedLength = [1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 1, 5];
    private static readonly byte[] CompressedShift = [25, 18, 25, 11, 25, 18, 25, 4, 25, 18, 25, 11, 25, 18, 25, 0];

    public static (uint Begin, uint End, uint Unwind)? FindRuntimeFunction(PE pe, uint rva)
    {
        var directory = pe.GetDataDirectory(ExceptionDirectory);
        if (directory is not { Size: > 0 })
            return null;

        var table = pe.MapVirtualAddressToRaw(pe.ImageBase + directory.VirtualAddress, false);
        if (table <= 0)
            return null;

        var raw = pe.RawBytes;
        int low = 0, high = (int)(directory.Size / 12);
        while (low < high)
        {
            var middle = (low + high) / 2;
            var entry = (int)table + middle * 12;
            if (entry + 12 > raw.Length)
                return null;

            var begin = BitConverter.ToUInt32(raw, entry);
            var end = BitConverter.ToUInt32(raw, entry + 4);
            if (rva < begin)
                high = middle;
            else if (rva >= end)
                low = middle + 1;
            else
                return (begin, end, BitConverter.ToUInt32(raw, entry + 8));
        }

        return null;
    }

    public static CxxExceptionInfo? Read(PE pe, ulong address)
    {
        try
        {
            return ReadUnchecked(pe, address);
        }
        catch (Exception e) when (e is ArgumentException or IndexOutOfRangeException or OverflowException)
        {
            return null; // not tables we understand
        }
    }

    private static CxxExceptionInfo? ReadUnchecked(PE pe, ulong address)
    {
        var imageBase = pe.ImageBase;
        if (address < imageBase || pe.is32Bit)
            return null;

        var function = FindRuntimeFunction(pe, (uint)(address - imageBase));
        if (function is not { } runtimeFunction)
            return null;

        var raw = pe.RawBytes;
        int Raw(uint rva)
        {
            var offset = pe.MapVirtualAddressToRaw(imageBase + rva, false);
            if (offset <= 0 || offset >= raw.Length)
                throw new ArgumentException($"RVA 0x{rva:X} isn't in the file");
            return (int)offset;
        }

        // the UNWIND_INFO of a chained entry describes another part of the function, which has the handler
        var unwind = Raw(runtimeFunction.Unwind);
        var frameRegister = raw[unwind + 3] & 0xF;
        var frameOffset = (raw[unwind + 3] >> 4) * 16;
        for (var chain = 0; (raw[unwind] >> 3 & 4) != 0 && chain < 8; chain++)
        {
            var codes = raw[unwind + 2];
            var parent = unwind + 4 + ((codes + 1) & ~1) * 2;
            unwind = Raw(BitConverter.ToUInt32(raw, parent + 8));
        }

        var flags = raw[unwind] >> 3;
        if ((flags & 3) == 0)
            return null; // no exception or termination handler

        var codeCount = raw[unwind + 2];
        var handlerData = unwind + 4 + ((codeCount + 1) & ~1) * 2 + 4;
        var funcInfoRva = BitConverter.ToUInt32(raw, handlerData);

        var position = Raw(funcInfoRva);
        if ((BitConverter.ToUInt32(raw, position) & 0xFFFFFFF0) == 0x19930520)
            return null; // __CxxFrameHandler3's FuncInfo

        var header = raw[position++];

        // isSeparated: the ip-to-state map is per funclet; BBT: rewritten by a profile optimiser. Both are laid out differently.
        if ((header & 0b110) != 0)
            return null;

        int ReadInt(ref int at)
        {
            var value = BitConverter.ToInt32(raw, at);
            at += 4;
            return value;
        }

        uint ReadCompressed(ref int at)
        {
            var low = raw[at] & 0xF;
            var length = CompressedLength[low];
            var value = BitConverter.ToUInt32(raw, at + length - 4) >> CompressedShift[low];
            at += length;
            return value;
        }

        if ((header & 0x08) != 0)
            ReadInt(ref position); // the unwind map: destructors to run, which IL2CPP code doesn't have
        var tryBlockMap = (header & 0x10) != 0 ? ReadInt(ref position) : 0;
        var ipToStateMap = ReadInt(ref position);

        var info = new CxxExceptionInfo
        {
            FunctionStart = imageBase + runtimeFunction.Begin,
            FunctionEnd = imageBase + runtimeFunction.End,
            FrameRegister = frameRegister,
            FrameOffset = frameOffset,
        };

        var map = Raw((uint)ipToStateMap);
        var entries = ReadCompressed(ref map);
        var current = (ulong)runtimeFunction.Begin;
        for (var i = 0; i < entries; i++)
        {
            current += ReadCompressed(ref map);
            var state = (int)ReadCompressed(ref map) - 1;
            if (current >= runtimeFunction.End || state < -1)
                return null; // not an FH4 map after all
            info.IpStates.Add((imageBase + current, state));
        }

        if (tryBlockMap == 0)
            return info;

        var tryPosition = Raw((uint)tryBlockMap);
        var tryCount = ReadCompressed(ref tryPosition);
        for (var i = 0; i < tryCount; i++)
        {
            var tryBlock = new CxxTryBlock
            {
                TryLow = (int)ReadCompressed(ref tryPosition),
                TryHigh = (int)ReadCompressed(ref tryPosition),
                CatchHigh = (int)ReadCompressed(ref tryPosition),
            };
            var handlerMap = ReadInt(ref tryPosition);

            var handlerPosition = Raw((uint)handlerMap);
            var handlerCount = ReadCompressed(ref handlerPosition);
            for (var j = 0; j < handlerCount; j++)
            {
                var handlerFlags = raw[handlerPosition++];
                var handler = new CxxCatchHandler();
                if ((handlerFlags & 0x01) != 0)
                    handler.Adjectives = ReadCompressed(ref handlerPosition);
                if ((handlerFlags & 0x02) != 0)
                    handler.TypeDescriptorRva = ReadInt(ref handlerPosition);
                if ((handlerFlags & 0x04) != 0)
                    handler.CatchObjectOffset = (int)ReadCompressed(ref handlerPosition);

                var funclet = (uint)ReadInt(ref handlerPosition);
                handler.FuncletStart = imageBase + funclet;
                handler.FuncletEnd = FindRuntimeFunction(pe, funclet) is { } funcletFunction && funcletFunction.Begin == funclet
                    ? imageBase + funcletFunction.End
                    : 0;

                var continuationCount = handlerFlags >> 4 & 3;
                for (var k = 0; k < continuationCount; k++)
                {
                    if ((handlerFlags & 0x08) != 0)
                        handler.Continuations.Add(imageBase + (uint)ReadInt(ref handlerPosition));
                    else
                        handler.Continuations.Add(imageBase + runtimeFunction.Begin + ReadCompressed(ref handlerPosition));
                }

                if (handler.Continuations.Exists(c => c < info.FunctionStart || c >= info.FunctionEnd))
                    return null;

                tryBlock.Handlers.Add(handler);
            }

            info.TryBlocks.Add(tryBlock);
        }

        return info;
    }
}
