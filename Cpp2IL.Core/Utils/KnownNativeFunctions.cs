using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

/// <summary>
/// Native functions in one specific GameAssembly.dll that stand in for managed methods but can't be matched to them by
/// code: the float CRT math functions MSVC calls when it inlines Mathf.Sin and friends (sinf for (float)sin((double)f)),
/// and out-of-line copies of inlinable methods that were compiled differently from the registered body.
/// Identified by hand. Each entry is guarded by the function's first bytes, so on any other binary nothing matches.
/// </summary>
internal static class KnownNativeFunctions
{
    private sealed record Entry(ulong Address, string Prefix, string Type, string Method, string[] Parameters);

    private static readonly Entry[] Entries =
    [
        new(0x18044CDB0, "833d712ed203000f8483fcff", "UnityEngine.Mathf", "Sin", ["System.Single"]),
        new(0x18044B330, "833df148d203000f8453fdff", "UnityEngine.Mathf", "Cos", ["System.Single"]),
        new(0x18044D4C0, "833d6127d203000f84d3fcff", "UnityEngine.Mathf", "Tan", ["System.Single"]),
        new(0x18044BB80, "4883ec68660f7f742420660f", "UnityEngine.Mathf", "Pow", ["System.Single", "System.Single"]),
        new(0x18044D100, "4883ec580f28d00f57c0f30f", "UnityEngine.Mathf", "Sqrt", ["System.Single"]),
        new(0x18048C0E0, "4883ec38803df24fcc03000f", "UnityEngine.Mathf", "RoundToInt", ["System.Single"]),
        new(0x18000D0D0, "4883ec380f29742420488d54", "UnityEngine.Mathf", "Round", ["System.Single"]),
        new(0x18048C940, "48895c240848897424105748", "UnityEngine.Vector3", "Normalize", ["UnityEngine.Vector3"]),
        new(0x1803BA6D0, "40534883ec20498bd8498bc0", "System.Threading.Interlocked", "CompareExchange", ["System.Object&", "System.Object", "System.Object"]),
    ];

    public static List<MethodAnalysisContext>? Lookup(ApplicationAnalysisContext app, ulong address)
    {
        var entry = Entries.FirstOrDefault(e => e.Address == address);
        if (entry == null)
            return null;

        try
        {
            if (!app.Binary.TryMapVirtualAddressToRaw(address, out var raw))
                return null;

            var expected = Enumerable.Range(0, entry.Prefix.Length / 2).Select(i => Convert.ToByte(entry.Prefix.Substring(i * 2, 2), 16)).ToArray();
            var content = app.Binary.GetRawBinaryContent();
            if (raw < 0 || raw + expected.Length > content.Length || !content.Slice((int)raw, expected.Length).SequenceEqual(expected))
                return null;
        }
        catch
        {
            return null;
        }

        var type = app.AllTypes.FirstOrDefault(t => t.FullName == entry.Type);
        var method = type?.Methods.FirstOrDefault(m => m.Name == entry.Method && m.Parameters.Count == entry.Parameters.Length
                                                           && m.Parameters.Select(p => p.ParameterType.FullName).SequenceEqual(entry.Parameters));
        return method == null ? null : [method];
    }
}
