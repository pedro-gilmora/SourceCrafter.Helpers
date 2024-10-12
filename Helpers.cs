using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Collections.ObjectModel;
using System.ComponentModel;
using System.Linq;
using System.Reflection.Metadata;
using System.Runtime.CompilerServices;
using System.Text;
using System.Xml.Linq;

using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

using SourceCrafter.DependencyInjection.Interop;

using static SourceCrafter.DependencyInjection.Interop.ServiceDescriptor;

namespace SourceCrafter.DependencyInjection
{
    public static class Extensions
    {
        internal readonly static SymbolDisplayFormat
            _globalizedNamespace = new(
                memberOptions:
                    SymbolDisplayMemberOptions.IncludeType |
                    SymbolDisplayMemberOptions.IncludeModifiers |
                    SymbolDisplayMemberOptions.IncludeExplicitInterface |
                    SymbolDisplayMemberOptions.IncludeParameters |
                    SymbolDisplayMemberOptions.IncludeContainingType |
                    SymbolDisplayMemberOptions.IncludeConstantValue |
                    SymbolDisplayMemberOptions.IncludeRef,
                globalNamespaceStyle:
                    SymbolDisplayGlobalNamespaceStyle.Included,
                typeQualificationStyle:
                    SymbolDisplayTypeQualificationStyle.NameAndContainingTypesAndNamespaces,
                genericsOptions:
                    SymbolDisplayGenericsOptions.IncludeTypeParameters |
                    SymbolDisplayGenericsOptions.IncludeVariance,
                miscellaneousOptions:
                    SymbolDisplayMiscellaneousOptions.UseSpecialTypes |
                    SymbolDisplayMiscellaneousOptions.IncludeNullableReferenceTypeModifier,
                parameterOptions:
                    SymbolDisplayParameterOptions.IncludeType |
                    SymbolDisplayParameterOptions.IncludeModifiers |
                    SymbolDisplayParameterOptions.IncludeName |
                    SymbolDisplayParameterOptions.IncludeDefaultValue),
            _globalizedNonGenericNamespace = new(
                globalNamespaceStyle: SymbolDisplayGlobalNamespaceStyle.Included,
                typeQualificationStyle: SymbolDisplayTypeQualificationStyle.NameAndContainingTypesAndNamespaces,
                miscellaneousOptions: SymbolDisplayMiscellaneousOptions.UseSpecialTypes),
            _symbolNameOnly = new(typeQualificationStyle: SymbolDisplayTypeQualificationStyle.NameOnly),
            _typeNameFormat = new(
                typeQualificationStyle: SymbolDisplayTypeQualificationStyle.NameAndContainingTypes,
                genericsOptions: SymbolDisplayGenericsOptions.IncludeTypeParameters | SymbolDisplayGenericsOptions.IncludeVariance,
                miscellaneousOptions: SymbolDisplayMiscellaneousOptions.UseSpecialTypes | SymbolDisplayMiscellaneousOptions.IncludeNullableReferenceTypeModifier);

        public static string ToGlobalNamespaced(this ISymbol t) => t.ToDisplayString(_globalizedNamespace);

        public static string ToGlobalNonGenericNamespace(this ISymbol t) => t.ToDisplayString(_globalizedNonGenericNamespace);

        public static string ToTypeNameFormat(this ITypeSymbol t) => t.ToDisplayString(_typeNameFormat);

        public static string ToNameOnly(this ISymbol t) => t.ToDisplayString(_symbolNameOnly);
        public static bool TryGetDependencyInfo(
            this SemanticModel model,
            AttributeData attrData,
            ref bool isExternal,
            out DependencySlimInfo depInfo,
            string key = "",
            ITypeSymbol? fallbackType = null)
        {
            depInfo = default;

            if (attrData is { AttributeClass: { } attrClass, ApplicationSyntaxReference: { } attrSyntaxRef } 
                && attrSyntaxRef.GetSyntax() is AttributeSyntax { ArgumentList.Arguments: var attrArgsSyntax } attrSyntax
                && model.GetSymbolInfo(attrSyntax).Symbol is IMethodSymbol{ Parameters: var attrParams }
                && !attrClass.Name.Equals("ServiceContainer")
                && GetLifetimeFromCtor(ref attrClass, ref isExternal, attrSyntax) is { } lifetime)
            {
                depInfo.Lifetime = lifetime;

                if (attrData.AttributeClass!.TypeArguments.Length > 0 is { } isGeneric)
                {
                    switch (attrClass!.TypeArguments)
                    {
                        case [{ } t1, { } t2, ..]:
                            
                            depInfo.IFaceType = t1; 
                            depInfo.ImplType = t2; 

                            break;

                        case [{ } t1]: 

                            depInfo.ImplType = t1;
                            
                            break;
                    }
                }

                foreach (var (param, arg) in GetAttrParamsMap(attrParams, attrArgsSyntax))
                {
                    switch (param.Name)
                    {
                        case ImplParamName when !isGeneric && arg is { Expression: TypeOfExpressionSyntax { Type: { } type } }:

                            depInfo.ImplType = (ITypeSymbol)model!.GetSymbolInfo(type).Symbol!;

                            continue;

                        case IfaceParamName when !isGeneric && arg is { Expression: TypeOfExpressionSyntax { Type: { } type } }:

                            depInfo.IFaceType = (ITypeSymbol)model!.GetSymbolInfo(type).Symbol!;

                            continue;

                        case KeyParamName when GetStrExpressionOrValue(model, param!, arg) is { } keyValue:

                            depInfo.Key = keyValue;

                            continue;

                        case NameFormatParamName when GetStrExpressionOrValue(model, param, arg) is { } nameOrValue:

                            depInfo.NameFormat = nameOrValue;

                            continue;

                        case FactoryOrInstanceParamName

                            when arg?.Expression is InvocationExpressionSyntax
                            {
                                Expression: IdentifierNameSyntax { Identifier.ValueText: "nameof" },
                                ArgumentList.Arguments: [{ } methodRef]
                            }:

                            switch (model.GetSymbolInfo(methodRef.Expression))
                            {
                                case { Symbol: (IFieldSymbol or IPropertySymbol) and { IsStatic: true, Kind: { } kind } fieldOrProp }:
                                    depInfo.Factory = fieldOrProp;
                                    depInfo.FactoryKind = kind;
                                    break;

                                case { CandidateReason: CandidateReason.MemberGroup, CandidateSymbols: [IMethodSymbol { ReturnsVoid: false, IsStatic: true } method] }:
                                    depInfo.Factory = method;
                                    depInfo.FactoryKind = SymbolKind.Method;
                                    depInfo.DefaultParamValues = method.Parameters;
                                    break;
                            }

                            continue;

                        case "disposability" when param.HasExplicitDefaultValue:

                            depInfo.Disposability = (Disposability)(byte)param.ExplicitDefaultValue!;

                            continue;
                    }
                }

                depInfo.FinalType = depInfo.FactoryKind switch
                {
                    SymbolKind.Method => ((IMethodSymbol)depInfo.Factory!).ReturnType,
                    SymbolKind.Field => ((IFieldSymbol)depInfo.Factory!).Type,
                    SymbolKind.Property => ((IPropertySymbol)depInfo.Factory!).Type,
                    _ => depInfo.IFaceType ?? depInfo.ImplType ?? fallbackType!
                };

                if (fallbackType is { TypeKind: not TypeKind.Interface }) depInfo.ImplType ??= fallbackType;

                depInfo.Key ??= key ?? "";

                return depInfo is { FinalType: not null, ImplType: not null };
            }
            return false;
        }

        static IEnumerable<(IParameterSymbol, AttributeArgumentSyntax?)> GetAttrParamsMap(
            ImmutableArray<IParameterSymbol> paramSymbols,
            SeparatedSyntaxList<AttributeArgumentSyntax> argsSyntax)
        {
            int i = 0;
            foreach (var param in paramSymbols)
            {
                if (argsSyntax.Count > i && argsSyntax[i] is { NameColon: null, NameEquals: null } argSyntax)
                {
                    yield return (param, argSyntax);
                }
                else
                {
                    yield return (param, argsSyntax.FirstOrDefault(arg => param.Name == arg.NameColon?.Name.Identifier.ValueText));
                }

                i++;
            }
        }

        private static string? GetStrExpressionOrValue(SemanticModel model, IParameterSymbol paramSymbol, AttributeArgumentSyntax? arg)
        {
            if (arg is not null)
            {
                if (model.GetSymbolInfo(arg.Expression).Symbol is IFieldSymbol
                    {
                        IsConst: true,
                        Type.SpecialType: SpecialType.System_String,
                        ConstantValue: { } val
                    })
                {
                    return val.ToString();
                }
                else if (arg.Expression is LiteralExpressionSyntax { Token.ValueText: { } value } e
                    && e.IsKind(SyntaxKind.StringLiteralExpression))
                {
                    return value;
                }
            }
            else if (paramSymbol.HasExplicitDefaultValue)
            {
                return paramSymbol.ExplicitDefaultValue?.ToString();
            }

            return null;
        }


        public static Lifetime? GetLifetimeFromCtor(ref INamedTypeSymbol attrClass, ref bool isExternal, AttributeSyntax attrSyntax)
        {
            var lifetime = GetLifetimeFromSyntax(attrSyntax);

            if (lifetime.HasValue) return lifetime.Value;

            do
            {
                (isExternal, lifetime) = attrClass.ToGlobalNonGenericNamespace() switch
                {
                    SingletonAttr => (isExternal, Lifetime.Singleton),
                    ScopedAttr => (isExternal, Lifetime.Scoped),
                    TransientAttr => (isExternal, Lifetime.Transient),
                    { } val => (val is not DependencyAttr, GetFromCtorSymbol(attrClass))
                };

                if (lifetime.HasValue) return lifetime.Value;

                isExternal = true;
            }
            while ((attrClass = attrClass?.BaseType!) is not null);

            return null;

            static Lifetime? GetFromCtorSymbol(INamedTypeSymbol attrClass)
            {
                foreach (var ctor in attrClass.Constructors)
                    foreach (var param in ctor.Parameters)
                        if (param.Name is "lifetime" && param.HasExplicitDefaultValue)
                            return (Lifetime)(byte)param.ExplicitDefaultValue!;

                return null;
            }

            static Lifetime? GetLifetimeFromSyntax(AttributeSyntax attribute)
            {
                if (attribute.ArgumentList?.Arguments
                        .FirstOrDefault(x => x.NameColon?.Name.Identifier.ValueText is "lifetime")?.Expression is MemberAccessExpressionSyntax { Name.Identifier.ValueText: { } memberName }
                    && Enum.TryParse(memberName, out Lifetime lifetime))
                {
                    return lifetime;
                }

                return null;
            }
        }



        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static string ToMetadataLongName(this ISymbol symbol)
        {
            var ret = new StringBuilder();

            foreach (var part in symbol.ToDisplayParts(_typeNameFormat))
            {
                if (part.Symbol is { Name: string name })
                    ret.Append(name.Capitalize());
                else
                    switch (part.ToString())
                    {
                        case ",": ret.Append("And"); break;
                        case "<": ret.Append("Of"); break;
                        case "[": ret.Append("Array"); break;
                    }
            }

            return ret.ToString();
        }

        public static string ToMetadataLongName(this ISymbol symbol, Map<string, byte> uniqueName)
        {
            var e = ToMetadataLongName(symbol);

            ref var count = ref uniqueName.GetValueOrAddDefault(e, out var exists);

            if (exists)
            {
                return e + "_" + (++count);
            }

            return e;
        }

        public static string Capitalize(this string str)
        {
            return (str is [{ } f, .. { } rest] ? char.ToUpper(f) + rest : str);
        }

        public static string Camelize(this string str)
        {
            return (str is [{ } f, .. { } rest] ? char.ToLower(f) + rest : str);
        }

        public static string? Pascalize(this string str)
        {
            if (string.IsNullOrEmpty(str))
                return str;

            ReadOnlySpan<char> span = str.AsSpan();
            Span<char> result = stackalloc char[span.Length];
            int resultIndex = 0;
            bool newWord = true;

            foreach (char c in span)
            {
                if (char.IsWhiteSpace(c) || c == '-' || c == '_')
                {
                    newWord = true;
                }
                else
                {
                    if (newWord)
                    {
                        result[resultIndex++] = char.ToUpperInvariant(c);
                        newWord = false;
                    }
                    else
                    {
                        result[resultIndex++] = c;
                    }
                }
            }

            return result[0..resultIndex].ToString();
        }

        public static ImmutableArray<IParameterSymbol>? GetParameters(DependencySlimInfo depInfo)
        {
            return depInfo.ImplType is INamedTypeSymbol { Constructors: var ctor, InstanceConstructors: var insCtor }
                ? ctor.OrderBy(d => !d.Parameters.IsDefaultOrEmpty).FirstOrDefault()?.Parameters
                    ?? insCtor.OrderBy(d => !d.Parameters.IsDefaultOrEmpty).FirstOrDefault()?.Parameters
                    ?? []
                : [];
        }

        public static bool IsPrimitive(this ITypeSymbol target, bool includeObject = true) =>
            (includeObject && target.SpecialType is SpecialType.System_Object)
                || target.SpecialType is SpecialType.System_Enum
                    or SpecialType.System_Boolean
                    or SpecialType.System_Byte
                    or SpecialType.System_SByte
                    or SpecialType.System_Char
                    or SpecialType.System_DateTime
                    or SpecialType.System_Decimal
                    or SpecialType.System_Double
                    or SpecialType.System_Int16
                    or SpecialType.System_Int32
                    or SpecialType.System_Int64
                    or SpecialType.System_Single
                    or SpecialType.System_UInt16
                    or SpecialType.System_UInt32
                    or SpecialType.System_UInt64
                    or SpecialType.System_String
                || target.Name is "DateTimeOffset" or "Guid"
                || (target.SpecialType is SpecialType.System_Nullable_T
                    && IsPrimitive(((INamedTypeSymbol)target).TypeArguments[0]));

        public static ITypeSymbol AsNonNullable(this ITypeSymbol type) =>
            type.Name == "Nullable"
                ? ((INamedTypeSymbol)type).TypeArguments[0]
                : type.WithNullableAnnotation(NullableAnnotation.None);

        public static void TryGetNullable(this ITypeSymbol type, out ITypeSymbol outType, out bool outIsNullable)
                    => (outType, outIsNullable) = type.SpecialType is SpecialType.System_Nullable_T
                        || type is INamedTypeSymbol { Name: "Nullable" }
                            ? (((INamedTypeSymbol)type).TypeArguments[0], true)
                            : type.NullableAnnotation == NullableAnnotation.Annotated
                                ? (type.WithNullableAnnotation(NullableAnnotation.None), true)
                                : (type, false);

        public static bool IsNullable(this ITypeSymbol typeSymbol)
            => typeSymbol.SpecialType is SpecialType.System_Nullable_T
                || typeSymbol.NullableAnnotation == NullableAnnotation.Annotated
                || typeSymbol is INamedTypeSymbol { Name: "Nullable" };

        public static bool AllowsNull(this ITypeSymbol typeSymbol)
            => typeSymbol is { IsValueType: false, IsTupleType: false, IsReferenceType: true };

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static string Wordify(this string identifier, short upper = 0)
            => ToJoined(identifier, " ", upper);

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static StringBuilder AddSpace(this StringBuilder sb, int count = 1) => sb.Append(new string(' ', count));

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static StringBuilder CaptureGeneratedString(this StringBuilder code, Action action, out string expression)
        {
            int start = code.Length, end;
            action();
            end = code.Length;
            char[] e = new char[end - start];
            code.CopyTo(start, e, 0, end - start);
            expression = new(e, 0, e.Length);
            return code;
        }

        public static string ToJoined(string identifier, string separator = "-", short casing = 0)
        {
            var buffer = new char[identifier.Length * (separator.Length + 1)];
            var bufferIndex = 0;

            for (int i = 0; i < identifier.Length; i++)
            {
                char ch = identifier[i];
                bool isLetterOrDigit = char.IsLetterOrDigit(ch), isUpper = char.IsUpper(ch);

                if (i > 0 && isUpper && char.IsLower(identifier[i - 1]))
                {
                    separator.CopyTo(0, buffer, bufferIndex, separator.Length);
                    bufferIndex += separator.Length;
                }
                if (isLetterOrDigit)
                {
                    buffer[bufferIndex++] = (casing, isUpper) switch
                    {
                        (1, false) => char.ToUpperInvariant(ch),
                        (-1, true) => char.ToLowerInvariant(ch),
                        _ => ch
                    };
                }
            }
            return new string(buffer, 0, bufferIndex);
        }

        public static bool TryGetAsyncType(this ITypeSymbol? typeSymbol, out ITypeSymbol? factoryType)
        {
            switch ((factoryType = typeSymbol)?.ToGlobalNonGenericNamespace())
            {
                case "global::System.Threading.Tasks.ValueTask" or "global::System.Threading.Tasks.Task"
                    when factoryType is INamedTypeSymbol { TypeArguments: [{ } firstTypeArg] }:

                    factoryType = firstTypeArg;
                    return true;

                default:

                    return false;
            };
        }

        public static Disposability GetDisposability(this ITypeSymbol type)
        {
            if (type is null) return Disposability.None;

            Disposability disposability = Disposability.None;

            foreach (var iFace in type.AllInterfaces)
            {
                switch (iFace.ToGlobalNonGenericNamespace())
                {
                    case "global::System.IDisposable" when disposability is Disposability.None:
                        disposability = Disposability.Disposable;
                        break;
                    case "global::System.IAsyncDisposable" when disposability < Disposability.AsyncDisposable:
                        return Disposability.AsyncDisposable;
                }
            }

            return disposability;
        }

        public static string RemoveDuplicates(this string? input)
        {
            if ((input = input?.Trim()) is null or "")
                return "";

            var result = "";
            int wordStart = 0;

            for (int i = 1; i < input.Length; i++)
            {
                if (char.IsUpper(input[i]))
                {
                    string word = input[wordStart..i];

                    if (!result.EndsWith(word))
                    {
                        result += word;
                    }

                    wordStart = i;
                }
            }

            string lastWord = input[wordStart..];

            if (!result.EndsWith(lastWord, StringComparison.OrdinalIgnoreCase))
            {
                result += lastWord;
            }

            return result;
        }

        public static string SanitizeTypeName(
            ITypeSymbol type,
            HashSet<string> methodsRegistry,
            DependencyNamesMap dependencyRegistry,
            Lifetime lifeTime,
            string key)
        {
            int hashCode = SymbolEqualityComparer.Default.GetHashCode(type);

            string id = Sanitize(type).Replace(" ", "").Capitalize();

            ref var idOut = ref dependencyRegistry.GetValueOrAddDefault((lifeTime, hashCode, key), out var exists);

            if (exists)
            {
                return idOut!;
            }

            if (key is "")
            {
                if (!methodsRegistry.Add(idOut = id))
                    methodsRegistry.Add(idOut = $"{lifeTime}{id}");
            }
            else if (!(methodsRegistry.Add(idOut = key)
                || methodsRegistry.Add(idOut = $"{key}{id}")
                || methodsRegistry.Add(idOut = $"{lifeTime}{key}")))
            {
                methodsRegistry.Add(idOut = $"{lifeTime}{key}{id}");
            }

            return idOut;

            static string Sanitize(ITypeSymbol type)
            {
                switch (type)
                {
                    case INamedTypeSymbol { IsTupleType: true, TupleElements: { Length: > 0 } els }:

                        return "TupleOf" + string.Join("", els.Select(f => Sanitize(f.Type)));

                    case INamedTypeSymbol { IsGenericType: true, TypeParameters: { } args }:

                        return type.Name + "Of" + string.Join("", args.Select(Sanitize));

                    default:

                        string typeName = type.ToTypeNameFormat();

                        if (type is IArrayTypeSymbol { ElementType: { } elType })
                            typeName = Sanitize(elType) + "Array";

                        return char.ToUpperInvariant(typeName[0]) + typeName[1..].TrimEnd('?', '_');
                };
            }
        }

        public static T Exchange<T>(ref this T oldVal, T newVal) where T : struct =>
                    oldVal.Equals(newVal) ? oldVal : ((oldVal, _) = (newVal, oldVal)).Item2;
    }
}


namespace SourceCrafter.Bindings
{
    public static class CollectionExtensions<T>
    {
        public static Collection<T> EmptyCollection => [];
        public static ReadOnlyCollection<T> EmptyReadOnlyCollection => new([]);
    }
}

#if NETSTANDARD2_0 || NETSTANDARD2_1 || NETCOREAPP2_0 || NETCOREAPP2_1 || NETCOREAPP2_2 || NETCOREAPP3_0 || NETCOREAPP3_1 || NET45 || NET451 || NET452 || NET6 || NET461 || NET462 || NET47 || NET471 || NET472 || NET48


// ReSharper disable once CheckNamespace
namespace System.Runtime.CompilerServices
{
    /// <summary>
    /// Reserved to be used by the compiler for tracking metadata.
    /// This class should not be used by developers in source code.
    /// </summary>
    [EditorBrowsable(EditorBrowsableState.Never)]
    internal static class IsExternalInit
    {
    }
}

#endif