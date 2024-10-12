
using System.Collections.Generic;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System;
using System.Collections;

namespace SourceCrafter.DependencyInjection.Interop;

public delegate void RefItemResolver<TKey, TVal>(TKey _, ref TVal item);
public class Map<TKey, TVal> : IEnumerable<(TKey, TVal)>
{
    private int[]? _buckets;
    private Entry<TKey, TVal>[]? _entries;
#if TARGET_64BIT
    private ulong _fastModMultiplier;
#endif
    private int _count;
    private int _freeList;
    private int _freeCount;
    private int _version;
    private readonly IEqualityComparer<TKey> _comparer;
    private const int StartOfFreeList = -3;
    public const int HashPrime = 101;
    internal static ReadOnlySpan<int> Primes =>
        [
            3,
            7,
            11,
            17,
            23,
            29,
            37,
            47,
            59,
            71,
            89,
            107,
            131,
            163,
            197,
            239,
            293,
            353,
            431,
            521,
            631,
            761,
            919,
            1103,
            1327,
            1597,
            1931,
            2333,
            2801,
            3371,
            4049,
            4861,
            5839,
            7013,
            8419,
            10103,
            12143,
            14591,
            17519,
            21023,
            25229,
            30293,
            36353,
            43627,
            52361,
            62851,
            75431,
            90523,
            108631,
            130363,
            156437,
            187751,
            225307,
            270371,
            324449,
            389357,
            467237,
            560689,
            672827,
            807403,
            968897,
            1162687,
            1395263,
            1674319,
            2009191,
            2411033,
            2893249,
            3471899,
            4166287,
            4999559,
            5999471,
            7199369
        ];

    public int Count => _count;

    public bool IsEmpty => _count == 0;

    public Map(IEqualityComparer<TKey> comparer)
    {
        _comparer = comparer;
        Initialize(0);
    }

    private int Initialize(int capacity)
    {
        int size = GetPrime(capacity);
        int[] buckets = new int[size];
        var entries = new Entry<TKey, TVal>[size];

        // Assign member variables after both arrays allocated to guard against corruption from OOM if second fails
        _freeList = -1;
#if TARGET_64BIT
            _fastModMultiplier = GetFastModMultiplier((uint)size);
#endif
        _buckets = buckets;
        _entries = entries;

        return size;
    }

    public static int GetPrime(int min)
    {
        if (min < 0)
            throw new ArgumentException("Hashtable's capacity overflowed and went negative. Check load factor, capacity and the current size of the table");

        foreach (int prime in Primes)
        {
            if (prime >= min)
                return prime;
        }

        // Outside of our predefined table. Compute the hard way.
        for (int i = min | 1; i < int.MaxValue; i += 2)
        {
            if (IsPrime(i) && (i - 1) % HashPrime != 0)
                return i;
        }
        return min;
    }

    public static bool IsPrime(int candidate)
    {
        if ((candidate & 1) != 0)
        {
            int limit = (int)Math.Sqrt(candidate);
            for (int divisor = 3; divisor <= limit; divisor += 2)
            {
                if (candidate % divisor == 0)
                    return false;
            }
            return true;
        }
        return candidate == 2;
    }
    // TODO: apply nullability attributes
    public virtual ref TVal? GetValueOrAddDefault(TKey key, out bool exists, Func<TVal>? valueCreator = null)
    {
        Entry<TKey, TVal>[]? entries = _entries!;

        uint hashCode = (uint)_comparer.GetHashCode(key);

        uint collisionCount = 0;
        ref int bucket = ref GetBucket(hashCode);
        int i = bucket - 1; // Value in _buckets is 1-based


        while ((uint)i < (uint)entries.Length)
        {
            if (entries[i].id == hashCode && _comparer.Equals(key, entries[i].Key))
            {
                exists = true;

                return ref entries[i].Value!;
            }

            i = entries[i].next;

            collisionCount++;
            if (collisionCount > (uint)entries.Length)
            {
                // The chain of entries forms a loop; which means a concurrent update has happened.
                // Break out of the loop and throw, rather than looping forever.
                throw new NotSupportedException("Concurrent operations are not allowed");
            }
        }

        int index;
        if (_freeCount > 0)
        {
            index = _freeList;
            Debug.Assert(StartOfFreeList - entries[_freeList].next >= -1, "shouldn't overflow because `next` cannot underflow");
            _freeList = StartOfFreeList - entries[_freeList].next;
            _freeCount--;
        }
        else
        {
            int count = _count;
            if (count == entries.Length)
            {
                Resize();
                bucket = ref GetBucket(hashCode);
            }
            index = count;
            _count = count + 1;
            entries = _entries;
        }

        ref Entry<TKey, TVal> entry = ref entries![index];
        entry.id = hashCode;
        entry.next = bucket - 1; // Value in _buckets is 1-based
        entry.Key = key;
        entry.Value = valueCreator != null ? valueCreator() : default!;
        bucket = index + 1; // Value in _buckets is 1-based
        _version++;

        exists = false;

        return ref entry.Value!;
    }

    public virtual bool TryGetValue(TKey key, out TVal val)
    {
        uint hashCode = (uint)_comparer.GetHashCode(key);
        int i = GetBucket(hashCode);
        var entries = _entries;
        uint collisionCount = 0;
        i--; // Value in _buckets is 1-based; subtract 1 from i. We do it here so it fuses with the following conditional.
        do
        {
            // Test in if to drop range check for following array access
            if ((uint)i >= (uint)entries!.Length)
            {
                val = default!;
                return false;
            }

            ref var entry = ref entries[i];
            if (entry.id == hashCode && _comparer.Equals(entry.Key, key))
            {
                val = entry.Value;
                return true;
            }

            i = entry.next;

            collisionCount++;
        } while (collisionCount <= (uint)entries.Length);

        // The chain of entries forms a loop; which means a concurrent update has happened.
        // Break out of the loop and throw, rather than looping forever.

        val = default!;
        return false;
    }

    public virtual bool Contains(TKey key)
    {
        uint hashCode = (uint)_comparer.GetHashCode(key);
        int i = GetBucket(hashCode);
        var entries = _entries;
        uint collisionCount = 0;
        i--; // Value in _buckets is 1-based; subtract 1 from i. We do it here so it fuses with the following conditional.
        do
        {
            // Test in if to drop range check for following array access
            if ((uint)i >= (uint)entries!.Length)
            {
                return false;
            }

            ref var entry = ref entries[i];
            if (entry.id == hashCode && _comparer.Equals(entry.Key, key))
            {
                return true;
            }

            i = entry.next;

            collisionCount++;
        } while (collisionCount <= (uint)entries.Length);

        // The chain of entries forms a loop; which means a concurrent update has happened.
        // Break out of the loop and throw, rather than looping forever.

        return false;
    }

    public bool TryAdd(TKey key, TVal value)
    {
        Entry<TKey, TVal>[]? entries = _entries!;

        uint hashCode = (uint)_comparer.GetHashCode(key);

        uint collisionCount = 0;
        ref int bucket = ref GetBucket(hashCode);
        int i = bucket - 1; // Value in _buckets is 1-based


        while ((uint)i < (uint)entries.Length)
        {
            if (entries[i].id == hashCode && _comparer.Equals(key, entries[i].Key))
            {
                return false;
            }

            i = entries[i].next;

            collisionCount++;
            if (collisionCount > (uint)entries.Length)
            {
                // The chain of entries forms a loop; which means a concurrent update has happened.
                // Break out of the loop and throw, rather than looping forever.
                throw new NotSupportedException("Concurrent operations are not allowed");
            }
        }

        int index;
        if (_freeCount > 0)
        {
            index = _freeList;
            Debug.Assert(StartOfFreeList - entries[_freeList].next >= -1, "shouldn't overflow because `next` cannot underflow");
            _freeList = StartOfFreeList - entries[_freeList].next;
            _freeCount--;
        }
        else
        {
            int count = _count;
            if (count == entries.Length)
            {
                Resize();
                bucket = ref GetBucket(hashCode);
            }
            index = count;
            _count = count + 1;
            entries = _entries;
        }

        ref Entry<TKey, TVal> entry = ref entries![index];
        entry.id = hashCode;
        entry.next = bucket - 1; // Value in _buckets is 1-based
        entry.Key = key;
        entry.Value = value;
        bucket = index + 1; // Value in _buckets is 1-based
        _version++;

        return true;
    }

    private void Resize() => Resize(ExpandPrime(_count), false);

    private void Resize(int newSize, bool forceNewHashCodes)
    {
        // Value types never rehash
        Debug.Assert(!forceNewHashCodes || !typeof(TKey).IsValueType);
        Debug.Assert(newSize >= _entries!.Length);

        var entries = new Entry<TKey, TVal>[newSize];

        int count = _count;
        Array.Copy(_entries, entries, count);

        // Assign member variables after both arrays allocated to guard against corruption from OOM if second fails
        _buckets = new int[newSize];
#if TARGET_64BIT
        _fastModMultiplier = GetFastModMultiplier((uint)newSize);
#endif
        for (int i = 0; i < count; i++)
        {
            if (entries[i].next >= -1)
            {
                ref int bucket = ref GetBucket(entries[i].id);
                entries[i].next = bucket - 1; // Value in _buckets is 1-based
                bucket = i + 1;
            }
        }

        _entries = entries;
    }
    public static ulong GetFastModMultiplier(uint divisor) =>
            ulong.MaxValue / divisor + 1;

    public const int MaxPrimeArrayLength = 0x7FFFFFC3;
    public static int ExpandPrime(int oldSize)
    {
        int newSize = 2 * oldSize;

        // Allow the hashtables to grow to maximum possible size (~2G elements) before encountering capacity overflow.
        // Note that this check works even when _items.Length overflowed thanks to the (uint) cast
        if ((uint)newSize > MaxPrimeArrayLength && MaxPrimeArrayLength > oldSize)
        {
            Debug.Assert(MaxPrimeArrayLength == GetPrime(MaxPrimeArrayLength), "Invalid MaxPrimeArrayLength");
            return MaxPrimeArrayLength;
        }

        return GetPrime(newSize);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private ref int GetBucket(uint hashCode)
    {
        int[] buckets = _buckets!;
#if TARGET_64BIT
        return ref buckets[FastMod(hashCode, (uint)buckets.Length, _fastModMultiplier)];
#else
        return ref buckets[hashCode % buckets.Length];
#endif
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static uint FastMod(uint value, uint divisor, ulong multiplier)
    {
        // We use modified Daniel Lemire's fastmod algorithm (https://github.com/dotnet/runtime/pull/406),
        // which allows to avoid the long multiplication if the divisor is less than 2**31.
        Debug.Assert(divisor <= int.MaxValue);

        // This is equivalent of (uint)Math.BigMul(multiplier * value, divisor, out _). This version
        // is faster than BigMul currently because we only need the high bits.
        uint highbits = (uint)(((multiplier * value >> 32) + 1) * divisor >> 32);

        Debug.Assert(highbits == value % divisor);
        return highbits;
    }

    public Span<Entry<TKey, TVal>> AsSpan()
    {
        return _entries.AsSpan(0, _count);
    }

    public Span<TKey> KeysAsSpan()
    {
        Span<TKey> _keys = new TKey[_count];

        for (int i = 0; i < _count; i++)
        {
            _keys[i] = _entries![i].Key;
        }

        return _keys;
    }

    public Span<TVal> ValuesAsSpan()
    {
        Span<TVal> _values = new TVal[_count];

        for (int i = 0; i < _count; i++)
        {
            _values[i] = _entries![i].Value;
        }

        return _values;
    }

    public void Clear()
    {
        int count = _count;
        if (count > 0)
        {
            Array.Clear(_buckets, 0, _buckets!.Length);

            _count = 0;
            _freeList = -1;
            _freeCount = 0;

            Array.Clear(_entries, 0, count);
        }
    }

    public void ForEach(RefItemResolver<TKey, TVal> iterator)
    {
        for (int i = 0; i < _count; i++)
        {
            iterator(_entries![i].Key, ref _entries[i].Value);
        }
    }
    public ref TVal GetValueOrInserter(TKey key, out Action<TVal> insertor)
    {
        Entry<TKey, TVal>[]? entries = _entries!;

        uint hashCode = (uint)_comparer.GetHashCode(key);

        uint collisionCount = 0;
        ref int bucket = ref GetBucket(hashCode);
        int i = bucket - 1; // Value in _buckets is 1-based


        while ((uint)i < (uint)entries.Length)
        {
            if (entries[i].id == hashCode && _comparer.Equals(key, entries[i].Key))
            {
                insertor = null!;
                return ref entries[i].Value;
            }

            i = entries[i].next;

            collisionCount++;
            if (collisionCount > (uint)entries.Length)
            {
                // The chain of entries forms a loop; which means a concurrent update has happened.
                // Break out of the loop and throw, rather than looping forever.
                throw new NotSupportedException("Concurrent operations are not allowed");
            }
        }

        insertor = item =>
        {
            hashCode = (uint)_comparer.GetHashCode(key);
            var entries = _entries!;
            ref int bucket = ref GetBucket(hashCode);
            int index;
            if (_freeCount > 0)
            {
                index = _freeList;
                Debug.Assert(StartOfFreeList - entries[_freeList].next >= -1, "shouldn't overflow because `next` cannot underflow");
                _freeList = StartOfFreeList - entries[_freeList].next;
                _freeCount--;
            }
            else
            {
                int count = _count;
                if (count == entries.Length)
                {
                    Resize();
                    bucket = ref GetBucket(hashCode);
                }
                index = count;
                _count = count + 1;
                entries = _entries;
            }

            ref Entry<TKey, TVal> entry = ref entries![index];
            entry.id = hashCode;
            entry.next = bucket - 1; // Value in _buckets is 1-based
            entry.Key = key;
            entry.Value = item;
            bucket = index + 1; // Value in _buckets is 1-based
            _version++;
        };

        return ref (new TVal[1] { default! })[0];
    }

    public IEnumerator<(TKey, TVal)> GetEnumerator()
    {
        if (_count == 0) return default(EmptyEnumerator);

        return new Enumerator(_entries!, _count);
    }

    public IEnumerable<TKey> Keys
    {
        get
        {
            if(_count == 0) yield break;

            for (int i = 0; i < _count; i++) yield return _entries![i].Key; 
        }
    }

    public IEnumerable<TVal> Values
    {
        get
        {
            if (_count == 0) yield break;

            for (int i = 0; i < _count; i++) yield return _entries![i].Value;
        }
    }

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    struct EmptyEnumerator : IEnumerator<(TKey, TVal)>
    {
        public readonly (TKey, TVal) Current => throw new NotImplementedException();

        readonly object IEnumerator.Current => throw new NotImplementedException();

        public void Dispose() => throw new NotImplementedException();

        public readonly bool MoveNext() => false;

        public void Reset() => throw new NotImplementedException();
    }

    struct Enumerator(Entry<TKey, TVal>[] entries, int count) : IEnumerator<(TKey, TVal)>
    {
        private int current = -1;

        public readonly (TKey, TVal) Current => entries[current];

        readonly object IEnumerator.Current => Current;

        public readonly void Dispose() => throw new NotImplementedException();

        public bool MoveNext() => ++current < count;

        public void Reset() => current = -1;
    }
}

public struct Entry<TKey, TValue>
{
    public TKey Key;
    public TValue Value;
    internal int next;
    internal uint id;

    public static implicit operator (TKey, TValue)(Entry<TKey, TValue> entry) => (entry.Key, entry.Value);
}