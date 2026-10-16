# -*- coding: utf-8 -*-
"""
Independent numerical checks for the proof of Chu's Conjecture 1.3 (OEIS A305503).
Standard library only. Usage:  python verify.py [max_span]   (default max_span = 24)

A set A of integers is MSTD (sum-dominant) if |A+A| > |A-A|.
a(n) = largest size of an MSTD subset of {0, ..., n-1} (0 if there is none).

Checks
  1. Finite check F: 2 D(L,R) <= S(L) + S(R) for all L, R in [1,5] with |L| + |R| <= 6.
  2. Proposition Q: no set with min 0, max m (9 <= m <= max_span), at most 6 holes
     and at least 10 elements is MSTD.
  3. The spans 9 <= m <= 17 in Proposition Q with a missing "middle" difference d (2d <= m):
     exactly the 8 sets of the case analysis, none MSTD.
  4. Chu's sets K_m (8 <= m <= 200): |K_m + K_m| - |K_m - K_m| = 1.
  5. a(n) for n <= 18 by exhaustive search (compare with OEIS A305503).
"""
import sys
import itertools
from collections import Counter


def elements(mask):
    out = []
    while mask:
        low = mask & -mask
        out.append(low.bit_length() - 1)
        mask ^= low
    return out


def sum_diff(mask):
    """Return (|A+A|, |A-A|, sum bitmask, nonnegative-difference bitmask) for A given as a bitmask."""
    S = 0
    D = 0
    for a in elements(mask):
        S |= mask << a
        D |= mask >> a
    return S.bit_count(), 2 * D.bit_count() - 1, S, D


def T(L, R):
    return [t for t in range(6) if all(a in L or (t - a) in R for a in range(t + 1))]


def S_(P):
    return [s for s in range(6) if all(x in P or (s - x) in P for x in range(s + 1))]


def check_F():
    subsets = [frozenset(c) for r in range(6) for c in itertools.combinations(range(1, 6), r)]
    dist = Counter()
    for L in subsets:
        for R in subsets:
            if len(L) + len(R) <= 6:
                dist[2 * len(T(L, R)) - len(S_(L)) - len(S_(R))] += 1
    return sum(dist.values()), dict(sorted(dist.items()))


def check_Q(max_span):
    total = 0
    mstd = 0
    middle = []
    for m in range(9, max_span + 1):
        full = (1 << (m + 1)) - 1
        for k in range(0, min(6, m - 9) + 1):
            for holes in itertools.combinations(range(1, m), k):
                mask = full
                for h in holes:
                    mask ^= 1 << h
                ns, nd, _, D = sum_diff(mask)
                total += 1
                if ns > nd:
                    mstd += 1
                if m <= 17 and any(not (D >> d) & 1 for d in range(1, m // 2 + 1)):
                    middle.append((m, holes, ns, nd))
    return total, mstd, middle


def K(m):
    return {0, 1, 2, 4} | set(range(7, m + 1)) | {m + 4, m + 6, m + 7}


def check_K():
    bad = []
    for m in range(8, 201):
        A = K(m)
        sums = {a + b for a in A for b in A}
        diffs = {a - b for a in A for b in A}
        if not (len(A) == m + 1 and len(sums) - len(diffs) == 1):
            bad.append(m)
    A7 = K(7)
    d7 = len({a + b for a in A7 for b in A7}) - len({a - b for a in A7 for b in A7})
    return bad, d7


def check_a(nmax):
    res = []
    for n in range(1, nmax + 1):
        best = 0
        for mask in range(1, 1 << n):
            c = mask.bit_count()
            if c <= best:
                continue
            ns, nd, _, _ = sum_diff(mask)
            if ns > nd:
                best = c
        res.append(best)
    return res


def main():
    max_span = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    total, dist = check_F()
    print(f"1. F: {total} pairs, distribution of 2D - S(L) - S(R): {dist}")
    print(f"   max = {max(dist)} (must be <= 0)")
    total, mstd, middle = check_Q(max_span)
    print(f"2. Proposition Q, spans 9..{max_span}: {total} sets checked, MSTD sets found: {mstd}")
    print(f"3. Missing middle difference (spans <= 17): {len(middle)} sets")
    for m, holes, ns, nd in middle:
        print(f"   m={m:2d}  holes={list(holes)}  |A+A|={ns}  |A-A|={nd}")
    bad, d7 = check_K()
    print(f"4. K_m for 8 <= m <= 200: failures {bad}; for m = 7 the difference is {d7:+d}")
    a = check_a(18)
    oeis = [0] * 14 + [9, 9, 10, 11]
    print(f"5. a(1..18) = {a}")
    print(f"   matches OEIS A305503: {a == oeis}")


if __name__ == "__main__":
    main()
