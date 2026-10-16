# The largest sum-dominant subsets of $\lbrace 0, 1, \dots, n-1\rbrace$

**A proof of H. V. Chu's Conjecture 1.3 (Integers 20 (2020), #A87), equivalently the conjectured formula $a(n) = n - 7$ in OEIS [A305503](https://oeis.org/A305503).**

Shido Tamaki, October 2026. Not peer reviewed.

> **How this was produced (AI disclosure).**
> The proof, the computer checks and the Lean formalization were found and written by Claude, an AI model made by Anthropic (Claude Opus 5.5), in research sessions that Shido Tamaki initiated and directed in October 2026. An independent review of the proof and of the Lean statement, with a separate re-implementation of all computations, was done by another Claude model (Claude Fable 5.1). This write-up was also drafted by Claude.
> The whole argument is formally verified in Lean 4 with Mathlib (file [`A305503.lean`](A305503.lean)). A reader can check the result by compiling that one file; what remains to be checked by a human is that the Lean statement (Section 4) says what the conjecture says.
>
> **What I checked myself (Shido Tamaki).** I ran [`verify.py`](verify.py) on my own computer and confirmed that all five checks give the results stated here. I also checked that the Lean statement in Section 4 says the same thing as Chu's Conjecture 1.3.

## 1. The problem

For a finite set $A \subset \mathbb{Z}$ let $A + A = \lbrace a + b : a, b \in A\rbrace$ and $A - A = \lbrace a - b : a, b \in A\rbrace$. The set $A$ is called *sum-dominant* (or MSTD, "more sums than differences") if $|A + A| > |A - A|$. Since addition is commutative while subtraction is not, most sets have more differences than sums; the smallest sum-dominant sets have 8 elements (Hegarty).

Let $a(n)$ be the largest size of a sum-dominant subset of $\lbrace 0, 1, \dots, n-1\rbrace$, with $a(n) = 0$ if there is none (OEIS A305503, T. Mathur 2018). The whole interval is balanced ($|A+A| = |A-A| = 2n-1$), so some elements must be discarded.

Chu proved that $n - 7 \le a(n) \le n - 4$ for $n \ge 16$ (his Theorem 1.2): the lower bound comes from an explicit family $K_m$ that discards 7 elements, and the upper bound from a hand analysis showing that discarding at most 3 elements never works. He conjectured $a(n) = n - 7$ for all $n \ge 16$ (Conjecture 1.3) and verified it by computer for $16 \le n \le 34$. The arXiv version of the paper (arXiv:1906.03793v2) also lists "Is Conjecture 1.3 correct?" as the first question for future research; there the subsets are additionally required to contain $0$ and $n - 1$. The result below covers both versions.

## 2. Result

**Theorem.** For every $n \ge 16$, $a(n) = n - 7$. Equivalently: if $A \subseteq \lbrace 0, \dots, n-1\rbrace$ and $|A| \ge n - 6$, then $|A + A| \le |A - A|$; and a sum-dominant subset of size $n - 7$ exists. The same holds for sum-dominant subsets containing $0$ and $n - 1$.

Consequences for the OEIS entry:
- the formula "$a(n) = n - 7$ (conjectured) for all $n > 15$" is a theorem;
- the conjectured recurrence $a(n) = 2a(n-1) - a(n-2)$ for $n > 17$ holds;
- the printed generating function $x^{14}(9 - 9x + x^2)/(1-x)^2$ is off by one: with offset 1 it should be $x^{15}(9 - 9x + x^2)/(1-x)^2$ (the printed one gives $a(14) = 9$).

The values $a(n) = 0$ for $n \le 14$ and $a(15) = 9$ are known by exhaustive search (Chu; rechecked here) and are not needed for the theorem.

**Proof idea.** Translate $A$ so that $\min A = 0$ and call the missing elements of $[0, \max A]$ *holes*. If there are at most 6 holes, then a difference can be missing only if it is close to $\max A$ (a missing difference $d$ forces every pair $\lbrace a, a+d\rbrace$ to contain a hole, and there are too many such pairs unless $d$ is large), and such missing differences, as well as missing small and large sums, are controlled by the holes within distance 5 of the two ends. A finite check over the 848 possible hole patterns at the two ends shows that every missing difference costs at least as many missing sums. A handful of short spans, where a "middle" difference can be blocked, are handled separately.

## 3. Proof

Throughout, $[a, b] = \lbrace a, a+1, \dots, b\rbrace$ denotes an integer interval.

### 3.1 Translation and holes

For $c \in \mathbb{Z}$, $(A + c) + (A + c) = (A + A) + 2c$ and $(A + c) - (A + c) = A - A$, so translating $A$ does not change $|A + A|$, $|A - A|$ or sum-dominance. Similarly the reflection $A \mapsto c - A$ preserves both sizes; in particular a symmetric set ($A = c - A$) satisfies $|A + A| = |A + (c - A)| = |A - A|$ and is not sum-dominant (Nathanson; see Chu, Proposition 2.1).

**Setting.** Let $m \ge 1$ and $A \subseteq [0, m]$ with $0, m \in A$ (so $m$ is the span of $A$). Let $B = [0, m] \setminus A$ be the set of *holes* and $k = |B|$, so $|A| = m + 1 - k$ and $B \subseteq [1, m-1]$.

**Proposition Q.** In the setting above, if $|A| \ge 10$ and $k \le 6$, then $A$ is not sum-dominant.

*Upper bound of the Theorem from Proposition Q.* Let $n \ge 16$ and let $A \subseteq [0, n-1]$ be sum-dominant with $|A| \ge n - 6$. Translate $A$ so that $\min A = 0$; then $m = \max A - \min A \le n - 1$ and $k = m + 1 - |A| \le n - |A| \le 6$, while $|A| \ge n - 6 \ge 10$. This contradicts Proposition Q. Hence $a(n) \le n - 7$.

### 3.2 Counting missing sums and differences

Let $\sigma = |[0, 2m] \setminus (A + A)|$ be the number of missing sums and $\delta = |[1, m] \setminus (A - A)|$ the number of missing positive differences. Since $A + A \subseteq [0, 2m]$, and $A - A \subseteq [-m, m]$ contains $0$ and is symmetric under $x \mapsto -x$,

$$|A + A| = 2m + 1 - \sigma, \qquad |A - A| = 2m + 1 - 2\delta, \qquad |A + A| - |A - A| = 2\delta - \sigma.$$

So $A$ is sum-dominant if and only if $2\delta > \sigma$: every missing difference counts twice (for $\pm d$).

### 3.3 Lemma A (pairs)

Let $d \in [1, m]$ with $d \notin A - A$. For $a \in [0, m - d]$ put $P_a = \lbrace a, a + d\rbrace \subseteq [0, m]$. Since $d \notin A - A$, **every $P_a$ contains a hole.**

- (a) If $2d > m$, then $m - d + 1 \le k$.
  *Proof.* The pairs $P_0, \dots, P_{m-d}$ have left elements in $[0, m-d]$ and right elements in $[d, m]$, and $m - d < d$, so they are pairwise disjoint. Each contains a hole.
- (b) If $2d \le m$, then $d \le k$ and $m - d + 1 \le 2k$; hence $3k \ge m + 1$.
  *Proof.* The pairs $P_0, \dots, P_{d-1}$ are pairwise disjoint (left elements in $[0, d-1]$, right elements in $[d, 2d-1]$), and $d - 1 \le m - d$, so $k \ge d$. A hole $b$ lies in at most two of the $m - d + 1$ pairs $P_0, \dots, P_{m-d}$ (namely $P_b$ and $P_{b-d}$), so $2k \ge m - d + 1$. Adding the two inequalities gives $3k \ge m + 1$.

### 3.4 Lemma B (missing differences near $m$)

Let $m \ge 6$ and define the hole patterns at the two ends

$$L = B \cap [1, 5], \qquad R = \lbrace  r \in [1, 5] : m - r \in B \rbrace,$$

and

$$T(L, R) = \lbrace  t \in [0, 5] : \text{for every } a \in [0, t],\ a \in L \text{ or } t - a \in R \rbrace, \qquad D(L, R) = |T(L, R)|.$$

**Claim.** If $t \in [0, 5]$ and $m - t \notin A - A$, then $t \in T(L, R)$.

*Proof.* Let $d = m - t \ge 1$ and $a \in [0, t]$. Both $a$ and $a + d = m - (t - a)$ lie in $[0, m]$, so one of them is a hole. If $a \notin A$ then $a \ne 0$, so $a \in B \cap [1, 5] = L$. If $m - (t - a) \notin A$ then $t - a \ne 0$ (as $m \in A$), so $t - a \in R$. $\square$

### 3.5 Lemma C (missing sums near the ends)

For $P \subseteq [1, 5]$ let $S(P) = |\lbrace  s \in [0, 5] : \text{for every } x \in [0, s],\ x \in P \text{ or } s - x \in P \rbrace|$.

**Claim.** If $m \ge 6$, then $\sigma \ge S(L) + S(R)$.

*Proof.* If $s$ is counted in $S(L)$ and $s = a + b$ with $a, b \in A$, then $a \in [0, s]$ and $b = s - a$, so $a \in L \subseteq B$ or $b \in L \subseteq B$, a contradiction; hence $s \notin A + A$. If $s'$ is counted in $S(R)$ and $2m - s' = a + b$ with $a, b \in A$, put $x = m - a \in [0, s']$; then $s' - x = m - b$, so $x \in R$ (i.e. $a \in B$) or $s' - x \in R$ (i.e. $b \in B$), a contradiction; hence $2m - s' \notin A + A$. The sums $s \le 5$ and $2m - s' \ge 2m - 5$ are distinct because $m \ge 6$. $\square$

### 3.6 The finite check F

**Fact F.** For all $L, R \subseteq [1, 5]$ with $|L| + |R| \le 6$ (there are $\sum_{j=0}^{6} \binom{10}{j} = 848$ such pairs),

$$2D(L, R) \le S(L) + S(R).$$

This is checked by computer ([`verify.py`](verify.py), and in Lean by kernel evaluation: theorem `checkF`). The distribution of $2D(L,R) - S(L) - S(R)$ over the 848 pairs is: $-5$: 6, $-4$: 56, $-3$: 152, $-2$: 216, $-1$: 260, $0$: 158. For example, $L = R = \lbrace 1\rbrace$ (holes $1$ and $m - 1$) gives $T = \lbrace 1\rbrace$ (the difference $m - 1$ is missing) and $S(L) = S(R) = 1$ (the sums $1$ and $2m - 1$ are missing): a tie.

### 3.7 Proposition P

**Proposition P.** In the setting of 3.1, assume $m \ge 6$ and

- (H1) every missing positive difference $d$ satisfies $d \ge m - 5$;
- (H2) $|L| + |R| \le 6$.

Then $A$ is not sum-dominant.

*Proof.* By (H1), each missing positive difference $d$ has $t = m - d \in [0, 5]$, and by Lemma B, $t \in T(L, R)$. Since $d \mapsto m - d$ is injective, $\delta \le D(L, R)$. By Lemma C, $\sigma \ge S(L) + S(R)$. By (H2) and Fact F,
$$|A + A| - |A - A| = 2\delta - \sigma \le 2D(L, R) - S(L) - S(R) \le 0. \qquad \square$$

### 3.8 Proof of Proposition Q

$|A| \ge 10$ means $k \le m - 9$, so $m \ge 9$ and $k \le \min(6, m - 9)$. We verify (H1) and (H2) and apply Proposition P. By Lemma A(a), a missing $d$ with $2d > m$ satisfies $m - d \le k - 1 \le 5$, as (H1) requires. So (H1) can fail only through a missing "middle" difference $d$ with $2d \le m$, which by Lemma A(b) requires $3k \ge m + 1$.

- **$m \ge 18$.** $3k \le 18 < m + 1$, so there is no missing middle difference and (H1) holds. Since $m \ge 11$, the windows $[1, 5]$ and $[m - 5, m - 1]$ are disjoint, so $|L| + |R| \le k \le 6$, which is (H2).
- **$9 \le m \le 13$.** $3k \le 3m - 27 < m + 1$, so (H1) holds. For (H2): if $m \ge 11$ then $|L| + |R| \le k \le 6$; if $m \in \lbrace 9, 10\rbrace$ then $k \le 1$ and $|L| + |R| \le 2k \le 2$.
- **$14 \le m \le 17$.** (H2) holds as $m \ge 11$. If no middle difference is missing, (H1) holds and we are done. Otherwise Lemma A(b) gives $d \le k$ and $m - d + 1 \le 2k$ with $k \le 6$ ($k \le 5$ if $m = 14$) and $2d \le m$, so
  $$(m, d) \in \lbrace (14,5), (15,4), (15,5), (15,6), (16,5), (16,6), (17,6)\rbrace.$$
  If $\mathcal{F}$ is a family of pairwise disjoint pairs $P_a$, each containing a hole, then $k \ge |\mathcal{F}|$; if $|\mathcal{F}| = k$, then every hole lies in $\bigcup \mathcal{F}$ and each pair contains exactly one hole. Using two such families in each case:

  | $(m, d)$ | disjoint families | conclusion |
  |---|---|---|
  | $(14, 5)$, $k \le 5$ | $P_0..P_4$ (union $[0, 9]$); $P_5..P_9$ (union $[5, 14]$) | $B = [5, 9]$ |
  | $(15, 4)$ | $P_0..P_3, P_8..P_{11}$ (8 pairs) | impossible ($k \ge 8$) |
  | $(15, 5)$ | $P_0..P_4, P_{10}$ (union $[0, 10] \cup \lbrace 15\rbrace$); $P_0, P_6..P_{10}$ (union $\lbrace 0, 5\rbrace \cup [6, 15]$) | $B = [5, 10]$ (as $0, 15 \notin B$) |
  | $(15, 6)$ | $P_0..P_5$ (union $[0, 11]$); $P_4..P_9$ (union $[4, 15]$) | $B \subseteq [4, 11]$; $P_0..P_3$ force $6, 7, 8, 9 \in B$, and one hole in each of $\lbrace 4, 10\rbrace$, $\lbrace 5, 11\rbrace$: 4 sets |
  | $(16, 5)$ | $P_0..P_4, P_{10}, P_{11}$ (7 pairs) | impossible |
  | $(16, 6)$ | $P_0..P_5$ (union $[0, 11]$); $P_5..P_{10}$ (union $[5, 16]$) | $[6, 10] \subseteq B$ plus one of $5, 11$: 2 sets |
  | $(17, 6)$ | $P_0..P_5$ (union $[0, 11]$); $P_6..P_{11}$ (union $[6, 17]$) | $B = [6, 11]$ |

  None of the resulting 8 sets $A = [0, m] \setminus B$ is sum-dominant:

  | $m$ | $B$ | $\lvert A+A \rvert$ | $\lvert A-A \rvert$ | |
  |---|---|---|---|---|
  | 14 | $[5, 9]$ | 27 | 27 | symmetric |
  | 15 | $[4, 9]$ | 27 | 29 | |
  | 15 | $\lbrace 4, 6, 7, 8, 9, 11\rbrace$ | 29 | 29 | symmetric |
  | 15 | $[5, 10]$ | 27 | 27 | symmetric |
  | 15 | $[6, 11]$ | 27 | 29 | |
  | 16 | $[5, 10]$ | 30 | 31 | |
  | 16 | $[6, 11]$ | 30 | 31 | |
  | 17 | $[6, 11]$ | 33 | 33 | symmetric |

  (The non-symmetric ones are unions of two intervals; their sizes are immediate, e.g. for $m = 15$, $B = [4, 9]$: $A + A = [0, 6] \cup [10, 18] \cup [20, 30]$ and $A - A = [-5, 5] \cup \pm[7, 15]$.) $\square$

This proves Proposition Q, and hence $a(n) \le n - 7$ for $n \ge 16$.

### 3.9 The lower bound (Chu's sets)

For $m \ge 8$ let
$$K_m = [0, m + 7] \setminus \lbrace 3, 5, 6, m+1, m+2, m+3, m+5\rbrace = \lbrace 0, 1, 2, 4\rbrace \cup [7, m] \cup \lbrace m+4, m+6, m+7\rbrace.$$
Chu (Lemma 4.1) states this for $m \ge 9$; the same computation works for $m = 8$, which is needed for $n = 16$.

- *Sums.* $\lbrace 0,1,2,4\rbrace + \lbrace 0,1,2,4\rbrace \supseteq [0, 6]$; $[7, m] + \lbrace 0,1,2,4\rbrace = [7, m+4]$ (as $11 \le m + 3$); $\lbrace 0,1,2,4\rbrace + \lbrace m+4, m+6, m+7\rbrace = [m+4, m+11]$; $[7, m] + \lbrace m+4, m+6, m+7\rbrace = [m+11, 2m+7]$ (as $m + 13 \le 2m + 5$); and $\lbrace m+4, m+6, m+7\rbrace + \lbrace m+4, m+6, m+7\rbrace = \lbrace 2m+8, 2m+10, 2m+11, 2m+12, 2m+13, 2m+14\rbrace$. So $K_m + K_m \supseteq [0, 2m+14] \setminus \lbrace 2m+9\rbrace$. If $2m + 9 = x + y$ with $x \le y$ in $K_m$, then $y \le m + 7$ forces $x \ge m + 2$, so $x \in \lbrace m+4, m+6, m+7\rbrace$ and $y \in \lbrace m+5, m+3, m+2\rbrace$, none of which is in $K_m$. Hence $|K_m + K_m| = 2m + 14$.
- *Differences.* $\lbrace 0,1,2,4\rbrace - \lbrace 0,1,2,4\rbrace \supseteq [1, 4]$; $[7, m] - \lbrace 0,1,2,4\rbrace \supseteq [3, m]$ (as $m - 4 \ge 4$); $\lbrace m+4, m+6, m+7\rbrace - \lbrace 0,1,2,4\rbrace = \lbrace m, m+2, m+3, m+4, m+5, m+6, m+7\rbrace$. So the positive differences include $[1, m+7] \setminus \lbrace m+1\rbrace$. If $m + 1 = y - x$ with $x, y \in K_m$, then $x \le 6$, so $x \in \lbrace 0,1,2,4\rbrace$ and $y \in \lbrace m+1, m+2, m+3, m+5\rbrace$, none of which is in $K_m$. Hence $|K_m - K_m| = 2(m + 6) + 1 = 2m + 13$.

So $|K_m + K_m| - |K_m - K_m| = 1$. With $m = n - 8$, $K_{n-8} \subseteq [0, n-1]$ contains $0$ and $n - 1$ and has $n - 7$ elements, so $a(n) \ge n - 7$ for $n \ge 16$ (also in the version requiring $0, n-1 \in A$). Together with 3.8 this proves the Theorem. $\blacksquare$

## 4. Formal verification (Lean 4)

[`A305503.lean`](A305503.lean) formalizes the whole argument (Lean v4.35.0-rc3, Mathlib v4.35.0-rc3). The main theorems are

```lean
def IsMSTD (A : Finset ℤ) : Prop := (A - A).card < (A + A).card   -- pointwise sum and difference

theorem A305503.main (n : ℕ) (hn : 16 ≤ n) :
    IsGreatest {k | ∃ A : Finset ℤ, A ⊆ Finset.Ico 0 (n : ℤ) ∧ IsMSTD A ∧ A.card = k} (n - 7)

theorem A305503.main_spanning (n : ℕ) (hn : 16 ≤ n) :
    IsGreatest {k | ∃ A : Finset ℤ, A ⊆ Finset.Ico 0 (n : ℤ) ∧ (0 : ℤ) ∈ A ∧ ((n : ℤ) - 1) ∈ A ∧
      IsMSTD A ∧ A.card = k} (n - 7)
```

- `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for both theorems; there is no `sorry` and no `native_decide`.
- The finite parts (Fact F and the spans $14 \le m \le 17$) are checked by kernel evaluation (`decide +kernel`).
- The file compiles without errors or warnings in about 30 seconds with a warm Mathlib cache (`lake env lean A305503.lean` inside a Lake project that depends on Mathlib).
- Correspondence with Section 3: `isMSTD_image_sub` (3.1), `card_add_le`, `card_sub_ge`, `card_pos_diff_ge` (3.2), `lemmaA_a`, `lemmaA_b` (3.3), `lemmaB` (3.4), `lemmaC_left`, `lemmaC_right` (3.5), `checkF` (3.6), `propP` (3.7), `case14`–`case17`, `propQ` (3.8), `upper`, `K_mstd` (3.1, 3.9).

## 5. Computations (independent of the proof)

[`verify.py`](verify.py) (Python 3, standard library only) rechecks Fact F, Proposition Q for spans $9 \le m \le 30$ (2,797,577 sets, none sum-dominant), the 8 exceptional sets of 3.8, the sets $K_m$ for $8 \le m \le 200$, and $a(1), \dots, a(18)$ by exhaustive search; its output is in [`verify_out.txt`](verify_out.txt). Two further independent implementations were used during the work:

| check | range | result |
|---|---|---|
| $a(n)$ by exhaustive search | $n \le 19$ | $0$ for $n \le 14$; $9, 9, 10, 11, 12$ for $n = 15, \dots, 19$ (agrees with OEIS) |
| subsets of $[0, n-1]$ missing at most 6 elements | $16 \le n \le 40$ | no sum-dominant set (Chu checked $n \le 34$) |
| Lemmas A, B, C directly on sets | spans $9 \le m \le 30$, at most 6 holes | no violation |

## 6. Further observations (not formalized)

- The number of sum-dominant subsets of $[0, n-1]$ of the maximum size is 2, 6, 10, 8 for $n = 15, 16, 17, 18$, and exactly 4 for every $19 \le n \le 40$ (computed): $K_{n-8}$, the set $[0, n-1] \setminus \lbrace 3, 4, 6, n-7, n-6, n-5, n-2\rbrace$, and the reflections $x \mapsto n - 1 - x$ of both. A window argument like the one in Section 3, with windows of width 13, suggests that it is exactly 4 for all $n \ge 28$; this is a sketch, not a checked proof.

## References

1. H. V. Chu, *The union of two arithmetic progressions with the same common difference is not sum-dominant*, Integers 20 (2020), #A87. arXiv:1906.03793.
2. OEIS Foundation, *A305503: Largest cardinality of subsets A of {0,1,...,n-1} with |A + A| > |A - A|*, https://oeis.org/A305503.
3. P. V. Hegarty, *Some explicit constructions of sets with more sums than differences*, Acta Arith. 130 (2007), 61–77.
4. G. Martin and K. O'Bryant, *Many sets have more sums than differences*, in Additive Combinatorics, CRM Proc. Lecture Notes 43, AMS, Providence, RI, 2007, pp. 287–305.
5. M. B. Nathanson, *Problems in additive number theory I*, in Additive Combinatorics, CRM Proc. Lecture Notes 43, AMS, Providence, RI, 2007, pp. 263–270.
