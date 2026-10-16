import Mathlib

/-!
# OEIS A305503 = H. V. Chu's Conjecture 1.3 (Integers 20 (2020) #A87)

A finite set `A ⊆ ℤ` is *MSTD* (more sums than differences) if `|A - A| < |A + A|`.
OEIS A305503: `a(n)` is the largest size of an MSTD subset of `{0, …, n-1}`.
Chu proved `n - 7 ≤ a(n) ≤ n - 4` for `n ≥ 16` and conjectured `a(n) = n - 7`.

Main results:
* `A305503.main`: for `n ≥ 16`, `n - 7` is the greatest size of an MSTD subset of `[0, n)`.
* `A305503.main_spanning`: the same for MSTD subsets containing `0` and `n - 1`
  (the arXiv-v2 form of Chu's conjecture).

Proof outline (details in `README.md`, which also contains the AI disclosure: this file was
written by Claude, an AI model made by Anthropic):
* translate so that `min A = 0`, `max A = m`; let `B = [0, m] \ A` and `k = |B|`;
* `|A + A| ≤ 2m + 1 - S(L) - S(R)` and `|A - A| ≥ 2m + 1 - 2 D(L,R)` for the hole patterns
  `L, R ⊆ [1,5]` of the two ends, provided every missing positive difference is `≥ m - 5`
  (Lemmas B, C, `propP`);
* `2 D(L,R) ≤ S(L) + S(R)` for all `L, R ⊆ [1,5]` with `|L| + |R| ≤ 6` (`checkF`, kernel `decide`);
* if `|A| ≥ 10` and `k ≤ 6`, missing differences `d ≤ m/2` only occur for spans `14 ≤ m ≤ 17`
  (pair counting, Lemma A); those cases are pinned down by disjoint pair families and finished by
  kernel `decide` (`propQ`);
* lower bound: Chu's family `K m = {0,1,2,4} ∪ [7,m] ∪ {m+4,m+6,m+7}` (`m ≥ 8`).

All finite checks use `decide +kernel` (no `native_decide`).
-/

open Pointwise Finset

namespace A305503

/-- `A` has more sums than differences. -/
def IsMSTD (A : Finset ℤ) : Prop := (A - A).card < (A + A).card

instance : DecidablePred IsMSTD := fun _ => Nat.decLt _ _

/-! ### Translation invariance -/

lemma add_image_sub (A : Finset ℤ) (c : ℤ) :
    A.image (· - c) + A.image (· - c) = (A + A).image (· - 2 * c) := by
  ext x
  simp only [mem_add, mem_image]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by ring⟩
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨a - c, ⟨a, ha, rfl⟩, b - c, ⟨b, hb, rfl⟩, by ring⟩

lemma sub_image_sub (A : Finset ℤ) (c : ℤ) :
    A.image (· - c) - A.image (· - c) = A - A := by
  ext x
  simp only [mem_sub, mem_image]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a, ha, b, hb, by ring⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a - c, ⟨a, ha, rfl⟩, b - c, ⟨b, hb, rfl⟩, by ring⟩

lemma isMSTD_image_sub (A : Finset ℤ) (c : ℤ) : IsMSTD (A.image (· - c)) ↔ IsMSTD A := by
  unfold IsMSTD
  rw [add_image_sub, sub_image_sub, card_image_of_injective _ sub_left_injective]

/-! ### Hole patterns at the two ends and the finite check `F` -/

/-- Left hole pattern `L = [1,5] \ A` (as naturals). -/
def Lw (A : Finset ℤ) : Finset ℕ := (Icc 1 5).filter (fun i : ℕ => (i : ℤ) ∉ A)

/-- Right hole pattern `R = {r ∈ [1,5] : m - r ∉ A}` (the right end, mirrored). -/
def Rw (A : Finset ℤ) (m : ℤ) : Finset ℕ := (Icc 1 5).filter (fun i : ℕ => m - (i : ℤ) ∉ A)

/-- `T(L,R)`: the `t ≤ 5` such that every `a ≤ t` has `a ∈ L` or `t - a ∈ R`. -/
def Tset (L R : Finset ℕ) : Finset ℕ :=
  (range 6).filter (fun t => ∀ a ∈ range (t + 1), a ∈ L ∨ t - a ∈ R)

/-- `S(P)`: the `s ≤ 5` such that every `x ≤ s` has `x ∈ P` or `s - x ∈ P`. -/
def Sset (P : Finset ℕ) : Finset ℕ :=
  (range 6).filter (fun s => ∀ x ∈ range (s + 1), x ∈ P ∨ s - x ∈ P)

/-- The finite check F (848 relevant pairs): `2 D(L,R) ≤ S(L) + S(R)`. -/
theorem checkF : ∀ L ∈ (Icc 1 5 : Finset ℕ).powerset, ∀ R ∈ (Icc 1 5 : Finset ℕ).powerset,
    L.card + R.card ≤ 6 → 2 * (Tset L R).card ≤ (Sset L).card + (Sset R).card := by
  decide +kernel

/-! ### Lemma B: missing differences near `m` are described by `T(L,R)` -/

lemma lemmaB {A : Finset ℤ} {m : ℤ} (h0 : (0 : ℤ) ∈ A) (hm : m ∈ A) {t : ℕ} (ht : t ≤ 5)
    (hd : m - t ∉ A - A) : t ∈ Tset (Lw A) (Rw A m) := by
  simp only [Tset, mem_filter, mem_range]
  refine ⟨by omega, fun a ha => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hL, hR⟩ := hcon
  apply hd
  rw [mem_sub]
  have haA : (a : ℤ) ∈ A := by
    rcases Nat.eq_zero_or_pos a with h | h
    · simpa [h] using h0
    · by_contra hn
      exact hL (by simp only [Lw, mem_filter, mem_Icc]; exact ⟨⟨h, by omega⟩, hn⟩)
  have hbA : m - ((t - a : ℕ) : ℤ) ∈ A := by
    rcases Nat.eq_zero_or_pos (t - a) with h | h
    · simpa [h] using hm
    · by_contra hn
      exact hR (by simp only [Rw, mem_filter, mem_Icc]; exact ⟨⟨h, by omega⟩, hn⟩)
  refine ⟨_, hbA, _, haA, ?_⟩
  rw [Nat.cast_sub (by omega : a ≤ t)]
  ring

/-! ### Lemma C: missing sums at the two ends -/

lemma lemmaC_left {A : Finset ℤ} {m : ℤ} (hA : A ⊆ Icc 0 m) {s : ℕ} (hs : s ∈ Sset (Lw A)) :
    (s : ℤ) ∉ A + A := by
  simp only [Sset, mem_filter, mem_range] at hs
  rw [mem_add]
  rintro ⟨a, ha, b, hb, hab⟩
  have ha0 := (mem_Icc.mp (hA ha)).1
  have hb0 := (mem_Icc.mp (hA hb)).1
  rcases hs.2 a.toNat (by omega) with h | h
  · simp only [Lw, mem_filter] at h
    exact h.2 (by rwa [Int.toNat_of_nonneg ha0])
  · simp only [Lw, mem_filter] at h
    apply h.2
    have : ((s - a.toNat : ℕ) : ℤ) = b := by omega
    rw [this]
    exact hb

lemma lemmaC_right {A : Finset ℤ} {m : ℤ} (hA : A ⊆ Icc 0 m) {s : ℕ}
    (hs : s ∈ Sset (Rw A m)) : 2 * m - s ∉ A + A := by
  simp only [Sset, mem_filter, mem_range] at hs
  rw [mem_add]
  rintro ⟨a, ha, b, hb, hab⟩
  have ha1 := mem_Icc.mp (hA ha)
  have hb1 := mem_Icc.mp (hA hb)
  rcases hs.2 (m - a).toNat (by omega) with h | h
  · simp only [Rw, mem_filter] at h
    apply h.2
    have : m - (((m - a).toNat : ℕ) : ℤ) = a := by omega
    rw [this]
    exact ha
  · simp only [Rw, mem_filter] at h
    apply h.2
    have : m - ((s - (m - a).toNat : ℕ) : ℤ) = b := by omega
    rw [this]
    exact hb

/-! ### Counting sums and differences -/

lemma card_add_le {A : Finset ℤ} {m : ℤ} (hA : A ⊆ Icc 0 m) (h6 : 6 ≤ m) :
    ((A + A).card : ℤ) + (Sset (Lw A)).card + (Sset (Rw A m)).card ≤ 2 * m + 1 := by
  have hS5 : ∀ P : Finset ℕ, ∀ s ∈ Sset P, s ≤ 5 := fun P s hs => by
    simp only [Sset, mem_filter, mem_range] at hs; omega
  set ML := (Sset (Lw A)).image (fun s : ℕ => (s : ℤ)) with hML
  set MR := (Sset (Rw A m)).image (fun s : ℕ => 2 * m - (s : ℤ)) with hMR
  have hAA : A + A ⊆ Icc 0 (2 * m) := by
    intro x hx
    rw [mem_add] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have := mem_Icc.mp (hA ha)
    have := mem_Icc.mp (hA hb)
    rw [mem_Icc]
    constructor <;> omega
  have hsub : (A + A) ∪ (ML ∪ MR) ⊆ Icc 0 (2 * m) := by
    refine union_subset hAA (union_subset ?_ ?_)
    · intro x hx
      rw [hML, mem_image] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      have := hS5 _ s hs
      rw [mem_Icc]
      constructor <;> omega
    · intro x hx
      rw [hMR, mem_image] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      have := hS5 _ s hs
      rw [mem_Icc]
      constructor <;> omega
  have hd1 : Disjoint ML MR := by
    rw [disjoint_left]
    intro x hx hx'
    rw [hML, mem_image] at hx
    rw [hMR, mem_image] at hx'
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', hss'⟩ := hx'
    have := hS5 _ s hs
    have := hS5 _ s' hs'
    omega
  have hd2 : Disjoint (A + A) (ML ∪ MR) := by
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_union] at hx'
    rcases hx' with hx' | hx'
    · rw [hML, mem_image] at hx'
      obtain ⟨s, hs, rfl⟩ := hx'
      exact lemmaC_left hA hs hx
    · rw [hMR, mem_image] at hx'
      obtain ⟨s, hs, rfl⟩ := hx'
      exact lemmaC_right hA hs hx
  have hinjL : Function.Injective (fun s : ℕ => (s : ℤ)) := Nat.cast_injective
  have hinjR : Function.Injective (fun s : ℕ => 2 * m - (s : ℤ)) := by
    intro a b h
    simp only at h
    omega
  have h := card_le_card hsub
  rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1, hML, hMR,
    card_image_of_injective _ hinjL, card_image_of_injective _ hinjR, Int.card_Icc] at h
  omega

lemma card_sub_ge {A : Finset ℤ} {m : ℤ} (h0 : (0 : ℤ) ∈ A) :
    2 * ((Icc 1 m).filter (fun d => d ∈ A - A)).card + 1 ≤ (A - A).card := by
  set P := (Icc 1 m).filter (fun d => d ∈ A - A) with hP
  have hneg : P.image (fun x => -x) ⊆ A - A := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hP, mem_filter, mem_sub] at hy
    obtain ⟨-, a, ha, b, hb, rfl⟩ := hy
    rw [mem_sub]
    exact ⟨b, hb, a, ha, by ring⟩
  have hpos : P ⊆ A - A := fun x hx => (mem_filter.mp hx).2
  have hzero : ({0} : Finset ℤ) ⊆ A - A := by
    intro x hx
    rw [mem_singleton] at hx
    subst hx
    rw [mem_sub]
    exact ⟨0, h0, 0, h0, by ring⟩
  have hsub : P ∪ P.image (fun x => -x) ∪ {0} ⊆ A - A :=
    union_subset (union_subset hpos hneg) hzero
  have hd1 : Disjoint P (P.image (fun x => -x)) := by
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_image] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    rw [hP, mem_filter, mem_Icc] at hx hy
    omega
  have hd2 : Disjoint (P ∪ P.image (fun x => -x)) {0} := by
    rw [disjoint_singleton_right, mem_union, mem_image, not_or]
    constructor
    · intro h
      rw [hP, mem_filter, mem_Icc] at h
      omega
    · rintro ⟨y, hy, hy0⟩
      rw [hP, mem_filter, mem_Icc] at hy
      omega
  have h := card_le_card hsub
  rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1,
    card_image_of_injective _ neg_injective, card_singleton] at h
  omega

lemma card_pos_diff_ge {A : Finset ℤ} {m : ℤ} (h0 : (0 : ℤ) ∈ A) (hm : m ∈ A)
    (H1 : ∀ d ∈ Icc 1 m, d ∉ A - A → m - 5 ≤ d) :
    m ≤ (((Icc 1 m).filter (fun d => d ∈ A - A)).card : ℤ) + (Tset (Lw A) (Rw A m)).card := by
  have hsplit := card_filter_add_card_filter_not (s := Icc 1 m) (fun d => d ∈ A - A)
  have hmiss : (Icc 1 m).filter (fun d => ¬ d ∈ A - A) ⊆
      (Tset (Lw A) (Rw A m)).image (fun t : ℕ => m - (t : ℤ)) := by
    intro d hd
    rw [mem_filter, mem_Icc] at hd
    have h5 := H1 d (mem_Icc.mpr hd.1) hd.2
    rw [mem_image]
    refine ⟨(m - d).toNat, lemmaB h0 hm (by omega) ?_, by omega⟩
    have : m - (((m - d).toNat : ℕ) : ℤ) = d := by omega
    rw [this]
    exact hd.2
  have h2 := card_le_card hmiss
  have h3 := card_image_le (s := Tset (Lw A) (Rw A m)) (f := fun t : ℕ => m - (t : ℤ))
  rw [Int.card_Icc] at hsplit
  omega

/-! ### Proposition P -/

/-- If every missing positive difference is `≥ m - 5` and the two hole patterns have at most six
holes in total, then `A` is not MSTD. -/
theorem propP {A : Finset ℤ} {m : ℤ} (hA : A ⊆ Icc 0 m) (h0 : (0 : ℤ) ∈ A) (hm : m ∈ A)
    (h6 : 6 ≤ m) (H1 : ∀ d ∈ Icc 1 m, d ∉ A - A → m - 5 ≤ d)
    (H2 : (Lw A).card + (Rw A m).card ≤ 6) : ¬ IsMSTD A := by
  unfold IsMSTD
  have hF := checkF (Lw A) (mem_powerset.mpr (filter_subset _ _)) (Rw A m)
    (mem_powerset.mpr (filter_subset _ _)) H2
  have h1 := card_add_le hA h6
  have h2 := card_sub_ge (m := m) h0
  have h3 := card_pos_diff_ge h0 hm H1
  omega

/-! ### Lemma A: counting pairs `{a, a + d}` -/

/-- If every pair `{a, a + d}` (`a ∈ I`) meets `B` and these pairs are pairwise disjoint, then
`B` has at least `|I|` elements inside their union. -/
lemma pairs_card (B I : Finset ℤ) (d : ℤ) (hcov : ∀ a ∈ I, a ∈ B ∨ a + d ∈ B)
    (hdisj : ∀ a ∈ I, a + d ∉ I) :
    I.card ≤ (B.filter (fun x => x ∈ I ∨ x - d ∈ I)).card := by
  refine card_le_card_of_injOn (fun a => if a ∈ B then a else a + d) ?_ ?_
  · intro a ha
    rw [mem_coe] at ha
    rw [mem_coe, mem_filter]
    by_cases h : a ∈ B
    · simp only [h, ↓reduceIte]
      exact ⟨trivial, Or.inl ha⟩
    · simp only [h, ↓reduceIte, add_sub_cancel_right]
      exact ⟨(hcov a ha).resolve_left h, Or.inr ha⟩
  · intro a ha a' ha' heq
    rw [mem_coe] at ha ha'
    dsimp only at heq
    by_cases h : a ∈ B <;> by_cases h' : a' ∈ B
    · simpa only [h, h', ↓reduceIte] using heq
    · simp only [h, h', ↓reduceIte] at heq
      exact absurd (by rw [← heq]; exact ha) (hdisj a' ha')
    · simp only [h, h', ↓reduceIte] at heq
      exact absurd (by rw [heq]; exact ha') (hdisj a ha)
    · simp only [h, h', ↓reduceIte] at heq
      linarith

/-- If moreover `|B| ≤ |I|`, then `B` lies inside the union of the pairs. -/
lemma pairs_cover (B I : Finset ℤ) (d : ℤ) (hcov : ∀ a ∈ I, a ∈ B ∨ a + d ∈ B)
    (hdisj : ∀ a ∈ I, a + d ∉ I) (hc : B.card ≤ I.card) :
    ∀ x ∈ B, x ∈ I ∨ x - d ∈ I := by
  have h1 := pairs_card B I d hcov hdisj
  have h2 : (B.filter (fun x => x ∈ I ∨ x - d ∈ I)).card = B.card :=
    le_antisymm (card_filter_le _ _) (by omega)
  exact card_filter_eq_iff.mp h2

/-- A missing difference `d` forces every pair `{a, a + d} ⊆ [0, m]` to meet `B = [0,m] \ A`. -/
lemma cover {A : Finset ℤ} {m d : ℤ} (hd : d ∉ A - A) (hd0 : 0 ≤ d) {a : ℤ}
    (ha : a ∈ Icc 0 (m - d)) : a ∈ Icc 0 m \ A ∨ a + d ∈ Icc 0 m \ A := by
  rw [mem_Icc] at ha
  by_contra h
  push Not at h
  simp only [mem_sdiff, mem_Icc, not_and, not_not] at h
  apply hd
  rw [mem_sub]
  exact ⟨a + d, h.2 ⟨by omega, by omega⟩, a, h.1 ⟨by omega, by omega⟩, by ring⟩

lemma lemmaA_a {A : Finset ℤ} {m d : ℤ} (hd : d ∉ A - A) (hd1 : 1 ≤ d) (h2 : m < 2 * d) :
    m - d + 1 ≤ ((Icc 0 m \ A).card : ℤ) := by
  have h := pairs_card (Icc 0 m \ A) (Icc 0 (m - d)) d (fun a ha => cover hd (by omega) ha)
    (fun a ha => by rw [mem_Icc] at ha ⊢; omega)
  have h3 := card_filter_le (Icc 0 m \ A) (fun x => x ∈ Icc 0 (m - d) ∨ x - d ∈ Icc 0 (m - d))
  rw [Int.card_Icc] at h
  omega

lemma lemmaA_b {A : Finset ℤ} {m d : ℤ} (hd : d ∉ A - A) (hd1 : 1 ≤ d) (h2 : 2 * d ≤ m) :
    d ≤ ((Icc 0 m \ A).card : ℤ) ∧ m - d + 1 ≤ 2 * ((Icc 0 m \ A).card : ℤ) := by
  constructor
  · have h := pairs_card (Icc 0 m \ A) (Icc 0 (d - 1)) d
      (fun a ha => cover hd (by omega) (by rw [mem_Icc] at ha ⊢; omega))
      (fun a ha => by rw [mem_Icc] at ha ⊢; omega)
    have h3 := card_filter_le (Icc 0 m \ A) (fun x => x ∈ Icc 0 (d - 1) ∨ x - d ∈ Icc 0 (d - 1))
    rw [Int.card_Icc] at h
    omega
  · have hsplit := card_filter_add_card_filter_not (s := Icc 0 (m - d))
      (fun a => a ∈ Icc 0 m \ A)
    have h1 : ((Icc 0 (m - d)).filter (fun a => a ∈ Icc 0 m \ A)).card ≤ (Icc 0 m \ A).card :=
      card_le_card (fun x hx => (mem_filter.mp hx).2)
    have h2' : ((Icc 0 (m - d)).filter (fun a => ¬ a ∈ Icc 0 m \ A)).card ≤
        (Icc 0 m \ A).card := by
      refine card_le_card_of_injOn (· + d) ?_ ?_
      · intro a ha
        rw [mem_coe, mem_filter] at ha
        rw [mem_coe]
        exact (cover hd (by omega) ha.1).resolve_left ha.2
      · intro a _ a' _ h
        simpa using h
    rw [Int.card_Icc] at hsplit
    omega

/-! ### The spans `14 ≤ m ≤ 17` with a missing difference `d ≤ m/2` -/

/-- Generic finishing step: `B = [0,m] \ A` lies in the union of two disjoint pair families, so it
is one of finitely many candidates, which are checked by the kernel. -/
lemma special {A : Finset ℤ} {m d : ℤ} (k : ℕ) (I1 I2 : Finset ℤ)
    (hA : A ⊆ Icc 0 m) (h0 : (0 : ℤ) ∈ A) (hm : m ∈ A) (hd : d ∉ A - A) (hd0 : 0 ≤ d)
    (hk : (Icc 0 m \ A).card ≤ k)
    (hI1 : I1 ⊆ Icc 0 (m - d)) (hI2 : I2 ⊆ Icc 0 (m - d))
    (hj1 : ∀ a ∈ I1, a + d ∉ I1) (hj2 : ∀ a ∈ I2, a + d ∉ I2)
    (hc1 : k ≤ I1.card) (hc2 : k ≤ I2.card)
    (hdec : ∀ B ∈ ((Icc 1 (m - 1)).filter
        (fun x => (x ∈ I1 ∨ x - d ∈ I1) ∧ (x ∈ I2 ∨ x - d ∈ I2))).powerset,
      B.card ≤ k → (∀ a ∈ Icc 0 (m - d), a ∈ B ∨ a + d ∈ B) → ¬ IsMSTD (Icc 0 m \ B)) :
    ¬ IsMSTD A := by
  have hcov : ∀ a ∈ Icc 0 (m - d), a ∈ Icc 0 m \ A ∨ a + d ∈ Icc 0 m \ A :=
    fun a ha => cover hd hd0 ha
  have c1 := pairs_cover (Icc 0 m \ A) I1 d (fun a ha => hcov a (hI1 ha)) hj1 (le_trans hk hc1)
  have c2 := pairs_cover (Icc 0 m \ A) I2 d (fun a ha => hcov a (hI2 ha)) hj2 (le_trans hk hc2)
  have hBX : Icc 0 m \ A ∈ ((Icc 1 (m - 1)).filter
      (fun x => (x ∈ I1 ∨ x - d ∈ I1) ∧ (x ∈ I2 ∨ x - d ∈ I2))).powerset := by
    rw [mem_powerset]
    intro x hx
    rw [mem_filter]
    refine ⟨?_, c1 x hx, c2 x hx⟩
    rw [mem_sdiff, mem_Icc] at hx
    rw [mem_Icc]
    obtain ⟨⟨hx0, hxm⟩, hxA⟩ := hx
    refine ⟨?_, ?_⟩
    · by_contra hc
      exact hxA (by rwa [show x = 0 by omega])
    · by_contra hc
      exact hxA (by rwa [show x = m by omega])
  have := hdec _ hBX hk hcov
  rwa [Finset.sdiff_sdiff_eq_self hA] at this

/-- Contradiction step: too many disjoint pairs. -/
lemma too_many {A : Finset ℤ} {m d : ℤ} (k : ℕ) (I : Finset ℤ) (hd : d ∉ A - A) (hd0 : 0 ≤ d)
    (hk : (Icc 0 m \ A).card ≤ k) (hI : I ⊆ Icc 0 (m - d)) (hj : ∀ a ∈ I, a + d ∉ I)
    (hc : k < I.card) : False := by
  have h := pairs_card (Icc 0 m \ A) I d (fun a ha => cover hd hd0 (hI ha)) hj
  have h3 := card_filter_le (Icc 0 m \ A) (fun x => x ∈ I ∨ x - d ∈ I)
  omega

lemma case14 {A : Finset ℤ} (hA : A ⊆ Icc 0 14) (h0 : (0 : ℤ) ∈ A) (hm : (14 : ℤ) ∈ A)
    (hk : (Icc 0 14 \ A).card ≤ 5) {d : ℤ} (hd : d ∉ A - A) (hd5 : d = 5) : ¬ IsMSTD A := by
  subst hd5
  exact special 5 (Icc 0 4) (Icc 5 9) hA h0 hm hd (by norm_num) hk (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

lemma case15 {A : Finset ℤ} (hA : A ⊆ Icc 0 15) (h0 : (0 : ℤ) ∈ A) (hm : (15 : ℤ) ∈ A)
    (hk : (Icc 0 15 \ A).card ≤ 6) {d : ℤ} (hd : d ∉ A - A) (hd4 : 4 ≤ d) (hd6 : d ≤ 6) :
    ¬ IsMSTD A := by
  obtain rfl | rfl | rfl : d = 4 ∨ d = 5 ∨ d = 6 := by omega
  · exact (too_many 6 (Icc 0 3 ∪ Icc 8 11) hd (by norm_num) hk (by decide) (by decide)
      (by decide)).elim
  · exact special 6 (Icc 0 4 ∪ {10}) ({0} ∪ Icc 6 10) hA h0 hm hd (by norm_num) hk (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  · exact special 6 (Icc 0 5) (Icc 4 9) hA h0 hm hd (by norm_num) hk (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

lemma case16 {A : Finset ℤ} (hA : A ⊆ Icc 0 16) (h0 : (0 : ℤ) ∈ A) (hm : (16 : ℤ) ∈ A)
    (hk : (Icc 0 16 \ A).card ≤ 6) {d : ℤ} (hd : d ∉ A - A) (hd5 : 5 ≤ d) (hd6 : d ≤ 6) :
    ¬ IsMSTD A := by
  obtain rfl | rfl : d = 5 ∨ d = 6 := by omega
  · exact (too_many 6 (Icc 0 4 ∪ Icc 10 11) hd (by norm_num) hk (by decide) (by decide)
      (by decide)).elim
  · exact special 6 (Icc 0 5) (Icc 5 10) hA h0 hm hd (by norm_num) hk (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

lemma case17 {A : Finset ℤ} (hA : A ⊆ Icc 0 17) (h0 : (0 : ℤ) ∈ A) (hm : (17 : ℤ) ∈ A)
    (hk : (Icc 0 17 \ A).card ≤ 6) {d : ℤ} (hd : d ∉ A - A) (hd6 : d = 6) : ¬ IsMSTD A := by
  subst hd6
  exact special 6 (Icc 0 5) (Icc 6 11) hA h0 hm hd (by norm_num) hk (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

/-! ### Proposition Q -/

lemma card_Lw_le {A : Finset ℤ} {m : ℤ} (hm5 : 5 ≤ m) :
    (Lw A).card ≤ (Icc 0 m \ A).card := by
  refine card_le_card_of_injOn (fun i : ℕ => (i : ℤ)) ?_ Nat.cast_injective.injOn
  intro i hi
  rw [mem_coe, Lw, mem_filter, mem_Icc] at hi
  rw [mem_coe, mem_sdiff, mem_Icc]
  dsimp only
  exact ⟨⟨by omega, by omega⟩, hi.2⟩

lemma card_Rw_le {A : Finset ℤ} {m : ℤ} (hm5 : 5 ≤ m) :
    (Rw A m).card ≤ (Icc 0 m \ A).card := by
  refine card_le_card_of_injOn (fun i : ℕ => m - (i : ℤ)) ?_ ?_
  · intro i hi
    rw [mem_coe, Rw, mem_filter, mem_Icc] at hi
    rw [mem_coe, mem_sdiff, mem_Icc]
    dsimp only
    exact ⟨⟨by omega, by omega⟩, hi.2⟩
  · intro a _ b _ h
    simp only at h
    omega

lemma card_LR_le {A : Finset ℤ} {m : ℤ} (hm11 : 11 ≤ m) :
    (Lw A).card + (Rw A m).card ≤ (Icc 0 m \ A).card := by
  have hinjL : Function.Injective (fun s : ℕ => (s : ℤ)) := Nat.cast_injective
  have hinjR : Function.Injective (fun s : ℕ => m - (s : ℤ)) := by
    intro a b h
    simp only at h
    omega
  have hd : Disjoint ((Lw A).image (fun s : ℕ => (s : ℤ))) ((Rw A m).image (fun s : ℕ => m - (s : ℤ))) := by
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_image] at hx hx'
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', hss'⟩ := hx'
    rw [Lw, mem_filter, mem_Icc] at hs
    rw [Rw, mem_filter, mem_Icc] at hs'
    omega
  have hsub : (Lw A).image (fun s : ℕ => (s : ℤ)) ∪ (Rw A m).image (fun s : ℕ => m - (s : ℤ)) ⊆
      Icc 0 m \ A := by
    refine union_subset ?_ ?_
    · intro x hx
      rw [mem_image] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      rw [Lw, mem_filter, mem_Icc] at hs
      rw [mem_sdiff, mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hs.2⟩
    · intro x hx
      rw [mem_image] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      rw [Rw, mem_filter, mem_Icc] at hs
      rw [mem_sdiff, mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hs.2⟩
  have h := card_le_card hsub
  rw [card_union_of_disjoint hd, card_image_of_injective _ hinjL,
    card_image_of_injective _ hinjR] at h
  exact h

/-- **Proposition Q.** If `min A = 0`, `max A = m`, `|A| ≥ 10` and at most six elements of
`[0, m]` are missing from `A`, then `A` is not MSTD. -/
theorem propQ {A : Finset ℤ} {m : ℤ} (hA : A ⊆ Icc 0 m) (h0 : (0 : ℤ) ∈ A) (hm : m ∈ A)
    (h10 : 10 ≤ A.card) (hk : (Icc 0 m \ A).card ≤ 6) : ¬ IsMSTD A := by
  have hcard : (A.card : ℤ) + (Icc 0 m \ A).card = m + 1 := by
    have := card_sdiff_add_card_eq_card hA
    rw [Int.card_Icc] at this
    omega
  by_cases hlong : ∃ d ∈ Icc 1 m, d ∉ A - A ∧ 2 * d ≤ m
  · obtain ⟨d, hd, hdA, h2d⟩ := hlong
    rw [mem_Icc] at hd
    obtain ⟨hb1, hb2⟩ := lemmaA_b hdA hd.1 h2d
    have hm14 : 14 ≤ m := by omega
    have hm17 : m ≤ 17 := by omega
    interval_cases m
    · exact case14 hA h0 hm (by omega) hdA (by omega)
    · exact case15 hA h0 hm hk hdA (by omega) (by omega)
    · exact case16 hA h0 hm hk hdA (by omega) (by omega)
    · exact case17 hA h0 hm hk hdA (by omega)
  · push Not at hlong
    have H1 : ∀ d ∈ Icc 1 m, d ∉ A - A → m - 5 ≤ d := by
      intro d hd hdA
      have h2 := hlong d hd hdA
      rw [mem_Icc] at hd
      have := lemmaA_a hdA hd.1 h2
      omega
    have H2 : (Lw A).card + (Rw A m).card ≤ 6 := by
      by_cases h11 : 11 ≤ m
      · have := card_LR_le (A := A) h11
        omega
      · have hL := card_Lw_le (A := A) (m := m) (by omega)
        have hR := card_Rw_le (A := A) (m := m) (by omega)
        omega
    exact propP hA h0 hm (by omega) H1 H2

/-! ### Upper bound -/

theorem upper (n : ℕ) (hn : 16 ≤ n) {A : Finset ℤ} (hA : A ⊆ Ico 0 (n : ℤ)) (h : IsMSTD A) :
    A.card ≤ n - 7 := by
  by_contra hc
  push Not at hc
  have hne : A.Nonempty := by
    rw [← card_pos]
    omega
  set a0 := A.min' hne with ha0def
  set a1 := A.max' hne with ha1def
  have hA' : A.image (· - a0) ⊆ Icc 0 (a1 - a0) := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have h1 : a0 ≤ a := min'_le A a ha
    have h2 : a ≤ a1 := le_max' A a ha
    rw [mem_Icc]
    constructor <;> omega
  have h0 : (0 : ℤ) ∈ A.image (· - a0) := mem_image.mpr ⟨a0, min'_mem A hne, by ring⟩
  have hm : a1 - a0 ∈ A.image (· - a0) := mem_image.mpr ⟨a1, max'_mem A hne, rfl⟩
  have hcard : (A.image (· - a0)).card = A.card := card_image_of_injective _ sub_left_injective
  have hmst : IsMSTD (A.image (· - a0)) := (isMSTD_image_sub A a0).mpr h
  have ha0 : 0 ≤ a0 := (mem_Ico.mp (hA (min'_mem A hne))).1
  have ha1 : a1 < n := (mem_Ico.mp (hA (max'_mem A hne))).2
  have hk : (Icc 0 (a1 - a0) \ A.image (· - a0)).card ≤ 6 := by
    have := card_sdiff_add_card_eq_card hA'
    rw [Int.card_Icc, hcard] at this
    omega
  exact propQ hA' h0 hm (by omega) hk hmst

/-! ### Lower bound: Chu's family -/

/-- Chu's family `K m = [0, m+7] \ {3,5,6,m+1,m+2,m+3,m+5} = {0,1,2,4} ∪ [7,m] ∪ {m+4,m+6,m+7}`. -/
def K (m : ℤ) : Finset ℤ := {0, 1, 2, 4} ∪ Icc 7 m ∪ {m + 4, m + 6, m + 7}

lemma mem_K {m x : ℤ} : x ∈ K m ↔ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 4 ∨ (7 ≤ x ∧ x ≤ m) ∨
    x = m + 4 ∨ x = m + 6 ∨ x = m + 7 := by
  simp only [K, mem_union, mem_insert, mem_singleton, mem_Icc]
  tauto

lemma card_K {m : ℤ} (hm : 8 ≤ m) : (K m).card = (m + 1).toNat := by
  have h1 : Disjoint ({0, 1, 2, 4} : Finset ℤ) (Icc 7 m) := by
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_Icc] at hx'
    omega
  have h2 : Disjoint ({0, 1, 2, 4} ∪ Icc 7 m) ({m + 4, m + 6, m + 7} : Finset ℤ) := by
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_union, mem_insert, mem_singleton, mem_Icc] at hx hx'
    omega
  have h3 : ({m + 4, m + 6, m + 7} : Finset ℤ).card = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp only [mem_singleton]
      omega
    · simp only [mem_insert, mem_singleton]
      omega
  have h4 : ({0, 1, 2, 4} : Finset ℤ).card = 4 := by decide
  unfold K
  rw [card_union_of_disjoint h2, card_union_of_disjoint h1, h3, h4, Int.card_Icc]
  omega

lemma K_sub {m : ℤ} (hm : 8 ≤ m) :
    K m - K m ⊆ ((Icc (-(m + 7)) (m + 7)).erase (m + 1)).erase (-(m + 1)) := by
  intro z hz
  rw [mem_sub] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  rw [mem_K] at hx hy
  rw [mem_erase, mem_erase, mem_Icc]
  omega

lemma K_add {m : ℤ} (hm : 8 ≤ m) : (Icc 0 (2 * m + 14)).erase (2 * m + 9) ⊆ K m + K m := by
  intro s hs
  rw [mem_erase, mem_Icc] at hs
  rw [mem_add]
  suffices ∃ x, x ∈ K m ∧ s - x ∈ K m by
    obtain ⟨x, hx, hy⟩ := this
    exact ⟨x, hx, s - x, hy, by ring⟩
  simp only [mem_K]
  rcases (by omega : s ≤ 2 ∨ s = 3 ∨ (4 ≤ s ∧ s ≤ 6) ∨ (7 ≤ s ∧ s ≤ m) ∨
      (m + 1 ≤ s ∧ s ≤ m + 2) ∨ (m + 3 ≤ s ∧ s ≤ m + 4) ∨ (m + 5 ≤ s ∧ s ≤ m + 6) ∨
      s = m + 7 ∨ s = m + 8 ∨ s = m + 9 ∨ (m + 10 ≤ s ∧ s ≤ m + 11) ∨
      (m + 12 ≤ s ∧ s ≤ 2 * m + 4) ∨ (2 * m + 5 ≤ s ∧ s ≤ 2 * m + 6) ∨ s = 2 * m + 7 ∨
      s = 2 * m + 8 ∨ (2 * m + 10 ≤ s ∧ s ≤ 2 * m + 11) ∨
      (2 * m + 12 ≤ s ∧ s ≤ 2 * m + 13) ∨ s = 2 * m + 14) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨0, by omega, by omega⟩
  · exact ⟨1, by omega, by omega⟩
  · exact ⟨4, by omega, by omega⟩
  · exact ⟨0, by omega, by omega⟩
  · exact ⟨s - m, by omega, by omega⟩
  · exact ⟨4, by omega, by omega⟩
  · exact ⟨s - m - 4, by omega, by omega⟩
  · exact ⟨0, by omega, by omega⟩
  · exact ⟨4, by omega, by omega⟩
  · exact ⟨2, by omega, by omega⟩
  · exact ⟨4, by omega, by omega⟩
  · exact ⟨s - m - 4, by omega, by omega⟩
  · exact ⟨s - m - 6, by omega, by omega⟩
  · exact ⟨m, by omega, by omega⟩
  · exact ⟨m + 4, by omega, by omega⟩
  · exact ⟨m + 4, by omega, by omega⟩
  · exact ⟨m + 6, by omega, by omega⟩
  · exact ⟨m + 7, by omega, by omega⟩

theorem K_mstd {m : ℤ} (hm : 8 ≤ m) : IsMSTD (K m) := by
  unfold IsMSTD
  have h1 := card_le_card (K_sub hm)
  have h2 := card_le_card (K_add hm)
  have he1 : m + 1 ∈ Icc (-(m + 7)) (m + 7) := by rw [mem_Icc]; constructor <;> omega
  have he2 : -(m + 1) ∈ (Icc (-(m + 7)) (m + 7)).erase (m + 1) := by
    rw [mem_erase, mem_Icc]; refine ⟨by omega, by omega, by omega⟩
  have he3 : 2 * m + 9 ∈ Icc 0 (2 * m + 14) := by rw [mem_Icc]; constructor <;> omega
  rw [card_erase_of_mem he2, card_erase_of_mem he1, Int.card_Icc] at h1
  rw [card_erase_of_mem he3, Int.card_Icc] at h2
  omega

/-! ### Main theorems -/

/-- **Chu's Conjecture 1.3 / OEIS A305503.** For `n ≥ 16`, the largest MSTD subset of
`{0, …, n-1}` has exactly `n - 7` elements. -/
theorem main (n : ℕ) (hn : 16 ≤ n) :
    IsGreatest {k | ∃ A : Finset ℤ, A ⊆ Ico 0 (n : ℤ) ∧ IsMSTD A ∧ A.card = k} (n - 7) := by
  constructor
  · refine ⟨K ((n : ℤ) - 8), ?_, K_mstd (by omega), ?_⟩
    · intro x hx
      rw [mem_K] at hx
      rw [mem_Ico]
      omega
    · rw [card_K (by omega)]
      omega
  · rintro k ⟨A, hA, hM, rfl⟩
    exact upper n hn hA hM

/-- The arXiv-v2 form: MSTD subsets of `{0, …, n-1}` containing `0` and `n - 1`. -/
theorem main_spanning (n : ℕ) (hn : 16 ≤ n) :
    IsGreatest {k | ∃ A : Finset ℤ, A ⊆ Ico 0 (n : ℤ) ∧ (0 : ℤ) ∈ A ∧ ((n : ℤ) - 1) ∈ A ∧
      IsMSTD A ∧ A.card = k} (n - 7) := by
  constructor
  · refine ⟨K ((n : ℤ) - 8), ?_, ?_, ?_, K_mstd (by omega), ?_⟩
    · intro x hx
      rw [mem_K] at hx
      rw [mem_Ico]
      omega
    · rw [mem_K]; omega
    · rw [mem_K]; omega
    · rw [card_K (by omega)]
      omega
  · rintro k ⟨A, hA, -, -, hM, rfl⟩
    exact upper n hn hA hM

end A305503

#print axioms A305503.main
#print axioms A305503.main_spanning
