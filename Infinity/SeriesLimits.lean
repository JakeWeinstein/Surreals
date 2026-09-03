/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.CanonicalSum
import Infinity.MicroKernel

/-!
# The Bridge Theorem: summation is approximation, completed through gaps

This repo proved that the two semantics of surreal analysis come apart: ℕ-sequences converge
only if eventually constant (`tendstoSurreal_atTop_iff_eventuallyEq`), yet every strictly
dominating series has a canonical Hahn sum (`Infinity.Summation`, `Infinity.CanonicalSum`).
This file proves the theorem that joins the two semantics back together, following the
informal blueprint of Rubinstein-Salzedo–Swaminathan, *Analysis on Surreal Numbers*
(arXiv:1307.7392; "RSS" below), whose Definition 19 limit operator is exactly a
liminf/limsup of Dedekind representations — that is, of our cut-valued `liminfCut`/`limsupCut`.

## The Bridge Theorem

For a strictly dominating series `t` with partial sums `sₙ`, the cut-valued lower and upper
limits of `(sₙ)` land **exactly on the edges `sumLo t`/`sumHi t` of the band of Hahn sums**,
according to the cofinal signs of the terms:

* `sumLo_le_liminfCut` / `limsupCut_le_sumHi`: always,
  `sumLo t ≤ liminfCut ≤ limsupCut ≤ sumHi t`;
* `liminfCut_partialSum_eq_sumLo`: if `0 < t n` cofinally, `liminfCut = sumLo t`;
* `limsupCut_partialSum_eq_sumHi`: if `t n < 0` cofinally, `limsupCut = sumHi t`;
* `limsupCut_partialSum_eq_sumLo` / `liminfCut_partialSum_eq_sumHi`: if the terms are
  eventually of one sign, **both** limits collapse onto the single corresponding edge.

The naive conjecture `liminfCut = sumLo ∧ limsupCut = sumHi` is therefore **false in
general** (for an eventually-positive series both limits equal `sumLo`), and the sign
dichotomy above is its true form. Consequences:

* `isHahnSum_iff_fits_liminfCut_limsupCut`: for a series with terms of both signs cofinally,
  **the Hahn sums are exactly the surreals squeezed between the lower and upper limits of
  the partial sums** — summation *is* approximation;
* `hahnSum_eq_simplestBtwn_liminfCut_limsupCut`: the canonical (birthday-simplest) sum is
  the simplest surreal between the two limits of its own partial sums.

## Gaps as first-class objects

* `Cut.IsGap` (`¬ Cut.Numeric`, matching RSS Definitions 5 and 25: a Dedekind section of
  `No` realized by no surreal; `⊥ = 𝐎𝐟𝐟` and `⊤ = 𝐎𝐧` count as gaps, as in RSS §2.2),
  with the max/min-free characterization `Cut.isGap_iff` and `Cut.isGap_bot`/`Cut.isGap_top`.
* `TendstoCut f l c`: sharp order convergence, `liminfCut = limsupCut = c`. For a constant
  sequence the two cuts hug the value without meeting, so `TendstoCut` and `TendstoSurreal`
  are *complementary* notions — and indeed:
* `TendstoCut.not_numeric` / `TendstoCut.isGap`: **a small-indexed family of surreals can
  only order-converge sharply to a gap** — the positive face of the eventual-constancy
  obstruction. In RSS's language: set-length sequences reach gaps, never numbers.
* `isGap_sumLo` / `isGap_sumHi`: the band edges of every strictly dominating series are
  gaps; with the collapse theorems, the partial sums of a one-signed series converge (in
  the sharp cut sense) to a genuine gap: `tendstoCut_partialSum_of_eventually_pos`. This is
  the ℕ-length shadow of RSS Example 24 (a Cauchy sequence converging to a gap, witnessing
  that `No` is not Cauchy complete).
* `microGap`, `tendstoCut_inv_natCast`, `isGap_microGap`: the sequence `1/n` sharply
  converges to the gap between the infinitesimals and the positive non-infinitesimals —
  the positive completion of the gap theorem `not_tendstoSurreal_inv_natCast`.
* `exists_pos_microInner`, `isGap_microHaloGap`: the micro-halo of `Infinity.MicroKernel`
  is nondegenerate (it contains positive elements) and its upper boundary is a gap.

The flagship instance `geometric_gap_convergence` assembles the story for `Σ ω⁻ᵏ`: its
partial sums sharply converge to the gap `sumLo`, and its canonical sum `ω/(ω−1)` is the
closest surreal beyond that gap.
-/

open ArchimedeanClass Filter Finset Set

universe u v

noncomputable section

namespace Surreal

/-! ### Coinitiality for small families

`exists_pos_forall_lt` (Limits.lean) works for countable families; the same Conway cut
`!{{0} | range z}` works for any *small* family. Smallness is the true boundary: it is
what makes the right set of the cut a legal set of options. -/

/-- **Small coinitiality**: any small-indexed family of positive surreals has a common
positive strict lower bound. -/
theorem exists_pos_forall_lt_of_small {ι : Type v} [Small.{u} ι] {z : ι → Surreal.{u}}
    (hz : ∀ i, 0 < z i) : ∃ e : Surreal.{u}, 0 < e ∧ ∀ i, e < z i := by
  have H : ∀ a ∈ ({0} : Set Surreal.{u}), ∀ b ∈ Set.range z, a < b := by
    rintro a rfl b ⟨i, rfl⟩
    exact hz i
  exact ⟨!{{0} | Set.range z}'H, lt_ofSets_of_mem_left (H := H) rfl,
    fun i ↦ ofSets_lt_of_mem_right (H := H) ⟨i, rfl⟩⟩

/-! ### Membership formulas for the limit cuts along `atTop`

The left/right sets of `liminfCut`/`limsupCut` along `atTop` on `ℕ`, computed explicitly.
These are exactly the classes appearing in RSS Definition 19: the left set of the liminf
cut is their class `{a : a < sup (⋃ᵢ⋂_{j≥i} ℒ_{a_j})}`, and dually. -/

private theorem cut_limsup_le_of_eventually_le {ι : Type*} {l : Filter ι} {u : ι → Cut}
    {a : Cut} (h : ∀ᶠ i in l, u i ≤ a) : limsup u l ≤ a := by
  rw [limsup_eq]
  exact sInf_le h

private theorem cut_le_liminf_of_eventually_le {ι : Type*} {l : Filter ι} {u : ι → Cut}
    {a : Cut} (h : ∀ᶠ i in l, a ≤ u i) : a ≤ liminf u l := by
  rw [liminf_eq]
  exact le_sSup h

variable {f : ℕ → Surreal} {z x : Surreal}

theorem mem_left_liminfCut_atTop :
    z ∈ (liminfCut f atTop).left ↔ ∃ n, ∀ k, n ≤ k → z < f k := by
  rw [liminfCut, liminf_eq, Cut.left_sSup]
  constructor
  · intro hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨a, ha, hza⟩ := hz
    obtain ⟨n, hn⟩ := eventually_atTop.1 ha
    exact ⟨n, fun k hk ↦ Set.mem_Iio.1 (Cut.left_subset_left_iff.2 (hn k hk) hza)⟩
  · rintro ⟨n, hn⟩
    rw [Set.mem_iUnion₂]
    refine ⟨Cut.rightSurreal z, eventually_atTop.2 ⟨n, fun k hk ↦ ?_⟩, Set.mem_Iic.2 le_rfl⟩
    exact Cut.rightSurreal_le_iff.2 (Set.mem_Iio.2 (hn k hk))

theorem mem_right_limsupCut_atTop :
    z ∈ (limsupCut f atTop).right ↔ ∃ n, ∀ k, n ≤ k → f k < z := by
  rw [limsupCut, limsup_eq, Cut.right_sInf]
  constructor
  · intro hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨a, ha, hza⟩ := hz
    obtain ⟨n, hn⟩ := eventually_atTop.1 ha
    exact ⟨n, fun k hk ↦ Cut.left_lt_right (Cut.rightSurreal_le_iff.1 (hn k hk)) hza⟩
  · rintro ⟨n, hn⟩
    rw [Set.mem_iUnion₂]
    refine ⟨Cut.leftSurreal z, eventually_atTop.2 ⟨n, fun k hk ↦ ?_⟩, Set.mem_Ici.2 le_rfl⟩
    exact Cut.rightSurreal_le_iff.2 (Set.mem_Iio.2 (hn k hk))

theorem mem_right_liminfCut_atTop :
    z ∈ (liminfCut f atTop).right ↔ ∀ n, ∃ k, n ≤ k ∧ f k ≤ z := by
  rw [← Cut.notMem_left_iff]
  simp only [mem_left_liminfCut_atTop]
  push Not
  rfl

theorem mem_left_limsupCut_atTop :
    z ∈ (limsupCut f atTop).left ↔ ∀ n, ∃ k, n ≤ k ∧ z ≤ f k := by
  rw [← Cut.notMem_right_iff]
  simp only [mem_right_limsupCut_atTop]
  push Not
  rfl

/-! ### Gaps as first-class objects

RSS Definition 5 (after Conway): a *gap* is a Dedekind section of `No` realized by no
number. In the `Cut` lattice, the sections realized by a number `x` are exactly the two
numeric cuts `leftSurreal x` and `rightSurreal x` (this is RSS Definition 25's
identification), so a gap is precisely a non-`Numeric` cut. `⊥ = 𝐎𝐟𝐟` and `⊤ = 𝐎𝐧` are
gaps, as in RSS §2.2. -/

/-- A cut is a **gap** when no surreal realizes it (RSS Definitions 5 and 25). -/
def Cut.IsGap (c : Cut) : Prop :=
  ¬ c.Numeric

/-- `𝐎𝐟𝐟`, the gap below all surreals, is a gap. -/
theorem Cut.isGap_bot : (⊥ : Cut).IsGap := fun hc ↦ Cut.Numeric.ne_bot ⊥ (hx := hc) rfl

/-- `𝐎𝐧`, the gap above all surreals, is a gap. -/
theorem Cut.isGap_top : (⊤ : Cut).IsGap := fun hc ↦ Cut.Numeric.ne_top ⊤ (hx := hc) rfl

/-- **The max/min-free characterization of gaps**: a cut is a gap iff its left set has no
maximum and its right set has no minimum. -/
theorem Cut.isGap_iff {c : Cut} :
    c.IsGap ↔ (∀ x ∈ c.left, ∃ y ∈ c.left, x < y) ∧ ∀ x ∈ c.right, ∃ y ∈ c.right, y < x := by
  constructor
  · intro hc
    constructor
    · intro x hx
      by_contra hmax
      push Not at hmax
      refine hc ?_
      have hcx : c = Cut.rightSurreal x := by
        ext w
        simp only [Cut.left_rightSurreal, Set.mem_Iic]
        exact ⟨fun hw ↦ hmax w hw, fun hw ↦ c.isLowerSet_left hw hx⟩
      rw [hcx]
      exact Cut.Numeric.rightSurreal x
    · intro x hx
      by_contra hmin
      push Not at hmin
      refine hc ?_
      have hcx : c = Cut.leftSurreal x := by
        refine Cut.ext' (Set.ext fun w ↦ ?_)
        simp only [Cut.right_leftSurreal, Set.mem_Ici]
        exact ⟨fun hw ↦ hmin w hw, fun hw ↦ c.isUpperSet_right hw hx⟩
      rw [hcx]
      exact Cut.Numeric.leftSurreal x
  · rintro ⟨hl, hr⟩ hc
    rw [Cut.numeric_def] at hc
    obtain ⟨y, hy⟩ | ⟨y, hy⟩ := hc
    · obtain ⟨w, hw, hwy⟩ := hr y (by rw [← hy]; exact Cut.mem_right_leftSurreal.2 le_rfl)
      rw [← hy] at hw
      exact absurd (Cut.mem_right_leftSurreal.1 hw) (not_le.2 hwy)
    · obtain ⟨w, hw, hwy⟩ := hl y (by rw [← hy]; exact Cut.mem_left_rightSurreal.2 le_rfl)
      rw [← hy] at hw
      exact absurd (Cut.mem_left_rightSurreal.1 hw) (not_le.2 hwy)

/-! ### Sharp order convergence: `TendstoCut`

`TendstoSurreal f l x` says the two cuts hugging `x` pinch `liminfCut`/`limsupCut` from
outside (`tendstoSurreal_iff_cuts`); a constant sequence has `liminfCut = leftSurreal x`
and `limsupCut = rightSurreal x`, which never meet. `TendstoCut f l c` is the *sharp*
regime: the two limit cuts coincide. The theorem below shows these regimes are mutually
exclusive in the strongest possible sense: a sharp limit of a small-indexed family is
never a numeric cut. Approximation on `No` terminates at numbers (only trivially) or at
gaps (only sharply). -/

/-- Sharp order convergence of a surreal family to a single cut: the cut-valued lower and
upper limits coincide at `c`. This is the cut formulation of convergence via RSS
Definition 19/20: their limit `ℓ(𝔄)` exists iff the pair (liminf-left, limsup-right)
forms a Dedekind representation, which for a gap means exactly `liminfCut = limsupCut`. -/
def TendstoCut {ι : Type*} (f : ι → Surreal) (l : Filter ι) (c : Cut) : Prop :=
  liminfCut f l = c ∧ limsupCut f l = c

/-- **Sharp limits are never numbers**: if a small-indexed family of surreals order-converges
sharply (liminf = limsup) to a cut, that cut is realized by no surreal. This upgrades the
eventual-constancy obstruction into a positive statement about where limits live. -/
theorem TendstoCut.not_numeric {ι : Type v} [Small.{u} ι] {l : Filter ι} [l.NeBot]
    {f : ι → Surreal.{u}} {c : Cut.{u}} (h : TendstoCut f l c) : ¬ c.Numeric := by
  intro hc
  rw [Cut.numeric_def] at hc
  obtain ⟨x, hx⟩ | ⟨x, hx⟩ := hc
  · -- If the common value were `leftSurreal x`, the family would eventually be `< x`;
    -- small coinitiality then pushes the limsup strictly below `leftSurreal x`.
    have h2 : limsup (fun i ↦ Cut.rightSurreal (f i)) l = Cut.leftSurreal x :=
      h.2.trans hx.symm
    rw [limsup_eq] at h2
    have hmem := Cut.leftSurreal_mem_of_sInf_eq h2
    have hev : ∀ᶠ i in l, f i < x :=
      hmem.mono fun i hi ↦ Cut.mem_left_leftSurreal.1 (Cut.rightSurreal_le_iff.1 hi)
    obtain ⟨e, he0, he⟩ := exists_pos_forall_lt_of_small
      (z := fun i ↦ if f i < x then x - f i else 1)
      (fun i ↦ by split <;> simp_all [sub_pos])
    have hev2 : ∀ᶠ i in l, Cut.rightSurreal (f i) ≤ Cut.rightSurreal (x - e) := by
      refine hev.mono fun i hi ↦ Cut.rightSurreal.monotone ?_
      have hei := he i
      rw [if_pos hi] at hei
      linarith
    have hle : limsupCut f l ≤ Cut.rightSurreal (x - e) :=
      cut_limsup_le_of_eventually_le hev2
    rw [h.2.trans hx.symm] at hle
    exact absurd hle (not_le.2 (Cut.rightSurreal_lt_leftSurreal_iff.2 (by linarith)))
  · -- Dually for `rightSurreal x`, via the liminf.
    have h1 : liminf (fun i ↦ Cut.leftSurreal (f i)) l = Cut.rightSurreal x :=
      h.1.trans hx.symm
    rw [liminf_eq] at h1
    have hmem := Cut.rightSurreal_mem_of_sSup_eq h1
    have hev : ∀ᶠ i in l, x < f i :=
      hmem.mono fun i hi ↦ Cut.mem_right_rightSurreal.1 (Cut.le_leftSurreal_iff.1 hi)
    obtain ⟨e, he0, he⟩ := exists_pos_forall_lt_of_small
      (z := fun i ↦ if x < f i then f i - x else 1)
      (fun i ↦ by split <;> simp_all [sub_pos])
    have hev2 : ∀ᶠ i in l, Cut.leftSurreal (x + e) ≤ Cut.leftSurreal (f i) := by
      refine hev.mono fun i hi ↦ Cut.leftSurreal.monotone ?_
      have hei := he i
      rw [if_pos hi] at hei
      linarith
    have hle : Cut.leftSurreal (x + e) ≤ liminfCut f l :=
      cut_le_liminf_of_eventually_le hev2
    rw [h.1.trans hx.symm] at hle
    exact absurd hle (not_le.2 (Cut.rightSurreal_lt_leftSurreal_iff.2 (by linarith)))

/-- Sharp limits of small-indexed families are gaps. -/
theorem TendstoCut.isGap {ι : Type v} [Small.{u} ι] {l : Filter ι} [l.NeBot]
    {f : ι → Surreal.{u}} {c : Cut.{u}} (h : TendstoCut f l c) : c.IsGap :=
  h.not_numeric

/-! ### The gap below the sequence `1/n`

`not_tendstoSurreal_inv_natCast` (Limits.lean) proved that `1/n` converges to no surreal.
Here is its positive completion: `1/n` *does* converge, sharply, to the gap `microGap`
between the infinitesimals and the positive non-infinitesimals (the "`1/∞`" location; in
RSS's classification an honest gap, unlike `{𝐍𝐨_{≤0} | 𝐍𝐨_{>0}}` which their Definition 25
identifies with `0`). -/

/-- The gap between the infinitesimals and the positive non-infinitesimal surreals. -/
def microGap : Cut :=
  ⨆ w : {w : Surreal // Infinitesimal w}, Cut.rightSurreal w.1

theorem mem_left_microGap : z ∈ microGap.left ↔ Infinitesimal z ∨ z ≤ 0 := by
  unfold microGap
  simp only [Cut.left_iSup, Set.mem_iUnion, Cut.left_rightSurreal, Set.mem_Iic,
    Subtype.exists, exists_prop]
  constructor
  · rintro ⟨w, hw, hzw⟩
    rcases le_or_gt z 0 with hz | hz
    · exact .inr hz
    · refine .inl (lt_of_lt_of_le hw (ArchimedeanClass.mk_le_mk_of_abs ?_))
      rw [abs_of_pos hz]
      exact hzw.trans (le_abs_self w)
  · rintro (hz | hz)
    · exact ⟨z, hz, le_rfl⟩
    · exact ⟨0, infinitesimal_zero, hz⟩

/-- **`1/n` sharply converges to the micro gap.** -/
theorem tendstoCut_inv_natCast :
    TendstoCut (fun n : ℕ ↦ (n : Surreal)⁻¹) atTop microGap := by
  have key : ∀ z : Surreal, (Infinitesimal z ∨ z ≤ 0) ↔
      ∀ m : ℕ, ∃ k, m ≤ k ∧ z ≤ (k : Surreal)⁻¹ := by
    intro z
    constructor
    · rintro hz m
      refine ⟨max m 1, le_max_left _ _, ?_⟩
      have hk0 : 0 < max m 1 := lt_of_lt_of_le one_pos (le_max_right m 1)
      have hkS : (0 : Surreal) < ((max m 1 : ℕ) : Surreal) := by exact_mod_cast hk0
      rcases hz with hz | hz
      · have hq : (0 : ℚ) < 1 / ((max m 1 : ℕ) : ℚ) := by positivity
        have h1 := (hz.abs_lt_ratCast hq).le
        have h2 : ((1 / ((max m 1 : ℕ) : ℚ) : ℚ) : Surreal) = ((max m 1 : ℕ) : Surreal)⁻¹ := by
          push_cast
          ring
        rw [h2] at h1
        exact (le_abs_self z).trans h1
      · exact hz.trans (inv_nonneg.2 hkS.le)
    · intro hz
      rcases le_or_gt z 0 with hz0 | hz0
      · exact .inr hz0
      · refine .inl (infinitesimal_of_pos_of_forall_le_ratCast hz0 fun q hq ↦ ?_)
        obtain ⟨m, hm⟩ := exists_nat_gt q⁻¹
        obtain ⟨k, hk, hzk⟩ := hz (m + 1)
        have hmk : q⁻¹ < (k : ℚ) := by
          refine hm.trans_le ?_
          exact_mod_cast (Nat.le_succ m).trans hk
        have hinv : (k : ℚ)⁻¹ < q := inv_lt_of_inv_lt₀ hq hmk
        have h2 : (((k : ℚ)⁻¹ : ℚ) : Surreal) = (k : Surreal)⁻¹ := by push_cast; ring
        refine hzk.trans ?_
        rw [← h2]
        exact_mod_cast hinv.le
  constructor
  · refine Cut.ext (Set.ext fun z ↦ ?_)
    rw [mem_left_liminfCut_atTop, mem_left_microGap]
    constructor
    · rintro ⟨n, hn⟩
      exact (key z).2 fun m ↦ ⟨max m n, le_max_left _ _, (hn _ (le_max_right _ _)).le⟩
    · intro hz
      refine ⟨1, fun k hk ↦ ?_⟩
      have hk0 : 0 < k := hk
      have hkS : (0 : Surreal) < (k : Surreal) := by exact_mod_cast hk0
      obtain ⟨j, hj, hzj⟩ := (key z).1 hz (k + 1)
      have hkj : k < j := (Nat.lt_succ_self k).trans_le hj
      have hkjS : (k : Surreal) < (j : Surreal) := by exact_mod_cast hkj
      have hjS : (0 : Surreal) < (j : Surreal) := hkS.trans hkjS
      exact hzj.trans_lt ((inv_lt_inv₀ hjS hkS).2 hkjS)
  · refine Cut.ext (Set.ext fun z ↦ ?_)
    rw [mem_left_limsupCut_atTop, mem_left_microGap]
    exact ⟨fun hz ↦ (key z).2 hz, fun hz ↦ (key z).1 hz⟩

/-- **The micro gap is a gap**: an instance of `TendstoCut.isGap`. The sequence `1/n`
converges — to a location that is provably not a surreal number. -/
theorem isGap_microGap : microGap.{u}.IsGap :=
  TendstoCut.isGap tendstoCut_inv_natCast.{u}

/-! ### The micro-halo boundary is a gap

`Infinity.MicroKernel` built the fractal kernel counterexample on the micro-halo
`{w | ∀ n, mk (ω⁻ⁿ) < mk w}`. Small coinitiality shows the halo contains positive
elements, and its upper boundary cut is a genuine gap. -/

/-- The micro-halo is nondegenerate: it contains positive surreals (a common positive
lower bound for all the scaled powers `ω⁻ⁿ/(k+1)`). -/
theorem exists_pos_microInner : ∃ w : Surreal.{u}, 0 < w ∧ MicroInner w := by
  obtain ⟨e, he0, he⟩ := exists_pos_forall_lt_of_small
    (z := fun m : ℕ ↦
      |((ω^ (1 : Surreal.{u}))⁻¹) ^ m.unpair.1| / ((m.unpair.2 : Surreal) + 1))
    (fun m ↦ by
      have h1 : ((ω^ (1 : Surreal.{u}))⁻¹) ^ m.unpair.1 ≠ 0 :=
        pow_ne_zero _ (inv_ne_zero (wpow_pos (1 : Surreal)).ne')
      have h2 : (0 : Surreal.{u}) < (m.unpair.2 : Surreal) + 1 := by positivity
      exact div_pos (abs_pos.2 h1) h2)
  refine ⟨e, he0, fun n ↦ ?_⟩
  rw [ArchimedeanClass.mk_lt_mk]
  intro j
  have hej : e < |((ω^ (1 : Surreal.{u}))⁻¹) ^ n| / ((j : Surreal) + 1) := by
    have h := he (Nat.pair n j)
    rwa [Nat.unpair_pair] at h
  have hj1 : (0 : Surreal) < (j : Surreal) + 1 := by positivity
  have h3 : ((j : Surreal) + 1) * e < |((ω^ (1 : Surreal.{u}))⁻¹) ^ n| := by
    rw [mul_comm]
    exact (lt_div_iff₀ hj1).1 hej
  have h4 : (j : Surreal) * e ≤ ((j : Surreal) + 1) * e :=
    mul_le_mul_of_nonneg_right (by linarith) he0.le
  rw [nsmul_eq_mul, abs_of_pos he0]
  exact h4.trans_lt h3

/-- The upper boundary of the micro-halo, as a cut. -/
def microHaloGap : Cut :=
  ⨆ w : {w : Surreal // MicroInner w}, Cut.rightSurreal w.1

theorem mem_left_microHaloGap : z ∈ microHaloGap.left ↔ ∃ w, MicroInner w ∧ z ≤ w := by
  unfold microHaloGap
  simp only [Cut.left_iSup, Set.mem_iUnion, Cut.left_rightSurreal, Set.mem_Iic,
    Subtype.exists, exists_prop]

theorem mem_right_microHaloGap : z ∈ microHaloGap.right ↔ ∀ w, MicroInner w → w < z := by
  unfold microHaloGap
  simp only [Cut.right_iSup, Set.mem_iInter, Cut.right_rightSurreal, Set.mem_Ioi,
    Subtype.forall]

/-- **The micro-halo boundary is a gap.** -/
theorem isGap_microHaloGap : microHaloGap.{u}.IsGap := by
  obtain ⟨e, he0, he⟩ := exists_pos_microInner.{u}
  rw [Cut.isGap_iff]
  constructor
  · intro z hz
    rw [mem_left_microHaloGap] at hz
    obtain ⟨w, hw, hzw⟩ := hz
    have habs : MicroInner |w| := fun n ↦ by
      rw [ArchimedeanClass.mk_abs]
      exact hw n
    have hsum : MicroInner (|w| + e) := fun n ↦
      lt_of_lt_of_le (lt_min (habs n) (he n)) (ArchimedeanClass.min_le_mk_add ..)
    refine ⟨|w| + e, ?_, ?_⟩
    · rw [mem_left_microHaloGap]
      exact ⟨|w| + e, hsum, le_rfl⟩
    · exact (hzw.trans (le_abs_self w)).trans_lt (by linarith)
  · intro z hz
    rw [mem_right_microHaloGap] at hz
    refine ⟨z - e, ?_, by linarith⟩
    rw [mem_right_microHaloGap]
    intro w hw
    have hsum : MicroInner (w + e) := fun n ↦
      lt_of_lt_of_le (lt_min (hw n) (he n)) (ArchimedeanClass.min_le_mk_add ..)
    have := hz _ hsum
    linarith

/-! ### Domination estimates for partial sums

For a strictly dominating series, all later partial sums stay within `|tₙ| + |tₙ|` of
`sₙ`: the tail beyond stage `n` is dominated by its first term. -/

variable {t : ℕ → Surreal}

private theorem lt_mk_add' {c : ArchimedeanClass Surreal} {a b : Surreal}
    (ha : c < ArchimedeanClass.mk a) (hb : c < ArchimedeanClass.mk b) :
    c < ArchimedeanClass.mk (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (ArchimedeanClass.min_le_mk_add ..)

private theorem lt_mk_sum' {c : ArchimedeanClass Surreal} (hc : c < ⊤) {s : Finset ℕ}
    {u : ℕ → Surreal} (h : ∀ i ∈ s, c < ArchimedeanClass.mk (u i)) :
    c < ArchimedeanClass.mk (∑ i ∈ s, u i) := by
  induction s using Finset.cons_induction with
  | empty =>
    have h0 : ArchimedeanClass.mk (0 : Surreal) = ⊤ := ArchimedeanClass.mk_eq_top_iff.2 rfl
    rw [Finset.sum_empty, h0]
    exact hc
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact lt_mk_add' (h a (Finset.mem_cons_self ..))
      (ih fun i hi ↦ h i (Finset.mem_cons_of_mem hi))

private theorem abs_partialSum_sub_lt
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {n k : ℕ} (hk : n ≤ k) :
    |partialSum t k - partialSum t n| < |t n| + |t n| := by
  have hpos : (0 : Surreal) < |t n| := abs_pos.2 (ne_zero_of_strict_dominating ht n)
  rcases eq_or_lt_of_le hk with rfl | hk'
  · rw [sub_self, abs_zero]
    linarith
  · have hmono : StrictMono fun m ↦ ArchimedeanClass.mk (t m) := strictMono_nat_of_lt_succ ht
    have hsub : partialSum t k - partialSum t n = ∑ i ∈ Ico n k, t i := by
      rw [partialSum, partialSum, Finset.sum_Ico_eq_sub _ hk]
    have hpeel : ∑ i ∈ Ico n k, t i = t n + ∑ i ∈ Ico (n + 1) k, t i :=
      Finset.sum_eq_sum_Ico_succ_bot hk' _
    have hD : ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (∑ i ∈ Ico (n + 1) k, t i) :=
      lt_mk_sum' ((ht n).trans_le le_top)
        fun i hi ↦ hmono (Nat.lt_of_succ_le (Finset.mem_Ico.1 hi).1)
    have habs : |∑ i ∈ Ico (n + 1) k, t i| < |t n| := abs_lt_abs_of_mk_lt hD
    calc |partialSum t k - partialSum t n| = |t n + ∑ i ∈ Ico (n + 1) k, t i| := by
          rw [hsub, hpeel]
      _ ≤ |t n| + |∑ i ∈ Ico (n + 1) k, t i| := abs_add_le _ _
      _ < |t n| + |t n| := by linarith

private theorem sub_lt_partialSum
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {n k : ℕ} (hk : n ≤ k) :
    partialSum t n - (|t n| + |t n|) < partialSum t k := by
  have h := (abs_lt.1 (abs_partialSum_sub_lt ht hk)).1
  linarith

private theorem partialSum_lt_add
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {n k : ℕ} (hk : n ≤ k) :
    partialSum t k < partialSum t n + (|t n| + |t n|) := by
  have h := (abs_lt.1 (abs_partialSum_sub_lt ht hk)).2
  linarith

/-! ### Membership formulas for the band edges -/

theorem mem_left_sumLo :
    z ∈ (sumLo t).left ↔ ∃ n, ∀ k : ℕ, z ≤ partialSum t n - (k + 1) • |t n| := by
  unfold sumLo bandLo
  simp only [Cut.left_iSup, Cut.left_iInf, Cut.left_rightSurreal, Set.mem_iUnion,
    Set.mem_iInter, Set.mem_Iic]

theorem mem_left_sumHi :
    z ∈ (sumHi t).left ↔ ∀ n, ∃ k : ℕ, z < partialSum t n + (k + 1) • |t n| := by
  unfold sumHi bandHi
  simp only [Cut.left_iInf, Cut.left_iSup, Cut.left_leftSurreal, Set.mem_iInter,
    Set.mem_iUnion, Set.mem_Iio]

theorem mem_right_sumLo :
    z ∈ (sumLo t).right ↔ ∀ n, ∃ k : ℕ, partialSum t n - (k + 1) • |t n| < z := by
  rw [← Cut.notMem_left_iff]
  simp only [mem_left_sumLo]
  push Not
  rfl

theorem mem_right_sumHi :
    z ∈ (sumHi t).right ↔ ∃ n, ∀ k : ℕ, partialSum t n + (k + 1) • |t n| ≤ z := by
  rw [← Cut.notMem_left_iff]
  simp only [mem_left_sumHi]
  push Not
  rfl

/-- **The trichotomy**: every surreal is a Hahn sum of `t`, or lies below the band
(`sumLo.left`), or above it (`sumHi.right`). -/
theorem isHahnSum_or_mem_left_or_mem_right (ht0 : ∀ n, t n ≠ 0) (z : Surreal) :
    IsHahnSum t z ∨ z ∈ (sumLo t).left ∨ z ∈ (sumHi t).right := by
  by_cases h : Cut.Fits z (sumLo t) (sumHi t)
  · exact .inl ((fits_iff_isHahnSum ht0).1 h)
  · rw [Cut.not_fits_iff] at h
    exact .inr h

/-! ### The residual sign law

For any Hahn sum `x` of a strictly dominating series, the `n`-th residual `x − sₙ` has
*exactly* the Archimedean class of `tₙ` — and, crucially, its **sign**: peeling one term,
`x − sₙ = tₙ + (x − sₙ₊₁)`, and the second summand is strictly dominated. So a Hahn sum
sits above every partial sum that is about to grow, and below every one about to shrink. -/

theorem IsHahnSum.mk_sub_partialSum
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {x : Surreal} (hx : IsHahnSum t x) (n : ℕ) :
    ArchimedeanClass.mk (x - partialSum t n) = ArchimedeanClass.mk (t n) := by
  have h1 : x - partialSum t n = t n + (x - partialSum t (n + 1)) := by
    rw [partialSum_succ]
    ring
  rw [h1, ArchimedeanClass.mk_add_eq_mk_left ((ht n).trans_le (hx (n + 1)))]

/-- If the `n`-th term is positive, every Hahn sum lies strictly above the `n`-th partial
sum. -/
theorem IsHahnSum.partialSum_lt
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {x : Surreal} (hx : IsHahnSum t x) {n : ℕ} (hn : 0 < t n) :
    partialSum t n < x := by
  have h1 : x - partialSum t n = t n + (x - partialSum t (n + 1)) := by
    rw [partialSum_succ]
    ring
  have h2 : ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (x - partialSum t (n + 1)) :=
    (ht n).trans_le (hx (n + 1))
  have h3 := (abs_lt.1 (abs_lt_abs_of_mk_lt h2)).1
  rw [abs_of_pos hn] at h3
  have h4 : 0 < x - partialSum t n := by
    rw [h1]
    linarith
  linarith

/-- If the `n`-th term is negative, every Hahn sum lies strictly below the `n`-th partial
sum. -/
theorem IsHahnSum.lt_partialSum
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {x : Surreal} (hx : IsHahnSum t x) {n : ℕ} (hn : t n < 0) :
    x < partialSum t n := by
  have h1 : x - partialSum t n = t n + (x - partialSum t (n + 1)) := by
    rw [partialSum_succ]
    ring
  have h2 : ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (x - partialSum t (n + 1)) :=
    (ht n).trans_le (hx (n + 1))
  have h3 := (abs_lt.1 (abs_lt_abs_of_mk_lt h2)).2
  rw [abs_of_neg hn] at h3
  have h4 : x - partialSum t n < 0 := by
    rw [h1]
    linarith
  linarith

/-! ### The Bridge Theorem, part 1: the outer bounds

The limit interval always sits inside the band interval. -/

/-- The lower band edge is at most the lower limit of the partial sums. -/
theorem sumLo_le_liminfCut
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    sumLo t ≤ liminfCut (partialSum t) atTop := by
  rw [← Cut.left_subset_left_iff]
  intro z hz
  rw [mem_left_sumLo] at hz
  obtain ⟨n, hn⟩ := hz
  rw [mem_left_liminfCut_atTop]
  refine ⟨n, fun k hk ↦ ?_⟩
  have h1 := sub_lt_partialSum ht hk
  have h2 := hn 1
  rw [succ_nsmul, one_nsmul] at h2
  linarith

/-- The upper limit of the partial sums is at most the upper band edge. -/
theorem limsupCut_le_sumHi
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    limsupCut (partialSum t) atTop ≤ sumHi t := by
  rw [← Cut.right_subset_right_iff]
  intro z hz
  rw [mem_right_sumHi] at hz
  obtain ⟨n, hn⟩ := hz
  rw [mem_right_limsupCut_atTop]
  refine ⟨n, fun k hk ↦ ?_⟩
  have h1 := partialSum_lt_add ht hk
  have h2 := hn 1
  rw [succ_nsmul, one_nsmul] at h2
  linarith

/-! ### The Bridge Theorem, part 2: the sign dichotomy

Where inside the band the limits land is governed by the *cofinal signs* of the terms.
This is the true form of the bridge: the naive `liminf = sumLo ∧ limsup = sumHi` holds
exactly when both signs occur cofinally, and a one-signed tail collapses both limits onto
a single edge. -/

/-- **The Bridge, lower half**: if positive terms occur cofinally, the lower limit of the
partial sums is exactly the lower edge of the Hahn band. (Partial sums dip to the bottom
of the band just before each positive term.) -/
theorem liminfCut_partialSum_eq_sumLo
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hpos : ∃ᶠ n in atTop, 0 < t n) :
    liminfCut (partialSum t) atTop = sumLo t := by
  refine le_antisymm ?_ (sumLo_le_liminfCut ht)
  rw [← Cut.left_subset_left_iff]
  intro z hz
  rw [mem_left_liminfCut_atTop] at hz
  obtain ⟨n₀, hn₀⟩ := hz
  rcases isHahnSum_or_mem_left_or_mem_right (ne_zero_of_strict_dominating ht) z with
    hH | hLo | hHi
  · obtain ⟨m, hm, hm0⟩ := frequently_atTop.1 hpos n₀
    exact absurd (hn₀ m hm) (lt_asymm (hH.partialSum_lt ht hm0))
  · exact hLo
  · rw [mem_right_sumHi] at hHi
    obtain ⟨n₁, hn₁⟩ := hHi
    have h1 := hn₀ (max n₀ n₁) (le_max_left _ _)
    have h2 := partialSum_lt_add ht (le_max_right n₀ n₁)
    have h3 := hn₁ 1
    rw [succ_nsmul, one_nsmul] at h3
    linarith

/-- **The Bridge, upper half**: if negative terms occur cofinally, the upper limit of the
partial sums is exactly the upper edge of the Hahn band. -/
theorem limsupCut_partialSum_eq_sumHi
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hneg : ∃ᶠ n in atTop, t n < 0) :
    limsupCut (partialSum t) atTop = sumHi t := by
  refine le_antisymm (limsupCut_le_sumHi ht) ?_
  rw [← Cut.left_subset_left_iff]
  intro z hz
  rw [mem_left_limsupCut_atTop]
  rcases isHahnSum_or_mem_left_or_mem_right (ne_zero_of_strict_dominating ht) z with
    hH | hLo | hHi
  · intro n
    obtain ⟨m, hm, hm0⟩ := frequently_atTop.1 hneg n
    exact ⟨m, hm, (hH.lt_partialSum ht hm0).le⟩
  · rw [mem_left_sumLo] at hLo
    obtain ⟨n₁, hn₁⟩ := hLo
    intro n
    refine ⟨max n n₁, le_max_left _ _, ?_⟩
    have h1 := sub_lt_partialSum ht (le_max_right n n₁)
    have h2 := hn₁ 1
    rw [succ_nsmul, one_nsmul] at h2
    linarith
  · exact absurd hz (Cut.notMem_left_iff.2 hHi)

/-- **The collapse, negative tail**: if the terms are eventually negative, both limits
collapse onto the *upper* band edge — the partial sums decrease onto the band from above
and never dip below it. -/
theorem liminfCut_partialSum_eq_sumHi
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hneg : ∀ᶠ n in atTop, t n < 0) :
    liminfCut (partialSum t) atTop = sumHi t := by
  refine le_antisymm (liminfCut_le_limsupCut.trans (limsupCut_le_sumHi ht)) ?_
  rw [← Cut.left_subset_left_iff]
  intro z hz
  rcases isHahnSum_or_mem_left_or_mem_right (ne_zero_of_strict_dominating ht) z with
    hH | hLo | hHi
  · rw [mem_left_liminfCut_atTop]
    obtain ⟨N, hN⟩ := eventually_atTop.1 hneg
    exact ⟨N, fun k hk ↦ hH.lt_partialSum ht (hN k hk)⟩
  · exact Cut.left_subset_left_iff.2 (sumLo_le_liminfCut ht) hLo
  · exact absurd hz (Cut.notMem_left_iff.2 hHi)

/-- **The collapse, positive tail**: if the terms are eventually positive, both limits
collapse onto the *lower* band edge — the partial sums increase onto the band from below
and never cross it. -/
theorem limsupCut_partialSum_eq_sumLo
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hpos : ∀ᶠ n in atTop, 0 < t n) :
    limsupCut (partialSum t) atTop = sumLo t := by
  refine le_antisymm ?_ ((sumLo_le_liminfCut ht).trans liminfCut_le_limsupCut)
  rw [← Cut.left_subset_left_iff]
  intro z hz
  rw [mem_left_limsupCut_atTop] at hz
  rcases isHahnSum_or_mem_left_or_mem_right (ne_zero_of_strict_dominating ht) z with
    hH | hLo | hHi
  · obtain ⟨N, hN⟩ := eventually_atTop.1 hpos
    obtain ⟨k, hk, hzk⟩ := hz N
    exact absurd hzk (not_le.2 (hH.partialSum_lt ht (hN k hk)))
  · exact hLo
  · rw [mem_right_sumHi] at hHi
    obtain ⟨n₁, hn₁⟩ := hHi
    obtain ⟨k, hk, hzk⟩ := hz n₁
    have h1 := partialSum_lt_add ht hk
    have h2 := hn₁ 1
    rw [succ_nsmul, one_nsmul] at h2
    linarith

/-- The signs of a strictly dominating series: positive terms occur cofinally, or the
terms are eventually negative (and dually). -/
theorem frequently_pos_or_eventually_neg (ht0 : ∀ n, t n ≠ 0) :
    (∃ᶠ n in atTop, 0 < t n) ∨ ∀ᶠ n in atTop, t n < 0 := by
  rcases Classical.em (∃ᶠ n in atTop, 0 < t n) with h | h
  · exact .inl h
  · rw [not_frequently] at h
    exact .inr (h.mono fun n hn ↦ lt_of_le_of_ne (not_lt.1 hn) (ht0 n))

/-- **THE BRIDGE THEOREM.** For a strictly dominating series whose terms take both signs
cofinally, the cut-valued limit machinery and the Hahn-sum machinery compute the same
objects: the lower and upper limits of the partial sums are exactly the two edges of the
band of Hahn sums. -/
theorem liminfCut_limsupCut_partialSum
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hpos : ∃ᶠ n in atTop, 0 < t n) (hneg : ∃ᶠ n in atTop, t n < 0) :
    liminfCut (partialSum t) atTop = sumLo t ∧ limsupCut (partialSum t) atTop = sumHi t :=
  ⟨liminfCut_partialSum_eq_sumLo ht hpos, limsupCut_partialSum_eq_sumHi ht hneg⟩

/-! ### The reconciliation: summation IS approximation

With the bridge in hand, the two semantics of this development coincide: a surreal is a
transfinite sum of the series if and only if it is squeezed between the lower and upper
limits of the partial sums. The partial sums fail to converge *to a surreal* not because
approximation fails, but because what they approximate is the canonical interval — an
interval whose edges are gaps. -/

/-- **Summation is approximation**: for a series with both signs cofinal, the Hahn sums
are exactly the surreals fitting between the lower and upper limits of the partial sums. -/
theorem isHahnSum_iff_fits_liminfCut_limsupCut
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hpos : ∃ᶠ n in atTop, 0 < t n) (hneg : ∃ᶠ n in atTop, t n < 0) {z : Surreal} :
    IsHahnSum t z ↔
      Cut.Fits z (liminfCut (partialSum t) atTop) (limsupCut (partialSum t) atTop) := by
  rw [liminfCut_partialSum_eq_sumLo ht hpos, limsupCut_partialSum_eq_sumHi ht hneg,
    fits_iff_isHahnSum (ne_zero_of_strict_dominating ht)]

theorem liminfCut_lt_limsupCut_partialSum
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hpos : ∃ᶠ n in atTop, 0 < t n) (hneg : ∃ᶠ n in atTop, t n < 0) :
    liminfCut (partialSum t) atTop < limsupCut (partialSum t) atTop := by
  rw [liminfCut_partialSum_eq_sumLo ht hpos, limsupCut_partialSum_eq_sumHi ht hneg]
  exact sumLo_lt_sumHi ht

private theorem simplestBtwn_congr {x x' y y' : Cut} (h : x < y) (h' : x' < y')
    (hx : x = x') (hy : y = y') : Cut.simplestBtwn h = Cut.simplestBtwn h' := by
  subst hx
  subst hy
  rfl

/-- **The canonical sum is the simplest surreal between the limits of its partial sums**:
the birthday-minimal Hahn sum of `Infinity.CanonicalSum` is `simplestBtwn` applied to the
liminf and limsup cuts of the partial-sum sequence. -/
theorem hahnSum_eq_simplestBtwn_liminfCut_limsupCut
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hpos : ∃ᶠ n in atTop, 0 < t n) (hneg : ∃ᶠ n in atTop, t n < 0)
    (h : liminfCut (partialSum t) atTop < limsupCut (partialSum t) atTop) :
    hahnSum ht = Cut.simplestBtwn h :=
  simplestBtwn_congr (sumLo_lt_sumHi ht) h
    (liminfCut_partialSum_eq_sumLo ht hpos).symm
    (limsupCut_partialSum_eq_sumHi ht hneg).symm

/-! ### The band edges are gaps

For any strictly dominating series, `sumLo` and `sumHi` are genuine gaps: the interval of
Hahn sums has no smallest or largest element (perturbing by a positive surreal below all
the scales of the series stays inside), and the outside classes are open as well. -/

/-- Below all scales: there is a positive surreal whose Archimedean class exceeds that of
every term. -/
theorem exists_pos_forall_mk_lt (ht0 : ∀ n, t n ≠ 0) :
    ∃ e : Surreal, 0 < e ∧ ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk e := by
  obtain ⟨e, he0, he⟩ := exists_pos_forall_lt_of_small
    (z := fun m : ℕ ↦ |t m.unpair.1| / ((m.unpair.2 : Surreal) + 1))
    (fun m ↦ div_pos (abs_pos.2 (ht0 _)) (by positivity))
  refine ⟨e, he0, fun n ↦ ?_⟩
  rw [ArchimedeanClass.mk_lt_mk]
  intro j
  have hej : e < |t n| / ((j : Surreal) + 1) := by
    have h := he (Nat.pair n j)
    rwa [Nat.unpair_pair] at h
  have hj1 : (0 : Surreal) < (j : Surreal) + 1 := by positivity
  have h3 : ((j : Surreal) + 1) * e < |t n| := by
    rw [mul_comm]
    exact (lt_div_iff₀ hj1).1 hej
  have h4 : (j : Surreal) * e ≤ ((j : Surreal) + 1) * e :=
    mul_le_mul_of_nonneg_right (by linarith) he0.le
  rw [nsmul_eq_mul, abs_of_pos he0]
  exact h4.trans_lt h3

/-- **The lower band edge is a gap.** -/
theorem isGap_sumLo
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    (sumLo t).IsGap := by
  obtain ⟨e, he0, he⟩ := exists_pos_forall_mk_lt (ne_zero_of_strict_dominating ht)
  have hee : ∀ n, e ≤ |t n| := fun n ↦ by
    have h := abs_lt_abs_of_mk_lt (he n)
    rw [abs_of_pos he0] at h
    exact h.le
  rw [Cut.isGap_iff]
  constructor
  · intro z hz
    rw [mem_left_sumLo] at hz
    obtain ⟨n, hn⟩ := hz
    refine ⟨z + e, ?_, by linarith⟩
    rw [mem_left_sumLo]
    refine ⟨n, fun k ↦ ?_⟩
    have h1 := hn (k + 1)
    rw [succ_nsmul] at h1
    have h2 := hee n
    linarith
  · intro z hz
    refine ⟨z - e, ?_, by linarith⟩
    rw [← Cut.notMem_left_iff] at hz ⊢
    rw [mem_left_sumLo] at hz ⊢
    rintro ⟨n, hn⟩
    refine hz ⟨n, fun k ↦ ?_⟩
    have h1 := hn (k + 1)
    rw [succ_nsmul] at h1
    have h2 := hee n
    linarith

/-- **The upper band edge is a gap.** -/
theorem isGap_sumHi
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    (sumHi t).IsGap := by
  obtain ⟨e, he0, he⟩ := exists_pos_forall_mk_lt (ne_zero_of_strict_dominating ht)
  have hee : ∀ n, e ≤ |t n| := fun n ↦ by
    have h := abs_lt_abs_of_mk_lt (he n)
    rw [abs_of_pos he0] at h
    exact h.le
  rw [Cut.isGap_iff]
  constructor
  · intro z hz
    rw [mem_left_sumHi] at hz
    refine ⟨z + e, ?_, by linarith⟩
    rw [mem_left_sumHi]
    intro n
    obtain ⟨k, hk⟩ := hz n
    refine ⟨k + 1, ?_⟩
    rw [succ_nsmul]
    have h2 := hee n
    linarith
  · intro z hz
    rw [mem_right_sumHi] at hz
    obtain ⟨n, hn⟩ := hz
    refine ⟨z - e, ?_, by linarith⟩
    rw [mem_right_sumHi]
    refine ⟨n, fun k ↦ ?_⟩
    have h1 := hn (k + 1)
    rw [succ_nsmul] at h1
    have h2 := hee n
    linarith

/-! ### One-signed series sharply converge to a gap

Combining the collapse theorems with the gap theorems: the partial sums of an eventually
one-signed strictly dominating series order-converge *sharply* — to a location that is
provably not a surreal. This is the ℕ-length shadow of RSS Example 24 (`No` is not Cauchy
complete: Cauchy-like sequences can converge to gaps). -/

theorem tendstoCut_partialSum_of_eventually_pos
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hpos : ∀ᶠ n in atTop, 0 < t n) :
    TendstoCut (partialSum t) atTop (sumLo t) :=
  ⟨liminfCut_partialSum_eq_sumLo ht hpos.frequently, limsupCut_partialSum_eq_sumLo ht hpos⟩

theorem tendstoCut_partialSum_of_eventually_neg
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hneg : ∀ᶠ n in atTop, t n < 0) :
    TendstoCut (partialSum t) atTop (sumHi t) :=
  ⟨liminfCut_partialSum_eq_sumHi ht hneg, limsupCut_partialSum_eq_sumHi ht hneg.frequently⟩

/-! ### The flagship instance: the geometric series

The partial sums of `Σ_{k<ω} ω⁻ᵏ` sharply converge to the gap `sumLo`, and the canonical
sum `ω/(ω−1)` is the nearest surreal beyond that gap. Summation is approximation,
completed through a gap. -/

private theorem geometric_strict_dominating' :
    ∀ n, ArchimedeanClass.mk (eps0 ^ n) < ArchimedeanClass.mk (eps0 ^ (n + 1)) :=
  mk_pow_lt_mk_pow_succ (infinitesimal_inv_wpow one_pos) (inv_pos.2 (wpow_pos _))

private theorem geometric_eventually_pos : ∀ᶠ n in atTop, (0 : Surreal.{0}) < eps0 ^ n :=
  Eventually.of_forall fun n ↦ pow_pos (inv_pos.2 (wpow_pos _)) n

/-- **The geometric showcase**: the partial sums of `Σ ω⁻ᵏ` sharply converge to the lower
band edge; that edge is a gap; and the classical sum `(1 − ω⁻¹)⁻¹ = ω/(ω−1)` lies just
past it (in its right class). The series "converges" — to the gap hugging its sums from
below. -/
theorem geometric_gap_convergence :
    TendstoCut (partialSum fun k ↦ eps0 ^ k) atTop (sumLo fun k ↦ eps0 ^ k) ∧
      (sumLo fun k ↦ eps0 ^ k).IsGap ∧
      (1 - eps0)⁻¹ ∈ (sumLo fun k ↦ eps0 ^ k).right := by
  refine ⟨tendstoCut_partialSum_of_eventually_pos geometric_strict_dominating'
    geometric_eventually_pos, isGap_sumLo geometric_strict_dominating', ?_⟩
  exact ((fits_iff_isHahnSum
    (ne_zero_of_strict_dominating geometric_strict_dominating')).2 isHahnSum_geometric).1

end Surreal
