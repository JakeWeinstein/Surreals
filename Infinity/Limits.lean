/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.StandardPart
import CombinatorialGames.Surreal.Cut
import Mathlib.Order.LiminfLimsup

/-!
# Limits of surreal sequences, valued in cuts

Naive limits fail on the surreals: the sequence `1/n` has *no* surreal limit, because every
positive real eventually exceeds it while every positive infinitesimal stays below all of its
terms — it converges to a *gap*. Following `notes/limits-design.md`, we therefore take limits
valued in `Surreal.Cut`, the complete linear order of cuts, where `limsup`/`liminf` always
exist; convergence *to a surreal* is the well-behaved special case, and the `1/n` phenomenon
becomes a theorem (`not_tendstoSurreal_inv_natCast`) rather than a pathology.

## Contents

* Order-theoretic characterizations of the Archimedean predicates:
  `isFinite_iff` (`|x| ≤ n`) and `infinitesimal_iff` (`n • |x| < 1`), with comparison
  corollaries against rational casts.
* `limsupCut` / `liminfCut`: cut-valued limit superior/inferior of a surreal-valued family
  along a filter, via `Filter.limsup` in the complete lattice `Cut`.
* `TendstoSurreal f l x`: order convergence to a surreal, and its sandwich characterization
  `leftSurreal x ≤ liminfCut f l ∧ limsupCut f l ≤ rightSurreal x`.
* `not_tendstoSurreal_inv_natCast`: **the gap theorem** — `1/n` converges to no surreal.
-/

open ArchimedeanClass Filter

noncomputable section

namespace Surreal

/-! ### Order-theoretic characterizations of `IsFinite` and `Infinitesimal` -/

/-- A surreal is finite iff it is bounded in absolute value by a natural number. -/
theorem isFinite_iff {x : Surreal} : IsFinite x ↔ ∃ n : ℕ, |x| ≤ n := by
  rw [IsFinite, ← ArchimedeanClass.mk_one, ArchimedeanClass.mk_le_mk]
  simp [nsmul_eq_mul]

/-- A surreal is infinitesimal iff all its natural multiples stay below `1`. -/
theorem infinitesimal_iff {x : Surreal} : Infinitesimal x ↔ ∀ n : ℕ, n • |x| < 1 := by
  rw [Infinitesimal, ← ArchimedeanClass.mk_one, ArchimedeanClass.mk_lt_mk]
  simp

/-- An infinitesimal is smaller in absolute value than every positive rational. -/
theorem Infinitesimal.abs_lt_ratCast {x : Surreal} (h : Infinitesimal x) {q : ℚ}
    (hq : 0 < q) : |x| < q := by
  obtain ⟨n, hn⟩ := exists_nat_gt q⁻¹
  have hn0 : (0 : ℚ) < n := (inv_pos.2 hq).trans hn
  have h1 := infinitesimal_iff.1 h n
  rw [nsmul_eq_mul] at h1
  have hnS : (0 : Surreal) < n := by exact_mod_cast hn0
  have hQ : (1 : ℚ) < q * n := by
    have h2 := mul_lt_mul_of_pos_left hn hq
    rwa [mul_inv_cancel₀ hq.ne'] at h2
  have hQ2 : (1 : ℚ) / n < q := (div_lt_iff₀ hn0).2 hQ
  calc |x| < 1 / n := (lt_div_iff₀ hnS).2 (by rwa [mul_comm])
    _ < q := by
      have h3 : ((1 / (n : ℚ) : ℚ) : Surreal) < ((q : ℚ) : Surreal) := Rat.cast_lt.2 hQ2
      push_cast at h3
      exact h3

theorem Infinitesimal.lt_ratCast {x : Surreal} (h : Infinitesimal x) {q : ℚ} (hq : 0 < q) :
    x < q :=
  (le_abs_self x).trans_lt (h.abs_lt_ratCast hq)

/-- A positive surreal below every positive rational is infinitesimal. -/
theorem infinitesimal_of_pos_of_forall_le_ratCast {x : Surreal} (hx : 0 < x)
    (h : ∀ q : ℚ, 0 < q → x ≤ q) : Infinitesimal x := by
  rw [infinitesimal_iff]
  intro n
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  · have hq : (0 : ℚ) < 1 / (2 * n) := by positivity
    have hle := h _ hq
    rw [abs_of_pos hx, nsmul_eq_mul]
    calc (n : Surreal) * x ≤ n * ((1 : ℚ) / (2 * n) : ℚ) := by
          exact mul_le_mul_of_nonneg_left hle (by exact_mod_cast n.zero_le)
      _ = (((n : ℚ) * (1 / (2 * n)) : ℚ) : Surreal) := by push_cast; ring
      _ = ((1 / 2 : ℚ) : Surreal) := by
          norm_num
          field_simp
      _ < 1 := by exact_mod_cast one_half_lt_one

/-! ### Cut-valued limit superior and inferior

`Cut` is a complete lattice and a linear order, so `Filter.limsup`/`Filter.liminf` always
exist there. A surreal value `z` is sent *up* via `Cut.rightSurreal z` for the limsup and
*down* via `Cut.leftSurreal z` for the liminf, so that a constant sequence has
`liminfCut = leftSurreal x` and `limsupCut = rightSurreal x` — the two cuts hugging `x`. -/

variable {ι : Type*} {f : ι → Surreal} {l : Filter ι} {x : Surreal}

/-- The cut-valued limit superior of a surreal-valued family: always exists. -/
def limsupCut (f : ι → Surreal) (l : Filter ι) : Cut :=
  limsup (fun i ↦ Cut.rightSurreal (f i)) l

/-- The cut-valued limit inferior of a surreal-valued family: always exists. -/
def liminfCut (f : ι → Surreal) (l : Filter ι) : Cut :=
  liminf (fun i ↦ Cut.leftSurreal (f i)) l

@[simp]
theorem limsupCut_const (l : Filter ι) [l.NeBot] (x : Surreal) :
    limsupCut (fun _ ↦ x) l = Cut.rightSurreal x :=
  limsup_const _

@[simp]
theorem liminfCut_const (l : Filter ι) [l.NeBot] (x : Surreal) :
    liminfCut (fun _ ↦ x) l = Cut.leftSurreal x :=
  liminf_const _

theorem liminfCut_le_limsupCut [l.NeBot] : liminfCut f l ≤ limsupCut f l :=
  le_trans (liminf_le_liminf (Eventually.of_forall fun i ↦
    Cut.leftSurreal_le_rightSurreal (f i))) liminf_le_limsup

/-! #### Extraction lemmas

These avoid needing a `ConditionallyCompleteLinearOrder` instance on `Cut`: they use only
the complete lattice structure plus linearity of the order, via `sSup`/`sInf` membership. -/

private theorem limsup_le_of_eventually_le {u : ι → Cut} {a : Cut}
    (h : ∀ᶠ i in l, u i ≤ a) : limsup u l ≤ a := by
  rw [limsup_eq]
  exact sInf_le h

private theorem le_liminf_of_eventually_le {u : ι → Cut} {a : Cut}
    (h : ∀ᶠ i in l, a ≤ u i) : a ≤ liminf u l := by
  rw [liminf_eq]
  exact le_sSup h

private theorem eventually_lt_of_lt_liminf {u : ι → Cut} {a : Cut}
    (h : a < liminf u l) : ∀ᶠ i in l, a < u i := by
  rw [liminf_eq] at h
  have h' : ¬ ∀ b ∈ {b : Cut | ∀ᶠ i in l, b ≤ u i}, b ≤ a := fun hb ↦ (sSup_le hb).not_gt h
  push Not at h'
  obtain ⟨b, hb, hab⟩ := h'
  exact hb.mono fun i hi ↦ hab.trans_le hi

private theorem eventually_lt_of_limsup_lt {u : ι → Cut} {a : Cut}
    (h : limsup u l < a) : ∀ᶠ i in l, u i < a := by
  rw [limsup_eq] at h
  have h' : ¬ ∀ b ∈ {b : Cut | ∀ᶠ i in l, u i ≤ b}, a ≤ b := fun hb ↦ (le_sInf hb).not_gt h
  push Not at h'
  obtain ⟨b, hb, hab⟩ := h'
  exact hb.mono fun i hi ↦ hi.trans_lt hab

/-! #### Collapsing the two-sided approximations -/

/-- The infimum of the cuts just left of all surreals above `x` is the cut just right of `x`. -/
theorem iInf_leftSurreal_Ioi (x : Surreal) :
    (⨅ y : Set.Ioi x, Cut.leftSurreal y.1) = Cut.rightSurreal x := by
  rw [← Cut.left_inj, Cut.left_iInf]
  ext z
  simp only [Set.mem_iInter, Cut.left_leftSurreal, Set.mem_Iio, Cut.left_rightSurreal,
    Set.mem_Iic]
  constructor
  · intro hz
    by_contra hzx
    rw [not_le] at hzx
    exact absurd (hz ⟨(x + z) / 2, left_lt_add_div_two.2 hzx⟩)
      (not_lt.2 (add_div_two_lt_right.2 hzx).le)
  · exact fun hz y ↦ hz.trans_lt y.2

/-- The supremum of the cuts just right of all surreals below `x` is the cut just left of `x`. -/
theorem iSup_rightSurreal_Iio (x : Surreal) :
    (⨆ y : Set.Iio x, Cut.rightSurreal y.1) = Cut.leftSurreal x := by
  rw [← Cut.right_inj, Cut.right_iSup]
  ext z
  simp only [Set.mem_iInter, Cut.right_rightSurreal, Set.mem_Ioi, Cut.right_leftSurreal,
    Set.mem_Ici]
  constructor
  · intro hz
    by_contra hzx
    rw [not_le] at hzx
    exact absurd (hz ⟨(z + x) / 2, add_div_two_lt_right.2 hzx⟩)
      (not_lt.2 (left_lt_add_div_two.2 hzx).le)
  · exact fun hz y ↦ y.2.trans_le hz

/-! ### Convergence to a surreal -/

/-- Order convergence of a surreal-valued family to a surreal limit: the family is eventually
above everything below `x` and eventually below everything above `x`. -/
def TendstoSurreal (f : ι → Surreal) (l : Filter ι) (x : Surreal) : Prop :=
  (∀ y < x, ∀ᶠ i in l, y < f i) ∧ ∀ y, x < y → ∀ᶠ i in l, f i < y

theorem tendstoSurreal_const (l : Filter ι) (x : Surreal) : TendstoSurreal (fun _ ↦ x) l x :=
  ⟨fun _ hy ↦ Eventually.of_forall fun _ ↦ hy, fun _ hy ↦ Eventually.of_forall fun _ ↦ hy⟩

/-- **The sandwich characterization**: a surreal family converges to `x` iff its cut-valued
liminf and limsup pinch the pair of cuts hugging `x`. -/
theorem tendstoSurreal_iff_cuts :
    TendstoSurreal f l x ↔
      Cut.leftSurreal x ≤ liminfCut f l ∧ limsupCut f l ≤ Cut.rightSurreal x := by
  constructor
  · rintro ⟨hlow, hupp⟩
    refine ⟨?_, ?_⟩
    · rw [← iSup_rightSurreal_Iio]
      refine iSup_le fun y ↦ le_liminf_of_eventually_le ?_
      exact (hlow y.1 y.2).mono fun i hi ↦ Cut.rightSurreal_le_iff.2 hi
    · rw [← iInf_leftSurreal_Ioi]
      refine le_iInf fun y ↦ limsup_le_of_eventually_le ?_
      exact (hupp y.1 y.2).mono fun i hi ↦ Cut.rightSurreal_le_iff.2 hi
  · rintro ⟨hlin, hlsup⟩
    constructor
    · intro y hy
      have h1 : Cut.leftSurreal y < liminfCut f l :=
        (Cut.leftSurreal_lt_rightSurreal y).trans_le
          ((Cut.rightSurreal_le_iff.2 (Cut.mem_left_leftSurreal.2 hy)).trans hlin)
      exact (eventually_lt_of_lt_liminf h1).mono fun i hi ↦
        Cut.mem_left_leftSurreal.1 (Cut.leftSurreal_lt_iff.1 hi)
    · intro y hy
      have h1 : limsupCut f l < Cut.rightSurreal y :=
        (hlsup.trans (Cut.rightSurreal_le_iff.2 (Cut.mem_left_leftSurreal.2 hy))).trans_lt
          (Cut.leftSurreal_lt_rightSurreal y)
      exact (eventually_lt_of_limsup_lt h1).mono fun i hi ↦
        Cut.mem_right_rightSurreal.1 (Cut.lt_rightSurreal_iff.1 hi)

/-! ### The gap theorem: `1/n` has no surreal limit -/

/-- **The gap theorem.** The sequence `1/n` converges to *no* surreal number: every positive
real is eventually above it, but every positive infinitesimal is below all of its (positive)
terms, and there is no surreal in between — the sequence converges to a gap of `No`.

This is the fundamental obstruction to naive analysis on the surreals, stated as a theorem. -/
theorem not_tendstoSurreal_inv_natCast (x : Surreal) :
    ¬ TendstoSurreal (fun n : ℕ ↦ (n : Surreal)⁻¹) atTop x := by
  rintro ⟨hlow, hupp⟩
  -- Step 1: every positive infinitesimal is at most `x`.
  have hstep1 : ∀ e : Surreal, Infinitesimal e → 0 < e → e ≤ x := by
    intro e he he0
    by_contra hxe
    rw [not_le] at hxe
    have hcontra : ∀ᶠ n : ℕ in atTop, ¬ ((n : Surreal)⁻¹ < e) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [not_lt]
      have hnq : (0 : ℚ) < 1 / n := by
        have : (0 : ℚ) < n := by exact_mod_cast hn
        positivity
      have h1 := he.lt_ratCast hnq
      have h2 : ((1 / (n : ℚ) : ℚ) : Surreal) = (n : Surreal)⁻¹ := by push_cast; ring
      rw [h2] at h1
      exact h1.le
    obtain ⟨n, h1, h2⟩ := ((hupp e hxe).and hcontra).exists
    exact h2 h1
  -- Hence `x` is positive (it dominates `1/ω`).
  have hx0 : 0 < x :=
    lt_of_lt_of_le (inv_pos.2 (wpow_pos (1 : Surreal)))
      (hstep1 _ (infinitesimal_inv_wpow one_pos) (inv_pos.2 (wpow_pos _)))
  -- Step 2: `x` is at most every positive rational.
  have hstep2 : ∀ q : ℚ, 0 < q → x ≤ q := by
    intro q hq
    by_contra hqx
    rw [not_le] at hqx
    have hcontra : ∀ᶠ n : ℕ in atTop, ¬ ((q : Surreal) < (n : Surreal)⁻¹) := by
      obtain ⟨m, hm⟩ := exists_nat_gt q⁻¹
      filter_upwards [eventually_ge_atTop (m + 1)] with n hn
      rw [not_lt]
      have hmn : q⁻¹ < (n : ℚ) := hm.trans (Nat.cast_lt.2 (Nat.lt_of_succ_le hn))
      have hinv : (n : ℚ)⁻¹ < q := inv_lt_of_inv_lt₀ hq hmn
      have h2 : (((n : ℚ)⁻¹ : ℚ) : Surreal) = (n : Surreal)⁻¹ := by push_cast; ring
      calc (n : Surreal)⁻¹ = (((n : ℚ)⁻¹ : ℚ) : Surreal) := h2.symm
        _ ≤ (q : Surreal) := by exact_mod_cast hinv.le
    obtain ⟨n, h1, h2⟩ := ((hlow _ hqx).and hcontra).exists
    exact h2 h1
  -- Step 3: therefore `x` is a positive infinitesimal — but then so is `2 * x`,
  -- which by Step 1 satisfies `2 * x ≤ x`: contradiction with `0 < x`.
  have hinf := infinitesimal_of_pos_of_forall_le_ratCast hx0 hstep2
  have h2fin : IsFinite (2 : Surreal) := by
    rw [show (2 : Surreal) = ((2 : ℚ) : Surreal) by norm_cast]
    exact isFinite_ratCast 2
  have h2x := hstep1 _ (h2fin.mul_infinitesimal hinf) (by positivity)
  linarith

/-! ### The definitive obstruction: ω-sequences only converge by being eventually constant

The gap theorem above is an instance of something far stronger. Because `No` is a proper-class
field, *any countable family of positive surreals has a positive surreal strictly below all of
them* — the Conway cut `{0 | z₀, z₁, …}` — so no point of `No` has a countable neighborhood
base. Consequently an ℕ-indexed sequence converges **only if it is eventually constant**. This
is why analysis on the surreals requires transfinite (ordinal-length) sequences, as in
Rubinstein-Salzedo–Swaminathan, or cut-valued limits as developed here. -/

/-- **Countable coinitiality**: any countable family of positive surreals has a common
positive strict lower bound, namely the cut `{0 | z₀, z₁, …}`. -/
theorem exists_pos_forall_lt {z : ℕ → Surreal} (hz : ∀ n, 0 < z n) :
    ∃ e : Surreal, 0 < e ∧ ∀ n, e < z n := by
  have H : ∀ a ∈ ({0} : Set Surreal), ∀ b ∈ Set.range z, a < b := by
    rintro a rfl b ⟨n, rfl⟩
    exact hz n
  exact ⟨!{{0} | Set.range z}'H, lt_ofSets_of_mem_left (H := H) rfl,
    fun n ↦ ofSets_lt_of_mem_right (H := H) ⟨n, rfl⟩⟩

/-- **Eventual constancy**: an ℕ-indexed sequence of surreals converges to `x` if and only if
it is eventually equal to `x`. Nontrivial limits require transfinite sequences. -/
theorem tendstoSurreal_atTop_iff_eventuallyEq {f : ℕ → Surreal} {x : Surreal} :
    TendstoSurreal f atTop x ↔ ∀ᶠ n in atTop, f n = x := by
  constructor
  · rintro ⟨hlow, hupp⟩
    by_contra hev
    have hfreq : ∃ᶠ n in atTop, f n ≠ x := Filter.not_eventually.1 hev
    -- A positive surreal below every nonzero deviation `|f n - x|`.
    obtain ⟨e, he0, he⟩ := exists_pos_forall_lt
      (z := fun n ↦ if f n = x then 1 else |f n - x|)
      (fun n ↦ by split <;> simp_all [abs_pos, sub_ne_zero])
    -- But the sequence eventually deviates by less than `e`.
    have hev' : ∀ᶠ n in atTop, |f n - x| < e := by
      filter_upwards [hlow (x - e) (by linarith), hupp (x + e) (by linarith)] with n h1 h2
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hev').exists
    have := he n
    rw [if_neg hn1] at this
    exact absurd (this.trans hn2) (lt_irrefl _)
  · intro hev
    constructor
    · intro y hy
      filter_upwards [hev] with n hn
      rw [hn]; exact hy
    · intro y hy
      filter_upwards [hev] with n hn
      rw [hn]; exact hy

/-- The gap theorem is an instance of eventual constancy: `1/n` is not eventually constant. -/
theorem not_tendstoSurreal_inv_natCast' (x : Surreal) :
    ¬ TendstoSurreal (fun n : ℕ ↦ (n : Surreal)⁻¹) atTop x := by
  rw [tendstoSurreal_atTop_iff_eventuallyEq]
  intro hev
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have h1 : ((N : ℕ) : Surreal)⁻¹ = x := hN N le_rfl
  have h2 : ((N + 1 : ℕ) : Surreal)⁻¹ = x := hN (N + 1) (Nat.le_succ N)
  rw [← h2] at h1
  have h3 : ((N + 1 : ℕ) : Surreal) = ((N : ℕ) : Surreal) := inv_injective h1.symm
  have h4 : (N + 1 : ℕ) = N := by exact_mod_cast h3
  omega

end Surreal
