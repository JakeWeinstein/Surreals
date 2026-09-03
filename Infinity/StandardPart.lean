/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import CombinatorialGames.Surreal.Pow
import Mathlib.Algebra.Order.Ring.StandardPart

/-!
# Finite surreals, infinitesimals, and the standard part

Every surreal number falls into exactly one of three regimes relative to the reals: *finite*
(bounded by some natural number), *infinite*, or — within the finites — *infinitesimally close*
to a unique real number. This file sets up that trichotomy for `Surreal` and proves the
fundamental decomposition:

* `Surreal.IsFinite x`: `x` is bounded in absolute value by a natural number, expressed via its
  Archimedean class.
* `Surreal.Infinitesimal x`: `|x|` is smaller than every positive rational.
* `Surreal.stdPart_realCast`: the standard part function of mathlib
  (`ArchimedeanClass.stdPart : Surreal → ℝ`) is a *section* of the canonical embedding
  `Real.toSurreal : ℝ ↪ Surreal`, i.e. `stdPart ↑r = r`.
* `Surreal.infinitesimal_sub_stdPart`: every finite surreal `x` decomposes as
  `x = ↑(stdPart x) + ε` with `ε` infinitesimal.
* `Surreal.stdPart_eq_of_infinitesimal_sub`: this real number is unique.

This is the surreal analogue of the standard part function from nonstandard analysis: the
"finite part" projection `No ⊇ {finite} → ℝ` that any theory of calculus on the surreals
factors through.
-/

universe u

noncomputable section

namespace Surreal

/-- A surreal number is *finite* if it is bounded in absolute value by some natural number,
i.e. its Archimedean class is at least that of `1`. -/
def IsFinite (x : Surreal) : Prop :=
  0 ≤ ArchimedeanClass.mk x

/-- A surreal number is *infinitesimal* if its absolute value is below every positive rational,
i.e. its Archimedean class is strictly greater than that of `1`. (Note `0` is infinitesimal.) -/
def Infinitesimal (x : Surreal) : Prop :=
  0 < ArchimedeanClass.mk x

theorem isFinite_def {x : Surreal} : IsFinite x ↔ 0 ≤ ArchimedeanClass.mk x := .rfl

theorem infinitesimal_def {x : Surreal} : Infinitesimal x ↔ 0 < ArchimedeanClass.mk x := .rfl

theorem Infinitesimal.isFinite {x : Surreal} (h : Infinitesimal x) : IsFinite x :=
  h.le

@[simp]
theorem isFinite_zero : IsFinite (0 : Surreal) := by
  simp [IsFinite]

@[simp]
theorem infinitesimal_zero : Infinitesimal (0 : Surreal) := by
  simp [Infinitesimal]

@[simp]
theorem isFinite_one : IsFinite (1 : Surreal) := by
  simp [IsFinite]

theorem IsFinite.neg {x : Surreal} (h : IsFinite x) : IsFinite (-x) := by
  rwa [IsFinite, ArchimedeanClass.mk_neg]

theorem Infinitesimal.neg {x : Surreal} (h : Infinitesimal x) : Infinitesimal (-x) := by
  rwa [Infinitesimal, ArchimedeanClass.mk_neg]

theorem IsFinite.add {x y : Surreal} (hx : IsFinite x) (hy : IsFinite y) : IsFinite (x + y) :=
  le_trans (le_min hx hy) (ArchimedeanClass.min_le_mk_add ..)

theorem IsFinite.sub {x y : Surreal} (hx : IsFinite x) (hy : IsFinite y) : IsFinite (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem Infinitesimal.add {x y : Surreal} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) :=
  lt_of_lt_of_le (lt_min hx hy) (ArchimedeanClass.min_le_mk_add ..)

theorem IsFinite.mul {x y : Surreal} (hx : IsFinite x) (hy : IsFinite y) : IsFinite (x * y) := by
  rw [IsFinite, ArchimedeanClass.mk_mul]
  exact add_nonneg hx hy

/-- A finite multiple of an infinitesimal is infinitesimal. -/
theorem IsFinite.mul_infinitesimal {x y : Surreal} (hx : IsFinite x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) := by
  have h := add_le_add_right hx (ArchimedeanClass.mk y)
  rw [add_zero] at h
  rw [Infinitesimal, ArchimedeanClass.mk_mul, add_comm]
  exact hy.trans_le h

theorem Infinitesimal.mul_isFinite {x y : Surreal} (hx : Infinitesimal x) (hy : IsFinite y) :
    Infinitesimal (x * y) := by
  rw [mul_comm]
  exact hy.mul_infinitesimal hx

theorem IsFinite.pow {x : Surreal} (h : IsFinite x) (n : ℕ) : IsFinite (x ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact ih.mul h

@[simp]
theorem isFinite_realCast (r : ℝ) : IsFinite (r : Surreal) := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  · exact (mk_realCast hr).ge

@[simp]
theorem isFinite_ratCast (q : ℚ) : IsFinite (q : Surreal) := by
  rw [← Real.toSurreal_ratCast]
  exact isFinite_realCast q

/-! ### The standard part is a section of `Real.toSurreal` -/

open ArchimedeanClass in
/-- The standard part function on the surreals, restricted along the canonical embedding of the
reals, is the identity: rounding a real number to its nearest real does nothing.

Together with `Surreal.infinitesimal_sub_stdPart`, this says `stdPart` is a retraction of
`Real.toSurreal` — the surreal-specific fact mathlib's general theory cannot state. -/
@[simp]
theorem stdPart_realCast (r : ℝ) : stdPart (r : Surreal) = r := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  -- Squeeze between rationals: `stdPart` is monotone on the finite elements and fixes `ℚ`.
  · have key : ∀ s : ℝ, ∀ q : ℚ, s < q → stdPart (s : Surreal) ≤ q := by
      intro s q h
      have h' : (s : Surreal) ≤ ((q : ℚ) : Surreal) := by
        rw [← Real.toSurreal_ratCast]
        exact Real.toSurreal_le_iff.2 h.le
      calc stdPart (s : Surreal) ≤ stdPart ((q : ℚ) : Surreal) :=
            stdPart_monotoneOn (isFinite_realCast s) (isFinite_ratCast q) h'
        _ = q := stdPart_ratCast q
    apply le_antisymm
    · by_contra h
      rw [not_le] at h
      obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn h
      exact absurd (key r q hq₁) hq₂.not_ge
    · by_contra h
      rw [not_le] at h
      obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn h
      have h' : ((q : ℚ) : Surreal) ≤ (r : Surreal) := by
        rw [← Real.toSurreal_ratCast]
        exact Real.toSurreal_le_iff.2 hq₂.le
      have hle : (q : ℝ) ≤ stdPart (r : Surreal) :=
        calc (q : ℝ) = stdPart ((q : ℚ) : Surreal) := (stdPart_ratCast q).symm
          _ ≤ stdPart (r : Surreal) :=
            stdPart_monotoneOn (isFinite_ratCast q) (isFinite_realCast r) h'
      exact absurd (hle.trans_lt hq₁) (lt_irrefl _)

open ArchimedeanClass in
/-- **The standard part decomposition**: every finite surreal number is infinitesimally close
to its standard part. Equivalently, `x = ↑(stdPart x) + ε` with `ε` infinitesimal. -/
theorem infinitesimal_sub_stdPart {x : Surreal} (hx : IsFinite x) :
    Infinitesimal (x - stdPart x) := by
  have hfin : IsFinite (x - (stdPart x : Surreal)) := hx.sub (isFinite_realCast _)
  have hzero : stdPart (x - (stdPart x : Surreal)) = 0 := by
    rw [stdPart_sub hx (isFinite_realCast _), stdPart_realCast, sub_self]
  rw [Infinitesimal]
  rcases hfin.lt_or_eq with h | h
  · exact h
  · exact absurd (stdPart_eq_zero.1 hzero) (by rw [← h]; simp)

open ArchimedeanClass in
/-- The standard part is the *unique* real number infinitesimally close to a finite surreal. -/
theorem stdPart_eq_of_infinitesimal_sub {x : Surreal} {r : ℝ} (h : Infinitesimal (x - r)) :
    stdPart x = r := by
  have hx : x = (r : Surreal) + (x - r) := by ring
  rw [hx, stdPart_add_eq_left h, stdPart_realCast]

open ArchimedeanClass in
/-- Existence and uniqueness of the standard part, packaged: a finite surreal is
infinitesimally close to exactly one real number. -/
theorem existsUnique_infinitesimal_sub {x : Surreal} (hx : IsFinite x) :
    ∃! r : ℝ, Infinitesimal (x - r) :=
  ⟨stdPart x, infinitesimal_sub_stdPart hx,
    fun _ h ↦ (stdPart_eq_of_infinitesimal_sub h).symm⟩

/-! ### Concrete infinitesimals: `(ω^ x)⁻¹` -/

open ArchimedeanClass in
/-- The reciprocal of `ω^ x` for positive `x` is a (nonzero) infinitesimal. In particular
`(ω^ 1)⁻¹ = 1/ω` is the canonical example of an infinitesimal surreal. -/
theorem infinitesimal_inv_wpow {x : Surreal} (hx : 0 < x) : Infinitesimal (ω^ x)⁻¹ := by
  rw [Infinitesimal, ← wpow_neg]
  have h := archimedeanClassMk_wpow_strictAnti (neg_lt_zero.2 hx)
  simpa [wpow_zero, ArchimedeanClass.mk_one] using h

end Surreal
