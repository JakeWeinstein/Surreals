/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.GeneralDeriv

/-!
# The Fractal Kernel Theorem

`Infinity.GeneralDeriv` posed the characterization question for the kernel of surreal
differentiation: is every function with derivative zero everywhere constant on galaxies —
is the galaxy indicator the *only* kind of counterexample? This file **settles the question
in the negative**, with a stronger and stranger counterexample.

The **micro-galaxy indicator** `microStep` is `0` on the surreals dominated by every power
`ω⁻ⁿ` (the "micro-halo" of `0` — a set of infinitesimals) and `1` everywhere else. We prove:

* `hasDerivS_microStep` : `microStep` has derivative **zero at every surreal point**, with
  the single uniform constant `C = ω^ω`. The reason: to jump the micro-gap, an increment
  `ε` must be at least `ω⁻ⁿ`-sized for some `n`, and then `ω^ω · ε² ≥ ω^(ω−2n)/k² ≥ 1`.
* `microStep_zero` / `microStep_inv_omega` : yet `microStep 0 = 0 ≠ 1 = microStep (1/ω)` —
  two points differing by an **infinitesimal**.

Hence (`exists_hasDerivS_zero_infinitesimal_jump`, `not_antideriv_unique_infinitesimal`):

**The kernel of differentiation on `No` is strictly larger than the galaxy-locally-constant
functions. Zero-derivative functions can jump across gaps at arbitrarily fine scales — the
Galaxy Kernel phenomenon is fractal, recurring inside every halo — and antiderivative
increments are ill-defined even over infinitesimal intervals.**

This closes the kernel-characterization question in the refined direction and shows the
cross-galaxy rigidity required for integration is needed at *every* scale simultaneously —
exactly the global-series rigidity that analyzable functions provide.
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

/-! ### Bridges: `ω`-powers vs iterated powers, naturals vs `ω` -/

/-- `ω`-power at a natural exponent is the iterated power of `ω`. -/
theorem wpow_natCast (n : ℕ) : ω^ ((n : ℕ) : Surreal) = (ω^ (1 : Surreal)) ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, wpow_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, wpow_add, ih, pow_succ]

private theorem mk_natCast_of_ne_zero {m : ℕ} (hm : m ≠ 0) :
    ArchimedeanClass.mk ((m : ℕ) : Surreal) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [ArchimedeanClass.stdPart_natCast]
  exact_mod_cast hm

private theorem mk_wpow_one_neg : ArchimedeanClass.mk (ω^ (1 : Surreal)) < 0 := by
  have h := archimedeanClassMk_wpow_strictAnti (one_pos : (0 : Surreal) < 1)
  simpa [wpow_zero, ArchimedeanClass.mk_one] using h

/-- Every natural number is below `ω`. -/
theorem natCast_lt_wpow_one (m : ℕ) : ((m : ℕ) : Surreal) < ω^ (1 : Surreal) := by
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · simp
  · have h1 : ArchimedeanClass.mk (ω^ (1 : Surreal)) <
        ArchimedeanClass.mk ((m : ℕ) : Surreal) := by
      rw [mk_natCast_of_ne_zero hm.ne']
      exact mk_wpow_one_neg
    have h2 := abs_lt_abs_of_mk_lt h1
    rwa [abs_of_nonneg (Nat.cast_nonneg m), wpow_abs] at h2

/-! ### The micro-galaxy indicator -/

/-- `w` is **micro-inner** when it is dominated by every power `ω⁻ⁿ`: it lies in the
micro-halo of `0`, below every scale the ω-powers can name. -/
def MicroInner (w : Surreal) : Prop :=
  ∀ n : ℕ, ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ n) < ArchimedeanClass.mk w

open Classical in
/-- The micro-galaxy indicator: `0` on the micro-halo of `0`, `1` everywhere else. -/
def microStep : Surreal → Surreal := fun w ↦ if MicroInner w then 0 else 1

theorem microInner_zero : MicroInner 0 := by
  intro n
  rw [ArchimedeanClass.mk_eq_top_iff.2 rfl]
  exact lt_top_iff_ne_top.2 fun h ↦
    pow_ne_zero n (inv_ne_zero (wpow_pos (1 : Surreal)).ne')
      (ArchimedeanClass.mk_eq_top_iff.1 h)

theorem not_microInner_inv_wpow_one : ¬ MicroInner ((ω^ (1 : Surreal))⁻¹) := by
  intro h
  have h1 := h 1
  rw [pow_one] at h1
  exact lt_irrefl _ h1

theorem microStep_zero : microStep 0 = 0 := by
  unfold microStep
  exact if_pos microInner_zero

theorem microStep_inv_wpow_one : microStep ((ω^ (1 : Surreal))⁻¹) = 1 := by
  unfold microStep
  exact if_neg not_microInner_inv_wpow_one

/-! ### Jumping the micro-gap requires an `ω⁻ⁿ`-sized increment -/

private theorem scale_of_inner_outer {x ε : Surreal} (hx : MicroInner x)
    (hxe : ¬ MicroInner (x + ε)) :
    ∃ n : ℕ, ArchimedeanClass.mk ε ≤ ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ n) := by
  rw [MicroInner] at hxe
  push Not at hxe
  obtain ⟨n, hn⟩ := hxe
  refine ⟨n, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  exact absurd (lt_of_lt_of_le (lt_min (hx n) hlt) (ArchimedeanClass.min_le_mk_add ..))
    (not_lt.2 hn)

private theorem scale_of_outer_inner {x ε : Surreal} (hx : ¬ MicroInner x)
    (hxe : MicroInner (x + ε)) :
    ∃ n : ℕ, ArchimedeanClass.mk ε ≤ ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ n) := by
  rw [MicroInner] at hx
  push Not at hx
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hx2 : x = (x + ε) + -ε := by ring
  refine absurd ?_ (not_lt.2 hn)
  rw [hx2]
  refine lt_of_lt_of_le (lt_min (hxe n) ?_) (ArchimedeanClass.min_le_mk_add ..)
  rwa [ArchimedeanClass.mk_neg]

/-! ### The uniform constant `C = ω^ω` beats every jump -/

private theorem one_le_wpow_mul_sq {ε : Surreal} {n : ℕ}
    (h : ArchimedeanClass.mk ε ≤ ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ n)) :
    1 ≤ ω^ (ω^ (1 : Surreal)) * ε ^ 2 := by
  have hE : (0 : Surreal) < (ω^ (1 : Surreal))⁻¹ := inv_pos.2 (wpow_pos _)
  obtain ⟨k, hk⟩ := ArchimedeanClass.mk_le_mk.1 h
  rw [abs_of_pos (pow_pos hE n), nsmul_eq_mul] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, zero_mul] at hk
    exact absurd hk (not_le.2 (pow_pos hE n))
  have hkS : (0 : Surreal) < (k : ℕ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk0)
  -- `|ε| ≥ ω⁻ⁿ / k`
  have hle : ((ω^ (1 : Surreal))⁻¹) ^ n / (k : ℕ) ≤ |ε| := by
    rw [div_le_iff₀ hkS, mul_comm]
    exact hk
  -- `C · (ω⁻ⁿ/k)² = ω^(ω − 2n) / k² ≥ ω > k²`
  have hpow : ω^ (ω^ (1 : Surreal)) * (((ω^ (1 : Surreal))⁻¹) ^ n) ^ 2 =
      ω^ (ω^ (1 : Surreal) - ((2 * n : ℕ) : Surreal)) := by
    rw [wpow_sub, wpow_natCast, ← pow_mul, div_eq_mul_inv, inv_pow]
    ring_nf
  have hexp : (1 : Surreal) ≤ ω^ (1 : Surreal) - ((2 * n : ℕ) : Surreal) := by
    have h1 := natCast_lt_wpow_one (2 * n + 1)
    push_cast at h1
    push_cast
    linarith
  have hbig : ((k : ℕ) : Surreal) ^ 2 < ω^ (ω^ (1 : Surreal) - ((2 * n : ℕ) : Surreal)) := by
    have h1 := natCast_lt_wpow_one (k ^ 2)
    push_cast at h1
    calc ((k : ℕ) : Surreal) ^ 2 < ω^ (1 : Surreal) := h1
      _ ≤ ω^ (ω^ (1 : Surreal) - ((2 * n : ℕ) : Surreal)) := wpow_le_wpow.2 hexp
  -- assemble
  have hstep : (1 : Surreal) ≤
      ω^ (ω^ (1 : Surreal)) * (((ω^ (1 : Surreal))⁻¹) ^ n / (k : ℕ)) ^ 2 := by
    rw [div_pow, ← mul_div_assoc, hpow, le_div_iff₀ (by positivity), one_mul]
    exact hbig.le
  refine hstep.trans ?_
  rw [show ε ^ 2 = |ε| ^ 2 from (sq_abs ε).symm]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hle 2) (wpow_pos _).le

/-! ### The theorems -/

/-- **The micro-galaxy indicator has derivative zero at every surreal point**, with the
single uniform constant `C = ω^ω`. -/
theorem hasDerivS_microStep (x : Surreal) : HasDerivS microStep x 0 := by
  refine ⟨ω^ (ω^ (1 : Surreal)), fun ε hε ↦ ?_⟩
  rw [zero_mul, sub_zero]
  unfold microStep
  by_cases hx : MicroInner x <;> by_cases hxe : MicroInner (x + ε)
  · rw [if_pos hxe, if_pos hx, sub_self, abs_zero]
    exact mul_nonneg (wpow_pos _).le (sq_nonneg ε)
  · obtain ⟨n, hn⟩ := scale_of_inner_outer hx hxe
    rw [if_neg hxe, if_pos hx, sub_zero, abs_one]
    exact one_le_wpow_mul_sq hn
  · obtain ⟨n, hn⟩ := scale_of_outer_inner hx hxe
    rw [if_pos hxe, if_neg hx, zero_sub, abs_neg, abs_one]
    exact one_le_wpow_mul_sq hn
  · rw [if_neg hxe, if_neg hx, sub_self, abs_zero]
    exact mul_nonneg (wpow_pos _).le (sq_nonneg ε)

/-- **The Fractal Kernel Theorem**: there is a function with derivative zero at every
surreal point that is non-constant *within a single halo* — its witnesses `0` and `1/ω`
differ by an infinitesimal. The kernel of surreal differentiation is strictly larger than
the galaxy-locally-constant functions: zero-derivative functions jump at arbitrarily fine
scales. -/
theorem exists_hasDerivS_zero_infinitesimal_jump :
    ∃ (F : Surreal → Surreal) (a b : Surreal), (∀ x, HasDerivS F x 0) ∧
      Infinitesimal (b - a) ∧ F a ≠ F b := by
  refine ⟨microStep, 0, (ω^ (1 : Surreal))⁻¹, hasDerivS_microStep, ?_, ?_⟩
  · simpa using infinitesimal_inv_wpow one_pos
  · rw [microStep_zero, microStep_inv_wpow_one]
    norm_num

/-- **Antiderivative increments are ill-defined even over infinitesimal intervals**:
two functions with derivative zero everywhere whose increments over `[0, 1/ω]` disagree.
The rigidity that integration requires is needed at every scale simultaneously. -/
theorem not_antideriv_unique_infinitesimal :
    ∃ (F G : Surreal → Surreal) (a b : Surreal), Infinitesimal (b - a) ∧
      (∀ x, HasDerivS F x 0) ∧ (∀ x, HasDerivS G x 0) ∧ F b - F a ≠ G b - G a := by
  refine ⟨microStep, fun _ ↦ 0, 0, (ω^ (1 : Surreal))⁻¹, ?_, hasDerivS_microStep,
    fun x ↦ ⟨1, fun ε hε ↦ ?_⟩, ?_⟩
  · simpa using infinitesimal_inv_wpow one_pos
  · rw [zero_mul, sub_zero, sub_self, abs_zero, one_mul]
    positivity
  · rw [microStep_zero, microStep_inv_wpow_one]
    norm_num

end Surreal
