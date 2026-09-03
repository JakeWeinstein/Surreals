/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.Summation

/-!
# The exponential series at an infinitesimal has a sum: `e^(1/ω)` exists

The Transfinite Summation Theorem (`exists_isHahnSum`) makes short work of a milestone:
the exponential series `Σ_{k<ω} εᵏ/k!` at any nonzero infinitesimal `ε` is strictly
dominating — each term lives in a strictly smaller magnitude class than the last — and
therefore **has a transfinite sum** in `No`. In particular `e^(1/ω)` denotes a surreal
number (well-defined up to the usual domination equivalence of `IsHahnSum.mk_sub_le`).

This is the first value of a transcendental function reached on `No` by this development,
and the on-ramp to Gonshor's exponential: once a *canonical* (simplest) Hahn sum is chosen,
`exp` on infinitesimals is exactly this series.

* `Surreal.mk_pow_lt_mk_pow_succ'` — powers of any nonzero infinitesimal strictly dominate
  (generalizing the positive case from `Infinity.Summation`).
* `Surreal.expSeries_strict_dominating` — the exponential series is strictly dominating.
* `Surreal.exists_isHahnSum_expSeries` — its Hahn sum exists.
* `Surreal.exists_exp_inv_omega` — the flagship instance: `Σ_{k<ω} (1/ω)ᵏ/k!` has a sum.
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

/-- Powers of any nonzero infinitesimal are strictly dominating (via absolute values). -/
theorem mk_pow_lt_mk_pow_succ' {e : Surreal} (he : Infinitesimal e) (he0 : e ≠ 0) (k : ℕ) :
    ArchimedeanClass.mk (e ^ k) < ArchimedeanClass.mk (e ^ (k + 1)) := by
  have habs0 : (0 : Surreal) < |e| := abs_pos.2 he0
  have habsinf : Infinitesimal |e| := by
    rwa [Infinitesimal, ArchimedeanClass.mk_abs]
  have h := mk_pow_lt_mk_pow_succ habsinf habs0 k
  rwa [← abs_pow, ← abs_pow, ArchimedeanClass.mk_abs, ArchimedeanClass.mk_abs] at h

theorem mk_factorial (k : ℕ) : ArchimedeanClass.mk ((k.factorial : ℕ) : Surreal) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [ArchimedeanClass.stdPart_natCast]
  exact_mod_cast k.factorial_ne_zero

/-- The exponential series `k ↦ εᵏ/k!` at a nonzero infinitesimal is strictly dominating. -/
theorem expSeries_strict_dominating {e : Surreal} (he : Infinitesimal e) (he0 : e ≠ 0)
    (k : ℕ) :
    ArchimedeanClass.mk (e ^ k / ((k.factorial : ℕ) : Surreal)) <
      ArchimedeanClass.mk (e ^ (k + 1) / (((k + 1).factorial : ℕ) : Surreal)) := by
  rw [ArchimedeanClass.mk_div, ArchimedeanClass.mk_div, mk_factorial, mk_factorial,
    sub_zero, sub_zero]
  exact mk_pow_lt_mk_pow_succ' he he0 k

/-- **The exponential series sums**: for any nonzero infinitesimal `ε`, the series
`Σ_{k<ω} εᵏ/k!` has a transfinite (Hahn) sum in `No`. -/
theorem exists_isHahnSum_expSeries {e : Surreal} (he : Infinitesimal e) (he0 : e ≠ 0) :
    ∃ x, IsHahnSum (fun k ↦ e ^ k / ((k.factorial : ℕ) : Surreal)) x :=
  exists_isHahnSum (expSeries_strict_dominating he he0)

/-- **`e^(1/ω)` exists**: the exponential series at the canonical infinitesimal `1/ω` has a
transfinite sum — a surreal number infinitesimally close to `1 + 1/ω`. -/
theorem exists_exp_inv_omega :
    ∃ x, IsHahnSum (fun k ↦ ((ω^ (1 : Surreal))⁻¹) ^ k / ((k.factorial : ℕ) : Surreal)) x :=
  exists_isHahnSum_expSeries (infinitesimal_inv_wpow one_pos)
    (inv_ne_zero (wpow_pos _).ne')

end Surreal
