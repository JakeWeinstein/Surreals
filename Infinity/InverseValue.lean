/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.ExpLog
import Infinity.AltGeometric
import Infinity.ExpNegLog
import Infinity.AltInverse

/-!
# The inverse exponential value: `exp (−log (1+ω⁻¹)) = (1+ω⁻¹)⁻¹`

Endgame file for the inverse-value campaign. Given the two halves proved in
`Infinity/AltInverse.lean` (the Conway-inverse upper bound
`birthday ((1+ω⁻¹)⁻¹) ≤ ω²`) and `Infinity/ExpNegLog.lean` (the domination half:
`(1+ω⁻¹)⁻¹` is a Hahn sum of the exponential series at `−logOmega`), this file closes:

* `expInf_neg_logOmega_eq` : **`exp (−logOmega) = (1+ω⁻¹)⁻¹`** — the first exact
  exponential value at a *negative* argument, and the first with genuine cancellation
  in its series.
* the **reflection law** `exp (logOmega) · exp (−logOmega) = 1` — the multiplicative
  inverse identity for the canonical-sum exponential.
* `hahnSum_alt_eq` : **`hahnSum (Σ (−1)ᵏ ω⁻ᵏ) = (1+ω⁻¹)⁻¹`** — the second computed
  value of the canonical transfinite summation operator.
* exact birthdays: both values are born exactly on day `ω²` — against
  `birthday (exp logOmega) = ω`: **negating the argument explodes the exponential's
  birthday from `ω` to `ω²`**, the first exponential value priced at a limit block.

This file contains the pieces independent of the two halves: the term-class calculus of
the exponential series at `−logOmega` and the `ω²` pricing of **every** Hahn sum of that
series (conditional on the domination half), via `AltGeometric`'s deep-halo trap.
-/

noncomputable section

namespace Surreal

open ArchimedeanClass

local notation "ε₀" => eps0
local notation "Ω" => NatOrdinal.of Ordinal.omega0

/-! ### The term-class calculus at `−logOmega` -/

private theorem mk_pow_congr'' {a b : Surreal}
    (h : ArchimedeanClass.mk a = ArchimedeanClass.mk b) (n : ℕ) :
    ArchimedeanClass.mk (a ^ n) = ArchimedeanClass.mk (b ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, ih, h]

/-- The exponential series terms at `−logOmega` live at exactly the `ω`-power scales. -/
theorem mk_expTerm_neg_logOmega (n : ℕ) :
    ArchimedeanClass.mk ((-logOmega) ^ n / ((n.factorial : ℕ) : Surreal))
      = ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n) := by
  rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero]
  refine mk_pow_congr'' ?_ n
  rw [ArchimedeanClass.mk_neg, mk_logOmega]
  rfl

/-! ### The `ω²` pricing of every exponential Hahn sum at `−logOmega` -/

/-- **Every Hahn sum of the exponential series at `−logOmega` is born at or after day
`ω²`** — conditional on the domination half (`(1+ω⁻¹)⁻¹` being one such sum): any two
Hahn sums of one series differ below every term's scale, so every sum sits in the deep
halo of `(1+ω⁻¹)⁻¹`, where `AltGeometric`'s trap prices it. -/
theorem omega_sq_le_birthday_of_isHahnSum_expNeg
    (hv : IsHahnSum (fun k ↦ (-logOmega) ^ k / ((k.factorial : ℕ) : Surreal))
      (((1 : Surreal.{0}) + ε₀)⁻¹))
    {w : Surreal.{0}}
    (hw : IsHahnSum (fun k ↦ (-logOmega) ^ k / ((k.factorial : ℕ) : Surreal)) w) :
    Ω * Ω ≤ w.birthday := by
  refine omega_sq_le_birthday_of_forall_mk_lt fun n ↦ ?_
  calc ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n)
      < ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ (n + 1)) :=
        mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos n
    _ = ArchimedeanClass.mk ((-logOmega) ^ (n + 1)
          / (((n + 1).factorial : ℕ) : Surreal)) :=
        (mk_expTerm_neg_logOmega (n + 1)).symm
    _ ≤ ArchimedeanClass.mk (w - ((1 : Surreal.{0}) + ε₀)⁻¹) := hw.mk_sub_le hv (n + 1)

/-- Unconditional form, via the domination half (`Infinity.ExpNegLog`): every Hahn sum
of the exponential series at `−logOmega` is born at or after day `ω²`. Contrast with the
positive anchor: at `+logOmega` the sums start at day `ω`. -/
theorem omega_sq_le_birthday_of_isHahnSum_expNeg' {w : Surreal.{0}}
    (hw : IsHahnSum (fun k ↦ (-logOmega) ^ k / ((k.factorial : ℕ) : Surreal)) w) :
    Ω * Ω ≤ w.birthday :=
  omega_sq_le_birthday_of_isHahnSum_expNeg isHahnSum_expSeries_neg_logOmega hw

/-! ### The exact birthday of `(1+ω⁻¹)⁻¹` -/

/-- **`birthday ((1+ω⁻¹)⁻¹) = ω·ω` exactly**: the Conway-inverse upper bound
(`AltInverse`) meets the `ω²`-hardness lower bound (`AltGeometric`). -/
theorem birthday_inv_one_add_eps0_eq :
    (((1 : Surreal.{0}) + ε₀)⁻¹).birthday = Ω * Ω :=
  le_antisymm birthday_inv_one_add_eps0_le omega_sq_le_birthday_inv_one_add

/-! ### The second computed canonical sum -/

/-- **THE CANONICAL ALTERNATING SUM**: `hahnSum (Σ (−1)ᵏ ω⁻ᵏ) = (1+ω⁻¹)⁻¹` — the
second computed value of the canonical transfinite summation operator, after
`hahnSum (Σ ω⁻ᵏ) = ω/(ω−1)`. -/
theorem hahnSum_alt_eq :
    hahnSum (monoTerm_strict_dominating altCoeff_ne_zero)
      = ((1 : Surreal.{0}) + ε₀)⁻¹ :=
  hahnSum_eq_of_isHahnSum_of_birthday_le _ isHahnSum_alt_inv
    (birthday_inv_one_add_eps0_le.trans
      (mono_omega_sq_le_birthday_hahnSum altCoeff_ne_zero))

/-- The `ω/(ω+1)` form of the canonical alternating sum. -/
theorem hahnSum_alt_eq_div :
    hahnSum (monoTerm_strict_dominating altCoeff_ne_zero)
      = ω^ (1 : Surreal) / (ω^ (1 : Surreal) + 1) := by
  rw [hahnSum_alt_eq, inv_one_add_eps0_eq_div]

/-- The canonical alternating sum is born exactly on day `ω·ω`. -/
theorem birthday_hahnSum_alt_eq :
    (hahnSum (monoTerm_strict_dominating altCoeff_ne_zero)).birthday = Ω * Ω := by
  rw [hahnSum_alt_eq]
  exact birthday_inv_one_add_eps0_eq

/-! ### The inverse exponential value and the reflection law -/

/-- **THE INVERSE EXPONENTIAL VALUE**: `exp (−log (1+ω⁻¹)) = (1+ω⁻¹)⁻¹` — the first
exact value of the canonical-sum exponential at a *negative* argument, and the first
whose series has genuine cancellation. Identification mirrors `expInf_logOmega_eq`:
the value is a Hahn sum (the domination half, `ExpNegLog`) of minimal birthday (born
by `ω²` via the Conway inverse, while every Hahn sum of the series is born at or after
`ω²` via the deep-halo trap). -/
theorem expInf_neg_logOmega_eq :
    expInf (-logOmega) neg_logOmega_infinitesimal neg_logOmega_ne_zero
      = ((1 : Surreal.{0}) + ε₀)⁻¹ := by
  unfold expInf
  rw [hahnSum_eq_iff]
  refine ⟨isHahnSum_expSeries_neg_logOmega, fun w hw ↦ ?_⟩
  exact birthday_inv_one_add_eps0_le.trans
    (omega_sq_le_birthday_of_isHahnSum_expNeg' hw)

/-- **THE REFLECTION LAW**: `exp (logOmega) · exp (−logOmega) = 1` — the multiplicative
inverse identity for the canonical-sum exponential, exact on **No**. -/
theorem expInf_logOmega_mul_expInf_neg_logOmega :
    (expInf logOmega logOmega_infinitesimal logOmega_pos.ne'
      * expInf (-logOmega) neg_logOmega_infinitesimal neg_logOmega_ne_zero
        : Surreal.{0}) = 1 := by
  rw [expInf_logOmega_eq, expInf_neg_logOmega_eq, ← eps0_def]
  exact mul_inv_cancel₀ one_add_eps0_ne_zero

/-- **Negating the argument explodes the birthday from `ω` to `ω²`**: the inverse
exponential value is born exactly on day `ω·ω` — the first exponential value priced at
a limit block (`birthday_expInf_logOmega` prices the positive anchor at `ω`). -/
theorem birthday_expInf_neg_logOmega :
    (expInf (-logOmega) neg_logOmega_infinitesimal neg_logOmega_ne_zero
      : Surreal.{0}).birthday = Ω * Ω := by
  rw [expInf_neg_logOmega_eq]
  exact birthday_inv_one_add_eps0_eq

end Surreal

end
