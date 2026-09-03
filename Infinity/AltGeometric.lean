/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.MonomialCensus

/-!
# The alternating geometric series and the halo of `(1 + ω⁻¹)⁻¹`

Substrate for the **inverse exponential value** `exp(−log(1+ω⁻¹)) = (1+ω⁻¹)⁻¹`: the
alternating geometric series `Σ (−1)ᵏ ω⁻ᵏ`, its exact residual calculus at
`v := (1+ω⁻¹)⁻¹ = ω/(ω+1)`, and the census lower bounds — all instances of the
parametric `MonomialCensus` machinery at the coefficient sequence `(−1)ᵏ`.

* `isHahnSum_alt_inv` : `v` **is a Hahn sum** of the alternating series, with exact
  residuals `v − Sₙ = (−ω⁻¹)ⁿ·v` — class exactly `ω⁻ⁿ`.
* `omega_sq_le_birthday_inv_one_add` : `birthday v ≥ ω²` (the `ω²`-hardness theorem at
  the alternating coefficients).
* `omega_sq_le_birthday_of_forall_mk_lt` — **the deep-halo trap**: *any* surreal at
  distance strictly finer than every scale `ω⁻ⁿ` from `v` is born at or after day `ω²`.
  (If it were born earlier, the monomial tube theorem centered at `v` would force it to
  be an alternating partial sum — which sits at distance *exactly* `ω⁻ⁿ` from `v`.)
  This is the lemma that will price every Hahn sum of the exponential series at
  `−logOmega`, since all of them live in `v`'s deep halo.

With the forthcoming upper bound `birthday v ≤ ω²` (the Conway-inverse device at
`ω + 1`) these close both the second computed canonical sum
`hahnSum (Σ (−1)ᵏ ω⁻ᵏ) = (1+ω⁻¹)⁻¹` and the inverse exponential value.
-/

noncomputable section

namespace Surreal

open ArchimedeanClass

local notation "ε₀" => eps0
local notation "Ω" => NatOrdinal.of Ordinal.omega0

/-! ### The alternating coefficients -/

/-- The alternating coefficient sequence `(−1)ᵏ`. -/
def altCoeff (k : ℕ) : Dyadic := (-1) ^ k

theorem altCoeff_ne_zero (k : ℕ) : altCoeff k ≠ 0 := by
  unfold altCoeff
  exact pow_ne_zero _ (by norm_num)

theorem altCoeff_cast (k : ℕ) : ((altCoeff k : Dyadic) : Surreal.{0}) = (-1) ^ k := by
  unfold altCoeff
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, dyadic_cast_mul', ih]
    congr 1
    rw [dyadic_cast_neg', dyadic_cast_one]

/-! ### The value and its class calculus -/

theorem one_add_eps0_pos : (0 : Surreal.{0}) < 1 + ε₀ := by
  have h := eps0_pos
  linarith

theorem one_add_eps0_ne_zero : (1 : Surreal.{0}) + ε₀ ≠ 0 :=
  one_add_eps0_pos.ne'

theorem mk_one_add_eps0 : ArchimedeanClass.mk ((1 : Surreal.{0}) + ε₀) = 0 := by
  have h : ArchimedeanClass.mk (1 : Surreal.{0}) < ArchimedeanClass.mk ε₀ := by
    rw [ArchimedeanClass.mk_one]
    exact eps0_infinitesimal
  rw [mk_add_eq_mk_left h, ArchimedeanClass.mk_one]

theorem mk_inv_one_add_eps0 :
    ArchimedeanClass.mk (((1 : Surreal.{0}) + ε₀)⁻¹) = 0 := by
  rw [ArchimedeanClass.mk_inv, mk_one_add_eps0, neg_zero]

theorem inv_one_add_eps0_pos : (0 : Surreal.{0}) < (1 + ε₀)⁻¹ :=
  inv_pos.2 one_add_eps0_pos

/-! ### The exact residual calculus -/

/-- The alternating partial sums against `1 + ω⁻¹`: the telescoping identity
`(1 + ω⁻¹)·Sₙ = 1 − (−ω⁻¹)ⁿ`. -/
theorem one_add_eps0_mul_monoS_alt (n : ℕ) :
    ((1 : Surreal.{0}) + ε₀) * monoS altCoeff n = 1 - (-ε₀) ^ n := by
  induction n with
  | zero => rw [monoS_zero, mul_zero, pow_zero, sub_self]
  | succ m ih =>
    rw [monoS_succ, mul_add, ih, altCoeff_cast]
    have h : ((-1 : Surreal.{0})) ^ m * ε₀ ^ m = (-ε₀) ^ m := (neg_pow ε₀ m).symm
    rw [pow_succ]
    calc 1 - (-ε₀) ^ m + (1 + ε₀) * ((-1 : Surreal.{0}) ^ m * ε₀ ^ m)
        = 1 - (-ε₀) ^ m + (1 + ε₀) * (-ε₀) ^ m := by rw [h]
      _ = 1 - (-ε₀) ^ m * -ε₀ := by ring

/-- **The exact residual**: `v − Sₙ = (−ω⁻¹)ⁿ · v`. -/
theorem sub_monoS_alt (n : ℕ) :
    ((1 : Surreal.{0}) + ε₀)⁻¹ - monoS altCoeff n = (-ε₀) ^ n * (1 + ε₀)⁻¹ := by
  have h := one_add_eps0_mul_monoS_alt n
  have hv : ((1 : Surreal.{0}) + ε₀)⁻¹ * (1 + ε₀) = 1 :=
    inv_mul_cancel₀ one_add_eps0_ne_zero
  calc ((1 : Surreal.{0}) + ε₀)⁻¹ - monoS altCoeff n
      = (1 + ε₀)⁻¹ * (1 - (1 + ε₀) * monoS altCoeff n) := by
        rw [mul_sub, mul_one, ← mul_assoc, hv, one_mul]
    _ = (-ε₀) ^ n * (1 + ε₀)⁻¹ := by rw [h]; ring

private theorem mk_neg_eps0_pow (n : ℕ) :
    ArchimedeanClass.mk ((-ε₀ : Surreal.{0}) ^ n) = ArchimedeanClass.mk (ε₀ ^ n) := by
  rw [neg_pow]
  rcases neg_one_pow_eq_or Surreal.{0} n with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, ArchimedeanClass.mk_neg]

/-- The residual class is exactly the scale. -/
theorem mk_sub_monoS_alt (n : ℕ) :
    ArchimedeanClass.mk (((1 : Surreal.{0}) + ε₀)⁻¹ - monoS altCoeff n)
      = ArchimedeanClass.mk (ε₀ ^ n) := by
  rw [sub_monoS_alt, ArchimedeanClass.mk_mul, mk_inv_one_add_eps0, add_zero,
    mk_neg_eps0_pow]

/-- **`(1+ω⁻¹)⁻¹` is a Hahn sum of the alternating geometric series.** -/
theorem isHahnSum_alt_inv :
    IsHahnSum (monoTerm altCoeff) (((1 : Surreal.{0}) + ε₀)⁻¹) := by
  intro n
  rw [show partialSum (monoTerm altCoeff) n = monoS altCoeff n from rfl,
    mk_sub_monoS_alt, mk_monoTerm altCoeff_ne_zero]

/-! ### The census lower bounds -/

/-- `birthday ((1+ω⁻¹)⁻¹) ≥ ω²`: the `ω²`-hardness theorem at the alternating
coefficients. -/
theorem omega_sq_le_birthday_inv_one_add :
    Ω * Ω ≤ (((1 : Surreal.{0}) + ε₀)⁻¹).birthday :=
  mono_omega_sq_le_birthday_of_isHahnSum altCoeff_ne_zero isHahnSum_alt_inv

/-- **The deep-halo trap**: any surreal at distance strictly finer than every scale
`ω⁻ⁿ` from `(1+ω⁻¹)⁻¹` is born at or after day `ω²`. Were it born earlier, the monomial
tube theorem centered at `v` would force it onto an alternating partial sum — which sits
at distance *exactly* `ω⁻ⁿ⁺²` from `v`. -/
theorem omega_sq_le_birthday_of_forall_mk_lt {z : Surreal.{0}}
    (hz : ∀ n : ℕ, ArchimedeanClass.mk (ε₀ ^ n)
      < ArchimedeanClass.mk (z - ((1 : Surreal.{0}) + ε₀)⁻¹)) :
    Ω * Ω ≤ z.birthday := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨a', ha', b', hb', hle⟩ := NatOrdinal.lt_mul_iff.1 hcon
  obtain ⟨p, rfl⟩ := NatOrdinal.lt_omega0.1 ha'
  obtain ⟨q, rfl⟩ := NatOrdinal.lt_omega0.1 hb'
  have h1 : z.birthday ≤ Ω * (((p + q) : ℕ) : NatOrdinal) := by
    have h2 : z.birthday ≤ (p : NatOrdinal) * Ω + Ω * (q : NatOrdinal) :=
      le_trans (le_add_of_nonneg_right bot_le) hle
    refine h2.trans (le_of_eq ?_)
    push_cast
    ring
  have h0 : (0 : NatOrdinal) < Ω := by
    have h := nat_lt_omega' 0
    rwa [Nat.cast_zero] at h
  have h3 : z.birthday < Ω * ((((p + q) + 2) : ℕ) : NatOrdinal) := by
    refine h1.trans_lt (mul_lt_mul_of_pos_left ?_ h0)
    exact_mod_cast (by omega : p + q < p + q + 2)
  have heq := mono_eq_monoS_of_birthday_lt_of_mk_lt altCoeff_ne_zero isHahnSum_alt_inv
    (p + q) (hz (p + q + 1)) h3
  have hres := mk_sub_monoS_alt (p + q + 2)
  have hz2 := hz (p + q + 2)
  rw [heq] at hz2
  rw [show ArchimedeanClass.mk (monoS altCoeff (p + q + 2) - (1 + ε₀)⁻¹)
      = ArchimedeanClass.mk ((1 + ε₀)⁻¹ - monoS altCoeff (p + q + 2)) from by
        rw [show monoS altCoeff (p + q + 2) - (1 + ε₀)⁻¹
            = -((1 + ε₀)⁻¹ - monoS altCoeff (p + q + 2)) from by ring,
          ArchimedeanClass.mk_neg],
    hres] at hz2
  exact lt_irrefl _ hz2

/-! ### The `ω/(ω+1)` form -/

/-- `(1+ω⁻¹)⁻¹ = ω/(ω+1)`. -/
theorem inv_one_add_eps0_eq_div :
    ((1 : Surreal.{0}) + ε₀)⁻¹ = ω^ (1 : Surreal) / (ω^ (1 : Surreal) + 1) := by
  have hw : (ω^ (1 : Surreal.{0})) ≠ 0 := (wpow_pos _).ne'
  have hw1 : (ω^ (1 : Surreal.{0})) + 1 ≠ 0 := by
    have := wpow_pos (1 : Surreal.{0})
    positivity
  rw [eps0_def]
  field_simp

end Surreal

end
