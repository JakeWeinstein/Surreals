/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.MonomialCensus

/-!
# The negative grid substrate: `Σ (−a)ᵏ ω⁻ᵏ` and the halos of `(1 + a·ω⁻¹)⁻¹`

Phase-23 substrate, generalizing `Infinity/AltGeometric.lean` from the single anchor
`a = 1` to every nonzero dyadic `a`: the series `Σ (−a)ᵏ ω⁻ᵏ`, its exact residual
calculus at `v_a := (1 + a·ω⁻¹)⁻¹`, the `ω²` census lower bounds, and — repairing a
hard-coding from Phase 22 — **the general deep-halo trap**
(`mono_omega_sq_le_birthday_of_forall_mk_lt`): around *any* Hahn sum of *any*
nonzero-dyadic-coefficient monomial series, anything strictly finer than every scale is
born at or after day `ω²`.

Downstream (`NegGridInverse`, `ExpNegGrid`, `NegGridValue`) this closes the **negative
grid theorem** `exp (−log (1 + a·ω⁻¹)) = (1 + a·ω⁻¹)⁻¹` and the **grid reflection
law**, plus an infinite family of computed canonical sums.
-/

noncomputable section

namespace Surreal

open ArchimedeanClass

local notation "ε₀" => eps0
local notation "Ω" => NatOrdinal.of Ordinal.omega0

/-! ### The general deep-halo trap -/

/-- **The general deep-halo trap**: for any nonzero-dyadic-coefficient monomial series
and any Hahn sum `w` of it, a surreal at distance strictly finer than every scale
`ω⁻ⁿ` from `w` is born at or after day `ω²`. (Were it born earlier, the monomial tube
theorem centered at `w` would force it onto a partial sum — which sits at distance
*exactly* `ω⁻ⁿ` from `w` by the exact residual calculus.) Generalizes
`AltGeometric.omega_sq_le_birthday_of_forall_mk_lt` from the alternating series to
every series `MonomialCensus` covers. -/
theorem mono_omega_sq_le_birthday_of_forall_mk_lt {c : ℕ → Dyadic}
    (hc : ∀ k, c k ≠ 0) {w : Surreal.{0}} (hw : IsHahnSum (monoTerm c) w)
    {z : Surreal.{0}}
    (hz : ∀ n : ℕ, ArchimedeanClass.mk (ε₀ ^ n) < ArchimedeanClass.mk (z - w)) :
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
  have heq := mono_eq_monoS_of_birthday_lt_of_mk_lt hc hw (p + q) (hz (p + q + 1)) h3
  have hres := mk_sub_monoS hc hw (p + q + 2)
  have hz2 := hz (p + q + 2)
  rw [heq] at hz2
  rw [show ArchimedeanClass.mk (monoS c (p + q + 2) - w)
      = ArchimedeanClass.mk (w - monoS c (p + q + 2)) from by
        rw [show monoS c (p + q + 2) - w = -(w - monoS c (p + q + 2)) from by ring,
          ArchimedeanClass.mk_neg],
    hres] at hz2
  exact lt_irrefl _ hz2

/-! ### The dyadic anchor `a·ω⁻¹` -/

theorem dyadic_mul_eps0_infinitesimal' (a : Dyadic) :
    Infinitesimal ((a : Surreal.{0}) * ε₀) := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [dyadic_cast_zero, zero_mul]
    exact infinitesimal_zero
  · rw [infinitesimal_def, ArchimedeanClass.mk_mul, mk_dyadic_cast_ne_zero ha, zero_add]
    exact infinitesimal_def.1 eps0_infinitesimal

theorem dyadic_mul_eps0_ne_zero' {a : Dyadic} (ha : a ≠ 0) :
    (a : Surreal.{0}) * ε₀ ≠ 0 := by
  refine mul_ne_zero (fun h ↦ ha ?_) eps0_pos.ne'
  exact dyadic_cast_inj (by rw [h, dyadic_cast_zero])

theorem mk_dyadic_mul_eps0 {a : Dyadic} (ha : a ≠ 0) :
    ArchimedeanClass.mk ((a : Surreal.{0}) * ε₀) = ArchimedeanClass.mk ε₀ := by
  rw [ArchimedeanClass.mk_mul, mk_dyadic_cast_ne_zero ha, zero_add]

/-! ### The value `(1 + a·ω⁻¹)⁻¹` -/

theorem one_add_dyadic_mul_eps0_pos (a : Dyadic) :
    (0 : Surreal.{0}) < 1 + (a : Surreal) * ε₀ := by
  have h := (dyadic_mul_eps0_infinitesimal' a).abs_lt_ratCast (q := 1) (by norm_num)
  rw [Rat.cast_one] at h
  have h2 := neg_abs_le ((a : Surreal.{0}) * ε₀)
  linarith

theorem one_add_dyadic_mul_eps0_ne_zero (a : Dyadic) :
    (1 : Surreal.{0}) + (a : Surreal) * ε₀ ≠ 0 :=
  (one_add_dyadic_mul_eps0_pos a).ne'

theorem mk_one_add_dyadic_mul_eps0 (a : Dyadic) :
    ArchimedeanClass.mk ((1 : Surreal.{0}) + (a : Surreal) * ε₀) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [dyadic_cast_zero, zero_mul, add_zero, ArchimedeanClass.mk_one]
  · have h : ArchimedeanClass.mk (1 : Surreal.{0})
        < ArchimedeanClass.mk ((a : Surreal) * ε₀) := by
      rw [ArchimedeanClass.mk_one]
      exact dyadic_mul_eps0_infinitesimal' a
    rw [mk_add_eq_mk_left h, ArchimedeanClass.mk_one]

theorem mk_inv_one_add_dyadic_mul_eps0 (a : Dyadic) :
    ArchimedeanClass.mk (((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹) = 0 := by
  rw [ArchimedeanClass.mk_inv, mk_one_add_dyadic_mul_eps0, neg_zero]

/-! ### The series `Σ (−a)ᵏ ω⁻ᵏ` and the exact residual calculus -/

/-- The negative-grid coefficient sequence `(−a)ᵏ`. -/
def negCoeff (a : Dyadic) (k : ℕ) : Dyadic := (-a) ^ k

theorem negCoeff_ne_zero {a : Dyadic} (ha : a ≠ 0) (k : ℕ) : negCoeff a k ≠ 0 := by
  unfold negCoeff
  exact pow_ne_zero _ (neg_ne_zero.2 ha)

theorem negCoeff_cast (a : Dyadic) (k : ℕ) :
    ((negCoeff a k : Dyadic) : Surreal.{0}) = (-(a : Surreal)) ^ k := by
  unfold negCoeff
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, dyadic_cast_mul', ih, dyadic_cast_neg']

/-- The telescoping identity `(1 + a·ω⁻¹) · Sₙ = 1 − (−a·ω⁻¹)ⁿ`. -/
theorem one_add_mul_monoS_neg (a : Dyadic) (n : ℕ) :
    ((1 : Surreal.{0}) + (a : Surreal) * ε₀) * monoS (negCoeff a) n
      = 1 - (-((a : Surreal) * ε₀)) ^ n := by
  induction n with
  | zero => rw [monoS_zero, mul_zero, pow_zero, sub_self]
  | succ m ih =>
    rw [monoS_succ, mul_add, ih, negCoeff_cast]
    have h : (-(a : Surreal.{0})) ^ m * ε₀ ^ m = (-((a : Surreal) * ε₀)) ^ m := by
      rw [← mul_pow]
      congr 1
      ring
    rw [pow_succ]
    calc 1 - (-((a : Surreal.{0}) * ε₀)) ^ m
          + (1 + (a : Surreal) * ε₀) * ((-(a : Surreal)) ^ m * ε₀ ^ m)
        = 1 - (-((a : Surreal) * ε₀)) ^ m
          + (1 + (a : Surreal) * ε₀) * (-((a : Surreal) * ε₀)) ^ m := by rw [h]
      _ = 1 - (-((a : Surreal) * ε₀)) ^ m * -((a : Surreal) * ε₀) := by ring

/-- **The exact residual**: `v_a − Sₙ = (−a·ω⁻¹)ⁿ · v_a`. -/
theorem sub_monoS_neg (a : Dyadic) (n : ℕ) :
    ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ - monoS (negCoeff a) n
      = (-((a : Surreal) * ε₀)) ^ n * (1 + (a : Surreal) * ε₀)⁻¹ := by
  have h := one_add_mul_monoS_neg a n
  have hv : ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹
      * (1 + (a : Surreal) * ε₀) = 1 :=
    inv_mul_cancel₀ (one_add_dyadic_mul_eps0_ne_zero a)
  calc ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ - monoS (negCoeff a) n
      = (1 + (a : Surreal) * ε₀)⁻¹
          * (1 - (1 + (a : Surreal) * ε₀) * monoS (negCoeff a) n) := by
        rw [mul_sub, mul_one, ← mul_assoc, hv, one_mul]
    _ = (-((a : Surreal) * ε₀)) ^ n * (1 + (a : Surreal) * ε₀)⁻¹ := by rw [h]; ring

private theorem mk_neg_pow_eq {x : Surreal} (n : ℕ) :
    ArchimedeanClass.mk ((-x) ^ n) = ArchimedeanClass.mk (x ^ n) := by
  rw [neg_pow]
  rcases neg_one_pow_eq_or Surreal n with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, ArchimedeanClass.mk_neg]

/-- The residual class is exactly the scale. -/
theorem mk_sub_monoS_neg {a : Dyadic} (ha : a ≠ 0) (n : ℕ) :
    ArchimedeanClass.mk
        (((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ - monoS (negCoeff a) n)
      = ArchimedeanClass.mk (ε₀ ^ n) := by
  rw [sub_monoS_neg, ArchimedeanClass.mk_mul, mk_inv_one_add_dyadic_mul_eps0,
    add_zero, mk_neg_pow_eq, mul_pow, ArchimedeanClass.mk_mul]
  rw [show ((a : Surreal.{0}) ^ n) = (((a ^ n : Dyadic) : Surreal)) from by
      induction n with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_succ, dyadic_cast_mul', ih],
    mk_dyadic_cast_ne_zero (pow_ne_zero _ ha), zero_add]

/-- **`(1 + a·ω⁻¹)⁻¹` is a Hahn sum of `Σ (−a)ᵏ ω⁻ᵏ`**, for every nonzero dyadic
`a`. -/
theorem isHahnSum_negGrid {a : Dyadic} (ha : a ≠ 0) :
    IsHahnSum (monoTerm (negCoeff a))
      (((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹) := by
  intro n
  rw [show partialSum (monoTerm (negCoeff a)) n = monoS (negCoeff a) n from rfl,
    mk_sub_monoS_neg ha, mk_monoTerm (negCoeff_ne_zero ha)]

/-! ### The census lower bounds -/

/-- `birthday ((1 + a·ω⁻¹)⁻¹) ≥ ω²` for every nonzero dyadic `a`. -/
theorem omega_sq_le_birthday_inv_one_add_dyadic {a : Dyadic} (ha : a ≠ 0) :
    Ω * Ω ≤ (((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹).birthday :=
  mono_omega_sq_le_birthday_of_isHahnSum (negCoeff_ne_zero ha) (isHahnSum_negGrid ha)

end Surreal

end
