/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.TubeCensus
import Infinity.InverseBirthday

/-!
# The close: `hahnSum (Σ ω⁻ᵏ) = ω/(ω−1)`

The repo's oldest conjecture, settled. The tube theorem of `Infinity.TubeCensus` says
the only surreal born before day `ω·(B+2)` at distance strictly finer than class
`ω^{−(B+1)}` from `v₀ = ω/(ω−1)` is the partial sum `S_{B+2}`. Every Hahn sum of the
geometric series lies in the **micro-halo** of `v₀` — strictly finer than every scale
(`IsHahnSum.mk_sub_le` plus strict domination) — while every partial sum sits at class
exactly `ω^{−m}`. Hence:

* `omega_sq_le_birthday_of_isHahnSum_geometric` — **the geometric halo is empty below
  day `ω²`**: every Hahn sum of `Σ ω⁻ᵏ` is born at or after day `ω·ω` (natural product;
  equals the ordinal `ω²`). The window `[ω·2, ω²)` left open by
  `Infinity.GeometricBirthday` is closed in one stroke.
* `birthday_geomSum_limit_eq` — **`birthday (ω/(ω−1)) = ω·ω` exactly** (upper bound from
  the Conway-inverse device of `Infinity.InverseBirthday`).
* `hahnSum_geometric_eq` — **THE CANONICAL GEOMETRIC SUM**:
  `hahnSum (Σ_{k<ω} ω⁻ᵏ) = ω/(ω−1)`, via the closing iff of
  `Infinity.InverseBirthday`. The first computed value of the canonical transfinite
  summation operator on a series with no exact finite form.
* `birthday_hahnSum_geometric_eq` — its birthday is exactly `ω·ω`.
* `birthday_geomS_eq` — the partial sums are priced exactly:
  `birthday S_{m+3} = ω·(m+2)` (and `birthday S₂ = ω`).
-/

open ArchimedeanClass IGame Set

noncomputable section

namespace Surreal

local notation "ε₀" => eps0
local notation "Ω" => NatOrdinal.of Ordinal.omega0
local notation "V₀" => (1 - eps0)⁻¹

/-- Every Hahn sum of the geometric series lies strictly finer than every scale from
`ω/(ω−1)`: the micro-halo membership, in strict form at every level. -/
theorem mk_pow_lt_mk_sub_of_isHahnSum_geometric {w : Surreal.{0}}
    (hw : IsHahnSum (fun k ↦ ε₀ ^ k) w) (n : ℕ) :
    ArchimedeanClass.mk (ε₀ ^ n) < ArchimedeanClass.mk (w - V₀) :=
  (geometric_strict_dominating n).trans_le
    (IsHahnSum.mk_sub_le hw isHahnSum_geometric (n + 1))

/-- **The geometric halo is empty below day `ω²`**: every Hahn sum of `Σ ω⁻ᵏ` is born
at or after day `ω·ω`. If one were born earlier, `NatOrdinal.lt_mul_iff` would trap its
birthday below some `ω·(p+q+2)`, the tube theorem would force it to be the partial sum
`S_{p+q+2}` — but a Hahn sum is strictly finer than the scale `ω^{−(p+q+2)}` at which
that partial sum deviates from `ω/(ω−1)`. -/
theorem omega_sq_le_birthday_of_isHahnSum_geometric {w : Surreal.{0}}
    (hw : IsHahnSum (fun k ↦ ε₀ ^ k) w) :
    Ω * Ω ≤ w.birthday := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨a', ha', b', hb', hle⟩ := NatOrdinal.lt_mul_iff.1 hcon
  obtain ⟨p, rfl⟩ := NatOrdinal.lt_omega0.1 ha'
  obtain ⟨q, rfl⟩ := NatOrdinal.lt_omega0.1 hb'
  have h1 : w.birthday ≤ Ω * (((p + q) : ℕ) : NatOrdinal) := by
    have h2 : w.birthday ≤ (p : NatOrdinal) * Ω + Ω * (q : NatOrdinal) :=
      le_trans (le_add_of_nonneg_right bot_le) hle
    refine h2.trans (le_of_eq ?_)
    push_cast
    ring
  have h0 : (0 : NatOrdinal) < Ω := by
    have h := nat_lt_omega' 0
    rwa [Nat.cast_zero] at h
  have h3 : w.birthday < Ω * ((((p + q) + 2) : ℕ) : NatOrdinal) := by
    refine h1.trans_lt (mul_lt_mul_of_pos_left ?_ h0)
    exact_mod_cast (by omega : p + q < p + q + 2)
  have heq := eq_geomS_of_birthday_lt_of_mk_lt (p + q)
    (mk_pow_lt_mk_sub_of_isHahnSum_geometric hw (p + q + 1)) h3
  have hfin := mk_pow_lt_mk_sub_of_isHahnSum_geometric hw (p + q + 2)
  rw [heq, mk_geomS_sub_v0] at hfin
  exact lt_irrefl _ hfin

/-- **`birthday (ω/(ω−1)) = ω·ω` exactly**: the Conway-inverse upper bound of
`Infinity.InverseBirthday` meets the halo emptiness lower bound. -/
theorem birthday_geomSum_limit_eq :
    (((1 : Surreal.{0}) - ε₀)⁻¹).birthday = Ω * Ω :=
  le_antisymm birthday_geomSum_limit_le_omega_mul_omega
    (omega_sq_le_birthday_of_isHahnSum_geometric isHahnSum_geometric)

/-- **THE CANONICAL GEOMETRIC SUM**: `hahnSum (Σ_{k<ω} ω⁻ᵏ) = ω/(ω−1)`. The
birthday-minimal Hahn sum of the geometric series is exactly `(1 − ω⁻¹)⁻¹` — the first
computed value of the canonical transfinite summation operator on a series whose sum has
no finite closed form at any stage. -/
theorem hahnSum_geometric_eq :
    hahnSum geometric_strict_dominating = ((1 : Surreal.{0}) - ε₀)⁻¹ := by
  rw [hahnSum_geometric_eq_iff_birthday_le, birthday_geomSum_limit_eq]
  exact omega_sq_le_birthday_of_isHahnSum_geometric
    (isHahnSum_hahnSum geometric_strict_dominating)

/-- The `ω/(ω−1)` form of the canonical geometric sum. -/
theorem hahnSum_geometric_eq_div :
    hahnSum geometric_strict_dominating
      = ω^ (1 : Surreal.{0}) / (ω^ (1 : Surreal) - 1) := by
  rw [hahnSum_geometric_eq, geomSum_limit_eq]

/-- The canonical geometric sum is born exactly on day `ω·ω`. -/
theorem birthday_hahnSum_geometric_eq :
    (hahnSum geometric_strict_dominating).birthday = Ω * Ω := by
  rw [hahnSum_geometric_eq]
  exact birthday_geomSum_limit_eq

/-- **Identification at the minimum**: any Hahn sum of the geometric series born by day
`ω·ω` *is* `ω/(ω−1)`. Every other Hahn sum is born strictly later. -/
theorem isHahnSum_geometric_eq_of_birthday_le {w : Surreal.{0}}
    (hw : IsHahnSum (fun k ↦ ε₀ ^ k) w) (hb : w.birthday ≤ Ω * Ω) :
    w = ((1 : Surreal.{0}) - ε₀)⁻¹ := by
  have h1 : w.birthday ≤ (hahnSum geometric_strict_dominating).birthday := by
    rw [birthday_hahnSum_geometric_eq]
    exact hb
  rw [← hahnSum_eq_of_isHahnSum_of_birthday_le geometric_strict_dominating hw h1,
    hahnSum_geometric_eq]

/-! ### Exact partial-sum birthdays -/

/-- `S₂ = 1 + ω⁻¹` is born exactly on day `ω`. -/
theorem birthday_geomS_two : (geomS 2).birthday = Ω := by
  have hval : geomS 2 = ((1 : Dyadic) : Surreal) + ((1 : Dyadic) : Surreal)
      * ω^ (-1 : Surreal) := by
    rw [geomS_succ, geomS_one, dyadic_cast_one, one_mul, pow_one, wpow_neg_one_eq_eps0]
  rw [hval, birthday_grid_dyadic_eq 1 one_ne_zero]
  have h : ((Dyadic.hgt 1 - 1 : ℕ) : NatOrdinal) = 0 := by
    rw [Dyadic.hgt_one]
    exact_mod_cast rfl
  rw [h, add_zero]

/-- **The partial sums are priced exactly**: `birthday (S_{m+3}) = ω·(m+2)`. Together
with `birthday_geomS_two`, `birthday (partialSum n) = ω·(n−1)` for every `n ≥ 2`. -/
theorem birthday_geomS_eq (m : ℕ) :
    (geomS (m + 3)).birthday = Ω * (((m + 2) : ℕ) : NatOrdinal) := by
  refine le_antisymm (birthday_geomS_le (m + 1)) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hmk : ArchimedeanClass.mk (ε₀ ^ (m + 1))
      < ArchimedeanClass.mk (geomS (m + 3) - V₀) := by
    rw [mk_geomS_sub_v0]
    exact (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos (m + 1)).trans
      (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos (m + 2))
  have heq := eq_geomS_of_birthday_lt_of_mk_lt m hmk hcon
  have hne : geomS (m + 3) ≠ geomS (m + 2) := by
    rw [geomS_succ]
    intro h
    have h2 : (ε₀ : Surreal.{0}) ^ (m + 2) = 0 := by linarith [h]
    exact (eps0_pow_pos (m + 2)).ne' h2
  exact hne heq

end Surreal

end
