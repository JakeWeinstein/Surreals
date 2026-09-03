/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.ExpLogGrid
import Infinity.ExpNegLog

/-!
# The generic negative domination half:
`(1+x)⁻¹` is a Hahn sum of the exponential series at `−σ`, for every log `σ`

`Infinity.ExpNegLog` proved the domination half of the inverse exponential value at
the single anchor `ω⁻¹` and the single canonical logarithm `logOmega`;
`Infinity.ExpLogGrid` made the *positive* half fully generic in both the anchor and
the Hahn sum. This file closes the square — the fully generic **negative** half:

* `isHahnSum_expSeries_inv_one_add_of_isHahnSum_log` : for every nonzero
  infinitesimal `x` and *every* Hahn sum `σ` of the logarithm series at `x`, the
  value `(1+x)⁻¹` satisfies all the domination equations of the exponential series
  at `−σ` — every residual `(1+x)⁻¹ − Σ_{k<n} (−σ)ᵏ/k!` has Archimedean class at
  least that of `(−σ)ⁿ/n!` (= that of `xⁿ`).

The algebraic half is `ExpNegLog`'s banked inverse polynomial identity
`X_pow_dvd_one_add_mul_expPoly_comp_neg_logPoly` (`Xⁿ ∣ (1+X)·E_n(−L_n) − 1`),
which is anchor-free; the domination transport runs exactly as in the templates:
the composition defect is `Xⁿ`-divisible with the class-`0` cofactor `(1+x)⁻¹`, and
the substitution error `E_n(−σ) − E_n(−L_n(x))` peels through the geometric
cofactors (`Commute.geom_sum₂_mul`, all factors finite) against the stage-`n` Hahn
residual of `σ`.

Side lemmas banked generically (anchor-free versions of the `NegGrid` dyadic ones;
`one_add_infinitesimal_pos` already lives in `ExpFin`):
`one_add_infinitesimal_ne_zero`, `mk_one_add_infinitesimal`,
`mk_inv_one_add_infinitesimal`.
-/

open ArchimedeanClass Filter Finset Polynomial

noncomputable section

namespace Surreal

/-! ### The class of `1 + x` and its inverse, generic in the infinitesimal -/

theorem one_add_infinitesimal_ne_zero {x : Surreal} (hx : Infinitesimal x) :
    (1 : Surreal) + x ≠ 0 :=
  (one_add_infinitesimal_pos hx).ne'

theorem mk_one_add_infinitesimal {x : Surreal} (hx : Infinitesimal x) :
    ArchimedeanClass.mk (1 + x) = 0 := by
  have h : ArchimedeanClass.mk (1 : Surreal) < ArchimedeanClass.mk x := by
    rw [ArchimedeanClass.mk_one]
    exact hx
  rw [ArchimedeanClass.mk_add_eq_mk_left h, ArchimedeanClass.mk_one]

theorem mk_inv_one_add_infinitesimal {x : Surreal} (hx : Infinitesimal x) :
    ArchimedeanClass.mk ((1 + x)⁻¹) = 0 := by
  rw [ArchimedeanClass.mk_inv, mk_one_add_infinitesimal hx, neg_zero]

/-! ### Local domination-calculus helpers -/

private theorem mk_pow_congr' {a b : Surreal}
    (h : ArchimedeanClass.mk a = ArchimedeanClass.mk b) (n : ℕ) :
    ArchimedeanClass.mk (a ^ n) = ArchimedeanClass.mk (b ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, ih, h]

/-- Sums of termwise-dominated surreals are dominated. -/
private theorem le_mk_sum' {c : ArchimedeanClass Surreal} {s : Finset ℕ} {f : ℕ → Surreal}
    (h : ∀ i ∈ s, c ≤ ArchimedeanClass.mk (f i)) :
    c ≤ ArchimedeanClass.mk (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, ArchimedeanClass.mk_zero]
    exact le_top
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact le_trans (le_min (h a (Finset.mem_cons_self ..))
      (ih fun i hi ↦ h i (Finset.mem_cons_of_mem hi))) (ArchimedeanClass.min_le_mk_add ..)

/-! ### The generic negative domination half -/

/-- **The generic negative domination half**: for every nonzero infinitesimal `x`
and *every* Hahn sum `σ` of the logarithm series at `x`, the value `(1+x)⁻¹`
satisfies all the domination equations of the exponential series at `−σ`. The
residual at stage `n` combines the composition defect of the banked inverse
polynomial identity (`Xⁿ`-divisible, with the class-`0` cofactor `(1+x)⁻¹`) with the
substitution error `E_n(−σ) − E_n(−L_n(x))` (a multiple of the stage-`n` Hahn
residual of `σ`, via the geometric cofactors), both of class at least that of
`xⁿ`. -/
theorem isHahnSum_expSeries_inv_one_add_of_isHahnSum_log {x σ : Surreal}
    (hx : Infinitesimal x) (hx0 : x ≠ 0)
    (hσ : IsHahnSum (logSeriesAt x) σ) :
    IsHahnSum (fun k ↦ (-σ) ^ k / ((k.factorial : ℕ) : Surreal)) ((1 + x)⁻¹) := by
  intro n
  -- the polynomial factorization of the composition defect
  obtain ⟨P, hP⟩ := X_pow_dvd_one_add_mul_expPoly_comp_neg_logPoly n
  -- Term 1: `E_n(−Lval) − (1+x)⁻¹ = (1+x)⁻¹·xⁿ·P(x)`
  have hterm1 : (expPoly n).eval₂ realHom (-(partialSum (logSeriesAt x) n)) - (1 + x)⁻¹ =
      (1 + x)⁻¹ * (x ^ n * P.eval₂ realHom x) := by
    have hev := congrArg (Polynomial.eval₂ realHom x) hP
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_add,
      Polynomial.eval₂_one, Polynomial.eval₂_X, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_comp, Polynomial.eval₂_neg] at hev
    rw [← partialSum_logSeriesAt_eq] at hev
    calc (expPoly n).eval₂ realHom (-(partialSum (logSeriesAt x) n)) - (1 + x)⁻¹
        = (1 + x)⁻¹ * ((1 + x) *
            (expPoly n).eval₂ realHom (-(partialSum (logSeriesAt x) n)) - 1) := by
          rw [mul_sub, mul_one, ← mul_assoc,
            inv_mul_cancel₀ (one_add_infinitesimal_ne_zero hx), one_mul]
      _ = (1 + x)⁻¹ * (x ^ n * P.eval₂ realHom x) := by rw [hev]
  -- the composition defect is below scale `xⁿ`
  have hmk1 : ArchimedeanClass.mk (x ^ n) ≤
      ArchimedeanClass.mk ((expPoly n).eval₂ realHom (-(partialSum (logSeriesAt x) n)) -
        (1 + x)⁻¹) := by
    rw [hterm1, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
      mk_inv_one_add_infinitesimal hx, zero_add]
    have hPfin : (0 : ArchimedeanClass Surreal) ≤
        ArchimedeanClass.mk (P.eval₂ realHom x) :=
      isFinite_eval₂ _ hx.isFinite
    calc ArchimedeanClass.mk (x ^ n)
        = ArchimedeanClass.mk (x ^ n) + 0 := (add_zero _).symm
      _ ≤ _ := add_le_add le_rfl hPfin
  -- finiteness of the two substitution points
  have hLfin : IsFinite (-(partialSum (logSeriesAt x) n)) := by
    refine IsFinite.neg ?_
    rw [partialSum_logSeriesAt_eq]
    exact isFinite_eval₂ _ hx.isFinite
  have hσfin : IsFinite (-σ) :=
    (infinitesimal_of_isHahnSum_log hx hx0 hσ).isFinite.neg
  -- Term 2: `E_n(−σ) − E_n(−Lval)` is dominated by the stage-`n` Hahn residual
  have hterm2 : ArchimedeanClass.mk (x ^ n) ≤
      ArchimedeanClass.mk ((expPoly n).eval₂ realHom (-σ) -
        (expPoly n).eval₂ realHom (-(partialSum (logSeriesAt x) n))) := by
    rw [← partialSum_expSeries_eq_eval, ← partialSum_expSeries_eq_eval,
      partialSum, partialSum, ← Finset.sum_sub_distrib]
    refine le_mk_sum' fun k _ ↦ ?_
    have hsplit : (-σ) ^ k / ((k.factorial : ℕ) : Surreal) -
        (-(partialSum (logSeriesAt x) n)) ^ k / ((k.factorial : ℕ) : Surreal) =
        (((k.factorial : ℕ) : Surreal))⁻¹ *
          ((∑ i ∈ Finset.range k,
            (-σ) ^ i * (-(partialSum (logSeriesAt x) n)) ^ (k - 1 - i)) *
            (-σ - -(partialSum (logSeriesAt x) n))) := by
      rw [(Commute.all (-σ) (-(partialSum (logSeriesAt x) n))).geom_sum₂_mul k]
      ring
    rw [hsplit, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul]
    have hinv0 : ArchimedeanClass.mk ((((k.factorial : ℕ) : Surreal))⁻¹) = 0 := by
      rw [ArchimedeanClass.mk_inv, mk_factorial, neg_zero]
    have hcof : (0 : ArchimedeanClass Surreal) ≤ ArchimedeanClass.mk
        (∑ i ∈ Finset.range k,
          (-σ) ^ i * (-(partialSum (logSeriesAt x) n)) ^ (k - 1 - i)) := by
      refine isFinite_sum fun i _ ↦ ?_
      exact (hσfin.pow i).mul (hLfin.pow (k - 1 - i))
    have hres : ArchimedeanClass.mk (x ^ n) ≤
        ArchimedeanClass.mk (-σ - -(partialSum (logSeriesAt x) n)) := by
      have hneg : -σ - -(partialSum (logSeriesAt x) n) =
          -(σ - partialSum (logSeriesAt x) n) := by ring
      rw [hneg, ArchimedeanClass.mk_neg]
      refine le_trans ?_ (hσ n)
      rw [mk_logSeriesAt]
      exact (mk_pow_lt_mk_pow_succ' hx hx0 n).le
    calc ArchimedeanClass.mk (x ^ n)
        = 0 + (0 + ArchimedeanClass.mk (x ^ n)) := by
          rw [zero_add, zero_add]
      _ ≤ ArchimedeanClass.mk ((((k.factorial : ℕ) : Surreal))⁻¹) +
          (ArchimedeanClass.mk (∑ i ∈ Finset.range k,
              (-σ) ^ i * (-(partialSum (logSeriesAt x) n)) ^ (k - 1 - i)) +
            ArchimedeanClass.mk (-σ - -(partialSum (logSeriesAt x) n))) := by
          rw [hinv0]
          exact add_le_add le_rfl (add_le_add hcof hres)
  -- assemble the residual
  have hsplit : (1 + x)⁻¹ -
      partialSum (fun k ↦ (-σ) ^ k / ((k.factorial : ℕ) : Surreal)) n =
      -((expPoly n).eval₂ realHom (-(partialSum (logSeriesAt x) n)) - (1 + x)⁻¹) +
      -((expPoly n).eval₂ realHom (-σ) -
        (expPoly n).eval₂ realHom (-(partialSum (logSeriesAt x) n))) := by
    rw [partialSum_expSeries_eq_eval]
    ring
  have htarget : ArchimedeanClass.mk
      ((-σ) ^ n / ((n.factorial : ℕ) : Surreal)) =
      ArchimedeanClass.mk (x ^ n) := by
    rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero]
    have hmkσ : ArchimedeanClass.mk (-σ) = ArchimedeanClass.mk x := by
      rw [ArchimedeanClass.mk_neg]
      exact mk_of_isHahnSum_log hx hx0 hσ
    exact mk_pow_congr' hmkσ n
  show ArchimedeanClass.mk ((-σ) ^ n / ((n.factorial : ℕ) : Surreal)) ≤ _
  rw [htarget, hsplit]
  refine le_trans (le_min ?_ ?_) (ArchimedeanClass.min_le_mk_add ..)
  · rwa [ArchimedeanClass.mk_neg]
  · rwa [ArchimedeanClass.mk_neg]

end Surreal

end
