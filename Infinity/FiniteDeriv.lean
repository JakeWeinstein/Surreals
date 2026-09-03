/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.DerivRules
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Derivatives at every finite surreal point

`Infinity.Derivative` differentiates polynomials at *real* anchor points. Here we extend to
arbitrary **finite surreal** anchor points `x₀` — points like `3 + 1/ω` that are not real but
are infinitesimally close to a real. The exact (finite!) Taylor expansion
`P (x₀ + ε) = Σᵢ (taylor x₀ P).coeff i * εⁱ` controls every term at once, and the standard
part of the difference quotient is the classical derivative evaluated at `stdPart x₀`:

* `Surreal.isFinite_eval₂` / `Surreal.stdPart_eval₂`: polynomial evaluation preserves
  finiteness and **commutes with the standard part** — `st (p(x)) = p (st x)`.
* `Surreal.stdPart_diffQuot_finite`: for any nonzero infinitesimal `ε` and any finite `x₀`,
  `st ((p (x₀ + ε) - p x₀) / ε) = p' (st x₀)`.

Conceptually: the surreal difference quotient sees only the *shadow* `st x₀` — differentiation
on `No` factors through the standard-part projection, so the derivative genuinely lives on the
real line even when the computation happens infinitesimally far from it.
-/

open Polynomial ArchimedeanClass Finset

noncomputable section

namespace Surreal

/-- Combined induction: evaluating a real polynomial at a finite surreal gives a finite
surreal whose standard part is the evaluation at the standard part. -/
theorem isFinite_eval₂_and_stdPart_eval₂ (p : ℝ[X]) {x : Surreal} (hx : IsFinite x) :
    IsFinite (p.eval₂ realHom x) ∧ stdPart (p.eval₂ realHom x) = p.eval (stdPart x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, eval_add]
    exact ⟨hp.1.add hq.1, by rw [stdPart_add hp.1 hq.1, hp.2, hq.2]⟩
  | monomial n a =>
    rw [eval₂_monomial, eval_monomial, realHom_apply]
    exact ⟨(isFinite_realCast a).mul (hx.pow n),
      by rw [stdPart_mul (isFinite_realCast a) (hx.pow n), stdPart_realCast, stdPart_pow hx]⟩

/-- Polynomial evaluation at a finite surreal is finite. -/
theorem isFinite_eval₂ (p : ℝ[X]) {x : Surreal} (hx : IsFinite x) :
    IsFinite (p.eval₂ realHom x) :=
  (isFinite_eval₂_and_stdPart_eval₂ p hx).1

/-- **Evaluation commutes with the standard part**: `st (p(x)) = p (st x)` for finite `x`. -/
theorem stdPart_eval₂ (p : ℝ[X]) {x : Surreal} (hx : IsFinite x) :
    stdPart (p.eval₂ realHom x) = p.eval (stdPart x) :=
  (isFinite_eval₂_and_stdPart_eval₂ p hx).2

private theorem hasseDeriv_map (p : ℝ[X]) (i : ℕ) :
    hasseDeriv i (p.map (realHom : ℝ →+* Surreal)) = (hasseDeriv i p).map realHom := by
  ext n
  simp [hasseDeriv_coeff, coeff_map]

/-- **The derivative at every finite surreal point.** For a real polynomial `p`, a finite
surreal `x₀`, and any nonzero infinitesimal `ε`, the difference quotient is finite and its
standard part is the classical derivative at the standard part of `x₀`. -/
theorem isFinite_diffQuot_finite_and_stdPart (p : ℝ[X]) {x₀ ε : Surreal}
    (hx : IsFinite x₀) (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    IsFinite ((p.eval₂ realHom (x₀ + ε) - p.eval₂ realHom x₀) / ε) ∧
      stdPart ((p.eval₂ realHom (x₀ + ε) - p.eval₂ realHom x₀) / ε) =
        p.derivative.eval (stdPart x₀) := by
  obtain hd | hd := Nat.eq_zero_or_pos p.natDegree
  -- Degenerate case: a constant polynomial.
  · obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.1 hd
    simp
  -- Main case: exact Taylor expansion at `x₀`.
  · set P : Surreal[X] := p.map (realHom : ℝ →+* Surreal) with hP
    set d := p.natDegree with hd'
    set q : ℕ → Surreal := fun i ↦ (taylor x₀ P).coeff i with hq
    -- Each Taylor coefficient is finite (it is a Hasse derivative of `p` evaluated at `x₀`).
    have hqfin : ∀ i, IsFinite (q i) := by
      intro i
      rw [hq]
      dsimp only
      rw [taylor_coeff, hP, hasseDeriv_map, eval_map]
      exact isFinite_eval₂ _ hx
    -- The linear coefficient has the right standard part.
    have hqst : stdPart (q 1) = p.derivative.eval (stdPart x₀) := by
      rw [hq]
      dsimp only
      rw [taylor_coeff_one, hP, derivative_map, eval_map]
      exact stdPart_eval₂ _ hx
    -- Exact expansion of the evaluation.
    have hval : P.eval (x₀ + ε) = ∑ i ∈ range (d + 1), q i * ε ^ i := by
      have h1 : P.eval (x₀ + ε) = (taylor x₀ P).eval ε := by rw [taylor_eval, add_comm]
      rw [h1, eval_eq_sum_range' (n := d + 1)
        (lt_of_le_of_lt (natDegree_taylor P x₀ ▸ natDegree_map_le) (Nat.lt_succ_self d)) ε]
    -- The difference quotient in closed form.
    have hquot : (P.eval (x₀ + ε) - P.eval x₀) / ε = ∑ i ∈ range d, q (i + 1) * ε ^ i := by
      have h0 : P.eval x₀ = q 0 := (taylor_coeff_zero x₀ P).symm
      rw [hval, sum_range_succ' _ d, pow_zero, mul_one, h0, add_sub_cancel_right,
        div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [pow_succ, ← mul_assoc, mul_assoc _ ε ε⁻¹, mul_inv_cancel₀ hε0, mul_one]
    -- Each summand is finite.
    have hterm : ∀ i ∈ range d, IsFinite (q (i + 1) * ε ^ i) :=
      fun i _ ↦ (hqfin _).mul (hε.isFinite.pow i)
    have hPe : ∀ y : Surreal, P.eval y = p.eval₂ realHom y := fun y ↦ by rw [hP, eval_map]
    rw [← hPe, ← hPe, hquot]
    refine ⟨isFinite_sum hterm, ?_⟩
    -- Standard parts: only the `i = 0` term survives.
    rw [stdPart_sum hterm]
    have hst : ∀ i ∈ range d, stdPart (q (i + 1) * ε ^ i) =
        stdPart (q (i + 1)) * (0 : ℝ) ^ i := by
      intro i _
      rw [stdPart_mul (hqfin _) (hε.isFinite.pow i), stdPart_pow hε.isFinite,
        hε.stdPart_eq_zero]
    rw [Finset.sum_congr rfl hst, Finset.sum_eq_single_of_mem 0 (mem_range.2 hd)
      (fun i _ hi ↦ by rw [zero_pow hi, mul_zero]), pow_zero, mul_one, hqst]

/-- **Differentiation on `No` factors through the standard part**: the difference quotient of
a real polynomial at any finite surreal anchor, with any nonzero infinitesimal increment,
has standard part `p' (st x₀)`. -/
theorem stdPart_diffQuot_finite (p : ℝ[X]) {x₀ ε : Surreal}
    (hx : IsFinite x₀) (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    stdPart ((p.eval₂ realHom (x₀ + ε) - p.eval₂ realHom x₀) / ε) =
      p.derivative.eval (stdPart x₀) :=
  (isFinite_diffQuot_finite_and_stdPart p hx hε hε0).2

end Surreal
