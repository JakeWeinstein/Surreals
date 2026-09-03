/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.StandardPart
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.GeomSum

/-!
# Differentiation via surreal infinitesimals

The signature theorem of infinitesimal calculus, on the surreal numbers: for a real polynomial
`p` and a real point `x`, the difference quotient `(p (x + ε) - p x) / ε` taken with an *actual
nonzero infinitesimal* `ε : Surreal` is a finite surreal whose standard part is exactly the
derivative `p' x`.

This is the Leibniz picture made literal, in the style of nonstandard analysis but carried out
inside Conway's surreal numbers: the increment `ε` is an honest element of the field (for
instance `(ω^ 1)⁻¹ = 1/ω`), the quotient is computed by ordinary field algebra, and rounding
away the infinitesimal error via `ArchimedeanClass.stdPart` recovers the classical derivative.

* `Surreal.isFinite_sum`, `Surreal.stdPart_sum`, `Surreal.stdPart_pow`: finite-sum and power
  API for the standard part.
* `Surreal.stdPart_diffQuot`: the main theorem.
-/

open Polynomial ArchimedeanClass Finset

noncomputable section

namespace Surreal

/-- The canonical embedding `ℝ →+* Surreal`, as a plain ring hom. -/
abbrev realHom : ℝ →+* Surreal :=
  Real.toSurrealRingHom.toRingHom

theorem realHom_apply (r : ℝ) : realHom r = (r : Surreal) := rfl

/-! ### Sums and powers of finite surreals -/

theorem isFinite_sum {ι : Type*} {s : Finset ι} {g : ι → Surreal}
    (h : ∀ i ∈ s, IsFinite (g i)) : IsFinite (∑ i ∈ s, g i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (h a (Finset.mem_cons_self ..)).add (ih fun i hi ↦ h i (Finset.mem_cons_of_mem hi))

theorem stdPart_sum {ι : Type*} {s : Finset ι} {g : ι → Surreal}
    (h : ∀ i ∈ s, IsFinite (g i)) :
    stdPart (∑ i ∈ s, g i) = ∑ i ∈ s, stdPart (g i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons,
      stdPart_add (h a (Finset.mem_cons_self ..))
        (isFinite_sum fun i hi ↦ h i (Finset.mem_cons_of_mem hi)),
      ih fun i hi ↦ h i (Finset.mem_cons_of_mem hi)]

theorem stdPart_pow {x : Surreal} (hx : IsFinite x) (n : ℕ) :
    stdPart (x ^ n) = stdPart x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, stdPart_mul (hx.pow n) hx, ih]

/-! ### The derivative of a polynomial -/

/-- **Differentiation via infinitesimals.** For a real polynomial `p`, a real point `x`, and any
nonzero infinitesimal surreal `ε`, the difference quotient `(p (x + ε) - p x) / ε` (computed in
the surreal field, with `p` acting through the canonical embedding `ℝ ↪ Surreal`) is finite,
and its standard part is the classical derivative `p' x`.

The two conjuncts are proved simultaneously by induction on `p`. -/
theorem isFinite_diffQuot_and_stdPart_diffQuot (p : ℝ[X]) (x : ℝ) {ε : Surreal}
    (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    IsFinite ((p.eval₂ realHom (x + ε) - p.eval₂ realHom x) / ε) ∧
      stdPart ((p.eval₂ realHom (x + ε) - p.eval₂ realHom x) / ε) = p.derivative.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hquot : ((p + q).eval₂ realHom (x + ε) - (p + q).eval₂ realHom x) / ε =
        (p.eval₂ realHom (x + ε) - p.eval₂ realHom x) / ε +
        (q.eval₂ realHom (x + ε) - q.eval₂ realHom x) / ε := by
      rw [eval₂_add, eval₂_add, add_sub_add_comm, add_div]
    rw [hquot]
    refine ⟨hp.1.add hq.1, ?_⟩
    rw [stdPart_add hp.1 hq.1, hp.2, hq.2, derivative_add, eval_add]
  | monomial n a =>
    -- The subtraction-free geometric sum identity turns the difference quotient into
    -- `↑a * ∑ i < n, (↑x + ε)^i * ↑x^(n-1-i)`.
    set S : Surreal := ∑ i ∈ range n, ((x : Surreal) + ε) ^ i * (x : Surreal) ^ (n - 1 - i)
      with hS
    have hkey : ((x : Surreal) + ε) ^ n - (x : Surreal) ^ n = S * ε := by
      have hg := geom_sum₂_mul_add ε (x : Surreal) n
      rw [add_comm ε (x : Surreal)] at hg
      rw [sub_eq_iff_eq_add, hS]
      exact hg.symm
    have hquot : ((monomial n a).eval₂ realHom (x + ε) - (monomial n a).eval₂ realHom x) / ε =
        (a : Surreal) * S := by
      rw [eval₂_monomial, eval₂_monomial, realHom_apply, ← mul_sub, mul_div_assoc, hkey,
        mul_div_cancel_right₀ _ hε0]
    -- Finiteness of each term of `S`.
    have hterm : ∀ i ∈ range n,
        IsFinite (((x : Surreal) + ε) ^ i * (x : Surreal) ^ (n - 1 - i)) :=
      fun i _ ↦ (((isFinite_realCast x).add hε.isFinite).pow i).mul
        ((isFinite_realCast x).pow (n - 1 - i))
    have hSfin : IsFinite S := isFinite_sum hterm
    refine hquot ▸ ⟨(isFinite_realCast a).mul hSfin, ?_⟩
    -- Standard part of each term: `x ^ (n - 1)`.
    have hst : ∀ i ∈ range n,
        stdPart (((x : Surreal) + ε) ^ i * (x : Surreal) ^ (n - 1 - i)) = x ^ (n - 1) := by
      intro i hi
      rw [stdPart_mul ((((isFinite_realCast x).add hε.isFinite)).pow i)
          ((isFinite_realCast x).pow (n - 1 - i)),
        stdPart_pow ((isFinite_realCast x).add hε.isFinite),
        stdPart_pow (isFinite_realCast x),
        stdPart_add_eq_left hε, stdPart_realCast, ← pow_add,
        Nat.add_sub_cancel' (Nat.le_sub_one_of_lt (mem_range.1 hi))]
    rw [stdPart_mul (isFinite_realCast a) hSfin, stdPart_realCast, stdPart_sum hterm,
      Finset.sum_congr rfl hst, Finset.sum_const, card_range, nsmul_eq_mul,
      derivative_monomial, eval_monomial]
    ring

/-- **The derivative via infinitesimals**: the standard part of a polynomial's infinitesimal
difference quotient is its derivative. -/
theorem stdPart_diffQuot (p : ℝ[X]) (x : ℝ) {ε : Surreal}
    (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    stdPart ((p.eval₂ realHom (x + ε) - p.eval₂ realHom x) / ε) = p.derivative.eval x :=
  (isFinite_diffQuot_and_stdPart_diffQuot p x hε hε0).2

/-- The infinitesimal difference quotient of a polynomial is a finite surreal. -/
theorem isFinite_diffQuot (p : ℝ[X]) (x : ℝ) {ε : Surreal}
    (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    IsFinite ((p.eval₂ realHom (x + ε) - p.eval₂ realHom x) / ε) :=
  (isFinite_diffQuot_and_stdPart_diffQuot p x hε hε0).1

/-- The derivative of `x ^ 2` at `3`, computed with the literal infinitesimal `1/ω`:
`st (((3 + ω⁻¹)² - 9) / ω⁻¹) = 6`. -/
example :
    stdPart ((((3 : Surreal) + (ω^ (1 : Surreal))⁻¹) ^ 2 - 9) / (ω^ (1 : Surreal))⁻¹) = 6 := by
  have h := stdPart_diffQuot (X ^ 2) 3 (infinitesimal_inv_wpow one_pos)
    (inv_ne_zero (wpow_pos (1 : Surreal)).ne')
  norm_num at h
  simpa [div_eq_mul_inv] using h

end Surreal
