/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.IntegralS
import Infinity.KernelSeparation

/-!
# Integration beyond polynomials: the Laurent class

`Infinity.IntegralS` resolved FTC integration on **No** at polynomial scope. This file
extends the resolved frontier to the first integrand class with poles: **Laurent
functions** `x ↦ Q(x) + A(x⁻¹)` with surreal-coefficient polynomials `Q, A` — finite sums
of monomials `xᵏ` with `k ∈ ℤ`. The class is rigid across galaxies (a Laurent function is
determined globally by finitely many coefficients), which is exactly what the Galaxy and
Fractal Kernel obstruction theorems demand of any integrand class admitting a
well-behaved integral.

* `HasDerivS.comp_inv` — **the chain rule through inversion**: if `f` has surreal-point
  derivative `d` at `x⁻¹`, then `f (·⁻¹)` has derivative `-d·x⁻²` at every
  non-infinitesimal `x`. The domain restriction is honest and sharp in kind: at
  infinitesimal `x` the increment can reach the pole at `0`, where no `O(ε²)` bound can
  hold.
* `hasDerivS_laurentFun` — every Laurent function is differentiable at every
  non-infinitesimal surreal point (finite non-infinitesimal *and* infinite alike), with
  the expected in-class derivative. Polynomial-part differentiation continues to hold at
  every point of **No**.
* Integrand data: the pair `(P, R)` denotes `x ↦ P(x) + x⁻²·R(x⁻¹)` — precisely the
  Laurent functions **with no `x⁻¹` term**. The derivative of `A(x⁻¹)` is
  `x⁻²·(-A')(x⁻¹)`, so differentiation maps the Laurent class *onto* this data class:
  the `x⁻¹` integrand — the logarithm's derivative — is structurally excluded, and
  nothing else is.
* `antiderivL` / `integralL` with **FTC I** (`hasDerivS_antiderivL`) at every
  non-infinitesimal point, **FTC II** (`integralL_laurentDeriv`), **uniqueness**
  (`integralL_unique`: any operator satisfying FTC II on Laurent data is this one),
  linearity, interval additivity, and compatibility with the polynomial integral
  (`integralL_poly`).
* `integralL_inv_sq_one_wpow` : **`∫₁^ω x⁻² dx = 1 − ω⁻¹`** — the first verified surreal
  integral of a function with a pole, across a galaxy-crossing interval: the area under
  `1/x²` from `1` to `ω` is `1` minus an infinitesimal.

This keeps the "existent, forced, and maximal" shape of the polynomial resolution:
existence and FTC hold on the class, the operator is unique given FTC II, and the
excluded direction (`∫ x⁻¹`, the logarithm) is excluded by the structure of the data, not
by fiat. Extending beyond finite Laurent sums to ω-power *series* integrands runs into a
genuinely new obstacle recorded here for the next attempt: a canonical-sum-defined
antiderivative is pinned only modulo perturbations below every series scale, while
`HasDerivS` demands `O(ε²)` control for increments `ε` finer than every scale — proving
FTC there requires understanding how birthday-minimal choices vary with the argument.
-/

open Polynomial

noncomputable section

namespace Surreal

/-! ### The chain rule through inversion -/

theorem hasDerivS_id (x : Surreal) : HasDerivS (fun s ↦ s) x 1 :=
  ⟨0, fun ε _ ↦ by simp⟩

/-- **The chain rule through inversion**: if `f` has surreal-point derivative `d` at
`x⁻¹`, then `s ↦ f s⁻¹` has derivative `-d·x⁻²` at `x`, for every non-infinitesimal `x`.
(At infinitesimal `x` the statement is genuinely false in general: increments can reach
the pole of the inversion.) -/
theorem HasDerivS.comp_inv {f : Surreal → Surreal} {x d : Surreal}
    (hf : HasDerivS f x⁻¹ d) (hx : ¬ Infinitesimal x) :
    HasDerivS (fun s ↦ f s⁻¹) x (-(d * x⁻¹ ^ 2)) := by
  obtain ⟨Cf, hCf⟩ := hf
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ infinitesimal_zero)
  have hxpos : (0 : Surreal) < |x| := abs_pos.2 hx0
  -- a rational scale separating `x` from `0`
  have hnex : ∃ n : ℕ, 1 ≤ n • |x| := by
    by_contra h
    push Not at h
    exact hx (infinitesimal_iff.2 h)
  obtain ⟨n, hn⟩ := hnex
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hn
    exact absurd hn (by norm_num)
  set s : Surreal := ((n : ℕ) : Surreal) with hs
  have hspos : (0 : Surreal) < s := by
    rw [hs]
    exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [nsmul_eq_mul] at hn
  have hxinv : |x⁻¹| ≤ s := by
    rw [abs_inv, inv_eq_one_div, div_le_iff₀ hxpos]
    linarith
  refine ⟨4 * s ^ 4 * |Cf| + 2 * s ^ 3 * |d|, fun ε hε ↦ ?_⟩
  -- the increment stays away from the pole
  have hq0 : (0 : ℚ) < 1 / (2 * n) := by
    have : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    positivity
  have hεq : |ε| < ((1 / (2 * n) : ℚ) : Surreal) := hε.abs_lt_ratCast hq0
  have hcast : ((1 / (2 * n) : ℚ) : Surreal) = 1 / (2 * s) := by
    rw [hs]
    push_cast
    ring
  rw [hcast] at hεq
  have hxlow : 1 / s ≤ |x| := by
    rw [div_le_iff₀ hspos]
    linarith
  have hhalf : 1 / (2 * s) = 1 / s - 1 / (2 * s) := by
    field_simp
    ring
  have habs := abs_add_le (x + ε) (-ε)
  rw [add_neg_cancel_right, abs_neg] at habs
  have hxe : 1 / (2 * s) ≤ |x + ε| := by
    rw [hhalf]
    linarith
  have hxe0 : x + ε ≠ 0 := by
    intro h
    rw [h, abs_zero] at hxe
    have h2s : (0 : Surreal) < 1 / (2 * s) := by positivity
    linarith
  have hxeinv : |(x + ε)⁻¹| ≤ 2 * s := by
    have h4 : (0 : Surreal) < 2 * s := by positivity
    rw [div_le_iff₀ h4] at hxe
    rw [abs_inv, inv_eq_one_div, div_le_iff₀ (abs_pos.2 hxe0)]
    linarith
  -- the induced increment of `x⁻¹`
  set δ : Surreal := (x + ε)⁻¹ - x⁻¹ with hδdef
  have hδeq : δ = -ε * ((x + ε)⁻¹ * x⁻¹) := by
    rw [hδdef, inv_sub_inv hxe0 hx0, div_eq_mul_inv, mul_inv]
    ring
  have hprodfin : IsFinite ((x + ε)⁻¹ * x⁻¹) := by
    refine isFinite_iff.2 ⟨2 * n ^ 2, ?_⟩
    rw [abs_mul]
    push_cast
    calc |(x + ε)⁻¹| * |x⁻¹| ≤ (2 * s) * s :=
          mul_le_mul hxeinv hxinv (abs_nonneg _) (by positivity)
      _ = 2 * s ^ 2 := by ring
  have hδinf : Infinitesimal δ := by
    rw [hδeq]
    exact hε.neg.mul_isFinite hprodfin
  have hδbound : |δ| ≤ 2 * s ^ 2 * |ε| := by
    rw [hδeq, abs_mul, abs_neg, abs_mul]
    calc |ε| * (|(x + ε)⁻¹| * |x⁻¹|) ≤ |ε| * ((2 * s) * s) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)
          exact mul_le_mul hxeinv hxinv (abs_nonneg _) (by positivity)
      _ = 2 * s ^ 2 * |ε| := by ring
  have hinvadd : (x + ε)⁻¹ = x⁻¹ + δ := by
    rw [hδdef]
    ring
  have hquad : δ + x⁻¹ ^ 2 * ε = ε ^ 2 * (x⁻¹ ^ 2 * (x + ε)⁻¹) := by
    rw [hδeq]
    field_simp
    ring
  -- the two error contributions
  have hf1 : |f (x⁻¹ + δ) - f x⁻¹ - d * δ| ≤ |Cf| * (4 * s ^ 4) * ε ^ 2 := by
    refine (hCf δ hδinf).trans ?_
    have hδ2 : δ ^ 2 ≤ 4 * s ^ 4 * ε ^ 2 := by
      have h2 : δ ^ 2 = |δ| ^ 2 := (sq_abs δ).symm
      rw [h2]
      calc |δ| ^ 2 ≤ (2 * s ^ 2 * |ε|) ^ 2 := by
            have := mul_le_mul hδbound hδbound (abs_nonneg δ) (by positivity)
            simpa [pow_two] using this
        _ = 4 * s ^ 4 * |ε| ^ 2 := by ring
        _ = 4 * s ^ 4 * ε ^ 2 := by rw [sq_abs]
    calc Cf * δ ^ 2 ≤ |Cf| * δ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self Cf) (sq_nonneg δ)
      _ ≤ |Cf| * (4 * s ^ 4 * ε ^ 2) :=
          mul_le_mul_of_nonneg_left hδ2 (abs_nonneg Cf)
      _ = |Cf| * (4 * s ^ 4) * ε ^ 2 := by ring
  have hf2 : |d * (δ + x⁻¹ ^ 2 * ε)| ≤ |d| * (2 * s ^ 3) * ε ^ 2 := by
    rw [hquad, abs_mul, abs_mul]
    have hb : |x⁻¹ ^ 2 * (x + ε)⁻¹| ≤ s ^ 2 * (2 * s) := by
      rw [abs_mul, abs_pow]
      have hsq : |x⁻¹| ^ 2 ≤ s ^ 2 := by
        have h := mul_le_mul hxinv hxinv (abs_nonneg _) hspos.le
        simpa [pow_two] using h
      exact mul_le_mul hsq hxeinv (abs_nonneg _) (by positivity)
    have hε2 : |ε ^ 2| = ε ^ 2 := abs_of_nonneg (sq_nonneg ε)
    have hstep : |d| * (|ε ^ 2| * |x⁻¹ ^ 2 * (x + ε)⁻¹|) ≤
        |d| * (ε ^ 2 * (s ^ 2 * (2 * s))) := by
      rw [hε2]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hb (sq_nonneg ε)) (abs_nonneg d)
    refine hstep.trans (le_of_eq ?_)
    ring
  -- assemble
  show |f (x + ε)⁻¹ - f x⁻¹ - -(d * x⁻¹ ^ 2) * ε| ≤ _
  rw [hinvadd]
  have hsplit : f (x⁻¹ + δ) - f x⁻¹ - -(d * x⁻¹ ^ 2) * ε =
      (f (x⁻¹ + δ) - f x⁻¹ - d * δ) + d * (δ + x⁻¹ ^ 2 * ε) := by
    ring
  rw [hsplit]
  calc |(f (x⁻¹ + δ) - f x⁻¹ - d * δ) + d * (δ + x⁻¹ ^ 2 * ε)|
      ≤ |f (x⁻¹ + δ) - f x⁻¹ - d * δ| + |d * (δ + x⁻¹ ^ 2 * ε)| := abs_add_le _ _
    _ ≤ |Cf| * (4 * s ^ 4) * ε ^ 2 + |d| * (2 * s ^ 3) * ε ^ 2 := add_le_add hf1 hf2
    _ = (4 * s ^ 4 * |Cf| + 2 * s ^ 3 * |d|) * ε ^ 2 := by ring

/-- The derivative of the inversion itself: `(x⁻¹)′ = -x⁻²` at every non-infinitesimal
point. -/
theorem hasDerivS_inv {x : Surreal} (hx : ¬ Infinitesimal x) :
    HasDerivS (fun s ↦ s⁻¹) x (-(x⁻¹ ^ 2)) := by
  have h := (hasDerivS_id x⁻¹).comp_inv hx
  rw [one_mul] at h
  exact h

/-! ### Laurent functions and their derivatives -/

/-- A **Laurent function**: `x ↦ Q(x) + A(x⁻¹)` — a finite sum of monomials `xᵏ`,
`k ∈ ℤ`, with surreal coefficients. -/
def laurentFun (Q A : Polynomial Surreal) : Surreal → Surreal :=
  fun x ↦ Q.eval x + A.eval x⁻¹

/-- **Every Laurent function is differentiable at every non-infinitesimal surreal
point**, with the expected derivative `Q′(x) + x⁻²·(-A′)(x⁻¹)`. Note the derivative's
principal part carries the prefactor `x⁻²`: differentiation lands in the
no-`x⁻¹`-term subclass, which is why the logarithm has no Laurent antiderivative. -/
theorem hasDerivS_laurentFun (Q A : Polynomial Surreal) {x : Surreal}
    (hx : ¬ Infinitesimal x) :
    HasDerivS (laurentFun Q A) x
      (Q.derivative.eval x + x⁻¹ ^ 2 * (-A.derivative).eval x⁻¹) := by
  have h := (hasDerivS_polynomial Q x).add ((hasDerivS_polynomial A x⁻¹).comp_inv hx)
  have hval : Q.derivative.eval x + x⁻¹ ^ 2 * (-A.derivative).eval x⁻¹ =
      Q.derivative.eval x + -(A.derivative.eval x⁻¹ * x⁻¹ ^ 2) := by
    rw [eval_neg]
    ring
  rw [hval]
  exact h

/-! ### The integral -/

/-- The Laurent antiderivative of the integrand `x ↦ P(x) + x⁻²·R(x⁻¹)`:
`x ↦ (antiderivS P)(x) + (-antiderivS R)(x⁻¹)`. -/
def antiderivL (P R : Polynomial Surreal) : Surreal → Surreal :=
  laurentFun (antiderivS P) (-antiderivS R)

/-- **The Laurent integral** `∫ₐᵇ (P(x) + x⁻²·R(x⁻¹)) dx`, for arbitrary surreal
endpoints. The data `(P, R)` ranges over exactly the Laurent integrands with no `x⁻¹`
term — the maximal log-free class. -/
def integralL (P R : Polynomial Surreal) (a b : Surreal) : Surreal :=
  antiderivL P R b - antiderivL P R a

/-- **FTC I on the Laurent class**: at every non-infinitesimal surreal point — finite or
infinite — the Laurent antiderivative has surreal-point derivative the integrand. -/
theorem hasDerivS_antiderivL (P R : Polynomial Surreal) {x : Surreal}
    (hx : ¬ Infinitesimal x) :
    HasDerivS (antiderivL P R) x (P.eval x + x⁻¹ ^ 2 * R.eval x⁻¹) := by
  have h := hasDerivS_laurentFun (antiderivS P) (-antiderivS R) hx
  simp only [derivative_neg, derivative_antiderivS, neg_neg] at h
  exact h

private theorem eval_sub_eval_of_derivative_eq' {P Q : Polynomial Surreal}
    (h : P.derivative = Q.derivative) (a b : Surreal) :
    P.eval b - P.eval a = Q.eval b - Q.eval a := by
  have h0 : (P - Q).derivative = 0 := by rw [derivative_sub, h, sub_self]
  have h1 : P - Q = C ((P - Q).coeff 0) :=
    eq_C_of_natDegree_eq_zero (Polynomial.derivative_eq_zero.1 h0)
  have h2 : P = Q + C ((P - Q).coeff 0) := by rw [← h1]; ring
  rw [h2, eval_add, eval_add, eval_C, eval_C]
  ring

/-- **FTC II on the Laurent class**: the Laurent integral of the derivative of a Laurent
function is its increment. -/
theorem integralL_laurentDeriv (Q A : Polynomial Surreal) (a b : Surreal) :
    integralL Q.derivative (-A.derivative) a b = laurentFun Q A b - laurentFun Q A a := by
  have h1 : (antiderivS Q.derivative).eval b - (antiderivS Q.derivative).eval a =
      Q.eval b - Q.eval a :=
    eval_sub_eval_of_derivative_eq' (by rw [derivative_antiderivS]) a b
  have h2 : (-antiderivS (-A.derivative)).eval b⁻¹ - (-antiderivS (-A.derivative)).eval a⁻¹ =
      A.eval b⁻¹ - A.eval a⁻¹ :=
    eval_sub_eval_of_derivative_eq'
      (by simp [derivative_neg, derivative_antiderivS]) a⁻¹ b⁻¹
  show antiderivL Q.derivative (-A.derivative) b -
      antiderivL Q.derivative (-A.derivative) a = _
  unfold antiderivL laurentFun
  linarith

/-- **Uniqueness of the Laurent integral**: any operator on Laurent integrand data
satisfying FTC II is `integralL`. The replacement, on this class, for the vacuous
Riemann characterization — mirroring `integralS_unique` at polynomial scope. -/
theorem integralL_unique
    {J : Polynomial Surreal → Polynomial Surreal → Surreal → Surreal → Surreal}
    (hJ : ∀ (Q A : Polynomial Surreal) (a b : Surreal),
      J Q.derivative (-A.derivative) a b = laurentFun Q A b - laurentFun Q A a)
    (P R : Polynomial Surreal) (a b : Surreal) : J P R a b = integralL P R a b := by
  have h := hJ (antiderivS P) (-antiderivS R) a b
  simp only [derivative_neg, derivative_antiderivS, neg_neg] at h
  exact h

/-! ### Linearity, additivity, compatibility -/

/-- Interval additivity: `∫ₐᵇ + ∫ᵇᶜ = ∫ₐᶜ`. -/
theorem integralL_add_integralL (P R : Polynomial Surreal) (a b c : Surreal) :
    integralL P R a b + integralL P R b c = integralL P R a c := by
  unfold integralL
  ring

/-- Additivity in the integrand. -/
theorem integralL_add (P P' R R' : Polynomial Surreal) (a b : Surreal) :
    integralL (P + P') (R + R') a b = integralL P R a b + integralL P' R' a b := by
  have hP : (antiderivS (P + P')).eval b - (antiderivS (P + P')).eval a =
      (antiderivS P + antiderivS P').eval b - (antiderivS P + antiderivS P').eval a :=
    eval_sub_eval_of_derivative_eq'
      (by simp [derivative_add, derivative_antiderivS]) a b
  have hR : (-antiderivS (R + R')).eval b⁻¹ - (-antiderivS (R + R')).eval a⁻¹ =
      (-antiderivS R + -antiderivS R').eval b⁻¹ -
        (-antiderivS R + -antiderivS R').eval a⁻¹ :=
    eval_sub_eval_of_derivative_eq'
      (by simp only [derivative_add, derivative_neg, derivative_antiderivS]; ring) a⁻¹ b⁻¹
  unfold integralL antiderivL laurentFun
  simp only [eval_add, eval_neg] at hP hR ⊢
  linarith

/-- Compatibility: with no principal part, the Laurent integral is the polynomial
integral. -/
theorem integralL_poly (P : Polynomial Surreal) (a b : Surreal) :
    integralL P 0 a b = integralS P a b := by
  have h0 : antiderivS (0 : Polynomial Surreal) = 0 := by
    rw [antiderivS]
    exact Polynomial.sum_zero_index _
  unfold integralL antiderivL laurentFun integralS
  rw [h0]
  simp

/-! ### The showcase: the integral of `1/x²` -/

private theorem antiderivS_one : antiderivS (1 : Polynomial Surreal) = X := by
  rw [antiderivS, ← C_1, Polynomial.sum_C_index (by simp)]
  norm_num
  exact Polynomial.monomial_one_one_eq_X

/-- The Laurent integral of `x⁻²` (integrand data `P = 0`, `R = 1`):
`∫ₐᵇ x⁻² dx = a⁻¹ − b⁻¹`. -/
theorem integralL_inv_sq (a b : Surreal) : integralL 0 1 a b = a⁻¹ - b⁻¹ := by
  have h0 : antiderivS (0 : Polynomial Surreal) = 0 := by
    rw [antiderivS]
    exact Polynomial.sum_zero_index _
  unfold integralL antiderivL laurentFun
  rw [h0, antiderivS_one]
  simp
  ring

/-- **`∫₁^ω x⁻² dx = 1 − ω⁻¹`** : the first verified surreal integral of a function with
a pole, over a galaxy-crossing interval — the area under `1/x²` from `1` to `ω` is `1`
minus an infinitesimal, in exact agreement with the real-analytic limit
`∫₁^∞ x⁻² dx = 1`. -/
theorem integralL_inv_sq_one_wpow :
    integralL 0 1 1 (ω^ (1 : Surreal)) = 1 - (ω^ (1 : Surreal))⁻¹ := by
  rw [integralL_inv_sq, inv_one]

end Surreal

end
