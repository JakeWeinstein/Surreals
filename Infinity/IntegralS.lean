import Infinity.GeneralDeriv
import Infinity.Integral

/-!
# The full surreal integral: surreal coefficients, surreal endpoints, FTC everywhere

The Galaxy Kernel Theorem (`Infinity.GeneralDeriv`) shows arbitrary-function integration on
`No` is ill-posed. This file completes the positive side at its maximal polynomial scope:
the integral for polynomials **with surreal coefficients**, over intervals with **arbitrary
surreal endpoints**, with the Fundamental Theorem of Calculus holding **at every surreal
point** in the strong `O(ε²)` sense of `HasDerivS`.

* `Surreal.antiderivS` / `Surreal.derivative_antiderivS` — the antiderivative on
  `Surreal[X]`.
* `Surreal.integralS P a b` — the integral `∫ₐᵇ P`.
* **FTC I everywhere** (`Surreal.hasDerivS_integralS`) : `s ↦ ∫ₐˢ P` has derivative `P(x)`
  at every surreal `x` — infinite and infinitesimal points included.
* **FTC II** (`Surreal.integralS_derivative`), uniqueness (`Surreal.integralS_unique`),
  linearity, interval additivity.
* `Surreal.integralS_map_realHom` — compatibility: on real-coefficient polynomials this
  integral agrees with `Infinity.Integral`'s.
* `Surreal.integralS_X_zero_omega` : `∫₀^ω x dx = ω²/2`, now as an instance of the
  everywhere-FTC theory.

Together with the Galaxy Kernel Theorem this is a complete resolution of FTC-integration on
`No` at the polynomial level: the integral exists, is forced, and satisfies the full FTC on
the largest class where the obstruction theorem permits it to be well-defined by
antiderivatives alone.
-/

open Polynomial ArchimedeanClass Finset

noncomputable section

namespace Surreal

/-! ### The antiderivative on `Surreal[X]` -/

/-- The formal antiderivative of a surreal polynomial: `Xⁿ ↦ Xⁿ⁺¹/(n+1)`. -/
def antiderivS (P : Polynomial Surreal) : Polynomial Surreal :=
  P.sum fun n a ↦ monomial (n + 1) (a / ((n + 1 : ℕ) : Surreal))

theorem derivative_antiderivS (P : Polynomial Surreal) : (antiderivS P).derivative = P := by
  rw [antiderivS, Polynomial.sum_def, map_sum]
  calc ∑ n ∈ P.support, ((monomial (n + 1)) (P.coeff n / ((n + 1 : ℕ) : Surreal))).derivative
      = ∑ n ∈ P.support, monomial n (P.coeff n) := by
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        rw [derivative_monomial, Nat.add_sub_cancel,
          div_mul_cancel₀ _ (Nat.cast_pos.2 n.succ_pos).ne']
    _ = P := by rw [← Polynomial.sum_def]; exact sum_monomial_eq P

/-! ### The integral -/

/-- The integral `∫ₐᵇ P` of a surreal-coefficient polynomial over any surreal interval. -/
def integralS (P : Polynomial Surreal) (a b : Surreal) : Surreal :=
  (antiderivS P).eval b - (antiderivS P).eval a

private theorem eval_sub_eval_of_derivative_eq {P Q : Polynomial Surreal}
    (h : P.derivative = Q.derivative) (a b : Surreal) :
    P.eval b - P.eval a = Q.eval b - Q.eval a := by
  have h0 : (P - Q).derivative = 0 := by rw [derivative_sub, h, sub_self]
  have h1 : P - Q = C ((P - Q).coeff 0) :=
    eq_C_of_natDegree_eq_zero (Polynomial.derivative_eq_zero.1 h0)
  have h2 : P = Q + C ((P - Q).coeff 0) := by rw [← h1]; ring
  rw [h2, eval_add, eval_add, eval_C, eval_C]
  ring

/-! ### The Fundamental Theorem of Calculus, everywhere -/

/-- **FTC I at every surreal point**: the integral function `s ↦ ∫ₐˢ P` has derivative
`P(x)` at every surreal `x`, in the strong `O(ε²)` sense — infinite and infinitesimal
points included. -/
theorem hasDerivS_integralS (P : Polynomial Surreal) (a x : Surreal) :
    HasDerivS (fun s ↦ integralS P a s) x (P.eval x) := by
  have h1 := hasDerivS_polynomial (antiderivS P) x
  rw [derivative_antiderivS] at h1
  exact h1.sub_const ((antiderivS P).eval a)

/-- **FTC II**: `∫ₐᵇ Q′ = Q(b) − Q(a)`. -/
theorem integralS_derivative (Q : Polynomial Surreal) (a b : Surreal) :
    integralS Q.derivative a b = Q.eval b - Q.eval a :=
  eval_sub_eval_of_derivative_eq (by rw [derivative_antiderivS]) a b

/-- **Uniqueness**: any operator satisfying FTC II is this integral. -/
theorem integralS_unique {J : Polynomial Surreal → Surreal → Surreal → Surreal}
    (hJ : ∀ (Q : Polynomial Surreal) (a b : Surreal),
      J Q.derivative a b = Q.eval b - Q.eval a)
    (P : Polynomial Surreal) (a b : Surreal) : J P a b = integralS P a b := by
  have h := hJ (antiderivS P) a b
  rw [derivative_antiderivS] at h
  rw [h, integralS]

/-! ### Linearity and interval additivity -/

theorem integralS_add_integralS (P : Polynomial Surreal) (a b c : Surreal) :
    integralS P a b + integralS P b c = integralS P a c := by
  rw [integralS, integralS, integralS]; ring

theorem integralS_add (P Q : Polynomial Surreal) (a b : Surreal) :
    integralS (P + Q) a b = integralS P a b + integralS Q a b := by
  have h : (antiderivS (P + Q)).derivative = (antiderivS P + antiderivS Q).derivative := by
    rw [derivative_add, derivative_antiderivS, derivative_antiderivS, derivative_antiderivS]
  rw [integralS, eval_sub_eval_of_derivative_eq h, eval_add, eval_add, integralS, integralS]
  ring

theorem integralS_C_mul (c : Surreal) (P : Polynomial Surreal) (a b : Surreal) :
    integralS (C c * P) a b = c * integralS P a b := by
  have h : (antiderivS (C c * P)).derivative = (C c * antiderivS P).derivative := by
    rw [derivative_C_mul, derivative_antiderivS, derivative_antiderivS]
  rw [integralS, eval_sub_eval_of_derivative_eq h, eval_mul, eval_mul, eval_C, eval_C, integralS]
  ring

/-! ### Compatibility and computations -/

/-- On real-coefficient polynomials, the surreal integral agrees with the one from
`Infinity.Integral`. -/
theorem integralS_map_realHom (p : Polynomial ℝ) (a b : Surreal) :
    integralS (p.map realHom) a b = integral p a b := by
  have h : (antiderivS (p.map realHom)).derivative =
      ((antideriv p).map realHom).derivative := by
    rw [derivative_antiderivS, derivative_map, derivative_antideriv]
  rw [integralS, eval_sub_eval_of_derivative_eq h, eval_map, eval_map, integral]

theorem antiderivS_X : antiderivS (X : Polynomial Surreal) = monomial 2 (1 / 2) := by
  rw [antiderivS, ← monomial_one_one_eq_X, sum_monomial_index _ _ (by simp)]
  norm_num

/-- `∫ₐᵇ x dx = b²/2 − a²/2` over any surreal interval. -/
theorem integralS_X (a b : Surreal) : integralS X a b = b ^ 2 / 2 - a ^ 2 / 2 := by
  rw [integralS, antiderivS_X, eval_monomial, eval_monomial]
  ring

/-- `∫₀^ω x dx = ω²/2`, as an instance of the everywhere-FTC theory. -/
theorem integralS_X_zero_omega :
    integralS X 0 (ω^ (1 : Surreal)) = (ω^ (1 : Surreal)) ^ 2 / 2 := by
  rw [integralS_X]
  norm_num

end Surreal
