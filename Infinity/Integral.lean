import Infinity.DerivRules
import Infinity.Summation

/-!
# Integration on the surreal numbers

The Riemann collapse (`Infinity.Riemann`) proved that approximation-based integration is
degenerate on `No`. This file builds the integral that survives: for polynomial integrands,
integration **is** antidifferentiation — the route the Fundamental Theorem of Calculus makes
canonical — and on `No` it works with **arbitrary surreal endpoints**, infinite ones included.

* `Surreal.antideriv` : the formal antiderivative on `ℝ[X]`, with
  `Surreal.derivative_antideriv : (antideriv p).derivative = p`.
* `Surreal.integral p a b` : the integral `∫ₐᵇ p`, defined for **any** surreals `a b`.
* **FTC I** (`Surreal.hasDerivAt_integral`) : `x ↦ ∫ₐˣ p` is differentiable with derivative
  `p x` — in the strong sense of `HasDerivAt`: every nonzero infinitesimal increment
  witnesses it.
* **FTC II** (`Surreal.integral_derivative`) : `∫ₐᵇ q′ = q(b) − q(a)`.
* `Surreal.integral_unique` : any operator satisfying FTC II *is* this integral — the
  characterization that replaces the (vacuous) Riemann definition.
* Linearity (`integral_add`, `integral_C_mul`) and interval additivity
  (`integral_add_integral`).
* `Surreal.integral_X` and the flagship: **`∫₀^ω x dx = ω²/2`** — the computation this
  project began with, now a kernel-checked theorem.
* `Surreal.exists_isHahnSum_integral_omegaPowerSeries` : **term-by-term integration** of a
  transfinite ω-power series produces another summable series — the integral meets the
  Transfinite Summation Theorem.
-/

open Polynomial ArchimedeanClass Finset

noncomputable section

namespace Surreal

/-! ### The antiderivative -/

/-- The formal antiderivative of a real polynomial: `Xⁿ ↦ Xⁿ⁺¹/(n+1)`. -/
def antideriv (p : ℝ[X]) : ℝ[X] :=
  p.sum fun n a ↦ monomial (n + 1) (a / ((n + 1 : ℕ) : ℝ))

/-- The antiderivative differentiates back to the original polynomial. -/
theorem derivative_antideriv (p : ℝ[X]) : (antideriv p).derivative = p := by
  rw [antideriv, Polynomial.sum_def, map_sum]
  calc ∑ n ∈ p.support, ((monomial (n + 1)) (p.coeff n / ((n + 1 : ℕ) : ℝ))).derivative
      = ∑ n ∈ p.support, monomial n (p.coeff n) := by
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        rw [derivative_monomial, Nat.add_sub_cancel,
          div_mul_cancel₀ _ (by exact_mod_cast Nat.succ_ne_zero n)]
    _ = p := by rw [← Polynomial.sum_def]; exact sum_monomial_eq p

/-! ### The integral -/

/-- The integral `∫ₐᵇ p` of a real polynomial over a surreal interval — endpoints may be any
surreals, infinite and infinitesimal ones included. Defined, as the Fundamental Theorem of
Calculus demands and the Riemann collapse forces, through the antiderivative. -/
def integral (p : ℝ[X]) (a b : Surreal) : Surreal :=
  (antideriv p).eval₂ realHom b - (antideriv p).eval₂ realHom a

/-- Polynomials with equal derivatives have equal increments (they differ by a constant). -/
private theorem eval₂_sub_eval₂_of_derivative_eq {P Q : ℝ[X]}
    (h : P.derivative = Q.derivative) (a b : Surreal) :
    P.eval₂ realHom b - P.eval₂ realHom a = Q.eval₂ realHom b - Q.eval₂ realHom a := by
  have h0 : (P - Q).derivative = 0 := by rw [derivative_sub, h, sub_self]
  have h1 : P - Q = C ((P - Q).coeff 0) :=
    eq_C_of_natDegree_eq_zero (Polynomial.derivative_eq_zero.1 h0)
  have h2 : P = Q + C ((P - Q).coeff 0) := by
    rw [← h1]; ring
  rw [h2, eval₂_add, eval₂_add, eval₂_C, eval₂_C]
  ring

/-! ### The Fundamental Theorem of Calculus -/

/-- **FTC II**: the integral of a derivative is the increment: `∫ₐᵇ q′ = q(b) − q(a)`. -/
theorem integral_derivative (q : ℝ[X]) (a b : Surreal) :
    integral q.derivative a b = q.eval₂ realHom b - q.eval₂ realHom a :=
  eval₂_sub_eval₂_of_derivative_eq (by rw [derivative_antideriv]) a b

/-- **FTC I**: the integral function `x ↦ ∫ₐˣ p` is differentiable at every real point with
derivative `p x` — witnessed by every nonzero infinitesimal increment. -/
theorem hasDerivAt_integral (p : ℝ[X]) (a : Surreal) (x : ℝ) :
    HasDerivAt (fun s ↦ integral p a s) (p.eval x) x := by
  have h1 := hasDerivAt_polynomial (antideriv p) x
  rw [derivative_antideriv] at h1
  have h2 := h1.sub (hasDerivAt_const ((antideriv p).eval₂ realHom a) x)
  simpa [integral] using h2

/-- **Uniqueness**: any operator satisfying FTC II *is* the integral. This is the
characterization that replaces the Riemann definition, which `Infinity.Riemann` proved
vacuous on `No`. -/
theorem integral_unique {J : ℝ[X] → Surreal → Surreal → Surreal}
    (hJ : ∀ (q : ℝ[X]) (a b : Surreal),
      J q.derivative a b = q.eval₂ realHom b - q.eval₂ realHom a)
    (p : ℝ[X]) (a b : Surreal) : J p a b = integral p a b := by
  have h := hJ (antideriv p) a b
  rw [derivative_antideriv] at h
  rw [h, integral]

/-! ### Linearity and interval additivity -/

theorem integral_add_integral (p : ℝ[X]) (a b c : Surreal) :
    integral p a b + integral p b c = integral p a c := by
  rw [integral, integral, integral]; ring

theorem integral_add (p q : ℝ[X]) (a b : Surreal) :
    integral (p + q) a b = integral p a b + integral q a b := by
  have h : (antideriv (p + q)).derivative = (antideriv p + antideriv q).derivative := by
    rw [derivative_add, derivative_antideriv, derivative_antideriv, derivative_antideriv]
  rw [integral, eval₂_sub_eval₂_of_derivative_eq h, eval₂_add, eval₂_add, integral, integral]
  ring

theorem integral_C_mul (c : ℝ) (p : ℝ[X]) (a b : Surreal) :
    integral (C c * p) a b = (c : Surreal) * integral p a b := by
  have h : (antideriv (C c * p)).derivative = (C c * antideriv p).derivative := by
    rw [derivative_C_mul, derivative_antideriv, derivative_antideriv]
  rw [integral, eval₂_sub_eval₂_of_derivative_eq h]
  simp only [eval₂_mul, eval₂_C, realHom_apply]
  rw [integral]
  ring

/-! ### Computations -/

theorem antideriv_X : antideriv (X : ℝ[X]) = monomial 2 (1 / 2) := by
  rw [antideriv, ← monomial_one_one_eq_X, sum_monomial_index _ _ (by simp)]
  norm_num

/-- `∫ₐᵇ x dx = b²/2 − a²/2`, for arbitrary surreal endpoints. -/
theorem integral_X (a b : Surreal) : integral X a b = b ^ 2 / 2 - a ^ 2 / 2 := by
  have hhalf : realHom (1 / 2 : ℝ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  rw [integral, antideriv_X, eval₂_monomial, eval₂_monomial, hhalf]
  ring

/-- **`∫₀^ω x dx = ω²/2`** — the algebra-with-infinity computation this project began with,
as a kernel-checked theorem: integrating the identity function from `0` to the infinite
surreal `ω` yields exactly `ω²/2`. -/
theorem integral_X_zero_omega :
    integral X 0 (ω^ (1 : Surreal)) = (ω^ (1 : Surreal)) ^ 2 / 2 := by
  rw [integral_X]
  norm_num

/-- And dually, an integral over an infinitesimal interval: `∫₀^(1/ω) x dx = 1/(2ω²)`. -/
example : integral X 0 (ω^ (1 : Surreal))⁻¹ = ((ω^ (1 : Surreal))⁻¹) ^ 2 / 2 := by
  rw [integral_X]; norm_num

/-! ### Term-by-term integration of transfinite series -/

theorem integral_C_mul_X_pow (c : ℝ) (k : ℕ) (a b : Surreal) :
    integral (C c * X ^ k) a b =
      ((c / ((k + 1 : ℕ) : ℝ) : ℝ) : Surreal) * b ^ (k + 1) -
        ((c / ((k + 1 : ℕ) : ℝ) : ℝ) : Surreal) * a ^ (k + 1) := by
  rw [integral, C_mul_X_pow_eq_monomial, antideriv, sum_monomial_index _ _ (by simp),
    eval₂_monomial, eval₂_monomial, realHom_apply]

/-- **Term-by-term integration**: integrating each term of a strictly dominating ω-power
series `Σ rₖ ω⁻ᵏ` from `0` to `1/ω` produces another strictly dominating series — which
therefore has a transfinite sum by the Summation Theorem. The integral and the Hahn-sum
semantics compose. -/
theorem exists_isHahnSum_integral_omegaPowerSeries (r : ℕ → ℝ) (hr : ∀ n, r n ≠ 0) :
    ∃ x, IsHahnSum
      (fun k ↦ integral (C (r k) * X ^ k) 0 ((ω^ (1 : Surreal))⁻¹)) x := by
  have he : Infinitesimal ((ω^ (1 : Surreal))⁻¹ : Surreal) := infinitesimal_inv_wpow one_pos
  have he0 : (0 : Surreal) < (ω^ (1 : Surreal))⁻¹ := inv_pos.2 (wpow_pos _)
  have hterm : ∀ k, integral (C (r k) * X ^ k) 0 ((ω^ (1 : Surreal))⁻¹) =
      ((r k / ((k + 1 : ℕ) : ℝ) : ℝ) : Surreal) * ((ω^ (1 : Surreal))⁻¹) ^ (k + 1) := by
    intro k
    rw [integral_C_mul_X_pow, zero_pow (Nat.succ_ne_zero k), mul_zero, sub_zero]
  rw [funext hterm]
  apply exists_isHahnSum
  intro n
  have hcoeff : ∀ k : ℕ, (r k / ((k + 1 : ℕ) : ℝ)) ≠ 0 := fun k ↦
    div_ne_zero (hr k) (by exact_mod_cast Nat.succ_ne_zero k)
  rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, mk_realCast (hcoeff n),
    mk_realCast (hcoeff (n + 1)), zero_add, zero_add]
  exact mk_pow_lt_mk_pow_succ he he0 (n + 1)

end Surreal
