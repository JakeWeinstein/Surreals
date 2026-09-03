/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.Norton
import Infinity.IntegralS
import Infinity.KernelSeparation

/-!
# The moonshot contrast: `∫₀^ω eˣ dx = e^ω − 1`, and Norton's overshoot is exactly `1`

`Infinity.Norton` proved the *negative* half of the Conway–Kruskal–Norton story: the
genetic (simplest-fit) integral evaluates `∫₀^ω eˣ dx` to `ω^ω = e^ω` — the wrong value,
missing the `−1` of Newton–Leibniz. This file supplies the *positive* half: an integral
operator on an exponential integrand class that is **forced** (unique given FTC II,
Laurent-style), satisfies **FTC I** with genuine `O(ε²)` surreal-point derivatives at
every point of the two-galaxy real lattice, and evaluates the same integral to the
Newton–Leibniz value

  `∫₀^ω eˣ dx = e^ω − 1 = ω^ω − 1`  (`integralE_exp_zero_wpow`).

The contrast lands as a single equation (`norton_error_eq_one`):

  `nortonIntegralExp − ∫₀^ω eˣ dx = 1` —

**the genetic integral overshoots the forced FTC integral by exactly `1`.** Both values
are kernel-checked; the discrepancy Kruskal observed in the 1970s is now a theorem with
an exact error term.

The construction, mirroring `Infinity.Laurent`:

* `HasDerivS.congr_halo` — `HasDerivS` only ever samples a function on the halo of the
  base point, so functions agreeing there share derivatives; `HasDerivS.const_mul`.
* **The exponential ODE on the two-galaxy lattice** (`hasDerivS_nortonExp_realCast`,
  `hasDerivS_nortonExp_wpow_add_realCast`): `nortonExp` has surreal-point derivative
  *itself* at every real point and at every `ω + real` point. At real points this is
  halo transport of `hasDerivS_expFin_realCast`; at top-galaxy points the increment
  never leaves the galaxy, so the derivative is the real-point one translated by `ω`
  (`HasDerivS.comp_sub_const`) and scaled by the constant `ω^ω`.
* The integrand class `expPolyFun c P = x ↦ c·nortonExp x + P(x)` — **closed under
  differentiation with `c` fixed** (`hasDerivS_expPolyFun_of`): the class is rigid across
  galaxies (globally determined by the data `(c, P)`), which is exactly what the Galaxy
  and Fractal Kernel theorems demand of an integrand class with a well-posed integral.
* `antiderivE` / `integralE` with **FTC I** at the lattice points, **FTC II**
  (`integralE_expPolyFunDeriv`) and **uniqueness** (`integralE_unique`) unconditionally —
  the uniqueness is structural on the data, dodging the kernel obstruction the same way
  `integralL_unique` does — plus linearity, interval additivity, and compatibility with
  the polynomial integral (`integralE_zero`).

Honesty note: FTC I is proved at `{reals} ∪ {ω + reals}` — precisely the two-galaxy
lattice on which `nortonExp` is a faithful exponential (it is junk-valued in the middle
galaxies) and precisely the points the showcase interval's endpoints inhabit. Extending
`exp′ = exp` to finite points with nonzero infinitesimal part is the canonical-sum
variation problem recorded in `Infinity.Laurent`; extending `nortonExp` itself across the
middle galaxies is Route B of `notes/exp-infinite-design.md`. Neither is needed for the
contrast: FTC II and uniqueness are unconditional, and the genetic integral disagrees
with the forced operator on their common integrand.
-/

open Polynomial

noncomputable section

namespace Surreal

/-! ### Halo congruence and constant multiples -/

/-- `HasDerivS` only ever samples a function on the halo of the base point: two functions
agreeing at every infinitesimal displacement of `x` (including `ε = 0`, i.e. at `x`
itself) have the same surreal-point derivatives there. -/
theorem HasDerivS.congr_halo {f g : Surreal → Surreal} {x d : Surreal}
    (h : HasDerivS f x d)
    (hfg : ∀ ε : Surreal, Infinitesimal ε → g (x + ε) = f (x + ε)) :
    HasDerivS g x d := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun ε hε ↦ ?_⟩
  have hx : g x = f x := by simpa using hfg 0 infinitesimal_zero
  rw [hfg ε hε, hx]
  exact hC ε hε

/-- Constant multiples: the error constant scales by `|c|`. -/
theorem HasDerivS.const_mul {f : Surreal → Surreal} {x d : Surreal} (c : Surreal)
    (h : HasDerivS f x d) : HasDerivS (fun s ↦ c * f s) x (c * d) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨|c| * C, fun ε hε ↦ ?_⟩
  have hsplit : c * f (x + ε) - c * f x - c * d * ε =
      c * (f (x + ε) - f x - d * ε) := by ring
  show |c * f (x + ε) - c * f x - c * d * ε| ≤ |c| * C * ε ^ 2
  rw [hsplit, abs_mul]
  calc |c| * |f (x + ε) - f x - d * ε| ≤ |c| * (C * ε ^ 2) :=
        mul_le_mul_of_nonneg_left (hC ε hε) (abs_nonneg c)
    _ = |c| * C * ε ^ 2 := by ring

/-! ### The exponential ODE on the two-galaxy lattice -/

/-- **`exp′ = exp` at every real point, for the lattice exponential**: on the halo of a
real, `nortonExp` is `expFin`, so `hasDerivS_expFin_realCast` transports. -/
theorem hasDerivS_nortonExp_realCast (r : ℝ) :
    HasDerivS nortonExp (r : Surreal) (nortonExp (r : Surreal)) := by
  have hval : nortonExp (r : Surreal) = expFin (r : Surreal) :=
    nortonExp_of_isFinite (isFinite_realCast r)
  rw [hval]
  exact (hasDerivS_expFin_realCast r).congr_halo fun ε hε ↦
    nortonExp_of_isFinite ((isFinite_realCast r).add hε.isFinite)

/-- **`exp′ = exp` at every point `ω + r` of the top galaxy's real lattice**: an
infinitesimal increment never leaves the galaxy, so on the halo `nortonExp` is the
translate-by-`ω` of `expFin` scaled by the constant `ω^ω`, and the real-point
differential equation transports through `comp_sub_const` and `const_mul`. -/
theorem hasDerivS_nortonExp_wpow_add_realCast (r : ℝ) :
    HasDerivS nortonExp (ω^ (1 : Surreal) + (r : Surreal))
      (nortonExp (ω^ (1 : Surreal) + (r : Surreal))) := by
  have h1 : HasDerivS expFin (ω^ (1 : Surreal) + (r : Surreal) - ω^ (1 : Surreal))
      (expFin (r : Surreal)) := by
    rw [add_sub_cancel_left]
    exact hasDerivS_expFin_realCast r
  have h2 := (h1.comp_sub_const).const_mul (ω^ ω^ (1 : Surreal))
  rw [nortonExp_wpow_one_add (isFinite_realCast r)]
  refine h2.congr_halo fun ε hε ↦ ?_
  have hnf : ¬ IsFinite (ω^ (1 : Surreal) + (r : Surreal) + ε) := by
    intro hfin
    exact not_isFinite_wpow_one
      (by simpa using hfin.sub ((isFinite_realCast r).add hε.isFinite))
  show nortonExp (ω^ (1 : Surreal) + (r : Surreal) + ε) =
    ω^ ω^ (1 : Surreal) * expFin (ω^ (1 : Surreal) + (r : Surreal) + ε - ω^ (1 : Surreal))
  rw [nortonExp_of_not_isFinite hnf]

/-! ### The exp-polynomial class -/

/-- The **exp-polynomial integrand class**: `x ↦ c·nortonExp x + P(x)`, globally
determined by the data `(c, P)` — the cross-galaxy rigidity the kernel obstruction
theorems demand. -/
def expPolyFun (c : Surreal) (P : Polynomial Surreal) : Surreal → Surreal :=
  fun x ↦ c * nortonExp x + P.eval x

/-- **The class is closed under differentiation with the exponential coefficient
fixed**: wherever `nortonExp` satisfies its differential equation,
`(c·exp + P)′ = c·exp + P′`. -/
theorem hasDerivS_expPolyFun_of {x : Surreal} (hx : HasDerivS nortonExp x (nortonExp x))
    (c : Surreal) (P : Polynomial Surreal) :
    HasDerivS (expPolyFun c P) x (expPolyFun c P.derivative x) :=
  (hx.const_mul c).add (hasDerivS_polynomial P x)

/-- The differentiation closure at every real point. -/
theorem hasDerivS_expPolyFun_realCast (c : Surreal) (P : Polynomial Surreal) (r : ℝ) :
    HasDerivS (expPolyFun c P) (r : Surreal) (expPolyFun c P.derivative (r : Surreal)) :=
  hasDerivS_expPolyFun_of (hasDerivS_nortonExp_realCast r) c P

/-- The differentiation closure at every top-galaxy lattice point `ω + r`. -/
theorem hasDerivS_expPolyFun_wpow_add_realCast (c : Surreal) (P : Polynomial Surreal)
    (r : ℝ) :
    HasDerivS (expPolyFun c P) (ω^ (1 : Surreal) + (r : Surreal))
      (expPolyFun c P.derivative (ω^ (1 : Surreal) + (r : Surreal))) :=
  hasDerivS_expPolyFun_of (hasDerivS_nortonExp_wpow_add_realCast r) c P

/-! ### The integral -/

/-- The exp-polynomial antiderivative of the integrand data `(c, P)`:
`x ↦ c·nortonExp x + (antiderivS P)(x)`. -/
def antiderivE (c : Surreal) (P : Polynomial Surreal) : Surreal → Surreal :=
  expPolyFun c (antiderivS P)

/-- **The exp-polynomial integral** `∫ₐᵇ (c·eˣ + P(x)) dx`, for arbitrary surreal
endpoints. -/
def integralE (c : Surreal) (P : Polynomial Surreal) (a b : Surreal) : Surreal :=
  antiderivE c P b - antiderivE c P a

/-- **FTC I at real points**: the antiderivative's surreal-point derivative is the
integrand. -/
theorem hasDerivS_antiderivE_realCast (c : Surreal) (P : Polynomial Surreal) (r : ℝ) :
    HasDerivS (antiderivE c P) (r : Surreal) (expPolyFun c P (r : Surreal)) := by
  have h := hasDerivS_expPolyFun_realCast c (antiderivS P) r
  rwa [derivative_antiderivS] at h

/-- **FTC I at top-galaxy lattice points** `ω + r`. -/
theorem hasDerivS_antiderivE_wpow_add_realCast (c : Surreal) (P : Polynomial Surreal)
    (r : ℝ) :
    HasDerivS (antiderivE c P) (ω^ (1 : Surreal) + (r : Surreal))
      (expPolyFun c P (ω^ (1 : Surreal) + (r : Surreal))) := by
  have h := hasDerivS_expPolyFun_wpow_add_realCast c (antiderivS P) r
  rwa [derivative_antiderivS] at h

/-- **FTC I at `ω` itself** — the upper endpoint of the showcase interval. -/
theorem hasDerivS_antiderivE_wpow (c : Surreal) (P : Polynomial Surreal) :
    HasDerivS (antiderivE c P) (ω^ (1 : Surreal)) (expPolyFun c P (ω^ (1 : Surreal))) := by
  have h := hasDerivS_antiderivE_wpow_add_realCast c P 0
  simpa using h

private theorem eval_sub_eval_of_derivative_eq'' {P Q : Polynomial Surreal}
    (h : P.derivative = Q.derivative) (a b : Surreal) :
    P.eval b - P.eval a = Q.eval b - Q.eval a := by
  have h0 : (P - Q).derivative = 0 := by rw [derivative_sub, h, sub_self]
  have h1 : P - Q = C ((P - Q).coeff 0) :=
    eq_C_of_natDegree_eq_zero (Polynomial.derivative_eq_zero.1 h0)
  have h2 : P = Q + C ((P - Q).coeff 0) := by rw [← h1]; ring
  rw [h2, eval_add, eval_add, eval_C, eval_C]
  ring

/-- **FTC II on the exp-polynomial class**: the integral of the derivative data is the
increment of the function. Unconditional — no derivative hypothesis, no kernel
constancy: pure structure of the data, exactly as in `integralL_laurentDeriv`. -/
theorem integralE_expPolyFunDeriv (c : Surreal) (Q : Polynomial Surreal) (a b : Surreal) :
    integralE c Q.derivative a b = expPolyFun c Q b - expPolyFun c Q a := by
  have h1 : (antiderivS Q.derivative).eval b - (antiderivS Q.derivative).eval a =
      Q.eval b - Q.eval a :=
    eval_sub_eval_of_derivative_eq'' (by rw [derivative_antiderivS]) a b
  show expPolyFun c (antiderivS Q.derivative) b - expPolyFun c (antiderivS Q.derivative) a = _
  unfold expPolyFun
  linarith

/-- **Uniqueness of the exp-polynomial integral**: any operator on the integrand data
satisfying FTC II is `integralE`. The forced-ness half of the contrast: on this class
the fundamental theorem admits exactly one integral, and it is Newton–Leibniz. -/
theorem integralE_unique
    {J : Surreal → Polynomial Surreal → Surreal → Surreal → Surreal}
    (hJ : ∀ (c : Surreal) (Q : Polynomial Surreal) (a b : Surreal),
      J c Q.derivative a b = expPolyFun c Q b - expPolyFun c Q a)
    (c : Surreal) (P : Polynomial Surreal) (a b : Surreal) :
    J c P a b = integralE c P a b := by
  have h := hJ c (antiderivS P) a b
  rw [derivative_antiderivS] at h
  exact h

/-! ### Linearity, additivity, compatibility -/

/-- Interval additivity: `∫ₐᵇ + ∫ᵇᶜ = ∫ₐᶜ`. -/
theorem integralE_add_integralE (c : Surreal) (P : Polynomial Surreal)
    (a b d : Surreal) :
    integralE c P a b + integralE c P b d = integralE c P a d := by
  unfold integralE
  ring

/-- Additivity in the integrand data. -/
theorem integralE_add (c c' : Surreal) (P P' : Polynomial Surreal) (a b : Surreal) :
    integralE (c + c') (P + P') a b = integralE c P a b + integralE c' P' a b := by
  have hP : (antiderivS (P + P')).eval b - (antiderivS (P + P')).eval a =
      (antiderivS P + antiderivS P').eval b - (antiderivS P + antiderivS P').eval a :=
    eval_sub_eval_of_derivative_eq''
      (by simp [derivative_add, derivative_antiderivS]) a b
  unfold integralE antiderivE expPolyFun
  simp only [eval_add] at hP ⊢
  linarith [hP]

/-- Compatibility: with no exponential part, the exp-polynomial integral is the
polynomial integral. -/
theorem integralE_zero (P : Polynomial Surreal) (a b : Surreal) :
    integralE 0 P a b = integralS P a b := by
  unfold integralE antiderivE expPolyFun integralS
  ring

/-! ### The showcase and the contrast -/

private theorem antiderivS_zero : antiderivS (0 : Polynomial Surreal) = 0 := by
  rw [antiderivS]
  exact Polynomial.sum_zero_index _

/-- The integral of the bare exponential (data `c = 1`, `P = 0`) is the increment of
`nortonExp` — Newton–Leibniz for `eˣ` over any surreal interval. -/
theorem integralE_exp (a b : Surreal) :
    integralE 1 0 a b = nortonExp b - nortonExp a := by
  unfold integralE antiderivE expPolyFun
  rw [antiderivS_zero]
  simp

/-- **THE MOONSHOT VALUE: `∫₀^ω eˣ dx = e^ω − 1 = ω^ω − 1`.** The forced FTC integral
of the exponential over `[0, ω]` — with FTC I genuinely holding at both endpoints
(`hasDerivS_antiderivE_realCast` at `0`, `hasDerivS_antiderivE_wpow` at `ω`) — takes
the Newton–Leibniz value that Norton's genetic integral misses. -/
theorem integralE_exp_zero_wpow :
    integralE 1 0 0 (ω^ (1 : Surreal)) = ω^ ω^ (1 : Surreal) - 1 := by
  rw [integralE_exp, nortonExp_wpow_one, nortonExp_of_isFinite isFinite_zero,
    expFin_zero]

/-- The genetic simplest-fit integral disagrees with the forced FTC integral on their
common integrand `eˣ` over `[0, ω]`. -/
theorem nortonIntegralExp_ne_integralE :
    nortonIntegralExp ≠ integralE 1 0 0 (ω^ (1 : Surreal)) := by
  rw [nortonIntegralExp_eq_wpow_wpow, integralE_exp_zero_wpow]
  intro h
  have h1 : (0 : Surreal) = -1 := by linarith
  norm_num at h1

/-- **THE CONTRAST: Norton's overshoot is exactly `1`.** The genetic integral exceeds
the forced FTC value by precisely the `exp 0` term the simplest-fit cut cannot see:
`nortonIntegralExp − ∫₀^ω eˣ dx = 1`. Kruskal's 1970s observation that the genetic
integral gives `e^ω` where Newton–Leibniz demands `e^ω − 1`, as a single exact
kernel-checked equation. -/
theorem norton_error_eq_one :
    nortonIntegralExp - integralE 1 0 0 (ω^ (1 : Surreal)) = 1 := by
  rw [nortonIntegralExp_eq_wpow_wpow, integralE_exp_zero_wpow]
  ring

end Surreal

end
