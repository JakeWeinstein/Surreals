import Infinity.JetCalculus
import Infinity.ExpIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The analytic calculus on the finite galaxy

`JetCalculus.lean` proved that every power series `T` is a differentiable function on the halo
of every centre, with the formal derivative as its derivative (`hasDerivS_jet'`). This file is the
endgame that theorem was built for: **every real function extends to the finite surreals through
its Taylor jets, the extension is differentiable at every finite point with the extension of the
derivative as its derivative, the Fundamental Theorem of Calculus holds in both directions, and the
resulting integral is the unique one on the class.** Every finite surreal is `x = st x + (x − st x)`
with `x − st x` infinitesimal (`StandardPart.lean`), and an infinitesimal increment does not move
the standard part — so on the halo of each real `r` a *jet family* `T : ℝ → PowerSeries ℝ` is the
single jet function `jet (T r) r`, and everything is transported from `JetCalculus`.

## Jet families and the extension operator

* **`extJ T x := fevalHS (x − st x) (T (st x))`** — the extension of a jet family to the finite
  galaxy; `extJ_realCast` (the constant term at reals), `isFinite_extJ`,
  **`hasDerivS_extJ : IsFinite x → HasDerivS (extJ T) x (extJ (fun r ↦ derivative (T r)) x)`**,
  `hasDerivS_extJ_iterate`; the algebra `extJ_add/neg/sub/mul/smul/C/zero` (`fevalHom` is a ring
  homomorphism).

## The extension of a real function

* **`taylorJet f r := mk (fun n ↦ iteratedDeriv n f r / n!)`** for ANY `f : ℝ → ℝ` (`iteratedDeriv`
  is total), and **`taylorJet_deriv : derivative (taylorJet f r) = taylorJet (deriv f) r`** —
  unconditional, from mathlib's unconditional `iteratedDeriv_succ'`.
* **`extC f := extJ (taylorJet f)`**, `extC_realCast : extC f r = f r`, `isFinite_extC`, and the
  headline **`hasDerivS_extC : IsFinite x → HasDerivS (extC f) x (extC (deriv f) x)`** for EVERY
  `f : ℝ → ℝ` (meaningful for smooth `f`; for a `C¹` function the higher jets are mathlib's junk
  zeros and the statement is still exactly right), `hasDerivS_extC_iterate`,
  `eq_extC_deriv_of_hasDerivS` (uniqueness of the derivative).
* Germ locality `extC_congr` (`f =ᶠ[𝓝 (st x)] g → extC f x = extC g x`); the algebra of extended
  functions: `extC_const_mul`, `extC_sub_const` (no hypotheses), `extC_add`, **`extC_mul`**
  (the Leibniz rule for `iteratedDeriv`, smooth `f, g`); polynomials: **`extC_polynomial`**
  (`extC (p.eval) x = p.eval₂ realHom x` at finite `x`, via `Polynomial.taylor` and `hasseDeriv`).

## THE FUNDAMENTAL THEOREM OF CALCULUS

* `prim f t := ∫₀ᵗ f` and **`integralC f a b := extC (prim f) b − extC (prim f) a`**.
* **FTC I** — `hasDerivS_integralC : Continuous f → IsFinite x →
  HasDerivS (fun y ↦ integralC f a y) x (extC f x)`: the integral is differentiable at every
  finite point with the extension of the integrand as its derivative.
* **FTC II** — `integralC_eq_of_hasDerivAt : Continuous f → (∀ t, HasDerivAt G (f t) t) →
  integralC f a b = extC G b − extC G a` (all surreal `a, b`): the primitive is `G − G 0`
  (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) and constants pass through the extension.
* **Uniqueness on the class** — `integralC_unique`: any operator satisfying FTC II for continuous
  integrands is `integralC` (structural uniqueness in the mold of `ExpIntegral.integralE_unique`);
  `integralC_unique'` (existential form). Also `integralC_same`, `integralC_symm`,
  `integralC_add_adjacent`, `integralC_const_mul` (no hypotheses), `integralC_add` (smooth
  integrands; `contDiff_prim`), **`integralC_realCast`** (agreement with the real interval
  integral at real endpoints), **`integralC_polynomial`** (agreement with `Integral.integral` for
  polynomial integrands at finite endpoints), and the local form `integralC_eq_of_stdPart_eq`.

## Showcases

* **The exponential**: `taylorJet_exp`, **`extC_exp : extC Real.exp x = expFinH x`** (at every
  `x`: the jet extension of the real exponential *is* the faithful exponential of
  `FaithfulExp.lean`), `hasDerivS_extC_exp` (`exp′ = exp` re-derived from the general theorem),
  **`integralC_exp : ∫ₐᵇ eˣ = expFinH b − expFinH a`**, **`integralC_exp_zero : ∫₀^ε eˣ = expH ε − 1`**.
  Contrast `ScaleCalculus.kernel_exponential` and `Norton.lean`: no canonical-sum extension of
  `exp` satisfies FTC I off the reals (the canonical derivative of `expInf` at a nonzero
  infinitesimal is `0`), and Norton's genetic integral overshoots by exactly `1`.
* **The flat function** (the Costin–Ehrlich–Friedman obstruction in miniature):
  `iteratedDeriv_eq_zero_of_eqOn_Iic` (a smooth `g` vanishing on `(−∞, 0]` has all derivatives
  `0` at `0`), **`extC_eq_zero_of_eqOn_Iic : extC g ε = 0`** for every infinitesimal `ε`,
  `extC_expNegInvGlue`, **`not_orderFaithful_extC`** (`expNegInvGlue > 0` on `(0, ∞)` yet its
  extension vanishes at every positive infinitesimal), `integralC_expNegInvGlue`
  (`∫₀^ε e^{−1/x} = 0`): the extension of a smooth function sees its jet, not its germ.
* **The logarithm**: `taylorJet_log_one : taylorJet Real.log 1 = log ℝ`,
  **`extC_log : extC Real.log (1 + ε) = logH1p ε`** (the jet extension of the real logarithm is the
  faithful logarithm of `JetCalculus.lean`), `extC_inv : extC (·⁻¹) (1 + ε) = (1 + ε)⁻¹`,
  `hasDerivS_extC_log` (`log′ = 1/x` re-derived), **`integralC_eq_logH1p : ∫₁^{1+ε} dt/t = logH1p ε`**
  for every continuous integrand agreeing with `t⁻¹` near `1` (`integralC_inv_max` for the
  concrete integrand `(max t ½)⁻¹`; `t ↦ t⁻¹` itself is not continuous on `ℝ`, so `prim` of it is
  junk — the local FTC II `integralC_eq_of_stdPart_eq` is the honest statement).
-/

open ArchimedeanClass
open scoped ContDiff

universe u

noncomputable section

namespace Surreal

/-! ### Jet families and the extension operator -/

/-- **The extension of a jet family** `T : ℝ → PowerSeries ℝ` to the finite galaxy:
`extJ T x := fevalHS (x − st x) (T (st x))` — the jet prescribed at the standard part of `x`,
evaluated faithfully at the infinitesimal part of `x`. A total function; honest on finite `x`
(where `x − st x` is infinitesimal), junk elsewhere. -/
def extJ (T : ℝ → PowerSeries ℝ) (x : Surreal.{u}) : Surreal.{u} :=
  fevalHS (x - (stdPart x : Surreal)) (T (stdPart x))

theorem extJ_apply (T : ℝ → PowerSeries ℝ) (x : Surreal.{u}) :
    extJ T x = fevalHS (x - (stdPart x : Surreal)) (T (stdPart x)) := rfl

/-- On the halo of a real `r`, `extJ T` is the jet function of `T r` centred at `r`. -/
theorem extJ_eq_jet (T : ℝ → PowerSeries ℝ) (x : Surreal.{u}) :
    extJ T x = jet (T (stdPart x)) (stdPart x : Surreal) x := rfl

/-- At a real point the extension is the constant term of the jet there. -/
theorem extJ_realCast (T : ℝ → PowerSeries ℝ) (r : ℝ) :
    extJ T (r : Surreal.{u}) = ((PowerSeries.coeff 0 (T r) : ℝ) : Surreal) := by
  rw [extJ_apply, stdPart_realCast, sub_self, fevalHS_zero_left,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem isFinite_extJ (T : ℝ → PowerSeries ℝ) {x : Surreal.{u}} (hx : IsFinite x) :
    IsFinite (extJ T x) :=
  isFinite_fevalHS (infinitesimal_sub_stdPart hx) _

/-- An infinitesimal increment does not move the standard part, so on the halo of `x` the
extension is the single jet function `jet (T (st x)) (st x)`. -/
theorem extJ_add_infinitesimal (T : ℝ → PowerSeries ℝ) (x : Surreal.{u}) {δ : Surreal.{u}}
    (hδ : Infinitesimal δ) :
    extJ T (x + δ) = jet (T (stdPart x)) (stdPart x : Surreal) (x + δ) := by
  rw [extJ_eq_jet, stdPart_add_eq_left hδ]

/-- **DIFFERENTIABILITY OF THE EXTENSION AT EVERY FINITE POINT**: `extJ T` has surreal-point
derivative `extJ T′ x` at every finite `x`, where `T′ r := derivative (T r)` is the jet family of
formal derivatives. (`hasDerivS_jet'` on the halo of `st x`, transported by `congr_halo`.) -/
theorem hasDerivS_extJ (T : ℝ → PowerSeries ℝ) {x : Surreal.{u}} (hx : IsFinite x) :
    HasDerivS (extJ T) x (extJ (fun r ↦ PowerSeries.derivative ℝ (T r)) x) :=
  (hasDerivS_jet' (T (stdPart x)) (stdPart x : Surreal) (infinitesimal_sub_stdPart hx)).congr_halo
    fun _ hδ ↦ extJ_add_infinitesimal T x hδ

/-- Higher derivatives of the extension: the `j`-th derivative family is differentiable with
derivative the `(j+1)`-st. -/
theorem hasDerivS_extJ_iterate (T : ℝ → PowerSeries ℝ) (j : ℕ) {x : Surreal.{u}}
    (hx : IsFinite x) :
    HasDerivS (extJ fun r ↦ (PowerSeries.derivative ℝ)^[j] (T r)) x
      (extJ (fun r ↦ (PowerSeries.derivative ℝ)^[j + 1] (T r)) x) := by
  simp only [Function.iterate_succ_apply']
  exact hasDerivS_extJ (fun r ↦ (PowerSeries.derivative ℝ)^[j] (T r)) hx

/-! #### The algebra of extended jet families -/

theorem extJ_add (T U : ℝ → PowerSeries ℝ) (x : Surreal.{u}) :
    extJ (T + U) x = extJ T x + extJ U x := by
  rw [extJ_apply, extJ_apply, extJ_apply, Pi.add_apply, fevalHS_add]

theorem extJ_neg (T : ℝ → PowerSeries ℝ) (x : Surreal.{u}) : extJ (-T) x = -extJ T x := by
  rw [extJ_apply, extJ_apply, Pi.neg_apply, fevalHS_neg]

theorem extJ_sub (T U : ℝ → PowerSeries ℝ) (x : Surreal.{u}) :
    extJ (T - U) x = extJ T x - extJ U x := by
  rw [extJ_apply, extJ_apply, extJ_apply, Pi.sub_apply, fevalHS_sub]

/-- Products: the extension is multiplicative (`fevalHom` is a ring homomorphism). -/
theorem extJ_mul (T U : ℝ → PowerSeries ℝ) (x : Surreal.{u}) :
    extJ (T * U) x = extJ T x * extJ U x := by
  rw [extJ_apply, extJ_apply, extJ_apply, Pi.mul_apply, fevalHS_mul]

theorem extJ_smul (c : ℝ) (T : ℝ → PowerSeries ℝ) (x : Surreal.{u}) :
    extJ (c • T) x = (c : Surreal) * extJ T x := by
  rw [extJ_apply, extJ_apply, Pi.smul_apply, PowerSeries.smul_eq_C_mul, fevalHS_C_mul]

theorem extJ_const (T : PowerSeries ℝ) (x : Surreal.{u}) :
    extJ (fun _ ↦ T) x = jet T (stdPart x : Surreal) x := rfl

theorem extJ_C (c : ℝ) (x : Surreal.{u}) : extJ (fun _ ↦ PowerSeries.C c) x = (c : Surreal) := by
  rw [extJ_apply, fevalHS_C]

theorem extJ_zero (x : Surreal.{u}) : extJ 0 x = 0 := by
  rw [extJ_apply, Pi.zero_apply, fevalHS_zero]

/-! ### The extension of a real function through its Taylor jets -/

/-- **The Taylor jet** of `f : ℝ → ℝ` at `r`: the formal power series
`Σ_n f⁽ⁿ⁾(r)/n! · Xⁿ`. Mathlib's `iteratedDeriv` is total, so this is defined for every function;
it is the honest Taylor series of `f` at `r` exactly when the derivatives are honest. -/
def taylorJet (f : ℝ → ℝ) (r : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n ↦ iteratedDeriv n f r / n.factorial

theorem coeff_taylorJet (f : ℝ → ℝ) (r : ℝ) (n : ℕ) :
    PowerSeries.coeff n (taylorJet f r) = iteratedDeriv n f r / n.factorial :=
  PowerSeries.coeff_mk _ _

theorem coeff_zero_taylorJet (f : ℝ → ℝ) (r : ℝ) :
    PowerSeries.coeff 0 (taylorJet f r) = f r := by
  rw [coeff_taylorJet, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]

/-- **The formal derivative of the Taylor jet is the Taylor jet of the derivative** — for every
`f : ℝ → ℝ`, with no regularity hypothesis, because `iteratedDeriv_succ'` is unconditional. -/
theorem taylorJet_deriv (f : ℝ → ℝ) (r : ℝ) :
    PowerSeries.derivative ℝ (taylorJet f r) = taylorJet (deriv f) r := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_taylorJet, coeff_taylorJet, iteratedDeriv_succ',
    Nat.factorial_succ]
  have h1 : ((n : ℝ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have h2 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  push_cast
  field_simp

theorem taylorJet_iterate_deriv (f : ℝ → ℝ) (r : ℝ) (j : ℕ) :
    (PowerSeries.derivative ℝ)^[j] (taylorJet f r) = taylorJet (deriv^[j] f) r := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, taylorJet_deriv, Function.iterate_succ_apply']

/-- **THE EXTENSION OF A REAL FUNCTION** to the finite galaxy: `extC f := extJ (taylorJet f)`,
i.e. `extC f x = Σ_n f⁽ⁿ⁾(st x)/n! · (x − st x)ⁿ` evaluated faithfully. Total in `f` and `x`;
it is the analytic continuation of `f` into the halo of each real point when `f` is analytic
there, and in general the "jet continuation" — for a `C¹` function whose higher derivatives are
mathlib's junk zeros it is `f (st x) + f′(st x)(x − st x)`. -/
def extC (f : ℝ → ℝ) : Surreal.{u} → Surreal.{u} :=
  extJ (taylorJet f)

theorem extC_apply (f : ℝ → ℝ) (x : Surreal.{u}) :
    extC f x = fevalHS (x - (stdPart x : Surreal)) (taylorJet f (stdPart x)) := rfl

/-- The extension restricts to `f` on the reals. -/
theorem extC_realCast (f : ℝ → ℝ) (r : ℝ) : extC f (r : Surreal.{u}) = (f r : Surreal) := by
  rw [extC, extJ_realCast, coeff_zero_taylorJet]

theorem isFinite_extC (f : ℝ → ℝ) {x : Surreal.{u}} (hx : IsFinite x) : IsFinite (extC f x) :=
  isFinite_extJ _ hx

/-- **THE EXTENSION IS DIFFERENTIABLE AT EVERY FINITE POINT, WITH THE EXTENSION OF THE
DERIVATIVE AS ITS DERIVATIVE**: for every `f : ℝ → ℝ` and every finite `x`,
`HasDerivS (extC f) x (extC (deriv f) x)`. No hypothesis on `f`: `iteratedDeriv` and `deriv` are
total, and the identity `derivative (taylorJet f r) = taylorJet (deriv f) r` is unconditional, so
the theorem holds for arbitrary functions and is *meaningful* for smooth ones (for `C¹` functions
the higher jets are junk zeros and the statement is still exactly right). -/
theorem hasDerivS_extC (f : ℝ → ℝ) {x : Surreal.{u}} (hx : IsFinite x) :
    HasDerivS (extC f) x (extC (deriv f) x) := by
  have h := hasDerivS_extJ (taylorJet f) hx
  simp only [taylorJet_deriv] at h
  exact h

/-- Higher derivatives: `extC (deriv^[n] f)` is differentiable at every finite point with
derivative `extC (deriv^[n+1] f)`. -/
theorem hasDerivS_extC_iterate (f : ℝ → ℝ) (n : ℕ) {x : Surreal.{u}} (hx : IsFinite x) :
    HasDerivS (extC (deriv^[n] f)) x (extC (deriv^[n + 1] f) x) := by
  rw [Function.iterate_succ_apply']
  exact hasDerivS_extC _ hx

/-- The derivative of the extension is the unique surreal-point derivative (`HasDerivS.unique`):
any candidate derivative of `extC f` at a finite point is `extC (deriv f) x`. -/
theorem eq_extC_deriv_of_hasDerivS (f : ℝ → ℝ) {x d : Surreal.{u}} (hx : IsFinite x)
    (h : HasDerivS (extC f) x d) : d = extC (deriv f) x :=
  h.unique (hasDerivS_extC f hx)


/-! ### Germ locality and the algebra of extended functions -/

/-- **Germ locality**: the extension of `f` at `x` depends only on the germ of `f` at `st x`. -/
theorem taylorJet_congr {f g : ℝ → ℝ} {r : ℝ} (h : f =ᶠ[nhds r] g) :
    taylorJet f r = taylorJet g r := by
  ext n
  rw [coeff_taylorJet, coeff_taylorJet, h.iteratedDeriv_eq n]

theorem extC_congr {f g : ℝ → ℝ} {x : Surreal.{u}} (h : f =ᶠ[nhds (stdPart x)] g) :
    extC f x = extC g x := by
  rw [extC_apply, extC_apply, taylorJet_congr h]

theorem taylorJet_const_mul (c : ℝ) (f : ℝ → ℝ) (r : ℝ) :
    taylorJet (fun t ↦ c * f t) r = PowerSeries.C c * taylorJet f r := by
  ext n
  rw [PowerSeries.coeff_C_mul, coeff_taylorJet, coeff_taylorJet, iteratedDeriv_const_mul_field,
    mul_div_assoc]

/-- Real scalars come out of the extension, for every `f` (no regularity needed). -/
theorem extC_const_mul (c : ℝ) (f : ℝ → ℝ) (x : Surreal.{u}) :
    extC (fun t ↦ c * f t) x = (c : Surreal) * extC f x := by
  rw [extC_apply, extC_apply, taylorJet_const_mul, fevalHS_C_mul]

theorem taylorJet_sub_const (G : ℝ → ℝ) (c r : ℝ) :
    taylorJet (fun t ↦ G t - c) r = taylorJet G r - PowerSeries.C c := by
  ext n
  rw [map_sub, coeff_taylorJet, coeff_taylorJet, PowerSeries.coeff_C]
  rcases n with _ | n
  · simp [iteratedDeriv_zero]
  · have h : (fun t ↦ G t - c) = fun t ↦ (-c) + G t := funext fun t ↦ by ring
    rw [h, iteratedDeriv_const_add (Nat.succ_pos n)]
    simp

/-- Subtracting a real constant from `f` subtracts it from the extension. -/
theorem extC_sub_const (G : ℝ → ℝ) (c : ℝ) (x : Surreal.{u}) :
    extC (fun t ↦ G t - c) x = extC G x - (c : Surreal) := by
  rw [extC_apply, extC_apply, taylorJet_sub_const, fevalHS_sub, fevalHS_C]

theorem taylorJet_add (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (r : ℝ) :
    taylorJet (f + g) r = taylorJet f r + taylorJet g r := by
  ext n
  rw [map_add, coeff_taylorJet, coeff_taylorJet, coeff_taylorJet,
    iteratedDeriv_add (hf.of_le (by exact_mod_cast le_top)).contDiffAt
      (hg.of_le (by exact_mod_cast le_top)).contDiffAt, add_div]

/-- Sums of smooth functions extend to sums. -/
theorem extC_add {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Surreal.{u}) :
    extC (f + g) x = extC f x + extC g x := by
  rw [extC_apply, extC_apply, extC_apply, taylorJet_add f g hf hg, fevalHS_add]

/-! ### THE FUNDAMENTAL THEOREM OF CALCULUS -/

/-- The real primitive `prim f t := ∫₀ᵗ f`. -/
def prim (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, f s

theorem prim_apply (f : ℝ → ℝ) (t : ℝ) : prim f t = ∫ s in (0 : ℝ)..t, f s := rfl

theorem prim_zero (f : ℝ → ℝ) : prim f 0 = 0 :=
  intervalIntegral.integral_same

theorem hasDerivAt_prim {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    _root_.HasDerivAt (prim f) (f t) t :=
  (hf.integral_hasStrictDerivAt 0 t).hasDerivAt

/-- The real FTC I: `(prim f)′ = f` as functions, for continuous `f`. -/
theorem deriv_prim {f : ℝ → ℝ} (hf : Continuous f) : deriv (prim f) = f :=
  funext fun t ↦ (hasDerivAt_prim hf t).deriv

/-- **THE INTEGRAL ON THE FINITE GALAXY**: `∫ₐᵇ f := extC (prim f) b − extC (prim f) a`, for a
real integrand `f` and surreal endpoints `a, b`. -/
def integralC (f : ℝ → ℝ) (a b : Surreal.{u}) : Surreal.{u} :=
  extC (prim f) b - extC (prim f) a

theorem integralC_apply (f : ℝ → ℝ) (a b : Surreal.{u}) :
    integralC f a b = extC (prim f) b - extC (prim f) a := rfl

/-- **FTC I ON THE FINITE GALAXY**: for continuous `f`, the integral `y ↦ ∫ₐʸ f` has surreal-point
derivative `extC f x` at every finite `x` — the extension of the integrand, exactly as
Newton–Leibniz demands. (Contrast `ScaleCalculus.kernel_exponential` and `Norton.lean`: no
canonical-sum extension can satisfy this off the reals.) -/
theorem hasDerivS_integralC {f : ℝ → ℝ} (hf : Continuous f) (a : Surreal.{u}) {x : Surreal.{u}}
    (hx : IsFinite x) :
    HasDerivS (fun y ↦ integralC f a y) x (extC f x) := by
  have h := (hasDerivS_extC (prim f) hx).sub_const (extC (prim f) a)
  rwa [deriv_prim hf] at h

/-- For continuous `f`, the primitive is any global antiderivative minus its value at `0`. -/
theorem prim_eq_of_hasDerivAt {f G : ℝ → ℝ} (hf : Continuous f)
    (hG : ∀ t, _root_.HasDerivAt G (f t) t) : prim f = fun t ↦ G t - G 0 :=
  funext fun t ↦
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hG s) (hf.intervalIntegrable 0 t)

/-- **FTC II ON THE FINITE GALAXY**: if `G` is a global antiderivative of the continuous
integrand `f`, then `∫ₐᵇ f = extC G b − extC G a` for all surreal `a, b`. -/
theorem integralC_eq_of_hasDerivAt {f G : ℝ → ℝ} (hf : Continuous f)
    (hG : ∀ t, _root_.HasDerivAt G (f t) t) (a b : Surreal.{u}) :
    integralC f a b = extC G b - extC G a := by
  rw [integralC_apply, prim_eq_of_hasDerivAt hf hG, extC_sub_const G (G 0) b,
    extC_sub_const G (G 0) a]
  ring

/-- **UNIQUENESS OF THE INTEGRAL ON THE CLASS**: any operator on integrands and surreal endpoints
that satisfies FTC II for continuous integrands — `I f a b = extC G b − extC G a` whenever `G` is a
global antiderivative of `f` — agrees with `integralC` on every continuous `f`. (Structural
uniqueness in the mold of `ExpIntegral.integralE_unique`.) -/
theorem integralC_unique {I : (ℝ → ℝ) → Surreal.{u} → Surreal.{u} → Surreal.{u}}
    (hI : ∀ (f G : ℝ → ℝ), Continuous f → (∀ t, _root_.HasDerivAt G (f t) t) →
      ∀ a b, I f a b = extC G b - extC G a)
    {f : ℝ → ℝ} (hf : Continuous f) (a b : Surreal.{u}) : I f a b = integralC f a b :=
  hI f (prim f) hf (hasDerivAt_prim hf) a b

/-- Uniqueness, existential form: if for every continuous `f` and every `a` the operator is
given by *some* antiderivative through FTC II, it is `integralC`. -/
theorem integralC_unique' {I : (ℝ → ℝ) → Surreal.{u} → Surreal.{u} → Surreal.{u}}
    (hI : ∀ (f : ℝ → ℝ), Continuous f → ∀ a, ∃ G : ℝ → ℝ, (∀ t, _root_.HasDerivAt G (f t) t) ∧
      ∀ b, I f a b = extC G b - extC G a)
    {f : ℝ → ℝ} (hf : Continuous f) (a b : Surreal.{u}) : I f a b = integralC f a b := by
  obtain ⟨G, hG, hIG⟩ := hI f hf a
  rw [hIG b]
  exact (integralC_eq_of_hasDerivAt hf hG a b).symm

/-! #### The elementary properties -/

theorem integralC_same (f : ℝ → ℝ) (a : Surreal.{u}) : integralC f a a = 0 :=
  sub_self _

theorem integralC_symm (f : ℝ → ℝ) (a b : Surreal.{u}) : integralC f b a = -integralC f a b := by
  rw [integralC_apply, integralC_apply]
  ring

/-- Interval additivity. -/
theorem integralC_add_adjacent (f : ℝ → ℝ) (a b c : Surreal.{u}) :
    integralC f a b + integralC f b c = integralC f a c := by
  simp only [integralC_apply]
  ring

theorem prim_const_mul (c : ℝ) (f : ℝ → ℝ) : prim (fun t ↦ c * f t) = fun t ↦ c * prim f t :=
  funext fun _ ↦ intervalIntegral.integral_const_mul c f

/-- Real scalars come out of the integral (no hypothesis on `f`). -/
theorem integralC_const_mul (c : ℝ) (f : ℝ → ℝ) (a b : Surreal.{u}) :
    integralC (fun t ↦ c * f t) a b = (c : Surreal) * integralC f a b := by
  rw [integralC_apply, integralC_apply, prim_const_mul, extC_const_mul, extC_const_mul]
  ring

theorem differentiable_prim {f : ℝ → ℝ} (hf : Continuous f) : Differentiable ℝ (prim f) :=
  fun t ↦ (hasDerivAt_prim hf t).differentiableAt

/-- The primitive of a smooth function is smooth. -/
theorem contDiff_prim {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (prim f) := by
  rw [contDiff_infty_iff_deriv, deriv_prim hf.continuous]
  exact ⟨differentiable_prim hf.continuous, hf⟩

theorem prim_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    prim (f + g) = prim f + prim g :=
  funext fun t ↦ by
    rw [Pi.add_apply, prim_apply, prim_apply, prim_apply]
    exact intervalIntegral.integral_add (hf.intervalIntegrable 0 t) (hg.intervalIntegrable 0 t)

/-- Additivity in the integrand, for smooth integrands. -/
theorem integralC_add {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (a b : Surreal.{u}) : integralC (f + g) a b = integralC f a b + integralC g a b := by
  simp only [integralC_apply]
  rw [prim_add hf.continuous hg.continuous, extC_add (contDiff_prim hf) (contDiff_prim hg),
    extC_add (contDiff_prim hf) (contDiff_prim hg)]
  ring

/-- **Agreement with the real integral**: at real endpoints, `integralC` is the interval integral. -/
theorem integralC_realCast {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    integralC f (a : Surreal.{u}) (b : Surreal.{u}) = ((∫ s in a..b, f s : ℝ) : Surreal) := by
  rw [integralC_apply, extC_realCast, extC_realCast, ← Real.toSurreal_sub, prim_apply, prim_apply,
    intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable 0 b)
      (hf.intervalIntegrable 0 a)]


/-! ### SHOWCASE I: the exponential -/

/-- The Taylor jet of `exp` at `r` is `e^r · exp`. -/
theorem taylorJet_exp (r : ℝ) :
    taylorJet Real.exp r = PowerSeries.C (Real.exp r) * PowerSeries.exp ℝ := by
  ext n
  rw [PowerSeries.coeff_C_mul, coeff_taylorJet, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    PowerSeries.coeff_exp]
  simp [div_eq_mul_inv]

/-- **CONSISTENCY WITH THE FAITHFUL EXPONENTIAL**: the jet extension of the real exponential is
`expFinH` — at every surreal `x`, not only finite ones (both sides are the same junk elsewhere). -/
theorem extC_exp (x : Surreal.{u}) : extC Real.exp x = expFinH x := by
  rw [extC_apply, taylorJet_exp, fevalHS_C_mul, expFinH, expH_def]

theorem extC_exp_eq : extC Real.exp = expFinH.{u} :=
  funext extC_exp

/-- `exp′ = exp` on the finite galaxy, re-derived from the general theorem `hasDerivS_extC`
(independently of `FaithfulExp.hasDerivS_expFinH`). -/
theorem hasDerivS_extC_exp {x : Surreal.{u}} (hx : IsFinite x) :
    HasDerivS (extC Real.exp) x (extC Real.exp x) := by
  have h := hasDerivS_extC Real.exp hx
  rwa [Real.deriv_exp] at h

/-- **`∫ₐᵇ eˣ dx = e^b − e^a`** with the faithful exponential, for all surreal `a, b`. -/
theorem integralC_exp (a b : Surreal.{u}) : integralC Real.exp a b = expFinH b - expFinH a := by
  rw [integralC_eq_of_hasDerivAt Real.continuous_exp Real.hasDerivAt_exp, extC_exp, extC_exp]

/-- **`∫₀^ε eˣ dx = expH ε − 1`** for every infinitesimal `ε`. -/
theorem integralC_exp_zero {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    integralC Real.exp 0 ε = expH ε - 1 := by
  rw [integralC_exp, expFinH_of_infinitesimal hε, expFinH_zero]

/-! ### SHOWCASE II: the flat function (the Costin–Ehrlich–Friedman obstruction in miniature) -/

/-- A smooth function vanishing on `(-∞, 0]` has all derivatives zero at `0`: on the open left
half-line every iterated derivative agrees with that of `0`, and iterated derivatives of a smooth
function are continuous, so the agreement extends to the closure. -/
theorem iteratedDeriv_eq_zero_of_eqOn_Iic {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (h0 : ∀ t ≤ 0, g t = 0) (n : ℕ) : iteratedDeriv n g 0 = 0 := by
  have h1 : Set.EqOn (iteratedDeriv n g) (iteratedDeriv n (fun _ : ℝ ↦ (0 : ℝ))) (Set.Iio 0) :=
    Set.EqOn.iteratedDeriv_of_isOpen (fun t ht ↦ h0 t (le_of_lt ht)) isOpen_Iio n
  have h2 := h1.closure (hg.continuous_iteratedDeriv n (by exact_mod_cast le_top))
    (ContDiff.continuous_iteratedDeriv' n contDiff_const)
  rw [closure_Iio] at h2
  rw [h2 (Set.mem_Iic.2 le_rfl), iteratedDeriv_const]
  split_ifs <;> rfl

theorem taylorJet_eq_zero_of_eqOn_Iic {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (h0 : ∀ t ≤ 0, g t = 0) : taylorJet g 0 = 0 := by
  ext n
  rw [coeff_taylorJet, iteratedDeriv_eq_zero_of_eqOn_Iic hg h0, zero_div, map_zero]

/-- **THE FLAT-FUNCTION REMARK**: a smooth `g` vanishing on `(-∞, 0]` extends to `0` on the whole
halo of `0` — whatever it does to the right of `0`. The extension operator on smooth functions
sees only the jet, not the germ: it is not order-faithful. -/
theorem extC_eq_zero_of_eqOn_Iic {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (h0 : ∀ t ≤ 0, g t = 0)
    {ε : Surreal.{u}} (hε : Infinitesimal ε) : extC g ε = 0 := by
  rw [extC_apply, hε.stdPart_eq_zero, Real.toSurreal_zero, sub_zero,
    taylorJet_eq_zero_of_eqOn_Iic hg h0, fevalHS_zero]

theorem taylorJet_expNegInvGlue_zero : taylorJet expNegInvGlue 0 = 0 :=
  taylorJet_eq_zero_of_eqOn_Iic expNegInvGlue.contDiff
    fun _ ht ↦ expNegInvGlue.zero_of_nonpos ht

/-- `expNegInvGlue` (`e^{-1/x}` for `x > 0`, `0` for `x ≤ 0`) extends to `0` on the halo of `0`. -/
theorem extC_expNegInvGlue {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    extC expNegInvGlue ε = 0 :=
  extC_eq_zero_of_eqOn_Iic expNegInvGlue.contDiff
    (fun _ ht ↦ expNegInvGlue.zero_of_nonpos ht) hε

/-- **The extension operator is not order-faithful on smooth functions**: `expNegInvGlue` is
strictly positive on `(0, ∞)` yet its extension vanishes at every positive infinitesimal. -/
theorem not_orderFaithful_extC :
    (∀ t : ℝ, 0 < t → 0 < expNegInvGlue t) ∧
      ∀ ε : Surreal.{u}, Infinitesimal ε → 0 < ε → extC expNegInvGlue ε = 0 :=
  ⟨fun _ ht ↦ expNegInvGlue.pos_of_pos ht, fun _ hε _ ↦ extC_expNegInvGlue hε⟩

theorem prim_eq_zero_of_eqOn_Iic {g : ℝ → ℝ} (h0 : ∀ t ≤ 0, g t = 0) {t : ℝ} (ht : t ≤ 0) :
    prim g t = 0 := by
  rw [prim_apply]
  have h : Set.EqOn g (fun _ ↦ (0 : ℝ)) (Set.uIcc 0 t) := fun s hs ↦ by
    rw [Set.uIcc_of_ge ht] at hs
    exact h0 s hs.2
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_zero]

/-- The integral of the flat function over `[0, ε]` vanishes for every infinitesimal `ε`, although
the integrand is positive on `(0, ε]` when `ε > 0`: the primitive is smooth and flat at `0` too. -/
theorem integralC_eq_zero_of_eqOn_Iic {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (h0 : ∀ t ≤ 0, g t = 0)
    {ε : Surreal.{u}} (hε : Infinitesimal ε) : integralC g 0 ε = 0 := by
  rw [integralC_apply, extC_eq_zero_of_eqOn_Iic (contDiff_prim hg)
    (fun _ ht ↦ prim_eq_zero_of_eqOn_Iic h0 ht) hε, ← Real.toSurreal_zero, extC_realCast,
    prim_zero, Real.toSurreal_zero, sub_zero]

theorem integralC_expNegInvGlue {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    integralC expNegInvGlue 0 ε = 0 :=
  integralC_eq_zero_of_eqOn_Iic expNegInvGlue.contDiff
    (fun _ ht ↦ expNegInvGlue.zero_of_nonpos ht) hε

/-! ### SHOWCASE III: the logarithm -/

theorem iteratedDeriv_log_succ_one (n : ℕ) :
    iteratedDeriv (n + 1) Real.log 1 = (-1) ^ n * n.factorial := by
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  simp

/-- The Taylor jet of `log` at `1` is the series `log (1 + X)`. -/
theorem taylorJet_log_one : taylorJet Real.log 1 = PowerSeries.log ℝ := by
  ext n
  rw [coeff_taylorJet, PowerSeries.coeff_log]
  rcases n with _ | n
  · simp [iteratedDeriv_zero]
  · rw [if_neg (Nat.succ_ne_zero n), iteratedDeriv_log_succ_one, Nat.factorial_succ, eq_ratCast]
    have h1 : ((n : ℝ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have h2 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    push_cast
    field_simp
    ring

/-- **CONSISTENCY WITH THE FAITHFUL LOGARITHM**: `extC Real.log (1 + ε) = logH1p ε`. -/
theorem extC_log {ε : Surreal.{u}} (hε : Infinitesimal ε) : extC Real.log (1 + ε) = logH1p ε := by
  rw [extC_apply, stdPart_add_eq_left hε, stdPart_one, Real.toSurreal_one, add_sub_cancel_left,
    taylorJet_log_one, logH1p_def]

theorem extC_log_one : extC Real.log (1 : Surreal.{u}) = 0 := by
  have h := extC_log (ε := (0 : Surreal.{u})) infinitesimal_zero
  rwa [add_zero, logH1p_zero] at h

/-- The Taylor jet of `x ↦ x⁻¹` at `1` is the geometric series `log′(1 + X)`. -/
theorem taylorJet_inv_one :
    taylorJet Inv.inv 1 = PowerSeries.derivative ℝ (PowerSeries.log ℝ) := by
  rw [← taylorJet_log_one, taylorJet_deriv, Real.deriv_log']

/-- `extC (·⁻¹) (1 + ε) = (1 + ε)⁻¹`. -/
theorem extC_inv {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    extC Inv.inv (1 + ε) = (1 + ε)⁻¹ := by
  rw [extC_apply, stdPart_add_eq_left hε, stdPart_one, Real.toSurreal_one, add_sub_cancel_left,
    taylorJet_inv_one, fevalHS_derivative_log hε]

/-- `log′ = 1/x` on the halo of `1`, re-derived from `hasDerivS_extC`. -/
theorem hasDerivS_extC_log {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    HasDerivS (extC Real.log) (1 + ε) ((1 + ε)⁻¹) := by
  have h := hasDerivS_extC Real.log (isFinite_one.add hε.isFinite)
  rwa [Real.deriv_log', extC_inv hε] at h

/-- The Taylor jet of the primitive of a continuous `f` at `r`: constant term `prim f r`, and
higher terms the jets of any `G` whose derivative agrees with `f` near `r`. -/
theorem taylorJet_prim_eq {f G : ℝ → ℝ} (hf : Continuous f) (r : ℝ)
    (hG : deriv G =ᶠ[nhds r] f) :
    taylorJet (prim f) r = taylorJet G r + PowerSeries.C (prim f r - G r) := by
  ext n
  rcases n with _ | n
  · rw [map_add, coeff_zero_taylorJet, coeff_zero_taylorJet, PowerSeries.coeff_C, if_pos rfl]
    ring
  · rw [map_add, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n), add_zero, coeff_taylorJet,
      coeff_taylorJet, iteratedDeriv_succ', iteratedDeriv_succ', deriv_prim hf,
      hG.iteratedDeriv_eq n]

/-- **FTC II, local form**: for endpoints in the same halo, the integral of a continuous `f` is the
increment of the extension of any local antiderivative `G` (`G′ = f` near the common standard
part). -/
theorem integralC_eq_of_stdPart_eq {f G : ℝ → ℝ} (hf : Continuous f) {a b : Surreal.{u}}
    (hab : stdPart a = stdPart b) (hG : deriv G =ᶠ[nhds (stdPart b)] f) :
    integralC f a b = extC G b - extC G a := by
  simp only [integralC_apply, extC_apply]
  rw [hab, taylorJet_prim_eq hf _ hG]
  simp only [fevalHS_add, fevalHS_C]
  ring

/-- **`∫₁^{1+ε} dt/t = log (1 + ε)`** for every continuous integrand agreeing with `t ↦ t⁻¹` near
`1`, with the faithful logarithm `logH1p`. -/
theorem integralC_eq_logH1p {f : ℝ → ℝ} (hf : Continuous f) (h : f =ᶠ[nhds 1] Inv.inv)
    {ε : Surreal.{u}} (hε : Infinitesimal ε) : integralC f 1 (1 + ε) = logH1p ε := by
  have hab : stdPart (1 : Surreal.{u}) = stdPart (1 + ε) := by rw [stdPart_add_eq_left hε]
  have hG : deriv Real.log =ᶠ[nhds (stdPart (1 + ε))] f := by
    rw [stdPart_add_eq_left hε, stdPart_one, Real.deriv_log']
    exact h.symm
  rw [integralC_eq_of_stdPart_eq hf hab hG, extC_log hε, extC_log_one, sub_zero]

/-- A concrete continuous integrand equal to `1/t` on `(1/2, ∞)`. -/
theorem integralC_inv_max {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    integralC (fun t ↦ (max t (1 / 2))⁻¹) 1 (1 + ε) = logH1p ε := by
  refine integralC_eq_logH1p ?_ ?_ hε
  · refine (continuous_id.max continuous_const).inv₀ fun t ↦ ?_
    exact ne_of_gt (lt_of_lt_of_le one_half_pos (le_max_right _ _))
  · filter_upwards [Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)] with t ht
    exact congrArg Inv.inv (max_eq_left (le_of_lt (Set.mem_Ioi.1 ht)))


/-! ### Products: the Leibniz rule -/

theorem taylorJet_mul {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (r : ℝ) :
    taylorJet (f * g) r = taylorJet f r * taylorJet g r := by
  ext n
  rw [PowerSeries.coeff_mul, coeff_taylorJet,
    iteratedDeriv_mul (hf.of_le (by exact_mod_cast le_top)).contDiffAt
      (hg.of_le (by exact_mod_cast le_top)).contDiffAt,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
  have h2 : ((n - i).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (n - i))
  have h3 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have h4 : ((n.choose i : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hi').ne'
  simp only [coeff_taylorJet]
  rw [← Nat.choose_mul_factorial_mul_factorial hi']
  push_cast
  field_simp

/-- **Products of smooth functions extend to products** (the Leibniz rule): on smooth functions
`extC` is a ring homomorphism into the surreal functions. -/
theorem extC_mul {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Surreal.{u}) :
    extC (f * g) x = extC f x * extC g x := by
  rw [extC_apply, extC_apply, extC_apply, taylorJet_mul hf hg, fevalHS_mul]

/-! ### Polynomials: agreement with `Integral.lean` -/

theorem iteratedDeriv_polynomial_eval (p : Polynomial ℝ) (n : ℕ) (r : ℝ) :
    iteratedDeriv n (fun t ↦ p.eval t) r = (Polynomial.derivative^[n] p).eval r := by
  induction n generalizing p with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have h : deriv (fun t ↦ p.eval t) = fun t ↦ p.derivative.eval t :=
      funext fun t ↦ (Polynomial.hasDerivAt p t).deriv
    rw [h, ih]

/-- The Taylor jet of a polynomial function at `r` is its Taylor expansion `p.comp (X + C r)`. -/
theorem taylorJet_polynomial (p : Polynomial ℝ) (r : ℝ) :
    taylorJet (fun t ↦ p.eval t) r = ((Polynomial.taylor r p : Polynomial ℝ) : PowerSeries ℝ) := by
  ext n
  rw [coeff_taylorJet, Polynomial.coeff_coe, Polynomial.taylor_coeff, iteratedDeriv_polynomial_eval,
    ← Polynomial.factorial_smul_hasseDeriv]
  have h3 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  rw [LinearMap.smul_apply, Polynomial.eval_smul, nsmul_eq_mul]
  field_simp

theorem eval₂_taylor (p : Polynomial ℝ) (r : ℝ) (x : Surreal.{u}) :
    (Polynomial.taylor r p).eval₂ realHom (x - r) = p.eval₂ realHom x := by
  rw [Polynomial.taylor_apply, Polynomial.eval₂_comp, Polynomial.eval₂_add, Polynomial.eval₂_X,
    Polynomial.eval₂_C, realHom_apply, sub_add_cancel]

/-- **The extension of a polynomial function is the polynomial** at every finite point. -/
theorem extC_polynomial (p : Polynomial ℝ) {x : Surreal.{u}} (hx : IsFinite x) :
    extC (fun t ↦ p.eval t) x = p.eval₂ realHom x := by
  rw [extC_apply, taylorJet_polynomial, fevalHS_coe (infinitesimal_sub_stdPart hx), eval₂_taylor]

/-- **Agreement with the polynomial integral** of `Integral.lean` at finite endpoints. -/
theorem integralC_polynomial (p : Polynomial ℝ) {a b : Surreal.{u}} (ha : IsFinite a)
    (hb : IsFinite b) : integralC (fun t ↦ p.eval t) a b = integral p a b := by
  have hG : ∀ t, _root_.HasDerivAt (fun t ↦ (antideriv p).eval t) (p.eval t) t := fun t ↦ by
    have h := Polynomial.hasDerivAt (antideriv p) t
    rwa [derivative_antideriv] at h
  have hc : Continuous fun t ↦ p.eval t :=
    continuous_iff_continuousAt.2 fun t ↦ (Polynomial.hasDerivAt p t).continuousAt
  rw [integralC_eq_of_hasDerivAt hc hG, extC_polynomial _ hb, extC_polynomial _ ha, integral]

end Surreal

end
