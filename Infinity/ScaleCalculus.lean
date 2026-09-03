/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.ScaleEval
import Infinity.ExpDichotomy
import Infinity.GeneralDeriv
import Infinity.KernelSeparation
import Infinity.ExpFin
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Where canonical-sum calculus ends: substitution, differentiability, and the kernel exponential

`Infinity.ScaleEval` made the canonical-sum semantics a ring homomorphism
`scaleEvalHom ε : PowerSeries ℝ →+* Surreal` at every positive infinitesimal scale `ε`. This
file pushes that semantics as far as it goes — and then proves exactly where it stops.

**What still works.**

* **Rescaling** (`scaleEval_realCast_mul`): `scaleEval (r ε) f = scaleEval ε (rescale r f)` for
  real `r > 0`; and the **signed evaluation** `scaleEvalS δ f` at a nonzero infinitesimal `δ` of
  either sign (`scaleEval (−δ) (f(−X))` for `δ < 0`) is again a ring homomorphism
  (`scaleEvalSHom`) with `scaleEvalS δ (exp ℝ) = expInf δ` on both sides (`scaleEvalS_exp`).
* **Substitution** (`scaleEval_subst`): if `X ^ k ∣ g` (`k ≠ 0`) and the inner value
  `η := scaleEval ε g` is a positive infinitesimal of class `mk (ε ^ k)`, then
  `scaleEval ε (f.subst g) = scaleEval η f` — the identification engine run against the
  `η`-scale game, with the residual `f.subst g − (trunc N f).subst g = X^{kN} · (⋯)` giving
  the scale-sum condition and the option gaps `mk (ε ^ M) < mk (η ^ (M + 1))` giving
  cofinality. Corollary `scaleEval_subst_of_coeff_one_pos`: for `g` with `g₀ = 0 < g₁` all
  side conditions are automatic. Every formal identity in mathlib's `PowerSeries.subst`
  therefore transfers to the surreals.
* **Blindness** (`scaleEval_add_eq_of_forall_nsmul_lt`): the scale evaluation at `ε + δ` equals
  the one at `ε` whenever `δ` lies below every power of `ε` — the scale-sum sets coincide.
  This is the blindness theorem of `Infinity.ExpDichotomy` at the level of the semantics
  itself.
* **The canonical jet extension is differentiable at every real point**
  (`hasDerivS_jetExt`): `jetExt f r (r + δ) := scaleEvalS δ f` has surreal-point derivative
  `f₁ = coeff 1 f` at `r`, with the real constant `|f₁| + 4(|f₂| + 1)` — from the **quadratic
  estimate** `abs_scaleEval_sub_le`: `|scaleEval ε f − f₀ − f₁ ε| ≤ (|f₁| + 4(|f₂| + 1)) ε²`,
  since `scaleEval ε f = f₀ + f₁ v + v² · scaleEval ε h` with `v = haloValue ε ε` in the
  deep halo of `ε`. In particular `hasDerivS_jetExt_exp_zero`: the jet of `exp ℝ` has
  derivative `1` at `0`, and it coincides with `expInf'` on the halo of `0`
  (`jetExt_exp_zero_of_infinitesimal`).

**Where it ends: THE KERNEL EXPONENTIAL THEOREM** (`hasDerivS_expInf'_of_ne`,
`hasDerivS_expInf'_iff`, `not_hasDerivS_expInf'_self`, `kernel_exponential`). At every
**nonzero** infinitesimal `σ`, the canonical exponential `expInf'` has surreal-point derivative
**zero** — and only zero, so `exp′ = exp` fails there — while it is not constant
(`expInf'_ne_expInf'_half`). The proof splits the increment `δ` by the class trichotomy: below
every power of `σ` the exponential is blind to `δ` (error `0`); otherwise `mk δ ≤ mk (σ ^ K)`
and an **amplifier** `C` with `C σ ^ k` infinite for every `k` (`exists_forall_lt`, countable
non-cofinality) makes `C δ²` dominate both `|δ|` and `σ²`, so the uniform bound
`|expInf' x − 1 − x| ≤ (3/2) x²` closes the estimate. Thus the canonical exponential is a
**kernel function on the infinitesimals**: the Galaxy/Kernel phenomenon of
`Infinity.GeneralDeriv` and `Infinity.KernelSeparation` is not an artefact of indicator
functions — it is the canonical-sum exponential itself, one scale below its own argument.
The faithful `exp′ = exp` needs normal-form (Hahn-series) evaluation, which sees every
scale.
-/

open ArchimedeanClass Finset

universe u

noncomputable section

namespace Surreal

/-! ### Rescaling: evaluation at `r ε` is evaluation of the rescaled series at `ε` -/

theorem realCast_pow (r : ℝ) (k : ℕ) : ((r ^ k : ℝ) : Surreal.{u}) = (r : Surreal) ^ k :=
  map_pow realHom r k

theorem scaleTerm_realCast_mul (ε : Surreal.{u}) (r : ℝ) (f : PowerSeries ℝ) (k : ℕ) :
    scaleTerm ((r : Surreal) * ε) f k = scaleTerm ε (PowerSeries.rescale r f) k := by
  unfold scaleTerm
  rw [PowerSeries.coeff_rescale, Real.toSurreal_mul, realCast_pow, mul_pow]
  ring

theorem scalePartial_realCast_mul (ε : Surreal.{u}) (r : ℝ) (f : PowerSeries ℝ) (N : ℕ) :
    scalePartial ((r : Surreal) * ε) f N = scalePartial ε (PowerSeries.rescale r f) N := by
  unfold scalePartial partialSum
  exact Finset.sum_congr rfl fun k _ ↦ scaleTerm_realCast_mul ε r f k

/-- The scale sums of `f` at `r ε` are the scale sums of `rescale r f` at `ε` (`r ≠ 0`). -/
theorem isScaleSum_realCast_mul_iff (ε : Surreal.{u}) {r : ℝ} (hr : r ≠ 0) (f : PowerSeries ℝ)
    (z : Surreal.{u}) :
    IsScaleSum ((r : Surreal) * ε) f z ↔ IsScaleSum ε (PowerSeries.rescale r f) z := by
  unfold IsScaleSum
  refine forall_congr' fun N ↦ ?_
  rw [scalePartial_realCast_mul, mul_pow, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_pow,
    mk_realCast hr, nsmul_zero, zero_add]

/-- **The rescaling law**: `scaleEval (r ε) f = scaleEval ε (rescale r f)` for real `r > 0`. -/
theorem scaleEval_realCast_mul {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) {r : ℝ}
    (hr : 0 < r) (f : PowerSeries ℝ) :
    scaleEval ((r : Surreal) * ε) f (infinitesimal_realCast_mul r hε)
        (mul_pos (Real.toSurreal_pos_iff.2 hr) hε0) =
      scaleEval ε (PowerSeries.rescale r f) hε hε0 := by
  rw [scaleEval_eq_iff]
  exact ⟨(isScaleSum_realCast_mul_iff ε hr.ne' f _).2 (isScaleSum_scaleEval hε hε0 _),
    fun w hw ↦ birthday_scaleEval_le hε hε0 ((isScaleSum_realCast_mul_iff ε hr.ne' f w).1 hw)⟩

/-! ### The signed evaluation: both sides of the origin -/

theorem coeff_rescale_neg_one (f : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.rescale (-1 : ℝ) f) = (-1) ^ n * PowerSeries.coeff n f :=
  PowerSeries.coeff_rescale f (-1) n

theorem abs_coeff_rescale_neg_one (f : PowerSeries ℝ) (n : ℕ) :
    |PowerSeries.coeff n (PowerSeries.rescale (-1 : ℝ) f)| = |PowerSeries.coeff n f| := by
  rw [coeff_rescale_neg_one, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

theorem rescale_neg_one_C (r : ℝ) :
    PowerSeries.rescale (-1 : ℝ) (PowerSeries.C r) = PowerSeries.C r := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · rw [h, pow_zero, one_mul]
  · rw [mul_zero]

/-- **The signed scale evaluation** at a nonzero infinitesimal `δ` of either sign:
`scaleEval δ f` for `δ > 0`, and `scaleEval (−δ) (f(−X))` for `δ < 0` (`f(−X)` is
`PowerSeries.rescale (−1) f`, mathlib's `evalNegHom`). -/
def scaleEvalS (δ : Surreal.{u}) (f : PowerSeries ℝ) (hδ : Infinitesimal δ) (hδ0 : δ ≠ 0) :
    Surreal.{u} :=
  if h : 0 < δ then scaleEval δ f hδ h
  else scaleEval (-δ) (PowerSeries.rescale (-1 : ℝ) f) hδ.neg
    (neg_pos.2 (lt_of_le_of_ne (not_lt.1 h) hδ0))

theorem scaleEvalS_of_pos {δ : Surreal.{u}} (hδ : Infinitesimal δ) (hδ0 : 0 < δ)
    (f : PowerSeries ℝ) : scaleEvalS δ f hδ hδ0.ne' = scaleEval δ f hδ hδ0 :=
  dif_pos hδ0

theorem scaleEvalS_of_neg {δ : Surreal.{u}} (hδ : Infinitesimal δ) (hδ0 : δ < 0)
    (f : PowerSeries ℝ) :
    scaleEvalS δ f hδ hδ0.ne =
      scaleEval (-δ) (PowerSeries.rescale (-1 : ℝ) f) hδ.neg (neg_pos.2 hδ0) :=
  dif_neg (not_lt.2 hδ0.le)

theorem scaleEvalS_add {δ : Surreal.{u}} (hδ : Infinitesimal δ) (hδ0 : δ ≠ 0)
    (f g : PowerSeries ℝ) :
    scaleEvalS δ (f + g) hδ hδ0 = scaleEvalS δ f hδ hδ0 + scaleEvalS δ g hδ hδ0 := by
  unfold scaleEvalS
  split_ifs with h
  · exact scaleEval_add hδ h f g
  · rw [map_add, scaleEval_add]

theorem scaleEvalS_mul {δ : Surreal.{u}} (hδ : Infinitesimal δ) (hδ0 : δ ≠ 0)
    (f g : PowerSeries ℝ) :
    scaleEvalS δ (f * g) hδ hδ0 = scaleEvalS δ f hδ hδ0 * scaleEvalS δ g hδ hδ0 := by
  unfold scaleEvalS
  split_ifs with h
  · exact scaleEval_mul hδ h f g
  · rw [map_mul, scaleEval_mul]

theorem scaleEvalS_C {δ : Surreal.{u}} (hδ : Infinitesimal δ) (hδ0 : δ ≠ 0) (r : ℝ) :
    scaleEvalS δ (PowerSeries.C r) hδ hδ0 = (r : Surreal) := by
  unfold scaleEvalS
  split_ifs with h
  · exact scaleEval_C hδ h r
  · rw [rescale_neg_one_C, scaleEval_C]

theorem scaleEvalS_one {δ : Surreal.{u}} (hδ : Infinitesimal δ) (hδ0 : δ ≠ 0) :
    scaleEvalS δ 1 hδ hδ0 = 1 := by
  have h : (1 : PowerSeries ℝ) = PowerSeries.C 1 := (map_one _).symm
  rw [h, scaleEvalS_C, Real.toSurreal_one]

/-- **The signed evaluation is a ring homomorphism** `PowerSeries ℝ →+* Surreal` at every
nonzero infinitesimal. -/
def scaleEvalSHom (δ : Surreal.{u}) (hδ : Infinitesimal δ) (hδ0 : δ ≠ 0) :
    PowerSeries ℝ →+* Surreal.{u} where
  toFun f := scaleEvalS δ f hδ hδ0
  map_one' := scaleEvalS_one hδ hδ0
  map_mul' := scaleEvalS_mul hδ hδ0
  map_zero' := by
    have h : (0 : PowerSeries ℝ) = PowerSeries.C 0 := (map_zero _).symm
    rw [h, scaleEvalS_C, Real.toSurreal_zero]
  map_add' := scaleEvalS_add hδ hδ0

@[simp]
theorem scaleEvalSHom_apply (δ : Surreal.{u}) (hδ : Infinitesimal δ) (hδ0 : δ ≠ 0)
    (f : PowerSeries ℝ) : scaleEvalSHom δ hδ hδ0 f = scaleEvalS δ f hδ hδ0 :=
  rfl

/-- **The exponential is the signed evaluation of `exp ℝ`** at every nonzero infinitesimal,
of either sign. -/
theorem scaleEvalS_exp {δ : Surreal.{u}} (hδ : Infinitesimal δ) (hδ0 : δ ≠ 0) :
    scaleEvalS δ (PowerSeries.exp ℝ) hδ hδ0 = expInf δ hδ hδ0 := by
  unfold scaleEvalS
  split_ifs with h
  · exact (expInf_eq_scaleEval_exp hδ h).symm
  · have hneg : 0 < -δ := neg_pos.2 (lt_of_le_of_ne (not_lt.1 h) hδ0)
    rw [scaleEval_rescale_exp hδ.neg hneg (neg_ne_zero.2 (one_ne_zero (α := ℝ)))]
    exact expInf_congr (by rw [Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul, neg_neg]) _ _ _ _

/-! ### The quadratic estimate for the scale evaluation -/

/-- Every real power series is `f₀ + f₁ X + X² h` with `h₀ = f₂`. -/
theorem exists_eq_C_add_C_mul_X_add_X_sq_mul (f : PowerSeries ℝ) :
    ∃ h : PowerSeries ℝ,
      f = PowerSeries.C (PowerSeries.coeff 0 f) +
          PowerSeries.C (PowerSeries.coeff 1 f) * PowerSeries.X + PowerSeries.X ^ 2 * h ∧
      PowerSeries.coeff 0 h = PowerSeries.coeff 2 f := by
  have hdvd : (PowerSeries.X : PowerSeries ℝ) ^ 2 ∣
      f - PowerSeries.C (PowerSeries.coeff 0 f) -
        PowerSeries.C (PowerSeries.coeff 1 f) * PowerSeries.X := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m <;> simp
  obtain ⟨h, hh⟩ := hdvd
  refine ⟨h, ?_, ?_⟩
  · rw [← hh]; ring
  · have h2 := congrArg (PowerSeries.coeff 2) hh
    rw [PowerSeries.coeff_X_pow_mul'] at h2
    simp at h2
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h2.symm

theorem scalePartial_one (ε : Surreal.{u}) (f : PowerSeries ℝ) :
    scalePartial ε f 1 = ((PowerSeries.coeff 0 f : ℝ) : Surreal) := by
  unfold scalePartial partialSum scaleTerm
  rw [Finset.sum_range_one, pow_zero, mul_one]

/-- The scale evaluation is within `1` of the constant coefficient (`N = 1` of the scale-sum
condition: the residual is at least as fine as `ε`, hence infinitesimal). -/
theorem abs_scaleEval_sub_coeff_zero_lt_one {ε : Surreal.{u}} (hε : Infinitesimal ε)
    (hε0 : 0 < ε) (f : PowerSeries ℝ) :
    |scaleEval ε f hε hε0 - ((PowerSeries.coeff 0 f : ℝ) : Surreal)| < 1 := by
  have h1 := isScaleSum_scaleEval hε hε0 f 1
  rw [pow_one, scalePartial_one] at h1
  have h2 : Infinitesimal (scaleEval ε f hε hε0 - ((PowerSeries.coeff 0 f : ℝ) : Surreal)) :=
    lt_of_lt_of_le hε h1
  have h3 := infinitesimal_iff.1 h2 1
  rwa [one_nsmul] at h3

/-- **The quadratic estimate**: `|scaleEval ε f − f₀ − f₁ ε| ≤ (|f₁| + 4(|f₂| + 1)) ε²` for
every positive infinitesimal `ε`, with a real constant independent of `ε`. Proof:
`scaleEval ε f = f₀ + f₁ v + v² · scaleEval ε h` with `v = haloValue ε ε` (`f = f₀ + f₁ X +
X² h`, ring homomorphism); `|v − ε| < ε²` and `|v| ≤ 2 ε` (deep halo), and
`|scaleEval ε h| ≤ |f₂| + 1`. -/
theorem abs_scaleEval_sub_le {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (f : PowerSeries ℝ) :
    |scaleEval ε f hε hε0 - ((PowerSeries.coeff 0 f : ℝ) : Surreal) -
        ((PowerSeries.coeff 1 f : ℝ) : Surreal) * ε| ≤
      (|((PowerSeries.coeff 1 f : ℝ) : Surreal)| +
        4 * (|((PowerSeries.coeff 2 f : ℝ) : Surreal)| + 1)) * ε ^ 2 := by
  obtain ⟨h, hf, hh⟩ := exists_eq_C_add_C_mul_X_add_X_sq_mul f
  have hev : scaleEval ε f hε hε0 =
      ((PowerSeries.coeff 0 f : ℝ) : Surreal) +
        ((PowerSeries.coeff 1 f : ℝ) : Surreal) * haloValue ε ε hε0 +
        haloValue ε ε hε0 ^ 2 * scaleEval ε h hε hε0 := by
    conv_lhs => rw [hf]
    rw [scaleEval_add, scaleEval_add, scaleEval_C, scaleEval_mul, scaleEval_C, scaleEval_X,
      scaleEval_mul, scaleEval_pow, scaleEval_X]
  have hD := deepHalo_haloValue hε hε0 ε
  have hv1 : |haloValue ε ε hε0 - ε| < ε ^ 2 := hD.abs_sub_lt hε0 2
  have hv2 : |haloValue ε ε hε0 - ε| < ε := by
    have := hD.abs_sub_lt hε0 1
    rwa [pow_one] at this
  have hv3 : |haloValue ε ε hε0| ≤ 2 * ε := by
    have := abs_lt.1 hv2
    rw [abs_le]
    constructor <;> linarith
  have hh1 := abs_scaleEval_sub_coeff_zero_lt_one hε hε0 h
  rw [hh] at hh1
  have hh2 : |scaleEval ε h hε hε0| ≤ |((PowerSeries.coeff 2 f : ℝ) : Surreal)| + 1 := by
    have h1 := abs_lt.1 hh1
    have h2 := le_abs_self ((PowerSeries.coeff 2 f : ℝ) : Surreal)
    have h3 := neg_abs_le ((PowerSeries.coeff 2 f : ℝ) : Surreal)
    rw [abs_le]
    constructor <;> linarith
  have herr : scaleEval ε f hε hε0 - ((PowerSeries.coeff 0 f : ℝ) : Surreal) -
      ((PowerSeries.coeff 1 f : ℝ) : Surreal) * ε =
      ((PowerSeries.coeff 1 f : ℝ) : Surreal) * (haloValue ε ε hε0 - ε) +
        haloValue ε ε hε0 ^ 2 * scaleEval ε h hε hε0 := by
    rw [hev]; ring
  rw [herr]
  calc |((PowerSeries.coeff 1 f : ℝ) : Surreal) * (haloValue ε ε hε0 - ε) +
        haloValue ε ε hε0 ^ 2 * scaleEval ε h hε hε0|
      ≤ |((PowerSeries.coeff 1 f : ℝ) : Surreal)| * |haloValue ε ε hε0 - ε| +
        |haloValue ε ε hε0| ^ 2 * |scaleEval ε h hε hε0| := by
        rw [← abs_mul, ← abs_pow, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ |((PowerSeries.coeff 1 f : ℝ) : Surreal)| * ε ^ 2 +
        (2 * ε) ^ 2 * (|((PowerSeries.coeff 2 f : ℝ) : Surreal)| + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hv1.le (abs_nonneg _))
          (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hv3 2) hh2 (abs_nonneg _)
            (by positivity))
    _ = (|((PowerSeries.coeff 1 f : ℝ) : Surreal)| +
        4 * (|((PowerSeries.coeff 2 f : ℝ) : Surreal)| + 1)) * ε ^ 2 := by ring

/-! ### The canonical jet extension -/

open Classical in
/-- **The canonical jet at the origin**: `δ ↦ scaleEvalS δ f` on nonzero infinitesimals, `f₀`
at `0` (and, as junk, off the halo of `0`). -/
def jetAt (f : PowerSeries ℝ) (δ : Surreal.{u}) : Surreal.{u} :=
  if h : Infinitesimal δ ∧ δ ≠ 0 then scaleEvalS δ f h.1 h.2
  else ((PowerSeries.coeff 0 f : ℝ) : Surreal)

/-- **The canonical jet extension** of the real power series `f` at the real point `r`:
`x ↦ jetAt f (x − r)`, i.e. `r + δ ↦ scaleEvalS δ f` on the halo of `r`. -/
def jetExt (f : PowerSeries ℝ) (r : ℝ) (x : Surreal.{u}) : Surreal.{u} :=
  jetAt f (x - r)

theorem jetAt_of_ne {f : PowerSeries ℝ} {δ : Surreal.{u}} (hδ : Infinitesimal δ) (hδ0 : δ ≠ 0) :
    jetAt f δ = scaleEvalS δ f hδ hδ0 :=
  dif_pos ⟨hδ, hδ0⟩

theorem jetAt_zero (f : PowerSeries ℝ) :
    jetAt f (0 : Surreal.{u}) = ((PowerSeries.coeff 0 f : ℝ) : Surreal) :=
  dif_neg fun h ↦ h.2 rfl

theorem jetExt_add_of_ne (f : PowerSeries ℝ) (r : ℝ) {δ : Surreal.{u}} (hδ : Infinitesimal δ)
    (hδ0 : δ ≠ 0) : jetExt f r ((r : Surreal) + δ) = scaleEvalS δ f hδ hδ0 := by
  rw [jetExt, add_sub_cancel_left, jetAt_of_ne hδ hδ0]

theorem jetExt_self (f : PowerSeries ℝ) (r : ℝ) :
    jetExt f r (r : Surreal.{u}) = ((PowerSeries.coeff 0 f : ℝ) : Surreal) := by
  rw [jetExt, sub_self, jetAt_zero]

/-- **THE CANONICAL JET EXTENSION IS DIFFERENTIABLE AT EVERY REAL POINT**, with the formal
derivative `f₁ = coeff 1 f` and the real constant `|f₁| + 4(|f₂| + 1)`: the quadratic estimate
on the positive side, and on the negative side the same estimate for `f(−X)` at `−δ`, whose
coefficients have the same absolute values. -/
theorem hasDerivS_jetExt (f : PowerSeries ℝ) (r : ℝ) :
    HasDerivS (jetExt f r) (r : Surreal.{u}) ((PowerSeries.coeff 1 f : ℝ) : Surreal) := by
  refine ⟨|((PowerSeries.coeff 1 f : ℝ) : Surreal)| +
    4 * (|((PowerSeries.coeff 2 f : ℝ) : Surreal)| + 1), fun δ hδ ↦ ?_⟩
  rw [jetExt_self]
  rcases eq_or_ne δ 0 with rfl | hδ0
  · rw [add_zero, jetExt_self]
    simp
  rw [jetExt_add_of_ne f r hδ hδ0]
  rcases lt_or_gt_of_ne hδ0 with hneg | hpos
  · rw [scaleEvalS_of_neg hδ hneg]
    have key := abs_scaleEval_sub_le hδ.neg (neg_pos.2 hneg) (PowerSeries.rescale (-1 : ℝ) f)
    simp only [coeff_rescale_neg_one, pow_zero, pow_one, one_mul, neg_one_mul,
      Real.toSurreal_neg, abs_neg, neg_mul_neg, neg_sq, one_pow] at key
    exact key
  · rw [scaleEvalS_of_pos hδ hpos]
    exact abs_scaleEval_sub_le hδ hpos f

/-- The canonical jet of `exp ℝ` at the origin **is** the canonical exponential on the halo of
`0`. -/
theorem jetExt_exp_zero_of_infinitesimal {x : Surreal.{u}} (hx : Infinitesimal x) :
    jetExt (PowerSeries.exp ℝ) 0 x = expInf' x := by
  rw [jetExt, Real.toSurreal_zero, sub_zero]
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [jetAt_zero, expInf'_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.constantCoeff_exp, Real.toSurreal_one]
  · rw [jetAt_of_ne hx hx0, scaleEvalS_exp, expInf'_of_ne hx hx0]

/-- The jet of the exponential has derivative `1` at the origin — consistent with
`Infinity.ExpFin.hasDerivS_expFin_realCast`. -/
theorem hasDerivS_jetExt_exp_zero :
    HasDerivS (jetExt (PowerSeries.exp ℝ) 0) (0 : Surreal.{u}) 1 := by
  have h1 : ((PowerSeries.coeff 1 (PowerSeries.exp ℝ) : ℝ) : Surreal.{u}) = 1 := by
    rw [PowerSeries.coeff_exp]
    simp
  have h := hasDerivS_jetExt.{u} (PowerSeries.exp ℝ) 0
  rwa [Real.toSurreal_zero, h1] at h

/-- Two functions agreeing on the halo of `x` have the same derivatives at `x`. -/
theorem HasDerivS.congr_of_forall_infinitesimal {f g : Surreal.{u} → Surreal.{u}}
    {x d : Surreal.{u}} (hfg : ∀ ε, Infinitesimal ε → f (x + ε) = g (x + ε))
    (h : HasDerivS f x d) : HasDerivS g x d := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun ε hε ↦ ?_⟩
  have h0 := hfg 0 infinitesimal_zero
  rw [add_zero] at h0
  rw [← hfg ε hε, ← h0]
  exact hC ε hε


/-! ### Blindness of the scale evaluation -/

/-- The partial sums at `ε + δ` and at `ε` differ by `δ` times a finite quantity. -/
theorem mk_le_mk_scalePartial_add_sub {ε δ : Surreal.{u}} (hε : Infinitesimal ε)
    (hδ : Infinitesimal δ) (f : PowerSeries ℝ) (N : ℕ) :
    ArchimedeanClass.mk δ ≤
      ArchimedeanClass.mk (scalePartial (ε + δ) f N - scalePartial ε f N) := by
  unfold scalePartial partialSum
  rw [← Finset.sum_sub_distrib]
  refine le_mk_sum fun k _ ↦ ?_
  unfold scaleTerm
  rw [← mul_sub, ArchimedeanClass.mk_mul]
  exact le_add_of_nonneg_of_le (isFinite_realCast _) (mk_le_mk_add_pow_sub_pow hε hδ k)

/-- A perturbation below every power of a positive scale keeps the scale positive. -/
theorem add_pos_of_forall_nsmul_lt {ε δ : Surreal.{u}} (hε0 : 0 < ε)
    (hfine : ∀ k : ℕ, k • ArchimedeanClass.mk ε < ArchimedeanClass.mk δ) : 0 < ε + δ := by
  have h := hfine 1
  rw [one_nsmul] at h
  have h2 := abs_lt_abs_of_mk_lt h
  rw [abs_of_pos hε0] at h2
  linarith [(abs_lt.1 h2).1]

/-- **The scale-sum sets are blind below every power of the scale**: if `δ` is strictly finer
than every power of `ε`, the scale sums of `f` at `ε + δ` and at `ε` coincide. -/
theorem isScaleSum_add_iff_of_forall_nsmul_lt {ε δ : Surreal.{u}} (hε : Infinitesimal ε)
    (hδ : Infinitesimal δ)
    (hfine : ∀ k : ℕ, k • ArchimedeanClass.mk ε < ArchimedeanClass.mk δ) (f : PowerSeries ℝ)
    (z : Surreal.{u}) : IsScaleSum (ε + δ) f z ↔ IsScaleSum ε f z := by
  have hμ : ArchimedeanClass.mk (ε + δ) = ArchimedeanClass.mk ε :=
    mk_add_eq_of_forall_nsmul_lt hfine
  unfold IsScaleSum
  refine forall_congr' fun N ↦ ?_
  rw [ArchimedeanClass.mk_pow, ArchimedeanClass.mk_pow, hμ]
  have hdiff : N • ArchimedeanClass.mk ε <
      ArchimedeanClass.mk (scalePartial (ε + δ) f N - scalePartial ε f N) :=
    (hfine N).trans_le (mk_le_mk_scalePartial_add_sub hε hδ f N)
  constructor
  · intro h
    have hs : z - scalePartial ε f N =
        (z - scalePartial (ε + δ) f N) + (scalePartial (ε + δ) f N - scalePartial ε f N) := by
      ring
    rw [hs]
    exact le_trans (le_min h hdiff.le) (ArchimedeanClass.min_le_mk_add _ _)
  · intro h
    have hs : z - scalePartial (ε + δ) f N =
        (z - scalePartial ε f N) - (scalePartial (ε + δ) f N - scalePartial ε f N) := by
      ring
    rw [hs]
    exact le_trans (le_min h hdiff.le) (ArchimedeanClass.min_le_mk_sub _ _)

/-- **BLINDNESS OF THE SCALE EVALUATION**: `scaleEval (ε + δ) f = scaleEval ε f` whenever `δ`
is strictly finer than every power of `ε` — the semantics cannot see below its own scale. -/
theorem scaleEval_add_eq_of_forall_nsmul_lt {ε δ : Surreal.{u}} (hε : Infinitesimal ε)
    (hε0 : 0 < ε) (hδ : Infinitesimal δ)
    (hfine : ∀ k : ℕ, k • ArchimedeanClass.mk ε < ArchimedeanClass.mk δ) (f : PowerSeries ℝ) :
    scaleEval (ε + δ) f (hε.add hδ) (add_pos_of_forall_nsmul_lt hε0 hfine) =
      scaleEval ε f hε hε0 := by
  rw [scaleEval_eq_iff]
  exact ⟨(isScaleSum_add_iff_of_forall_nsmul_lt hε hδ hfine f _).2 (isScaleSum_scaleEval hε hε0 f),
    fun w hw ↦ birthday_scaleEval_le hε hε0
      ((isScaleSum_add_iff_of_forall_nsmul_lt hε hδ hfine f w).1 hw)⟩

/-- The blindness theorem for the exponential, re-derived from the semantics. -/
theorem expInf_add_eq_of_forall_nsmul_lt' {ε δ : Surreal.{u}} (hε : Infinitesimal ε)
    (hε0 : 0 < ε) (hδ : Infinitesimal δ)
    (hfine : ∀ k : ℕ, k • ArchimedeanClass.mk ε < ArchimedeanClass.mk δ) :
    expInf (ε + δ) (hε.add hδ) (add_pos_of_forall_nsmul_lt hε0 hfine).ne' =
      expInf ε hε hε0.ne' := by
  rw [expInf_eq_scaleEval_exp (hε.add hδ) (add_pos_of_forall_nsmul_lt hε0 hfine),
    expInf_eq_scaleEval_exp hε hε0, scaleEval_add_eq_of_forall_nsmul_lt hε hε0 hδ hfine]

/-! ### Substitution -/

/-- `scaleEval ε (X ^ m · q) = (haloValue ε ε) ^ m · scaleEval ε q`. -/
theorem scaleEval_X_pow_mul {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) (m : ℕ)
    (q : PowerSeries ℝ) :
    scaleEval ε (PowerSeries.X ^ m * q) hε hε0 =
      haloValue ε ε hε0 ^ m * scaleEval ε q hε hε0 := by
  rw [scaleEval_mul, scaleEval_pow, scaleEval_X]

/-- The halo value of `ε` at scale `ε` has the class of `ε`. -/
theorem mk_haloValue_self {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) :
    ArchimedeanClass.mk (haloValue ε ε hε0) = ArchimedeanClass.mk ε := by
  have h := deepHalo_haloValue hε hε0 ε 1
  rw [pow_one] at h
  have hs : haloValue ε ε hε0 = ε + (haloValue ε ε hε0 - ε) := by ring
  rw [hs]
  exact ArchimedeanClass.mk_add_eq_mk_left h

/-- `scaleEval ε (X ^ m · q)` is at least as fine as `ε ^ m`. -/
theorem mk_pow_le_mk_scaleEval_X_pow_mul {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (m : ℕ) (q : PowerSeries ℝ) :
    ArchimedeanClass.mk (ε ^ m) ≤
      ArchimedeanClass.mk (scaleEval ε (PowerSeries.X ^ m * q) hε hε0) := by
  rw [scaleEval_X_pow_mul, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_pow,
    ArchimedeanClass.mk_pow, mk_haloValue_self hε hε0]
  exact le_add_of_nonneg_right (isFinite_scaleEval hε hε0 q)

theorem mk_pow_le_mk_scaleEval_of_X_pow_dvd {ε : Surreal.{u}} (hε : Infinitesimal ε)
    (hε0 : 0 < ε) {g : PowerSeries ℝ} {k : ℕ} (hg : PowerSeries.X ^ k ∣ g) :
    ArchimedeanClass.mk (ε ^ k) ≤ ArchimedeanClass.mk (scaleEval ε g hε hε0) := by
  obtain ⟨g', rfl⟩ := hg
  exact mk_pow_le_mk_scaleEval_X_pow_mul hε hε0 k g'

/-- `X ^ N` divides `f − trunc N f`. -/
theorem X_pow_dvd_sub_trunc (f : PowerSeries ℝ) (N : ℕ) :
    (PowerSeries.X : PowerSeries ℝ) ^ N ∣ f - (PowerSeries.trunc N f : PowerSeries ℝ) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]

/-- **Polynomials substitute**: `scaleEval ε (p(g)) = p(scaleEval ε g)` for every real
polynomial `p` and substitutable `g`. -/
theorem scaleEval_subst_coe {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {g : PowerSeries ℝ} (hg : PowerSeries.HasSubst g) (p : Polynomial ℝ) :
    scaleEval ε ((p : PowerSeries ℝ).subst g) hε hε0 =
      p.eval₂ realHom (scaleEval ε g hε hε0) := by
  rw [PowerSeries.subst_coe hg, Polynomial.aeval_def, ← scaleEvalHom_apply ε hε hε0,
    Polynomial.hom_eval₂, scaleEvalHom_apply]
  congr 1
  refine RingHom.ext fun r ↦ ?_
  rw [RingHom.comp_apply, scaleEvalHom_apply, realHom_apply]
  exact scaleEval_C hε hε0 r

/-- **The substitution residual**: `scaleEval ε (f(g)) − scaleEval ε ((trunc N f)(g))` is at
least as fine as `ε ^ (k N)` when `X ^ k ∣ g`, since `f − trunc N f = X ^ N · h` and so
`f(g) − (trunc N f)(g) = g ^ N · h(g) = X ^ (k N) · (⋯)`. -/
theorem mk_pow_le_mk_scaleEval_subst_sub {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {g : PowerSeries ℝ} {k : ℕ} (hk : k ≠ 0) (hg : PowerSeries.X ^ k ∣ g) (f : PowerSeries ℝ)
    (N : ℕ) :
    ArchimedeanClass.mk (ε ^ (k * N)) ≤ ArchimedeanClass.mk
      (scaleEval ε (f.subst g) hε hε0 -
        scaleEval ε ((PowerSeries.trunc N f : PowerSeries ℝ).subst g) hε hε0) := by
  have hgs : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (PowerSeries.X_dvd_iff.1 ((dvd_pow_self _ hk).trans hg))
  obtain ⟨h, hh⟩ := X_pow_dvd_sub_trunc f N
  rw [← scaleEval_sub, ← PowerSeries.subst_sub hgs, hh, PowerSeries.subst_mul hgs,
    PowerSeries.subst_pow hgs, PowerSeries.subst_X hgs]
  obtain ⟨g', rfl⟩ := hg
  rw [mul_pow, ← pow_mul, mul_assoc]
  exact mk_pow_le_mk_scaleEval_X_pow_mul hε hε0 (k * N) _

/-- **THE SUBSTITUTION THEOREM**: let `ε` be a positive infinitesimal, `X ^ k ∣ g` with
`k ≠ 0`, and suppose the inner value `η := scaleEval ε g` is a positive infinitesimal at least
as coarse as `ε ^ k` (`mk η ≤ mk (ε ^ k)`; the reverse inequality is automatic). Then
`scaleEval ε (f.subst g) = scaleEval η f` for every `f`.

Proof: the identification engine for the `η`-scale game. The value `z = scaleEval ε (f(g))` is
an `η`-scale sum of `f` because `Σ_{j<N} fⱼ ηʲ = scaleEval ε ((trunc N f)(g))` and the residual
is `X ^ (kN) · (⋯)` at scale `ε`, of class `≥ mk (ε ^ (kN)) = N • mk (ε ^ k) ≥ mk (η ^ N)`; and
each option `z ∓ D` of the `ε`-scale game of `f(g)` at index `M` has `mk D ≤ mk (ε ^ M) <
mk (ε ^ (M + 1)) ≤ mk (η ^ (M + 1))`, so it is beaten by the `η`-option at index `M + 1`. -/
theorem scaleEval_subst {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {g : PowerSeries ℝ} {k : ℕ} (hk : k ≠ 0) (hg : PowerSeries.X ^ k ∣ g)
    (hη : Infinitesimal (scaleEval ε g hε hε0)) (hη0 : 0 < scaleEval ε g hε hε0)
    (hηk : ArchimedeanClass.mk (scaleEval ε g hε hε0) ≤ ArchimedeanClass.mk (ε ^ k))
    (f : PowerSeries ℝ) :
    scaleEval ε (f.subst g) hε hε0 = scaleEval (scaleEval ε g hε hε0) f hη hη0 := by
  have hgs : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (PowerSeries.X_dvd_iff.1 ((dvd_pow_self _ hk).trans hg))
  have hkη := mk_pow_le_mk_scaleEval_of_X_pow_dvd hε hε0 hg
  -- (a) the value is an `η`-scale sum of `f`
  have hz : IsScaleSum (scaleEval ε g hε hε0) f (scaleEval ε (f.subst g) hε hε0) := by
    intro N
    rw [scalePartial_eq_eval₂_trunc, ← scaleEval_subst_coe hε hε0 hgs]
    refine le_trans ?_ (mk_pow_le_mk_scaleEval_subst_sub hε hε0 hk hg f N)
    rw [ArchimedeanClass.mk_pow, pow_mul, ArchimedeanClass.mk_pow]
    exact nsmul_le_nsmul_right hηk N
  -- (b) the option gaps
  have hz' : IsScaleSum ε (f.subst g) (scaleEval ε (f.subst g) hε hε0) :=
    isScaleSum_scaleEval hε hε0 _
  have hgap : ∀ M : ℕ, ArchimedeanClass.mk (ε ^ M) <
      ArchimedeanClass.mk (scaleEval ε g hε hε0 ^ (M + 1)) := by
    intro M
    refine (mk_pow_lt_mk_pow_succ hε hε0 M).trans_le ?_
    calc ArchimedeanClass.mk (ε ^ (M + 1))
        ≤ ArchimedeanClass.mk (ε ^ (k * (M + 1))) :=
          mk_pow_le_mk_pow_of_le hε.isFinite
            (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hk))
      _ = (M + 1) • ArchimedeanClass.mk (ε ^ k) := by
          rw [pow_mul, ArchimedeanClass.mk_pow]
      _ ≤ (M + 1) • ArchimedeanClass.mk (scaleEval ε g hε hε0) := nsmul_le_nsmul_right hkη _
      _ = ArchimedeanClass.mk (scaleEval ε g hε hε0 ^ (M + 1)) :=
          (ArchimedeanClass.mk_pow _ _).symm
  haveI := numeric_scaleGame hε hε0 (f.subst g)
  rw [← mk_scaleGame hε hε0 (f.subst g)]
  refine mk_eq_scaleEval_of_moves_le hη hη0 (by rw [mk_scaleGame]; exact hz) ?_ ?_
  · intro a ha
    rw [leftMoves_scaleGame] at ha
    obtain ⟨M, rfl⟩ := ha
    refine ⟨M + 1, ?_⟩
    rw [← Surreal.mk_le_mk, out_eq, out_eq]
    have hD := sub_scaleOptLo_pos hε hε0 hz' M
    have hDmk : ArchimedeanClass.mk
        (scaleEval ε (f.subst g) hε hε0 - scaleOptLo ε (f.subst g) M) <
        ArchimedeanClass.mk (scaleEval ε g hε hε0 ^ (M + 1)) :=
      (mk_sub_scaleOptLo_le hε hε0 hz' M).trans_lt (hgap M)
    have key := sub_le_scaleOptLo_of_mk_lt hz hD hDmk
    rwa [sub_sub_cancel] at key
  · intro b hb
    rw [rightMoves_scaleGame] at hb
    obtain ⟨M, rfl⟩ := hb
    refine ⟨M + 1, ?_⟩
    rw [← Surreal.mk_le_mk, out_eq, out_eq]
    have hD := scaleOptHi_sub_pos hε hε0 hz' M
    have hDmk : ArchimedeanClass.mk
        (scaleOptHi ε (f.subst g) M - scaleEval ε (f.subst g) hε hε0) <
        ArchimedeanClass.mk (scaleEval ε g hε hε0 ^ (M + 1)) :=
      (mk_scaleOptHi_sub_le hε hε0 hz' M).trans_lt (hgap M)
    have key := scaleOptHi_le_add_of_mk_lt hz hD hDmk
    rwa [add_sub_cancel] at key

/-- The value of `X · g'` at `ε` is positive and has the class of `ε` when `g'₀ > 0`
(`haloValue ε ε > 0` and `scaleEval ε g' = g'₀ + infinitesimal > 0`). -/
theorem scaleEval_X_mul_pos_of_coeff_zero_pos {ε : Surreal.{u}} (hε : Infinitesimal ε)
    (hε0 : 0 < ε) {g' : PowerSeries ℝ} (hg' : 0 < PowerSeries.coeff 0 g') :
    0 < scaleEval ε (PowerSeries.X * g') hε hε0 ∧
      ArchimedeanClass.mk (scaleEval ε (PowerSeries.X * g') hε hε0) = ArchimedeanClass.mk ε := by
  have h1 : scaleEval ε (PowerSeries.X * g') hε hε0 =
      haloValue ε ε hε0 * scaleEval ε g' hε hε0 := by
    rw [scaleEval_mul, scaleEval_X]
  have hD := deepHalo_haloValue hε hε0 ε
  have hv2 : |haloValue ε ε hε0 - ε| < ε := by
    have := hD.abs_sub_lt hε0 1
    rwa [pow_one] at this
  have hvpos : 0 < haloValue ε ε hε0 := by
    have := (abs_lt.1 hv2).1
    linarith
  have hS1 : Infinitesimal
      (scaleEval ε g' hε hε0 - ((PowerSeries.coeff 0 g' : ℝ) : Surreal)) := by
    have h := isScaleSum_scaleEval hε hε0 g' 1
    rw [pow_one, scalePartial_one] at h
    exact lt_of_lt_of_le hε h
  have hg'pos : (0 : Surreal.{u}) < ((PowerSeries.coeff 0 g' : ℝ) : Surreal) :=
    Real.toSurreal_pos_iff.2 hg'
  have hlt : ArchimedeanClass.mk ((PowerSeries.coeff 0 g' : ℝ) : Surreal.{u}) <
      ArchimedeanClass.mk (scaleEval ε g' hε hε0 - ((PowerSeries.coeff 0 g' : ℝ) : Surreal)) := by
    rw [mk_realCast hg'.ne']
    exact hS1
  have hSpos : 0 < scaleEval ε g' hε hε0 := by
    have h := abs_lt_abs_of_mk_lt hlt
    rw [abs_of_pos hg'pos] at h
    have := (abs_lt.1 h).1
    linarith
  have hSmk : ArchimedeanClass.mk (scaleEval ε g' hε hε0) = 0 := by
    have hs : scaleEval ε g' hε hε0 = ((PowerSeries.coeff 0 g' : ℝ) : Surreal) +
        (scaleEval ε g' hε hε0 - ((PowerSeries.coeff 0 g' : ℝ) : Surreal)) := by ring
    rw [hs, ArchimedeanClass.mk_add_eq_mk_left hlt, mk_realCast hg'.ne']
  rw [h1]
  refine ⟨mul_pos hvpos hSpos, ?_⟩
  rw [ArchimedeanClass.mk_mul, hSmk, add_zero, mk_haloValue_self hε hε0]

/-- **Substitution with a positive linear leading term**: for `g` with `g₀ = 0 < g₁`, the inner
value `η := scaleEval ε g` is a positive infinitesimal of the class of `ε`, and
`scaleEval ε (f.subst g) = scaleEval η f` for every `f` — no side conditions. -/
theorem scaleEval_subst_of_coeff_one_pos {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {g : PowerSeries ℝ} (hg0 : PowerSeries.coeff 0 g = 0) (hg1 : 0 < PowerSeries.coeff 1 g)
    (f : PowerSeries ℝ) :
    ∃ (hη : Infinitesimal (scaleEval ε g hε hε0)) (hη0 : 0 < scaleEval ε g hε hε0),
      ArchimedeanClass.mk (scaleEval ε g hε hε0) = ArchimedeanClass.mk ε ∧
      scaleEval ε (f.subst g) hε hε0 = scaleEval (scaleEval ε g hε hε0) f hη hη0 := by
  have hdvd : (PowerSeries.X : PowerSeries ℝ) ∣ g := by
    rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hg0
  obtain ⟨g', hg'⟩ := hdvd
  have hg'0 : 0 < PowerSeries.coeff 0 g' := by
    have h : PowerSeries.coeff 1 (PowerSeries.X * g') = PowerSeries.coeff 0 g' :=
      PowerSeries.coeff_succ_X_mul 0 g'
    rw [hg', h] at hg1
    exact hg1
  obtain ⟨hpos, hmk⟩ := scaleEval_X_mul_pos_of_coeff_zero_pos hε hε0 hg'0
  rw [← hg'] at hpos hmk
  have hη : Infinitesimal (scaleEval ε g hε hε0) := by
    rw [Infinitesimal, hmk]
    exact hε
  have hdvd1 : PowerSeries.X ^ 1 ∣ g := by
    rw [pow_one]
    exact ⟨g', hg'⟩
  have hηk : ArchimedeanClass.mk (scaleEval ε g hε hε0) ≤ ArchimedeanClass.mk (ε ^ 1) := by
    rw [pow_one, hmk]
  exact ⟨hη, hpos, hmk, scaleEval_subst hε hε0 one_ne_zero hdvd1 hη hpos hηk f⟩


/-! ### The amplifier: a constant beyond every power of the scale -/

/-- **The amplifier**: for every nonzero `σ` there is a positive surreal `C` with `C · σᵏ`
infinite for every `k` — any strict upper bound of the countable family `ω · (|σ|ᵏ)⁻¹`
(`exists_forall_lt`, countable non-cofinality). -/
theorem exists_pos_forall_mk_mul_pow_lt_zero {σ : Surreal.{u}} (hσ0 : σ ≠ 0) :
    ∃ C : Surreal.{u}, 0 < C ∧ ∀ k : ℕ, ArchimedeanClass.mk (C * σ ^ k) < 0 := by
  obtain ⟨B, hB⟩ := exists_forall_lt fun k : ℕ ↦ ω^ (1 : Surreal.{u}) * (|σ| ^ k)⁻¹
  have hB0 : 0 < B := by
    refine lt_trans ?_ (hB 0)
    rw [pow_zero, inv_one, mul_one]
    exact wpow_pos _
  refine ⟨B, hB0, fun k ↦ ?_⟩
  have hk : 0 < |σ| ^ k := pow_pos (abs_pos.2 hσ0) k
  have h1 : ω^ (1 : Surreal.{u}) < B * |σ| ^ k := by
    have h := mul_lt_mul_of_pos_right (hB k) hk
    rwa [mul_assoc, inv_mul_cancel₀ hk.ne', mul_one] at h
  have h2 : ArchimedeanClass.mk (B * |σ| ^ k) ≤
      ArchimedeanClass.mk (ω^ (1 : Surreal.{u})) := by
    refine ArchimedeanClass.mk_le_mk_of_abs ?_
    rw [abs_of_pos (wpow_pos _), abs_of_pos (mul_pos hB0 hk)]
    exact h1.le
  have h3 : ArchimedeanClass.mk (ω^ (1 : Surreal.{u})) < 0 := by
    have h : ¬ IsFinite (ω^ (1 : Surreal.{u})) := not_isFinite_wpow_one
    rwa [IsFinite, not_le] at h
  rw [← ArchimedeanClass.mk_abs, abs_mul, abs_of_pos hB0, abs_pow]
  exact h2.trans_lt h3

/-- **The amplifier estimate**: if `δ ≠ 0` is not below every power of `σ`
(`mk δ ≤ mk (σ ^ K)` for some `K`) and `C` amplifies every power of `σ` to infinity, then
`|δ| < C δ²` and `σ² < C δ²`. -/
theorem abs_lt_mul_sq_of_mk_le {σ δ C : Surreal.{u}} (hσ : Infinitesimal σ)
    (hδ0 : δ ≠ 0) (hC0 : 0 < C)
    (hC : ∀ k : ℕ, ArchimedeanClass.mk (C * σ ^ k) < 0) {K : ℕ}
    (hK : ArchimedeanClass.mk δ ≤ ArchimedeanClass.mk (σ ^ K)) :
    |δ| < C * δ ^ 2 ∧ σ ^ 2 < C * δ ^ 2 := by
  have hδabs : 0 < |δ| := abs_pos.2 hδ0
  constructor
  · have h1 : ArchimedeanClass.mk (C * δ) < ArchimedeanClass.mk (1 : Surreal.{u}) := by
      rw [ArchimedeanClass.mk_one]
      calc ArchimedeanClass.mk (C * δ)
          = ArchimedeanClass.mk C + ArchimedeanClass.mk δ := ArchimedeanClass.mk_mul _ _
        _ ≤ ArchimedeanClass.mk C + ArchimedeanClass.mk (σ ^ K) := add_le_add le_rfl hK
        _ = ArchimedeanClass.mk (C * σ ^ K) := (ArchimedeanClass.mk_mul _ _).symm
        _ < 0 := hC K
    have h2 := ArchimedeanClass.mk_lt_mk.1 h1 1
    rw [one_nsmul, abs_one, abs_mul, abs_of_pos hC0] at h2
    have h3 : |δ| * 1 < |δ| * (C * |δ|) := mul_lt_mul_of_pos_left h2 hδabs
    rw [mul_one] at h3
    refine h3.trans_eq ?_
    rw [show |δ| * (C * |δ|) = C * (|δ| * |δ|) by ring, ← sq, sq_abs]
  · have h1 : ArchimedeanClass.mk (C * δ ^ 2) < ArchimedeanClass.mk (σ ^ 2) := by
      have h2 : ArchimedeanClass.mk (C * δ ^ 2) ≤ ArchimedeanClass.mk (C * σ ^ (K * 2)) := by
        rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, pow_mul, ArchimedeanClass.mk_pow,
          ArchimedeanClass.mk_pow]
        exact add_le_add le_rfl (nsmul_le_nsmul_right hK 2)
      have h3 : (0 : ArchimedeanClass Surreal.{u}) < ArchimedeanClass.mk (σ ^ 2) := by
        rw [ArchimedeanClass.mk_pow, two_nsmul]
        exact lt_of_lt_of_le hσ (le_add_of_nonneg_right hσ.le)
      exact (h2.trans_lt (hC (K * 2))).trans h3
    have h4 := abs_lt_abs_of_mk_lt h1
    rwa [abs_of_nonneg (sq_nonneg σ), abs_of_nonneg (mul_nonneg hC0.le (sq_nonneg δ))] at h4

/-! ### The kernel exponential theorem -/

/-- **THE KERNEL EXPONENTIAL THEOREM**: at every nonzero infinitesimal `σ` (of either
sign), the canonical exponential `expInf'` has surreal-point derivative **zero**.

Proof. Fix an amplifier `C` (`exists_pos_forall_mk_mul_pow_lt_zero`) and take the constant
`9 C`. For an infinitesimal increment `δ ≠ 0`, either `δ` lies below every power of `σ` — then
`expInf' (σ + δ) = expInf' σ` outright by the blindness theorem
(`expInf_add_eq_of_forall_nsmul_lt`), error `0` — or `mk δ ≤ mk (σ ^ K)` for some `K`, in
which case the amplifier estimate gives `|δ| < C δ²` and `σ² < C δ²`, and the uniform
quadratic bound `|expInf' x − 1 − x| ≤ (3/2) x²` at `x = σ + δ` and `x = σ` yields
`|expInf' (σ + δ) − expInf' σ| ≤ |δ| + (3/2)(σ + δ)² + (3/2)σ² ≤ 9 C δ²`. -/
theorem hasDerivS_expInf'_of_ne {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : σ ≠ 0) :
    HasDerivS expInf' σ 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_pos_forall_mk_mul_pow_lt_zero hσ0
  refine ⟨9 * C, fun δ hδ ↦ ?_⟩
  rw [zero_mul, sub_zero]
  rcases eq_or_ne δ 0 with rfl | hδ0
  · simp
  by_cases hfine : ∀ k : ℕ, k • ArchimedeanClass.mk σ < ArchimedeanClass.mk δ
  · have hστ0 : σ + δ ≠ 0 := add_ne_zero_of_forall_nsmul_lt hσ0 hfine
    rw [expInf'_of_ne (hσ.add hδ) hστ0, expInf'_of_ne hσ hσ0,
      expInf_add_eq_of_forall_nsmul_lt hσ hδ hσ0 hστ0 hfine, sub_self, abs_zero]
    positivity
  · push Not at hfine
    obtain ⟨K, hK⟩ := hfine
    rw [← ArchimedeanClass.mk_pow] at hK
    obtain ⟨h1, h2⟩ := abs_lt_mul_sq_of_mk_le hσ hδ0 hC0 hC hK
    have e1 := abs_expInf'_sub_one_sub_le (hσ.add hδ)
    have e2 := abs_expInf'_sub_one_sub_le hσ
    have hC1 : δ ^ 2 ≤ C * δ ^ 2 := by
      have h0 : ArchimedeanClass.mk (C * σ ^ 0) < ArchimedeanClass.mk (1 : Surreal.{u}) := by
        rw [ArchimedeanClass.mk_one]
        exact hC 0
      have h := ArchimedeanClass.mk_lt_mk.1 h0 1
      rw [pow_zero, mul_one, one_nsmul, abs_one, abs_of_pos hC0] at h
      exact le_mul_of_one_le_left (sq_nonneg δ) h.le
    have hsq : (σ + δ) ^ 2 ≤ 2 * σ ^ 2 + 2 * δ ^ 2 := by nlinarith [sq_nonneg (σ - δ)]
    have hsplit : expInf' (σ + δ) - expInf' σ =
        (expInf' (σ + δ) - 1 - (σ + δ)) + (-(expInf' σ - 1 - σ)) + δ := by ring
    rw [hsplit]
    calc |(expInf' (σ + δ) - 1 - (σ + δ)) + (-(expInf' σ - 1 - σ)) + δ|
        ≤ |expInf' (σ + δ) - 1 - (σ + δ)| + |-(expInf' σ - 1 - σ)| + |δ| :=
          abs_add_three _ _ _
      _ = |expInf' (σ + δ) - 1 - (σ + δ)| + |expInf' σ - 1 - σ| + |δ| := by rw [abs_neg]
      _ ≤ 3 / 2 * (σ + δ) ^ 2 + 3 / 2 * σ ^ 2 + |δ| := by linarith
      _ ≤ 9 * C * δ ^ 2 := by nlinarith [mul_nonneg hC0.le (sq_nonneg δ)]

/-- At the origin the canonical exponential has derivative `1` (the uniform quadratic
bound `abs_expInf'_sub_one_sub_le`, restated). -/
theorem hasDerivS_expInf'_zero : HasDerivS expInf'.{u} 0 1 := by
  refine ⟨3 / 2, fun δ hδ ↦ ?_⟩
  rw [zero_add, expInf'_zero, one_mul]
  exact abs_expInf'_sub_one_sub_le hδ

/-- **The derivative of the canonical exponential at a nonzero infinitesimal is `0`, and
only `0`.** -/
theorem hasDerivS_expInf'_iff {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : σ ≠ 0)
    (d : Surreal.{u}) : HasDerivS expInf' σ d ↔ d = 0 :=
  ⟨fun h ↦ h.unique (hasDerivS_expInf'_of_ne hσ hσ0),
    fun h ↦ h ▸ hasDerivS_expInf'_of_ne hσ hσ0⟩

/-- **`exp′ = exp` fails at every nonzero infinitesimal**: the canonical exponential is
never its own derivative there (its value is positive, its derivative is zero). -/
theorem not_hasDerivS_expInf'_self {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : σ ≠ 0) :
    ¬ HasDerivS expInf' σ (expInf' σ) := by
  rw [hasDerivS_expInf'_iff hσ hσ0]
  exact (expInf'_pos hσ).ne'

/-- The canonical exponential is **not constant** on the positive infinitesimals:
`expInf' σ ≠ expInf' (σ / 2)` (since `expInf' σ = (expInf' (σ/2))²` and `expInf' (σ/2) > 1`).
Together with `hasDerivS_expInf'_of_ne`: `expInf'` is a nonconstant function with derivative
zero at every point of the positive infinitesimals — a kernel function of the surreal
derivative living entirely inside the halo of `0`. -/
theorem expInf'_ne_expInf'_half {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : 0 < σ) :
    expInf' σ ≠ expInf' (σ / 2) := by
  have hh0 : 0 < σ / 2 := by positivity
  rw [expInf'_of_ne hσ hσ0.ne', expInf'_of_ne hσ.half hh0.ne', expInf_eq_sq_expInf_half hσ hσ0]
  have h1 := one_lt_expInf hσ.half hh0
  have h2 : expInf (σ / 2) hσ.half hh0.ne' < expInf (σ / 2) hσ.half hh0.ne' ^ 2 := by
    rw [sq]
    exact lt_mul_of_one_lt_left (zero_lt_one.trans h1) h1
  exact h2.ne'

/-- **The kernel exponential theorem, packaged**: the canonical exponential has derivative
`1` at `0` and derivative `0` at every other infinitesimal, and is not constant there. -/
theorem kernel_exponential :
    HasDerivS expInf'.{u} 0 1 ∧
      (∀ σ : Surreal.{u}, Infinitesimal σ → σ ≠ 0 → HasDerivS expInf' σ 0) ∧
      (∀ σ : Surreal.{u}, Infinitesimal σ → σ ≠ 0 → ¬ HasDerivS expInf' σ (expInf' σ)) ∧
      ∃ σ τ : Surreal.{u}, Infinitesimal σ ∧ σ ≠ 0 ∧ Infinitesimal τ ∧ τ ≠ 0 ∧
        expInf' σ ≠ expInf' τ := by
  have hσ : Infinitesimal ((ω^ (1 : Surreal.{u}))⁻¹ : Surreal.{u}) :=
    infinitesimal_inv_wpow one_pos
  have hσ0 : (0 : Surreal.{u}) < (ω^ (1 : Surreal.{u}))⁻¹ := inv_pos.2 (wpow_pos _)
  refine ⟨hasDerivS_expInf'_zero, fun σ hσ hσ0 ↦ hasDerivS_expInf'_of_ne hσ hσ0,
    fun σ hσ hσ0 ↦ not_hasDerivS_expInf'_self hσ hσ0,
    (ω^ (1 : Surreal.{u}))⁻¹, (ω^ (1 : Surreal.{u}))⁻¹ / 2, hσ, hσ0.ne', hσ.half,
    (by positivity), expInf'_ne_expInf'_half hσ hσ0⟩

/-! ### The jet of the exponential: derivative `1` at the origin, `0` everywhere else -/

/-- **The canonical jet of `exp ℝ` is a kernel function away from the origin**: at every
nonzero infinitesimal `σ` it has derivative `0` — it agrees with `expInf'` on the halo of `0`,
and the kernel exponential theorem applies. Together with `hasDerivS_jetExt_exp_zero` this is
the complete derivative picture of the canonical-sum exponential on the infinitesimals:
`1` at the origin, `0` at every other point. -/
theorem hasDerivS_jetExt_exp_of_ne {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : σ ≠ 0) :
    HasDerivS (jetExt (PowerSeries.exp ℝ) 0) σ 0 :=
  (hasDerivS_expInf'_of_ne hσ hσ0).congr_of_forall_infinitesimal fun _ hε ↦
    (jetExt_exp_zero_of_infinitesimal (hσ.add hε)).symm

theorem not_hasDerivS_jetExt_exp_self {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : σ ≠ 0) :
    ¬ HasDerivS (jetExt (PowerSeries.exp ℝ) 0) σ (jetExt (PowerSeries.exp ℝ) 0 σ) := by
  intro h
  have h1 : HasDerivS expInf' σ (jetExt (PowerSeries.exp ℝ) 0 σ) :=
    h.congr_of_forall_infinitesimal fun _ hε ↦ jetExt_exp_zero_of_infinitesimal (hσ.add hε)
  rw [jetExt_exp_zero_of_infinitesimal hσ] at h1
  exact not_hasDerivS_expInf'_self hσ hσ0 h1

end Surreal

end
