/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.HahnProduct
import Infinity.ScaleCalculus
import Mathlib.RingTheory.HahnSeries.HEval
import Mathlib.Data.Countable.Small

/-!
# The faithful exponential: `exp′ = exp` on the infinitesimals and the finite galaxy

The canonical-sum exponential `expInf` is blind below its scale: `ScaleCalculus.kernel_exponential`
shows it has derivative `0` at every nonzero infinitesimal. Conway's isomorphism
`No ≅ ℝ((ω^No))` (`HahnProduct.hahnOrderRingIso`) makes the honest construction possible: evaluate
the exponential power series in the Hahn-series field (mathlib's `PowerSeries.heval`, the
substitution `X ↦ toHahnSeries ε` for a Hahn series of positive order) and transport the result
back along `evalHahn`. This file builds that exponential and proves it is multiplicative
everywhere and satisfies `exp′ = exp`.

## The bridge (`SurrealHahnSeries.toHahn`, `ofHahn`, `small_support_heval`)

`toHahn x := ofLex x.1` is the underlying mathlib Hahn series over `Surrealᵒᵈ`; `ofHahn h hs`
repackages a mathlib Hahn series with `u`-small support. The one genuinely new lemma is
`small_support_heval`: the support of `heval a f` is small when `a`'s is (it lies in the union of
the supports of the powers `aⁿ`, each a finite sumset of `a`'s support).

## The faithful evaluation (`fevalHS`)

* `orderTop_pos_of_infinitesimal`: every exponent of the normal form of an infinitesimal is
  negative (`lt_zero_of_mem_support_toHahnSeries`, from
  `mk_le_mk_wpow_of_mem_support_toHahnSeries`: every term of a normal form is dominated by the
  number), so the underlying Hahn series has `0 < orderTop`.
* `hevalS ε f := ofHahn (heval (toHahn (toHahnSeries ε)) f)` and
  `fevalHS ε f := evalHahn (hevalS ε f)`; **`fevalHom ε : PowerSeries ℝ →+* Surreal`** with
  `fevalHS_C : C r ↦ r` and **`fevalHS_X : X ↦ ε` exactly** at every infinitesimal `ε` (contrast
  `scaleEval_X = haloValue ε ε`); `fevalHS_coe` (polynomials evaluate to their values),
  `isFinite_fevalHS`, **`isScaleSum_fevalHS`** (the faithful value is a scale sum),
  `mk_pow_le_mk_fevalHS_of_X_pow_dvd` (the residual estimate), the uniform jet bound
  `abs_fevalHS_sub_le : |fevalHS δ f − f₀ − f₁ δ| ≤ (|f₂| + 1) δ²`, and the faithful jet at the
  origin `hasDerivS_fevalHS_zero`.

## The functional equation in the Hahn-series field (`heval_exp_add`)

For Hahn series `a, b` of positive order, `heval (a + b) exp = heval a exp * heval b exp`: the
product of the two exponential summable families, regrouped along the antidiagonals
(`HahnSeries.SummableFamily.hsum_eq_hsum_of_antidiagonal`, from the finsum regrouping
`finsum_sum_antidiagonal`), is the exponential family at `a + b`, by the coefficient identity of
mathlib's `PowerSeries.exp_mul_exp_eq_exp_add` read over the Hahn-series field itself
(`coeff_rescale_exp_eq`). No binomial computation is needed.

## THE FAITHFUL EXPONENTIAL (`expH`)

`expH ε := fevalHS ε (exp ℝ)`, a total function, honest on infinitesimals:
* `expH_zero`, **`expH_add : expH (σ + τ) = expH σ * expH τ` for ALL infinitesimals** (no
  comparability of classes — contrast `expInf_add_eq_mul_iff_classComparable`);
* **the reflection law** `expH_mul_expH_neg`, `expH_neg_eq_inv`, `expH_sub`, `expH_nsmul`,
  `expH_zsmul`, `expH_ne_zero`, `expH_pos`, `one_lt_expH_of_pos`, `expH_lt_one_of_neg`,
  `expH_inj` (injective on infinitesimals), `expH_lt_expH_of_lt` (strictly increasing);
* the uniform bound `abs_expH_sub_one_sub_le : |expH σ − 1 − σ| ≤ (3/2) σ²`,
  `infinitesimal_expH_sub_one`, `stdPart_expH`, `isFinite_expH`.

## THE FAITHFUL EXPONENTIAL ODE

* **`hasDerivS_expH : HasDerivS expH σ (expH σ)`** at every infinitesimal `σ` (including `0`),
  with the finite constant `(3/2)|expH σ|`; the contrast theorem
  `hasDerivS_expH_and_not_hasDerivS_expInf'` records it next to `kernel_exponential`.
* The finite galaxy: `expFinH x := e^{st x} · expH (x − st x)`; `expFinH_realCast`,
  `expFinH_of_infinitesimal`, `expFinH_add_infinitesimal`, **`expFinH_add`** (the functional
  equation for all finite `x, y`), `expFinH_pos`, `stdPart_expFinH`, and
  **`hasDerivS_expFinH : HasDerivS expFinH x (expFinH x)` at every finite `x`** — `exp′ = exp`
  on the whole finite galaxy.

## Faithful versus canonical

* `isHahnSum_expSeries_expH`: the faithful exponential is a Hahn sum of the exponential series;
* **`expInf_eq_haloValue_expH : expInf ε = haloValue |ε| (expH ε)`** — the canonical exponential
  is the halo simplification of the faithful one — and
  **`expInf_eq_expH_iff : expInf ε = expH ε ↔ HaloSimple |ε| (expH ε)`**;
* **the monomial instance** `expInf_monomial_eq_expH`: for `c ≠ 0` and `y < 0`,
  `expInf (c ω^y) = expH (c ω^y)` (the support of the monomial exponential is `{m y}`, so its
  normal form has limit length and is halo-simple by `haloSimple_hahnSumO`);
* **the sharp witness** at `ε = ω⁻¹ + ω^(−ω)`: `faithful_sees_fine_term` (`expH ε ≠ expH ω⁻¹`
  while `expInf ε = expInf ω⁻¹`), `expH_ne_expInf_wpow_neg_one_add_wpow_neg_omega`, and
  `not_haloSimple_expH_wpow_neg_one_add_wpow_neg_omega`.
-/

open ArchimedeanClass Finset

universe u

noncomputable section

/-! ### The bridge to mathlib's Hahn series -/

namespace SurrealHahnSeries

open OrderDual

/-- The underlying mathlib Hahn series of a surreal Hahn series (exponents in `Surrealᵒᵈ`). -/
def toHahn (x : SurrealHahnSeries.{u}) : HahnSeries Surreal.{u}ᵒᵈ ℝ := ofLex x.1

theorem coeff_toHahn (x : SurrealHahnSeries.{u}) (j : Surreal.{u}ᵒᵈ) :
    (toHahn x).coeff j = x.coeff (ofDual j) := rfl

theorem coeff_toHahn_toDual (x : SurrealHahnSeries.{u}) (i : Surreal.{u}) :
    (toHahn x).coeff (toDual i) = x.coeff i := rfl

theorem mem_support_toHahn {x : SurrealHahnSeries.{u}} {i : Surreal.{u}} :
    toDual i ∈ (toHahn x).support ↔ i ∈ x.support := Iff.rfl

theorem toHahn_injective : Function.Injective (toHahn : SurrealHahnSeries.{u} → _) := by
  intro x y h
  exact SurrealHahnSeries.ext (funext fun i ↦ congrArg (fun z ↦ HahnSeries.coeff z (toDual i)) h)

@[simp] theorem toHahn_zero : toHahn (0 : SurrealHahnSeries.{u}) = 0 := rfl
@[simp] theorem toHahn_one : toHahn (1 : SurrealHahnSeries.{u}) = 1 := rfl
theorem toHahn_add (x y : SurrealHahnSeries.{u}) : toHahn (x + y) = toHahn x + toHahn y := rfl
theorem toHahn_mul (x y : SurrealHahnSeries.{u}) : toHahn (x * y) = toHahn x * toHahn y := rfl
theorem toHahn_neg (x : SurrealHahnSeries.{u}) : toHahn (-x) = -toHahn x := rfl

theorem toHahn_single (z : Surreal.{u}) (c : ℝ) :
    toHahn (single z c) = HahnSeries.single (toDual z) c :=
  ofLex_val_single z c

instance small_support_toHahn (x : SurrealHahnSeries.{u}) : Small.{u} (toHahn x).support :=
  x.small_support

/-- Repackaging a mathlib Hahn series with `u`-small support as a surreal Hahn series. -/
def ofHahn (h : HahnSeries Surreal.{u}ᵒᵈ ℝ) (hs : Small.{u} h.support) : SurrealHahnSeries.{u} :=
  mk (fun i ↦ h.coeff (toDual i)) hs h.isWF_support

theorem coeff_ofHahn (h : HahnSeries Surreal.{u}ᵒᵈ ℝ) (hs : Small.{u} h.support)
    (i : Surreal.{u}) : (ofHahn h hs).coeff i = h.coeff (toDual i) := rfl

theorem toHahn_ofHahn (h : HahnSeries Surreal.{u}ᵒᵈ ℝ) (hs : Small.{u} h.support) :
    toHahn (ofHahn h hs) = h :=
  HahnSeries.ext (funext fun _ ↦ rfl)

theorem ofHahn_toHahn (x : SurrealHahnSeries.{u}) (hs : Small.{u} (toHahn x).support) :
    ofHahn (toHahn x) hs = x :=
  SurrealHahnSeries.ext rfl

end SurrealHahnSeries

/-! ### Smallness of the support of `heval` -/

namespace SurrealHahnSeries

open HahnSeries

theorem small_support_pow {a : HahnSeries Surreal.{u}ᵒᵈ ℝ} (ha : Small.{u} a.support) (n : ℕ) :
    Small.{u} ((a ^ n).support) := by
  induction n with
  | zero =>
    rw [pow_zero, HahnSeries.support_one]
    infer_instance
  | succ n ih =>
    rw [pow_succ]
    haveI := ih
    haveI := ha
    have h2 : Small.{u} ↥(Set.image2 (· + ·) (a ^ n).support a.support) := inferInstance
    rw [Set.image2_add] at h2
    exact small_subset support_mul_subset

theorem small_support_powers {a : HahnSeries Surreal.{u}ᵒᵈ ℝ} (ha : Small.{u} a.support) (n : ℕ) :
    Small.{u} ((SummableFamily.powers a n).support) := by
  rw [SummableFamily.powers_toFun]
  split_ifs with h
  · exact small_support_pow ha n
  · rcases n with _ | n
    · rw [pow_zero, HahnSeries.support_one]
      infer_instance
    · rw [zero_pow (Nat.succ_ne_zero n), HahnSeries.support_zero]
      infer_instance

/-- **The support of `heval` is small**: the faithful evaluation of a power series at a
`u`-small Hahn series has `u`-small support. -/
theorem small_support_heval {a : HahnSeries Surreal.{u}ᵒᵈ ℝ} (ha : Small.{u} a.support)
    (f : PowerSeries ℝ) : Small.{u} (PowerSeries.heval a f).support := by
  rw [PowerSeries.heval_apply]
  haveI : ∀ n, Small.{u} ((SummableFamily.powerSeriesFamily a f n).support) := fun n ↦ by
    haveI := small_support_powers ha n
    rw [SummableFamily.powerSeriesFamily, SummableFamily.smulFamily_toFun]
    exact small_subset (support_smul_subset _ _)
  exact small_subset SummableFamily.support_hsum_subset

end SurrealHahnSeries

/-! ### Exponents of infinitesimals are negative -/

namespace Surreal

open SurrealHahnSeries OrderDual

/-- **Every exponent of a normal form is dominated by the number**: `mk x ≤ mk (ω^ s)` for
every exponent `s` of `toHahnSeries x`. -/
theorem mk_le_mk_wpow_of_mem_support_toHahnSeries {x s : Surreal.{u}}
    (hs : s ∈ (toHahnSeries x).support) :
    ArchimedeanClass.mk x ≤ ArchimedeanClass.mk (ω^ s) := by
  rw [support_toHahnSeries] at hs
  obtain ⟨⟨β, hβ⟩, rfl⟩ := hs
  have hβ' : β < cnfLength x := hβ
  have hne := cnfRes_ne_zero_of_lt_cnfLength hβ'
  show ArchimedeanClass.mk x ≤ ArchimedeanClass.mk (ω^ (cnfRes x β).wlog)
  rw [archimedeanClassMk_wpow_wlog hne]
  rcases eq_or_ne β 0 with rfl | hβ0
  · rw [cnfRes_zero]
  · have h := mk_cnfRes_lt (fun δ hδ ↦ cnfRes_ne_zero_of_lt_cnfLength (hδ.trans hβ'))
      (pos_iff_ne_zero.2 hβ0)
    rw [cnfRes_zero] at h
    exact h.le

/-- Every exponent of the normal form of an infinitesimal is negative. -/
theorem lt_zero_of_mem_support_toHahnSeries {ε s : Surreal.{u}} (hε : Infinitesimal ε)
    (hs : s ∈ (toHahnSeries ε).support) : s < 0 := by
  have h := mk_le_mk_wpow_of_mem_support_toHahnSeries hs
  have h0 : ArchimedeanClass.mk (ω^ (0 : Surreal.{u})) < ArchimedeanClass.mk (ω^ s) := by
    rw [wpow_zero, ArchimedeanClass.mk_one]
    exact lt_of_lt_of_le hε h
  exact (StrictAnti.lt_iff_gt archimedeanClassMk_wpow_strictAnti).1 h0

/-- **Infinitesimals have positive order**: in mathlib's convention (exponents in `Surrealᵒᵈ`),
the underlying Hahn series of the normal form of an infinitesimal has `0 < orderTop`. -/
theorem orderTop_pos_of_infinitesimal {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    0 < (toHahn (toHahnSeries ε)).orderTop := by
  rw [← not_le]
  intro h
  set a := toHahn (toHahnSeries ε) with ha
  have hne : a ≠ 0 := by
    intro h0
    rw [h0, HahnSeries.orderTop_zero] at h
    exact absurd h (WithTop.not_top_le_coe _)
  rw [HahnSeries.orderTop_of_ne_zero hne, ← WithTop.coe_zero, WithTop.coe_le_coe] at h
  have hmem := a.isWF_support.min_mem (HahnSeries.support_nonempty_iff.2 hne)
  have hlt := lt_zero_of_mem_support_toHahnSeries hε
    (s := ofDual (a.isWF_support.min (HahnSeries.support_nonempty_iff.2 hne))) hmem
  exact absurd hlt (not_lt.2 (OrderDual.ofDual_le_ofDual.2 h))

end Surreal

/-! ### The faithful evaluation of power series -/

namespace Surreal

open SurrealHahnSeries OrderDual HahnSeries

/-- **The faithful evaluation of a power series at `ε`, in Hahn-series form**: mathlib's
`PowerSeries.heval` (the substitution `X ↦ toHahnSeries ε`, summed as a Hahn series) repackaged
as a surreal Hahn series. Honest on infinitesimals (`hevalS_X`); junk elsewhere. -/
def hevalS (ε : Surreal.{u}) (f : PowerSeries ℝ) : SurrealHahnSeries.{u} :=
  ofHahn (PowerSeries.heval (toHahn (toHahnSeries ε)) f) (small_support_heval inferInstance f)

theorem toHahn_hevalS (ε : Surreal.{u}) (f : PowerSeries ℝ) :
    toHahn (hevalS ε f) = PowerSeries.heval (toHahn (toHahnSeries ε)) f :=
  toHahn_ofHahn _ _

theorem hevalS_mul (ε : Surreal.{u}) (f g : PowerSeries ℝ) :
    hevalS ε (f * g) = hevalS ε f * hevalS ε g :=
  toHahn_injective (by
    rw [toHahn_mul, toHahn_hevalS, toHahn_hevalS, toHahn_hevalS, PowerSeries.heval_mul])

theorem hevalS_add (ε : Surreal.{u}) (f g : PowerSeries ℝ) :
    hevalS ε (f + g) = hevalS ε f + hevalS ε g :=
  toHahn_injective (by rw [toHahn_add, toHahn_hevalS, toHahn_hevalS, toHahn_hevalS, map_add])

theorem hevalS_one (ε : Surreal.{u}) : hevalS ε 1 = 1 :=
  toHahn_injective (by rw [toHahn_hevalS, map_one, toHahn_one])

theorem hevalS_zero (ε : Surreal.{u}) : hevalS ε 0 = 0 :=
  toHahn_injective (by rw [toHahn_hevalS, map_zero, toHahn_zero])

theorem smul_one_eq_single (r : ℝ) :
    r • (1 : HahnSeries Surreal.{u}ᵒᵈ ℝ) = HahnSeries.single (toDual (0 : Surreal.{u})) r := by
  ext j
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_one, HahnSeries.coeff_single, smul_eq_mul]
  by_cases hj : j = 0
  · rw [if_pos hj, if_pos (show j = toDual 0 from hj), mul_one]
  · rw [if_neg hj, if_neg (show ¬ j = toDual 0 from hj), mul_zero]

theorem hevalS_C (ε : Surreal.{u}) (r : ℝ) :
    hevalS ε (PowerSeries.C r) = SurrealHahnSeries.single 0 r :=
  toHahn_injective (by
    rw [toHahn_hevalS, PowerSeries.heval_C, toHahn_single, smul_one_eq_single])

/-- **Faithfulness**: `X` evaluates to `ε` itself, exactly, at every infinitesimal `ε`. -/
theorem hevalS_X {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    hevalS ε PowerSeries.X = toHahnSeries ε :=
  toHahn_injective (by
    rw [toHahn_hevalS, PowerSeries.heval_X _ (orderTop_pos_of_infinitesimal hε)])

theorem hevalS_pow (ε : Surreal.{u}) (f : PowerSeries ℝ) (n : ℕ) :
    hevalS ε (f ^ n) = hevalS ε f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, hevalS_one]
  | succ n ih => rw [pow_succ, pow_succ, hevalS_mul, ih]

/-- At `ε = 0` the evaluation is the constant coefficient. -/
theorem hevalS_zero_left (f : PowerSeries ℝ) :
    hevalS (0 : Surreal.{u}) f = SurrealHahnSeries.single 0 (PowerSeries.constantCoeff f) :=
  toHahn_injective (by
    rw [toHahn_hevalS, toHahnSeries_zero, toHahn_zero, PowerSeries.heval_apply,
      SummableFamily.powerSeriesFamily_hsum_zero, toHahn_single, smul_one_eq_single])

/-- **THE FAITHFUL EVALUATION** `fevalHS ε f := evalHahn (hevalS ε f)`: the power series `f`
evaluated at `ε` through Conway's isomorphism `No ≅ ℝ((ω^No))`. -/
def fevalHS (ε : Surreal.{u}) (f : PowerSeries ℝ) : Surreal.{u} :=
  evalHahn (hevalS ε f)

theorem fevalHS_mul (ε : Surreal.{u}) (f g : PowerSeries ℝ) :
    fevalHS ε (f * g) = fevalHS ε f * fevalHS ε g := by
  rw [fevalHS, hevalS_mul, evalHahn_mul]
  rfl

theorem fevalHS_add (ε : Surreal.{u}) (f g : PowerSeries ℝ) :
    fevalHS ε (f + g) = fevalHS ε f + fevalHS ε g := by
  rw [fevalHS, hevalS_add, evalHahn_add']
  rfl

theorem fevalHS_one (ε : Surreal.{u}) : fevalHS ε 1 = 1 := by
  rw [fevalHS, hevalS_one, evalHahn_one]

theorem fevalHS_zero (ε : Surreal.{u}) : fevalHS ε 0 = 0 := by
  rw [fevalHS, hevalS_zero, evalHahn_zero]

theorem fevalHS_C (ε : Surreal.{u}) (r : ℝ) : fevalHS ε (PowerSeries.C r) = (r : Surreal) := by
  rw [fevalHS, hevalS_C, evalHahn_single, wpow_zero, mul_one]

/-- **`X ↦ ε` exactly** (contrast `scaleEval_X = haloValue ε ε`). -/
theorem fevalHS_X {ε : Surreal.{u}} (hε : Infinitesimal ε) : fevalHS ε PowerSeries.X = ε := by
  rw [fevalHS, hevalS_X hε, evalHahn_toHahnSeries]

theorem fevalHS_zero_left (f : PowerSeries ℝ) :
    fevalHS (0 : Surreal.{u}) f = ((PowerSeries.constantCoeff f : ℝ) : Surreal) := by
  rw [fevalHS, hevalS_zero_left, evalHahn_single, wpow_zero, mul_one]

/-- **The faithful evaluation is a ring homomorphism** `PowerSeries ℝ →+* Surreal`, with
`X ↦ ε` exactly when `ε` is infinitesimal. -/
def fevalHom (ε : Surreal.{u}) : PowerSeries ℝ →+* Surreal.{u} where
  toFun f := fevalHS ε f
  map_one' := fevalHS_one ε
  map_mul' := fevalHS_mul ε
  map_zero' := fevalHS_zero ε
  map_add' := fevalHS_add ε

@[simp]
theorem fevalHom_apply (ε : Surreal.{u}) (f : PowerSeries ℝ) : fevalHom ε f = fevalHS ε f :=
  rfl

theorem fevalHS_neg (ε : Surreal.{u}) (f : PowerSeries ℝ) : fevalHS ε (-f) = -fevalHS ε f :=
  map_neg (fevalHom ε) f

theorem fevalHS_sub (ε : Surreal.{u}) (f g : PowerSeries ℝ) :
    fevalHS ε (f - g) = fevalHS ε f - fevalHS ε g :=
  map_sub (fevalHom ε) f g

theorem fevalHS_pow (ε : Surreal.{u}) (f : PowerSeries ℝ) (n : ℕ) :
    fevalHS ε (f ^ n) = fevalHS ε f ^ n :=
  map_pow (fevalHom ε) f n

theorem fevalHS_C_mul (ε : Surreal.{u}) (r : ℝ) (f : PowerSeries ℝ) :
    fevalHS ε (PowerSeries.C r * f) = (r : Surreal) * fevalHS ε f := by
  rw [fevalHS_mul, fevalHS_C]

theorem fevalHS_X_pow_mul {ε : Surreal.{u}} (hε : Infinitesimal ε) (n : ℕ) (g : PowerSeries ℝ) :
    fevalHS ε (PowerSeries.X ^ n * g) = ε ^ n * fevalHS ε g := by
  rw [fevalHS_mul, fevalHS_pow, fevalHS_X hε]

/-- Polynomials evaluate to their values. -/
theorem fevalHS_coe {ε : Surreal.{u}} (hε : Infinitesimal ε) (p : Polynomial ℝ) :
    fevalHS ε (p : PowerSeries ℝ) = p.eval₂ realHom ε := by
  have h : (fevalHom ε).comp Polynomial.coeToPowerSeries.ringHom =
      Polynomial.eval₂RingHom realHom ε := by
    apply Polynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
        fevalHom_apply, fevalHS_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, realHom_apply]
    · rw [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
        fevalHom_apply, fevalHS_X hε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have h' := RingHom.congr_fun h p
  rwa [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, fevalHom_apply,
    Polynomial.coe_eval₂RingHom] at h'

/-! ### Finiteness and the scale-sum property -/

/-- Every exponent of `hevalS ε f` is `≤ 0` when `ε` is infinitesimal. -/
theorem le_zero_of_mem_support_hevalS {ε : Surreal.{u}} (hε : Infinitesimal ε) (f : PowerSeries ℝ)
    {s : Surreal.{u}} (hs : s ∈ (hevalS ε f).support) : s ≤ 0 := by
  have hs' : toDual s ∈ (PowerSeries.heval (toHahn (toHahnSeries ε)) f).support := by
    rw [← toHahn_hevalS]
    exact hs
  rw [PowerSeries.heval_apply] at hs'
  have hpos := orderTop_pos_of_infinitesimal hε
  have h0 : (0 : Surreal.{u}ᵒᵈ) ≤ toDual s := by
    refine SummableFamily.le_hsum_support_mem (fun n g' hg' ↦ ?_) hs'
    rw [SummableFamily.powerSeriesFamily, SummableFamily.smulFamily_toFun] at hg'
    have hg'' := HahnSeries.support_smul_subset _ _ hg'
    rw [SummableFamily.powers_of_orderTop_pos hpos] at hg''
    by_contra hneg
    rw [not_le] at hneg
    have hzero : ((toHahn (toHahnSeries ε)) ^ n).coeff g' = 0 := by
      apply HahnSeries.coeff_eq_zero_of_lt_orderTop
      refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 hneg) ?_
      rw [WithTop.coe_zero]
      refine le_trans ?_ HahnSeries.orderTop_nsmul_le_orderTop_pow
      exact nsmul_nonneg hpos.le n
    exact hg'' hzero
  exact h0

/-- **The faithful evaluation at an infinitesimal is finite.** -/
theorem isFinite_fevalHS {ε : Surreal.{u}} (hε : Infinitesimal ε) (f : PowerSeries ℝ) :
    IsFinite (fevalHS ε f) := by
  have h := mk_wpow_le_mk_evalHahn_of_support_le (x := hevalS ε f) (a := 0)
    (fun s hs ↦ le_zero_of_mem_support_hevalS hε f hs)
  rwa [wpow_zero, ArchimedeanClass.mk_one] at h

theorem scalePartial_eq_fevalHS {ε : Surreal.{u}} (hε : Infinitesimal ε) (f : PowerSeries ℝ)
    (N : ℕ) : scalePartial ε f N = fevalHS ε (PowerSeries.trunc N f : PowerSeries ℝ) := by
  rw [scalePartial_eq_eval₂_trunc, fevalHS_coe hε]

/-- The residual estimate: a multiple of `X^N` evaluates to something of class `≥ mk (ε^N)`. -/
theorem mk_pow_le_mk_fevalHS_of_X_pow_dvd {ε : Surreal.{u}} (hε : Infinitesimal ε)
    {g : PowerSeries ℝ} {N : ℕ} (hg : PowerSeries.X ^ N ∣ g) :
    ArchimedeanClass.mk (ε ^ N) ≤ ArchimedeanClass.mk (fevalHS ε g) := by
  obtain ⟨g', rfl⟩ := hg
  rw [fevalHS_X_pow_mul hε, ArchimedeanClass.mk_mul]
  exact le_add_of_nonneg_right (isFinite_fevalHS hε g')

/-- **The faithful value is a scale sum**: `fevalHS ε f` differs from every partial sum
`∑_{k<N} fₖ εᵏ` by a quantity of class `≥ mk (ε^N)`. -/
theorem isScaleSum_fevalHS {ε : Surreal.{u}} (hε : Infinitesimal ε) (f : PowerSeries ℝ) :
    IsScaleSum ε f (fevalHS ε f) := by
  intro N
  rw [scalePartial_eq_fevalHS hε, ← fevalHS_sub]
  exact mk_pow_le_mk_fevalHS_of_X_pow_dvd hε (X_pow_dvd_sub_trunc f N)

/-- The uniform bound `|fevalHS δ g| ≤ |g₀| + 1` at every infinitesimal `δ`. -/
theorem abs_fevalHS_le {δ : Surreal.{u}} (hδ : Infinitesimal δ) (g : PowerSeries ℝ) :
    |fevalHS δ g| ≤ |((PowerSeries.coeff 0 g : ℝ) : Surreal)| + 1 := by
  have h1 := congrArg (fevalHS δ) (PowerSeries.eq_X_mul_shift_add_const g)
  rw [fevalHS_add, fevalHS_mul, fevalHS_X hδ, fevalHS_C] at h1
  set g' := PowerSeries.mk fun p ↦ PowerSeries.coeff (p + 1) g
  have hinf : Infinitesimal (δ * fevalHS δ g') := hδ.mul_isFinite (isFinite_fevalHS hδ g')
  have h2 : |δ * fevalHS δ g'| < 1 := by
    have := infinitesimal_iff.1 hinf 1
    rwa [one_nsmul] at this
  rw [h1, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  calc |δ * fevalHS δ g' + ((PowerSeries.constantCoeff g : ℝ) : Surreal)|
      ≤ |δ * fevalHS δ g'| + |((PowerSeries.constantCoeff g : ℝ) : Surreal)| := abs_add_le _ _
    _ ≤ |((PowerSeries.constantCoeff g : ℝ) : Surreal)| + 1 := by linarith

/-- **The faithful jet bound**: `|fevalHS δ f − f₀ − f₁ δ| ≤ (|f₂| + 1) δ²` at every
infinitesimal `δ` — a uniform quadratic bound. -/
theorem abs_fevalHS_sub_le {δ : Surreal.{u}} (hδ : Infinitesimal δ) (f : PowerSeries ℝ) :
    |fevalHS δ f - ((PowerSeries.coeff 0 f : ℝ) : Surreal) -
        ((PowerSeries.coeff 1 f : ℝ) : Surreal) * δ| ≤
      (|((PowerSeries.coeff 2 f : ℝ) : Surreal)| + 1) * δ ^ 2 := by
  obtain ⟨h, hf, hh0⟩ := exists_eq_C_add_C_mul_X_add_X_sq_mul f
  have h1 := congrArg (fevalHS δ) hf
  rw [fevalHS_add, fevalHS_add, fevalHS_C, fevalHS_mul, fevalHS_C, fevalHS_X hδ,
    fevalHS_X_pow_mul hδ] at h1
  have h2 := abs_fevalHS_le hδ h
  rw [hh0] at h2
  rw [h1, show ((PowerSeries.coeff 0 f : ℝ) : Surreal) + ((PowerSeries.coeff 1 f : ℝ) : Surreal) * δ
      + δ ^ 2 * fevalHS δ h - ((PowerSeries.coeff 0 f : ℝ) : Surreal) -
      ((PowerSeries.coeff 1 f : ℝ) : Surreal) * δ = δ ^ 2 * fevalHS δ h by ring]
  calc |δ ^ 2 * fevalHS δ h| = δ ^ 2 * |fevalHS δ h| := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg δ)]
    _ ≤ δ ^ 2 * (|((PowerSeries.coeff 2 f : ℝ) : Surreal)| + 1) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg δ)
    _ = _ := by ring

/-- **The faithful jet at the origin**: `δ ↦ fevalHS δ f` has surreal-point derivative `f₁` at
`0` (the faithful counterpart of `hasDerivS_jetExt`). -/
theorem hasDerivS_fevalHS_zero (f : PowerSeries ℝ) :
    HasDerivS (fun δ ↦ fevalHS δ f) (0 : Surreal.{u}) ((PowerSeries.coeff 1 f : ℝ) : Surreal) := by
  refine ⟨|((PowerSeries.coeff 2 f : ℝ) : Surreal)| + 1, fun δ hδ ↦ ?_⟩
  dsimp only
  rw [zero_add, fevalHS_zero_left, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact abs_fevalHS_sub_le hδ f

end Surreal

/-! ### The exponential functional equation in the Hahn-series field -/

/-- Regrouping a finitely supported function on `ℕ × ℕ` along the antidiagonals. -/
theorem finsum_sum_antidiagonal {M : Type*} [AddCommMonoid M] (F : ℕ × ℕ → M)
    (hF : (Function.support F).Finite) :
    ∑ᶠ n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, F p = ∑ᶠ p, F p := by
  classical
  set S := hF.toFinset with hS
  set N := S.image (fun p ↦ p.1 + p.2) with hN
  have h1 : ∑ᶠ p, F p = ∑ p ∈ S, F p :=
    finsum_eq_sum_of_support_subset _ (by rw [hS, Set.Finite.coe_toFinset])
  have h2 : ∑ᶠ n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, F p =
      ∑ n ∈ N, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, F p := by
    apply finsum_eq_sum_of_support_subset
    intro n hn
    obtain ⟨p, hp, hp0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    rw [Finset.mem_coe, hN, Finset.mem_image]
    exact ⟨p, hF.mem_toFinset.2 hp0, Finset.HasAntidiagonal.mem_antidiagonal.1 hp⟩
  rw [h1, h2, ← Finset.sum_biUnion]
  · symm
    apply Finset.sum_subset
    · intro p hp
      exact Finset.mem_biUnion.2 ⟨p.1 + p.2, Finset.mem_image_of_mem _ hp,
        Finset.HasAntidiagonal.mem_antidiagonal.2 rfl⟩
    · intro p _ hp
      have h : p ∉ Function.support F := fun h ↦ hp (hF.mem_toFinset.2 h)
      simpa using h
  · intro m _ n _ hmn
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpm hpn
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpm hpn
    exact hmn (hpm.symm.trans hpn)

/-- **Regrouping a summable family along the antidiagonals**: if `v n = ∑_{i+j=n} u (i, j)`
then the two families have the same Hahn sum. -/
theorem HahnSeries.SummableFamily.hsum_eq_hsum_of_antidiagonal {Γ R : Type*} [PartialOrder Γ]
    [AddCommMonoid R] {u : HahnSeries.SummableFamily Γ R (ℕ × ℕ)}
    {v : HahnSeries.SummableFamily Γ R ℕ}
    (h : ∀ n, v n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, u p) : v.hsum = u.hsum := by
  ext g
  rw [HahnSeries.SummableFamily.coeff_hsum, HahnSeries.SummableFamily.coeff_hsum]
  simp_rw [h, HahnSeries.coeff_sum]
  exact finsum_sum_antidiagonal (fun p ↦ (u p).coeff g) (u.finite_co_support g)

namespace Surreal

open SurrealHahnSeries OrderDual HahnSeries

/-- The `n`-th term of the exponential family at `c` is the `n`-th coefficient of the rescaled
exponential series `exp (cX)` over the Hahn-series field. -/
theorem coeff_rescale_exp_eq (c : HahnSeries Surreal.{u}ᵒᵈ ℝ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.exp ℝ) • c ^ n =
      PowerSeries.coeff n
        (PowerSeries.rescale c (PowerSeries.exp (HahnSeries Surreal.{u}ᵒᵈ ℝ))) := by
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_exp, eq_ratCast,
    eq_ratCast, mul_comm, ← HahnSeries.single_zero_ratCast, HahnSeries.single_zero_mul_eq_smul]

/-- **THE EXPONENTIAL FUNCTIONAL EQUATION IN THE HAHN-SERIES FIELD**: for Hahn series `a, b` of
positive order, `heval (a + b) exp = heval a exp * heval b exp`. Proof: the product of the two
exponential families regrouped along the antidiagonals is the exponential family at `a + b`,
by the coefficient identity of mathlib's `exp_mul_exp_eq_exp_add` over the Hahn-series field. -/
theorem heval_exp_add {a b : HahnSeries Surreal.{u}ᵒᵈ ℝ} (ha : 0 < a.orderTop)
    (hb : 0 < b.orderTop) :
    PowerSeries.heval (a + b) (PowerSeries.exp ℝ) =
      PowerSeries.heval a (PowerSeries.exp ℝ) * PowerSeries.heval b (PowerSeries.exp ℝ) := by
  have hab : 0 < (a + b).orderTop :=
    lt_of_lt_of_le (lt_min ha hb) HahnSeries.min_orderTop_le_orderTop_add
  rw [PowerSeries.heval_apply, PowerSeries.heval_apply, PowerSeries.heval_apply,
    ← HahnSeries.SummableFamily.hsum_mul]
  apply HahnSeries.SummableFamily.hsum_eq_hsum_of_antidiagonal
  intro n
  rw [HahnSeries.SummableFamily.powerSeriesFamily_of_orderTop_pos hab, coeff_rescale_exp_eq,
    ← PowerSeries.exp_mul_exp_eq_exp_add, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [HahnSeries.SummableFamily.mul_toFun,
    HahnSeries.SummableFamily.powerSeriesFamily_of_orderTop_pos ha,
    HahnSeries.SummableFamily.powerSeriesFamily_of_orderTop_pos hb, coeff_rescale_exp_eq,
    coeff_rescale_exp_eq]

/-! ### The faithful exponential -/

/-- **THE FAITHFUL EXPONENTIAL** `expH ε := fevalHS ε (exp ℝ)`: the exponential power series
evaluated at `ε` through Conway's isomorphism. A total function; honest on infinitesimals. -/
def expH (ε : Surreal.{u}) : Surreal.{u} :=
  fevalHS ε (PowerSeries.exp ℝ)

theorem expH_def (ε : Surreal.{u}) : expH ε = fevalHS ε (PowerSeries.exp ℝ) := rfl

@[simp]
theorem expH_zero : expH (0 : Surreal.{u}) = 1 := by
  rw [expH, fevalHS_zero_left, PowerSeries.constantCoeff_exp, Real.toSurreal_one]

theorem hevalS_exp_add {σ τ : Surreal.{u}} (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) :
    hevalS (σ + τ) (PowerSeries.exp ℝ) =
      hevalS σ (PowerSeries.exp ℝ) * hevalS τ (PowerSeries.exp ℝ) :=
  toHahn_injective (by
    rw [toHahn_mul, toHahn_hevalS, toHahn_hevalS, toHahn_hevalS, toHahnSeries_add, toHahn_add,
      heval_exp_add (orderTop_pos_of_infinitesimal hσ) (orderTop_pos_of_infinitesimal hτ)])

/-- **THE EXPONENTIAL FUNCTIONAL EQUATION, FOR ALL INFINITESIMALS**:
`expH (σ + τ) = expH σ * expH τ` — no comparability of Archimedean classes needed (contrast
`expInf_add_eq_mul_iff_classComparable`). -/
theorem expH_add {σ τ : Surreal.{u}} (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) :
    expH (σ + τ) = expH σ * expH τ := by
  rw [expH, expH, expH, fevalHS, fevalHS, fevalHS, hevalS_exp_add hσ hτ, evalHahn_mul]

/-- **THE REFLECTION LAW** for the faithful exponential. -/
theorem expH_mul_expH_neg {σ : Surreal.{u}} (hσ : Infinitesimal σ) : expH σ * expH (-σ) = 1 := by
  rw [← expH_add hσ hσ.neg, add_neg_cancel, expH_zero]

theorem expH_ne_zero {σ : Surreal.{u}} (hσ : Infinitesimal σ) : expH σ ≠ 0 :=
  left_ne_zero_of_mul_eq_one (expH_mul_expH_neg hσ)

theorem expH_neg_eq_inv {σ : Surreal.{u}} (hσ : Infinitesimal σ) : expH (-σ) = (expH σ)⁻¹ :=
  eq_inv_of_mul_eq_one_right (expH_mul_expH_neg hσ)

theorem expH_sub {σ τ : Surreal.{u}} (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) :
    expH (σ - τ) = expH σ / expH τ := by
  rw [sub_eq_add_neg, expH_add hσ hτ.neg, expH_neg_eq_inv hτ, div_eq_mul_inv]

theorem expH_nsmul {σ : Surreal.{u}} (hσ : Infinitesimal σ) (n : ℕ) :
    expH (n • σ) = expH σ ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, expH_zero]
  | succ n ih => rw [succ_nsmul, expH_add (hσ.nsmul n) hσ, ih, pow_succ]

theorem expH_zsmul {σ : Surreal.{u}} (hσ : Infinitesimal σ) (n : ℤ) :
    expH (n • σ) = expH σ ^ n := by
  induction n using Int.induction_on with
  | zero => rw [zero_zsmul, zpow_zero, expH_zero]
  | succ i ih =>
    rw [add_zsmul, one_zsmul, expH_add (hσ.zsmul i) hσ, ih, zpow_add_one₀ (expH_ne_zero hσ)]
  | pred i ih =>
    rw [sub_zsmul, one_zsmul, expH_add (hσ.zsmul (-i)) hσ.neg, expH_neg_eq_inv hσ, ih,
      zpow_sub_one₀ (expH_ne_zero hσ)]

/-- The uniform quadratic bound `|expH σ − 1 − σ| ≤ (3/2) σ²`. -/
theorem abs_expH_sub_one_sub_le {σ : Surreal.{u}} (hσ : Infinitesimal σ) :
    |expH σ - 1 - σ| ≤ 3 / 2 * σ ^ 2 := by
  have h := abs_fevalHS_sub_le hσ (PowerSeries.exp ℝ)
  have h0 : ((PowerSeries.coeff 0 (PowerSeries.exp ℝ) : ℝ) : Surreal.{u}) = 1 := by
    rw [PowerSeries.coeff_exp]
    simp
  have h1 : ((PowerSeries.coeff 1 (PowerSeries.exp ℝ) : ℝ) : Surreal.{u}) = 1 := by
    rw [PowerSeries.coeff_exp]
    simp
  have h2 : |((PowerSeries.coeff 2 (PowerSeries.exp ℝ) : ℝ) : Surreal.{u})| = 1 / 2 := by
    rw [PowerSeries.coeff_exp, eq_ratCast, Real.toSurreal_ratCast]
    norm_num [Nat.factorial]
  rw [h0, h1, h2, one_mul] at h
  rw [expH]
  calc |fevalHS σ (PowerSeries.exp ℝ) - 1 - σ| ≤ (1 / 2 + 1) * σ ^ 2 := h
    _ = 3 / 2 * σ ^ 2 := by ring

theorem infinitesimal_expH_sub_one {σ : Surreal.{u}} (hσ : Infinitesimal σ) :
    Infinitesimal (expH σ - 1) := by
  have h := isScaleSum_fevalHS hσ (PowerSeries.exp ℝ) 1
  rw [scalePartial_one, pow_one, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_exp, Real.toSurreal_one] at h
  exact lt_of_lt_of_le hσ h

theorem isFinite_expH {σ : Surreal.{u}} (hσ : Infinitesimal σ) : IsFinite (expH σ) :=
  isFinite_fevalHS hσ _

theorem stdPart_expH {σ : Surreal.{u}} (hσ : Infinitesimal σ) : stdPart (expH σ) = 1 := by
  have h := stdPart_eq_of_infinitesimal_sub (r := 1) (x := expH σ) (by
    rw [Real.toSurreal_one]; exact infinitesimal_expH_sub_one hσ)
  exact h

theorem expH_pos {σ : Surreal.{u}} (hσ : Infinitesimal σ) : 0 < expH σ := by
  have h := expH_add hσ.half hσ.half
  rw [add_halves] at h
  rw [h]
  exact mul_self_pos.2 (expH_ne_zero hσ.half)

theorem one_lt_expH_of_pos {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : 0 < σ) :
    1 < expH σ := by
  have h := (abs_le.1 (abs_expH_sub_one_sub_le hσ)).1
  have h2 : (2 : ℕ) • |σ| < 1 := infinitesimal_iff.1 hσ 2
  rw [nsmul_eq_mul, abs_of_pos hσ0] at h2
  push_cast at h2
  nlinarith

theorem expH_lt_one_of_neg {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : σ < 0) :
    expH σ < 1 := by
  have h := one_lt_expH_of_pos hσ.neg (neg_pos.2 hσ0)
  rw [expH_neg_eq_inv hσ] at h
  exact (one_lt_inv₀ (expH_pos hσ)).1 h

/-- **The faithful exponential is injective on infinitesimals.** -/
theorem expH_inj {σ τ : Surreal.{u}} (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) :
    expH σ = expH τ ↔ σ = τ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hστ : Infinitesimal (σ - τ) := by
    rw [sub_eq_add_neg]
    exact hσ.add hτ.neg
  have h1 : expH (σ - τ) = 1 := by
    rw [expH_sub hσ hτ, h, div_self (expH_ne_zero hτ)]
  rcases lt_trichotomy (σ - τ) 0 with hlt | heq | hgt
  · exact absurd h1 (expH_lt_one_of_neg hστ hlt).ne
  · exact sub_eq_zero.1 heq
  · exact absurd h1 (one_lt_expH_of_pos hστ hgt).ne'

theorem expH_lt_expH_of_lt {σ τ : Surreal.{u}} (hσ : Infinitesimal σ) (hτ : Infinitesimal τ)
    (h : σ < τ) : expH σ < expH τ := by
  have hτσ : Infinitesimal (τ - σ) := by
    rw [sub_eq_add_neg]
    exact hτ.add hσ.neg
  have h1 : 1 < expH (τ - σ) := one_lt_expH_of_pos hτσ (sub_pos.2 h)
  rw [expH_sub hτ hσ, lt_div_iff₀ (expH_pos hσ), one_mul] at h1
  exact h1

/-! ### The faithful exponential ODE: `exp′ = exp` at every infinitesimal -/

/-- **THE FAITHFUL EXPONENTIAL ODE**: `expH` has surreal-point derivative `expH σ` at every
infinitesimal `σ` (including `0`), with the finite constant `(3/2)|expH σ|` — exactly what
`kernel_exponential` shows the canonical-sum exponential cannot do. -/
theorem hasDerivS_expH {σ : Surreal.{u}} (hσ : Infinitesimal σ) : HasDerivS expH σ (expH σ) := by
  refine ⟨|expH σ| * (3 / 2), fun δ hδ ↦ ?_⟩
  calc |expH (σ + δ) - expH σ - expH σ * δ| = |expH σ| * |expH δ - 1 - δ| := by
        rw [expH_add hσ hδ, ← abs_mul]
        congr 1
        ring
    _ ≤ |expH σ| * (3 / 2 * δ ^ 2) :=
        mul_le_mul_of_nonneg_left (abs_expH_sub_one_sub_le hδ) (abs_nonneg _)
    _ = |expH σ| * (3 / 2) * δ ^ 2 := by ring

/-- **THE CONTRAST**: at every nonzero infinitesimal, the faithful exponential satisfies
`exp′ = exp` while the canonical-sum exponential `expInf'` does not. -/
theorem hasDerivS_expH_and_not_hasDerivS_expInf' {σ : Surreal.{u}} (hσ : Infinitesimal σ)
    (hσ0 : σ ≠ 0) :
    HasDerivS expH σ (expH σ) ∧ ¬ HasDerivS expInf' σ (expInf' σ) :=
  ⟨hasDerivS_expH hσ, not_hasDerivS_expInf'_self hσ hσ0⟩

/-! ### The finite galaxy -/

/-- **The faithful exponential on the finite galaxy**: `e^{st x} · expH (x − st x)`. -/
def expFinH (x : Surreal.{u}) : Surreal.{u} :=
  (Real.exp (stdPart x) : Surreal) * expH (x - (stdPart x : Surreal))

theorem expFinH_realCast (r : ℝ) : expFinH (r : Surreal.{u}) = (Real.exp r : Surreal) := by
  rw [expFinH, stdPart_realCast, sub_self, expH_zero, mul_one]

theorem expFinH_eq_expFin_realCast (r : ℝ) : expFinH (r : Surreal.{u}) = expFin (r : Surreal) := by
  rw [expFinH_realCast, expFin_realCast]

theorem expFinH_zero : expFinH (0 : Surreal.{u}) = 1 := by
  have h := expFinH_realCast.{u} 0
  rwa [Real.toSurreal_zero, Real.exp_zero, Real.toSurreal_one] at h

theorem expFinH_of_infinitesimal {ε : Surreal.{u}} (hε : Infinitesimal ε) : expFinH ε = expH ε := by
  rw [expFinH, hε.stdPart_eq_zero, Real.exp_zero, Real.toSurreal_one, Real.toSurreal_zero,
    sub_zero, one_mul]

/-- An infinitesimal increment factors out as `expH δ`. -/
theorem expFinH_add_infinitesimal {x δ : Surreal.{u}} (hx : IsFinite x) (hδ : Infinitesimal δ) :
    expFinH (x + δ) = expFinH x * expH δ := by
  rw [expFinH, expFinH, stdPart_add_eq_left hδ,
    show x + δ - (stdPart x : Surreal) = (x - (stdPart x : Surreal)) + δ by ring,
    expH_add (infinitesimal_sub_stdPart hx) hδ]
  ring

/-- **THE FUNCTIONAL EQUATION ON THE FINITE GALAXY.** -/
theorem expFinH_add {x y : Surreal.{u}} (hx : IsFinite x) (hy : IsFinite y) :
    expFinH (x + y) = expFinH x * expFinH y := by
  unfold expFinH
  rw [stdPart_add hx hy, Real.exp_add, Real.toSurreal_mul,
    show x + y - ((stdPart x + stdPart y : ℝ) : Surreal) =
      (x - (stdPart x : Surreal)) + (y - (stdPart y : Surreal)) by
        rw [Real.toSurreal_add]; ring,
    expH_add (infinitesimal_sub_stdPart hx) (infinitesimal_sub_stdPart hy)]
  ring

theorem expFinH_pos {x : Surreal.{u}} (hx : IsFinite x) : 0 < expFinH x :=
  mul_pos (Real.toSurreal_pos_iff.2 (Real.exp_pos _)) (expH_pos (infinitesimal_sub_stdPart hx))

theorem stdPart_expFinH {x : Surreal.{u}} (hx : IsFinite x) :
    stdPart (expFinH x) = Real.exp (stdPart x) := by
  rw [expFinH, stdPart_mul (isFinite_realCast _) (isFinite_expH (infinitesimal_sub_stdPart hx)),
    stdPart_realCast, stdPart_expH (infinitesimal_sub_stdPart hx), mul_one]

theorem isFinite_expFinH {x : Surreal.{u}} (hx : IsFinite x) : IsFinite (expFinH x) :=
  (isFinite_realCast _).mul (isFinite_expH (infinitesimal_sub_stdPart hx))

/-- **`exp′ = exp` ON THE WHOLE FINITE GALAXY**: `expFinH` has surreal-point derivative
`expFinH x` at every finite `x`. -/
theorem hasDerivS_expFinH {x : Surreal.{u}} (hx : IsFinite x) :
    HasDerivS expFinH x (expFinH x) := by
  refine ⟨|expFinH x| * (3 / 2), fun δ hδ ↦ ?_⟩
  calc |expFinH (x + δ) - expFinH x - expFinH x * δ| = |expFinH x| * |expH δ - 1 - δ| := by
        rw [expFinH_add_infinitesimal hx hδ, ← abs_mul]
        congr 1
        ring
    _ ≤ |expFinH x| * (3 / 2 * δ ^ 2) :=
        mul_le_mul_of_nonneg_left (abs_expH_sub_one_sub_le hδ) (abs_nonneg _)
    _ = |expFinH x| * (3 / 2) * δ ^ 2 := by ring

/-! ### Faithful versus canonical -/

theorem coeff_exp_ne_zero (k : ℕ) : PowerSeries.coeff k (PowerSeries.exp ℝ) ≠ 0 := by
  rw [PowerSeries.coeff_exp]
  exact (map_ne_zero _).2 (one_div_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)))

theorem scaleTerm_exp (ε : Surreal.{u}) (k : ℕ) :
    scaleTerm ε (PowerSeries.exp ℝ) k = ε ^ k / ((k.factorial : ℕ) : Surreal) := by
  have h := scaleTerm_rescale_exp ε 1 k
  rwa [PowerSeries.rescale_one, RingHom.id_apply, Real.toSurreal_one, one_mul] at h

/-- **The faithful exponential is a Hahn sum of the exponential series.** -/
theorem isHahnSum_expSeries_expH {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    IsHahnSum (fun k ↦ ε ^ k / ((k.factorial : ℕ) : Surreal)) (expH ε) := by
  have h := isScaleSum_fevalHS hε (PowerSeries.exp ℝ)
  rw [isScaleSum_iff_isHahnSum ε coeff_exp_ne_zero] at h
  have hfun : scaleTerm ε (PowerSeries.exp ℝ) = fun k ↦ ε ^ k / ((k.factorial : ℕ) : Surreal) :=
    funext (scaleTerm_exp ε)
  rwa [hfun] at h

theorem isScaleSum_exp_expH {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    IsScaleSum ε (PowerSeries.exp ℝ) (expH ε) :=
  isScaleSum_fevalHS hε _

/-- **THE CANONICAL EXPONENTIAL IS THE HALO SIMPLIFICATION OF THE FAITHFUL ONE**:
`expInf ε = haloValue |ε| (expH ε)` — the canonical sum is the birthday-simplest point of the
deep halo of the faithful value at scale `|ε|`. -/
theorem expInf_eq_haloValue_expH {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    expInf ε hε hε0 = haloValue |ε| (expH ε) (abs_pos.2 hε0) := by
  unfold expInf
  refine hahnSum_eq_haloValue hε.abs (abs_pos.2 hε0) _ ?_ ?_
  · intro N
    have h := IsHahnSum.mk_sub_le (isHahnSum_hahnSum (expSeries_strict_dominating hε hε0))
      (isHahnSum_expSeries_expH hε) (N + 1)
    refine lt_of_lt_of_le ?_ h
    rw [← abs_pow, ArchimedeanClass.mk_abs, ArchimedeanClass.mk_div, mk_factorial, sub_zero]
    exact mk_pow_lt_mk_pow_succ' hε hε0 N
  · intro m
    refine ⟨m + 1, ?_⟩
    rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero, ← abs_pow, ArchimedeanClass.mk_abs]
    exact mk_pow_lt_mk_pow_succ' hε hε0 m

/-- **The canonical and faithful exponentials agree exactly when the faithful value is
halo-simple at scale `|ε|`.** -/
theorem expInf_eq_expH_iff {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    expInf ε hε hε0 = expH ε ↔ HaloSimple |ε| (expH ε) := by
  rw [expInf_eq_haloValue_expH hε hε0, haloValue_eq_self_iff hε.abs (abs_pos.2 hε0)]

theorem expInf_eq_expH_of_haloSimple {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : ε ≠ 0)
    (h : HaloSimple |ε| (expH ε)) : expInf ε hε hε0 = expH ε :=
  (expInf_eq_expH_iff hε hε0).2 h

/-- The deep halo of the faithful value at scale `|ε|` contains the canonical value. -/
theorem deepHalo_expH_expInf {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    DeepHalo |ε| (expH ε) (expInf ε hε hε0) := by
  rw [expInf_eq_haloValue_expH hε hε0]
  exact deepHalo_haloValue hε.abs (abs_pos.2 hε0) _

/-- **BLINDNESS, CONTRASTED**: at `ε = ω⁻¹ + ω^(−ω)` the canonical exponential does not see
the fine term (`expInf ε = expInf ω⁻¹`), while the faithful exponential does
(`expH ε ≠ expH ω⁻¹`). -/
theorem faithful_sees_fine_term :
    expH (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal)))) ≠ expH (ω^ (-1 : Surreal)) ∧
      expInf (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal))))
          (infinitesimal_wpow_neg_one.add infinitesimal_wpow_neg_omega)
          (add_pos (wpow_pos _) (wpow_pos _)).ne' =
        expInf (ω^ (-1 : Surreal)) infinitesimal_wpow_neg_one (wpow_pos _).ne' := by
  refine ⟨fun h ↦ ?_, expInf_wpow_neg_one_add_wpow_neg_omega⟩
  rw [expH_inj (infinitesimal_wpow_neg_one.add infinitesimal_wpow_neg_omega)
    infinitesimal_wpow_neg_one] at h
  have h2 : ω^ (-(ω^ (1 : Surreal.{u}))) = 0 := by linarith
  exact wpow_ne_zero _ h2

end Surreal

/-! ### Positive instances: monomials are halo-simple, so `expInf = expH` there -/

namespace Surreal

open SurrealHahnSeries OrderDual HahnSeries

theorem toHahnSeries_monomial (c : ℝ) (y : Surreal.{u}) :
    toHahnSeries ((c : Surreal) * ω^ y) = SurrealHahnSeries.single y c :=
  toHahnSeries_eq_iff.2 (evalHahn_single y c)

theorem wpow_nsmul (y : Surreal.{u}) (m : ℕ) : ω^ (m • y) = (ω^ y) ^ m := by
  induction m with
  | zero => rw [zero_nsmul, wpow_zero, pow_zero]
  | succ m ih => rw [succ_nsmul, wpow_add, ih, pow_succ]

theorem infinitesimal_wpow_of_neg {y : Surreal.{u}} (hy : y < 0) : Infinitesimal (ω^ y) := by
  rw [← neg_neg y, wpow_neg]
  exact infinitesimal_inv_wpow (neg_pos.2 hy)

theorem infinitesimal_monomial_of_neg (c : ℝ) {y : Surreal.{u}} (hy : y < 0) :
    Infinitesimal ((c : Surreal) * ω^ y) :=
  infinitesimal_realCast_mul c (infinitesimal_wpow_of_neg hy)

theorem monomial_ne_zero {c : ℝ} (hc : c ≠ 0) (y : Surreal.{u}) : (c : Surreal) * ω^ y ≠ 0 :=
  realCast_mul_ne_zero hc (wpow_ne_zero y)

theorem mk_monomial {c : ℝ} (hc : c ≠ 0) (y : Surreal.{u}) :
    ArchimedeanClass.mk ((c : Surreal) * ω^ y) = ArchimedeanClass.mk (ω^ y) := by
  rw [ArchimedeanClass.mk_mul, mk_realCast hc, zero_add]

theorem nsmul_left_injective_of_ne_zero {y : Surreal.{u}} (hy : y ≠ 0) {m n : ℕ}
    (h : m • y = n • y) : m = n := by
  rw [nsmul_eq_mul, nsmul_eq_mul] at h
  exact_mod_cast mul_right_cancel₀ hy h

theorem orderTop_single_toDual_pos (c : ℝ) {y : Surreal.{u}} (hy : y < 0) :
    0 < (HahnSeries.single (toDual y) c).orderTop := by
  have h := orderTop_pos_of_infinitesimal (infinitesimal_monomial_of_neg c hy)
  rwa [toHahnSeries_monomial, toHahn_single] at h

/-- The coefficient of the monomial exponential at `m • y` is `cᵐ/m!`. -/
theorem coeff_hevalS_monomial_exp (c : ℝ) {y : Surreal.{u}} (hy : y < 0) (m : ℕ) :
    (hevalS ((c : Surreal) * ω^ y) (PowerSeries.exp ℝ)).coeff (m • y) =
      PowerSeries.coeff m (PowerSeries.exp ℝ) * c ^ m := by
  have hpos := orderTop_single_toDual_pos c hy
  rw [← coeff_toHahn_toDual, toHahn_hevalS, toHahnSeries_monomial, toHahn_single,
    PowerSeries.coeff_heval, finsum_eq_single _ m]
  · rw [SummableFamily.coeff_def, SummableFamily.powerSeriesFamily_of_orderTop_pos hpos,
      HahnSeries.coeff_smul, HahnSeries.single_pow, HahnSeries.coeff_single,
      if_pos (show toDual (m • y) = m • toDual y from rfl), smul_eq_mul]
  · intro n hn
    rw [SummableFamily.coeff_def, SummableFamily.powerSeriesFamily_of_orderTop_pos hpos,
      HahnSeries.coeff_smul, HahnSeries.single_pow, HahnSeries.coeff_single, if_neg, smul_zero]
    intro h
    have h' : m • y = n • y := congrArg ofDual h
    exact hn (nsmul_left_injective_of_ne_zero hy.ne h').symm

theorem coeff_hevalS_monomial_exp_eq_zero (c : ℝ) {y : Surreal.{u}} (hy : y < 0)
    {s : Surreal.{u}} (hs : ∀ n : ℕ, s ≠ n • y) :
    (hevalS ((c : Surreal) * ω^ y) (PowerSeries.exp ℝ)).coeff s = 0 := by
  have hpos := orderTop_single_toDual_pos c hy
  rw [← coeff_toHahn_toDual, toHahn_hevalS, toHahnSeries_monomial, toHahn_single,
    PowerSeries.coeff_heval]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  rw [SummableFamily.coeff_def, SummableFamily.powerSeriesFamily_of_orderTop_pos hpos,
    HahnSeries.coeff_smul, HahnSeries.single_pow, HahnSeries.coeff_single, if_neg, smul_zero]
  intro h
  exact hs n (congrArg ofDual h)

/-- The support of the monomial exponential is exactly `{m • y : m ∈ ℕ}`. -/
theorem support_hevalS_monomial_exp {c : ℝ} (hc : c ≠ 0) {y : Surreal.{u}} (hy : y < 0) :
    (hevalS ((c : Surreal) * ω^ y) (PowerSeries.exp ℝ)).support =
      Set.range (fun n : ℕ ↦ n • y) := by
  ext s
  rw [mem_support_iff, Set.mem_range]
  constructor
  · intro h
    by_contra hne
    exact h (coeff_hevalS_monomial_exp_eq_zero c hy fun n hn ↦ hne ⟨n, hn.symm⟩)
  · rintro ⟨n, rfl⟩
    rw [coeff_hevalS_monomial_exp c hy n]
    exact mul_ne_zero (coeff_exp_ne_zero n) (pow_ne_zero n hc)

/-- The monomial exponential has limit length (its support `{m • y}` has no least element). -/
theorem isSuccLimit_length_hevalS_monomial_exp {c : ℝ} (hc : c ≠ 0) {y : Surreal.{u}}
    (hy : y < 0) :
    Order.IsSuccLimit (hevalS ((c : Surreal) * ω^ y) (PowerSeries.exp ℝ)).length := by
  set x := hevalS ((c : Surreal) * ω^ y) (PowerSeries.exp ℝ) with hx
  have hsupp := support_hevalS_monomial_exp hc hy
  rw [← hx] at hsupp
  rcases Ordinal.zero_or_succ_or_isSuccLimit x.length with h0 | ⟨β, hβ⟩ | hlim
  · exfalso
    have hx0 : x = 0 := length_eq_zero.1 h0
    have hmem : (0 : ℕ) • y ∈ x.support := by
      rw [hsupp]
      exact ⟨0, rfl⟩
    rw [hx0, SurrealHahnSeries.support_zero] at hmem
    exact hmem
  · exfalso
    have hβlt : β < x.length := by
      rw [← hβ]
      exact Order.lt_succ β
    have hlb : ∀ s ∈ x.support, (x.exp ⟨β, hβlt⟩).1 ≤ s := by
      intro s hs
      obtain ⟨j, hj⟩ := eq_exp_of_mem_support hs
      rw [← hj]
      refine Subtype.coe_le_coe.2 (exp_le_exp_iff.2 ?_)
      have hj2 : j.1 < Order.succ β := by
        rw [hβ]
        exact j.2
      exact Subtype.mk_le_mk.2 (Order.lt_succ_iff.1 hj2)
    have he : (x.exp ⟨β, hβlt⟩).1 ∈ Set.range (fun n : ℕ ↦ n • y) :=
      (Set.ext_iff.1 hsupp _).1 (x.exp ⟨β, hβlt⟩).2
    obtain ⟨m, hm⟩ := he
    have hmem : (m + 1) • y ∈ x.support := by
      rw [hsupp]
      exact ⟨m + 1, rfl⟩
    have h1 := hlb _ hmem
    rw [← hm, succ_nsmul] at h1
    linarith
  · exact hlim

/-- **THE MONOMIAL INSTANCE**: the faithful exponential of `c ω^y` (`c ≠ 0`, `y < 0`) is
halo-simple at its own scale — the canonical sum of its (monomial-cofinal) normal form. -/
theorem haloSimple_expH_monomial {c : ℝ} (hc : c ≠ 0) {y : Surreal.{u}} (hy : y < 0) :
    HaloSimple |(c : Surreal) * ω^ y| (expH ((c : Surreal) * ω^ y)) := by
  set ε := (c : Surreal.{u}) * ω^ y with hε_def
  set x := hevalS ε (PowerSeries.exp ℝ) with hx
  have hε : Infinitesimal ε := infinitesimal_monomial_of_neg c hy
  have hε0 : ε ≠ 0 := monomial_ne_zero hc y
  have hsupp := support_hevalS_monomial_exp hc hy
  rw [← hε_def, ← hx] at hsupp
  have hlim := isSuccLimit_length_hevalS_monomial_exp hc hy
  rw [← hε_def, ← hx] at hlim
  rw [expH, fevalHS, ← hx, evalHahn]
  refine haloSimple_hahnSumO hlim x.isStrictDom_term fun β hβ ↦ ?_
  obtain ⟨m, hm⟩ : (x.exp ⟨β, hβ⟩).1 ∈ Set.range (fun n : ℕ ↦ n • y) :=
    (Set.ext_iff.1 hsupp _).1 (x.exp ⟨β, hβ⟩).2
  refine ⟨m + 1, ?_⟩
  rw [term_of_lt hβ, ArchimedeanClass.mk_mul, mk_realCast (coeffIdx_ne_zero hβ), zero_add, ← hm,
    wpow_nsmul, ← abs_pow, ArchimedeanClass.mk_abs, ArchimedeanClass.mk_pow]
  have h1 : ArchimedeanClass.mk (ε ^ m) = m • ArchimedeanClass.mk (ω^ y) := by
    rw [ArchimedeanClass.mk_pow, mk_monomial hc]
  rw [← h1]
  exact mk_pow_lt_mk_pow_succ' hε hε0 m

/-- **`expInf = expH` ON MONOMIALS**: for every nonzero real `c` and negative `y`, the canonical
and the faithful exponentials of `c ω^y` coincide. -/
theorem expInf_monomial_eq_expH {c : ℝ} (hc : c ≠ 0) {y : Surreal.{u}} (hy : y < 0) :
    expInf ((c : Surreal) * ω^ y) (infinitesimal_monomial_of_neg c hy) (monomial_ne_zero hc y) =
      expH ((c : Surreal) * ω^ y) :=
  expInf_eq_expH_of_haloSimple _ _ (haloSimple_expH_monomial hc hy)

theorem expInf_wpow_neg_one_eq_expH :
    expInf (ω^ (-1 : Surreal.{u})) infinitesimal_wpow_neg_one (wpow_pos _).ne' =
      expH (ω^ (-1 : Surreal)) := by
  have h := haloSimple_expH_monomial (c := 1) (y := (-1 : Surreal.{u})) one_ne_zero (by norm_num)
  rw [Real.toSurreal_one, one_mul] at h
  exact expInf_eq_expH_of_haloSimple _ _ h

/-- **THE SHARP WITNESS**: at `ε = ω⁻¹ + ω^(−ω)` the faithful and canonical exponentials
differ — the faithful value is not halo-simple at scale `|ε|`. -/
theorem expH_ne_expInf_wpow_neg_one_add_wpow_neg_omega :
    expH (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal)))) ≠
      expInf (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal))))
        (infinitesimal_wpow_neg_one.add infinitesimal_wpow_neg_omega)
        (add_pos (wpow_pos _) (wpow_pos _)).ne' := by
  rw [expInf_wpow_neg_one_add_wpow_neg_omega, expInf_wpow_neg_one_eq_expH]
  exact faithful_sees_fine_term.1

theorem not_haloSimple_expH_wpow_neg_one_add_wpow_neg_omega :
    ¬ HaloSimple |ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal)))|
      (expH (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal))))) := by
  intro h
  exact expH_ne_expInf_wpow_neg_one_add_wpow_neg_omega
    ((expInf_eq_expH_iff _ _).2 h).symm

end Surreal

end
