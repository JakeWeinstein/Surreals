/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.HahnRing
import Mathlib.Algebra.Order.Hom.Ring

/-!
# The transfinite product theorem: Conway's isomorphism `No ≅ ℝ((ω^No))`

`Infinity.NormalFormTheorem` proved Conway's Normal Form Theorem — the evaluation map
`evalHahn : SurrealHahnSeries → Surreal` is a bijection `hahnEquiv` — and `Infinity.HahnRing`
made it additive without exceptions and multiplicative when one factor has finite support. This
file proves multiplicativity for **all** pairs of surreal Hahn series, and assembles Conway's
theorem: the surreal numbers are the ordered field of real Hahn series over themselves,
`hahnOrderRingIso : SurrealHahnSeries ≃+*o Surreal`.

* **Order-preservation.** The order of `SurrealHahnSeries` is the colexicographic order on the
  coefficient functions: `x < y` iff the coefficients agree above some exponent `e` and
  `x.coeff e < y.coeff e` (`SurrealHahnSeries.lt_iff_exists`). So `0 < v` iff the leading
  coefficient of `v` is positive (`pos_of_coeff_pos`), and then `evalHahn v = c ω^e + (residual
  strictly dominated by ω^e)` is positive (`Surreal.evalHahn_pos_of_pos`). Hence
  **`Surreal.evalHahn_strictMono`**, `evalHahn_lt_iff`, `evalHahn_le_iff`, `evalHahn_pos_iff`.
* **The option series.** For `β < x.length`, `optSeries x hβ r := x.truncIdx β + r ω^{e_β}` is
  the prefix before the `β`-th term with a single adjusting term at the `β`-th exponent; it has
  length `β + 1` (`length_optSeries`), evaluates to `hahnSumO x.term β + r ω^{e_β}`
  (`evalHahn_optSeries`), and with `r = ∓ 2|c_β|` its value is exactly the lower/upper option
  `optLoO/optHiO x.term β` of the transfinite option game (`evalHahn_optSeries_lo/hi`). The tail
  `x − optSeries x hβ r` is supported at exponents `≤ e_β` with coefficient `c_β − r` there
  (`le_of_mem_support_sub_optSeries`, `coeff_sub_optSeries_exp`), so `x − (lower option series)`
  is positive and `x − (upper option series)` is negative in the Hahn order.
* **THE TRANSFINITE PRODUCT THEOREM** `Surreal.evalHahn_mul`:
  `evalHahn (x * y) = evalHahn x * evalHahn y` for all `x y`. Induction on the pair
  `(x.length, y.length)`, lexicographically. A factor of successor length splits off its last
  term (`eq_truncIdx_add_single`) and distributivity, `evalHahn_single_mul_eq` and the induction
  hypothesis finish. When both lengths are limits, let `G := optionGameO x.term _ * optionGameO
  y.term _` be the Conway product of the two transfinite option games, so `mk G = X · Y`. Every
  option of `G` is `mulOption` at a pair of options `(a, b)`, whose value is
  `mk a · Y + X · mk b − mk a · mk b`; the option values are evaluations of the shorter option
  series, so by the induction hypothesis on the three shorter pairs and additivity the option's
  value is `evalHahn (w − D)` with `w := x * y` and `D := (x − x_opt)(y − y_opt)` — a Hahn
  series which is positive for same-side pairs (left options) and negative for mixed pairs
  (right options). Order-preservation gives: **`Z := evalHahn w` fits `G`**
  (`out_fits_mul_optionGameO`). Conversely, `Z` has a termwise coarse representative `H`
  (`termRep_evalHahn`), each option of which sits at distance of class `≤ mk (ω^e)` for some
  `w`-exponent `e = e_{β₀} + f_{δ₀}`; the option of `G` at the pair `(β₀ + 1, δ₀)`
  differs from `Z` by `evalHahn D` with `D` supported below `e_{β₀+1} + f_{δ₀} < e`, hence
  strictly finer, so it beats the option of `H`: **`X · Y` fits `H`** and
  `birthday Z ≤ birthday (X · Y)` (`birthday_evalHahn_mul_le`). The uniqueness half of the
  simplicity theorem (`Surreal.eq_mk_of_fits_of_birthday_le`) then gives `Z = mk G = X · Y`. No
  estimate below the supports is ever needed — the cancellation trap `x · x⁻¹ = 1` with both
  factors transfinite is never entered.
* **CONWAY'S THEOREM** `Surreal.hahnRingEquiv : SurrealHahnSeries ≃+* Surreal`,
  `Surreal.hahnOrderRingIso : SurrealHahnSeries ≃+*o Surreal`, with `evalHahnRingHom`,
  `toHahnSeries_mul`, `evalHahn_inv`, `evalHahn_div`, `evalHahn_pow`, `toHahnSeries_inv`.
-/

open ArchimedeanClass IGame Order

universe u

noncomputable section

/-! ### The order of surreal Hahn series: the leading-coefficient criterion -/

namespace SurrealHahnSeries

/-- **The colexicographic order, unfolded**: `x < y` iff the coefficients agree above some
exponent `e` and `x.coeff e < y.coeff e`. -/
theorem lt_iff_exists {x y : SurrealHahnSeries.{u}} :
    x < y ↔ ∃ e, (∀ s, e < s → x.coeff s = y.coeff s) ∧ x.coeff e < y.coeff e := by
  rw [lt_def]
  exact Iff.rfl

/-- Positivity: some coefficient is positive and every higher coefficient vanishes. -/
theorem pos_iff {x : SurrealHahnSeries.{u}} :
    0 < x ↔ ∃ e, (∀ s, e < s → x.coeff s = 0) ∧ 0 < x.coeff e := by
  rw [lt_iff_exists]
  simp only [coeff_zero, Pi.zero_apply, eq_comm]

/-- **A positive leading coefficient makes the series positive.** -/
theorem pos_of_coeff_pos {x : SurrealHahnSeries.{u}} {e : Surreal.{u}}
    (hub : ∀ s ∈ x.support, s ≤ e) (hc : 0 < x.coeff e) : 0 < x :=
  pos_iff.2 ⟨e, fun s hs ↦ by
    by_contra h
    exact (hub s (mem_support_iff.2 h)).not_gt hs, hc⟩

/-- **A negative leading coefficient makes the series negative.** -/
theorem neg_of_coeff_neg {x : SurrealHahnSeries.{u}} {e : Surreal.{u}}
    (hub : ∀ s ∈ x.support, s ≤ e) (hc : x.coeff e < 0) : x < 0 := by
  rw [← neg_pos]
  refine pos_of_coeff_pos (e := e) (fun s hs ↦ hub s ?_) ?_
  · rwa [support_neg] at hs
  · rw [coeff_neg, Pi.neg_apply]
    exact neg_pos.2 hc

/-- The leading exponent of a series whose support is bounded above by one of its
exponents. -/
theorem exp_zero_eq {x : SurrealHahnSeries.{u}} {e : Surreal.{u}} (he : e ∈ x.support)
    (hub : ∀ s ∈ x.support, s ≤ e) (h0 : 0 < x.length) : (x.exp ⟨0, h0⟩).1 = e := by
  refine le_antisymm (hub _ (x.exp _).2) ?_
  obtain ⟨j, hj⟩ := eq_exp_of_mem_support he
  rw [← hj]
  exact Subtype.coe_le_coe.2 (exp_le_exp_iff.2 (Subtype.coe_le_coe.1 _root_.zero_le))

end SurrealHahnSeries

/-! ### Order-preservation of the evaluation -/

namespace Surreal

open SurrealHahnSeries

/-- **The evaluation of a positive series is positive**: its leading term `c ω^e` has `c > 0`, and
the residual is strictly dominated by the leading term. -/
theorem evalHahn_pos_of_pos {v : SurrealHahnSeries.{u}} (hv : 0 < v) : 0 < evalHahn v := by
  obtain ⟨e, hz, hc⟩ := pos_iff.1 hv
  have he : e ∈ v.support := mem_support_iff.2 hc.ne'
  have hub : ∀ s ∈ v.support, s ≤ e := fun s hs ↦
    not_lt.1 fun h ↦ mem_support_iff.1 hs (hz s h)
  have h0 : 0 < v.length := pos_iff_ne_zero.2 fun h ↦ hv.ne' (length_eq_zero.1 h)
  have hexp : (v.exp ⟨0, h0⟩).1 = e := exp_zero_eq he hub h0
  have hterm : v.term 0 = (v.coeff e : Surreal.{u}) * ω^ e := by
    rw [term_of_lt h0, coeffIdx_of_lt h0, hexp]
  have hpos : 0 < v.term 0 := by
    rw [hterm]
    exact mul_pos (Real.toSurreal_pos_iff.2 hc) (wpow_pos e)
  have h1 : hahnSumO v.term 1 = v.term 0 := by
    rw [← zero_add (1 : Ordinal.{u}), hahnSumO_add_one, hahnSumO_zero, zero_add]
  rcases (Order.one_le_iff_ne_zero.2 h0.ne').eq_or_lt with h | h
  · show 0 < hahnSumO v.term v.length
    rw [← h, h1]
    exact hpos
  · have hres := isHahnSumO_evalHahn v 1 h
    have hdom := v.isStrictDom_term zero_lt_one h
    rw [h1] at hres
    have habs := abs_lt_abs_of_mk_lt (hdom.trans_le hres)
    rw [abs_of_pos hpos] at habs
    have := (abs_lt.1 habs).1
    linarith

/-- The evaluation of a negative series is negative. -/
theorem evalHahn_neg_of_neg {v : SurrealHahnSeries.{u}} (hv : v < 0) : evalHahn v < 0 := by
  have h := evalHahn_pos_of_pos (neg_pos.2 hv)
  rwa [evalHahn_neg, neg_pos] at h

/-- **Order-preservation**: `x < y → evalHahn x < evalHahn y`. -/
theorem evalHahn_lt_evalHahn {x y : SurrealHahnSeries.{u}} (h : x < y) :
    evalHahn x < evalHahn y := by
  have := evalHahn_pos_of_pos (sub_pos.2 h)
  rwa [evalHahn_sub, sub_pos] at this

/-- **The evaluation is strictly monotone.** -/
theorem evalHahn_strictMono : StrictMono (evalHahn : SurrealHahnSeries.{u} → Surreal.{u}) :=
  fun _ _ h ↦ evalHahn_lt_evalHahn h

theorem evalHahn_lt_iff {x y : SurrealHahnSeries.{u}} : evalHahn x < evalHahn y ↔ x < y :=
  evalHahn_strictMono.lt_iff_lt

theorem evalHahn_le_iff {x y : SurrealHahnSeries.{u}} : evalHahn x ≤ evalHahn y ↔ x ≤ y :=
  evalHahn_strictMono.le_iff_le

theorem evalHahn_pos_iff {x : SurrealHahnSeries.{u}} : 0 < evalHahn x ↔ 0 < x := by
  rw [← evalHahn_zero, evalHahn_lt_iff]

theorem evalHahn_neg_iff {x : SurrealHahnSeries.{u}} : evalHahn x < 0 ↔ x < 0 := by
  rw [← evalHahn_zero, evalHahn_lt_iff]

theorem evalHahn_nonneg_iff {x : SurrealHahnSeries.{u}} : 0 ≤ evalHahn x ↔ 0 ≤ x := by
  rw [← evalHahn_zero, evalHahn_le_iff]

end Surreal

/-! ### The option series -/

namespace SurrealHahnSeries

variable (x : SurrealHahnSeries.{u}) {β : Ordinal.{u}} (hβ : β < x.length) (r : ℝ)

/-- **The option series at index `β` with adjustment `r`**: the prefix of `x` before its `β`-th
term, plus the single term `r · ω^{e_β}` at the `β`-th exponent. With `r = ∓ 2 |c_β|` these
are the series whose values are the lower and upper options of the transfinite option game. -/
def optSeries : SurrealHahnSeries.{u} :=
  x.truncIdx β + single (x.exp ⟨β, hβ⟩).1 r

theorem coeff_truncIdx_exp : (x.truncIdx β).coeff (x.exp ⟨β, hβ⟩).1 = 0 := by
  rw [truncIdx_of_lt hβ, coeff_trunc_of_le le_rfl]

theorem lt_of_mem_support_truncIdx {s : Surreal.{u}} (hs : s ∈ (x.truncIdx β).support) :
    (x.exp ⟨β, hβ⟩).1 < s := by
  rw [truncIdx_of_lt hβ, support_trunc] at hs
  exact hs.2

/-- Every exponent of the option series is `≥ e_β`. -/
theorem le_of_mem_support_optSeries {s : Surreal.{u}} (hs : s ∈ (optSeries x hβ r).support) :
    (x.exp ⟨β, hβ⟩).1 ≤ s := by
  rcases support_add_subset hs with h | h
  · exact (lt_of_mem_support_truncIdx x hβ h).le
  · exact (Set.mem_singleton_iff.1 (support_single_subset h)).ge

theorem coeff_optSeries_exp : (optSeries x hβ r).coeff (x.exp ⟨β, hβ⟩).1 = r := by
  rw [optSeries, coeff_add_apply, coeff_truncIdx_exp, coeff_single_self, zero_add]

theorem trunc_optSeries : (optSeries x hβ r).trunc (x.exp ⟨β, hβ⟩).1 = x.truncIdx β := by
  rw [optSeries, trunc_add, trunc_single_of_le le_rfl, add_zero, truncIdx_of_lt hβ, trunc_trunc,
    max_self]

/-- **The option series has length `β + 1`.** -/
theorem length_optSeries (hr : r ≠ 0) : (optSeries x hβ r).length = β + 1 := by
  have he : (x.exp ⟨β, hβ⟩).1 ∈ (optSeries x hβ r).support := by
    rw [mem_support_iff, coeff_optSeries_exp]
    exact hr
  rw [length_eq_length_trunc_add_one _ he (fun s hs ↦ le_of_mem_support_optSeries x hβ r hs),
    trunc_optSeries, length_truncIdx, min_eq_left hβ.le]

/-- **The tail below the option series is supported at exponents `≤ e_β`.** -/
theorem le_of_mem_support_sub_optSeries {s : Surreal.{u}}
    (hs : s ∈ (x - optSeries x hβ r).support) : s ≤ (x.exp ⟨β, hβ⟩).1 := by
  by_contra h
  rw [not_le] at h
  rw [mem_support_iff, coeff_sub_apply, optSeries, coeff_add_apply, truncIdx_of_lt hβ,
    coeff_trunc_of_lt h, coeff_single_of_ne h.ne, add_zero, sub_self] at hs
  exact hs rfl

/-- The coefficient of the tail at `e_β` is `c_β − r`. -/
theorem coeff_sub_optSeries_exp :
    (x - optSeries x hβ r).coeff (x.exp ⟨β, hβ⟩).1 = x.coeffIdx β - r := by
  rw [coeff_sub_apply, coeff_optSeries_exp, coeffIdx_of_lt hβ]

theorem sub_optSeries_pos (hr : r < x.coeffIdx β) : 0 < x - optSeries x hβ r :=
  pos_of_coeff_pos (fun s hs ↦ le_of_mem_support_sub_optSeries x hβ r hs)
    (by rw [coeff_sub_optSeries_exp]; exact sub_pos.2 hr)

theorem sub_optSeries_neg (hr : x.coeffIdx β < r) : x - optSeries x hβ r < 0 :=
  neg_of_coeff_neg (fun s hs ↦ le_of_mem_support_sub_optSeries x hβ r hs)
    (by rw [coeff_sub_optSeries_exp]; exact sub_neg.2 hr)

/-- `x − (lower option series) > 0`: the leading coefficient is `c_β + 2|c_β| > 0`. -/
theorem sub_optSeries_lo_pos : 0 < x - optSeries x hβ (-(2 * |x.coeffIdx β|)) :=
  sub_optSeries_pos x hβ _ (by
    have := abs_pos.2 (coeffIdx_ne_zero hβ)
    have := neg_abs_le (x.coeffIdx β)
    linarith)

/-- `x − (upper option series) < 0`: the leading coefficient is `c_β − 2|c_β| < 0`. -/
theorem sub_optSeries_hi_neg : x - optSeries x hβ (2 * |x.coeffIdx β|) < 0 :=
  sub_optSeries_neg x hβ _ (by
    have := abs_pos.2 (coeffIdx_ne_zero hβ)
    have := le_abs_self (x.coeffIdx β)
    linarith)

theorem neg_two_abs_coeffIdx_ne_zero (hβ : β < x.length) : -(2 * |x.coeffIdx β|) ≠ 0 :=
  neg_ne_zero.2 (mul_ne_zero two_ne_zero (abs_ne_zero.2 (coeffIdx_ne_zero hβ)))

theorem two_abs_coeffIdx_ne_zero (hβ : β < x.length) : 2 * |x.coeffIdx β| ≠ 0 :=
  mul_ne_zero two_ne_zero (abs_ne_zero.2 (coeffIdx_ne_zero hβ))

/-- **A series of successor length is its prefix plus its last term.** -/
theorem eq_truncIdx_add_single (h : x.length ≤ β + 1) :
    x = x.truncIdx β + single (x.exp ⟨β, hβ⟩).1 (x.coeffIdx β) := by
  have hlb : (x.exp ⟨β, hβ⟩).1 ∈ lowerBounds x.support := by
    intro s hs
    obtain ⟨j, rfl⟩ := eq_exp_of_mem_support hs
    have hj : j.1 ≤ β := lt_add_one_iff.1 (j.2.trans_le h)
    exact Subtype.coe_le_coe.2 (exp_le_exp_iff.2 (Subtype.coe_le_coe.1 hj))
  rw [truncIdx_of_lt hβ, coeffIdx_of_lt hβ]
  exact (trunc_add_single hlb).symm

/-- Support bound for a product from support bounds for the factors. -/
theorem le_add_of_mem_support_mul {x y : SurrealHahnSeries.{u}} {a b : Surreal.{u}}
    (hx : ∀ s ∈ x.support, s ≤ a) (hy : ∀ s ∈ y.support, s ≤ b) :
    ∀ s ∈ (x * y).support, s ≤ a + b := by
  intro s hs
  obtain ⟨a', ha', b', hb', rfl⟩ := exists_add_eq_of_mem_support_mul hs
  exact add_le_add (hx a' ha') (hy b' hb')

/-- A series supported at exponents `≤ a` is killed by truncation at `a`. -/
theorem trunc_eq_zero_of_support_le {x : SurrealHahnSeries.{u}} {a : Surreal.{u}}
    (hx : ∀ s ∈ x.support, s ≤ a) : x.trunc a = 0 := by
  ext s
  simp only [coeff_trunc, coeff_zero, Pi.zero_apply]
  split_ifs with h
  · by_contra hne
    exact (hx s (mem_support_iff.2 hne)).not_gt h
  · rfl

end SurrealHahnSeries

namespace Surreal

open SurrealHahnSeries

variable (x : SurrealHahnSeries.{u}) {β : Ordinal.{u}} (hβ : β < x.length) (r : ℝ)

/-- **The value of the option series**: `hahnSumO x.term β + r · ω^{e_β}`. -/
theorem evalHahn_optSeries :
    evalHahn (optSeries x hβ r) =
      hahnSumO x.term β + (r : Surreal.{u}) * ω^ (x.exp ⟨β, hβ⟩).1 := by
  rw [optSeries, evalHahn_add', evalHahn_truncIdx, min_eq_left hβ.le, evalHahn_single]

/-- **The lower option series evaluates to the lower option** `optLoO x.term β`. -/
theorem evalHahn_optSeries_lo :
    evalHahn (optSeries x hβ (-(2 * |x.coeffIdx β|))) = optLoO x.term β := by
  rw [evalHahn_optSeries, optLoO, term_of_lt hβ, Real.toSurreal_neg, Real.toSurreal_mul,
    Real.toSurreal_abs, abs_mul, abs_of_pos (wpow_pos _), Real.toSurreal_ofNat]
  ring

/-- **The upper option series evaluates to the upper option** `optHiO x.term β`. -/
theorem evalHahn_optSeries_hi :
    evalHahn (optSeries x hβ (2 * |x.coeffIdx β|)) = optHiO x.term β := by
  rw [evalHahn_optSeries, optHiO, term_of_lt hβ, Real.toSurreal_mul,
    Real.toSurreal_abs, abs_mul, abs_of_pos (wpow_pos _), Real.toSurreal_ofNat]
  ring

/-- **The class of the evaluation of a series supported at exponents `≤ a` is at least
`mk (ω^a)`.** -/
theorem mk_wpow_le_mk_evalHahn_of_support_le {x : SurrealHahnSeries.{u}} {a : Surreal.{u}}
    (hx : ∀ s ∈ x.support, s ≤ a) :
    ArchimedeanClass.mk (ω^ a) ≤ ArchimedeanClass.mk (evalHahn x) := by
  have h := mk_wpow_le_mk_evalHahn_sub_trunc x a
  rwa [trunc_eq_zero_of_support_le hx, evalHahn_zero, sub_zero] at h

/-! ### The product game: option values -/

/-- **The value of a product option, as an evaluation**: if the option values are evaluations of
`xo` and `yo`, and the products `xo · y`, `x · yo`, `xo · yo` evaluate multiplicatively, then
`mk a · Y + X · mk b − mk a · mk b = evalHahn (x * y) − evalHahn ((x − xo) (y − yo))`. -/
private theorem option_value_eq {x y xo yo : SurrealHahnSeries.{u}}
    (h1 : evalHahn (xo * y) = evalHahn xo * evalHahn y)
    (h2 : evalHahn (x * yo) = evalHahn x * evalHahn yo)
    (h3 : evalHahn (xo * yo) = evalHahn xo * evalHahn yo) :
    evalHahn xo * evalHahn y + evalHahn x * evalHahn yo - evalHahn xo * evalHahn yo =
      evalHahn (x * y) - evalHahn ((x - xo) * (y - yo)) := by
  rw [← h1, ← h2, ← h3, ← evalHahn_add', ← evalHahn_sub, ← evalHahn_sub]
  congr 1
  ring

/-- The value of the product option at representatives of the option values. -/
private theorem mk_mulOption_out {Gx Gy : IGame.{u}} [Gx.Numeric] [Gy.Numeric]
    {x y xo yo : SurrealHahnSeries.{u}} (hGx : Surreal.mk Gx = evalHahn x)
    (hGy : Surreal.mk Gy = evalHahn y) {A B : Surreal.{u}} (hA : evalHahn xo = A)
    (hB : evalHahn yo = B)
    (h1 : evalHahn (xo * y) = evalHahn xo * evalHahn y)
    (h2 : evalHahn (x * yo) = evalHahn x * evalHahn yo)
    (h3 : evalHahn (xo * yo) = evalHahn xo * evalHahn yo) :
    Surreal.mk (mulOption Gx Gy A.out B.out) =
      evalHahn (x * y) - evalHahn ((x - xo) * (y - yo)) := by
  rw [mk_mulOption, out_eq, out_eq, hGx, hGy, ← hA, ← hB]
  exact option_value_eq h1 h2 h3

/-! ### The uniqueness half of the simplicity theorem, value form -/

/-- **Uniqueness of the simplest fit, value form**: if `w` fits the numeric game `G` and is born no
later than the value of `G`, then `w` *is* the value of `G`. -/
theorem eq_mk_of_fits_of_birthday_le {G : IGame.{u}} [G.Numeric] {w : Surreal.{u}}
    (h : w.out.Fits G) (hb : w.birthday ≤ (Surreal.mk G).birthday) : w = Surreal.mk G := by
  obtain ⟨g, hgn, hgw, hgb⟩ := birthday_eq_iGameBirthday w
  haveI := hgn
  have hfit : g.Fits G := h.congr (Surreal.mk_eq_mk.1 (by rw [out_eq, hgw]))
  have hequiv : g ≈ G := hfit.equiv_of_forall_birthday_le fun z hz hzG ↦ by
    haveI := hz
    rw [hgb]
    exact hb.trans ((birthday_mk_le_of_fits
      (hzG.congr (Surreal.mk_out_equiv z).symm)).trans (birthday_mk_le z))
  rw [← hgw]
  exact Surreal.mk_eq hequiv

/-! ### The successor steps -/

/-- The successor step, first factor: split off the last term of `x`. -/
private theorem evalHahn_mul_of_length_eq_add_one {x y : SurrealHahnSeries.{u}}
    {β : Ordinal.{u}} (hx : x.length = β + 1)
    (ih : evalHahn (x.truncIdx β * y) = evalHahn (x.truncIdx β) * evalHahn y) :
    evalHahn (x * y) = evalHahn x * evalHahn y := by
  have hβ : β < x.length := by rw [hx]; exact lt_add_one β
  have hdec := eq_truncIdx_add_single x hβ hx.le
  have key : evalHahn ((x.truncIdx β + single (x.exp ⟨β, hβ⟩).1 (x.coeffIdx β)) * y) =
      evalHahn (x.truncIdx β + single (x.exp ⟨β, hβ⟩).1 (x.coeffIdx β)) * evalHahn y := by
    rw [add_mul, evalHahn_add', evalHahn_add', ih, evalHahn_single_mul_eq, add_mul]
  rwa [← hdec] at key

/-- The successor step, second factor. -/
private theorem evalHahn_mul_of_length_eq_add_one' {x y : SurrealHahnSeries.{u}}
    {δ : Ordinal.{u}} (hy : y.length = δ + 1)
    (ih : evalHahn (x * y.truncIdx δ) = evalHahn x * evalHahn (y.truncIdx δ)) :
    evalHahn (x * y) = evalHahn x * evalHahn y := by
  rw [mul_comm, mul_comm (evalHahn x)]
  exact evalHahn_mul_of_length_eq_add_one hy (by rw [mul_comm, ih, mul_comm])

/-! ### The both-limit case: the two fits arguments -/

/-- **The product value fits the product game.** For `x`, `y` of limit length, every option of
the Conway product `optionGameO x.term _ * optionGameO y.term _` has value
`evalHahn (x * y) − evalHahn D` with `D = (x − x_opt)(y − y_opt)` positive for same-side pairs
and negative for mixed pairs (in the Hahn order), so by order-preservation the left options are
below `evalHahn (x * y)` and the right options above. -/
private theorem out_fits_mul_optionGameO {x y : SurrealHahnSeries.{u}}
    (hlim : IsSuccLimit x.length) (hlim' : IsSuccLimit y.length)
    (ih : ∀ β (hβ : β < x.length) δ (hδ : δ < y.length) (r s : ℝ), r ≠ 0 → s ≠ 0 →
      evalHahn (optSeries x hβ r * y) = evalHahn (optSeries x hβ r) * evalHahn y ∧
      evalHahn (x * optSeries y hδ s) = evalHahn x * evalHahn (optSeries y hδ s) ∧
      evalHahn (optSeries x hβ r * optSeries y hδ s) =
        evalHahn (optSeries x hβ r) * evalHahn (optSeries y hδ s)) :
    (evalHahn (x * y)).out.Fits (optionGameO x.term x.length * optionGameO y.term y.length) := by
  haveI := numeric_optionGameO hlim x.isStrictDom_term
  haveI := numeric_optionGameO hlim' y.isStrictDom_term
  have hmkGx : Surreal.mk (optionGameO x.term x.length) = evalHahn x :=
    mk_optionGameO_eq_hahnSumO hlim x.isStrictDom_term
  have hmkGy : Surreal.mk (optionGameO y.term y.length) = evalHahn y :=
    mk_optionGameO_eq_hahnSumO hlim' y.isStrictDom_term
  constructor
  · refine forall_moves_mul.2 fun p a ha b hb ↦ ?_
    cases p with
    | left =>
      rw [Player.left_mul] at hb
      rw [leftMoves_optionGameO] at ha hb
      obtain ⟨⟨β, hβ⟩, rfl⟩ := ha
      obtain ⟨⟨δ, hδ⟩, rfl⟩ := hb
      obtain ⟨h1, h2, h3⟩ := ih β hβ δ hδ _ _ (neg_two_abs_coeffIdx_ne_zero x hβ)
        (neg_two_abs_coeffIdx_ne_zero y hδ)
      refine IGame.Numeric.not_le.2 ?_
      rw [← Surreal.mk_lt_mk, out_eq, mk_mulOption_out hmkGx hmkGy (evalHahn_optSeries_lo x hβ)
        (evalHahn_optSeries_lo y hδ) h1 h2 h3]
      exact sub_lt_self _ (evalHahn_pos_iff.2
        (mul_pos (sub_optSeries_lo_pos x hβ) (sub_optSeries_lo_pos y hδ)))
    | right =>
      rw [Player.right_mul, Player.neg_left] at hb
      rw [rightMoves_optionGameO] at ha hb
      obtain ⟨⟨β, hβ⟩, rfl⟩ := ha
      obtain ⟨⟨δ, hδ⟩, rfl⟩ := hb
      obtain ⟨h1, h2, h3⟩ := ih β hβ δ hδ _ _ (two_abs_coeffIdx_ne_zero x hβ)
        (two_abs_coeffIdx_ne_zero y hδ)
      refine IGame.Numeric.not_le.2 ?_
      rw [← Surreal.mk_lt_mk, out_eq, mk_mulOption_out hmkGx hmkGy (evalHahn_optSeries_hi x hβ)
        (evalHahn_optSeries_hi y hδ) h1 h2 h3]
      exact sub_lt_self _ (evalHahn_pos_iff.2
        (mul_pos_of_neg_of_neg (sub_optSeries_hi_neg x hβ) (sub_optSeries_hi_neg y hδ)))
  · refine forall_moves_mul.2 fun p a ha b hb ↦ ?_
    cases p with
    | left =>
      rw [Player.left_mul] at hb
      rw [leftMoves_optionGameO] at ha
      rw [rightMoves_optionGameO] at hb
      obtain ⟨⟨β, hβ⟩, rfl⟩ := ha
      obtain ⟨⟨δ, hδ⟩, rfl⟩ := hb
      obtain ⟨h1, h2, h3⟩ := ih β hβ δ hδ _ _ (neg_two_abs_coeffIdx_ne_zero x hβ)
        (two_abs_coeffIdx_ne_zero y hδ)
      refine IGame.Numeric.not_le.2 ?_
      rw [← Surreal.mk_lt_mk, out_eq, mk_mulOption_out hmkGx hmkGy (evalHahn_optSeries_lo x hβ)
        (evalHahn_optSeries_hi y hδ) h1 h2 h3]
      have := evalHahn_neg_iff.2
        (mul_neg_of_pos_of_neg (sub_optSeries_lo_pos x hβ) (sub_optSeries_hi_neg y hδ))
      linarith
    | right =>
      rw [Player.right_mul, Player.neg_right] at hb
      rw [rightMoves_optionGameO] at ha
      rw [leftMoves_optionGameO] at hb
      obtain ⟨⟨β, hβ⟩, rfl⟩ := ha
      obtain ⟨⟨δ, hδ⟩, rfl⟩ := hb
      obtain ⟨h1, h2, h3⟩ := ih β hβ δ hδ _ _ (two_abs_coeffIdx_ne_zero x hβ)
        (neg_two_abs_coeffIdx_ne_zero y hδ)
      refine IGame.Numeric.not_le.2 ?_
      rw [← Surreal.mk_lt_mk, out_eq, mk_mulOption_out hmkGx hmkGy (evalHahn_optSeries_hi x hβ)
        (evalHahn_optSeries_lo y hδ) h1 h2 h3]
      have := evalHahn_neg_iff.2
        (mul_neg_of_neg_of_pos (sub_optSeries_hi_neg x hβ) (sub_optSeries_lo_pos y hδ))
      linarith

/-- **The product of the values is born no earlier than the value of the product.** For `x`, `y`
of limit length, `evalHahn (x * y)` has a termwise coarse representative `H`, each of whose
options sits at distance of class `≤ mk (ω^e)` for some exponent `e = e_{β₀} + f_{δ₀}` of
`x * y`. The option of the product game at the pair `(β₀ + 1, δ₀)` differs from
`evalHahn (x * y)` by the evaluation of a series supported below `e_{β₀+1} + f_{δ₀} < e`,
hence strictly finer, so it beats the option of `H`: `evalHahn x * evalHahn y` fits `H`. -/
private theorem birthday_evalHahn_mul_le {x y : SurrealHahnSeries.{u}}
    (hlim : IsSuccLimit x.length) (hlim' : IsSuccLimit y.length)
    (ih : ∀ β (hβ : β < x.length) δ (hδ : δ < y.length) (r s : ℝ), r ≠ 0 → s ≠ 0 →
      evalHahn (optSeries x hβ r * y) = evalHahn (optSeries x hβ r) * evalHahn y ∧
      evalHahn (x * optSeries y hδ s) = evalHahn x * evalHahn (optSeries y hδ s) ∧
      evalHahn (optSeries x hβ r * optSeries y hδ s) =
        evalHahn (optSeries x hβ r) * evalHahn (optSeries y hδ s)) :
    (evalHahn (x * y)).birthday ≤ (evalHahn x * evalHahn y).birthday := by
  haveI := numeric_optionGameO hlim x.isStrictDom_term
  haveI := numeric_optionGameO hlim' y.isStrictDom_term
  have hmkGx : Surreal.mk (optionGameO x.term x.length) = evalHahn x :=
    mk_optionGameO_eq_hahnSumO hlim x.isStrictDom_term
  have hmkGy : Surreal.mk (optionGameO y.term y.length) = evalHahn y :=
    mk_optionGameO_eq_hahnSumO hlim' y.isStrictDom_term
  have hmkG : Surreal.mk (optionGameO x.term x.length * optionGameO y.term y.length) =
      evalHahn x * evalHahn y := by
    rw [Surreal.mk_mul, hmkGx, hmkGy]
  obtain ⟨H, hHn, hHZ, hHl, hHr⟩ := termRep_evalHahn (x * y)
  haveI := hHn
  rw [← hHZ]
  refine birthday_mk_le_of_fits ?_
  constructor
  · intro a ha
    haveI := IGame.Numeric.of_mem_moves ha
    obtain ⟨_, ⟨ε, hε, rfl⟩, hc⟩ := hHl a ha
    refine IGame.Numeric.not_le.2 ?_
    rw [← Surreal.mk_lt_mk, out_eq]
    obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ :=
      exists_add_eq_of_mem_support_mul ((x * y).exp ⟨ε, hε⟩).2
    obtain ⟨⟨β₀, hβ₀⟩, rfl⟩ := eq_exp_of_mem_support ha₀
    obtain ⟨⟨δ, hδ⟩, rfl⟩ := eq_exp_of_mem_support hb₀
    have hβ : β₀ + 1 < x.length := hlim.add_one_lt_of_ordinal hβ₀
    have hlt : (x.exp ⟨β₀ + 1, hβ⟩).1 + (y.exp ⟨δ, hδ⟩).1 <
        ((x * y).exp ⟨ε, hε⟩).1 := by
      rw [← hab]
      exact add_lt_add_of_lt_of_le (Subtype.coe_lt_coe.2 (exp_lt_exp_iff.2
        (Subtype.mk_lt_mk.2 (lt_add_one β₀)))) le_rfl
    obtain ⟨h1, h2, h3⟩ := ih (β₀ + 1) hβ δ hδ _ _ (neg_two_abs_coeffIdx_ne_zero x hβ)
      (neg_two_abs_coeffIdx_ne_zero y hδ)
    have hopt := mulOption_mem_moves_mul (optLoO_out_mem_leftMoves_optionGameO x.term hβ)
      (optLoO_out_mem_leftMoves_optionGameO y.term hδ)
    rw [Player.left_mul] at hopt
    have hval := mk_mulOption_out hmkGx hmkGy (evalHahn_optSeries_lo x hβ)
      (evalHahn_optSeries_lo y hδ) h1 h2 h3
    have hoptlt := Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt hopt)
    rw [hmkG, hval] at hoptlt
    have hmkterm : ArchimedeanClass.mk ((x * y).term ε) =
        ArchimedeanClass.mk (ω^ ((x * y).exp ⟨ε, hε⟩).1) := by
      rw [term_of_lt hε, ArchimedeanClass.mk_mul, mk_realCast (coeffIdx_ne_zero hε), zero_add]
    have hsupp := le_add_of_mem_support_mul
      (fun s hs ↦ le_of_mem_support_sub_optSeries x hβ (-(2 * |x.coeffIdx (β₀ + 1)|)) hs)
      (fun s hs ↦ le_of_mem_support_sub_optSeries y hδ (-(2 * |y.coeffIdx δ|)) hs)
    have hmkD : ArchimedeanClass.mk (evalHahn (x * y) - Surreal.mk a) <
        ArchimedeanClass.mk (evalHahn ((x - optSeries x hβ (-(2 * |x.coeffIdx (β₀ + 1)|))) *
          (y - optSeries y hδ (-(2 * |y.coeffIdx δ|))))) :=
      (hc.trans_eq hmkterm).trans_lt ((archimedeanClassMk_wpow_strictAnti hlt).trans_le
        (mk_wpow_le_mk_evalHahn_of_support_le hsupp))
    have habs := abs_lt_abs_of_mk_lt hmkD
    have hpos : 0 < evalHahn (x * y) - Surreal.mk a := by
      rw [sub_pos, ← hHZ]
      exact Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt ha)
    rw [abs_of_pos hpos] at habs
    have := le_abs_self (evalHahn ((x - optSeries x hβ (-(2 * |x.coeffIdx (β₀ + 1)|))) *
      (y - optSeries y hδ (-(2 * |y.coeffIdx δ|)))))
    linarith
  · intro b hb
    haveI := IGame.Numeric.of_mem_moves hb
    obtain ⟨_, ⟨ε, hε, rfl⟩, hc⟩ := hHr b hb
    refine IGame.Numeric.not_le.2 ?_
    rw [← Surreal.mk_lt_mk, out_eq]
    obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ :=
      exists_add_eq_of_mem_support_mul ((x * y).exp ⟨ε, hε⟩).2
    obtain ⟨⟨β₀, hβ₀⟩, rfl⟩ := eq_exp_of_mem_support ha₀
    obtain ⟨⟨δ, hδ⟩, rfl⟩ := eq_exp_of_mem_support hb₀
    have hβ : β₀ + 1 < x.length := hlim.add_one_lt_of_ordinal hβ₀
    have hlt : (x.exp ⟨β₀ + 1, hβ⟩).1 + (y.exp ⟨δ, hδ⟩).1 <
        ((x * y).exp ⟨ε, hε⟩).1 := by
      rw [← hab]
      exact add_lt_add_of_lt_of_le (Subtype.coe_lt_coe.2 (exp_lt_exp_iff.2
        (Subtype.mk_lt_mk.2 (lt_add_one β₀)))) le_rfl
    obtain ⟨h1, h2, h3⟩ := ih (β₀ + 1) hβ δ hδ _ _ (neg_two_abs_coeffIdx_ne_zero x hβ)
      (two_abs_coeffIdx_ne_zero y hδ)
    have hopt := mulOption_mem_moves_mul (optLoO_out_mem_leftMoves_optionGameO x.term hβ)
      (optHiO_out_mem_rightMoves_optionGameO y.term hδ)
    rw [Player.left_mul] at hopt
    have hval := mk_mulOption_out hmkGx hmkGy (evalHahn_optSeries_lo x hβ)
      (evalHahn_optSeries_hi y hδ) h1 h2 h3
    have hoptlt := Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right hopt)
    rw [hmkG, hval] at hoptlt
    have hmkterm : ArchimedeanClass.mk ((x * y).term ε) =
        ArchimedeanClass.mk (ω^ ((x * y).exp ⟨ε, hε⟩).1) := by
      rw [term_of_lt hε, ArchimedeanClass.mk_mul, mk_realCast (coeffIdx_ne_zero hε), zero_add]
    have hsupp := le_add_of_mem_support_mul
      (fun s hs ↦ le_of_mem_support_sub_optSeries x hβ (-(2 * |x.coeffIdx (β₀ + 1)|)) hs)
      (fun s hs ↦ le_of_mem_support_sub_optSeries y hδ (2 * |y.coeffIdx δ|) hs)
    have hmkD : ArchimedeanClass.mk (Surreal.mk b - evalHahn (x * y)) <
        ArchimedeanClass.mk (evalHahn ((x - optSeries x hβ (-(2 * |x.coeffIdx (β₀ + 1)|))) *
          (y - optSeries y hδ (2 * |y.coeffIdx δ|)))) :=
      (hc.trans_eq hmkterm).trans_lt ((archimedeanClassMk_wpow_strictAnti hlt).trans_le
        (mk_wpow_le_mk_evalHahn_of_support_le hsupp))
    have habs := abs_lt_abs_of_mk_lt hmkD
    have hpos : 0 < Surreal.mk b - evalHahn (x * y) := by
      rw [sub_pos, ← hHZ]
      exact Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right hb)
    rw [abs_of_pos hpos] at habs
    have := neg_abs_le (evalHahn ((x - optSeries x hβ (-(2 * |x.coeffIdx (β₀ + 1)|))) *
      (y - optSeries y hδ (2 * |y.coeffIdx δ|))))
    linarith

/-! ### THE TRANSFINITE PRODUCT THEOREM -/

/-- The multiplicativity induction, on the pair `(x.length, y.length)` lexicographically. -/
private theorem evalHahn_mul_aux (α : Ordinal.{u}) :
    ∀ γ : Ordinal.{u}, ∀ x y : SurrealHahnSeries.{u},
      x.length = α → y.length = γ → evalHahn (x * y) = evalHahn x * evalHahn y := by
  induction α using WellFoundedLT.induction with
  | ind α ihα =>
    intro γ
    induction γ using WellFoundedLT.induction with
    | ind γ ihγ =>
      intro x y hx hy
      rcases Ordinal.zero_or_succ_or_isSuccLimit α with h0 | ⟨β, hβ⟩ | hlim
      · rw [h0, length_eq_zero] at hx
        subst hx
        rw [zero_mul, evalHahn_zero, zero_mul]
      · rw [← hβ, succ_eq_add_one] at hx
        have hβx : β < x.length := by rw [hx]; exact lt_add_one β
        refine evalHahn_mul_of_length_eq_add_one hx (ihα β ?_ γ _ y ?_ hy)
        · rw [← hβ]; exact lt_succ β
        · rw [length_truncIdx, min_eq_left hβx.le]
      rcases Ordinal.zero_or_succ_or_isSuccLimit γ with h0 | ⟨δ, hδ⟩ | hlim'
      · rw [h0, length_eq_zero] at hy
        subst hy
        rw [mul_zero, evalHahn_zero, mul_zero]
      · rw [← hδ, succ_eq_add_one] at hy
        have hδy : δ < y.length := by rw [hy]; exact lt_add_one δ
        refine evalHahn_mul_of_length_eq_add_one' hy (ihγ δ ?_ x _ hx ?_)
        · rw [← hδ]; exact lt_succ δ
        · rw [length_truncIdx, min_eq_left hδy.le]
      -- Both lengths are limits.
      subst hx
      subst hy
      have ih : ∀ β (hβ : β < x.length) δ (hδ : δ < y.length) (r s : ℝ),
          r ≠ 0 → s ≠ 0 →
          evalHahn (optSeries x hβ r * y) = evalHahn (optSeries x hβ r) * evalHahn y ∧
          evalHahn (x * optSeries y hδ s) = evalHahn x * evalHahn (optSeries y hδ s) ∧
          evalHahn (optSeries x hβ r * optSeries y hδ s) =
            evalHahn (optSeries x hβ r) * evalHahn (optSeries y hδ s) := by
        intro β hβ δ hδ r s hr hs
        exact ⟨ihα (β + 1) (hlim.add_one_lt_of_ordinal hβ) y.length _ y
            (length_optSeries x hβ r hr) rfl,
          ihγ (δ + 1) (hlim'.add_one_lt_of_ordinal hδ) x _ rfl (length_optSeries y hδ s hs),
          ihα (β + 1) (hlim.add_one_lt_of_ordinal hβ) (δ + 1) _ _ (length_optSeries x hβ r hr)
            (length_optSeries y hδ s hs)⟩
      haveI := numeric_optionGameO hlim x.isStrictDom_term
      haveI := numeric_optionGameO hlim' y.isStrictDom_term
      have hmkG : Surreal.mk (optionGameO x.term x.length * optionGameO y.term y.length) =
          evalHahn x * evalHahn y := by
        rw [Surreal.mk_mul, mk_optionGameO_eq_hahnSumO hlim x.isStrictDom_term,
          mk_optionGameO_eq_hahnSumO hlim' y.isStrictDom_term]
        rfl
      have hfit := out_fits_mul_optionGameO hlim hlim' ih
      have hbd := birthday_evalHahn_mul_le hlim hlim' ih
      rw [← hmkG] at hbd
      rw [eq_mk_of_fits_of_birthday_le hfit hbd, hmkG]

/-- **THE TRANSFINITE PRODUCT THEOREM — the normal-form correspondence is multiplicative**: for
all surreal Hahn series `x, y`, `evalHahn (x * y) = evalHahn x * evalHahn y`. -/
theorem evalHahn_mul (x y : SurrealHahnSeries.{u}) :
    evalHahn (x * y) = evalHahn x * evalHahn y :=
  evalHahn_mul_aux x.length y.length x y rfl rfl

/-! ### CONWAY'S THEOREM: `No ≅ ℝ((ω^No))` -/

/-- **The evaluation map as a ring homomorphism.** -/
def evalHahnRingHom : SurrealHahnSeries.{u} →+* Surreal.{u} where
  toFun := evalHahn
  map_one' := evalHahn_one
  map_mul' := evalHahn_mul
  map_zero' := evalHahn_zero
  map_add' := evalHahn_add'

@[simp]
theorem evalHahnRingHom_apply (x : SurrealHahnSeries.{u}) : evalHahnRingHom x = evalHahn x :=
  rfl

/-- **CONWAY'S THEOREM, ring form**: the normal-form correspondence is a ring isomorphism
`SurrealHahnSeries ≃+* Surreal` — the surreal numbers are the field of real Hahn series over
themselves. -/
def hahnRingEquiv : SurrealHahnSeries.{u} ≃+* Surreal.{u} where
  toEquiv := hahnEquiv
  map_mul' := evalHahn_mul
  map_add' := evalHahn_add'

@[simp]
theorem hahnRingEquiv_apply (x : SurrealHahnSeries.{u}) : hahnRingEquiv x = evalHahn x :=
  rfl

@[simp]
theorem hahnRingEquiv_symm_apply (x : Surreal.{u}) : hahnRingEquiv.symm x = toHahnSeries x :=
  rfl

/-- **CONWAY'S THEOREM, ordered form**: the normal-form correspondence is an isomorphism of
ordered rings `SurrealHahnSeries ≃+*o Surreal` — `No ≅ ℝ((ω^No))` as ordered fields. -/
def hahnOrderRingIso : SurrealHahnSeries.{u} ≃+*o Surreal.{u} where
  toRingEquiv := hahnRingEquiv
  map_le_map_iff' := fun {_ _} ↦ evalHahn_le_iff

@[simp]
theorem hahnOrderRingIso_apply (x : SurrealHahnSeries.{u}) : hahnOrderRingIso x = evalHahn x :=
  rfl

/-- Inverses evaluate to inverses. -/
theorem evalHahn_inv (x : SurrealHahnSeries.{u}) : evalHahn x⁻¹ = (evalHahn x)⁻¹ :=
  map_inv₀ evalHahnRingHom x

theorem evalHahn_div (x y : SurrealHahnSeries.{u}) :
    evalHahn (x / y) = evalHahn x / evalHahn y :=
  map_div₀ evalHahnRingHom x y

theorem evalHahn_pow (x : SurrealHahnSeries.{u}) (n : ℕ) : evalHahn (x ^ n) = evalHahn x ^ n :=
  map_pow evalHahnRingHom x n

/-- Normal-form extraction is multiplicative. -/
theorem toHahnSeries_mul (x y : Surreal.{u}) :
    toHahnSeries (x * y) = toHahnSeries x * toHahnSeries y :=
  map_mul hahnRingEquiv.symm x y

theorem toHahnSeries_one : toHahnSeries (1 : Surreal.{u}) = 1 :=
  map_one hahnRingEquiv.symm

theorem toHahnSeries_inv (x : Surreal.{u}) : toHahnSeries x⁻¹ = (toHahnSeries x)⁻¹ :=
  map_inv₀ hahnRingEquiv.symm x

theorem toHahnSeries_pow (x : Surreal.{u}) (n : ℕ) : toHahnSeries (x ^ n) = toHahnSeries x ^ n :=
  map_pow hahnRingEquiv.symm x n

/-- Normal-form extraction is order-preserving. -/
theorem toHahnSeries_lt_iff {x y : Surreal.{u}} : toHahnSeries x < toHahnSeries y ↔ x < y := by
  rw [← evalHahn_lt_iff, evalHahn_toHahnSeries, evalHahn_toHahnSeries]

theorem toHahnSeries_le_iff {x y : Surreal.{u}} :
    toHahnSeries x ≤ toHahnSeries y ↔ x ≤ y := by
  rw [← evalHahn_le_iff, evalHahn_toHahnSeries, evalHahn_toHahnSeries]

theorem toHahnSeries_strictMono :
    StrictMono (toHahnSeries : Surreal.{u} → SurrealHahnSeries.{u}) :=
  fun _ _ h ↦ toHahnSeries_lt_iff.2 h

end Surreal

end
