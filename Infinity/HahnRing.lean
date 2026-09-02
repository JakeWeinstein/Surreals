import Infinity.NormalFormTheorem
import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# The normal-form correspondence is additive, and its first products

`Infinity.NormalFormTheorem` established Conway's Normal Form Theorem: the evaluation map
`evalHahn : SurrealHahnSeries → Surreal` (the canonical transfinite sum of the term sequence) is a
bijection, `hahnEquiv`. `Infinity.HahnMerge` proved it additive on pairs of series with **no
coefficient cancellation**. This file removes that hypothesis, and proves the first two
multiplicative laws — products by a single term, and products with a finite-support factor — on
the way to `hahnEquiv` being Conway's isomorphism `No ≅ ℝ((ω^No))`.

* **Negation** `Surreal.evalHahn_neg : evalHahn (−x) = −evalHahn x` (`(−x).term = −x.term` on
  the same support; `hahnSumO_neg`).
* **ADDITIVITY WITH CANCELLATION** `Surreal.evalHahn_add'`:
  `evalHahn (x + y) = evalHahn x + evalHahn y` for **all** surreal Hahn series `x, y` — no
  hypothesis. Proof: transfinite induction over the stages `γ ≤ w.length` of a *non-cancelling*
  auxiliary series `w = unionSeries x y` (coefficients `|x_e| + |y_e|`, support exactly
  `supp x ∪ supp y`), proving `evalHahn (z ⇂ γ) = evalHahn (x ⇂ γ) + evalHahn (y ⇂ γ)` for
  `z = x + y`, where `⇂ γ` truncates along the `γ`-th exponent of `w`. Successor stages are the
  append law (a cancelled term adds `c ω^e − c ω^e = 0`; the append law tolerates a zero
  coefficient). At a limit stage `γ` there is a new case split:
  - *cofinal case*: if the exponents of `z ⇂ γ` come arbitrarily close to the stage-`γ` cut
    (for every `β < γ` some `z`-exponent lies below `w.exp β`), then `z ⇂ γ` has limit length
    and the identification engine `hahnSumO_eq_of_isHahnSumO_of_moves_le` applies to the Conway
    sum `G_X + G_Y` of termwise-coarse representatives (`TermRep`) of the two truncated values:
    the residuals are controlled by the induction hypothesis and the split law, and every option
    of `G_X + G_Y` is coarse against some `w.term β`, which cofinality beats with a strictly finer
    `z`-term;
  - *bounded-away case*: otherwise `z ⇂ γ = z ⇂ (β + 1)` for some `β < γ`, and the blocks of
    `x` and `y` between the two stages cancel *as Hahn series*, so their values are negatives
    of each other (`evalHahn_neg`) and the induction hypothesis at `β + 1` finishes
    (`evalHahn_add_eq_of_trunc_eq`).
  Corollaries: `evalHahn_sub`, `evalHahnAddHom : SurrealHahnSeries →+ Surreal`,
  **`hahnAddEquiv : SurrealHahnSeries ≃+ Surreal`**, `evalHahn_sum`.
* **The coefficient formula for products** `SurrealHahnSeries.coeff_mul`, transported from
  mathlib's `HahnSeries.coeff_mul` through the `Lex`/subfield layer of `SurrealHahnSeries`;
  `coeff_single_mul : (single z c * y).coeff e = c * y.coeff (e − z)`, `coeff_mul_single`,
  `single_mul_single`, `support_single_mul` (the translate `(· + z) '' y.support`).
* **SINGLE-TERM PRODUCTS** `Surreal.evalHahn_single_mul`:
  `evalHahn (single z c * y) = c · ω^ z · evalHahn y`. The support of `single z c * y` is the
  translate of `y`'s by `z`, order-isomorphic to it (`singleMulRelIso`), so the lengths agree
  (`length_single_mul`), the exponents shift by `z` (`exp_single_mul`, via `typein_apply` on the
  isomorphism), the terms scale by `c ω^ z` (`term_single_mul`, `wpow_add`), and the scaling
  theorem `hahnSumO_monomial_mul` finishes.
* **FINITE-SUPPORT PRODUCTS** `Surreal.evalHahn_mul_of_finite_support`: if `x.support` is
  finite, `evalHahn (x * y) = evalHahn x * evalHahn y` (and symmetrically). `x` is the finite
  sum of its single terms (`eq_sum_single`), and additivity plus single-term products finish.
-/

open ArchimedeanClass IGame Order

universe u

noncomputable section

/-! ### Negation -/

namespace SurrealHahnSeries

open Ordinal

theorem support_neg (x : SurrealHahnSeries.{u}) : (-x).support = x.support := by
  ext i
  rw [mem_support_iff, mem_support_iff, coeff_neg, Pi.neg_apply, neg_ne_zero]

theorem length_neg (x : SurrealHahnSeries.{u}) : (-x).length = x.length :=
  length_eq_of_support_eq (support_neg x)

/-- The terms of `−x` are the negated terms of `x`. -/
theorem term_neg (x : SurrealHahnSeries.{u}) (j : Ordinal.{u}) : (-x).term j = -x.term j := by
  rcases lt_or_ge j x.length with hj | hj
  · have hj' : j < (-x).length := (length_neg x).symm ▸ hj
    rw [term_of_lt hj', term_of_lt hj, coeffIdx_of_lt hj', coeffIdx_of_lt hj,
      exp_eq_of_support_eq (support_neg x) hj' hj, coeff_neg, Pi.neg_apply, Real.toSurreal_neg,
      neg_mul]
  · rw [term_of_le hj, term_of_le (by rwa [length_neg]), neg_zero]

end SurrealHahnSeries

namespace Surreal

open SurrealHahnSeries

/-- **Negation**: `evalHahn (−x) = −evalHahn x`. -/
theorem evalHahn_neg (x : SurrealHahnSeries.{u}) : evalHahn (-x) = -evalHahn x := by
  unfold evalHahn
  rw [length_neg, hahnSumO_congr fun j _ ↦ term_neg x j]
  exact hahnSumO_neg x.isStrictDom_term

/-- **The bounded-away step**: if no exponent of `x + y` lies at or below `e` (the sum is
unchanged by truncation at `e`), then the tails of `x` and `y` below `e` cancel as Hahn series,
their values are negatives of each other, and the truncated values add to the full values. -/
theorem evalHahn_add_eq_of_trunc_eq (x y : SurrealHahnSeries.{u}) (e : Surreal.{u})
    (h : (x + y).trunc e = x + y) :
    evalHahn (x.trunc e) + evalHahn (y.trunc e) = evalHahn x + evalHahn y := by
  rw [evalHahn_eq_trunc_add_sub_trunc x e, evalHahn_eq_trunc_add_sub_trunc y e]
  have hsum : (x - x.trunc e) + (y - y.trunc e) = 0 := by
    rw [← add_sub_add_comm, ← trunc_add, h, sub_self]
  rw [eq_neg_of_add_eq_zero_right hsum, evalHahn_neg]
  ring

end Surreal

/-! ### The union-support series -/

namespace SurrealHahnSeries

/-- The support of the coefficient function `e ↦ |x_e| + |y_e|` is the union of the
supports. -/
theorem support_abs_add_abs (x y : SurrealHahnSeries.{u}) :
    Function.support (fun e ↦ |x.coeff e| + |y.coeff e|) = x.support ∪ y.support := by
  ext e
  rw [Function.mem_support, Set.mem_union, mem_support_iff, mem_support_iff]
  constructor
  · intro h
    by_contra hne
    rw [not_or, not_not, not_not] at hne
    rw [hne.1, hne.2] at h
    simp at h
  · rintro (h | h)
    · exact fun h0 ↦ h (abs_eq_zero.1
        ((add_eq_zero_iff_of_nonneg (abs_nonneg _) (abs_nonneg _)).1 h0).1)
    · exact fun h0 ↦ h (abs_eq_zero.1
        ((add_eq_zero_iff_of_nonneg (abs_nonneg _) (abs_nonneg _)).1 h0).2)

/-- **The union-support series**: the non-cancelling series with coefficients `|x_e| + |y_e|`,
whose support is exactly `supp x ∪ supp y`. It enumerates the union of the two supports, which is
what the additivity induction runs over. -/
def unionSeries (x y : SurrealHahnSeries.{u}) : SurrealHahnSeries.{u} :=
  mk (fun e ↦ |x.coeff e| + |y.coeff e|)
    (by rw [support_abs_add_abs]; infer_instance)
    (by rw [support_abs_add_abs]; exact x.wellFoundedOn_support.union y.wellFoundedOn_support)

@[simp]
theorem support_unionSeries (x y : SurrealHahnSeries.{u}) :
    (unionSeries x y).support = x.support ∪ y.support := by
  rw [unionSeries, support_mk, support_abs_add_abs]

theorem support_subset_unionSeries_left (x y : SurrealHahnSeries.{u}) :
    x.support ⊆ (unionSeries x y).support := by
  rw [support_unionSeries]; exact Set.subset_union_left

theorem support_subset_unionSeries_right (x y : SurrealHahnSeries.{u}) :
    y.support ⊆ (unionSeries x y).support := by
  rw [support_unionSeries]; exact Set.subset_union_right

/-- Truncation along a series is additive. -/
theorem truncAlong_add (x y w : SurrealHahnSeries.{u}) (γ : Ordinal.{u}) :
    (x + y).truncAlong w γ = x.truncAlong w γ + y.truncAlong w γ := by
  unfold truncAlong
  split_ifs with h
  · exact trunc_add x y _
  · rfl

end SurrealHahnSeries

/-! ### ADDITIVITY WITH CANCELLATION -/

namespace Surreal

open SurrealHahnSeries

/-- The additivity induction along the union-support series: for `z = x + y` and any series `w`
containing both supports, at every stage `γ ≤ w.length`,
`evalHahn (z ⇂ γ) = evalHahn (x ⇂ γ) + evalHahn (y ⇂ γ)`. -/
private theorem evalHahn_truncAlong_add_aux (x y z w : SurrealHahnSeries.{u})
    (hxw : x.support ⊆ w.support) (hyw : y.support ⊆ w.support) (hz : z = x + y)
    (γ : Ordinal.{u}) :
    γ ≤ w.length →
      evalHahn (z.truncAlong w γ) = evalHahn (x.truncAlong w γ) + evalHahn (y.truncAlong w γ) := by
  have hzw : z.support ⊆ w.support := fun e he ↦ by
    rw [hz] at he
    rcases support_add_subset he with h | h
    · exact hxw h
    · exact hyw h
  have hzc : ∀ e, z.coeff e = x.coeff e + y.coeff e := fun e ↦ by rw [hz, coeff_add_apply]
  induction γ using Ordinal.limitRecOn with
  | zero =>
    intro _
    rw [truncAlong_zero hzw, truncAlong_zero hxw, truncAlong_zero hyw, evalHahn_zero, add_zero]
  | add_one δ ih =>
    intro h
    have hδ : δ < w.length := add_one_le_iff.1 h
    rw [evalHahn_truncAlong_add_one hzw hδ, evalHahn_truncAlong_add_one hxw hδ,
      evalHahn_truncAlong_add_one hyw hδ, ih hδ.le, hzc, Real.toSurreal_add]
    ring
  | limit γ hγ ih =>
    intro hγN
    have hV : ∀ β < γ, evalHahn (z.truncAlong w β) =
        evalHahn (x.truncAlong w β) + evalHahn (y.truncAlong w β) :=
      fun β hβ ↦ ih β hβ (hβ.le.trans hγN)
    have hzγ : z.truncAlong w γ = x.truncAlong w γ + y.truncAlong w γ := by
      rw [hz, truncAlong_add]
    by_cases hcof : ∀ β, ∀ hβ : β < γ, ∃ s ∈ (z.truncAlong w γ).support,
        s < (w.exp ⟨β, hβ.trans_le hγN⟩).1
    · -- THE COFINAL CASE: the exponents of `z ⇂ γ` accumulate at the stage-`γ` cut.
      have hzsw : (z.truncAlong w γ).support ⊆ w.support :=
        (support_truncAlong_subset _ _ _).trans hzw
      -- `z ⇂ γ` has limit length.
      have hlim : IsSuccLimit (z.truncAlong w γ).length := by
        rcases Ordinal.zero_or_succ_or_isSuccLimit (z.truncAlong w γ).length with h0 | ⟨μ, hμ⟩ | hl
        · exfalso
          obtain ⟨s, hs, _⟩ := hcof 0 hγ.pos
          rw [length_eq_zero] at h0
          rw [h0, support_zero] at hs
          exact hs
        · exfalso
          have hμ' : μ < (z.truncAlong w γ).length := by
            rw [← hμ]; exact Order.lt_succ μ
          obtain ⟨β, hβN, hβγ, hexp⟩ := exists_exp_truncAlong_eq hzw hγN hμ'
          obtain ⟨s, hs, hslt⟩ := hcof β hβγ
          obtain ⟨k, hk⟩ := eq_exp_of_mem_support hs
          have hkμ : k.1 ≤ μ :=
            Order.lt_succ_iff.1 (lt_of_lt_of_eq (Set.mem_Iio.1 k.2) hμ.symm)
          have hle : ((z.truncAlong w γ).exp ⟨μ, hμ'⟩).1 ≤ ((z.truncAlong w γ).exp k).1 :=
            Subtype.coe_le_coe.2 (exp_le_exp_iff.2 (Subtype.coe_le_coe.1 hkμ))
          rw [hk, hexp] at hle
          exact absurd hslt (not_lt.2 hle)
        · exact hl
      have hzt : IsStrictDom (z.truncAlong w γ).term (z.truncAlong w γ).length :=
        (z.truncAlong w γ).isStrictDom_term
      -- The value `X_γ + Y_γ` is a Hahn sum of the term sequence of `z ⇂ γ`.
      have hP : IsHahnSumO (z.truncAlong w γ).term (z.truncAlong w γ).length
          (evalHahn (x.truncAlong w γ) + evalHahn (y.truncAlong w γ)) := by
        intro j hj
        obtain ⟨β, hβN, hβγ, hexp⟩ := exists_exp_truncAlong_eq hzw hγN hj
        have h2 := evalHahn_truncIdx (z.truncAlong w γ) j
        rw [min_eq_left hj.le, truncIdx_of_lt hj, hexp, truncAlong_trunc_exp hβγ hγN,
          hV β hβγ] at h2
        rw [← h2, ← truncAlong_trunc_exp hβγ hγN (x := x), ← truncAlong_trunc_exp hβγ hγN (x := y),
          add_sub_add_comm]
        have hmk : ArchimedeanClass.mk ((z.truncAlong w γ).term j) =
            ArchimedeanClass.mk (ω^ (w.exp ⟨β, hβN⟩).1) := by
          rw [term_of_lt hj, ArchimedeanClass.mk_mul, mk_realCast (coeffIdx_ne_zero hj), zero_add,
            hexp]
        rw [hmk]
        exact le_trans (le_min (mk_wpow_le_mk_evalHahn_sub_trunc _ _)
          (mk_wpow_le_mk_evalHahn_sub_trunc _ _)) (ArchimedeanClass.min_le_mk_add ..)
      -- The class of a `z`-term at an exponent below `w.exp β` is strictly finer than the class
      -- of `w.term β`.
      have hfine : ∀ β (hβ : β < γ) (j : Ordinal.{u}) (hj : j < (z.truncAlong w γ).length),
          ((z.truncAlong w γ).exp ⟨j, hj⟩).1 < (w.exp ⟨β, hβ.trans_le hγN⟩).1 →
          ArchimedeanClass.mk (w.term β) < ArchimedeanClass.mk ((z.truncAlong w γ).term j) := by
        intro β hβ j hj hlt
        rw [term_of_lt hj, ArchimedeanClass.mk_mul, mk_realCast (coeffIdx_ne_zero hj), zero_add,
          term_of_lt (hβ.trans_le hγN), ArchimedeanClass.mk_mul,
          mk_realCast (coeffIdx_ne_zero (hβ.trans_le hγN)), zero_add]
        exact archimedeanClassMk_wpow_strictAnti hlt
      -- The game: the Conway sum of termwise-coarse representatives of the truncated values.
      obtain ⟨GX, hGXn, hGX, hGXl, hGXr⟩ := termRep_evalHahn_truncAlong hxw hγN
      obtain ⟨GY, hGYn, hGY, hGYl, hGYr⟩ := termRep_evalHahn_truncAlong hyw hγN
      haveI := hGXn
      haveI := hGYn
      have hG : Surreal.mk (GX + GY) =
          evalHahn (x.truncAlong w γ) + evalHahn (y.truncAlong w γ) := by
        rw [Surreal.mk_add, hGX, hGY]
      show hahnSumO (z.truncAlong w γ).term (z.truncAlong w γ).length = _
      rw [← hG]
      refine hahnSumO_eq_of_isHahnSumO_of_moves_le hlim hzt (by rwa [hG]) ?_ ?_
      · rw [forall_moves_add]
        constructor
        · intro a ha
          haveI := IGame.Numeric.of_mem_moves ha
          obtain ⟨c, ⟨β, hβ, rfl⟩, hc⟩ := hGXl a ha
          obtain ⟨s, hs, hslt⟩ := hcof β hβ
          obtain ⟨⟨j, hj⟩, hjs⟩ := eq_exp_of_mem_support hs
          have hj1 : j + 1 < (z.truncAlong w γ).length := hlim.add_one_lt_of_ordinal hj
          refine ⟨j, hj, ?_⟩
          rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, hGY]
          have hpos : 0 < evalHahn (x.truncAlong w γ) - Surreal.mk a := by
            rw [sub_pos, ← hGX]
            exact Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt ha)
          have hmk : ArchimedeanClass.mk (evalHahn (x.truncAlong w γ) - Surreal.mk a) <
              ArchimedeanClass.mk ((z.truncAlong w γ).term j) :=
            hc.trans_lt (hfine β hβ j hj (by rw [hjs]; exact hslt))
          have key := sub_le_optLoO_of_mk_lt hzt hP hpos hj1 hmk
          rw [show Surreal.mk a + evalHahn (y.truncAlong w γ) =
            evalHahn (x.truncAlong w γ) + evalHahn (y.truncAlong w γ) -
              (evalHahn (x.truncAlong w γ) - Surreal.mk a) by ring]
          exact key
        · intro b hb
          haveI := IGame.Numeric.of_mem_moves hb
          obtain ⟨c, ⟨β, hβ, rfl⟩, hc⟩ := hGYl b hb
          obtain ⟨s, hs, hslt⟩ := hcof β hβ
          obtain ⟨⟨j, hj⟩, hjs⟩ := eq_exp_of_mem_support hs
          have hj1 : j + 1 < (z.truncAlong w γ).length := hlim.add_one_lt_of_ordinal hj
          refine ⟨j, hj, ?_⟩
          rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, hGX]
          have hpos : 0 < evalHahn (y.truncAlong w γ) - Surreal.mk b := by
            rw [sub_pos, ← hGY]
            exact Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt hb)
          have hmk : ArchimedeanClass.mk (evalHahn (y.truncAlong w γ) - Surreal.mk b) <
              ArchimedeanClass.mk ((z.truncAlong w γ).term j) :=
            hc.trans_lt (hfine β hβ j hj (by rw [hjs]; exact hslt))
          have key := sub_le_optLoO_of_mk_lt hzt hP hpos hj1 hmk
          rw [show evalHahn (x.truncAlong w γ) + Surreal.mk b =
            evalHahn (x.truncAlong w γ) + evalHahn (y.truncAlong w γ) -
              (evalHahn (y.truncAlong w γ) - Surreal.mk b) by ring]
          exact key
      · rw [forall_moves_add]
        constructor
        · intro a ha
          haveI := IGame.Numeric.of_mem_moves ha
          obtain ⟨c, ⟨β, hβ, rfl⟩, hc⟩ := hGXr a ha
          obtain ⟨s, hs, hslt⟩ := hcof β hβ
          obtain ⟨⟨j, hj⟩, hjs⟩ := eq_exp_of_mem_support hs
          have hj1 : j + 1 < (z.truncAlong w γ).length := hlim.add_one_lt_of_ordinal hj
          refine ⟨j, hj, ?_⟩
          rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, hGY]
          have hpos : 0 < Surreal.mk a - evalHahn (x.truncAlong w γ) := by
            rw [sub_pos, ← hGX]
            exact Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right ha)
          have hmk : ArchimedeanClass.mk (Surreal.mk a - evalHahn (x.truncAlong w γ)) <
              ArchimedeanClass.mk ((z.truncAlong w γ).term j) :=
            hc.trans_lt (hfine β hβ j hj (by rw [hjs]; exact hslt))
          have key := optHiO_le_add_of_mk_lt hzt hP hpos hj1 hmk
          rw [show Surreal.mk a + evalHahn (y.truncAlong w γ) =
            evalHahn (x.truncAlong w γ) + evalHahn (y.truncAlong w γ) +
              (Surreal.mk a - evalHahn (x.truncAlong w γ)) by ring]
          exact key
        · intro b hb
          haveI := IGame.Numeric.of_mem_moves hb
          obtain ⟨c, ⟨β, hβ, rfl⟩, hc⟩ := hGYr b hb
          obtain ⟨s, hs, hslt⟩ := hcof β hβ
          obtain ⟨⟨j, hj⟩, hjs⟩ := eq_exp_of_mem_support hs
          have hj1 : j + 1 < (z.truncAlong w γ).length := hlim.add_one_lt_of_ordinal hj
          refine ⟨j, hj, ?_⟩
          rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, hGX]
          have hpos : 0 < Surreal.mk b - evalHahn (y.truncAlong w γ) := by
            rw [sub_pos, ← hGY]
            exact Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right hb)
          have hmk : ArchimedeanClass.mk (Surreal.mk b - evalHahn (y.truncAlong w γ)) <
              ArchimedeanClass.mk ((z.truncAlong w γ).term j) :=
            hc.trans_lt (hfine β hβ j hj (by rw [hjs]; exact hslt))
          have key := optHiO_le_add_of_mk_lt hzt hP hpos hj1 hmk
          rw [show evalHahn (x.truncAlong w γ) + Surreal.mk b =
            evalHahn (x.truncAlong w γ) + evalHahn (y.truncAlong w γ) +
              (Surreal.mk b - evalHahn (y.truncAlong w γ)) by ring]
          exact key
    · -- THE BOUNDED-AWAY CASE: some `w.exp β` lies below every exponent of `z ⇂ γ`, so
      -- `z ⇂ γ = z ⇂ (β + 1)` and the blocks of `x` and `y` between the stages cancel.
      have hcof' : ∃ β, ∃ hβ : β < γ, ∀ s ∈ (z.truncAlong w γ).support,
          (w.exp ⟨β, hβ.trans_le hγN⟩).1 ≤ s := by
        by_contra hcon
        apply hcof
        intro β hβ
        by_contra hcon2
        apply hcon
        refine ⟨β, hβ, fun s hs ↦ ?_⟩
        by_contra hlt
        exact hcon2 ⟨s, hs, not_le.1 hlt⟩
      obtain ⟨β, hβ, hall⟩ := hcof'
      have hβ1 : β + 1 < γ := hγ.add_one_lt_of_ordinal hβ
      have hself : (z.truncAlong w γ).trunc (w.exp ⟨β + 1, hβ1.trans_le hγN⟩) =
          z.truncAlong w γ := by
        refine trunc_eq_self fun s hs ↦ lt_of_lt_of_le ?_ (hall s hs)
        exact Subtype.coe_lt_coe.2 (exp_lt_exp_iff.2 (Subtype.mk_lt_mk.2 (lt_add_one_iff.2 le_rfl)))
      have hzβ : z.truncAlong w γ = z.truncAlong w (β + 1) := by
        rw [← truncAlong_trunc_exp hβ1 hγN (x := z), hself]
      rw [hzβ, hV (β + 1) hβ1, ← truncAlong_trunc_exp hβ1 hγN (x := x),
        ← truncAlong_trunc_exp hβ1 hγN (x := y)]
      refine evalHahn_add_eq_of_trunc_eq _ _ _ ?_
      rw [← hzγ]
      exact hself

/-- **ADDITIVITY WITH CANCELLATION — the normal-form correspondence is additive**: for all
surreal Hahn series `x, y`, `evalHahn (x + y) = evalHahn x + evalHahn y`. No hypothesis on the
supports or the coefficients: cancelled terms are handled by the induction along the union of
the supports (`unionSeries`), with the cofinal / bounded-away split at limit stages. -/
theorem evalHahn_add' (x y : SurrealHahnSeries.{u}) :
    evalHahn (x + y) = evalHahn x + evalHahn y := by
  have h := evalHahn_truncAlong_add_aux x y (x + y) (unionSeries x y)
    (support_subset_unionSeries_left x y) (support_subset_unionSeries_right x y) rfl
    (unionSeries x y).length le_rfl
  rwa [truncAlong_of_le le_rfl, truncAlong_of_le le_rfl, truncAlong_of_le le_rfl] at h

/-- **Subtraction.** -/
theorem evalHahn_sub (x y : SurrealHahnSeries.{u}) :
    evalHahn (x - y) = evalHahn x - evalHahn y := by
  rw [sub_eq_add_neg, evalHahn_add', evalHahn_neg, sub_eq_add_neg]

/-- **The evaluation map as an additive homomorphism.** -/
def evalHahnAddHom : SurrealHahnSeries.{u} →+ Surreal.{u} where
  toFun := evalHahn
  map_zero' := evalHahn_zero
  map_add' := evalHahn_add'

@[simp]
theorem evalHahnAddHom_apply (x : SurrealHahnSeries.{u}) : evalHahnAddHom x = evalHahn x :=
  rfl

/-- **THE NORMAL-FORM CORRESPONDENCE IS AN ADDITIVE ISOMORPHISM**:
`SurrealHahnSeries ≃+ Surreal`, by evaluation and normal-form extraction. -/
def hahnAddEquiv : SurrealHahnSeries.{u} ≃+ Surreal.{u} where
  toEquiv := hahnEquiv
  map_add' := evalHahn_add'

@[simp]
theorem hahnAddEquiv_apply (x : SurrealHahnSeries.{u}) : hahnAddEquiv x = evalHahn x :=
  rfl

@[simp]
theorem hahnAddEquiv_symm_apply (x : Surreal.{u}) : hahnAddEquiv.symm x = toHahnSeries x :=
  rfl

/-- Finite sums evaluate termwise. -/
theorem evalHahn_sum {ι : Type*} (s : Finset ι) (f : ι → SurrealHahnSeries.{u}) :
    evalHahn (∑ i ∈ s, f i) = ∑ i ∈ s, evalHahn (f i) :=
  map_sum evalHahnAddHom f s

/-- Normal-form extraction is additive. -/
theorem toHahnSeries_add (x y : Surreal.{u}) :
    toHahnSeries (x + y) = toHahnSeries x + toHahnSeries y :=
  map_add hahnAddEquiv.symm x y

theorem toHahnSeries_neg (x : Surreal.{u}) : toHahnSeries (-x) = -toHahnSeries x :=
  map_neg hahnAddEquiv.symm x

end Surreal

/-! ### The coefficient formula for products

`SurrealHahnSeries` is a subfield of `Lex (HahnSeries Surrealᵒᵈ ℝ)`; multiplication is the
underlying Hahn-series multiplication, so mathlib's coefficient formula transports verbatim. -/

namespace SurrealHahnSeries

open OrderDual

/-- **The coefficient formula for products**: the coefficient of `x * y` at `e` is the finite sum
over the pairs `(a, b)` of exponents of `x` and `y` with `a + b = e` (mathlib's
`HahnSeries.coeff_mul`, over `Surrealᵒᵈ`). -/
theorem coeff_mul (x y : SurrealHahnSeries.{u}) (e : Surreal.{u}) :
    (x * y).coeff e =
      ∑ ij ∈ Finset.antidiagonal x.1.isPWO_support y.1.isPWO_support (toDual e),
        x.coeff (ofDual ij.1) * y.coeff (ofDual ij.2) :=
  HahnSeries.coeff_mul

/-- Membership in the index set of `coeff_mul`. -/
theorem mem_antidiagonal_iff (x y : SurrealHahnSeries.{u}) (e : Surreal.{u})
    (ij : Surrealᵒᵈ × Surrealᵒᵈ) :
    ij ∈ Finset.antidiagonal x.1.isPWO_support y.1.isPWO_support (toDual e) ↔
      ofDual ij.1 ∈ x.support ∧ ofDual ij.2 ∈ y.support ∧ ofDual ij.1 + ofDual ij.2 = e :=
  Finset.mem_antidiagonal

/-- The underlying mathlib Hahn series of a single term. -/
theorem ofLex_val_single (z : Surreal.{u}) (c : ℝ) :
    ofLex (single z c).1 = HahnSeries.single (toDual z) c := by
  ext j
  show (single z c).coeff (ofDual j) = _
  rw [coeff_single, HahnSeries.coeff_single, Pi.single_apply]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

/-- **Coefficients of a single-term product**: `(single z c * y).coeff e = c * y.coeff (e − z)`. -/
theorem coeff_single_mul (z : Surreal.{u}) (c : ℝ) (y : SurrealHahnSeries.{u})
    (e : Surreal.{u}) : (single z c * y).coeff e = c * y.coeff (e - z) := by
  show ((single z c).1 * y.1).coeff (toDual e) = c * y.1.coeff (toDual (e - z))
  change (ofLex (single z c).1 * ofLex y.1).coeff (toDual e) = _
  rw [ofLex_val_single, HahnSeries.coeff_single_mul]
  rfl

theorem coeff_mul_single (y : SurrealHahnSeries.{u}) (z : Surreal.{u}) (c : ℝ)
    (e : Surreal.{u}) : (y * single z c).coeff e = y.coeff (e - z) * c := by
  rw [mul_comm, coeff_single_mul, mul_comm]

/-- **Products of single terms.** -/
theorem single_mul_single (a b : Surreal.{u}) (r s : ℝ) :
    single a r * single b s = single (a + b) (r * s) := by
  ext e
  rw [coeff_single_mul, coeff_single, coeff_single, Pi.single_apply, Pi.single_apply]
  by_cases h : e = a + b
  · rw [if_pos h, if_pos (sub_eq_iff_eq_add'.2 h)]
  · rw [if_neg h, if_neg fun h' ↦ h (sub_eq_iff_eq_add'.1 h'), mul_zero]

/-- The multiplicative identity is the single term `ω^ 0`. -/
theorem one_eq_single : (1 : SurrealHahnSeries.{u}) = single 0 1 := by
  ext e
  show (1 : HahnSeries Surrealᵒᵈ ℝ).coeff (toDual e) = _
  rw [HahnSeries.coeff_one, coeff_single, Pi.single_apply]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

theorem mem_support_single_mul_iff {z : Surreal.{u}} {c : ℝ} (hc : c ≠ 0)
    {y : SurrealHahnSeries.{u}} {e : Surreal.{u}} :
    e ∈ (single z c * y).support ↔ e - z ∈ y.support := by
  rw [mem_support_iff, mem_support_iff, coeff_single_mul, mul_ne_zero_iff_left hc]

/-- **The support of a single-term product is the translate of the support.** -/
theorem support_single_mul {z : Surreal.{u}} {c : ℝ} (hc : c ≠ 0) (y : SurrealHahnSeries.{u}) :
    (single z c * y).support = (· + z) '' y.support := by
  ext e
  rw [mem_support_single_mul_iff hc, Set.mem_image]
  constructor
  · intro h
    exact ⟨e - z, h, sub_add_cancel e z⟩
  · rintro ⟨s, hs, rfl⟩
    rwa [add_sub_cancel_right]

/-- Every exponent of a product is a sum of an exponent of each factor. -/
theorem exists_add_eq_of_mem_support_mul {x y : SurrealHahnSeries.{u}} {e : Surreal.{u}}
    (he : e ∈ (x * y).support) : ∃ a ∈ x.support, ∃ b ∈ y.support, a + b = e := by
  have h : toDual e ∈ (ofLex x.1 * ofLex y.1).support := he
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.1 (HahnSeries.support_mul_subset h)
  exact ⟨ofDual a, ha, ofDual b, hb, hab⟩

/-! ### Single-term products: the support translates, the terms scale -/

/-- **Translation by `z` is an order isomorphism** (for `>`) from the support of `y` onto the
support of `single z c * y`. -/
def singleMulRelIso {c : ℝ} (hc : c ≠ 0) (z : Surreal.{u}) (y : SurrealHahnSeries.{u}) :
    (· > · : y.support → y.support → Prop) ≃r
      (· > · : (single z c * y).support → (single z c * y).support → Prop) :=
  ⟨⟨fun s ↦ ⟨s.1 + z, (mem_support_single_mul_iff hc).2 (by rw [add_sub_cancel_right]; exact s.2)⟩,
    fun s ↦ ⟨s.1 - z, (mem_support_single_mul_iff hc).1 s.2⟩,
    fun s ↦ Subtype.ext (add_sub_cancel_right s.1 z),
    fun s ↦ Subtype.ext (sub_add_cancel s.1 z)⟩,
   fun {a b} ↦ by
     show b.1 + z < a.1 + z ↔ b.1 < a.1
     exact add_lt_add_iff_right z⟩

/-- **The length of a single-term product is the length of the factor.** -/
theorem length_single_mul {c : ℝ} (hc : c ≠ 0) (z : Surreal.{u}) (y : SurrealHahnSeries.{u}) :
    (single z c * y).length = y.length := by
  have h := (singleMulRelIso hc z y).ordinalType_congr
  rw [type_support, type_support, Ordinal.lift_inj] at h
  exact h.symm

/-- The index of a translated exponent is the index of the exponent. -/
theorem symm_exp_single_mul {c : ℝ} (hc : c ≠ 0) (z : Surreal.{u}) (y : SurrealHahnSeries.{u})
    (s : y.support) :
    ((single z c * y).exp.symm (singleMulRelIso hc z y s)).1 = (y.exp.symm s).1 := by
  have h := Ordinal.typein_apply (singleMulRelIso hc z y).toInitialSeg s
  rw [typein_support, typein_support, Ordinal.lift_inj] at h
  exact h

/-- **The exponents of a single-term product are the translated exponents.** -/
theorem exp_single_mul {c : ℝ} (hc : c ≠ 0) {z : Surreal.{u}} {y : SurrealHahnSeries.{u}}
    {j : Ordinal.{u}} (hj : j < (single z c * y).length) (hj' : j < y.length) :
    ((single z c * y).exp ⟨j, hj⟩).1 = (y.exp ⟨j, hj'⟩).1 + z := by
  have h1 := symm_exp_single_mul hc z y (y.exp ⟨j, hj'⟩)
  rw [RelIso.symm_apply_apply] at h1
  have h2 : (single z c * y).exp.symm (singleMulRelIso hc z y (y.exp ⟨j, hj'⟩)) = ⟨j, hj⟩ :=
    Subtype.ext h1
  have h3 := congrArg (single z c * y).exp h2
  rw [RelIso.apply_symm_apply] at h3
  rw [← h3]
  rfl

/-- **The terms of a single-term product are the scaled terms**:
`(single z c * y).term j = c · ω^ z · y.term j` (at every index). -/
theorem term_single_mul {c : ℝ} (hc : c ≠ 0) (z : Surreal.{u}) (y : SurrealHahnSeries.{u})
    (j : Ordinal.{u}) :
    (single z c * y).term j = (c : Surreal.{u}) * ω^ z * y.term j := by
  rcases lt_or_ge j y.length with hj | hj
  · have hj' : j < (single z c * y).length := (length_single_mul hc z y).symm ▸ hj
    rw [term_of_lt hj', term_of_lt hj, coeffIdx_of_lt hj', coeffIdx_of_lt hj,
      exp_single_mul hc hj' hj, coeff_single_mul, add_sub_cancel_right, Real.toSurreal_mul,
      Surreal.wpow_add]
    ring
  · rw [term_of_le hj, term_of_le (by rwa [length_single_mul hc]), mul_zero]

/-! ### Finite supports: a series is the sum of its single terms -/

theorem coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → SurrealHahnSeries.{u})
    (i : Surreal.{u}) : (∑ e ∈ s, f e).coeff i = ∑ e ∈ s, (f e).coeff i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, coeff_add_apply, ih]

/-- **A series with finite support is the sum of its single terms.** -/
theorem eq_sum_single {x : SurrealHahnSeries.{u}} (hx : x.support.Finite) :
    x = ∑ e ∈ hx.toFinset, single e (x.coeff e) := by
  ext i
  rw [coeff_finset_sum]
  simp only [coeff_single, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  split_ifs with hi
  · rfl
  · rw [Set.Finite.mem_toFinset, mem_support_iff, not_not] at hi
    exact hi

end SurrealHahnSeries

/-! ### SINGLE-TERM AND FINITE-SUPPORT PRODUCTS -/

namespace Surreal

open SurrealHahnSeries

/-- **SINGLE-TERM PRODUCTS**: for a nonzero real `c`,
`evalHahn (single z c * y) = c · ω^ z · evalHahn y`. The support of the product is the translate
of `y`'s support by `z`, the terms are the terms of `y` scaled by `c · ω^ z`, and the scaling
theorem `hahnSumO_monomial_mul` identifies the canonical sum. -/
theorem evalHahn_single_mul {c : ℝ} (hc : c ≠ 0) (z : Surreal.{u}) (y : SurrealHahnSeries.{u}) :
    evalHahn (single z c * y) = (c : Surreal.{u}) * ω^ z * evalHahn y := by
  unfold evalHahn
  rw [length_single_mul hc, hahnSumO_congr fun j _ ↦ term_single_mul hc z y j]
  exact hahnSumO_monomial_mul y.isStrictDom_term hc z

/-- Single-term products, every real coefficient. -/
theorem evalHahn_single_mul' (z : Surreal.{u}) (c : ℝ) (y : SurrealHahnSeries.{u}) :
    evalHahn (single z c * y) = (c : Surreal.{u}) * ω^ z * evalHahn y := by
  by_cases hc : c = 0
  · rw [hc, single_zero, zero_mul, evalHahn_zero, Real.toSurreal_zero, zero_mul, zero_mul]
  · exact evalHahn_single_mul hc z y

theorem evalHahn_mul_single (y : SurrealHahnSeries.{u}) (z : Surreal.{u}) (c : ℝ) :
    evalHahn (y * single z c) = evalHahn y * ((c : Surreal.{u}) * ω^ z) := by
  rw [mul_comm, evalHahn_single_mul', mul_comm]

/-- Single-term products are multiplicative in the evaluation. -/
theorem evalHahn_single_mul_eq (z : Surreal.{u}) (c : ℝ) (y : SurrealHahnSeries.{u}) :
    evalHahn (single z c * y) = evalHahn (single z c) * evalHahn y := by
  rw [evalHahn_single_mul', evalHahn_single]

theorem evalHahn_one : evalHahn (1 : SurrealHahnSeries.{u}) = 1 := by
  rw [one_eq_single, evalHahn_single, wpow_zero, mul_one, Real.toSurreal_one]

private theorem evalHahn_sum_single_mul (s : Finset Surreal.{u}) (f : Surreal.{u} → ℝ)
    (y : SurrealHahnSeries.{u}) :
    evalHahn ((∑ e ∈ s, single e (f e)) * y) =
      evalHahn (∑ e ∈ s, single e (f e)) * evalHahn y := by
  rw [Finset.sum_mul, evalHahn_sum, evalHahn_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun e _ ↦ evalHahn_single_mul_eq e (f e) y

/-- **FINITE-SUPPORT PRODUCTS**: if `x` has finite support (finitely many terms),
`evalHahn (x * y) = evalHahn x * evalHahn y` for every `y`. -/
theorem evalHahn_mul_of_finite_support {x : SurrealHahnSeries.{u}} (hx : x.support.Finite)
    (y : SurrealHahnSeries.{u}) : evalHahn (x * y) = evalHahn x * evalHahn y := by
  have h := evalHahn_sum_single_mul hx.toFinset x.coeff y
  rwa [← eq_sum_single hx] at h

/-- Finite-support products, the factor on the right. -/
theorem evalHahn_mul_of_finite_support' (x : SurrealHahnSeries.{u}) {y : SurrealHahnSeries.{u}}
    (hy : y.support.Finite) : evalHahn (x * y) = evalHahn x * evalHahn y := by
  rw [mul_comm, evalHahn_mul_of_finite_support hy, mul_comm]

/-- Normal-form extraction of a single-term product. -/
theorem toHahnSeries_single_mul (z : Surreal.{u}) (c : ℝ) (x : Surreal.{u}) :
    toHahnSeries ((c : Surreal.{u}) * ω^ z * x) = single z c * toHahnSeries x := by
  rw [toHahnSeries_eq_iff, evalHahn_single_mul', evalHahn_toHahnSeries]

end Surreal

end
