/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.BirthdayHahn

/-!
# Identification theorems for canonical transfinite sums

`Infinity.BirthdayHahn` reduced the exact evaluation of canonical sums — and with it the
additivity and exp-multiplicativity of the operator — to birthday-minimality within halos of
perturbations lying below every term scale. This file proves the first *general*
identification theorems: unconditional criteria under which a candidate value provably *is*
the canonical sum. The engine is a new bridge between birthday and magnitude:

## The birthday–magnitude bridges

* `isFinite_of_birthday_lt_omega0` / `omega0_le_birthday_of_not_isFinite` : surreals born
  before day `ω` are dyadic rationals, hence finite; infinite surreals are born at or after
  day `ω`.
* **The day-`ω` classification of infinite surreals** —
  `eq_wpow_one_of_pos_of_not_isFinite_of_birthday_le` and its variants: *the only infinite
  surreals born by day `ω` are `ω` and `-ω`*. The proof is sign-expansion-free: choose a
  birthday-minimal numeric game `g` for such a surreal; all of `g`'s options are dyadic
  (born before day `ω`), so no right option can exceed an infinite value (`gᴿ` is
  empty-in-effect) and every left option is finite, whence `ω` fits between `g`'s option
  cuts; by the upstream simplicity theorem (`Cut.simplestBtwn_supLeft_infRight`) the value
  of `g` is the *simplest* fit, and by the uniqueness of simplest fits
  (`Cut.eq_of_fits_of_birthday_le`) it must equal `ω`.
* `omega0_add_one_le_birthday_of_not_isFinite_of_ne` : an infinite surreal other than
  `±ω` is born at or after day `ω + 1`.

## Identification of canonical sums

For a strictly dominating series whose scales reach the finite range
(`∃ n, 0 ≤ mk (t n)`), any two Hahn sums differ by an infinitesimal; combined with the
bridges this identifies the canonical sum whenever one Hahn sum is provably simpler than
everything in its halo:

* `hahnSum_eq_of_birthday_lt_omega0` : a **dyadic** Hahn sum is the canonical sum.
* `hahnSum_eq_of_not_isFinite_of_birthday_le` : an **infinite** Hahn sum born by day `ω`
  is the canonical sum.
* `hahnSum_eq_of_not_isFinite_of_birthday_le_succ` : an infinite Hahn sum born by day
  `ω + 1` whose halo avoids `±ω` is the canonical sum.
* `hahnSum_eq_of_irrational_stdPart` : a finite Hahn sum born by day `ω` with
  **irrational standard part** is the canonical sum.

## Additivity of the canonical sum, unconditionally, in the identifiable regime

* `hahnSum_add_eq_of_birthday_lt_omega0` / `hahnSum_add_eq_of_not_isFinite_of_birthday_le` /
  `hahnSum_add_eq_of_not_isFinite_of_birthday_le_succ` : under termwise non-cancellation,
  `hahnSum (t + u) = hahnSum t + hahnSum u` whenever the right-hand side lands in an
  identifiable class. These discharge the birthday inequality that
  `hahnSum_add_eq_iff` isolated — no conjecture needed on this regime.
* **The showcase** `hahnSum_add_telescoping_omega` : for the telescoping series (canonical
  sum `1`) and the `ω`-scaled telescoping series (canonical sum `ω`),
  `hahnSum (t + u) = 1 + ω = hahnSum t + hahnSum u` — the first verified instance of
  additivity of canonical transfinite sums in which the combined value is transfinite and
  none of the three sums is evaluated by fiat. Uses the full day-`ω + 1` machinery:
  `birthday (1 + ω) ≤ ω + 1`, while every other Hahn sum of the combined series is
  infinite, is not `±ω`, and is therefore born at or after day `ω + 1`.

## The exponential

* `omega0_le_birthday_of_isHahnSum_expSeries` / `omega0_le_birthday_expInf` : every value
  of the exponential at a positive infinitesimal is born at or after day `ω` —
  exponentials are genuinely transfinite objects.
* `expInf_add_eq_mul_of_birthday_le` : the functional equation
  `expInf (ε + δ) = expInf ε * expInf δ` holds outright **whenever
  `birthday (expInf ε * expInf δ) ≤ ω`** — a one-sided birthday bound on the product
  alone now suffices; no comparison against the other Hahn sums is needed. (Whether that
  antecedent ever holds is open: the classification proved here makes it equivalent to a
  concrete question about day-`ω` surreals infinitesimally close to `1`.)

What remains genuinely open is exactly what `BirthdayHahn` isolated: identification when
the candidate's birthday exceeds `ω + 1` in an essential way (the geometric sum
`ω/(ω−1)`, presumably born at day `ω²`, is the flagship case), which classically follows
from Conway-normal-form birthday theory not yet formalized.
-/

open ArchimedeanClass Filter Finset IGame

noncomputable section

namespace Surreal

/-! ### Birthday–magnitude bridges -/

/-- A surreal born before day `ω` is a dyadic rational, hence finite. -/
theorem isFinite_of_birthday_lt_omega0 {x : Surreal}
    (h : x.birthday < NatOrdinal.of Ordinal.omega0) : IsFinite x := by
  obtain ⟨q, hq⟩ := Surreal.birthday_lt_omega0_iff.1 h
  have hq' : ((q : ℚ) : Surreal) = x := hq
  rw [← hq']
  exact isFinite_ratCast _

/-- **Infinite surreals are born at or after day `ω`.** -/
theorem omega0_le_birthday_of_not_isFinite {x : Surreal} (hx : ¬ IsFinite x) :
    NatOrdinal.of Ordinal.omega0 ≤ x.birthday :=
  le_of_not_gt fun h ↦ hx (isFinite_of_birthday_lt_omega0 h)

private theorem not_isFinite_of_wpow_lt {x : Surreal} (hx : ω^ (1 : Surreal) < x) :
    ¬ IsFinite x := by
  intro h
  obtain ⟨n, hn⟩ := isFinite_iff.1 h
  have hx0 : (0 : Surreal) < x := (wpow_pos _).trans hx
  rw [abs_of_pos hx0] at hn
  exact (natCast_lt_wpow_one n).asymm (hx.trans_le hn)

/-! ### The day-`ω` classification of infinite surreals -/

/-- **The day-`ω` classification, positive case**: a positive infinite surreal born by day
`ω` is exactly `ω`. Proof: take a birthday-minimal numeric game `g` for `y`. All options
of `g` are born before day `ω`, hence are dyadic and finite; so no right option can
dominate the infinite value `y` (there are none in effect), and `ω` fits between `g`'s
option cuts. By the simplicity theorem `y` is the simplest such fit, and by uniqueness of
simplest fits `y = ω`. -/
theorem eq_wpow_one_of_pos_of_not_isFinite_of_birthday_le {y : Surreal}
    (hy0 : 0 < y) (hy : ¬ IsFinite y)
    (hb : y.birthday ≤ NatOrdinal.of Ordinal.omega0) :
    y = ω^ (1 : Surreal) := by
  -- `y` exceeds every natural number.
  have hyn : ∀ n : ℕ, (n : Surreal) < y := by
    intro n
    by_contra hn
    rw [not_lt] at hn
    exact hy (isFinite_iff.2 ⟨n, by rwa [abs_of_pos hy0]⟩)
  -- A birthday-minimal numeric representation of `y`.
  obtain ⟨g, hgn, hgy, hgb⟩ := birthday_eq_iGameBirthday y
  haveI := hgn
  -- `ω` fits between the option cuts of `g`: every option of `g` is born before day `ω`,
  -- hence dyadic and finite, so left options sit below `ω` and right options (which would
  -- have to exceed the infinite value `y`) cannot exist in effect.
  have hslt := Cut.supLeft_lt_infRight_of_numeric g
  have hfitω : Cut.Fits (ω^ (1 : Surreal)) (Cut.supLeft g) (Cut.infRight g) := by
    rw [Cut.Fits, Set.mem_inter_iff]
    constructor
    · rw [Cut.right_supLeft]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro i hi
      haveI : i.Numeric := IGame.Numeric.of_mem_moves hi
      have hbi : (Surreal.mk i).birthday < NatOrdinal.of Ordinal.omega0 :=
        (birthday_mk_le i).trans_lt
          ((IGame.birthday_lt_of_mem_moves hi).trans_le (hgb.le.trans hb))
      obtain ⟨n, hn⟩ := isFinite_iff.1 (isFinite_of_birthday_lt_omega0 hbi)
      have hlt : Surreal.mk i < ω^ (1 : Surreal) :=
        calc Surreal.mk i ≤ |Surreal.mk i| := le_abs_self _
          _ ≤ n := hn
          _ < ω^ (1 : Surreal) := natCast_lt_wpow_one n
      rw [← toGame_mk, toGame_le_iff]
      exact not_le.2 hlt
    · rw [Cut.left_infRight]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro j hj
      haveI : j.Numeric := IGame.Numeric.of_mem_moves hj
      have hyj : y < Surreal.mk j := by
        rw [← hgy]
        exact mk_lt_mk.2 (IGame.Numeric.lt_right hj)
      have hbj : (Surreal.mk j).birthday < NatOrdinal.of Ordinal.omega0 :=
        (birthday_mk_le j).trans_lt
          ((IGame.birthday_lt_of_mem_moves hj).trans_le (hgb.le.trans hb))
      obtain ⟨n, hn⟩ := isFinite_iff.1 (isFinite_of_birthday_lt_omega0 hbj)
      have hjn : Surreal.mk j ≤ n := (le_abs_self _).trans hn
      exact ((hyn n).asymm (hyj.trans_le hjn)).elim
  -- `y` is the simplest fit between the option cuts of `g` (the simplicity theorem).
  have hy' : Cut.simplestBtwn hslt = y := by
    rw [← toGame_inj, Cut.simplestBtwn_supLeft_infRight hslt, ← hgy, toGame_mk]
  have hfity : Cut.Fits y (Cut.supLeft g) (Cut.infRight g) := hy' ▸ Cut.fits_simplestBtwn hslt
  have hmin : ∀ v, Cut.Fits v (Cut.supLeft g) (Cut.infRight g) → y.birthday ≤ v.birthday := by
    intro v hv
    have h := Cut.birthday_simplestBtwn_le_of_fits hv
    rwa [hy'] at h
  -- Uniqueness of simplest fits: `ω` is a fit no more complex than `y`, so it *is* `y`.
  exact (Cut.eq_of_fits_of_birthday_le hfity hfitω hmin
    (by rw [birthday_wpow_one]; exact omega0_le_birthday_of_not_isFinite hy)).symm

/-- The day-`ω` classification, negative case: a negative infinite surreal born by day `ω`
is exactly `-ω`. -/
theorem eq_neg_wpow_one_of_neg_of_not_isFinite_of_birthday_le {y : Surreal}
    (hy0 : y < 0) (hy : ¬ IsFinite y)
    (hb : y.birthday ≤ NatOrdinal.of Ordinal.omega0) :
    y = -ω^ (1 : Surreal) := by
  have h := eq_wpow_one_of_pos_of_not_isFinite_of_birthday_le (y := -y)
    (neg_pos.2 hy0) (fun h ↦ hy (by simpa using h.neg)) (by rwa [birthday_neg])
  linarith

/-- **The day-`ω` classification of infinite surreals**: the only infinite surreals born
by day `ω` are `ω` and `-ω`. In particular `ω` is the unique simplest positive infinite
surreal. -/
theorem eq_wpow_one_or_eq_neg_of_not_isFinite_of_birthday_le {y : Surreal}
    (hy : ¬ IsFinite y) (hb : y.birthday ≤ NatOrdinal.of Ordinal.omega0) :
    y = ω^ (1 : Surreal) ∨ y = -ω^ (1 : Surreal) := by
  rcases lt_trichotomy y 0 with h | h | h
  · exact .inr (eq_neg_wpow_one_of_neg_of_not_isFinite_of_birthday_le h hy hb)
  · exact absurd (by rw [h]; exact isFinite_zero) hy
  · exact .inl (eq_wpow_one_of_pos_of_not_isFinite_of_birthday_le h hy hb)

/-- An infinite surreal other than `±ω` is born at or after day `ω + 1`. -/
theorem omega0_add_one_le_birthday_of_not_isFinite_of_ne {y : Surreal}
    (hy : ¬ IsFinite y) (h1 : y ≠ ω^ (1 : Surreal)) (h2 : y ≠ -ω^ (1 : Surreal)) :
    NatOrdinal.of Ordinal.omega0 + 1 ≤ y.birthday := by
  refine Order.add_one_le_of_lt ((omega0_le_birthday_of_not_isFinite hy).lt_of_ne ?_)
  intro heq
  rcases eq_wpow_one_or_eq_neg_of_not_isFinite_of_birthday_le hy heq.ge with h | h
  · exact h1 h
  · exact h2 h

/-- **An exact transfinite birthday**: `birthday (1 + ω) = ω + 1`. The upper bound is the
additivity estimate; the lower bound is the day-`ω` classification (an infinite surreal
other than `±ω` is born at or after day `ω + 1`). The second exactly-computed birthday of
an infinite surreal in this development, after `birthday ω = ω`. -/
theorem birthday_one_add_wpow :
    ((1 : Surreal) + ω^ (1 : Surreal)).birthday = NatOrdinal.of Ordinal.omega0 + 1 := by
  have hω : (0 : Surreal) < ω^ (1 : Surreal) := wpow_pos _
  refine le_antisymm ?_ ?_
  · refine (birthday_add_le _ _).trans (le_of_eq ?_)
    rw [birthday_one, birthday_wpow_one, add_comm]
  · refine omega0_add_one_le_birthday_of_not_isFinite_of_ne
      (not_isFinite_of_wpow_lt (lt_one_add _)) ?_ ?_
    · intro h
      exact one_ne_zero (by linarith : (1 : Surreal) = 0)
    · intro h
      have h2 : (1 : Surreal) + 2 * ω^ (1 : Surreal) = 0 := by linarith
      linarith

/-! ### Identification theorems for canonical sums -/

variable {t u : ℕ → Surreal}

/-- Two Hahn sums of a strictly dominating series whose scales reach the finite range
differ by an infinitesimal. -/
theorem infinitesimal_sub_of_isHahnSum {x z : Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hx : IsHahnSum t x) (hz : IsHahnSum t z)
    (hsc : ∃ n, 0 ≤ ArchimedeanClass.mk (t n)) : Infinitesimal (x - z) := by
  obtain ⟨n, hn⟩ := hsc
  exact lt_of_le_of_lt hn ((ht n).trans_le (IsHahnSum.mk_sub_le hx hz (n + 1)))

/-- **Identification I (dyadic values)**: a Hahn sum born before day `ω` — i.e. a dyadic
rational — is the canonical sum: every other Hahn sum is a nonzero infinitesimal
perturbation of a dyadic, hence born at or after day `ω`. -/
theorem hahnSum_eq_of_birthday_lt_omega0
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {z : Surreal} (hz : IsHahnSum t z)
    (hb : z.birthday < NatOrdinal.of Ordinal.omega0)
    (hsc : ∃ n, 0 ≤ ArchimedeanClass.mk (t n)) :
    hahnSum ht = z := by
  rw [hahnSum_eq_iff]
  refine ⟨hz, fun w hw ↦ ?_⟩
  rcases eq_or_ne w z with rfl | hne
  · exact le_rfl
  · exact hb.le.trans (omega0_le_birthday_of_infinitesimal_sub hb
      (infinitesimal_sub_of_isHahnSum ht hw hz hsc) hne)

/-- **Identification II (infinite values)**: an infinite Hahn sum born by day `ω` is the
canonical sum: every other Hahn sum is also infinite, hence born at or after day `ω`. -/
theorem hahnSum_eq_of_not_isFinite_of_birthday_le
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {z : Surreal} (hz : IsHahnSum t z) (hzf : ¬ IsFinite z)
    (hb : z.birthday ≤ NatOrdinal.of Ordinal.omega0)
    (hsc : ∃ n, 0 ≤ ArchimedeanClass.mk (t n)) :
    hahnSum ht = z := by
  rw [hahnSum_eq_iff]
  refine ⟨hz, fun w hw ↦ ?_⟩
  have hwf : ¬ IsFinite w := by
    intro hwF
    have h1 : Infinitesimal (w - z) := infinitesimal_sub_of_isHahnSum ht hw hz hsc
    have h2 : w - (w - z) = z := by ring
    exact hzf (h2 ▸ hwF.sub h1.isFinite)
  exact hb.trans (omega0_le_birthday_of_not_isFinite hwf)

/-- **Identification III (infinite values at day `ω + 1`)**: an infinite Hahn sum born by
day `ω + 1` whose halo avoids `±ω` is the canonical sum. Uses the day-`ω` classification:
every other Hahn sum is infinite and is not `±ω`, hence born at or after day `ω + 1`. -/
theorem hahnSum_eq_of_not_isFinite_of_birthday_le_succ
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {z : Surreal} (hz : IsHahnSum t z) (hzf : ¬ IsFinite z)
    (hb : z.birthday ≤ NatOrdinal.of Ordinal.omega0 + 1)
    (hzω : ¬ Infinitesimal (z - ω^ (1 : Surreal)))
    (hzω' : ¬ Infinitesimal (z + ω^ (1 : Surreal)))
    (hsc : ∃ n, 0 ≤ ArchimedeanClass.mk (t n)) :
    hahnSum ht = z := by
  rw [hahnSum_eq_iff]
  refine ⟨hz, fun w hw ↦ ?_⟩
  rcases eq_or_ne w z with rfl | hne
  · exact le_rfl
  have hinf : Infinitesimal (w - z) := infinitesimal_sub_of_isHahnSum ht hw hz hsc
  have hwf : ¬ IsFinite w := by
    intro hwF
    have h2 : w - (w - z) = z := by ring
    exact hzf (h2 ▸ hwF.sub hinf.isFinite)
  have h1 : w ≠ ω^ (1 : Surreal) := by
    rintro rfl
    exact hzω (by simpa [neg_sub] using hinf.neg)
  have h2 : w ≠ -ω^ (1 : Surreal) := by
    rintro rfl
    refine hzω' ?_
    have h3 : z + ω^ (1 : Surreal) = -(-ω^ (1 : Surreal) - z) := by ring
    rw [h3]
    exact hinf.neg
  exact hb.trans (omega0_add_one_le_birthday_of_not_isFinite_of_ne hwf h1 h2)

/-- **Identification IV (irrational standard parts)**: a finite Hahn sum born by day `ω`
with irrational standard part is the canonical sum: every Hahn sum has the same standard
part, and a dyadic rational value would force that standard part to be rational. -/
theorem hahnSum_eq_of_irrational_stdPart
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {z : Surreal} (hz : IsHahnSum t z)
    (hirr : ∀ q : ℚ, stdPart z ≠ (q : ℝ))
    (hb : z.birthday ≤ NatOrdinal.of Ordinal.omega0)
    (hsc : ∃ n, 0 ≤ ArchimedeanClass.mk (t n)) :
    hahnSum ht = z := by
  rw [hahnSum_eq_iff]
  refine ⟨hz, fun w hw ↦ ?_⟩
  have hinf : Infinitesimal (w - z) := infinitesimal_sub_of_isHahnSum ht hw hz hsc
  have hst : stdPart w = stdPart z := by
    have hsplit : w = z + (w - z) := by ring
    rw [hsplit, stdPart_add_eq_left hinf]
  refine hb.trans (le_of_not_gt fun hlt ↦ ?_)
  obtain ⟨q, hq⟩ := Surreal.birthday_lt_omega0_iff.1 hlt
  have hq' : ((q : ℚ) : Surreal) = w := hq
  refine hirr (q : ℚ) ?_
  rw [← hst, ← hq', ArchimedeanClass.stdPart_ratCast]

/-! ### Scaling Hahn sums by a constant -/

theorem partialSum_const_mul (c : Surreal) (t : ℕ → Surreal) (n : ℕ) :
    partialSum (fun k ↦ c * t k) n = c * partialSum t n := by
  simp [partialSum, Finset.mul_sum]

/-- Hahn sums scale by arbitrary constants. -/
theorem IsHahnSum.const_mul {x : Surreal} (c : Surreal) (hx : IsHahnSum t x) :
    IsHahnSum (fun n ↦ c * t n) (c * x) := by
  intro n
  show ArchimedeanClass.mk (c * t n) ≤ _
  have h1 : c * x - partialSum (fun k ↦ c * t k) n = c * (x - partialSum t n) := by
    rw [partialSum_const_mul]; ring
  obtain ⟨m, hm⟩ := ArchimedeanClass.mk_le_mk.1 (hx n)
  refine ArchimedeanClass.mk_le_mk.2 ⟨m, ?_⟩
  rw [h1, abs_mul, abs_mul]
  calc |c| * |x - partialSum t n| ≤ |c| * (m • |t n|) :=
        mul_le_mul_of_nonneg_left hm (abs_nonneg c)
    _ = m • (|c| * |t n|) := by rw [nsmul_eq_mul, nsmul_eq_mul]; ring

/-- Multiplication by a nonzero constant preserves strict comparison of Archimedean
classes. -/
theorem mk_mul_lt_mk_mul_of_ne {c a b : Surreal} (hc : c ≠ 0)
    (h : ArchimedeanClass.mk a < ArchimedeanClass.mk b) :
    ArchimedeanClass.mk (c * a) < ArchimedeanClass.mk (c * b) := by
  rw [ArchimedeanClass.mk_lt_mk] at h ⊢
  intro j
  have hc' : (0 : Surreal) < |c| := abs_pos.2 hc
  calc j • |c * b| = |c| * (j • |b|) := by
        rw [abs_mul, nsmul_eq_mul, nsmul_eq_mul]; ring
    _ < |c| * |a| := mul_lt_mul_of_pos_left (h j) hc'
    _ = |c * a| := (abs_mul ..).symm

/-- Scaling a strictly dominating series by a nonzero constant preserves strict
domination. -/
theorem strict_dominating_const_mul {c : Surreal} (hc : c ≠ 0)
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) (n : ℕ) :
    ArchimedeanClass.mk (c * t n) < ArchimedeanClass.mk (c * t (n + 1)) :=
  mk_mul_lt_mk_mul_of_ne hc (ht n)

/-! ### Additivity of the canonical sum in the identifiable regime -/

/-- **Unconditional additivity, dyadic regime**: for non-cancelling strictly dominating
series whose scales reach the finite range, if `hahnSum t + hahnSum u` is born before day
`ω` then the canonical sum is additive at `(t, u)`. -/
theorem hahnSum_add_eq_of_birthday_lt_omega0
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (hnc : ∀ n, ArchimedeanClass.mk (t n + u n) ≤
      min (ArchimedeanClass.mk (t n)) (ArchimedeanClass.mk (u n)))
    (hb : (hahnSum ht + hahnSum hu).birthday < NatOrdinal.of Ordinal.omega0)
    (hsc : ∃ n, 0 ≤ ArchimedeanClass.mk (t n + u n)) :
    hahnSum (strict_dominating_add ht hu hnc) = hahnSum ht + hahnSum hu :=
  hahnSum_eq_of_birthday_lt_omega0 _
    ((isHahnSum_hahnSum ht).add (isHahnSum_hahnSum hu) hnc) hb hsc

/-- **Unconditional additivity, infinite regime**: likewise if `hahnSum t + hahnSum u` is
infinite and born by day `ω`. -/
theorem hahnSum_add_eq_of_not_isFinite_of_birthday_le
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (hnc : ∀ n, ArchimedeanClass.mk (t n + u n) ≤
      min (ArchimedeanClass.mk (t n)) (ArchimedeanClass.mk (u n)))
    (hf : ¬ IsFinite (hahnSum ht + hahnSum hu))
    (hb : (hahnSum ht + hahnSum hu).birthday ≤ NatOrdinal.of Ordinal.omega0)
    (hsc : ∃ n, 0 ≤ ArchimedeanClass.mk (t n + u n)) :
    hahnSum (strict_dominating_add ht hu hnc) = hahnSum ht + hahnSum hu :=
  hahnSum_eq_of_not_isFinite_of_birthday_le _
    ((isHahnSum_hahnSum ht).add (isHahnSum_hahnSum hu) hnc) hf hb hsc

/-- **Unconditional additivity, day-`ω + 1` regime**: likewise if `hahnSum t + hahnSum u`
is infinite, born by day `ω + 1`, and not infinitesimally close to `±ω`. -/
theorem hahnSum_add_eq_of_not_isFinite_of_birthday_le_succ
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (hnc : ∀ n, ArchimedeanClass.mk (t n + u n) ≤
      min (ArchimedeanClass.mk (t n)) (ArchimedeanClass.mk (u n)))
    (hf : ¬ IsFinite (hahnSum ht + hahnSum hu))
    (hb : (hahnSum ht + hahnSum hu).birthday ≤ NatOrdinal.of Ordinal.omega0 + 1)
    (hω : ¬ Infinitesimal (hahnSum ht + hahnSum hu - ω^ (1 : Surreal)))
    (hω' : ¬ Infinitesimal (hahnSum ht + hahnSum hu + ω^ (1 : Surreal)))
    (hsc : ∃ n, 0 ≤ ArchimedeanClass.mk (t n + u n)) :
    hahnSum (strict_dominating_add ht hu hnc) = hahnSum ht + hahnSum hu :=
  hahnSum_eq_of_not_isFinite_of_birthday_le_succ _
    ((isHahnSum_hahnSum ht).add (isHahnSum_hahnSum hu) hnc) hf hb hω hω' hsc

/-! ### The showcase: `hahnSum (t + u) = 1 + ω` for the telescoping pair -/

private theorem eps0_infinitesimal' : Infinitesimal eps0 :=
  show Infinitesimal (ω^ (1 : Surreal))⁻¹ from infinitesimal_inv_wpow one_pos

private theorem wpow_mul_eps0 : ω^ (1 : Surreal) * eps0 = 1 := by
  rw [eps0_def]
  exact mul_inv_cancel₀ (wpow_pos _).ne'

/-- Termwise non-cancellation for the telescoping pair: adding the `ω`-scaled telescoping
series to the telescoping series only coarsens each term's scale to that of the dominant
(`ω`-scaled) summand. -/
theorem noncancel_telescoping_omega (n : ℕ) :
    ArchimedeanClass.mk ((eps0 ^ n - eps0 ^ (n + 1)) +
        ω^ (1 : Surreal) * (eps0 ^ n - eps0 ^ (n + 1))) ≤
      min (ArchimedeanClass.mk (eps0 ^ n - eps0 ^ (n + 1)))
        (ArchimedeanClass.mk (ω^ (1 : Surreal) * (eps0 ^ n - eps0 ^ (n + 1)))) := by
  set τ : Surreal.{0} := eps0 ^ n - eps0 ^ (n + 1) with hτ
  have hsum : τ + ω^ (1 : Surreal) * τ = (1 + ω^ (1 : Surreal)) * τ := by ring
  have hω0 : (0 : Surreal) < ω^ (1 : Surreal) := wpow_pos _
  have h1ω : (0 : Surreal) < 1 + ω^ (1 : Surreal) := by linarith
  rw [hsum]
  refine le_min ?_ ?_
  · -- `mk ((1 + ω) * τ) ≤ mk τ`
    refine ArchimedeanClass.mk_le_mk.2 ⟨1, ?_⟩
    rw [one_nsmul, abs_mul, abs_of_pos h1ω]
    exact le_mul_of_one_le_left (abs_nonneg τ) (by linarith)
  · -- `mk ((1 + ω) * τ) ≤ mk (ω * τ)`
    refine ArchimedeanClass.mk_le_mk.2 ⟨1, ?_⟩
    rw [one_nsmul, abs_mul, abs_mul, abs_of_pos h1ω, abs_of_pos hω0]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg τ)

private theorem scale_witness_telescoping_omega :
    ∃ n, 0 ≤ ArchimedeanClass.mk ((eps0 ^ n - eps0 ^ (n + 1)) +
      ω^ (1 : Surreal) * (eps0 ^ n - eps0 ^ (n + 1))) := by
  refine ⟨1, ?_⟩
  have hval : (eps0 ^ 1 - eps0 ^ (1 + 1)) +
      ω^ (1 : Surreal) * (eps0 ^ 1 - eps0 ^ (1 + 1)) = 1 - eps0 ^ 2 := by
    have h1 : ω^ (1 : Surreal) * (eps0 ^ 1 - eps0 ^ (1 + 1)) =
        (ω^ (1 : Surreal) * eps0) * (1 - eps0) := by ring
    rw [h1, wpow_mul_eps0, one_mul]
    ring
  rw [hval]
  have hinf2 : Infinitesimal (eps0 ^ 2) := by
    rw [pow_two]
    exact eps0_infinitesimal'.mul_isFinite eps0_infinitesimal'.isFinite
  have hst : stdPart ((1 : Surreal) - eps0 ^ 2) = 1 := by
    rw [stdPart_sub isFinite_one hinf2.isFinite, hinf2.stdPart_eq_zero,
      ArchimedeanClass.stdPart_one, sub_zero]
  rw [mk_eq_zero_of_stdPart_ne_zero (by rw [hst]; norm_num)]

/-- **The additivity showcase**: the canonical transfinite sum is additive on the
telescoping pair — `hahnSum (Σ (τₖ + ω·τₖ)) = 1 + ω = hahnSum (Σ τₖ) + hahnSum (Σ ω·τₖ)`
for `τₖ = ω⁻ᵏ − ω⁻⁽ᵏ⁺¹⁾`. The first verified instance of additivity of canonical sums
with a transfinite combined value: the candidate `1 + ω` is born by day `ω + 1`, while
every other Hahn sum of the combined series is infinite and distinct from `±ω`, hence born
strictly later. -/
theorem hahnSum_add_telescoping_omega :
    hahnSum (strict_dominating_add telescoping_strict_dominating
        omega_telescoping_strict_dominating noncancel_telescoping_omega) =
      hahnSum telescoping_strict_dominating +
        hahnSum omega_telescoping_strict_dominating := by
  rw [hahnSum_telescoping_eq_one, hahnSum_omega_telescoping_eq]
  have hω0 : (0 : Surreal) < ω^ (1 : Surreal) := wpow_pos _
  refine hahnSum_eq_of_not_isFinite_of_birthday_le_succ _
    (isHahnSum_telescoping.add isHahnSum_omega_telescoping noncancel_telescoping_omega)
    (not_isFinite_of_wpow_lt (by linarith)) ?_ ?_ ?_ scale_witness_telescoping_omega
  · -- `birthday (1 + ω) ≤ ω + 1`
    refine (birthday_add_le _ _).trans (le_of_eq ?_)
    rw [birthday_one, birthday_wpow_one, add_comm]
  · -- `1 + ω − ω = 1` is not infinitesimal
    have h1 : (1 : Surreal) + ω^ (1 : Surreal) - ω^ (1 : Surreal) = 1 := by ring
    rw [h1]
    intro h
    rw [infinitesimal_def, ArchimedeanClass.mk_one] at h
    exact lt_irrefl _ h
  · -- `1 + ω + ω` is not infinitesimal (it is not even finite)
    intro h
    exact not_isFinite_of_wpow_lt (x := 1 + ω^ (1 : Surreal) + ω^ (1 : Surreal))
      (by linarith) h.isFinite

/-- The combined telescoping sum, evaluated: `hahnSum (Σ (τₖ + ω·τₖ)) = 1 + ω` — a new
exact closed-form canonical sum at a transfinite birthday not equal to `ω` itself. -/
theorem hahnSum_add_telescoping_omega_eq :
    hahnSum (strict_dominating_add telescoping_strict_dominating
        omega_telescoping_strict_dominating noncancel_telescoping_omega) =
      1 + ω^ (1 : Surreal) := by
  rw [hahnSum_add_telescoping_omega, hahnSum_telescoping_eq_one,
    hahnSum_omega_telescoping_eq]

/-! ### The exponential is transfinite-born, and a one-sided criterion for the
functional equation -/

private theorem partialSum_expSeries_one {σ : Surreal} :
    partialSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) 1 = 1 := by
  rw [partialSum, Finset.sum_range_one]
  norm_num

private theorem partialSum_expSeries_two {σ : Surreal} :
    partialSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) 2 = 1 + σ := by
  rw [partialSum, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num

/-- Every Hahn sum of the exponential series at a positive infinitesimal is born at or
after day `ω`: it is infinitesimally close to `1` but — since `1` itself is not a Hahn
sum — distinct from it. -/
theorem omega0_le_birthday_of_isHahnSum_expSeries {σ : Surreal}
    (hσ : Infinitesimal σ) (hσ0 : 0 < σ) {y : Surreal}
    (hy : IsHahnSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) y) :
    NatOrdinal.of Ordinal.omega0 ≤ y.birthday := by
  have hinf : Infinitesimal (y - 1) := by
    have h1 := hy 1
    rw [partialSum_expSeries_one] at h1
    have ht1 : ArchimedeanClass.mk (σ ^ 1 / (((1 : ℕ).factorial : ℕ) : Surreal)) =
        ArchimedeanClass.mk σ := by norm_num
    rw [ht1] at h1
    exact lt_of_lt_of_le hσ h1
  have hne : y ≠ 1 := by
    rintro rfl
    have h2 := hy 2
    rw [partialSum_expSeries_two] at h2
    have hval : (1 : Surreal) - (1 + σ) = -σ := by ring
    rw [hval, ArchimedeanClass.mk_neg] at h2
    have ht2 : ArchimedeanClass.mk (σ ^ 2 / (((2 : ℕ).factorial : ℕ) : Surreal)) =
        ArchimedeanClass.mk (σ ^ 2) := by
      rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero]
    rw [ht2] at h2
    have hlt : ArchimedeanClass.mk (σ ^ 1) < ArchimedeanClass.mk (σ ^ 2) :=
      mk_pow_lt_mk_pow_succ hσ hσ0 1
    rw [pow_one] at hlt
    exact absurd h2 (not_le.2 hlt)
  refine omega0_le_birthday_of_infinitesimal_sub ?_ hinf hne
  rw [birthday_one, ← NatOrdinal.of_one, NatOrdinal.of_lt_iff, NatOrdinal.val_of]
  exact Ordinal.one_lt_omega0

/-- **The exponential is transfinite-born**: `expInf ε` is born at or after day `ω` for
every positive infinitesimal `ε`. -/
theorem omega0_le_birthday_expInf {ε : Surreal} (hε : Infinitesimal ε) (hε0 : 0 < ε) :
    NatOrdinal.of Ordinal.omega0 ≤ (expInf ε hε hε0.ne').birthday :=
  omega0_le_birthday_of_isHahnSum_expSeries hε hε0 (isHahnSum_expInf hε hε0.ne')

/-- **A one-sided criterion for the exponential functional equation**: for positive
infinitesimals, `expInf (ε + δ) = expInf ε * expInf δ` holds outright as soon as the
product is born by day `ω` — because *every* Hahn sum of the exponential series at
`ε + δ` is born at or after day `ω`. This upgrades the two-sided minimality condition of
`expInf_add_eq_mul_iff` to a single birthday bound on the product alone. -/
theorem expInf_add_eq_mul_of_birthday_le {ε δ : Surreal}
    (hε : Infinitesimal ε) (hδ : Infinitesimal δ) (hε0 : 0 < ε) (hδ0 : 0 < δ)
    (hb : (expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne').birthday ≤
      NatOrdinal.of Ordinal.omega0) :
    expInf (ε + δ) (hε.add hδ) (by positivity) =
      expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne' := by
  rw [expInf_add_eq_mul_iff hε hδ hε0 hδ0]
  intro z hz
  exact hb.trans
    (omega0_le_birthday_of_isHahnSum_expSeries (hε.add hδ) (by positivity) hz)

end Surreal

end
