/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.Identification
import Infinity.ExpFin

/-!
# The day-`ω` census, finite branch: birthdays of `d ± ω⁻¹`

`Infinity.Identification` classified the *infinite* surreals born by day `ω`: only `±ω`.
This file begins the classification of the *finite* ones — Conway's day-`ω` census
(ONAG, ch. 2: the numbers born on day `ω` are the non-dyadic reals, `±ω`, and the
neighbours `d ± 1/ω` of the dyadics) — by constructing the exceptional elements and
computing their birthdays:

* `dyadicPlusInv d` — the two-sided cut `!{d | d + q}` (over positive dyadic `q`) as an
  explicit game with dyadic options;
* `dyadic_add_wpow_neg_one_eq` — its value **is** `d + ω⁻¹`: Conway addition of the
  canonical dyadic game and CG's genetic `ω`-power game `ω^(−1)` is mutually cofinal
  with the two-sided cut (a pure order computation, no simplicity);
* `birthday_dyadic_add_wpow_neg_one_le` / `birthday_dyadic_sub_wpow_neg_one_le` :
  **`d ± ω⁻¹` is born by day `ω`** — the first birthday bounds in this development for
  surreals that are neither dyadic, real, ordinal, nor `ω`-power shaped;
* `birthday_wpow_neg_one` : **`birthday (ω⁻¹) = ω`** exactly (the case `d = 0`,
  with the lower bound from the infinitesimal-halo bound of `Infinity.BirthdayHahn`).

These are the missing "upper bound" ingredients for the finite day-`ω` classification
(`Infinity.DayOmegaClass`): a surreal born by day `ω` that is infinitesimally close to a
dyadic `d` but distinct from it can only be `d ± ω⁻¹`, because those two are born by day
`ω` and simplest-fit uniqueness (`Cut.eq_of_fits_of_birthday_le`) leaves no room for
anything else.
-/

open ArchimedeanClass Filter Finset IGame Set

universe u

noncomputable section

namespace Surreal

/-! ### Order helpers for `ω⁻¹` -/

theorem infinitesimal_wpow_neg_one : Infinitesimal (ω^ (-1 : Surreal)) := by
  rw [show (-1 : Surreal) = -(1 : Surreal) from rfl, wpow_neg]
  exact infinitesimal_inv_wpow one_pos

theorem wpow_neg_one_lt_dyadic {q : Dyadic} (hq : 0 < q) :
    ω^ (-1 : Surreal) < (q : Surreal) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  exact infinitesimal_wpow_neg_one.lt_ratCast hq'

private theorem dyadic_cast_sub (a b : Dyadic) :
    ((a - b : Dyadic) : Surreal) = (a : Surreal) - (b : Surreal) := by
  show (((a - b : Dyadic) : ℚ) : Surreal) = (((a : Dyadic) : ℚ) : Surreal) - (((b : Dyadic) : ℚ) : Surreal)
  have h : ((a - b : Dyadic) : ℚ) = (a : ℚ) - (b : ℚ) := by push_cast; ring
  rw [h, Rat.cast_sub]

private theorem dyadic_cast_add (a b : Dyadic) :
    ((a + b : Dyadic) : Surreal) = (a : Surreal) + (b : Surreal) := by
  show (((a + b : Dyadic) : ℚ) : Surreal) = (((a : Dyadic) : ℚ) : Surreal) + (((b : Dyadic) : ℚ) : Surreal)
  have h : ((a + b : Dyadic) : ℚ) = (a : ℚ) + (b : ℚ) := by push_cast; ring
  rw [h, Rat.cast_add]

private theorem dyadic_cast_neg (a : Dyadic) :
    ((-a : Dyadic) : Surreal) = -(a : Surreal) := by
  show (((-a : Dyadic) : ℚ) : Surreal) = -(((a : Dyadic) : ℚ) : Surreal)
  have h : ((-a : Dyadic) : ℚ) = -(a : ℚ) := by push_cast; ring
  rw [h, Rat.cast_neg]

/-! ### The two-sided cut `!{d | d + q}` as an explicit game -/

/-- The game `!{d | d + q : 0 < q dyadic}` — the canonical representation of `d + ω⁻¹`
by dyadic options. -/
private def dyadicPlusInv (d : Dyadic) : IGame.{u} :=
  !{{(d : IGame)} | (fun q : Dyadic ↦ ((d + q : Dyadic) : IGame)) '' Set.Ioi 0}

private theorem numeric_dyadicPlusInv (d : Dyadic) : Numeric (dyadicPlusInv d) := by
  rw [dyadicPlusInv]
  refine Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
  · rw [leftMoves_ofSets] at hy
    rw [rightMoves_ofSets] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Dyadic.toIGame_lt_toIGame.2 (lt_add_of_pos_right d hq)
  · cases p with
    | left =>
      rw [moves_ofSets] at hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      infer_instance
    | right =>
      rw [moves_ofSets] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      infer_instance

/-- The moves of the game `ω^ (-1)`. -/
private theorem leftMoves_wpow_neg_one : (ω^ (-1 : IGame))ᴸ = {0} := by
  have h1 : (-1 : IGame)ᴸ = ∅ := by
    rw [show (-1 : IGame) = -(1 : IGame) from rfl]
    simp
  rw [leftMoves_wpow, h1]
  simp

private theorem rightMoves_wpow_neg_one : (ω^ (-1 : IGame))ᴿ =
    (fun r : Dyadic ↦ (r : IGame) * ω^ (0 : IGame)) '' Set.Ioi 0 := by
  have h1 : (-1 : IGame)ᴿ = {0} := by
    rw [show (-1 : IGame) = -(1 : IGame) from rfl]
    simp
  rw [rightMoves_wpow, h1, Set.image2_singleton_right]

private theorem mk_wpow_neg_one : mk (ω^ (-1 : IGame)) = ω^ (-1 : Surreal) := by
  rw [Surreal.mk_wpow]
  norm_num

/-- **Conway addition meets the two-sided cut**: the game sum `d + ω^(−1)` is mutually
cofinal with the cut `!{d | d + q}`. -/
private theorem add_wpow_neg_one_equiv (d : Dyadic) :
    (d : IGame) + ω^ (-1 : IGame) ≈ dyadicPlusInv d := by
  haveI := numeric_dyadicPlusInv d
  have hRHSL : (dyadicPlusInv d)ᴸ = {(d : IGame)} := by
    rw [dyadicPlusInv, leftMoves_ofSets]
  have hRHSR : (dyadicPlusInv d)ᴿ = (fun q : Dyadic ↦ ((d + q : Dyadic) : IGame)) '' Set.Ioi 0 := by
    rw [dyadicPlusInv, rightMoves_ofSets]
  apply equiv_of_exists_le
  · -- every left move of the sum is below the left option `d`
    rw [forall_moves_add]
    constructor
    · intro a ha
      have hal := Dyadic.eq_lower_of_mem_leftMoves_toIGame ha
      subst hal
      refine ⟨(d : IGame), by rw [hRHSL]; exact Set.mem_singleton _, ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_dyadic, Surreal.mk_dyadic,
        mk_wpow_neg_one]
      have hgap : (0 : Dyadic) < d - d.lower := sub_pos.2 (Dyadic.lower_lt d)
      have h2 := wpow_neg_one_lt_dyadic hgap
      rw [dyadic_cast_sub] at h2
      linarith
    · intro b hb
      rw [leftMoves_wpow_neg_one, Set.mem_singleton_iff] at hb
      subst hb
      refine ⟨(d : IGame), by rw [hRHSL]; exact Set.mem_singleton _, ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_dyadic, Surreal.mk_zero]
      simp
  · -- every right move of the sum is above some right option `d + q`
    rw [forall_moves_add]
    constructor
    · intro a ha
      have hau := Dyadic.eq_upper_of_mem_rightMoves_toIGame ha
      subst hau
      have hq : (0 : Dyadic) < d.upper - d := sub_pos.2 (Dyadic.lt_upper d)
      refine ⟨((d + (d.upper - d) : Dyadic) : IGame),
        by rw [hRHSR]; exact Set.mem_image_of_mem _ hq, ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_dyadic, Surreal.mk_dyadic,
        mk_wpow_neg_one, dyadic_cast_add, dyadic_cast_sub]
      have h2 := (wpow_pos (-1 : Surreal)).le
      linarith
    · intro b hb
      rw [rightMoves_wpow_neg_one] at hb
      obtain ⟨r, hr, rfl⟩ := hb
      refine ⟨((d + r : Dyadic) : IGame),
        by rw [hRHSR]; exact Set.mem_image_of_mem _ hr, ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_dyadic, Surreal.mk_dyadic,
        Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow, Surreal.mk_zero,
        dyadic_cast_add, wpow_zero, mul_one]
  · -- the left option `d` is below the sum's left move `d + 0`
    rw [hRHSL]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine ⟨(d : IGame) + 0, add_left_mem_moves_add (by rw [leftMoves_wpow_neg_one]; rfl) _, ?_⟩
    rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_zero]
    simp
  · -- each right option `d + q` is above the sum's right move `d + q·ω⁰`
    rw [hRHSR]
    intro b hb
    obtain ⟨q, hq, rfl⟩ := hb
    refine ⟨(d : IGame) + ((q : IGame) * ω^ (0 : IGame)),
      add_left_mem_moves_add (by rw [rightMoves_wpow_neg_one]; exact Set.mem_image_of_mem _ hq) _, ?_⟩
    rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_dyadic, Surreal.mk_mul,
      Surreal.mk_dyadic, Surreal.mk_wpow, Surreal.mk_zero, Surreal.mk_dyadic,
      dyadic_cast_add, wpow_zero, mul_one]

/-- The value of the two-sided cut `!{d | d + q}` is `d + ω⁻¹`. -/
theorem dyadic_add_wpow_neg_one_eq (d : Dyadic) :
    (d : Surreal) + ω^ (-1 : Surreal) =
      @Surreal.mk (dyadicPlusInv d) (numeric_dyadicPlusInv d) := by
  haveI := numeric_dyadicPlusInv d
  rw [← Surreal.mk_dyadic d, ← mk_wpow_neg_one, ← Surreal.mk_add]
  exact Surreal.mk_eq (add_wpow_neg_one_equiv d)

/-- **`d + ω⁻¹` is born by day `ω`** for every dyadic `d`. -/
theorem birthday_dyadic_add_wpow_neg_one_le (d : Dyadic) :
    ((d : Surreal) + ω^ (-1 : Surreal)).birthday ≤ NatOrdinal.of Ordinal.omega0 := by
  haveI := numeric_dyadicPlusInv d
  refine le_of_eq_of_le (congrArg birthday (dyadic_add_wpow_neg_one_eq d)) ?_
  refine (birthday_mk_le _).trans ?_
  rw [dyadicPlusInv, IGame.birthday_ofSets]
  have hbound : ∀ x : Dyadic, (x : IGame).birthday < NatOrdinal.of Ordinal.omega0 :=
    fun x ↦ IGame.short_iff_birthday_finite.1 (IGame.Short.dyadic x)
  refine max_le ?_ ?_
  · refine csSup_le' ?_
    rintro o ⟨g, hg, rfl⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact Order.succ_le_of_lt (hbound d)
  · refine csSup_le' ?_
    rintro o ⟨g, ⟨q, hq, rfl⟩, rfl⟩
    exact Order.succ_le_of_lt (hbound (d + q))

/-- **`d − ω⁻¹` is born by day `ω`** for every dyadic `d` (by symmetry). -/
theorem birthday_dyadic_sub_wpow_neg_one_le (d : Dyadic) :
    ((d : Surreal) - ω^ (-1 : Surreal)).birthday ≤ NatOrdinal.of Ordinal.omega0 := by
  have h := birthday_dyadic_add_wpow_neg_one_le (-d)
  rw [dyadic_cast_neg] at h
  have heq : (d : Surreal) - ω^ (-1 : Surreal) = -(-(d : Surreal) + ω^ (-1 : Surreal)) := by
    ring
  rw [heq, birthday_neg]
  exact h

/-- **The birthday of `ω⁻¹` is exactly `ω`**: at most `ω` by the cut representation
(`d = 0`), at least `ω` because a nonzero infinitesimal is not dyadic. -/
theorem birthday_wpow_neg_one :
    (ω^ (-1 : Surreal)).birthday = NatOrdinal.of Ordinal.omega0 := by
  refine le_antisymm ?_ ?_
  · have h := birthday_dyadic_add_wpow_neg_one_le 0
    have h0 : ((0 : Dyadic) : Surreal) = 0 := by
      show (((0 : Dyadic) : ℚ) : Surreal) = 0
      norm_num
    rwa [h0, zero_add] at h
  · refine omega0_le_birthday_of_infinitesimal_sub (c := 0) ?_ ?_ (wpow_ne_zero _)
    · rw [birthday_zero]
      exact NatOrdinal.of_pos.2 Ordinal.omega0_pos
    · rw [sub_zero]
      exact infinitesimal_wpow_neg_one

/-! ### Every real is born by day `ω` -/

/-- **Every real number is born by day `ω`** — the birthday bound stated as an open task
in CG's `Surreal/Real.lean`: the canonical representation of a real is its Dedekind cut
of dyadics, all of which are born before day `ω`. -/
theorem birthday_realCast_le (x : ℝ) :
    (x : Surreal).birthday ≤ NatOrdinal.of Ordinal.omega0 := by
  show (Surreal.mk (Real.toIGame x)).birthday ≤ NatOrdinal.of Ordinal.omega0
  refine (birthday_mk_le _).trans ?_
  rw [Real.toIGame, IGame.birthday_ofSets]
  refine max_le ?_ ?_ <;>
  · refine csSup_le' ?_
    rintro o ⟨z, ⟨q, hq, rfl⟩, rfl⟩
    refine Order.succ_le_of_lt ?_
    exact IGame.short_iff_birthday_finite.1 (IGame.Short.dyadic q)

/-- A real cast that is infinitesimal is zero. -/
theorem eq_zero_of_infinitesimal_realCast {r : ℝ} (h : Infinitesimal (r : Surreal)) :
    r = 0 := by
  by_contra hr
  rw [infinitesimal_def, mk_realCast hr] at h
  exact lt_irrefl _ h

/-- Domination transfers infinitesimality. -/
theorem Infinitesimal.mono {a b : Surreal} (hb : Infinitesimal b) (h : |a| ≤ |b|) :
    Infinitesimal a := by
  rw [infinitesimal_iff] at hb ⊢
  intro n
  refine lt_of_le_of_lt ?_ (hb n)
  rw [nsmul_eq_mul, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)

/-! ### The day-`ω` classification: finite surreals with non-dyadic standard part -/

/-- **The day-`ω` classification, non-dyadic branch**: a finite surreal born by day `ω`
whose standard part is not a dyadic rational *is* the real cast of its standard part.
Proof by the method of `Infinity.Identification`: a birthday-minimal game for such a
surreal has all-dyadic options, no dyadic option can enter the infinitesimal halo of a
non-dyadic real, so the real cast fits the option cuts; it is born by day `ω`
(`birthday_realCast_le`), and simplest-fit uniqueness leaves no alternative. -/
theorem eq_realCast_stdPart_of_isFinite_of_birthday_le {y : Surreal}
    (hy : IsFinite y) (hnd : ∀ d : Dyadic, stdPart y ≠ ((d : ℚ) : ℝ))
    (hb : y.birthday ≤ NatOrdinal.of Ordinal.omega0) :
    y = ((stdPart y : ℝ) : Surreal) := by
  -- `y` is not itself a dyadic
  have hynd : NatOrdinal.of Ordinal.omega0 ≤ y.birthday := by
    by_contra h
    rw [not_le] at h
    obtain ⟨q, hq⟩ := Surreal.birthday_lt_omega0_iff.1 h
    have hq' : ((q : ℚ) : Surreal) = y := hq
    refine hnd q ?_
    rw [← hq', ArchimedeanClass.stdPart_ratCast]
  -- the infinitesimal halo
  have hev : Infinitesimal (y - ((stdPart y : ℝ) : Surreal)) := infinitesimal_sub_stdPart hy
  -- a birthday-minimal numeric representation of `y`
  obtain ⟨g, hgn, hgy, hgb⟩ := birthday_eq_iGameBirthday y
  haveI := hgn
  have hslt := Cut.supLeft_lt_infRight_of_numeric g
  -- the real cast fits between the option cuts of `g`
  have hfitc : Cut.Fits ((stdPart y : ℝ) : Surreal) (Cut.supLeft g) (Cut.infRight g) := by
    rw [Cut.Fits, Set.mem_inter_iff]
    constructor
    · rw [Cut.right_supLeft]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro i hi
      haveI : i.Numeric := IGame.Numeric.of_mem_moves hi
      obtain ⟨e, he⟩ := Surreal.birthday_lt_omega0_iff.1 ((birthday_mk_le i).trans_lt
        ((IGame.birthday_lt_of_mem_moves hi).trans_le (hgb.le.trans hb)))
      have he' : ((e : ℚ) : Surreal) = Surreal.mk i := he
      have hiy : Surreal.mk i < y := by
        rw [← hgy]
        exact mk_lt_mk.2 (IGame.Numeric.left_lt hi)
      have hlt : Surreal.mk i < ((stdPart y : ℝ) : Surreal) := by
        by_contra hcon
        rw [not_lt] at hcon
        have h1 : Infinitesimal (Surreal.mk i - ((stdPart y : ℝ) : Surreal)) := by
          refine hev.mono ?_
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        rw [← he', ← Real.toSurreal_ratCast, ← Real.toSurreal_sub] at h1
        have h2 := eq_zero_of_infinitesimal_realCast h1
        exact hnd e (by linarith [sub_eq_zero.1 h2])
      rw [← toGame_mk, toGame_le_iff]
      exact not_le.2 hlt
    · rw [Cut.left_infRight]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro j hj
      haveI : j.Numeric := IGame.Numeric.of_mem_moves hj
      obtain ⟨e, he⟩ := Surreal.birthday_lt_omega0_iff.1 ((birthday_mk_le j).trans_lt
        ((IGame.birthday_lt_of_mem_moves hj).trans_le (hgb.le.trans hb)))
      have he' : ((e : ℚ) : Surreal) = Surreal.mk j := he
      have hyj : y < Surreal.mk j := by
        rw [← hgy]
        exact mk_lt_mk.2 (IGame.Numeric.lt_right hj)
      have hlt : ((stdPart y : ℝ) : Surreal) < Surreal.mk j := by
        by_contra hcon
        rw [not_lt] at hcon
        have h1 : Infinitesimal (((stdPart y : ℝ) : Surreal) - Surreal.mk j) := by
          refine hev.mono ?_
          rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          linarith
        rw [← he', ← Real.toSurreal_ratCast, ← Real.toSurreal_sub] at h1
        have h2 := eq_zero_of_infinitesimal_realCast h1
        exact hnd e (by linarith [sub_eq_zero.1 h2])
      rw [← toGame_mk, toGame_le_iff]
      exact not_le.2 hlt
  -- `y` is the simplest fit; the real cast is a no-later fit; uniqueness finishes
  have hy' : Cut.simplestBtwn hslt = y := by
    rw [← toGame_inj, Cut.simplestBtwn_supLeft_infRight hslt, ← hgy, toGame_mk]
  have hfity : Cut.Fits y (Cut.supLeft g) (Cut.infRight g) :=
    hy' ▸ Cut.fits_simplestBtwn hslt
  have hmin : ∀ v, Cut.Fits v (Cut.supLeft g) (Cut.infRight g) →
      y.birthday ≤ v.birthday := by
    intro v hv
    have h := Cut.birthday_simplestBtwn_le_of_fits hv
    rwa [hy'] at h
  exact (Cut.eq_of_fits_of_birthday_le hfity hfitc hmin
    ((birthday_realCast_le _).trans hynd)).symm

/-- The exact birthday of a non-dyadic real: `ω`. -/
theorem birthday_realCast_eq {r : ℝ} (hnd : ∀ d : Dyadic, r ≠ ((d : ℚ) : ℝ)) :
    ((r : Surreal)).birthday = NatOrdinal.of Ordinal.omega0 := by
  refine le_antisymm (birthday_realCast_le r) ?_
  by_contra h
  rw [not_le] at h
  obtain ⟨q, hq⟩ := Surreal.birthday_lt_omega0_iff.1 h
  have hq' : ((q : ℚ) : Surreal) = (r : Surreal) := hq
  rw [← Real.toSurreal_ratCast, Real.toSurreal_inj] at hq'
  exact hnd q hq'.symm

/-! ### The day-`ω` classification near a dyadic -/

/-- A positive rational-cast bound: a surreal strictly between two rational casts that
differ infinitesimally forces the rationals equal. Auxiliary: an infinitesimal rational
cast is zero. -/
private theorem ratCast_eq_of_infinitesimal_sub {p q : ℚ}
    (h : Infinitesimal (((p : ℚ) : Surreal) - ((q : ℚ) : Surreal))) : p = q := by
  rw [← Real.toSurreal_ratCast, ← Real.toSurreal_ratCast, ← Real.toSurreal_sub] at h
  have h2 := eq_zero_of_infinitesimal_realCast h
  have h3 : ((p : ℚ) : ℝ) = ((q : ℚ) : ℝ) := by linarith [sub_eq_zero.1 h2]
  exact_mod_cast h3

/-- **The day-`ω` classification near a dyadic, positive side**: a surreal born by day
`ω` lying infinitesimally above a dyadic `d` is exactly `d + ω⁻¹`. -/
theorem eq_dyadic_add_wpow_neg_one_of_birthday_le {y : Surreal} {d : Dyadic}
    (hinf : Infinitesimal (y - (d : Surreal))) (hpos : 0 < y - (d : Surreal))
    (hb : y.birthday ≤ NatOrdinal.of Ordinal.omega0) :
    y = (d : Surreal) + ω^ (-1 : Surreal) := by
  -- `y` is not a dyadic
  have hynd : NatOrdinal.of Ordinal.omega0 ≤ y.birthday := by
    by_contra h
    rw [not_le] at h
    obtain ⟨q, hq⟩ := Surreal.birthday_lt_omega0_iff.1 h
    have hq' : ((q : ℚ) : Surreal) = y := hq
    rw [← hq'] at hinf hpos
    have heq := ratCast_eq_of_infinitesimal_sub (p := (q : ℚ)) (q := (d : ℚ)) hinf
    rw [heq] at hpos
    simp at hpos
  -- a birthday-minimal numeric representation of `y`
  obtain ⟨g, hgn, hgy, hgb⟩ := birthday_eq_iGameBirthday y
  haveI := hgn
  have hslt := Cut.supLeft_lt_infRight_of_numeric g
  -- the candidate fits between the option cuts of `g`
  have hfitc : Cut.Fits ((d : Surreal) + ω^ (-1 : Surreal))
      (Cut.supLeft g) (Cut.infRight g) := by
    rw [Cut.Fits, Set.mem_inter_iff]
    constructor
    · rw [Cut.right_supLeft]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro i hi
      haveI : i.Numeric := IGame.Numeric.of_mem_moves hi
      obtain ⟨e, he⟩ := Surreal.birthday_lt_omega0_iff.1 ((birthday_mk_le i).trans_lt
        ((IGame.birthday_lt_of_mem_moves hi).trans_le (hgb.le.trans hb)))
      have he' : ((e : ℚ) : Surreal) = Surreal.mk i := he
      have hiy : Surreal.mk i < y := by
        rw [← hgy]
        exact mk_lt_mk.2 (IGame.Numeric.left_lt hi)
      -- the left option cannot exceed `d`
      have hile : Surreal.mk i ≤ (d : Surreal) := by
        by_contra hcon
        rw [not_le] at hcon
        have h1 : Infinitesimal (Surreal.mk i - (d : Surreal)) := by
          refine hinf.mono ?_
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        rw [← he'] at h1 hcon
        have := ratCast_eq_of_infinitesimal_sub (p := (e : ℚ)) (q := (d : ℚ)) h1
        rw [this] at hcon
        exact lt_irrefl _ hcon
      have hlt : Surreal.mk i < (d : Surreal) + ω^ (-1 : Surreal) :=
        hile.trans_lt (lt_add_of_pos_right _ (wpow_pos _))
      rw [← toGame_mk, toGame_le_iff]
      exact not_le.2 hlt
    · rw [Cut.left_infRight]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro j hj
      haveI : j.Numeric := IGame.Numeric.of_mem_moves hj
      obtain ⟨e, he⟩ := Surreal.birthday_lt_omega0_iff.1 ((birthday_mk_le j).trans_lt
        ((IGame.birthday_lt_of_mem_moves hj).trans_le (hgb.le.trans hb)))
      have he' : ((e : ℚ) : Surreal) = Surreal.mk j := he
      have hyj : y < Surreal.mk j := by
        rw [← hgy]
        exact mk_lt_mk.2 (IGame.Numeric.lt_right hj)
      -- the right option lies strictly above `d`, at dyadic distance
      have hdj : (d : Surreal) < Surreal.mk j := by
        have h1 : (d : Surreal) < y := by linarith
        linarith
      have hde : d < e := by
        rw [← he'] at hdj
        have h1 : ((d : ℚ) : Surreal) < ((e : ℚ) : Surreal) := hdj
        have h2 : ((d : Dyadic) : ℚ) < ((e : Dyadic) : ℚ) := by exact_mod_cast h1
        exact_mod_cast h2
      have hlt : (d : Surreal) + ω^ (-1 : Surreal) < Surreal.mk j := by
        have hgap : (0 : Dyadic) < e - d := sub_pos.2 hde
        have h2 := wpow_neg_one_lt_dyadic hgap
        rw [dyadic_cast_sub] at h2
        rw [← he']
        have h3 : ((e : Dyadic) : Surreal) = ((e : ℚ) : Surreal) := rfl
        rw [h3] at h2
        linarith
      rw [← toGame_mk, toGame_le_iff]
      exact not_le.2 hlt
  -- `y` is the simplest fit; the candidate is a no-later fit; uniqueness finishes
  have hy' : Cut.simplestBtwn hslt = y := by
    rw [← toGame_inj, Cut.simplestBtwn_supLeft_infRight hslt, ← hgy, toGame_mk]
  have hfity : Cut.Fits y (Cut.supLeft g) (Cut.infRight g) :=
    hy' ▸ Cut.fits_simplestBtwn hslt
  have hmin : ∀ v, Cut.Fits v (Cut.supLeft g) (Cut.infRight g) →
      y.birthday ≤ v.birthday := by
    intro v hv
    have h := Cut.birthday_simplestBtwn_le_of_fits hv
    rwa [hy'] at h
  exact (Cut.eq_of_fits_of_birthday_le hfity hfitc hmin
    ((birthday_dyadic_add_wpow_neg_one_le d).trans hynd)).symm

/-- **The day-`ω` classification near a dyadic**: a surreal born by day `ω`
infinitesimally close to a dyadic `d` is `d` itself or one of its two neighbours
`d ± ω⁻¹` — Conway's "d plus-or-minus 1/ω" census entries, machine-checked. -/
theorem day_omega_near_dyadic {y : Surreal} {d : Dyadic}
    (hinf : Infinitesimal (y - (d : Surreal)))
    (hb : y.birthday ≤ NatOrdinal.of Ordinal.omega0) :
    y = (d : Surreal) ∨ y = (d : Surreal) + ω^ (-1 : Surreal) ∨
      y = (d : Surreal) - ω^ (-1 : Surreal) := by
  rcases lt_trichotomy (y - (d : Surreal)) 0 with h | h | h
  · -- mirror: apply the positive case to `-y` and `-d`
    refine .inr (.inr ?_)
    have hinf' : Infinitesimal (-y - ((-d : Dyadic) : Surreal)) := by
      rw [dyadic_cast_neg]
      have : -y - -(d : Surreal) = -(y - (d : Surreal)) := by ring
      rw [this]
      exact hinf.neg
    have hpos' : 0 < -y - ((-d : Dyadic) : Surreal) := by
      rw [dyadic_cast_neg]
      linarith
    have hb' : (-y).birthday ≤ NatOrdinal.of Ordinal.omega0 := by
      rwa [birthday_neg]
    have h1 := eq_dyadic_add_wpow_neg_one_of_birthday_le hinf' hpos' hb'
    rw [dyadic_cast_neg] at h1
    linarith
  · refine .inl ?_
    linarith
  · exact .inr (.inl (eq_dyadic_add_wpow_neg_one_of_birthday_le hinf h hb))

/-! ### The complete day-`ω` census -/

/-- **Conway's day-`ω` census, machine-checked**: a surreal is born by day `ω` if and
only if it is a real number, `±ω`, or a dyadic neighbour `d ± ω⁻¹`. (ONAG ch. 2's
description of the numbers created on day `ω`, as a single kernel-checked `iff`.
The infinite branch is `Infinity.Identification`'s day-`ω` classification; the finite
branches are the standard-part case analyses of this file.) -/
theorem birthday_le_omega0_iff {y : Surreal} :
    y.birthday ≤ NatOrdinal.of Ordinal.omega0 ↔
      (∃ r : ℝ, y = (r : Surreal)) ∨ y = ω^ (1 : Surreal) ∨ y = -ω^ (1 : Surreal) ∨
        ∃ d : Dyadic, y = (d : Surreal) + ω^ (-1 : Surreal) ∨
          y = (d : Surreal) - ω^ (-1 : Surreal) := by
  constructor
  · intro hb
    by_cases hy : IsFinite y
    · by_cases hd : ∃ d : Dyadic, stdPart y = ((d : ℚ) : ℝ)
      · obtain ⟨d, hdst⟩ := hd
        have hinf : Infinitesimal (y - (d : Surreal)) := by
          have h := infinitesimal_sub_stdPart hy
          rwa [hdst, Real.toSurreal_ratCast] at h
        rcases day_omega_near_dyadic hinf hb with h | h | h
        · exact .inl ⟨((d : ℚ) : ℝ), by rw [h, Real.toSurreal_ratCast]⟩
        · exact .inr (.inr (.inr ⟨d, .inl h⟩))
        · exact .inr (.inr (.inr ⟨d, .inr h⟩))
      · push Not at hd
        exact .inl ⟨stdPart y, eq_realCast_stdPart_of_isFinite_of_birthday_le hy hd hb⟩
    · rcases eq_wpow_one_or_eq_neg_of_not_isFinite_of_birthday_le hy hb with h | h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
  · rintro (⟨r, rfl⟩ | rfl | rfl | ⟨d, rfl | rfl⟩)
    · exact birthday_realCast_le r
    · exact le_of_eq birthday_wpow_one
    · rw [birthday_neg]
      exact le_of_eq birthday_wpow_one
    · exact birthday_dyadic_add_wpow_neg_one_le d
    · exact birthday_dyadic_sub_wpow_neg_one_le d

/-! ### The exponential corollaries: the day-`ω` criterion for the functional
equation, settled -/

private theorem one_dyadic_cast : ((1 : Dyadic) : Surreal) = 1 := by
  show (((1 : Dyadic) : ℚ) : Surreal) = 1
  norm_num

/-- The day-`ω` classification near `1`. -/
theorem day_omega_near_one {y : Surreal} (hinf : Infinitesimal (y - 1))
    (hb : y.birthday ≤ NatOrdinal.of Ordinal.omega0) :
    y = 1 ∨ y = 1 + ω^ (-1 : Surreal) ∨ y = 1 - ω^ (-1 : Surreal) := by
  have h := day_omega_near_dyadic (d := 1) (by rwa [one_dyadic_cast]) hb
  rwa [one_dyadic_cast] at h

/-- The exponential of a positive infinitesimal exceeds `1` (quantitatively: it is
`1 + ε + O(ε²)` with `ε > 0`). -/
theorem one_lt_expInf {ε : Surreal} (hε : Infinitesimal ε) (hε0 : 0 < ε) :
    1 < expInf ε hε hε0.ne' := by
  rw [← expInf'_of_ne hε hε0.ne']
  have h := abs_expInf'_sub_one_sub_le hε
  have h1 : expInf' ε - 1 - ε ≥ -(3 / 2 * ε ^ 2) := by
    have := (abs_le.1 h).1
    linarith
  have h2 : (2 : ℕ) • |ε| < 1 := infinitesimal_iff.1 hε 2
  rw [nsmul_eq_mul, abs_of_pos hε0] at h2
  push_cast at h2
  have hp : (2 : Surreal) * ε ^ 2 < ε := by nlinarith [h2, hε0]
  linarith

/-- Infinitesimal closeness to `1` for `expInf`. -/
theorem infinitesimal_expInf_sub_one {ε : Surreal} (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    Infinitesimal (expInf ε hε hε0 - 1) := by
  have h := infinitesimal_sub_stdPart (x := expInf ε hε hε0) ?_
  · rwa [stdPart_expInf hε hε0, Real.toSurreal_one] at h
  · rw [← expInf'_of_ne hε hε0]
    exact isFinite_expInf' hε

/-- **The day-`ω` criterion for the exponential functional equation, settled**: for
positive infinitesimals `ε, δ`, the product `expInf ε · expInf δ` is born by day `ω`
**iff** it equals `1 + ω⁻¹` on the nose. (The criterion of
`Infinity.Identification.expInf_add_eq_mul_of_birthday_le` therefore fires exactly on
the fibre of Gonshor's `exp` over `1 + ω⁻¹` — by the census, no other value born by
day `ω` is available to a product of exponentials.) -/
theorem birthday_expInf_mul_le_iff {ε δ : Surreal}
    (hε : Infinitesimal ε) (hδ : Infinitesimal δ) (hε0 : 0 < ε) (hδ0 : 0 < δ) :
    (expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne').birthday ≤ NatOrdinal.of Ordinal.omega0 ↔
      expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne' = 1 + ω^ (-1 : Surreal) := by
  constructor
  · intro hb
    have ha := infinitesimal_expInf_sub_one hε hε0.ne'
    have hbd := infinitesimal_expInf_sub_one hδ hδ0.ne'
    have hP : Infinitesimal (expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne' - 1) := by
      have hsplit : expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne' - 1 =
          (expInf ε hε hε0.ne' - 1) + (expInf δ hδ hδ0.ne' - 1) +
            (expInf ε hε hε0.ne' - 1) * (expInf δ hδ hδ0.ne' - 1) := by ring
      rw [hsplit]
      exact (ha.add hbd).add (ha.mul_isFinite hbd.isFinite)
    have h1ε := one_lt_expInf hε hε0
    have h1δ := one_lt_expInf hδ hδ0
    have h1P : 1 < expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne' := by nlinarith
    rcases day_omega_near_one hP hb with h | h | h
    · rw [h] at h1P
      exact absurd h1P (lt_irrefl 1)
    · exact h
    · rw [h] at h1P
      have := wpow_pos (-1 : Surreal)
      linarith
  · intro h
    rw [h]
    have hb := birthday_dyadic_add_wpow_neg_one_le 1
    rwa [one_dyadic_cast] at hb

/-- If a product of exponentials hits `1 + ω⁻¹` exactly, the functional equation holds
at that pair — the (unique possible) day-`ω` instance of Gonshor's
`exp (ε + δ) = exp ε · exp δ` for the canonical-sum exponential. -/
theorem expInf_add_eq_mul_of_eq_one_add {ε δ : Surreal}
    (hε : Infinitesimal ε) (hδ : Infinitesimal δ) (hε0 : 0 < ε) (hδ0 : 0 < δ)
    (h : expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne' = 1 + ω^ (-1 : Surreal)) :
    expInf (ε + δ) (hε.add hδ) (by positivity) =
      expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne' :=
  expInf_add_eq_mul_of_birthday_le hε hδ hε0 hδ0
    ((birthday_expInf_mul_le_iff hε hδ hε0 hδ0).2 h)

/-! ### The census as an engine: the geometric halo is empty at day `ω` -/

private theorem wpow_neg_one_eq_eps0 : ω^ (-1 : Surreal) = eps0 := by
  rw [eps0_def, show (-1 : Surreal) = -(1 : Surreal) from rfl, wpow_neg]

private theorem eps0_infinitesimal : Infinitesimal eps0 := by
  rw [eps0_def]
  exact infinitesimal_inv_wpow one_pos

private theorem eps0_pos : (0 : Surreal.{0}) < eps0 := by
  rw [eps0_def]
  exact inv_pos.2 (wpow_pos _)

private theorem partialSum_geom_one : partialSum (fun k ↦ eps0 ^ k) 1 = 1 := by
  rw [partialSum, Finset.sum_range_one, pow_zero]

private theorem partialSum_geom_two : partialSum (fun k ↦ eps0 ^ k) 2 = 1 + eps0 := by
  rw [partialSum, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]

private theorem partialSum_geom_three :
    partialSum (fun k ↦ eps0 ^ k) 3 = 1 + eps0 + eps0 ^ 2 := by
  rw [partialSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    pow_zero, pow_one]

/-- **Every Hahn sum of the geometric series is born at or after day `ω + 1`**: by the
census, the only day-`ω` surreals infinitesimally close to `1` are `1` and `1 ± ω⁻¹`,
and none of them satisfies the domination equations of `Σ ω⁻ᵏ` (each fails at the
residual of stage `2` or `3`). This strengthens
`omega0_le_birthday_of_isHahnSum_geometric` and takes the first transfinite step toward
the halo-minimality conjecture (`hahnSum_geometric_eq_of_halo_minimal`'s hypothesis):
the halo of `ω/(ω−1)` is provably empty at day `ω`. -/
theorem omega0_add_one_le_birthday_of_isHahnSum_geometric {w : Surreal}
    (hw : IsHahnSum (fun k ↦ eps0 ^ k) w) :
    NatOrdinal.of Ordinal.omega0 + 1 ≤ w.birthday := by
  have hωle := omega0_le_birthday_of_isHahnSum_geometric hw
  refine Order.add_one_le_of_lt (hωle.lt_of_ne ?_)
  intro heq
  -- `w` is infinitesimally close to `1`
  have hinf : Infinitesimal (w - 1) := by
    have h1 := hw 1
    rw [partialSum_geom_one] at h1
    simp only [pow_one] at h1
    exact lt_of_lt_of_le eps0_infinitesimal h1
  -- census: `w ∈ {1, 1 ± ω⁻¹}`
  rcases day_omega_near_one hinf heq.ge with h | h | h
  · -- `1` fails the stage-2 residual
    have h2 := hw 2
    rw [partialSum_geom_two, h] at h2
    have hval : (1 : Surreal) - (1 + eps0) = -eps0 := by ring
    rw [hval, ArchimedeanClass.mk_neg] at h2
    have hlt : ArchimedeanClass.mk (eps0 ^ 1) < ArchimedeanClass.mk (eps0 ^ 2) :=
      mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos 1
    rw [pow_one] at hlt
    exact absurd h2 (not_le.2 hlt)
  · -- `1 + ω⁻¹` fails the stage-3 residual
    have h3 := hw 3
    rw [partialSum_geom_three, h, wpow_neg_one_eq_eps0] at h3
    have hval : 1 + eps0 - (1 + eps0 + eps0 ^ 2) = -(eps0 ^ 2) := by ring
    rw [hval, ArchimedeanClass.mk_neg] at h3
    have hlt : ArchimedeanClass.mk (eps0 ^ 2) < ArchimedeanClass.mk (eps0 ^ 3) :=
      mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos 2
    exact absurd h3 (not_le.2 hlt)
  · -- `1 − ω⁻¹` fails the stage-2 residual
    have h2 := hw 2
    rw [partialSum_geom_two, h, wpow_neg_one_eq_eps0] at h2
    have hval : 1 - eps0 - (1 + eps0) = -(((2 : ℕ) : Surreal) * eps0) := by
      push_cast
      ring
    rw [hval, ArchimedeanClass.mk_neg] at h2
    have hmk : ArchimedeanClass.mk (((2 : ℕ) : Surreal) * eps0) = ArchimedeanClass.mk eps0 := by
      rw [ArchimedeanClass.mk_mul]
      have h20 : ArchimedeanClass.mk (((2 : ℕ) : Surreal)) = 0 := by
        rw [← Real.toSurreal_natCast]
        exact mk_realCast (by norm_num)
      rw [h20, zero_add]
    rw [hmk] at h2
    have hlt : ArchimedeanClass.mk (eps0 ^ 1) < ArchimedeanClass.mk (eps0 ^ 2) :=
      mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos 1
    rw [pow_one] at hlt
    exact absurd h2 (not_le.2 hlt)

/-- The canonical geometric sum is born at or after day `ω + 1`. -/
theorem omega0_add_one_le_birthday_hahnSum_geometric :
    NatOrdinal.of Ordinal.omega0 + 1 ≤ (hahnSum geometric_strict_dominating).birthday :=
  omega0_add_one_le_birthday_of_isHahnSum_geometric
    (isHahnSum_hahnSum geometric_strict_dominating)

end Surreal

end
