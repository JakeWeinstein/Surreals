/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.TubeCensus
import Infinity.SeriesLimits

/-!
# The uniform `ω²`-hardness of monomial summation

`Infinity.GeometricClose` proved that every Hahn sum of the geometric series is born at
or after day `ω²`. This file generalizes the tube census from the geometric series to
**every strictly dominating `ω`-power series with dyadic coefficients**
`Σ_{k<ω} cₖ·ω⁻ᵏ` (`cₖ` nonzero dyadics): around *any* Hahn sum `w` of such a series,
the tube census holds with the series' own partial sums `Tₘ = Σ_{k<m} cₖ ω⁻ᵏ` as the
moving anchors, and hence

* `mono_omega_sq_le_birthday_of_isHahnSum` — **the `ω²`-hardness theorem**: every Hahn
  sum of every such series is born at or after day `ω·ω`. Summing a monomial series is
  never cheap: the canonical sum — and every other consistent sum — costs at least `ω²`
  days, uniformly in the coefficients.

The ingredients mirror `Infinity.TubeCensus`, with two simplifications discovered in
the generalization: the tail calculus needs no closed form (one residual peel
`w − Tₘ = cₘ ω⁻ᵐ + (w − Tₘ₊₁)` plus `IsHahnSum.mk_sub_partialSum` replaces the
geometric identity), and the excluded grid coefficient at level `B` is simply `c_B`.
The level pack handles arbitrary nonzero dyadic coefficients by a four-way case split
(non-integer via the non-integer core, positive integers via the integer core,
negative coefficients by anchor negation).
-/

open ArchimedeanClass IGame Set

noncomputable section

namespace Surreal

local notation "ε₀" => eps0
local notation "Ω" => NatOrdinal.of Ordinal.omega0

variable {c : ℕ → Dyadic}

/-! ### The series, its partial sums, and the residual calculus -/

/-- The monomial series `k ↦ cₖ·ω⁻ᵏ`. -/
def monoTerm (c : ℕ → Dyadic) (k : ℕ) : Surreal.{0} :=
  (c k : Surreal) * ε₀ ^ k

/-- The partial sums `Tₘ = Σ_{k<m} cₖ·ω⁻ᵏ`. -/
def monoS (c : ℕ → Dyadic) (m : ℕ) : Surreal.{0} :=
  partialSum (monoTerm c) m

theorem monoS_zero : monoS c 0 = 0 :=
  partialSum_zero _

theorem monoS_succ (m : ℕ) :
    monoS c (m + 1) = monoS c m + (c m : Surreal) * ε₀ ^ m :=
  partialSum_succ _ m

theorem mk_monoTerm (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    ArchimedeanClass.mk (monoTerm c k) = ArchimedeanClass.mk (ε₀ ^ k) := by
  rw [monoTerm, ArchimedeanClass.mk_mul, mk_dyadic_cast_ne_zero (hc k), zero_add]

/-- Dyadic-coefficient monomial series are strictly dominating. -/
theorem monoTerm_strict_dominating (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    ArchimedeanClass.mk (monoTerm c k) < ArchimedeanClass.mk (monoTerm c (k + 1)) := by
  rw [mk_monoTerm hc, mk_monoTerm hc]
  exact mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos k

/-- The exact residual class of any Hahn sum of the series. -/
theorem mk_sub_monoS (hc : ∀ k, c k ≠ 0) {w : Surreal.{0}}
    (hw : IsHahnSum (monoTerm c) w) (m : ℕ) :
    ArchimedeanClass.mk (w - monoS c m) = ArchimedeanClass.mk (ε₀ ^ m) := by
  rw [show ArchimedeanClass.mk (w - monoS c m)
      = ArchimedeanClass.mk (w - partialSum (monoTerm c) m) from rfl,
    IsHahnSum.mk_sub_partialSum (monoTerm_strict_dominating hc) hw m, mk_monoTerm hc]

/-- The distance class of a level-`(B+1)` grid point with coefficient `t ≠ c (B+1)`
from any Hahn sum `w` is exactly the grid scale. -/
theorem mk_mono_grid_sub (hc : ∀ k, c k ≠ 0) {w : Surreal.{0}}
    (hw : IsHahnSum (monoTerm c) w) (B : ℕ) {t : Dyadic} (ht : t ≠ c (B + 1)) :
    ArchimedeanClass.mk (monoS c (B + 1) + (t : Surreal) * ε₀ ^ (B + 1) - w)
      = ArchimedeanClass.mk (ε₀ ^ (B + 1)) := by
  have hpeel : monoS c (B + 1) + (t : Surreal) * ε₀ ^ (B + 1) - w
      = ((t - c (B + 1) : Dyadic) : Surreal) * ε₀ ^ (B + 1) + (-(w - monoS c (B + 2))) := by
    rw [dyadic_cast_sub', monoS_succ (B + 1)]
    ring
  rw [hpeel, ArchimedeanClass.mk_add_eq_mk_left ?_]
  · rw [ArchimedeanClass.mk_mul, mk_dyadic_cast_ne_zero (sub_ne_zero.2 ht), zero_add]
  · rw [ArchimedeanClass.mk_mul, mk_dyadic_cast_ne_zero (sub_ne_zero.2 ht), zero_add,
      ArchimedeanClass.mk_neg, mk_sub_monoS hc hw (B + 2)]
    exact (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos (B + 1))

/-- The distance class of the partial sum `Tₘ` from any Hahn sum. -/
theorem mk_monoS_sub (hc : ∀ k, c k ≠ 0) {w : Surreal.{0}}
    (hw : IsHahnSum (monoTerm c) w) (m : ℕ) :
    ArchimedeanClass.mk (monoS c m - w) = ArchimedeanClass.mk (ε₀ ^ m) := by
  rw [show monoS c m - w = -(w - monoS c m) from by ring, ArchimedeanClass.mk_neg]
  exact mk_sub_monoS hc hw m

/-- Every Hahn sum of the series is strictly finer than every scale from any other Hahn
sum (micro-halo membership, strict at every level). -/
theorem mk_pow_lt_mk_sub_of_isHahnSum_mono (hc : ∀ k, c k ≠ 0) {w w' : Surreal.{0}}
    (hw : IsHahnSum (monoTerm c) w) (hw' : IsHahnSum (monoTerm c) w') (n : ℕ) :
    ArchimedeanClass.mk (ε₀ ^ n) < ArchimedeanClass.mk (w - w') := by
  have h1 := IsHahnSum.mk_sub_le hw hw' (n + 1)
  rw [mk_monoTerm hc] at h1
  exact (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos n).trans_le h1

/-! ### Choice games and one more separation helper -/

/-- A choice of numeric game realizing a given surreal, of minimal birthday. -/
private def gameOf (x : Surreal.{0}) : IGame.{0} :=
  (birthday_eq_iGameBirthday x).choose

private theorem gameOf_numeric (x : Surreal.{0}) : (gameOf x).Numeric :=
  (birthday_eq_iGameBirthday x).choose_spec.choose

private theorem mk_gameOf (x : Surreal.{0}) :
    @Surreal.mk (gameOf x) (gameOf_numeric x) = x :=
  (birthday_eq_iGameBirthday x).choose_spec.choose_spec.1

/-- A two-sided cut with singleton right move `{X}` inherits right separation from a
single value inequality. -/
theorem rightSepV_of_singleton {X G : IGame.{0}} [IGame.Numeric G] [IGame.Numeric X]
    {v : Surreal.{0}} (hmoves : Gᴿ = {X}) {q : Dyadic} (hq : 0 < q)
    (h : Surreal.mk G + (q : Surreal) * v ≤ Surreal.mk X) : RightSepV G v := by
  intro j hj
  have hj2 := hj
  rw [hmoves, Set.mem_singleton_iff] at hj2
  refine ⟨q, hq, ?_⟩
  have heq : @Surreal.mk j (IGame.Numeric.of_mem_moves hj) = Surreal.mk X := by
    subst hj2
    rfl
  rw [heq]
  exact h

/-! ### The anchor step: realizing `T_{B+2}` with separations, for any coefficient -/

/-- **The anchor step**: given a separated anchor for `T_{B+1}`, there is a separated
anchor for `T_{B+2} = T_{B+1} + c_{B+1}·ω^{−(B+1)}`, for an arbitrary nonzero dyadic
coefficient — non-integer coefficients (any sign) via the non-integer core, positive
integers via the integer core, negative integers by negating the anchor. -/
private theorem mono_anchor_step (hc : ∀ k, c k ≠ 0) (B : ℕ)
    {X : IGame.{0}} [hXn : X.Numeric] (hmkX : Surreal.mk X = monoS c (B + 1))
    (hL : LeftSepV X (ε₀ ^ B)) (hR : RightSepV X (ε₀ ^ B)) :
    ∃ (X' : IGame.{0}) (hX'n : X'.Numeric),
      @Surreal.mk X' hX'n = monoS c (B + 2) ∧
      @LeftSepV X' hX'n (ε₀ ^ (B + 1)) ∧ @RightSepV X' hX'n (ε₀ ^ (B + 1)) := by
  classical
  by_cases hden : (c (B + 1)).den = 1
  · -- integer coefficient
    have hnum : (c (B + 1)).num ≠ 0 := by
      intro h0
      apply hc (B + 1)
      rw [Dyadic.eq_intCast_of_den_eq_one hden, h0]
      push_cast
      rfl
    rcases lt_or_gt_of_ne hnum with hneg | hpos
    · -- negative integer: negate the anchor
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (c (B + 1)).num = -(((k + 1 : ℕ) : ℤ)) :=
        ⟨(-(c (B + 1)).num).toNat - 1, by omega⟩
      have hreq : c (B + 1) = -(((k + 1 : ℕ)) : Dyadic) := by
        rw [Dyadic.eq_intCast_of_den_eq_one hden, hk]
        push_cast
        ring
      haveI : IGame.Numeric (-X) := hXn.neg
      have hmkNX : Surreal.mk (-X) = -(monoS c (B + 1)) := by
        rw [Surreal.mk_neg, hmkX]
      set vK : Surreal.{0} := -(monoS c (B + 1)) + ((k : ℕ) : Surreal) * ε₀ ^ (B + 1)
        with hvK
      haveI := gameOf_numeric vK
      have hgL : Surreal.mk (gameOf vK)
          = Surreal.mk (-X) + ((k : ℕ) : Surreal) * ε₀ ^ (B + 1) := by
        rw [mk_gameOf, hmkNX]
      set gRf : Dyadic → IGame.{0} :=
        fun q ↦ gameOf (-(monoS c (B + 1)) + (q : Surreal) * ε₀ ^ B) with hgRf
      have hgRn : ∀ q : Dyadic, 0 < q → (gRf q).Numeric := fun q _ ↦ gameOf_numeric _
      have hgR : ∀ q (hq : 0 < q), @Surreal.mk (gRf q) (hgRn q hq)
          = Surreal.mk (-X) + (q : Surreal) * ε₀ ^ B := by
        intro q hq
        rw [hmkNX]
        exact mk_gameOf _
      have hequiv := add_natCast_succ_mul_scale_equiv
        (leftMoves_wpow_neg_natCast (B + 1)) (rightMoves_wpow_neg_natCast_succ B)
        (mk_Wg (B + 1)) (mk_Wg B) (eps0_pow_pos (B + 1)) (sep_eps0 B)
        (x := -X) k (gR := gRf) hgRn hgL hgR hR.neg hL.neg
      have hYn : IGame.Numeric (!{{gameOf vK} | gRf '' Set.Ioi 0} : IGame.{0}) := by
        refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
        · rw [leftMoves_ofSets, Set.mem_singleton_iff] at hy
          rw [rightMoves_ofSets] at hz
          obtain ⟨q, hq, rfl⟩ := hz
          subst hy
          haveI := hgRn q hq
          rw [← Surreal.mk_lt_mk, hgL, hgR q hq]
          have h1 : ((k : ℕ) : Surreal) * ε₀ ^ (B + 1) < (q : Surreal) * ε₀ ^ B := by
            have h := sep_eps0 B ((k : ℕ) : Dyadic) hq
            rwa [dyadic_cast_natCast] at h
          linarith
        · cases p with
          | left =>
            rw [moves_ofSets, Set.mem_singleton_iff] at hy
            subst hy
            infer_instance
          | right =>
            rw [moves_ofSets] at hy
            obtain ⟨q, hq, rfl⟩ := hy
            exact hgRn q hq
      have hmkY : @Surreal.mk _ hYn = -(monoS c (B + 2)) := by
        have h1 : Surreal.mk (-X + (((k + 1 : ℕ)) : IGame)
            * ω^ (-(((B + 1) : ℕ) : IGame.{0}))) = -(monoS c (B + 2)) := by
          rw [Surreal.mk_add, Surreal.mk_mul, Surreal.mk_natCast, mk_Wg, hmkNX,
            monoS_succ (B + 1), hreq, dyadic_cast_neg', dyadic_cast_natCast]
          push_cast
          ring
        rw [← h1]
        exact (Surreal.mk_eq hequiv).symm
      haveI := hYn
      have hYL : @LeftSepV _ hYn (ε₀ ^ (B + 1)) := by
        refine leftSepV_of_singleton (leftMoves_ofSets ..) one_pos_dyadic ?_
        have h : Surreal.mk (gameOf vK) + ((1 : Dyadic) : Surreal) * ε₀ ^ (B + 1)
            = -(monoS c (B + 2)) := by
          rw [mk_gameOf, hvK, dyadic_cast_one, one_mul, monoS_succ (B + 1), hreq,
            dyadic_cast_neg', dyadic_cast_natCast]
          push_cast
          ring
        exact le_of_eq (h.trans (show -(monoS c (B + 2)) = Surreal.mk _ from hmkY.symm))
      have hYR : @RightSepV _ hYn (ε₀ ^ (B + 1)) := by
        refine rightSepV_of_family (rightMoves_ofSets ..) ?_
        intro q hq hn
        refine ⟨1, one_pos_dyadic, ?_⟩
        have hval : @Surreal.mk (gRf q) hn
            = -(monoS c (B + 1)) + (q : Surreal) * ε₀ ^ B := mk_gameOf _
        rw [hval, show Surreal.mk (!{{gameOf vK} | gRf '' Set.Ioi 0} : IGame.{0})
          = -(monoS c (B + 2)) from hmkY, dyadic_cast_one, one_mul,
          monoS_succ (B + 1), hreq, dyadic_cast_neg', dyadic_cast_natCast]
        have hsep2 := sep_eps0 B ((k + 2 : ℕ) : Dyadic) hq
        rw [dyadic_cast_natCast] at hsep2
        push_cast at hsep2 ⊢
        linarith
      refine ⟨-(!{{gameOf vK} | gRf '' Set.Ioi 0} : IGame.{0}), hYn.neg, ?_, ?_, ?_⟩
      · rw [Surreal.mk_neg, show Surreal.mk (!{{gameOf vK} | gRf '' Set.Ioi 0} : IGame.{0})
          = -(monoS c (B + 2)) from hmkY, neg_neg]
      · exact hYR.neg
      · exact hYL.neg
    · -- positive integer: the integer core over the anchor itself
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (c (B + 1)).num = ((k + 1 : ℕ) : ℤ) :=
        ⟨(c (B + 1)).num.toNat - 1, by omega⟩
      have hreq : c (B + 1) = (((k + 1 : ℕ)) : Dyadic) := by
        rw [Dyadic.eq_intCast_of_den_eq_one hden, hk]
        push_cast
        rfl
      set vK : Surreal.{0} := monoS c (B + 1) + ((k : ℕ) : Surreal) * ε₀ ^ (B + 1)
        with hvK
      haveI := gameOf_numeric vK
      have hgL : Surreal.mk (gameOf vK)
          = Surreal.mk X + ((k : ℕ) : Surreal) * ε₀ ^ (B + 1) := by
        rw [mk_gameOf, hmkX]
      set gRf : Dyadic → IGame.{0} :=
        fun q ↦ gameOf (monoS c (B + 1) + (q : Surreal) * ε₀ ^ B) with hgRf
      have hgRn : ∀ q : Dyadic, 0 < q → (gRf q).Numeric := fun q _ ↦ gameOf_numeric _
      have hgR : ∀ q (hq : 0 < q), @Surreal.mk (gRf q) (hgRn q hq)
          = Surreal.mk X + (q : Surreal) * ε₀ ^ B := by
        intro q hq
        rw [hmkX]
        exact mk_gameOf _
      have hequiv := add_natCast_succ_mul_scale_equiv
        (leftMoves_wpow_neg_natCast (B + 1)) (rightMoves_wpow_neg_natCast_succ B)
        (mk_Wg (B + 1)) (mk_Wg B) (eps0_pow_pos (B + 1)) (sep_eps0 B)
        (x := X) k (gR := gRf) hgRn hgL hgR hL hR
      have hYn : IGame.Numeric (!{{gameOf vK} | gRf '' Set.Ioi 0} : IGame.{0}) := by
        refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
        · rw [leftMoves_ofSets, Set.mem_singleton_iff] at hy
          rw [rightMoves_ofSets] at hz
          obtain ⟨q, hq, rfl⟩ := hz
          subst hy
          haveI := hgRn q hq
          rw [← Surreal.mk_lt_mk, hgL, hgR q hq]
          have h1 : ((k : ℕ) : Surreal) * ε₀ ^ (B + 1) < (q : Surreal) * ε₀ ^ B := by
            have h := sep_eps0 B ((k : ℕ) : Dyadic) hq
            rwa [dyadic_cast_natCast] at h
          linarith
        · cases p with
          | left =>
            rw [moves_ofSets, Set.mem_singleton_iff] at hy
            subst hy
            infer_instance
          | right =>
            rw [moves_ofSets] at hy
            obtain ⟨q, hq, rfl⟩ := hy
            exact hgRn q hq
      have hmkY : @Surreal.mk _ hYn = monoS c (B + 2) := by
        have h1 : Surreal.mk (X + (((k + 1 : ℕ)) : IGame)
            * ω^ (-(((B + 1) : ℕ) : IGame.{0}))) = monoS c (B + 2) := by
          rw [Surreal.mk_add, Surreal.mk_mul, Surreal.mk_natCast, mk_Wg, hmkX,
            monoS_succ (B + 1), hreq, dyadic_cast_natCast]
        rw [← h1]
        exact (Surreal.mk_eq hequiv).symm
      haveI := hYn
      refine ⟨_, hYn, hmkY, ?_, ?_⟩
      · refine leftSepV_of_singleton (leftMoves_ofSets ..) one_pos_dyadic ?_
        have h : Surreal.mk (gameOf vK) + ((1 : Dyadic) : Surreal) * ε₀ ^ (B + 1)
            = monoS c (B + 2) := by
          rw [mk_gameOf, hvK, dyadic_cast_one, one_mul, monoS_succ (B + 1), hreq,
            dyadic_cast_natCast]
          push_cast
          ring
        exact le_of_eq (h.trans (show monoS c (B + 2) = Surreal.mk _ from hmkY.symm))
      · refine rightSepV_of_family (rightMoves_ofSets ..) ?_
        intro q hq hn
        refine ⟨1, one_pos_dyadic, ?_⟩
        have hval : @Surreal.mk (gRf q) hn
            = monoS c (B + 1) + (q : Surreal) * ε₀ ^ B := mk_gameOf _
        rw [hval, show Surreal.mk (!{{gameOf vK} | gRf '' Set.Ioi 0} : IGame.{0})
          = monoS c (B + 2) from hmkY, dyadic_cast_one, one_mul,
          monoS_succ (B + 1), hreq, dyadic_cast_natCast]
        have hsep2 := sep_eps0 B ((k + 2 : ℕ) : Dyadic) hq
        rw [dyadic_cast_natCast] at hsep2
        push_cast at hsep2 ⊢
        linarith
  · -- the non-integer case, any sign: the two-sided parent cut
    set vL : Surreal.{0} := monoS c (B + 1)
      + ((c (B + 1)).lower : Surreal) * ε₀ ^ (B + 1) with hvL
    set vU : Surreal.{0} := monoS c (B + 1)
      + ((c (B + 1)).upper : Surreal) * ε₀ ^ (B + 1) with hvU
    haveI := gameOf_numeric vL
    haveI := gameOf_numeric vU
    have hgLv : Surreal.mk (gameOf vL)
        = Surreal.mk X + ((c (B + 1)).lower : Surreal) * ε₀ ^ (B + 1) := by
      rw [mk_gameOf, hmkX]
    have hgUv : Surreal.mk (gameOf vU)
        = Surreal.mk X + ((c (B + 1)).upper : Surreal) * ε₀ ^ (B + 1) := by
      rw [mk_gameOf, hmkX]
    have hequiv := add_dyadic_mul_scale_equiv_of_den_ne_one
      (leftMoves_wpow_neg_natCast (B + 1)) (rightMoves_wpow_neg_natCast_succ B)
      (mk_Wg (B + 1)) (mk_Wg B) (sep_eps0 B) (x := X) hden hgLv hgUv hL hR
    have hCn : IGame.Numeric (!{{gameOf vL} | {gameOf vU}} : IGame.{0}) := by
      refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
      · rw [leftMoves_ofSets, Set.mem_singleton_iff] at hy
        rw [rightMoves_ofSets, Set.mem_singleton_iff] at hz
        subst hy
        subst hz
        rw [← Surreal.mk_lt_mk, hgLv, hgUv]
        have h1 : ((c (B + 1)).lower : Surreal) * ε₀ ^ (B + 1)
            < ((c (B + 1)).upper : Surreal) * ε₀ ^ (B + 1) :=
          mul_lt_mul_of_pos_right (dyadic_cast_lt (Dyadic.lower_lt_upper _))
            (eps0_pow_pos (B + 1))
        linarith
      · cases p with
        | left =>
          rw [moves_ofSets, Set.mem_singleton_iff] at hy
          subst hy
          infer_instance
        | right =>
          rw [moves_ofSets, Set.mem_singleton_iff] at hy
          subst hy
          infer_instance
    have hmkC : @Surreal.mk _ hCn = monoS c (B + 2) := by
      have h1 : Surreal.mk (X + ((c (B + 1) : Dyadic) : IGame)
          * ω^ (-(((B + 1) : ℕ) : IGame.{0}))) = monoS c (B + 2) := by
        rw [Surreal.mk_add, Surreal.mk_mul, Surreal.mk_dyadic, mk_Wg, hmkX,
          monoS_succ (B + 1)]
      rw [← h1]
      exact (Surreal.mk_eq hequiv).symm
    haveI := hCn
    refine ⟨_, hCn, hmkC, ?_, ?_⟩
    · refine leftSepV_of_singleton (leftMoves_ofSets ..)
        (q := c (B + 1) - (c (B + 1)).lower) (sub_pos.2 (Dyadic.lower_lt _)) ?_
      have h : Surreal.mk (gameOf vL)
          + ((c (B + 1) - (c (B + 1)).lower : Dyadic) : Surreal) * ε₀ ^ (B + 1)
          = monoS c (B + 2) := by
        rw [mk_gameOf, hvL, dyadic_cast_sub', monoS_succ (B + 1)]
        ring
      exact le_of_eq (h.trans (show monoS c (B + 2) = Surreal.mk _ from hmkC.symm))
    · refine rightSepV_of_singleton (rightMoves_ofSets ..)
        (q := (c (B + 1)).upper - c (B + 1)) (sub_pos.2 (Dyadic.lt_upper _)) ?_
      have h : Surreal.mk (!{{gameOf vL} | {gameOf vU}} : IGame.{0})
          + (((c (B + 1)).upper - c (B + 1) : Dyadic) : Surreal) * ε₀ ^ (B + 1)
          = vU := by
        rw [show Surreal.mk (!{{gameOf vL} | {gameOf vU}} : IGame.{0})
          = monoS c (B + 2) from hmkC, hvU, dyadic_cast_sub', monoS_succ (B + 1)]
        ring
      rw [h]
      exact (mk_gameOf vU).ge

private theorem birthday_gameOf (x : Surreal.{0}) : (gameOf x).birthday = x.birthday :=
  (birthday_eq_iGameBirthday x).choose_spec.choose_spec.2

/-! ### The general level pack -/

/-- A uniform bound for all level-`(B+1)` grid birthdays plus one day, inside the next
block. -/
private theorem mono_translate_bound (B : ℕ)
    (hb1 : (monoS c (B + 1)).birthday + 1 ≤ Ω * (((B + 1) : ℕ) : NatOrdinal))
    (hRgrid : ∀ t : Dyadic, t ≠ 0 →
      (monoS c (B + 1) + (t : Surreal) * ε₀ ^ (B + 1)).birthday
        ≤ Ω * (((B + 1) : ℕ) : NatOrdinal) + ((Dyadic.hgt t - 1 : ℕ) : NatOrdinal))
    (q : Dyadic) :
    (monoS c (B + 1) + (q : Surreal) * ε₀ ^ (B + 1)).birthday + 1
      ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) := by
  rcases eq_or_ne q 0 with rfl | hq
  · rw [dyadic_cast_zero, zero_mul, add_zero]
    refine hb1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    exact_mod_cast (by omega : B + 1 ≤ B + 2)
  · have h := hRgrid q hq
    have h1 := add_le_add h (le_refl 1)
    refine h1.trans ?_
    rw [base_add_nat_succ]
    have hgt1 : Dyadic.hgt q - 1 + 1 = Dyadic.hgt q := by
      have := Dyadic.hgt_pos_of_ne_zero hq
      omega
    rw [hgt1]
    exact omega_mul_add_nat_le_succ (B + 1) _

/-- **The general level pack**: for every strictly dominating dyadic-coefficient
monomial series and every `B`, an anchor game realizing the partial sum `T_{B+1}` with
separations at scale `ε₀^B`, the bound `birthday T_{B+1} < ω·(B+1)`, and the
level-`(B+1)` grid bound `birthday (T_{B+1} + t·ε₀^{B+1}) ≤ ω·(B+1) + (hgt t − 1)`. -/
theorem mono_anchor_pack (hc : ∀ k, c k ≠ 0) : ∀ B : ℕ, ∃ (X : IGame.{0}) (hXn : X.Numeric),
    @Surreal.mk X hXn = monoS c (B + 1) ∧
    (@LeftSepV X hXn (ε₀ ^ B) ∧ @RightSepV X hXn (ε₀ ^ B)) ∧
    (monoS c (B + 1)).birthday + 1 ≤ Ω * (((B + 1) : ℕ) : NatOrdinal) ∧
    (∀ t : Dyadic, t ≠ 0 →
      (monoS c (B + 1) + (t : Surreal) * ε₀ ^ (B + 1)).birthday
        ≤ Ω * (((B + 1) : ℕ) : NatOrdinal) + ((Dyadic.hgt t - 1 : ℕ) : NatOrdinal)) := by
  intro B
  have hT1 : monoS c 1 = ((c 0 : Dyadic) : Surreal) := by
    rw [monoS_succ 0, monoS_zero, zero_add, pow_zero, mul_one]
  induction B with
  | zero =>
    refine ⟨((c 0 : Dyadic) : IGame.{0}), inferInstance, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [Surreal.mk_dyadic, hT1]
    · rw [pow_zero]
      intro i hi
      obtain ⟨q, hq, hle⟩ := leftSep_dyadic (c 0) i hi
      exact ⟨q, hq, by rwa [mul_one]⟩
    · rw [pow_zero]
      intro j hj
      obtain ⟨q, hq, hle⟩ := rightSep_dyadic (c 0) j hj
      exact ⟨q, hq, by rwa [mul_one]⟩
    · rw [hT1, ← Surreal.mk_dyadic (c 0)]
      have h : ((c 0 : Dyadic) : IGame.{0}).birthday < Ω :=
        IGame.short_iff_birthday_finite.1 (IGame.Short.dyadic _)
      have h1 : Ω * (((0 + 1) : ℕ) : NatOrdinal) = Ω := by norm_num
      rw [h1]
      refine le_trans (add_le_add (birthday_mk_le _) (le_refl 1)) ?_
      rw [← Order.succ_eq_add_one]
      exact Order.succ_le_of_lt h
    · intro t ht
      have h := birthday_dyadic_add_dyadic_mul_wpow_le (c 0) ht
      rw [wpow_neg_one_eq_eps0] at h
      have h1 : Ω * (((0 + 1) : ℕ) : NatOrdinal) = Ω := by norm_num
      rw [hT1, pow_one, h1]
      exact h
  | succ B ih =>
    classical
    obtain ⟨X, hXn, hmkX, ⟨hL, hR⟩, hb1, hRgrid⟩ := ih
    haveI := hXn
    obtain ⟨X', hX'n, hmkX', hL', hR'⟩ := mono_anchor_step hc B hmkX hL hR
    haveI := hX'n
    -- the new partial-sum bound, from the level-(B+1) grid bound at `t = c (B+1)`
    have hb1' : (monoS c (B + 2)).birthday + 1 ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) := by
      have h := mono_translate_bound B hb1 hRgrid (c (B + 1))
      rwa [← monoS_succ (B + 1)] at h
    -- the new grid bound via the parametric engine
    have hRgrid' : ∀ t : Dyadic, t ≠ 0 →
        (monoS c (B + 2) + (t : Surreal) * ε₀ ^ (B + 2)).birthday
          ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) + ((Dyadic.hgt t - 1 : ℕ) : NatOrdinal) := by
      have hgames : ∀ q : Dyadic, 0 ≤ q → ∃ (g : IGame.{0}) (_ : g.Numeric),
          Surreal.mk g = Surreal.mk X' + (q : Surreal) * ε₀ ^ (B + 1) ∧
            g.birthday + 1
              ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) + ((0 : ℕ) : NatOrdinal) := by
        intro q hq
        refine ⟨gameOf (Surreal.mk X' + (q : Surreal) * ε₀ ^ (B + 1)), gameOf_numeric _,
          mk_gameOf _, ?_⟩
        rw [birthday_gameOf, show ((0 : ℕ) : NatOrdinal) = 0 from by exact_mod_cast rfl,
          add_zero, hmkX']
        have hval : monoS c (B + 2) + (q : Surreal) * ε₀ ^ (B + 1)
            = monoS c (B + 1) + ((c (B + 1) + q : Dyadic) : Surreal) * ε₀ ^ (B + 1) := by
          rw [monoS_succ (B + 1), dyadic_cast_add']
          ring
        rw [hval]
        exact mono_translate_bound B hb1 hRgrid _
      haveI : IGame.Numeric (-X') := hX'n.neg
      have hmkNX' : Surreal.mk (-X') = -(monoS c (B + 2)) := by
        rw [Surreal.mk_neg, show Surreal.mk X' = monoS c (B + 2) from hmkX']
      have hgamesN : ∀ q : Dyadic, 0 ≤ q → ∃ (g : IGame.{0}) (_ : g.Numeric),
          Surreal.mk g = Surreal.mk (-X') + (q : Surreal) * ε₀ ^ (B + 1) ∧
            g.birthday + 1
              ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) + ((0 : ℕ) : NatOrdinal) := by
        intro q hq
        refine ⟨gameOf (Surreal.mk (-X') + (q : Surreal) * ε₀ ^ (B + 1)),
          gameOf_numeric _, mk_gameOf _, ?_⟩
        rw [birthday_gameOf, show ((0 : ℕ) : NatOrdinal) = 0 from by exact_mod_cast rfl,
          add_zero, hmkNX']
        have hval : -(monoS c (B + 2)) + (q : Surreal) * ε₀ ^ (B + 1)
            = -(monoS c (B + 1) + ((c (B + 1) - q : Dyadic) : Surreal) * ε₀ ^ (B + 1)) := by
          rw [monoS_succ (B + 1), dyadic_cast_sub']
          ring
        rw [hval, birthday_neg]
        exact mono_translate_bound B hb1 hRgrid _
      intro t ht
      rcases lt_trichotomy t 0 with htn | ht0 | htp
      · have h := scale_grid_aux
          (leftMoves_wpow_neg_natCast (B + 2)) (rightMoves_wpow_neg_natCast_succ (B + 1))
          (mk_Wg (B + 2)) (mk_Wg (B + 1)) (eps0_pow_pos (B + 2)) (sep_eps0 (B + 1))
          (x := -X') hR'.neg hL'.neg
          (Ω * (((B + 2) : ℕ) : NatOrdinal)) 0 hgamesN
          (Dyadic.hgt (-t)) (-t) (by rwa [neg_pos]) le_rfl
        have hval2 : Surreal.mk (-X') + ((-t : Dyadic) : Surreal) * ε₀ ^ (B + 2)
            = -(monoS c (B + 2) + (t : Surreal) * ε₀ ^ (B + 2)) := by
          rw [hmkNX', dyadic_cast_neg']
          ring
        rw [hval2, birthday_neg, Dyadic.hgt_neg] at h
        exact h
      · exact absurd ht0 ht
      · have h := scale_grid_aux
          (leftMoves_wpow_neg_natCast (B + 2)) (rightMoves_wpow_neg_natCast_succ (B + 1))
          (mk_Wg (B + 2)) (mk_Wg (B + 1)) (eps0_pow_pos (B + 2)) (sep_eps0 (B + 1))
          (x := X') hL' hR'
          (Ω * (((B + 2) : ℕ) : NatOrdinal)) 0 hgames
          (Dyadic.hgt t) t htp le_rfl
        rw [show Surreal.mk X' = monoS c (B + 2) from hmkX'] at h
        exact h
    exact ⟨X', hX'n, hmkX', ⟨hL', hR'⟩, hb1', hRgrid'⟩

/-- The public grid bound along any monomial series. -/
theorem birthday_monoS_add_dyadic_mul_le (hc : ∀ k, c k ≠ 0) (B : ℕ) {t : Dyadic}
    (ht : t ≠ 0) :
    (monoS c (B + 1) + (t : Surreal) * ε₀ ^ (B + 1)).birthday
      ≤ Ω * (((B + 1) : ℕ) : NatOrdinal) + ((Dyadic.hgt t - 1 : ℕ) : NatOrdinal) := by
  obtain ⟨X, hXn, -, -, -, hRgrid⟩ := mono_anchor_pack hc B
  exact hRgrid t ht

/-- Every monomial partial sum is born strictly inside its block. -/
theorem birthday_monoS_add_one_le (hc : ∀ k, c k ≠ 0) (B : ℕ) :
    (monoS c (B + 1)).birthday + 1 ≤ Ω * (((B + 1) : ℕ) : NatOrdinal) := by
  obtain ⟨X, hXn, -, -, hb1, -⟩ := mono_anchor_pack hc B
  exact hb1

/-! ### The census core along a monomial series -/

/-- **The critical-day step of the monomial tube census**: as in
`Infinity.TubeCensus.tube_census_core`, with an arbitrary Hahn sum `w` of the series
as the tube center and the series' own partial sums as anchors. -/
private theorem mono_census_core (hc : ∀ k, c k ≠ 0) {w : Surreal.{0}}
    (hw : IsHahnSum (monoTerm c) w) (B N : ℕ) {u : Surreal.{0}}
    (hu : ArchimedeanClass.mk (ε₀ ^ (B + 1)) < ArchimedeanClass.mk (u - w))
    (hbeq : u.birthday = Ω * (((B + 2) : ℕ) : NatOrdinal) + (N : NatOrdinal))
    (horacle : ∀ v : Surreal.{0},
      v.birthday < Ω * (((B + 2) : ℕ) : NatOrdinal) + (N : NatOrdinal) →
      ArchimedeanClass.mk (ε₀ ^ (B + 1)) < ArchimedeanClass.mk (v - w) →
      ∃ s : Dyadic, v = monoS c (B + 2) + (s : Surreal) * ε₀ ^ (B + 2) ∧
        Dyadic.hgt s ≤ N) :
    ∃ t : Dyadic, u = monoS c (B + 2) + (t : Surreal) * ε₀ ^ (B + 2) ∧
      Dyadic.hgt t ≤ N + 1 := by
  classical
  obtain ⟨g, hgn, hgy, hgb⟩ := birthday_eq_iGameBirthday u
  haveI := hgn
  have hslt := Cut.supLeft_lt_infRight_of_numeric g
  have hopt : ∀ (p : Player) (i : IGame), i ∈ g.moves p → ∀ (hn : i.Numeric),
      (@Surreal.mk i hn).birthday
        < Ω * (((B + 2) : ℕ) : NatOrdinal) + (N : NatOrdinal) := by
    intro p i hi hn
    have h1 := IGame.birthday_lt_of_mem_moves hi
    rw [hgb, hbeq] at h1
    exact lt_of_le_of_lt (birthday_mk_le i) h1
  set S : Set Dyadic := {s | Dyadic.hgt s ≤ N ∧ ∃ i ∈ gᴸ, ∃ _ : i.Numeric,
    Surreal.mk i = monoS c (B + 2) + (s : Surreal) * ε₀ ^ (B + 2)} with hS
  set S' : Set Dyadic := {s | Dyadic.hgt s ≤ N ∧ ∃ j ∈ gᴿ, ∃ _ : j.Numeric,
    Surreal.mk j = monoS c (B + 2) + (s : Surreal) * ε₀ ^ (B + 2)} with hS'
  have hSfin : S.Finite := (Dyadic.finite_setOf_hgt_le N).subset (fun s hs ↦ hs.1)
  have hS'fin : S'.Finite := (Dyadic.finite_setOf_hgt_le N).subset (fun s hs ↦ hs.1)
  have hSS' : ∀ s ∈ S, ∀ s' ∈ S', s < s' := by
    rintro s ⟨_, i, hi, hin, hiv⟩ s' ⟨_, j, hj, hjn, hjv⟩
    haveI := hin
    haveI := hjn
    have h1 : Surreal.mk i < u := by
      rw [← hgy]
      exact mk_lt_mk.2 (IGame.Numeric.left_lt hi)
    have h2 : u < Surreal.mk j := by
      rw [← hgy]
      exact mk_lt_mk.2 (IGame.Numeric.lt_right hj)
    refine dyadic_lt_of_mul_eps_lt (m := B + 2) ?_
    rw [hiv] at h1
    rw [hjv] at h2
    linarith
  obtain ⟨t, htgt, htS, htS'⟩ : ∃ t : Dyadic, Dyadic.hgt t ≤ N + 1 ∧
      (∀ s ∈ S, s < t) ∧ (∀ s' ∈ S', t < s') := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · rcases S'.eq_empty_or_nonempty with hS'e | hS'ne
      · refine ⟨0, by simp, ?_, ?_⟩
        · intro s hs
          rw [hSe] at hs
          exact absurd hs (Set.notMem_empty s)
        · intro s hs
          rw [hS'e] at hs
          exact absurd hs (Set.notMem_empty s)
      · have hne : hS'fin.toFinset.Nonempty := by
          rwa [Set.Finite.toFinset_nonempty]
        set m := hS'fin.toFinset.min' hne with hm
        have hmS' : m ∈ S' := by
          rw [← Set.Finite.mem_toFinset hS'fin]
          exact hS'fin.toFinset.min'_mem hne
        obtain ⟨t, ht1, ht2⟩ := Dyadic.exists_hgt_below m
        refine ⟨t, by have := hmS'.1; omega, ?_, ?_⟩
        · intro s hs
          rw [hSe] at hs
          exact absurd hs (Set.notMem_empty s)
        · intro s' hs'
          refine ht1.trans_le ?_
          rw [hm]
          exact hS'fin.toFinset.min'_le s' ((Set.Finite.mem_toFinset hS'fin).2 hs')
    · rcases S'.eq_empty_or_nonempty with hS'e | hS'ne
      · have hne : hSfin.toFinset.Nonempty := by
          rwa [Set.Finite.toFinset_nonempty]
        set m := hSfin.toFinset.max' hne with hm
        have hmS : m ∈ S := by
          rw [← Set.Finite.mem_toFinset hSfin]
          exact hSfin.toFinset.max'_mem hne
        obtain ⟨t, ht1, ht2⟩ := Dyadic.exists_hgt_above m
        refine ⟨t, by have := hmS.1; omega, ?_, ?_⟩
        · intro s hs
          refine lt_of_le_of_lt ?_ ht1
          rw [hm]
          exact hSfin.toFinset.le_max' s ((Set.Finite.mem_toFinset hSfin).2 hs)
        · intro s' hs'
          rw [hS'e] at hs'
          exact absurd hs' (Set.notMem_empty s')
      · have hneS : hSfin.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
        have hneS' : hS'fin.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
        set mS := hSfin.toFinset.max' hneS with hmS
        set mS' := hS'fin.toFinset.min' hneS' with hmS'
        have hmSm : mS ∈ S := by
          rw [← Set.Finite.mem_toFinset hSfin]
          exact hSfin.toFinset.max'_mem hneS
        have hmS'm : mS' ∈ S' := by
          rw [← Set.Finite.mem_toFinset hS'fin]
          exact hS'fin.toFinset.min'_mem hneS'
        have hlt : mS < mS' := hSS' mS hmSm mS' hmS'm
        obtain ⟨t, ht1, ht2, ht3⟩ := Dyadic.exists_hgt_btwn mS mS' hlt
        refine ⟨t, ?_, ?_, ?_⟩
        · have h1 := hmSm.1
          have h2 := hmS'm.1
          omega
        · intro s hs
          refine lt_of_le_of_lt ?_ ht1
          rw [hmS]
          exact hSfin.toFinset.le_max' s ((Set.Finite.mem_toFinset hSfin).2 hs)
        · intro s' hs'
          refine ht2.trans_le ?_
          rw [hmS']
          exact hS'fin.toFinset.min'_le s' ((Set.Finite.mem_toFinset hS'fin).2 hs')
  set cnd : Surreal.{0} := monoS c (B + 2) + (t : Surreal) * ε₀ ^ (B + 2) with hcnd
  have hcb : cnd.birthday ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) + (N : NatOrdinal) := by
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [hcnd, dyadic_cast_zero, zero_mul, add_zero]
      have h := birthday_monoS_add_one_le hc (B + 1)
      refine le_trans (le_trans (le_add_of_nonneg_right zero_le_one) h) ?_
      exact le_add_of_nonneg_right bot_le
    · rw [hcnd]
      refine (birthday_monoS_add_dyadic_mul_le hc (B + 1) ht0).trans ?_
      refine add_le_add le_rfl (nat_cast_mono ?_)
      omega
  have hcv : ArchimedeanClass.mk (ε₀ ^ (B + 1)) < ArchimedeanClass.mk (cnd - w) := by
    by_cases ht1 : t = c (B + 2)
    · have hcs : cnd - w = monoS c (B + 3) - w := by
        rw [hcnd, ht1, ← monoS_succ (B + 2)]
      rw [hcs, mk_monoS_sub hc hw]
      exact (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos (B + 1)).trans
        (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos (B + 2))
    · rw [hcnd, mk_mono_grid_sub hc hw (B + 1) ht1]
      exact mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos (B + 1)
  have hfitc : Cut.Fits cnd (Cut.supLeft g) (Cut.infRight g) := by
    rw [Cut.Fits, Set.mem_inter_iff]
    constructor
    · rw [Cut.right_supLeft]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro i hi
      haveI : i.Numeric := IGame.Numeric.of_mem_moves hi
      have hiy : Surreal.mk i < u := by
        rw [← hgy]
        exact mk_lt_mk.2 (IGame.Numeric.left_lt hi)
      have hib := hopt _ i hi inferInstance
      have hlt : Surreal.mk i < cnd := by
        by_cases hitube : ArchimedeanClass.mk (ε₀ ^ (B + 1))
            < ArchimedeanClass.mk (Surreal.mk i - w)
        · obtain ⟨s, hsv, hshgt⟩ := horacle (Surreal.mk i) hib hitube
          have hst : s < t := htS s ⟨hshgt, i, hi, inferInstance, hsv⟩
          rw [hsv, hcnd]
          have := mul_lt_mul_of_pos_right (dyadic_cast_lt hst) (eps0_pow_pos (B + 2))
          linarith
        · rw [not_lt] at hitube
          have hmk_iu : ArchimedeanClass.mk (Surreal.mk i - u)
              = ArchimedeanClass.mk (Surreal.mk i - w) := by
            rw [show Surreal.mk i - u = (Surreal.mk i - w) + (w - u) from by ring,
              ArchimedeanClass.mk_add_eq_mk_left ?_]
            rw [show w - u = -(u - w) from by ring, ArchimedeanClass.mk_neg]
            exact lt_of_le_of_lt hitube hu
          have hmk_cu : ArchimedeanClass.mk (Surreal.mk i - u)
              < ArchimedeanClass.mk (cnd - u) := by
            rw [hmk_iu]
            refine lt_of_le_of_lt hitube ?_
            have hmin2 : ArchimedeanClass.mk (ε₀ ^ (B + 1))
                < min (ArchimedeanClass.mk (cnd - w)) (ArchimedeanClass.mk (w - u)) := by
              refine lt_min hcv ?_
              rw [show w - u = -(u - w) from by ring, ArchimedeanClass.mk_neg]
              exact hu
            refine lt_of_lt_of_le hmin2 ?_
            rw [show cnd - u = (cnd - w) + (w - u) from by ring]
            exact ArchimedeanClass.min_le_mk_add ..
          exact lt_of_lt_of_mk_sub_lt hiy hmk_cu
      rw [← toGame_mk, toGame_le_iff]
      exact not_le.2 hlt
    · rw [Cut.left_infRight]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro j hj
      haveI : j.Numeric := IGame.Numeric.of_mem_moves hj
      have hyj : u < Surreal.mk j := by
        rw [← hgy]
        exact mk_lt_mk.2 (IGame.Numeric.lt_right hj)
      have hjb := hopt _ j hj inferInstance
      have hlt : cnd < Surreal.mk j := by
        by_cases hjtube : ArchimedeanClass.mk (ε₀ ^ (B + 1))
            < ArchimedeanClass.mk (Surreal.mk j - w)
        · obtain ⟨s, hsv, hshgt⟩ := horacle (Surreal.mk j) hjb hjtube
          have hst : t < s := htS' s ⟨hshgt, j, hj, inferInstance, hsv⟩
          rw [hsv, hcnd]
          have := mul_lt_mul_of_pos_right (dyadic_cast_lt hst) (eps0_pow_pos (B + 2))
          linarith
        · rw [not_lt] at hjtube
          have hmk_ju : ArchimedeanClass.mk (Surreal.mk j - u)
              = ArchimedeanClass.mk (Surreal.mk j - w) := by
            rw [show Surreal.mk j - u = (Surreal.mk j - w) + (w - u) from by ring,
              ArchimedeanClass.mk_add_eq_mk_left ?_]
            rw [show w - u = -(u - w) from by ring, ArchimedeanClass.mk_neg]
            exact lt_of_le_of_lt hjtube hu
          have hmk_cu : ArchimedeanClass.mk (Surreal.mk j - u)
              < ArchimedeanClass.mk (cnd - u) := by
            rw [hmk_ju]
            refine lt_of_le_of_lt hjtube ?_
            have hmin2 : ArchimedeanClass.mk (ε₀ ^ (B + 1))
                < min (ArchimedeanClass.mk (cnd - w)) (ArchimedeanClass.mk (w - u)) := by
              refine lt_min hcv ?_
              rw [show w - u = -(u - w) from by ring, ArchimedeanClass.mk_neg]
              exact hu
            refine lt_of_lt_of_le hmin2 ?_
            rw [show cnd - u = (cnd - w) + (w - u) from by ring]
            exact ArchimedeanClass.min_le_mk_add ..
          exact lt_of_lt_of_mk_sub_lt' hyj hmk_cu
      rw [← toGame_mk, toGame_le_iff]
      exact not_le.2 hlt
  have hy' : Cut.simplestBtwn hslt = u := by
    rw [← toGame_inj, Cut.simplestBtwn_supLeft_infRight hslt, ← hgy, toGame_mk]
  have hfity : Cut.Fits u (Cut.supLeft g) (Cut.infRight g) :=
    hy' ▸ Cut.fits_simplestBtwn hslt
  have hmin : ∀ v, Cut.Fits v (Cut.supLeft g) (Cut.infRight g) →
      u.birthday ≤ v.birthday := by
    intro v hv
    have h := Cut.birthday_simplestBtwn_le_of_fits hv
    rwa [hy'] at h
  have hyc : u = cnd :=
    (Cut.eq_of_fits_of_birthday_le hfity hfitc hmin (hcb.trans_eq hbeq.symm)).symm
  exact ⟨t, by rw [hyc, hcnd], htgt⟩

/-! ### The monomial tube census -/

theorem monoS_one : monoS c 1 = ((c 0 : Dyadic) : Surreal) := by
  rw [monoS_succ 0, monoS_zero, zero_add, pow_zero, mul_one]

/-- **The monomial tube census**: around any Hahn sum `w` of a strictly dominating
dyadic-coefficient monomial series, a surreal born by day `ω·(B+1) + n` at distance of
class strictly finer than `mk (ω^{−B})` from `w` is a dyadic grid point
`T_{B+1} + t·ω^{−(B+1)}` over the series' own partial sums, with `hgt t ≤ n + 1`. -/
theorem mono_census (hc : ∀ k, c k ≠ 0) {w : Surreal.{0}}
    (hw : IsHahnSum (monoTerm c) w) : ∀ (B : ℕ) (n : ℕ) {u : Surreal.{0}},
    ArchimedeanClass.mk (ε₀ ^ B) < ArchimedeanClass.mk (u - w) →
    u.birthday ≤ Ω * (((B + 1) : ℕ) : NatOrdinal) + (n : NatOrdinal) →
    ∃ t : Dyadic, u = monoS c (B + 1) + (t : Surreal) * ε₀ ^ (B + 1) ∧
      Dyadic.hgt t ≤ n + 1 := by
  intro B
  induction B with
  | zero =>
    intro n u hu hb
    have hu0 : (0 : ArchimedeanClass Surreal.{0}) < ArchimedeanClass.mk (u - w) := by
      rw [pow_zero, mk_one_surreal] at hu
      exact hu
    have hinf : Infinitesimal (u - w) := infinitesimal_def.2 hu0
    have hw1 : Infinitesimal (w - monoS c 1) := by
      refine infinitesimal_def.2 ?_
      rw [mk_sub_monoS hc hw 1, pow_one]
      exact infinitesimal_def.1 eps0_infinitesimal
    have hcast : ((c 0 : Dyadic) : Surreal.{0}) = (((c 0 : ℚ) : ℝ) : Surreal) := by
      rw [← Real.toSurreal_ratCast]
    have h2 : u = ((c 0 : Dyadic) : Surreal.{0}) + ((w - monoS c 1) + (u - w)) := by
      rw [← monoS_one]
      ring
    have hsum : Infinitesimal ((w - monoS c 1) + (u - w)) := hw1.add hinf
    have hufin : IsFinite u := by
      rw [h2]
      exact (isFinite_dyadic_cast _).add hsum.isFinite
    have hst : stdPart u = ((c 0 : ℚ) : ℝ) := by
      rw [h2, stdPart_add_eq_left hsum, hcast, stdPart_realCast]
    have hb' : u.birthday ≤ Ω + (n : NatOrdinal) := by
      have h1 : Ω * (((0 + 1) : ℕ) : NatOrdinal) = Ω := by norm_num
      rwa [h1] at hb
    obtain ⟨r, hval, hh1, -⟩ := eq_grid_of_isFinite_of_birthday_le n hufin hb'
    rw [hst] at hval
    refine ⟨r, ?_, hh1⟩
    rw [monoS_one, hcast, pow_one, ← wpow_neg_one_eq_eps0]
    exact hval
  | succ B ihB =>
    have hlow : ∀ v : Surreal.{0}, v.birthday < Ω * (((B + 2) : ℕ) : NatOrdinal) →
        ArchimedeanClass.mk (ε₀ ^ (B + 1)) < ArchimedeanClass.mk (v - w) →
        v = monoS c (B + 2) := by
      intro v hvb hvt
      obtain ⟨m, hm⟩ := lt_omega_mul_succ_decomp (B + 1) hvb
      have hvt' : ArchimedeanClass.mk (ε₀ ^ B) < ArchimedeanClass.mk (v - w) :=
        (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos B).trans hvt
      obtain ⟨s, hsv, -⟩ := ihB m hvt' hm
      by_cases hs1 : s = c (B + 1)
      · rw [hsv, hs1, ← monoS_succ (B + 1)]
      · exfalso
        have hmk := mk_mono_grid_sub hc hw B hs1
        rw [← hsv] at hmk
        rw [hmk] at hvt
        exact lt_irrefl _ hvt
    intro n
    induction n with
    | zero =>
      intro u hu hb
      have hb0 : u.birthday ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) := by
        rwa [show ((0 : ℕ) : NatOrdinal) = 0 from by exact_mod_cast rfl, add_zero] at hb
      rcases lt_or_eq_of_le hb0 with hlt | heq
      · refine ⟨0, ?_, by simp⟩
        rw [hlow u hlt hu, dyadic_cast_zero, zero_mul, add_zero]
      · refine mono_census_core hc hw B 0 hu ?_ ?_
        · rw [heq]
          rw [show ((0 : ℕ) : NatOrdinal) = 0 from by exact_mod_cast rfl, add_zero]
        · intro v hvb hvt
          have hvb' : v.birthday < Ω * (((B + 2) : ℕ) : NatOrdinal) := by
            rwa [show ((0 : ℕ) : NatOrdinal) = 0 from by exact_mod_cast rfl,
              add_zero] at hvb
          refine ⟨0, ?_, by simp⟩
          rw [hlow v hvb' hvt, dyadic_cast_zero, zero_mul, add_zero]
    | succ n ihn =>
      intro u hu hb
      rcases lt_or_eq_of_le hb with hlt | heq
      · have hb' : u.birthday ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) + (n : NatOrdinal) := by
          rw [← base_add_nat_succ] at hlt
          exact Order.lt_add_one_iff.1 hlt
        obtain ⟨t, hval, hh⟩ := ihn hu hb'
        exact ⟨t, hval, by omega⟩
      · refine mono_census_core hc hw B (n + 1) hu heq ?_
        intro v hvb hvt
        have hvb' : v.birthday ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) + (n : NatOrdinal) := by
          rw [← base_add_nat_succ] at hvb
          exact Order.lt_add_one_iff.1 hvb
        exact ihn hvt hvb'

/-- **The monomial tube theorem**: the only surreal born before day `ω·(B+2)` at
distance strictly finer than class `ω^{−(B+1)}` from a Hahn sum of the series is the
partial sum `T_{B+2}`. -/
theorem mono_eq_monoS_of_birthday_lt_of_mk_lt (hc : ∀ k, c k ≠ 0) {w : Surreal.{0}}
    (hw : IsHahnSum (monoTerm c) w) (B : ℕ) {u : Surreal.{0}}
    (hu : ArchimedeanClass.mk (ε₀ ^ (B + 1)) < ArchimedeanClass.mk (u - w))
    (hb : u.birthday < Ω * (((B + 2) : ℕ) : NatOrdinal)) : u = monoS c (B + 2) := by
  obtain ⟨m, hm⟩ := lt_omega_mul_succ_decomp (B + 1) hb
  have hu' : ArchimedeanClass.mk (ε₀ ^ B) < ArchimedeanClass.mk (u - w) :=
    (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos B).trans hu
  obtain ⟨s, hsv, -⟩ := mono_census hc hw B m hu' hm
  by_cases hs1 : s = c (B + 1)
  · rw [hsv, hs1, ← monoS_succ (B + 1)]
  · exfalso
    have hmk := mk_mono_grid_sub hc hw B hs1
    rw [← hsv] at hmk
    rw [hmk] at hu
    exact lt_irrefl _ hu

/-! ### The `ω²`-hardness theorem -/

/-- **The `ω²`-hardness of monomial summation**: every Hahn sum of every strictly
dominating `ω`-power series with nonzero dyadic coefficients is born at or after day
`ω·ω`. Transfinite summation of monomial series is uniformly expensive: no choice of
coefficients admits a sum — canonical or otherwise — below day `ω²`. -/
theorem mono_omega_sq_le_birthday_of_isHahnSum (hc : ∀ k, c k ≠ 0) {w : Surreal.{0}}
    (hw : IsHahnSum (monoTerm c) w) :
    Ω * Ω ≤ w.birthday := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨a', ha', b', hb', hle⟩ := NatOrdinal.lt_mul_iff.1 hcon
  obtain ⟨p, rfl⟩ := NatOrdinal.lt_omega0.1 ha'
  obtain ⟨q, rfl⟩ := NatOrdinal.lt_omega0.1 hb'
  have h1 : w.birthday ≤ Ω * (((p + q) : ℕ) : NatOrdinal) := by
    have h2 : w.birthday ≤ (p : NatOrdinal) * Ω + Ω * (q : NatOrdinal) :=
      le_trans (le_add_of_nonneg_right bot_le) hle
    refine h2.trans (le_of_eq ?_)
    push_cast
    ring
  have h0 : (0 : NatOrdinal) < Ω := by
    have h := nat_lt_omega' 0
    rwa [Nat.cast_zero] at h
  have h3 : w.birthday < Ω * ((((p + q) + 2) : ℕ) : NatOrdinal) := by
    refine h1.trans_lt (mul_lt_mul_of_pos_left ?_ h0)
    exact_mod_cast (by omega : p + q < p + q + 2)
  have heq := mono_eq_monoS_of_birthday_lt_of_mk_lt hc hw (p + q)
    (mk_pow_lt_mk_sub_of_isHahnSum_mono hc hw hw (p + q + 1)) h3
  have hres := mk_sub_monoS hc hw (p + q + 3)
  rw [heq] at hres
  have hval : monoS c (p + q + 2) - monoS c (p + q + 3)
      = -((c (p + q + 2) : Surreal) * ε₀ ^ (p + q + 2)) := by
    rw [monoS_succ (p + q + 2)]
    ring
  rw [hval, ArchimedeanClass.mk_neg, ArchimedeanClass.mk_mul,
    mk_dyadic_cast_ne_zero (hc _), zero_add] at hres
  exact absurd hres (ne_of_lt (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos _))

/-- The canonical sum of every dyadic-coefficient monomial series is born at or after
day `ω·ω`. -/
theorem mono_omega_sq_le_birthday_hahnSum (hc : ∀ k, c k ≠ 0) :
    Ω * Ω ≤ (hahnSum (monoTerm_strict_dominating hc)).birthday :=
  mono_omega_sq_le_birthday_of_isHahnSum hc
    (isHahnSum_hahnSum (monoTerm_strict_dominating hc))

end Surreal

end
