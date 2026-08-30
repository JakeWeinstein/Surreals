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

end Surreal

end
