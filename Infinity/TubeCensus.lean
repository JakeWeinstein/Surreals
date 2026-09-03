/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.ScaleRealization

/-!
# The tube census along the geometric partial sums

The halo-minimality conjecture (`hahnSum (Σ ω⁻ᵏ) = ω/(ω−1)`) was reduced by
`Infinity.InverseBirthday` to the emptiness of the geometric halo on `[ω·2, ω²)`. The
key discovery of this file is that no two-scale census is needed for that: it suffices
to classify the surreals in the **shrinking tube around `v₀ = ω/(ω−1)`** — those whose
distance from `v₀` has Archimedean class strictly finer than `mk (ω^{−(B−1)})` — block
by block, and in each block `[ω·B, ω·(B+1))` the tube contains only the dyadic
one-scale grid `S_B + t·ω^{−B}` over the *moving anchor* `S_B` (the `B`-term partial
sum). Coarse options of a birthday-minimal game are handled by pure class domination,
so the block-1 census induction of `Infinity.GeometricBirthday` transcribes with anchor
`1 ↦ S_B` and scale `ω⁻¹ ↦ ω^{−B}`.

This file provides:

* `geomS` — the partial sums `S_m = Σ_{k<m} ω⁻ᵏ`, with their tail calculus against
  `v₀ = (1 − ω⁻¹)⁻¹` (`geomS_tail`, `mk_sub_geomS`, `mk_grid_sub_v0`).
* `geom_anchor_pack` — the level induction: for every `B` an anchor game realizing
  `S_{B+1}` with separations at scale `ω^{−B}`, and **the grid realization bound**
  `birthday (S_{B+1} + t·ω^{−(B+1)}) ≤ ω·(B+1) + (hgt t − 1)` — obtained by feeding
  the level-`B` translates into `Infinity.ScaleRealization.scale_grid_aux`.
* `birthday_geomS_add_dyadic_mul_le` / `birthday_geomS_le` — the public forms; in
  particular **`birthday (S_{m+1}) ≤ ω·m`**: every partial sum is born by day `ω·m`.
* `tube_census` — **the tube census**: a surreal born by day `ω·B + n` whose distance
  from `v₀` is strictly finer than class `ω^{−(B−1)}` is `S_B + t·ω^{−B}` with
  `hgt t ≤ n + 1`.
* `eq_geomS_of_birthday_lt_of_mk_lt` — **the tube theorem**: the only surreal born
  before day `ω·(B+1)` at distance strictly finer than class `ω^{−B}` from `v₀` is
  `S_{B+1}`.

`Infinity.GeometricClose` derives from this the emptiness of the geometric halo below
day `ω²` and the value of the canonical geometric sum.
-/

open ArchimedeanClass IGame Set

noncomputable section

namespace Surreal

local notation "ε₀" => eps0
local notation "Ω" => NatOrdinal.of Ordinal.omega0

/-! ### The geometric partial sums -/

/-- The `m`-th partial sum `S_m = Σ_{k<m} ω⁻ᵏ` of the geometric series. -/
def geomS (m : ℕ) : Surreal.{0} :=
  partialSum (fun k ↦ ε₀ ^ k) m

theorem geomS_zero : geomS 0 = 0 :=
  partialSum_zero _

theorem geomS_succ (m : ℕ) : geomS (m + 1) = geomS m + ε₀ ^ m :=
  partialSum_succ _ m

theorem geomS_one : geomS 1 = 1 := by
  rw [geomS, partialSum, Finset.sum_range_one, pow_zero]

/-! ### Bridges between `ε₀`-powers and `ω`-powers -/

theorem wpow_neg_one_eq_eps0 : ω^ (-1 : Surreal.{0}) = ε₀ := by
  rw [eps0_def, show (-1 : Surreal.{0}) = -(1 : Surreal) from rfl, wpow_neg]

theorem eps0_pos : (0 : Surreal.{0}) < ε₀ := by
  rw [eps0_def]
  exact inv_pos.2 (wpow_pos _)

theorem eps0_pow_pos (m : ℕ) : (0 : Surreal.{0}) < ε₀ ^ m :=
  pow_pos eps0_pos m

theorem eps0_pow_eq_wpow : ∀ m : ℕ, (ε₀ : Surreal.{0}) ^ m = ω^ (-((m : ℕ) : Surreal))
  | 0 => by
    rw [pow_zero, Nat.cast_zero, neg_zero, wpow_zero]
  | (m + 1) => by
    rw [eps0_def, wpow_neg, wpow_natCast, inv_pow]

/-- The value of the scale game `ω^(−m)`. -/
theorem mk_Wg (m : ℕ) : Surreal.mk (ω^ (-((m : ℕ) : IGame.{0}))) = ε₀ ^ m := by
  rw [mk_wpow_neg_natCast, eps0_pow_eq_wpow]

/-- The scale separation: every dyadic multiple of `ε₀^{m+1}` is below every positive
dyadic multiple of `ε₀^m`. -/
theorem sep_eps0 (m : ℕ) (s : Dyadic) {q : Dyadic} (hq : 0 < q) :
    (s : Surreal) * ε₀ ^ (m + 1) < (q : Surreal) * ε₀ ^ m := by
  have h1 : (s : Surreal) * ω^ (-1 : Surreal.{0}) < (q : Surreal) := dyadic_mul_wpow_lt hq
  rw [wpow_neg_one_eq_eps0] at h1
  have h2 : (0 : Surreal.{0}) < ε₀ ^ m := eps0_pow_pos m
  calc (s : Surreal) * ε₀ ^ (m + 1) = ((s : Surreal) * ε₀) * ε₀ ^ m := by
        rw [pow_succ]; ring
    _ < (q : Surreal) * ε₀ ^ m := mul_lt_mul_of_pos_right h1 h2

theorem two_dyadic_cast : ((2 : Dyadic) : Surreal.{0}) = 2 := by
  have h : ((2 : Dyadic) : Surreal.{0}) = (((2 : ℕ) : Dyadic) : Surreal) := by norm_num
  rw [h, dyadic_cast_natCast]
  norm_num

/-! ### `NatOrdinal` block arithmetic -/

theorem omega_mul_succ (B : ℕ) :
    Ω * (((B + 1) : ℕ) : NatOrdinal) = Ω * ((B : ℕ) : NatOrdinal) + Ω := by
  have h : (((B + 1) : ℕ) : NatOrdinal) = ((B : ℕ) : NatOrdinal) + 1 := by
    push_cast
    ring
  rw [h, mul_add, mul_one]

theorem nat_lt_omega' (m : ℕ) : ((m : ℕ) : NatOrdinal) < Ω :=
  NatOrdinal.natCast_lt_omega0 m

/-- Absorbing a finite offset into the next `ω`-block. -/
theorem omega_mul_add_nat_le_succ (B m : ℕ) :
    Ω * ((B : ℕ) : NatOrdinal) + ((m : ℕ) : NatOrdinal)
      ≤ Ω * (((B + 1) : ℕ) : NatOrdinal) := by
  rw [omega_mul_succ]
  exact add_le_add le_rfl (nat_lt_omega' m).le

theorem one_pos_dyadic : (0 : Dyadic) < 1 := by
  rw [← Dyadic.coe_lt_coe]
  norm_num

/-- A two-sided cut with singleton left move `{X}` inherits left separation from a
single value inequality. -/
theorem leftSepV_of_singleton {X G : IGame.{0}} [IGame.Numeric G] [IGame.Numeric X]
    {v : Surreal.{0}} (hmoves : Gᴸ = {X}) {q : Dyadic} (hq : 0 < q)
    (h : Surreal.mk X + (q : Surreal) * v ≤ Surreal.mk G) : LeftSepV G v := by
  intro i hi
  have hi2 := hi
  rw [hmoves, Set.mem_singleton_iff] at hi2
  refine ⟨q, hq, ?_⟩
  have heq : @Surreal.mk i (IGame.Numeric.of_mem_moves hi) = Surreal.mk X := by
    subst hi2
    rfl
  rw [heq]
  exact h

/-- A two-sided cut whose right moves form a dyadic-indexed family inherits right
separation from a value inequality for each member. -/
theorem rightSepV_of_family {G : IGame.{0}} [IGame.Numeric G] {f : Dyadic → IGame.{0}}
    {v : Surreal.{0}} (hmoves : Gᴿ = f '' Set.Ioi 0)
    (h : ∀ q : Dyadic, 0 < q → ∀ (hn : (f q).Numeric),
      ∃ q' : Dyadic, 0 < q' ∧
        Surreal.mk G + (q' : Surreal) * v ≤ @Surreal.mk (f q) hn) :
    RightSepV G v := by
  intro j hj
  have hj2 := hj
  rw [hmoves] at hj2
  obtain ⟨q, hq, hfq⟩ := hj2
  have hn : (f q).Numeric := by
    rw [hfq]
    exact IGame.Numeric.of_mem_moves hj
  obtain ⟨q', hq', hle⟩ := h q hq hn
  refine ⟨q', hq', le_trans hle (le_of_eq ?_)⟩
  subst hfq
  rfl

/-! ### The level induction: anchors, translates, and grid bounds at every scale -/

/-- **The level pack**: for every `B`, an anchor game realizing the partial sum
`S_{B+1}` with separations at scale `ε₀^B`, realizations of all its nonnegative
`ε₀^B`-translates below day `ω·(B+1)`, the bound `birthday S_{B+1} < ω·(B+1)`, and the
level-`(B+1)` grid bound `birthday (S_{B+1} + t·ε₀^{B+1}) ≤ ω·(B+1) + (hgt t − 1)`. -/
theorem geom_anchor_pack : ∀ B : ℕ, ∃ (X : IGame.{0}) (hXn : X.Numeric),
    @Surreal.mk X hXn = geomS (B + 1) ∧
    (@LeftSepV X hXn (ε₀ ^ B) ∧ @RightSepV X hXn (ε₀ ^ B)) ∧
    (∀ q : Dyadic, 0 ≤ q → ∃ (g : IGame.{0}) (_ : g.Numeric),
      Surreal.mk g = geomS (B + 1) + (q : Surreal) * ε₀ ^ B ∧
        g.birthday + 1 ≤ Ω * (((B + 1) : ℕ) : NatOrdinal)) ∧
    (geomS (B + 1)).birthday + 1 ≤ Ω * (((B + 1) : ℕ) : NatOrdinal) ∧
    (∀ t : Dyadic, t ≠ 0 →
      (geomS (B + 1) + (t : Surreal) * ε₀ ^ (B + 1)).birthday
        ≤ Ω * (((B + 1) : ℕ) : NatOrdinal) + ((Dyadic.hgt t - 1 : ℕ) : NatOrdinal)) := by
  intro B
  induction B with
  | zero =>
    refine ⟨((1 : Dyadic) : IGame.{0}), inferInstance, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [Surreal.mk_dyadic, dyadic_cast_one, geomS_one]
    · -- left separation at scale ε₀^0 = 1
      rw [pow_zero]
      intro i hi
      obtain ⟨q, hq, hle⟩ := leftSep_dyadic (1 : Dyadic) i hi
      exact ⟨q, hq, by rwa [mul_one]⟩
    · rw [pow_zero]
      intro j hj
      obtain ⟨q, hq, hle⟩ := rightSep_dyadic (1 : Dyadic) j hj
      exact ⟨q, hq, by rwa [mul_one]⟩
    · -- translates: `1 + q` is a dyadic game
      intro q _
      refine ⟨((1 + q : Dyadic) : IGame.{0}), inferInstance, ?_, ?_⟩
      · rw [Surreal.mk_dyadic, dyadic_cast_add', dyadic_cast_one, geomS_one, pow_zero,
          mul_one]
      · have h : ((1 + q : Dyadic) : IGame.{0}).birthday < Ω :=
          IGame.short_iff_birthday_finite.1 (IGame.Short.dyadic _)
        have h1 : Ω * (((0 + 1) : ℕ) : NatOrdinal) = Ω := by
          norm_num
        rw [h1, ← Order.succ_eq_add_one]
        exact Order.succ_le_of_lt h
    · -- the partial sum `S₁ = 1` is born on day 1
      rw [geomS_one, birthday_one]
      have h1 : Ω * (((0 + 1) : ℕ) : NatOrdinal) = Ω := by norm_num
      rw [h1]
      have h2 : (1 : NatOrdinal) + 1 = ((2 : ℕ) : NatOrdinal) := by push_cast; ring
      rw [h2]
      exact (nat_lt_omega' 2).le
    · -- the level-1 grid bound, from the block-1 realization
      intro t ht
      have h := birthday_dyadic_add_dyadic_mul_wpow_le (1 : Dyadic) ht
      rw [dyadic_cast_one, wpow_neg_one_eq_eps0] at h
      have h1 : Ω * (((0 + 1) : ℕ) : NatOrdinal) = Ω := by norm_num
      rw [geomS_one, pow_one, h1]
      exact h
  | succ B ih =>
    classical
    obtain ⟨X, hXn, hmkX, ⟨hL, hR⟩, htrans, hb1, hRgrid⟩ := ih
    haveI := hXn
    -- the translate family for the cut realizing `S_{B+2}`
    choose gt hgtn hgtv hgtb using htrans
    let gR' : Dyadic → IGame.{0} := fun q ↦ if h : 0 ≤ q then gt q h else 0
    have hgR'n : ∀ q : Dyadic, 0 < q → (gR' q).Numeric := by
      intro q hq
      show (if h : 0 ≤ q then gt q h else 0).Numeric
      rw [dif_pos hq.le]
      exact hgtn q hq.le
    have hgR'v : ∀ q (hq : 0 < q), @Surreal.mk (gR' q) (hgR'n q hq)
        = Surreal.mk X + (q : Surreal) * ε₀ ^ B := by
      intro q hq
      have h : gR' q = gt q hq.le := dif_pos hq.le
      rw [show @Surreal.mk (gR' q) (hgR'n q hq)
        = @Surreal.mk (gt q hq.le) (hgtn q hq.le) from by congr 1]
      rw [hgtv q hq.le, hmkX]
    have hgL0 : Surreal.mk X = Surreal.mk X + ((0 : ℕ) : Surreal) * ε₀ ^ (B + 1) := by
      norm_num
    have hequiv := add_natCast_succ_mul_scale_equiv
      (leftMoves_wpow_neg_natCast (B + 1)) (rightMoves_wpow_neg_natCast_succ B)
      (mk_Wg (B + 1)) (mk_Wg B) (eps0_pow_pos (B + 1)) (sep_eps0 B)
      (x := X) 0 (gR := gR') hgR'n hgL0 hgR'v hL hR
    -- numericity of the cut
    have hCn : IGame.Numeric (!{{X} | gR' '' Set.Ioi 0} : IGame.{0}) := by
      refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
      · rw [leftMoves_ofSets, Set.mem_singleton_iff] at hy
        rw [rightMoves_ofSets] at hz
        obtain ⟨q, hq, rfl⟩ := hz
        subst hy
        haveI := hgR'n q hq
        rw [← Surreal.mk_lt_mk, hgR'v q hq]
        have h2 : (0 : Surreal) < (q : Surreal) * ε₀ ^ B :=
          mul_pos (dyadic_cast_pos hq) (eps0_pow_pos B)
        linarith
      · cases p with
        | left =>
          rw [moves_ofSets, Set.mem_singleton_iff] at hy
          subst hy
          exact hXn
        | right =>
          rw [moves_ofSets] at hy
          obtain ⟨q, hq, rfl⟩ := hy
          exact hgR'n q hq
    -- the value of the cut
    have hmkC : @Surreal.mk _ hCn = geomS (B + 2) := by
      have h1 : Surreal.mk (X + (((0 + 1 : ℕ)) : IGame) * ω^ (-(((B + 1) : ℕ) : IGame.{0})))
          = geomS (B + 2) := by
        have hone : (((0 + 1 : ℕ)) : Surreal) = 1 := by norm_num
        rw [Surreal.mk_add, Surreal.mk_mul, Surreal.mk_natCast, mk_Wg, hmkX, hone, one_mul,
          show geomS (B + 2) = geomS (B + 1) + ε₀ ^ (B + 1) from geomS_succ (B + 1)]
      rw [← h1]
      exact (Surreal.mk_eq hequiv).symm
    -- the separations of the cut at scale `ε₀^{B+1}`
    have hL' : @LeftSepV _ hCn (ε₀ ^ (B + 1)) := by
      haveI := hCn
      refine leftSepV_of_singleton (leftMoves_ofSets ..) one_pos_dyadic ?_
      rw [hmkX, dyadic_cast_one, one_mul,
        show Surreal.mk (!{{X} | gR' '' Set.Ioi 0} : IGame.{0}) = geomS (B + 2) from hmkC,
        show geomS (B + 2) = geomS (B + 1) + ε₀ ^ (B + 1) from geomS_succ (B + 1)]
    have hR' : @RightSepV _ hCn (ε₀ ^ (B + 1)) := by
      haveI := hCn
      refine rightSepV_of_family (rightMoves_ofSets ..) ?_
      intro q hq hn
      refine ⟨1, one_pos_dyadic, ?_⟩
      have hval : @Surreal.mk (gR' q) hn = Surreal.mk X + (q : Surreal) * ε₀ ^ B := by
        rw [show @Surreal.mk (gR' q) hn = @Surreal.mk (gR' q) (hgR'n q hq) from by congr 1]
        exact hgR'v q hq
      rw [hval, hmkX, dyadic_cast_one, one_mul,
        show Surreal.mk (!{{X} | gR' '' Set.Ioi 0} : IGame.{0}) = geomS (B + 2) from hmkC,
        show geomS (B + 2) = geomS (B + 1) + ε₀ ^ (B + 1) from geomS_succ (B + 1)]
      have hsep2 := sep_eps0 B 2 hq
      rw [two_dyadic_cast] at hsep2
      have h2 : (2 : Surreal) * ε₀ ^ (B + 1) = ε₀ ^ (B + 1) + ε₀ ^ (B + 1) := by ring
      rw [h2] at hsep2
      linarith
    -- the new partial-sum birthday bound, from the level-(B+1) grid bound at `t = 1`
    have hb1' : (geomS (B + 2)).birthday + 1 ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) := by
      have h := hRgrid 1 one_pos_dyadic.ne'
      rw [dyadic_cast_one, one_mul, ← geomS_succ] at h
      have h0 : ((Dyadic.hgt 1 - 1 : ℕ) : NatOrdinal) = 0 := by
        rw [Dyadic.hgt_one]
        exact_mod_cast rfl
      rw [h0, add_zero] at h
      have h1 := add_le_add h (le_refl 1)
      refine h1.trans ?_
      have h2 : Ω * (((B + 1) : ℕ) : NatOrdinal) + 1
          = Ω * (((B + 1) : ℕ) : NatOrdinal) + ((1 : ℕ) : NatOrdinal) := by
        norm_num
      rw [h2]
      exact omega_mul_add_nat_le_succ (B + 1) 1
    -- the new translate realizations, from the level-(B+1) grid bound
    have htrans' : ∀ q : Dyadic, 0 ≤ q → ∃ (g : IGame.{0}) (_ : g.Numeric),
        Surreal.mk g = geomS (B + 2) + (q : Surreal) * ε₀ ^ (B + 1) ∧
          g.birthday + 1 ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) := by
      intro q hq
      have h1q : (0 : Dyadic) < 1 + q := add_pos_of_pos_of_nonneg one_pos_dyadic hq
      have hval : geomS (B + 2) + (q : Surreal) * ε₀ ^ (B + 1)
          = geomS (B + 1) + ((1 + q : Dyadic) : Surreal) * ε₀ ^ (B + 1) := by
        rw [geomS_succ, dyadic_cast_add', dyadic_cast_one]
        ring
      obtain ⟨g, hgn, hgv, hgb⟩ := birthday_eq_iGameBirthday
        (geomS (B + 2) + (q : Surreal) * ε₀ ^ (B + 1))
      refine ⟨g, hgn, hgv, ?_⟩
      rw [hgb, hval]
      have h := hRgrid (1 + q) h1q.ne'
      have h1 := add_le_add h (le_refl 1)
      refine h1.trans ?_
      rw [base_add_nat_succ]
      have hgt1 : Dyadic.hgt (1 + q) - 1 + 1 = Dyadic.hgt (1 + q) := by
        have := Dyadic.hgt_pos_of_ne_zero h1q.ne'
        omega
      rw [hgt1]
      exact omega_mul_add_nat_le_succ (B + 1) _
    -- the new level-(B+2) grid bound
    have hRgrid' : ∀ t : Dyadic, t ≠ 0 →
        (geomS (B + 2) + (t : Surreal) * ε₀ ^ (B + 2)).birthday
          ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) + ((Dyadic.hgt t - 1 : ℕ) : NatOrdinal) := by
      haveI := hCn
      have hgames : ∀ q : Dyadic, 0 ≤ q → ∃ (g : IGame.{0}) (_ : g.Numeric),
          Surreal.mk g = @Surreal.mk _ hCn + (q : Surreal) * ε₀ ^ (B + 1) ∧
            g.birthday + 1 ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) + ((0 : ℕ) : NatOrdinal) := by
        intro q hq
        obtain ⟨g, hgn, hgv, hgb⟩ := htrans' q hq
        refine ⟨g, hgn, ?_, ?_⟩
        · rw [hgv, hmkC]
        · rw [show ((0 : ℕ) : NatOrdinal) = 0 from by exact_mod_cast rfl, add_zero]
          exact hgb
      intro t ht
      rcases lt_trichotomy t 0 with htn | ht0 | htp
      · -- negative coefficients: negate the anchor
        haveI : IGame.Numeric (-(!{{X} | gR' '' Set.Ioi 0} : IGame.{0})) := inferInstance
        have hmkNC : Surreal.mk (-(!{{X} | gR' '' Set.Ioi 0} : IGame.{0}))
            = -(geomS (B + 2)) := by
          rw [Surreal.mk_neg]
          rw [show Surreal.mk (!{{X} | gR' '' Set.Ioi 0} : IGame.{0})
            = @Surreal.mk _ hCn from by congr 1, hmkC]
        have hgamesN : ∀ q : Dyadic, 0 ≤ q → ∃ (g : IGame.{0}) (_ : g.Numeric),
            Surreal.mk g = Surreal.mk (-(!{{X} | gR' '' Set.Ioi 0} : IGame.{0}))
                + (q : Surreal) * ε₀ ^ (B + 1) ∧
              g.birthday + 1 ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) + ((0 : ℕ) : NatOrdinal) := by
          intro q hq
          have hval : Surreal.mk (-(!{{X} | gR' '' Set.Ioi 0} : IGame.{0}))
              + (q : Surreal) * ε₀ ^ (B + 1)
              = -(geomS (B + 1) + ((1 - q : Dyadic) : Surreal) * ε₀ ^ (B + 1)) := by
            rw [hmkNC, geomS_succ, dyadic_cast_sub', dyadic_cast_one]
            ring
          obtain ⟨g, hgn, hgv, hgb⟩ := birthday_eq_iGameBirthday
            (Surreal.mk (-(!{{X} | gR' '' Set.Ioi 0} : IGame.{0}))
              + (q : Surreal) * ε₀ ^ (B + 1))
          refine ⟨g, hgn, hgv, ?_⟩
          rw [hgb, hval, birthday_neg,
            show ((0 : ℕ) : NatOrdinal) = 0 from by exact_mod_cast rfl, add_zero]
          by_cases hq1 : (1 - q : Dyadic) = 0
          · rw [hq1, dyadic_cast_zero, zero_mul, add_zero]
            refine hb1.trans ?_
            refine mul_le_mul_of_nonneg_left ?_ bot_le
            exact_mod_cast (by omega : B + 1 ≤ B + 2)
          · have h := hRgrid (1 - q) hq1
            have h1 := add_le_add h (le_refl 1)
            refine h1.trans ?_
            rw [base_add_nat_succ]
            have hgt1 : Dyadic.hgt (1 - q) - 1 + 1 = Dyadic.hgt (1 - q) := by
              have := Dyadic.hgt_pos_of_ne_zero hq1
              omega
            rw [hgt1]
            exact omega_mul_add_nat_le_succ (B + 1) _
        have h := scale_grid_aux
          (leftMoves_wpow_neg_natCast (B + 2)) (rightMoves_wpow_neg_natCast_succ (B + 1))
          (mk_Wg (B + 2)) (mk_Wg (B + 1)) (eps0_pow_pos (B + 2)) (sep_eps0 (B + 1))
          (x := -(!{{X} | gR' '' Set.Ioi 0} : IGame.{0})) hR'.neg hL'.neg
          (Ω * (((B + 2) : ℕ) : NatOrdinal)) 0 hgamesN
          (Dyadic.hgt (-t)) (-t) (by rwa [neg_pos]) le_rfl
        have hval2 : Surreal.mk (-(!{{X} | gR' '' Set.Ioi 0} : IGame.{0}))
            + ((-t : Dyadic) : Surreal) * ε₀ ^ (B + 2)
            = -(geomS (B + 2) + (t : Surreal) * ε₀ ^ (B + 2)) := by
          rw [hmkNC, dyadic_cast_neg']
          ring
        rw [hval2, birthday_neg, Dyadic.hgt_neg] at h
        exact h
      · exact absurd ht0 ht
      · -- positive coefficients: the direct grid induction over the new anchor
        have h := scale_grid_aux
          (leftMoves_wpow_neg_natCast (B + 2)) (rightMoves_wpow_neg_natCast_succ (B + 1))
          (mk_Wg (B + 2)) (mk_Wg (B + 1)) (eps0_pow_pos (B + 2)) (sep_eps0 (B + 1))
          (x := (!{{X} | gR' '' Set.Ioi 0} : IGame.{0})) hL' hR'
          (Ω * (((B + 2) : ℕ) : NatOrdinal)) 0 hgames
          (Dyadic.hgt t) t htp le_rfl
        rw [hmkC] at h
        exact h
    exact ⟨_, hCn, hmkC, ⟨hL', hR'⟩, htrans', hb1', hRgrid'⟩

/-! ### Public grid and partial-sum birthday bounds -/

/-- **The grid bound at every scale**: the dyadic grid point `S_{B+1} + t·ω^{−(B+1)}`
over the partial-sum anchor is born by day `ω·(B+1) + (hgt t − 1)`. -/
theorem birthday_geomS_add_dyadic_mul_le (B : ℕ) {t : Dyadic} (ht : t ≠ 0) :
    (geomS (B + 1) + (t : Surreal) * ε₀ ^ (B + 1)).birthday
      ≤ Ω * (((B + 1) : ℕ) : NatOrdinal) + ((Dyadic.hgt t - 1 : ℕ) : NatOrdinal) := by
  obtain ⟨X, hXn, -, -, -, -, hRgrid⟩ := geom_anchor_pack B
  exact hRgrid t ht

/-- **Every partial sum is born strictly inside its block**:
`birthday (S_{B+1}) < ω·(B+1)`. -/
theorem birthday_geomS_add_one_le (B : ℕ) :
    (geomS (B + 1)).birthday + 1 ≤ Ω * (((B + 1) : ℕ) : NatOrdinal) := by
  obtain ⟨X, hXn, -, -, -, hb1, -⟩ := geom_anchor_pack B
  exact hb1

/-- **The sharp partial-sum bound**: `S_{m+2}` (with leading term `ω^{−(m+1)}`) is born
by day `ω·(m+1)`. -/
theorem birthday_geomS_le (m : ℕ) :
    (geomS (m + 2)).birthday ≤ Ω * (((m + 1) : ℕ) : NatOrdinal) := by
  obtain ⟨X, hXn, -, -, -, -, hRgrid⟩ := geom_anchor_pack m
  have h := hRgrid 1 one_pos_dyadic.ne'
  rw [dyadic_cast_one, one_mul, ← geomS_succ] at h
  have h0 : ((Dyadic.hgt 1 - 1 : ℕ) : NatOrdinal) = 0 := by
    rw [Dyadic.hgt_one]
    exact_mod_cast rfl
  rw [h0, add_zero] at h
  exact h

/-! ### The tail calculus of `v₀ = (1 − ω⁻¹)⁻¹` -/

local notation "V₀" => (1 - eps0)⁻¹

theorem eps0_infinitesimal : Infinitesimal (ε₀ : Surreal.{0}) := by
  rw [eps0_def]
  exact infinitesimal_inv_wpow one_pos

theorem eps0_lt_one : (ε₀ : Surreal.{0}) < 1 := by
  have h := eps0_infinitesimal.lt_ratCast (q := 1) one_pos
  simpa using h

theorem one_sub_eps0_ne_zero : (1 : Surreal.{0}) - ε₀ ≠ 0 :=
  sub_ne_zero.2 (ne_of_gt eps0_lt_one)

theorem v0_sub_one : V₀ - 1 = ε₀ * V₀ := by
  have h2 : ((1 : Surreal.{0}) - ε₀) * (1 - ε₀)⁻¹ = 1 :=
    mul_inv_cancel₀ one_sub_eps0_ne_zero
  linear_combination h2

/-- The tail identity: `v₀ − S_m = ω^{−m}·v₀`. -/
theorem geomS_tail : ∀ m : ℕ, V₀ - geomS m = ε₀ ^ m * V₀
  | 0 => by rw [geomS_zero, sub_zero, pow_zero, one_mul]
  | (m + 1) => by
    rw [geomS_succ]
    calc V₀ - (geomS m + ε₀ ^ m) = (V₀ - geomS m) - ε₀ ^ m := by ring
      _ = ε₀ ^ m * V₀ - ε₀ ^ m := by rw [geomS_tail m]
      _ = ε₀ ^ m * (V₀ - 1) := by ring
      _ = ε₀ ^ m * (ε₀ * V₀) := by rw [v0_sub_one]
      _ = ε₀ ^ (m + 1) * V₀ := by rw [pow_succ]; ring

theorem mk_one_surreal : ArchimedeanClass.mk (1 : Surreal.{0}) = 0 := by
  rw [show (1 : Surreal.{0}) = ((1 : ℝ) : Surreal) from Real.toSurreal_one.symm]
  exact mk_realCast one_ne_zero

theorem mk_v0 : ArchimedeanClass.mk V₀ = 0 := by
  rw [ArchimedeanClass.mk_inv, neg_eq_zero]
  have h : (1 : Surreal.{0}) - ε₀ = 1 + (-ε₀) := by ring
  rw [h, ArchimedeanClass.mk_add_eq_mk_left ?_]
  · exact mk_one_surreal
  · rw [ArchimedeanClass.mk_neg, mk_one_surreal]
    exact infinitesimal_def.1 eps0_infinitesimal

/-- The distance class of a partial sum from `v₀`. -/
theorem mk_geomS_sub_v0 (m : ℕ) :
    ArchimedeanClass.mk (geomS m - V₀) = ArchimedeanClass.mk (ε₀ ^ m) := by
  have h : geomS m - V₀ = -(ε₀ ^ m * V₀) := by
    rw [← geomS_tail m]
    ring
  rw [h, ArchimedeanClass.mk_neg, ArchimedeanClass.mk_mul, mk_v0, add_zero]

theorem mk_dyadic_cast_ne_zero {c : Dyadic} (hc : c ≠ 0) :
    ArchimedeanClass.mk ((c : Surreal.{0})) = 0 := by
  have h : ((c : Dyadic) : Surreal.{0}) = (((c : ℚ) : ℝ) : Surreal) := by
    rw [← Real.toSurreal_ratCast]
  rw [h]
  refine mk_realCast ?_
  intro h0
  apply hc
  have h1 : (c : ℚ) = (0 : ℚ) := by exact_mod_cast h0
  ext
  rw [h1]
  norm_num

/-- The distance class of a grid point with coefficient `t ≠ 1` from `v₀` is exactly the
grid scale. -/
theorem mk_grid_sub_v0 (B : ℕ) {t : Dyadic} (ht : t ≠ 1) :
    ArchimedeanClass.mk (geomS (B + 1) + (t : Surreal) * ε₀ ^ (B + 1) - V₀)
      = ArchimedeanClass.mk (ε₀ ^ (B + 1)) := by
  have h : geomS (B + 1) + (t : Surreal) * ε₀ ^ (B + 1) - V₀
      = ε₀ ^ (B + 1) * ((t : Surreal) - V₀) := by
    calc geomS (B + 1) + (t : Surreal) * ε₀ ^ (B + 1) - V₀
        = (t : Surreal) * ε₀ ^ (B + 1) - (V₀ - geomS (B + 1)) := by ring
      _ = (t : Surreal) * ε₀ ^ (B + 1) - ε₀ ^ (B + 1) * V₀ := by rw [geomS_tail]
      _ = ε₀ ^ (B + 1) * ((t : Surreal) - V₀) := by ring
  rw [h, ArchimedeanClass.mk_mul]
  have h2 : (t : Surreal) - V₀ = ((t - 1 : Dyadic) : Surreal) + (-(ε₀ * V₀)) := by
    rw [dyadic_cast_sub', dyadic_cast_one]
    linear_combination -v0_sub_one
  rw [h2, ArchimedeanClass.mk_add_eq_mk_left ?_]
  · rw [mk_dyadic_cast_ne_zero (sub_ne_zero.2 ht), add_zero]
  · rw [ArchimedeanClass.mk_neg, ArchimedeanClass.mk_mul, mk_v0, add_zero,
      mk_dyadic_cast_ne_zero (sub_ne_zero.2 ht)]
    exact infinitesimal_def.1 eps0_infinitesimal

/-! ### Sign transport across dominated differences -/

theorem pos_add_of_mk_lt {a b : Surreal.{0}} (ha : 0 < a)
    (h : ArchimedeanClass.mk a < ArchimedeanClass.mk b) : 0 < a + b := by
  have h2 := abs_lt_abs_of_mk_lt h
  rw [abs_of_pos ha] at h2
  have h3 := (abs_lt.1 h2).1
  linarith

/-- If `i < u` and `c` differs from `u` at a strictly finer class than `i` does, then
`i < c`. -/
theorem lt_of_lt_of_mk_sub_lt {i u c : Surreal.{0}} (hiu : i < u)
    (h : ArchimedeanClass.mk (i - u) < ArchimedeanClass.mk (c - u)) : i < c := by
  have h1 : ArchimedeanClass.mk (u - i) < ArchimedeanClass.mk (c - u) := by
    rwa [show u - i = -(i - u) from by ring, ArchimedeanClass.mk_neg]
  have h2 := pos_add_of_mk_lt (by linarith : (0 : Surreal.{0}) < u - i) h1
  linarith

/-- If `u < j` and `c` differs from `u` at a strictly finer class than `j` does, then
`c < j`. -/
theorem lt_of_lt_of_mk_sub_lt' {j u c : Surreal.{0}} (huj : u < j)
    (h : ArchimedeanClass.mk (j - u) < ArchimedeanClass.mk (c - u)) : c < j := by
  have h1 : ArchimedeanClass.mk (j - u) < ArchimedeanClass.mk (u - c) := by
    rwa [show u - c = -(c - u) from by ring, ArchimedeanClass.mk_neg]
  have h2 := pos_add_of_mk_lt (by linarith : (0 : Surreal.{0}) < j - u) h1
  linarith

/-- Grid monotonicity in the coefficient, reversed. -/
theorem dyadic_lt_of_mul_eps_lt {m : ℕ} {s t : Dyadic}
    (h : (s : Surreal) * ε₀ ^ m < (t : Surreal) * ε₀ ^ m) : s < t := by
  rcases lt_trichotomy s t with hst | hst | hst
  · exact hst
  · subst hst
    exact absurd h (lt_irrefl _)
  · exact absurd (mul_lt_mul_of_pos_right (dyadic_cast_lt hst) (eps0_pow_pos m))
      (not_lt.2 h.le)

/-! ### The block decomposition of days below `ω·(k+1)` -/

theorem lt_omega_mul_succ_decomp : ∀ (k : ℕ) {x : NatOrdinal},
    x < Ω * (((k + 1) : ℕ) : NatOrdinal) →
    ∃ m : ℕ, x ≤ Ω * ((k : ℕ) : NatOrdinal) + (m : NatOrdinal) := by
  intro k
  induction k with
  | zero =>
    intro x hx
    have h1 : Ω * (((0 + 1) : ℕ) : NatOrdinal) = Ω := by norm_num
    rw [h1] at hx
    obtain ⟨m, rfl⟩ := NatOrdinal.lt_omega0.1 hx
    refine ⟨m, ?_⟩
    have h2 : Ω * ((0 : ℕ) : NatOrdinal) = 0 := by norm_num
    rw [h2, zero_add]
  | succ k ihk =>
    intro x hx
    rw [omega_mul_succ] at hx
    rcases NatOrdinal.lt_add_iff.1 hx with ⟨b', hb', hle⟩ | ⟨c', hc', hle⟩
    · obtain ⟨m', hm'⟩ := ihk hb'
      refine ⟨m', hle.trans ?_⟩
      calc b' + Ω ≤ (Ω * ((k : ℕ) : NatOrdinal) + (m' : NatOrdinal)) + Ω :=
            add_le_add hm' le_rfl
        _ = Ω * (((k + 1) : ℕ) : NatOrdinal) + (m' : NatOrdinal) := by
            rw [omega_mul_succ]
            ring
    · obtain ⟨m, rfl⟩ := NatOrdinal.lt_omega0.1 hc'
      exact ⟨m, hle⟩

/-! ### The census core: the critical-day analysis -/

/-- **The critical-day step of the tube census.** If `u` sits in the level-`(B+1)` tube
(distance from `v₀` strictly finer than class `ω^{−(B+1)}`), is born exactly on day
`ω·(B+2) + N`, and every strictly earlier tube inhabitant is a level-`(B+2)` grid point
of height at most `N`, then `u` is itself a level-`(B+2)` grid point of height at most
`N + 1`. The candidate is produced by the interleaving theorem of `Infinity.Census`,
priced by the pack of this file, and forced by simplest-fit uniqueness; options outside
the tube are handled by pure class domination. -/
private theorem tube_census_core (B N : ℕ) {u : Surreal.{0}}
    (hu : ArchimedeanClass.mk (ε₀ ^ (B + 1)) < ArchimedeanClass.mk (u - V₀))
    (hbeq : u.birthday = Ω * (((B + 2) : ℕ) : NatOrdinal) + (N : NatOrdinal))
    (horacle : ∀ v : Surreal.{0},
      v.birthday < Ω * (((B + 2) : ℕ) : NatOrdinal) + (N : NatOrdinal) →
      ArchimedeanClass.mk (ε₀ ^ (B + 1)) < ArchimedeanClass.mk (v - V₀) →
      ∃ s : Dyadic, v = geomS (B + 2) + (s : Surreal) * ε₀ ^ (B + 2) ∧ Dyadic.hgt s ≤ N) :
    ∃ t : Dyadic, u = geomS (B + 2) + (t : Surreal) * ε₀ ^ (B + 2) ∧
      Dyadic.hgt t ≤ N + 1 := by
  classical
  obtain ⟨g, hgn, hgy, hgb⟩ := birthday_eq_iGameBirthday u
  haveI := hgn
  have hslt := Cut.supLeft_lt_infRight_of_numeric g
  -- every option is born strictly earlier
  have hopt : ∀ (p : Player) (i : IGame), i ∈ g.moves p → ∀ (hn : i.Numeric),
      (@Surreal.mk i hn).birthday
        < Ω * (((B + 2) : ℕ) : NatOrdinal) + (N : NatOrdinal) := by
    intro p i hi hn
    have h1 := IGame.birthday_lt_of_mem_moves hi
    rw [hgb, hbeq] at h1
    exact lt_of_le_of_lt (birthday_mk_le i) h1
  -- the coefficient sets of the tube options
  set S : Set Dyadic := {s | Dyadic.hgt s ≤ N ∧ ∃ i ∈ gᴸ, ∃ _ : i.Numeric,
    Surreal.mk i = geomS (B + 2) + (s : Surreal) * ε₀ ^ (B + 2)} with hS
  set S' : Set Dyadic := {s | Dyadic.hgt s ≤ N ∧ ∃ j ∈ gᴿ, ∃ _ : j.Numeric,
    Surreal.mk j = geomS (B + 2) + (s : Surreal) * ε₀ ^ (B + 2)} with hS'
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
  -- choose the candidate coefficient by interleaving
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
  -- the candidate
  set c : Surreal.{0} := geomS (B + 2) + (t : Surreal) * ε₀ ^ (B + 2) with hc
  have hcb : c.birthday ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) + (N : NatOrdinal) := by
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [hc, dyadic_cast_zero, zero_mul, add_zero]
      have h := birthday_geomS_add_one_le (B + 1)
      refine le_trans (le_trans (le_add_of_nonneg_right zero_le_one) h) ?_
      exact le_add_of_nonneg_right bot_le
    · rw [hc]
      refine (birthday_geomS_add_dyadic_mul_le (B + 1) ht0).trans ?_
      refine add_le_add le_rfl (nat_cast_mono ?_)
      omega
  -- the candidate's distance from `v₀` is strictly finer than the tube level
  have hcv : ArchimedeanClass.mk (ε₀ ^ (B + 1)) < ArchimedeanClass.mk (c - V₀) := by
    by_cases ht1 : t = 1
    · have hcs : c - V₀ = geomS (B + 3) - V₀ := by
        rw [hc, ht1, dyadic_cast_one, one_mul, ← geomS_succ]
      rw [hcs, mk_geomS_sub_v0]
      exact (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos (B + 1)).trans
        (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos (B + 2))
    · rw [hc, mk_grid_sub_v0 (B + 1) ht1]
      exact mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos (B + 1)
  -- the candidate fits the option cuts of the minimal game
  have hfitc : Cut.Fits c (Cut.supLeft g) (Cut.infRight g) := by
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
      have hlt : Surreal.mk i < c := by
        by_cases hitube : ArchimedeanClass.mk (ε₀ ^ (B + 1))
            < ArchimedeanClass.mk (Surreal.mk i - V₀)
        · -- tube option: the oracle puts it on the grid, strictly left of `t`
          obtain ⟨s, hsv, hshgt⟩ := horacle (Surreal.mk i) hib hitube
          have hst : s < t := htS s ⟨hshgt, i, hi, inferInstance, hsv⟩
          rw [hsv, hc]
          have := mul_lt_mul_of_pos_right (dyadic_cast_lt hst) (eps0_pow_pos (B + 2))
          linarith
        · -- coarse option: class domination
          rw [not_lt] at hitube
          have hmk_iu : ArchimedeanClass.mk (Surreal.mk i - u)
              = ArchimedeanClass.mk (Surreal.mk i - V₀) := by
            rw [show Surreal.mk i - u = (Surreal.mk i - V₀) + (V₀ - u) from by ring,
              ArchimedeanClass.mk_add_eq_mk_left ?_]
            rw [show V₀ - u = -(u - V₀) from by ring, ArchimedeanClass.mk_neg]
            exact lt_of_le_of_lt hitube hu
          have hmk_cu : ArchimedeanClass.mk (Surreal.mk i - u)
              < ArchimedeanClass.mk (c - u) := by
            rw [hmk_iu]
            refine lt_of_le_of_lt hitube ?_
            have hmin2 : ArchimedeanClass.mk (ε₀ ^ (B + 1))
                < min (ArchimedeanClass.mk (c - V₀)) (ArchimedeanClass.mk (V₀ - u)) := by
              refine lt_min hcv ?_
              rw [show V₀ - u = -(u - V₀) from by ring, ArchimedeanClass.mk_neg]
              exact hu
            refine lt_of_lt_of_le hmin2 ?_
            rw [show c - u = (c - V₀) + (V₀ - u) from by ring]
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
      have hlt : c < Surreal.mk j := by
        by_cases hjtube : ArchimedeanClass.mk (ε₀ ^ (B + 1))
            < ArchimedeanClass.mk (Surreal.mk j - V₀)
        · obtain ⟨s, hsv, hshgt⟩ := horacle (Surreal.mk j) hjb hjtube
          have hst : t < s := htS' s ⟨hshgt, j, hj, inferInstance, hsv⟩
          rw [hsv, hc]
          have := mul_lt_mul_of_pos_right (dyadic_cast_lt hst) (eps0_pow_pos (B + 2))
          linarith
        · rw [not_lt] at hjtube
          have hmk_ju : ArchimedeanClass.mk (Surreal.mk j - u)
              = ArchimedeanClass.mk (Surreal.mk j - V₀) := by
            rw [show Surreal.mk j - u = (Surreal.mk j - V₀) + (V₀ - u) from by ring,
              ArchimedeanClass.mk_add_eq_mk_left ?_]
            rw [show V₀ - u = -(u - V₀) from by ring, ArchimedeanClass.mk_neg]
            exact lt_of_le_of_lt hjtube hu
          have hmk_cu : ArchimedeanClass.mk (Surreal.mk j - u)
              < ArchimedeanClass.mk (c - u) := by
            rw [hmk_ju]
            refine lt_of_le_of_lt hjtube ?_
            have hmin2 : ArchimedeanClass.mk (ε₀ ^ (B + 1))
                < min (ArchimedeanClass.mk (c - V₀)) (ArchimedeanClass.mk (V₀ - u)) := by
              refine lt_min hcv ?_
              rw [show V₀ - u = -(u - V₀) from by ring, ArchimedeanClass.mk_neg]
              exact hu
            refine lt_of_lt_of_le hmin2 ?_
            rw [show c - u = (c - V₀) + (V₀ - u) from by ring]
            exact ArchimedeanClass.min_le_mk_add ..
          exact lt_of_lt_of_mk_sub_lt' hyj hmk_cu
      rw [← toGame_mk, toGame_le_iff]
      exact not_le.2 hlt
  -- simplest-fit uniqueness closes the census
  have hy' : Cut.simplestBtwn hslt = u := by
    rw [← toGame_inj, Cut.simplestBtwn_supLeft_infRight hslt, ← hgy, toGame_mk]
  have hfity : Cut.Fits u (Cut.supLeft g) (Cut.infRight g) :=
    hy' ▸ Cut.fits_simplestBtwn hslt
  have hmin : ∀ v, Cut.Fits v (Cut.supLeft g) (Cut.infRight g) →
      u.birthday ≤ v.birthday := by
    intro v hv
    have h := Cut.birthday_simplestBtwn_le_of_fits hv
    rwa [hy'] at h
  have hyc : u = c :=
    (Cut.eq_of_fits_of_birthday_le hfity hfitc hmin (hcb.trans_eq hbeq.symm)).symm
  exact ⟨t, by rw [hyc, hc], htgt⟩

/-! ### The tube census -/

/-- **The tube census**: a surreal born by day `ω·(B+1) + n` whose distance from
`v₀ = ω/(ω−1)` has Archimedean class strictly finer than `mk (ω^{−B})` is a dyadic grid
point `S_{B+1} + t·ω^{−(B+1)}` over the partial-sum anchor, with `hgt t ≤ n + 1`.
One induction on the block index `B` with the block-1 grid census of
`Infinity.GeometricBirthday` as base, and an inner induction on `n` through the
critical-day core. -/
theorem tube_census : ∀ (B : ℕ) (n : ℕ) {u : Surreal.{0}},
    ArchimedeanClass.mk (ε₀ ^ B) < ArchimedeanClass.mk (u - V₀) →
    u.birthday ≤ Ω * (((B + 1) : ℕ) : NatOrdinal) + (n : NatOrdinal) →
    ∃ t : Dyadic, u = geomS (B + 1) + (t : Surreal) * ε₀ ^ (B + 1) ∧
      Dyadic.hgt t ≤ n + 1 := by
  intro B
  induction B with
  | zero =>
    intro n u hu hb
    have hu0 : (0 : ArchimedeanClass Surreal.{0}) < ArchimedeanClass.mk (u - V₀) := by
      rw [pow_zero, mk_one_surreal] at hu
      exact hu
    have hinf : Infinitesimal (u - V₀) := infinitesimal_def.2 hu0
    have hev : Infinitesimal (ε₀ * V₀) := by
      refine infinitesimal_def.2 ?_
      rw [ArchimedeanClass.mk_mul, mk_v0, add_zero]
      exact infinitesimal_def.1 eps0_infinitesimal
    have h2 : u = 1 + (ε₀ * V₀ + (u - V₀)) := by
      linear_combination v0_sub_one
    have hsum : Infinitesimal (ε₀ * V₀ + (u - V₀)) := hev.add hinf
    have hufin : IsFinite u := by
      rw [h2]
      exact isFinite_one.add hsum.isFinite
    have hst : stdPart u = 1 := by
      rw [h2, stdPart_add_eq_left hsum, ArchimedeanClass.stdPart_one]
    have hb' : u.birthday ≤ Ω + (n : NatOrdinal) := by
      have h1 : Ω * (((0 + 1) : ℕ) : NatOrdinal) = Ω := by norm_num
      rwa [h1] at hb
    obtain ⟨r, hval, hh1, -⟩ := eq_grid_of_isFinite_of_birthday_le n hufin hb'
    rw [hst, Real.toSurreal_one] at hval
    refine ⟨r, ?_, hh1⟩
    rw [geomS_one, pow_one, ← wpow_neg_one_eq_eps0]
    exact hval
  | succ B ihB =>
    -- the cascade: everything in the tube below the block start is the partial sum
    have hlow : ∀ v : Surreal.{0}, v.birthday < Ω * (((B + 2) : ℕ) : NatOrdinal) →
        ArchimedeanClass.mk (ε₀ ^ (B + 1)) < ArchimedeanClass.mk (v - V₀) →
        v = geomS (B + 2) := by
      intro v hvb hvt
      obtain ⟨m, hm⟩ := lt_omega_mul_succ_decomp (B + 1) hvb
      have hvt' : ArchimedeanClass.mk (ε₀ ^ B) < ArchimedeanClass.mk (v - V₀) :=
        (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos B).trans hvt
      obtain ⟨s, hsv, -⟩ := ihB m hvt' hm
      by_cases hs1 : s = 1
      · rw [hsv, hs1, dyadic_cast_one, one_mul, ← geomS_succ]
      · exfalso
        have hmk := mk_grid_sub_v0 B hs1
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
      · refine tube_census_core B 0 hu ?_ ?_
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
      · refine tube_census_core B (n + 1) hu heq ?_
        intro v hvb hvt
        have hvb' : v.birthday ≤ Ω * (((B + 2) : ℕ) : NatOrdinal) + (n : NatOrdinal) := by
          rw [← base_add_nat_succ] at hvb
          exact Order.lt_add_one_iff.1 hvb
        exact ihn hvt hvb'

/-- **The tube theorem**: the only surreal born before day `ω·(B+2)` whose distance
from `v₀ = ω/(ω−1)` has class strictly finer than `mk (ω^{−(B+1)})` is the partial sum
`S_{B+2}` — whose distance has class exactly `mk (ω^{−(B+2)})`. -/
theorem eq_geomS_of_birthday_lt_of_mk_lt (B : ℕ) {u : Surreal.{0}}
    (hu : ArchimedeanClass.mk (ε₀ ^ (B + 1)) < ArchimedeanClass.mk (u - V₀))
    (hb : u.birthday < Ω * (((B + 2) : ℕ) : NatOrdinal)) : u = geomS (B + 2) := by
  obtain ⟨m, hm⟩ := lt_omega_mul_succ_decomp (B + 1) hb
  have hu' : ArchimedeanClass.mk (ε₀ ^ B) < ArchimedeanClass.mk (u - V₀) :=
    (mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos B).trans hu
  obtain ⟨s, hsv, -⟩ := tube_census B m hu' hm
  by_cases hs1 : s = 1
  · rw [hsv, hs1, dyadic_cast_one, one_mul, ← geomS_succ]
  · exfalso
    have hmk := mk_grid_sub_v0 B hs1
    rw [← hsv] at hmk
    rw [hmk] at hu
    exact lt_irrefl _ hu

end Surreal

end
