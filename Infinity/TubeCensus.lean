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

private theorem one_pos_dyadic : (0 : Dyadic) < 1 := by
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

end Surreal

end
