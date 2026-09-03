/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.HaloRealization

/-!
# The uniform census below day `ω·2`, and the geometric ladder

`Infinity.DayOmega` proved Conway's day-`ω` census. This file proves the **uniform
theorem for all the days `ω + n` at once** — the finite surreals born before day `ω·2`
are exactly the dyadic `ω⁻¹`-grid over the reals:

* `eq_grid_of_isFinite_of_birthday_le` — **the grid census**: a finite surreal born by
  day `ω + n` is `a + r·ω⁻¹` with `a` its own standard part and `r` a dyadic of height
  at most `n + 1` (at most `n` when `a` is not a dyadic rational). Proved by a single
  induction on `n` through the census method: a birthday-minimal game's options are
  grid points by the inductive hypothesis, the interleaving theorem of `Infinity.Census`
  inserts a one-day-younger dyadic coefficient between the option coefficients, the grid
  bounds of `Infinity.HaloRealization` price the candidate, and simplest-fit uniqueness
  forces equality.
* `eq_grid_of_isFinite_of_birthday_lt_omega_two` — the packaged form: finite and born
  before day `ω·2` implies lying on the grid.

The payoff is the **uniform step of the geometric ladder**, bypassing the day-by-day
censuses entirely:

* `omega0_add_omega0_le_birthday_of_isHahnSum_geometric` — **every Hahn sum of the
  geometric series `Σ ω⁻ᵏ` is born at or after day `ω·2`.** A Hahn sum lies in the halo
  of `1` with residuals below `ω⁻¹`-scale from stage `2` on; a grid point `1 + r·ω⁻¹`
  can only satisfy the stage-`2` residual when `r = 1`, and `1 + ω⁻¹` fails stage `3`.
  This leaps past the day-`ω+1`, `ω+2`, … censuses in one stroke: the halo of
  `ω/(ω−1)` is empty throughout `[ω, ω·2)`.
* `omega0_mul_two_le_birthday_hahnSum_geometric` — in particular the canonical sum
  `hahnSum (Σ ω⁻ᵏ)` is born at or after day `ω·2`.

The remaining gap to the halo-minimality conjecture (`hahnSum (Σ ω⁻ᵏ) = ω/(ω−1)`) is
recorded at the end of the file: emptiness on `[ω·2, birthday (ω/(ω−1)))` and the
matching upper bound for `ω/(ω−1)` itself.
-/

open ArchimedeanClass IGame Set

universe u

noncomputable section

namespace Surreal

local notation "Ω" => NatOrdinal.of Ordinal.omega0

/-! ### Finiteness and standard-part comparisons -/

/-- An infinite surreal below a finite one is below every finite one. -/
theorem lt_finite_of_not_isFinite_of_lt {v y c : Surreal} (hv : ¬ IsFinite v)
    (hvy : v < y) (hy : IsFinite y) (hc : IsFinite c) : v < c := by
  by_contra hcon
  rw [not_lt] at hcon
  apply hv
  obtain ⟨m, hm⟩ := isFinite_iff.1 hy
  obtain ⟨mc, hmc⟩ := isFinite_iff.1 hc
  rw [isFinite_iff]
  refine ⟨m + mc, ?_⟩
  rw [abs_le]
  have h1 := (abs_le.1 hm).2
  have h2 := (abs_le.1 hmc).1
  have hcast : ((m + mc : ℕ) : Surreal) = (m : Surreal) + (mc : Surreal) := by push_cast; ring
  rw [hcast]
  have hm0 : (0 : Surreal) ≤ (m : Surreal) := by exact_mod_cast Nat.zero_le m
  have hmc0 : (0 : Surreal) ≤ (mc : Surreal) := by exact_mod_cast Nat.zero_le mc
  constructor
  · linarith
  · linarith

/-- An infinite surreal above a finite one is above every finite one. -/
theorem finite_lt_of_not_isFinite_of_lt {v y c : Surreal} (hv : ¬ IsFinite v)
    (hyv : y < v) (hy : IsFinite y) (hc : IsFinite c) : c < v := by
  have h := lt_finite_of_not_isFinite_of_lt (v := -v) (fun h ↦ hv (by simpa using h.neg))
    (neg_lt_neg hyv) hy.neg hc.neg
  linarith

/-! ### Grid values: standard parts, finiteness, coefficient order -/

theorem stdPart_grid (a : ℝ) (s : Dyadic) :
    stdPart ((a : Surreal) + (s : Surreal) * ω^ (-1 : Surreal)) = a := by
  rw [stdPart_add_eq_left (infinitesimal_def.1 (infinitesimal_dyadic_mul_wpow s)),
    stdPart_realCast]

theorem isFinite_grid (a : ℝ) (s : Dyadic) :
    IsFinite ((a : Surreal) + (s : Surreal) * ω^ (-1 : Surreal)) :=
  (isFinite_realCast a).add (infinitesimal_dyadic_mul_wpow s).isFinite

theorem dyadic_lt_of_cast_mul_wpow_lt {s t : Dyadic}
    (h : (s : Surreal) * ω^ (-1 : Surreal) < (t : Surreal) * ω^ (-1 : Surreal)) : s < t := by
  rcases lt_trichotomy s t with hst | hst | hst
  · exact hst
  · subst hst
    exact absurd h (lt_irrefl _)
  · exact absurd (dyadic_mul_wpow_lt_dyadic_mul_wpow hst) (not_lt.2 h.le)

theorem dyadic_cast_one : ((1 : Dyadic) : Surreal) = 1 := by
  show (((1 : Dyadic) : ℚ) : Surreal) = 1
  norm_num

/-! ### The uniform grid census below day `ω·2` -/

/-- **The grid census at day `ω + n`**, one induction for every `n` at once: a finite
surreal born by day `ω + n` is `a + r·ω⁻¹` where `a` is its standard part and `r` is a
dyadic of height at most `n + 1` — at most `n` when `a` is not a dyadic rational.
(Conway's censuses for the days `ω, ω+1, ω+2, …` in a single statement; the day-`ω`
census of `Infinity.DayOmega` is the base case.) -/
theorem eq_grid_of_isFinite_of_birthday_le :
    ∀ (n : ℕ) {y : Surreal.{u}}, IsFinite y →
      y.birthday ≤ NatOrdinal.of Ordinal.omega0 + (n : NatOrdinal) →
    ∃ r : Dyadic,
      y = ((stdPart y : ℝ) : Surreal) + (r : Surreal) * ω^ (-1 : Surreal) ∧
      Dyadic.hgt r ≤ n + 1 ∧
      ((∀ e : Dyadic, stdPart y ≠ ((e : ℚ) : ℝ)) → Dyadic.hgt r ≤ n) := by
  intro n
  induction n with
  | zero =>
    intro y hy hb
    have hb' : y.birthday ≤ NatOrdinal.of Ordinal.omega0 := by
      have h0 : ((0 : ℕ) : NatOrdinal) = 0 := by exact_mod_cast rfl
      rwa [h0, add_zero] at hb
    rcases birthday_le_omega0_iff.1 hb' with ⟨rr, rfl⟩ | h | h | ⟨d, hd⟩
    · refine ⟨0, ?_, by simp, fun _ ↦ by simp⟩
      rw [stdPart_realCast, dyadic_cast_zero, zero_mul, add_zero]
    · rw [h] at hy
      exact absurd hy not_isFinite_wpow_one
    · rw [h] at hy
      have := hy.neg
      rw [neg_neg] at this
      exact absurd this not_isFinite_wpow_one
    · rcases hd with h | h
      · -- y = d + ω⁻¹
        have hval : y = (((d : ℚ) : ℝ) : Surreal) + ((1 : Dyadic) : Surreal)
            * ω^ (-1 : Surreal) := by
          rw [h, Real.toSurreal_ratCast, dyadic_cast_one, one_mul]
        have hst : stdPart y = ((d : ℚ) : ℝ) := by
          rw [hval, stdPart_grid]
        refine ⟨1, ?_, by simp, fun hnd ↦ absurd hst (hnd d)⟩
        rw [hst]
        exact hval
      · -- y = d − ω⁻¹
        have hval : y = (((d : ℚ) : ℝ) : Surreal) + ((-1 : Dyadic) : Surreal)
            * ω^ (-1 : Surreal) := by
          rw [h, Real.toSurreal_ratCast, show ((-1 : Dyadic) : Surreal) = -((1 : Dyadic) : Surreal)
            from dyadic_cast_neg' 1, dyadic_cast_one]
          ring
        have hst : stdPart y = ((d : ℚ) : ℝ) := by
          rw [hval, stdPart_grid]
        refine ⟨-1, ?_, by simp, fun hnd ↦ absurd hst (hnd d)⟩
        rw [hst]
        exact hval
  | succ n ih =>
    intro y hy hb
    rcases lt_or_eq_of_le hb with hlt | heq
    · -- strictly earlier: use the inductive hypothesis
      have hb' : y.birthday ≤ NatOrdinal.of Ordinal.omega0 + (n : NatOrdinal) := by
        rw [← omega_add_nat_succ] at hlt
        exact Order.lt_add_one_iff.1 hlt
      obtain ⟨r, hr1, hr2, hr3⟩ := ih hy hb'
      exact ⟨r, hr1, by omega, fun h ↦ by have := hr3 h; omega⟩
    · -- the critical day: the census method
      set a := stdPart y with ha
      -- the branch-dependent coefficient bound and candidate price
      obtain ⟨B, hBle, hBnd, hcoef, hcand⟩ :
          ∃ B : ℕ, B ≤ n + 1 ∧
            ((∀ e : Dyadic, a ≠ ((e : ℚ) : ℝ)) → B ≤ n) ∧
            (∀ v : Surreal.{u}, IsFinite v →
              v.birthday ≤ NatOrdinal.of Ordinal.omega0 + (n : NatOrdinal) →
              stdPart v = a → ∃ s : Dyadic,
                v = ((a : ℝ) : Surreal) + (s : Surreal) * ω^ (-1 : Surreal) ∧
                  Dyadic.hgt s ≤ B) ∧
            (∀ t : Dyadic, Dyadic.hgt t ≤ B + 1 →
              (((a : ℝ) : Surreal) + (t : Surreal) * ω^ (-1 : Surreal)).birthday
                ≤ NatOrdinal.of Ordinal.omega0 + ((n + 1 : ℕ) : NatOrdinal)) := by
        by_cases hdy : ∃ e : Dyadic, a = ((e : ℚ) : ℝ)
        · obtain ⟨e, he⟩ := hdy
          refine ⟨n + 1, le_rfl, fun hnd ↦ absurd he (hnd e), ?_, ?_⟩
          · intro v hv hvb hvst
            obtain ⟨s, hs1, hs2, _⟩ := ih hv hvb
            exact ⟨s, by rwa [hvst] at hs1, hs2⟩
          · intro t ht
            rcases eq_or_ne t 0 with rfl | ht0
            · rw [dyadic_cast_zero, zero_mul, add_zero]
              refine (birthday_realCast_le a).trans ?_
              exact le_add_of_nonneg_right (by exact_mod_cast Nat.zero_le (n + 1))
            · have hcast : ((a : ℝ) : Surreal) = (e : Surreal) := by
                rw [he, Real.toSurreal_ratCast]
              rw [hcast]
              refine (birthday_dyadic_add_dyadic_mul_wpow_le e ht0).trans ?_
              refine add_le_add le_rfl ?_
              exact_mod_cast (by omega : Dyadic.hgt t - 1 ≤ n + 1)
        · push Not at hdy
          refine ⟨n, Nat.le_succ n, fun _ ↦ le_rfl, ?_, ?_⟩
          · intro v hv hvb hvst
            obtain ⟨s, hs1, _, hs3⟩ := ih hv hvb
            refine ⟨s, by rwa [hvst] at hs1, ?_⟩
            apply hs3
            rw [hvst]
            exact hdy
          · intro t ht
            refine (birthday_realCast_add_dyadic_mul_wpow_le a t).trans ?_
            refine add_le_add le_rfl ?_
            exact_mod_cast (by omega : Dyadic.hgt t ≤ n + 1)
      have hev : Infinitesimal (y - ((a : ℝ) : Surreal)) := infinitesimal_sub_stdPart hy
      obtain ⟨g, hgn, hgy, hgb⟩ := birthday_eq_iGameBirthday y
      haveI := hgn
      have hslt := Cut.supLeft_lt_infRight_of_numeric g
      -- birthday of any option
      have hopt : ∀ (p : Player) (i : IGame), i ∈ g.moves p →
          i.birthday ≤ NatOrdinal.of Ordinal.omega0 + (n : NatOrdinal) := by
        intro p i hi
        have h1 := IGame.birthday_lt_of_mem_moves hi
        rw [hgb, heq, ← omega_add_nat_succ] at h1
        exact Order.lt_add_one_iff.1 h1
      classical
      -- the coefficient sets of the halo options
      set S : Set Dyadic := {s | Dyadic.hgt s ≤ B ∧ ∃ i ∈ gᴸ, ∃ _ : i.Numeric,
        Surreal.mk i = ((a : ℝ) : Surreal) + (s : Surreal) * ω^ (-1 : Surreal)} with hS
      set S' : Set Dyadic := {s | Dyadic.hgt s ≤ B ∧ ∃ j ∈ gᴿ, ∃ _ : j.Numeric,
        Surreal.mk j = ((a : ℝ) : Surreal) + (s : Surreal) * ω^ (-1 : Surreal)} with hS'
      have hSfin : S.Finite := (Dyadic.finite_setOf_hgt_le B).subset (fun s hs ↦ hs.1)
      have hS'fin : S'.Finite := (Dyadic.finite_setOf_hgt_le B).subset (fun s hs ↦ hs.1)
      have hSS' : ∀ s ∈ S, ∀ s' ∈ S', s < s' := by
        rintro s ⟨_, i, hi, hin, hiv⟩ s' ⟨_, j, hj, hjn, hjv⟩
        haveI := hin
        haveI := hjn
        have h1 : Surreal.mk i < y := by
          rw [← hgy]
          exact mk_lt_mk.2 (IGame.Numeric.left_lt hi)
        have h2 : y < Surreal.mk j := by
          rw [← hgy]
          exact mk_lt_mk.2 (IGame.Numeric.lt_right hj)
        refine dyadic_lt_of_cast_mul_wpow_lt (h := ?_)
        rw [hiv] at h1
        rw [hjv] at h2
        linarith
      -- choose the candidate coefficient
      obtain ⟨t, htgt, htS, htS'⟩ : ∃ t : Dyadic, Dyadic.hgt t ≤ B + 1 ∧
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
      set c : Surreal := ((a : ℝ) : Surreal) + (t : Surreal) * ω^ (-1 : Surreal) with hc
      have hcfin : IsFinite c := isFinite_grid a t
      have hcb : c.birthday ≤ NatOrdinal.of Ordinal.omega0 + ((n + 1 : ℕ) : NatOrdinal) :=
        hcand t htgt
      -- the candidate fits the option cuts of the minimal game
      have hfitc : Cut.Fits c (Cut.supLeft g) (Cut.infRight g) := by
        rw [Cut.Fits, Set.mem_inter_iff]
        constructor
        · rw [Cut.right_supLeft]
          simp only [Set.mem_iInter, Set.mem_ofPred_eq]
          intro i hi
          haveI : i.Numeric := IGame.Numeric.of_mem_moves hi
          have hiy : Surreal.mk i < y := by
            rw [← hgy]
            exact mk_lt_mk.2 (IGame.Numeric.left_lt hi)
          have hib : (Surreal.mk i).birthday ≤ NatOrdinal.of Ordinal.omega0 + (n : NatOrdinal) :=
            (birthday_mk_le i).trans (hopt _ i hi)
          have hlt : Surreal.mk i < c := by
            by_cases hif : IsFinite (Surreal.mk i)
            · have hsti : stdPart (Surreal.mk i) ≤ a :=
                ha ▸ stdPart_monotoneOn hif hy hiy.le
              rcases eq_or_lt_of_le hsti with hstie | hstil
              · obtain ⟨s, hsv, hshgt⟩ := hcoef _ hif hib hstie
                have hst : s < t := htS s ⟨hshgt, i, hi, inferInstance, hsv⟩
                rw [hsv, hc]
                have := dyadic_mul_wpow_lt_dyadic_mul_wpow hst
                linarith
              · refine lt_of_stdPart_lt hif hcfin ?_
                rw [hc, stdPart_grid]
                exact hstil
            · exact lt_finite_of_not_isFinite_of_lt hif hiy hy hcfin
          rw [← toGame_mk, toGame_le_iff]
          exact not_le.2 hlt
        · rw [Cut.left_infRight]
          simp only [Set.mem_iInter, Set.mem_ofPred_eq]
          intro j hj
          haveI : j.Numeric := IGame.Numeric.of_mem_moves hj
          have hyj : y < Surreal.mk j := by
            rw [← hgy]
            exact mk_lt_mk.2 (IGame.Numeric.lt_right hj)
          have hjb : (Surreal.mk j).birthday ≤ NatOrdinal.of Ordinal.omega0 + (n : NatOrdinal) :=
            (birthday_mk_le j).trans (hopt _ j hj)
          have hlt : c < Surreal.mk j := by
            by_cases hjf : IsFinite (Surreal.mk j)
            · have hstj : a ≤ stdPart (Surreal.mk j) :=
                ha ▸ stdPart_monotoneOn hy hjf hyj.le
              rcases eq_or_lt_of_le hstj with hstje | hstjl
              · obtain ⟨s, hsv, hshgt⟩ := hcoef _ hjf hjb hstje.symm
                have hst : t < s := htS' s ⟨hshgt, j, hj, inferInstance, hsv⟩
                rw [hsv, hc]
                have := dyadic_mul_wpow_lt_dyadic_mul_wpow hst
                linarith
              · refine lt_of_stdPart_lt hcfin hjf ?_
                rw [hc, stdPart_grid]
                exact hstjl
            · exact finite_lt_of_not_isFinite_of_lt hjf hyj hy hcfin
          rw [← toGame_mk, toGame_le_iff]
          exact not_le.2 hlt
      -- simplest-fit uniqueness closes the induction
      have hy' : Cut.simplestBtwn hslt = y := by
        rw [← toGame_inj, Cut.simplestBtwn_supLeft_infRight hslt, ← hgy, toGame_mk]
      have hfity : Cut.Fits y (Cut.supLeft g) (Cut.infRight g) :=
        hy' ▸ Cut.fits_simplestBtwn hslt
      have hmin : ∀ v, Cut.Fits v (Cut.supLeft g) (Cut.infRight g) →
          y.birthday ≤ v.birthday := by
        intro v hv
        have h := Cut.birthday_simplestBtwn_le_of_fits hv
        rwa [hy'] at h
      have hyc : y = c :=
        (Cut.eq_of_fits_of_birthday_le hfity hfitc hmin (hcb.trans_eq heq.symm)).symm
      refine ⟨t, ?_, by omega, fun hnd ↦ ?_⟩
      · rw [hyc, hc]
      · have := hBnd hnd
        omega

/-- **The census below day `ω·2`, packaged**: a finite surreal born before day `ω·2`
lies on the dyadic `ω⁻¹`-grid over its standard part. -/
theorem eq_grid_of_isFinite_of_birthday_lt_omega_two {y : Surreal.{u}} (hy : IsFinite y)
    (hb : y.birthday < NatOrdinal.of Ordinal.omega0 + NatOrdinal.of Ordinal.omega0) :
    ∃ r : Dyadic, y = ((stdPart y : ℝ) : Surreal) + (r : Surreal) * ω^ (-1 : Surreal) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, y.birthday ≤ NatOrdinal.of Ordinal.omega0 + (n : NatOrdinal) := by
    rcases NatOrdinal.lt_add_iff.1 hb with ⟨b', hb', hle⟩ | ⟨c', hc', hle⟩
    · obtain ⟨n, rfl⟩ := NatOrdinal.lt_omega0.1 hb'
      exact ⟨n, by rwa [add_comm] at hle⟩
    · obtain ⟨n, rfl⟩ := NatOrdinal.lt_omega0.1 hc'
      exact ⟨n, hle⟩
  obtain ⟨r, hr, -, -⟩ := eq_grid_of_isFinite_of_birthday_le n hy hn
  exact ⟨r, hr⟩

/-! ### The census as an iff, and exact birthdays on the grid -/

/-- **The grid census as an iff** — the census-iff format at every day `ω + n`
simultaneously (for finite surreals): born by day `ω + n` exactly when the coefficient
over the standard part has height at most `n + 1` (at most `n` over a non-dyadic
standard part). -/
theorem isFinite_birthday_le_omega0_add_iff {y : Surreal.{u}} (hy : IsFinite y) (n : ℕ) :
    y.birthday ≤ NatOrdinal.of Ordinal.omega0 + (n : NatOrdinal) ↔
      ∃ r : Dyadic, y = ((stdPart y : ℝ) : Surreal) + (r : Surreal) * ω^ (-1 : Surreal) ∧
        Dyadic.hgt r ≤ n + 1 ∧
        ((∀ e : Dyadic, stdPart y ≠ ((e : ℚ) : ℝ)) → Dyadic.hgt r ≤ n) := by
  constructor
  · exact eq_grid_of_isFinite_of_birthday_le n hy
  · rintro ⟨r, hval, _, h2⟩
    by_cases hdy : ∃ e : Dyadic, stdPart y = ((e : ℚ) : ℝ)
    · obtain ⟨e, he⟩ := hdy
      rcases eq_or_ne r 0 with rfl | hr0
      · rw [hval, dyadic_cast_zero, zero_mul, add_zero, he, Real.toSurreal_ratCast]
        refine le_trans ?_ (le_add_of_nonneg_right (by exact_mod_cast Nat.zero_le n))
        exact (birthday_dyadic_lt_omega0 e).le
      · rw [hval, he, Real.toSurreal_ratCast]
        refine (birthday_dyadic_add_dyadic_mul_wpow_le e hr0).trans (add_le_add le_rfl ?_)
        exact_mod_cast (by omega : Dyadic.hgt r - 1 ≤ n)
    · push Not at hdy
      rw [hval]
      refine (birthday_realCast_add_dyadic_mul_wpow_le _ r).trans (add_le_add le_rfl ?_)
      exact_mod_cast (h2 hdy)

theorem dyadic_cast_inj {r s : Dyadic} (h : (r : Surreal) = (s : Surreal)) : r = s := by
  rcases lt_trichotomy r s with hrs | hrs | hrs
  · exact absurd (dyadic_cast_lt hrs) (by rw [h]; exact lt_irrefl _)
  · exact hrs
  · exact absurd (dyadic_cast_lt hrs) (by rw [h]; exact lt_irrefl _)

theorem dyadic_cast_ne_zero {r : Dyadic} (hr : r ≠ 0) : (r : Surreal) ≠ 0 := by
  intro h
  apply hr
  refine dyadic_cast_inj (s := 0) ?_
  rw [h, dyadic_cast_zero]

theorem isFinite_dyadic_cast (d : Dyadic) : IsFinite ((d : Surreal)) := by
  show IsFinite (((d : ℚ) : Surreal))
  exact isFinite_ratCast _

/-- Distinct coefficients give distinct grid points. -/
theorem grid_coeff_unique {a : ℝ} {r s : Dyadic}
    (h : (a : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)
      = (a : Surreal) + (s : Surreal) * ω^ (-1 : Surreal)) : r = s := by
  have h1 : (r : Surreal) * ω^ (-1 : Surreal) = (s : Surreal) * ω^ (-1 : Surreal) := by
    linarith
  exact dyadic_cast_inj (mul_right_cancel₀ (wpow_ne_zero _) h1)

private theorem mk_dyadic_cast_of_ne_zero' {c : Dyadic} (hc : c ≠ 0) :
    ArchimedeanClass.mk ((c : Surreal)) = 0 := by
  have h : ((c : Dyadic) : Surreal) = (((c : ℚ) : ℝ) : Surreal) := by
    rw [← Real.toSurreal_ratCast]
  rw [h]
  refine mk_realCast ?_
  intro h0
  apply hc
  have h1 : (c : ℚ) = (0 : ℚ) := by exact_mod_cast h0
  ext
  rw [h1]
  norm_num

/-- **The exact birthday of every grid point over a dyadic anchor**:
`d + r·ω⁻¹` is born exactly on day `ω + (hgt r − 1)` for `r ≠ 0`. In particular the
height function `hgt` of `Infinity.Census` computes genuine birthdays over dyadic
anchors: the upper bounds of `Infinity.HaloRealization` are tight. -/
theorem birthday_grid_dyadic_eq (d : Dyadic) {r : Dyadic} (hr : r ≠ 0) :
    ((d : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)).birthday
      = NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt r - 1 : ℕ) : NatOrdinal) := by
  refine le_antisymm (birthday_dyadic_add_dyadic_mul_wpow_le d hr) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hgt1 := Dyadic.hgt_pos_of_ne_zero hr
  have hcastd : ((d : Dyadic) : Surreal) = ((((d : ℚ) : ℝ)) : Surreal) := by
    rw [← Real.toSurreal_ratCast]
  have hyfin : IsFinite ((d : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)) :=
    (isFinite_dyadic_cast d).add (infinitesimal_dyadic_mul_wpow r).isFinite
  have hst : stdPart ((d : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)) = ((d : ℚ) : ℝ) := by
    rw [hcastd]
    exact stdPart_grid _ r
  rcases eq_or_lt_of_le (show 1 ≤ Dyadic.hgt r from hgt1) with h1 | h2
  · -- height 1: below day `ω` only dyadics live
    have hΩ : ((d : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)).birthday
        < NatOrdinal.of Ordinal.omega0 := by
      have h0 : ((Dyadic.hgt r - 1 : ℕ) : NatOrdinal) = 0 := by
        exact_mod_cast (by omega : Dyadic.hgt r - 1 = 0)
      rwa [h0, add_zero] at hcon
    obtain ⟨e, he⟩ := birthday_lt_omega0_iff.1 hΩ
    have he' : ((e : Dyadic) : Surreal) = (d : Surreal) + (r : Surreal) * ω^ (-1 : Surreal) :=
      he
    have hsub : (r : Surreal) * ω^ (-1 : Surreal) = ((e - d : Dyadic) : Surreal) := by
      rw [dyadic_cast_sub']
      linarith [he'.symm]
    have hed : (e - d : Dyadic) ≠ 0 := by
      intro h0
      rw [h0, dyadic_cast_zero] at hsub
      exact absurd hsub (mul_ne_zero (dyadic_cast_ne_zero hr) (wpow_ne_zero _))
    have hmk0 : ArchimedeanClass.mk ((r : Surreal) * ω^ (-1 : Surreal)) = 0 := by
      rw [hsub]
      exact mk_dyadic_cast_of_ne_zero' hed
    have hmkpos := infinitesimal_def.1 (infinitesimal_dyadic_mul_wpow r)
    rw [hmk0] at hmkpos
    exact absurd hmkpos (lt_irrefl _)
  · -- height at least 2: the census one day earlier forbids the point
    have hb2 : ((d : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)).birthday
        ≤ NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt r - 2 : ℕ) : NatOrdinal) := by
      have hstep : NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt r - 1 : ℕ) : NatOrdinal)
          = (NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt r - 2 : ℕ) : NatOrdinal)) + 1 := by
        rw [omega_add_nat_succ]
        congr 1
        exact_mod_cast (by omega : Dyadic.hgt r - 1 = Dyadic.hgt r - 2 + 1)
      rw [hstep] at hcon
      exact Order.lt_add_one_iff.1 hcon
    obtain ⟨r', hval', hh1', _⟩ :=
      eq_grid_of_isFinite_of_birthday_le (Dyadic.hgt r - 2) hyfin hb2
    rw [hst, ← hcastd] at hval'
    have hrr : r' = r := by
      refine dyadic_cast_inj (mul_right_cancel₀ (wpow_ne_zero (-1 : Surreal)) ?_)
      linarith [hval'.symm]
    rw [hrr] at hh1'
    omega

/-- **The exact birthday of every grid point over a non-dyadic real anchor**:
`a + r·ω⁻¹` is born exactly on day `ω + hgt r` when `a` is not a dyadic rational.
For `r = 0` this is the exact birthday of a non-dyadic real (day `ω`); for `r = ±1` it
certifies the day-`ω + 1` newborns `a ± ω⁻¹` over every non-dyadic real. -/
theorem birthday_grid_realCast_eq {a : ℝ} (hnd : ∀ e : Dyadic, a ≠ ((e : ℚ) : ℝ))
    (r : Dyadic) :
    ((a : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)).birthday
      = NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt r : ℕ) : NatOrdinal) := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [dyadic_cast_zero, zero_mul, add_zero]
    have h := birthday_realCast_eq hnd
    rw [h]
    have h0 : ((Dyadic.hgt 0 : ℕ) : NatOrdinal) = 0 := by
      exact_mod_cast Dyadic.hgt_zero
    rw [h0, add_zero]
  · refine le_antisymm (birthday_realCast_add_dyadic_mul_wpow_le a r) ?_
    by_contra hcon
    rw [not_le] at hcon
    have hgt1 := Dyadic.hgt_pos_of_ne_zero hr
    have hyfin : IsFinite ((a : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)) :=
      isFinite_grid a r
    have hst : stdPart ((a : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)) = a :=
      stdPart_grid a r
    have hb2 : ((a : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)).birthday
        ≤ NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt r - 1 : ℕ) : NatOrdinal) := by
      have hstep : NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt r : ℕ) : NatOrdinal)
          = (NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt r - 1 : ℕ) : NatOrdinal)) + 1 := by
        rw [omega_add_nat_succ]
        congr 1
        exact_mod_cast (by omega : Dyadic.hgt r = Dyadic.hgt r - 1 + 1)
      rw [hstep] at hcon
      exact Order.lt_add_one_iff.1 hcon
    obtain ⟨r', hval', _, hh2'⟩ :=
      eq_grid_of_isFinite_of_birthday_le (Dyadic.hgt r - 1) hyfin hb2
    rw [hst] at hval'
    have hrr : r' = r := grid_coeff_unique hval'.symm
    have := hh2' (by rw [hst]; exact hnd)
    rw [hrr] at this
    omega

/-! ### The geometric ladder: the halo of `ω/(ω−1)` is empty below day `ω·2` -/

private theorem wpow_neg_one_eq_eps0' : ω^ (-1 : Surreal.{0}) = eps0 := by
  rw [eps0_def, show (-1 : Surreal.{0}) = -(1 : Surreal) from rfl, wpow_neg]

private theorem eps0_infinitesimal' : Infinitesimal eps0 := by
  rw [eps0_def]
  exact infinitesimal_inv_wpow one_pos

private theorem eps0_pos' : (0 : Surreal.{0}) < eps0 := by
  rw [eps0_def]
  exact inv_pos.2 (wpow_pos _)

private theorem partialSum_geom_one' : partialSum (fun k ↦ eps0 ^ k) 1 = 1 := by
  rw [partialSum, Finset.sum_range_one, pow_zero]

private theorem partialSum_geom_two' : partialSum (fun k ↦ eps0 ^ k) 2 = 1 + eps0 := by
  rw [partialSum, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]

private theorem partialSum_geom_three' :
    partialSum (fun k ↦ eps0 ^ k) 3 = 1 + eps0 + eps0 ^ 2 := by
  rw [partialSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    pow_zero, pow_one]

/-- **The uniform step of the geometric ladder**: every Hahn sum of the geometric
series `Σ ω⁻ᵏ` is born at or after day `ω·2`. By the grid census, anything finite born
earlier is `1 + r·ω⁻¹` for a dyadic `r` (its standard part being `1`); the stage-`2`
domination residual forces `r = 1`, and `1 + ω⁻¹` already fails the stage-`3` residual.
This single theorem leaps past the day-`ω+n` censuses for every `n` at once —
the halo of `ω/(ω−1)` is empty throughout `[ω, ω·2)`. -/
theorem omega0_add_omega0_le_birthday_of_isHahnSum_geometric {w : Surreal.{0}}
    (hw : IsHahnSum (fun k ↦ eps0 ^ k) w) :
    NatOrdinal.of Ordinal.omega0 + NatOrdinal.of Ordinal.omega0 ≤ w.birthday := by
  by_contra hcon
  rw [not_le] at hcon
  -- `w` is infinitesimally close to `1`
  have hinf : Infinitesimal (w - 1) := by
    have h1 := hw 1
    rw [partialSum_geom_one'] at h1
    simp only [pow_one] at h1
    exact lt_of_lt_of_le eps0_infinitesimal' h1
  have hfin : IsFinite w := by
    have h : w = 1 + (w - 1) := by ring
    rw [h]
    exact isFinite_one.add hinf.isFinite
  have hst : stdPart w = 1 := by
    have h : w = 1 + (w - 1) := by ring
    rw [h, stdPart_add_eq_left hinf, ArchimedeanClass.stdPart_one]
  -- the census puts `w` on the grid over `1`
  obtain ⟨r, hr⟩ := eq_grid_of_isFinite_of_birthday_lt_omega_two hfin hcon
  rw [hst, Real.toSurreal_one] at hr
  -- stage 2 forces the coefficient to be `1`
  have hr1 : r = 1 := by
    by_contra hne
    have h2 := hw 2
    rw [partialSum_geom_two'] at h2
    have hval : w - (1 + eps0) = ((r - 1 : Dyadic) : Surreal) * ω^ (-1 : Surreal) := by
      rw [hr, dyadic_cast_sub', dyadic_cast_one, sub_mul, one_mul, wpow_neg_one_eq_eps0']
      ring
    rw [hval] at h2
    have hne' : (r - 1 : Dyadic) ≠ 0 := by
      intro h0
      apply hne
      have : r - 1 + 1 = (0 : Dyadic) + 1 := by rw [h0]
      simpa using this
    have hmk : ArchimedeanClass.mk (((r - 1 : Dyadic) : Surreal) * ω^ (-1 : Surreal))
        = ArchimedeanClass.mk (eps0 ^ 1) := by
      rw [ArchimedeanClass.mk_mul, mk_dyadic_cast_of_ne_zero' hne', zero_add, pow_one,
        wpow_neg_one_eq_eps0']
    rw [hmk] at h2
    exact absurd h2 (not_le.2 (mk_pow_lt_mk_pow_succ eps0_infinitesimal' eps0_pos' 1))
  -- and `1 + ω⁻¹` fails stage 3
  have h3 := hw 3
  rw [partialSum_geom_three', hr, hr1, dyadic_cast_one, one_mul, wpow_neg_one_eq_eps0'] at h3
  have hval : 1 + eps0 - (1 + eps0 + eps0 ^ 2) = -(eps0 ^ 2) := by ring
  rw [hval, ArchimedeanClass.mk_neg] at h3
  exact absurd h3 (not_le.2 (mk_pow_lt_mk_pow_succ eps0_infinitesimal' eps0_pos' 2))

/-- The ordinal form: every Hahn sum of the geometric series is born at or after
day `ω·2`. -/
theorem omega0_mul_two_le_birthday_of_isHahnSum_geometric {w : Surreal.{0}}
    (hw : IsHahnSum (fun k ↦ eps0 ^ k) w) :
    NatOrdinal.of (Ordinal.omega0 * 2) ≤ w.birthday := by
  have h2 : Ordinal.omega0 * 2 = Ordinal.omega0 + Ordinal.omega0 := by
    rw [show (2 : Ordinal) = 1 + 1 from (one_add_one_eq_two).symm, mul_add, mul_one]
  rw [h2]
  exact (NatOrdinal.oadd_le_add' _ _).trans
    (omega0_add_omega0_le_birthday_of_isHahnSum_geometric hw)

/-- **The canonical geometric sum is born at or after day `ω·2`** — the uniform ladder
step applied to `hahnSum (Σ ω⁻ᵏ)` itself. The halo-minimality conjecture
(`hahnSum (Σ ω⁻ᵏ) = ω/(ω−1)`) is now squeezed into the window
`[ω·2, birthday (ω/(ω−1))]`: what remains is emptiness of the halo on
`[ω·2, birthday (ω/(ω−1)))` — which needs the day-`ω·2 + n` censuses (the `ω⁻²`-grid
and beyond) — together with the matching upper bound for `ω/(ω−1)` itself. -/
theorem omega0_mul_two_le_birthday_hahnSum_geometric :
    NatOrdinal.of (Ordinal.omega0 * 2) ≤ (hahnSum geometric_strict_dominating).birthday :=
  omega0_mul_two_le_birthday_of_isHahnSum_geometric
    (isHahnSum_hahnSum geometric_strict_dominating)

end Surreal

end
