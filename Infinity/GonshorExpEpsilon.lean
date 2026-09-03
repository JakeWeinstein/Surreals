/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.GonshorExpTower

/-!
# `ε₀`: the first `ω`-map fixed point, and `exp ε₀ = ω^(ω^(ε₀+1))`

The finale of the Gonshor ladder. We construct `ε₀` as the left-cut of the finite
`ω`-towers `{1, ω, ω^ω, ω^(ω^ω), …}` and prove:

* `Surreal.wpow_epsilon0` — **`ω^ε₀ = ε₀`**: the first machine-checked fixed point of
  surreal `ω`-exponentiation. (By Gonshor ch. 9 the fixed points of the `ω`-map are the
  generalized ε-numbers; this verifies the first one exists and is this cut.)
* `Surreal.gonshorExp_epsilon0` — **`exp ε₀ = ω^(ω^(ε₀+1)) ≠ ε₀`**: the survey's
  (Mantova–Matusinski §2.3) displayed computation of `exp ε₀`, machine-checked. This is
  the first verified value where Gonshor's `exp` *diverges* from the `ω`-map — the
  `g ≠ id` phenomenon at an ε-number, and the reason `exp` has no fixed points while `Ω`
  does.

The seed values used at the left options of `ε₀ = !{1, ω, ω^ω, … | ∅}` are
`exp 1 = e` (the real exponential) and `exp (ω^b) = ω^(ω^b)` for the towers `b < ε₀`
(Gonshor Thm 10.17, `g = id` strictly below `ε₀`; the instances `exp ω = ω^ω` and
`exp ω² = ω^(ω²)` are themselves verified in `GonshorExp`/`GonshorExpTower`). As
throughout, this is the evaluation of Gonshor's recursion given its values at earlier
arguments — see `notes/gonshor-exp-design.md` for the honest scope.
-/

open Set IGame

noncomputable section

namespace Surreal

/-! ### The finite `ω`-towers -/

/-- The finite `ω`-towers: `wtower 0 = 1`, `wtower (n+1) = ω^(wtower n)` —
`1, ω, ω^ω, ω^(ω^ω), …`. -/
def wtower : ℕ → Surreal
  | 0 => 1
  | n + 1 => ω^ (wtower n)

@[simp]
theorem wtower_zero : wtower 0 = 1 := rfl

theorem wtower_succ (n : ℕ) : wtower (n + 1) = ω^ (wtower n) := rfl

theorem wtower_pos (n : ℕ) : 0 < wtower n := by
  cases n with
  | zero => exact one_pos
  | succ n => exact wpow_pos _

theorem wtower_lt_succ (n : ℕ) : wtower n < wtower (n + 1) := by
  induction n with
  | zero =>
    rw [wtower_succ, wtower_zero]
    simpa using natCast_lt_wpow_one 1
  | succ n ih =>
    rw [wtower_succ (n + 1), wtower_succ n]
    exact wpow_lt_wpow.2 ih

theorem mk_wtower_succ_neg (n : ℕ) :
    ArchimedeanClass.mk (wtower (n + 1)) < 0 := by
  rw [wtower_succ]
  exact mk_wpow_lt_zero (wtower_pos n)

/-- Each tower plus one is still below the next tower. -/
theorem wtower_add_one_lt (n : ℕ) : wtower n + 1 < wtower (n + 1) := by
  cases n with
  | zero =>
    rw [wtower_zero, wtower_succ, wtower_zero]
    have h := natCast_lt_wpow_one 2
    push_cast at h
    linarith
  | succ m =>
    have h1 : ArchimedeanClass.mk (wtower (m + 1) + 1) =
        ArchimedeanClass.mk (wtower (m + 1)) := by
      apply ArchimedeanClass.mk_add_eq_mk_left
      rw [ArchimedeanClass.mk_one]
      exact mk_wtower_succ_neg m
    have hmk : ArchimedeanClass.mk (wtower (m + 1 + 1)) <
        ArchimedeanClass.mk (wtower (m + 1) + 1) := by
      rw [h1, wtower_succ (m + 1), wtower_succ m]
      exact archimedeanClassMk_wpow_strictAnti (wtower_lt_succ m)
    exact lt_of_mk_lt_of_pos hmk (wtower_pos _)

/-! ### `ε₀` and the fixed-point theorem -/

/-- `ε₀`: the left-cut of the finite `ω`-towers. -/
def epsilon0 : Surreal := !{Set.range wtower | ∅}

theorem wtower_lt_epsilon0 (n : ℕ) : wtower n < epsilon0 :=
  lt_ofSets_of_mem_left ⟨n, rfl⟩

theorem epsilon0_pos : 0 < epsilon0 :=
  lt_trans one_pos (by simpa using wtower_lt_epsilon0 0)

/-- **`ε₀` is a fixed point of the `ω`-map**: `ω^ε₀ = ε₀`. The first machine-checked
fixed point of surreal exponentiation with base `ω` (the first generalized ε-number,
Gonshor ch. 9). -/
theorem wpow_epsilon0 : ω^ epsilon0 = epsilon0 := by
  rw [epsilon0, wpow_ofSets]
  apply ofSets_left_eq_of_cofinal
  · rintro z (rfl | ⟨r, hr, x, ⟨n, rfl⟩, rfl⟩)
    · exact ⟨wtower 0, ⟨0, rfl⟩, by simp⟩
    · refine ⟨wtower (n + 2), ⟨n + 2, rfl⟩, le_of_lt ?_⟩
      show (r : Surreal) * ω^ (wtower n) < wtower (n + 2)
      rw [wtower_succ (n + 1), ← Real.toSurreal_ratCast]
      exact mul_wpow_lt_wpow _ (wtower_lt_succ n)
  · rintro z ⟨n, rfl⟩
    refine ⟨((1 : Dyadic) : Surreal) * ω^ (wtower n),
      Set.mem_insert_of_mem _ (Set.mem_image2_of_mem (by norm_num) ⟨n, rfl⟩), ?_⟩
    have hone : ((1 : Dyadic) : Surreal) = 1 := by norm_cast
    rw [hone, one_mul, ← wtower_succ]
    exact (wtower_lt_succ n).le

theorem mk_epsilon0_neg : ArchimedeanClass.mk epsilon0 < 0 := by
  rw [← wpow_epsilon0]
  exact mk_wpow_lt_zero epsilon0_pos

theorem wlog_epsilon0 : wlog epsilon0 = epsilon0 := by
  conv_lhs => rw [← wpow_epsilon0]
  exact wlog_wpow _

/-- Every tower is negligible next to `ε₀`: `mk (ε₀ − wtower n) = mk ε₀`. -/
theorem mk_epsilon0_sub_wtower (n : ℕ) :
    ArchimedeanClass.mk (epsilon0 - wtower n) = ArchimedeanClass.mk epsilon0 := by
  rw [sub_eq_add_neg]
  apply ArchimedeanClass.mk_add_eq_mk_left
  rw [ArchimedeanClass.mk_neg]
  cases n with
  | zero =>
    rw [wtower_zero, ArchimedeanClass.mk_one]
    exact mk_epsilon0_neg
  | succ m =>
    rw [wtower_succ]
    conv_lhs => rw [← wpow_epsilon0]
    exact archimedeanClassMk_wpow_strictAnti (wtower_lt_epsilon0 m)

theorem not_isFinite_epsilon0_sub_wtower (n : ℕ) :
    ¬ IsFinite (epsilon0 - wtower n) := by
  intro h
  have h0 := isFinite_def.1 h
  rw [mk_epsilon0_sub_wtower n] at h0
  exact absurd h0 (not_le.2 mk_epsilon0_neg)

theorem wlog_epsilon0_sub_wtower (n : ℕ) :
    wlog (epsilon0 - wtower n) = epsilon0 := by
  have h := wlog_congr (veq_def.2 (mk_epsilon0_sub_wtower n))
  rw [h, wlog_epsilon0]

/-- `ε₀ + 1` is the left-cut of `{ε₀}` (its day-(ε₀+1) representation). -/
theorem epsilon0_add_one_rep :
    epsilon0 + 1 = !{({epsilon0} : Set Surreal) | ∅} := by
  rw [ofSets_left_add (rfl : epsilon0 = !{Set.range wtower | ∅}) one_def]
  apply ofSets_left_eq_of_cofinal
  · rintro z (⟨w, ⟨n, rfl⟩, rfl⟩ | ⟨w, hw, rfl⟩)
    · exact ⟨epsilon0, Set.mem_singleton _,
        le_of_lt ((wtower_add_one_lt n).trans (wtower_lt_epsilon0 (n + 1)))⟩
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨epsilon0, Set.mem_singleton _, le_of_eq (add_zero _)⟩
  · rintro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨epsilon0 + 0,
      Set.mem_union_right _ (Set.mem_image_of_mem _ (Set.mem_singleton 0)),
      le_of_eq (add_zero _).symm⟩

/-! ### The exponential of `ε₀` -/

/-- The seed values of Gonshor's recursion at the left options of `ε₀`:
`exp 1 = e` and `exp (ω^b) = ω^(ω^b)` for the towers `b` (Gonshor Thm 10.17 — `g = id`
strictly below `ε₀`; the first instances are verified in this development). -/
def expWtower : ℕ → Surreal
  | 0 => ((Real.exp 1 : ℝ) : Surreal)
  | n + 1 => wtower (n + 2)

theorem expWtower_pos (n : ℕ) : 0 < expWtower n := by
  cases n with
  | zero => exact (by simpa using Real.exp_pos 1 : (0 : Surreal) < ((Real.exp 1 : ℝ) : Surreal))
  | succ n => exact wtower_pos _

theorem wlog_expWtower_zero : wlog (expWtower 0) = 0 :=
  wlog_realCast _

theorem wlog_expWtower_succ (n : ℕ) : wlog (expWtower (n + 1)) = wtower (n + 1) := by
  show wlog (wtower (n + 2)) = wtower (n + 1)
  rw [wtower_succ (n + 1)]
  exact wlog_wpow _

/-- **The exponential of `ε₀` is `ω^(ω^(ε₀+1))`** — in particular `exp ε₀ ≠ ε₀`. At the
representation `ε₀ = !{1, ω, ω^ω, … | ∅}`, Gonshor's genetic formula — seeded with
`exp 1 = e` and `exp (ω^b) = ω^(ω^b)` at the towers — evaluates to `ω^(ω^(ε₀+1))`
(the survey's displayed computation). The first verified value where `exp` diverges from
the `ω`-map: `g(ε₀) = ε₀ + 1 ≠ ε₀`. -/
theorem gonshorExp_epsilon0 :
    (!{insert 0 (Set.range fun p : ℕ × ℕ ↦
        expWtower p.1 * expPartial p.2 (epsilon0 - wtower p.1)) | ∅} : Surreal)
      = ω^ ω^ (epsilon0 + 1) := by
  have h := gonshorCut_eq_wpow (a := epsilon0) (s := wtower) (v := expWtower)
    expWtower_pos wtower_lt_epsilon0 not_isFinite_epsilon0_sub_wtower
  have hexp : (!{Set.range fun p : ℕ × ℕ ↦
      wlog (expWtower p.1) + (p.2 : Surreal) * wlog (epsilon0 - wtower p.1) | ∅} : Surreal)
      = ω^ (epsilon0 + 1) := by
    rw [epsilon0_add_one_rep, wpow_ofSets]
    apply ofSets_left_eq_of_cofinal
    · rintro z ⟨⟨n, k⟩, rfl⟩
      cases n with
      | zero =>
        refine ⟨(((k + 1 : ℕ) : Dyadic) : Surreal) * ω^ epsilon0,
          Set.mem_insert_of_mem _
            (Set.mem_image2_of_mem ?_ (Set.mem_singleton _)), ?_⟩
        · rw [Set.mem_Ioi]
          exact_mod_cast Nat.succ_pos k
        · show wlog (expWtower 0) +
            ((k : ℕ) : Surreal) * wlog (epsilon0 - wtower 0) ≤
            (((k + 1 : ℕ) : Dyadic) : Surreal) * ω^ epsilon0
          rw [wlog_expWtower_zero, wlog_epsilon0_sub_wtower, zero_add, wpow_epsilon0]
          have hcast : (((k + 1 : ℕ) : Dyadic) : Surreal) = ((k + 1 : ℕ) : Surreal) := by
            norm_cast
          rw [hcast]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k)
            epsilon0_pos.le
      | succ m =>
        refine ⟨(((k + 2 : ℕ) : Dyadic) : Surreal) * ω^ epsilon0,
          Set.mem_insert_of_mem _
            (Set.mem_image2_of_mem ?_ (Set.mem_singleton _)), ?_⟩
        · rw [Set.mem_Ioi]
          exact_mod_cast Nat.succ_pos (k + 1)
        · show wlog (expWtower (m + 1)) +
            ((k : ℕ) : Surreal) * wlog (epsilon0 - wtower (m + 1)) ≤
            (((k + 2 : ℕ) : Dyadic) : Surreal) * ω^ epsilon0
          rw [wlog_expWtower_succ, wlog_epsilon0_sub_wtower, wpow_epsilon0]
          have hcast1 : (((k + 2 : ℕ) : Dyadic) : Surreal) = ((k + 2 : ℕ) : Surreal) := by
            norm_cast
          have hcast2 : ((k + 2 : ℕ) : Surreal) = ((k : ℕ) : Surreal) + 2 := by
            push_cast
            ring
          rw [hcast1, hcast2, add_mul]
          have h1 : wtower (m + 1) ≤ epsilon0 := (wtower_lt_epsilon0 (m + 1)).le
          have h2 : (0 : Surreal) < epsilon0 := epsilon0_pos
          linarith
    · rintro z (rfl | ⟨r, hr, x, hx, rfl⟩)
      · refine ⟨_, ⟨((0 : ℕ), (0 : ℕ)), rfl⟩, ?_⟩
        show (0 : Surreal) ≤ wlog (expWtower 0) +
          ((0 : ℕ) : Surreal) * wlog (epsilon0 - wtower 0)
        rw [wlog_expWtower_zero, wlog_epsilon0_sub_wtower]
        simp
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        obtain ⟨j, hj⟩ := exists_nat_ge (r : ℚ)
        refine ⟨_, ⟨((0 : ℕ), j), rfl⟩, ?_⟩
        show (r : Surreal) * ω^ epsilon0 ≤ wlog (expWtower 0) +
          ((j : ℕ) : Surreal) * wlog (epsilon0 - wtower 0)
        rw [wlog_expWtower_zero, wlog_epsilon0_sub_wtower, zero_add, wpow_epsilon0]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) epsilon0_pos.le
  exact h.trans (by rw [hexp])

/-- `exp ε₀ ≠ ε₀`: unlike the `ω`-map, `exp` does not fix `ε₀` (`exp` has no fixed
points at all — Gonshor; here is the first checked witness). -/
theorem gonshorExp_epsilon0_ne :
    (!{insert 0 (Set.range fun p : ℕ × ℕ ↦
        expWtower p.1 * expPartial p.2 (epsilon0 - wtower p.1)) | ∅} : Surreal)
      ≠ epsilon0 := by
  rw [gonshorExp_epsilon0]
  intro hcon
  have h1 : ω^ (epsilon0 + 1) = epsilon0 := by
    have := congrArg wlog hcon
    rwa [wlog_wpow, wlog_epsilon0] at this
  have h2 : epsilon0 + 1 = epsilon0 := by
    have := congrArg wlog h1
    rwa [wlog_wpow, wlog_epsilon0] at this
  simp at h2

end Surreal
