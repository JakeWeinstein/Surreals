/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.GonshorExp

/-!
# The Gonshor tower: `exp (ω·m) = (ω^ω)^m` and `exp (ω²) = ω^(ω²)`

`Infinity.GonshorExp` verified the evaluation of Gonshor's genetic exponential at limit
arguments (`gonshorCut_eq_wpow`) and its flagship instance `exp ω = ω^ω`. This file climbs
the next rungs of Gonshor's ladder, showing the limit-step theorem *composes*: each rung
consumes the previous rung's values as seed data, exactly as the genetic recursion does.

* `Surreal.ofSets_left_add` — addition of left-cuts: Conway's sum formula at the `Surreal`
  level, for cuts with no right options.
* `Surreal.wpow_one_mul_natCast_rep` — `ω·(m+1) = !{ω·m + n | ∅}` (the canonical
  representation of the additive ladder above `ω`).
* `Surreal.gonshorExp_omega_mul` — **`exp (ω·(m+1)) = (ω^ω)^(m+1)`**: Gonshor's formula
  at `ω·(m+1) = !{ω·m + n | ∅}`, seeded with `exp (ω·m + n) = (ω^ω)^m·eⁿ`, evaluates to
  `(ω^ω)^(m+1)` — an infinite family of checked exponential values, one per rung.
* `Surreal.two_eq_ofSets_one`, `Surreal.wpow_two_rep` — `2 = !{1 | ∅}` and
  `ω² = !{ω·n | ∅}`.
* `Surreal.gonshorExp_omega_sq` — **`exp (ω²) = ω^(ω²)`**: the first rung at a limit of
  limits, seeded with the `gonshorExp_omega_mul` values `exp (ω·n) = (ω^ω)^n`.

As in `GonshorExp`, these are evaluations of Gonshor's recursion given its values at
earlier arguments — the honest scope is documented in `notes/gonshor-exp-design.md`.
-/

open Set IGame

noncomputable section

namespace Surreal

/-! ### Addition of left-cuts -/

/-- **Conway addition of left-cuts.** If `x = !{A | ∅}` and `y = !{B | ∅}`, then
`x + y = !{(A + y) ∪ (x + B) | ∅}` — Conway's genetic sum formula, at the `Surreal`
level, in the right-optionless case. -/
theorem ofSets_left_add {A B : Set Surreal} [Small.{u} A] [Small.{u} B] {x y : Surreal}
    (hx : x = !{A | ∅}) (hy : y = !{B | ∅}) :
    x + y = !{(· + y) '' A ∪ (x + ·) '' B | ∅} := by
  haveI := numeric_ofSets_out_left A
  haveI := numeric_ofSets_out_left B
  haveI := numeric_ofSets_out_left ((· + y) '' A ∪ (x + ·) '' B)
  have hxm : x = Surreal.mk (!{Surreal.out '' A | (∅ : Set IGame)}) := by
    rw [hx, surreal_ofSets_left_rep]
  have hym : y = Surreal.mk (!{Surreal.out '' B | (∅ : Set IGame)}) := by
    rw [hy, surreal_ofSets_left_rep]
  rw [surreal_ofSets_left_rep ((· + y) '' A ∪ (x + ·) '' B)]
  conv_lhs => rw [hxm, hym, ← Surreal.mk_add]
  apply Surreal.mk_eq
  apply equiv_of_exists_le
  · rw [moves_add, leftMoves_ofSets, leftMoves_ofSets]
    rintro a (⟨w, ⟨u, hu, rfl⟩, rfl⟩ | ⟨w, ⟨u, hu, rfl⟩, rfl⟩)
    · refine ⟨Surreal.out (u + y), ?_, ?_⟩
      · rw [leftMoves_ofSets]
        exact Set.mem_image_of_mem _ (Set.mem_union_left _ (Set.mem_image_of_mem _ hu))
      · rw [← Surreal.mk_le_mk]
        simp only [Surreal.mk_add, Surreal.out_eq, ← hym]
        exact le_rfl
    · refine ⟨Surreal.out (x + u), ?_, ?_⟩
      · rw [leftMoves_ofSets]
        exact Set.mem_image_of_mem _ (Set.mem_union_right _ (Set.mem_image_of_mem _ hu))
      · rw [← Surreal.mk_le_mk]
        simp only [Surreal.mk_add, Surreal.out_eq, ← hxm]
        exact le_rfl
  · intro a ha
    rw [moves_add] at ha
    simp only [rightMoves_ofSets, Set.image_empty, Set.union_self,
      Set.mem_empty_iff_false] at ha
  · rw [leftMoves_ofSets]
    rintro b ⟨w, hw, rfl⟩
    rcases hw with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · refine ⟨Surreal.out u + !{Surreal.out '' B | (∅ : Set IGame)}, ?_, ?_⟩
      · refine add_right_mem_moves_add ?_ _
        rw [leftMoves_ofSets]
        exact Set.mem_image_of_mem _ hu
      · rw [← Surreal.mk_le_mk]
        simp only [Surreal.mk_add, Surreal.out_eq, ← hym]
        exact le_rfl
    · refine ⟨!{Surreal.out '' A | (∅ : Set IGame)} + Surreal.out u, ?_, ?_⟩
      · refine add_left_mem_moves_add ?_ _
        rw [leftMoves_ofSets]
        exact Set.mem_image_of_mem _ hu
      · rw [← Surreal.mk_le_mk]
        simp only [Surreal.mk_add, Surreal.out_eq, ← hxm]
        exact le_rfl
  · rw [rightMoves_ofSets]
    rintro b hb
    exact absurd hb (Set.notMem_empty b)

/-! ### The additive ladder above `ω` -/

/-- The canonical representation of the rungs `ω·(m+1)`: each is the left-cut of
`ω·m + n` over `n ∈ ℕ`. -/
theorem wpow_one_mul_natCast_rep (m : ℕ) :
    ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal) =
      !{Set.range (fun n : ℕ ↦ ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + (n : Surreal)) | ∅} := by
  induction m with
  | zero =>
    rw [Nat.cast_one, mul_one, wpow_one_eq_ofSets_natCast]
    apply ofSets_left_eq_of_cofinal
    · rintro z ⟨n, rfl⟩
      exact ⟨_, ⟨n, rfl⟩, le_of_eq (by push_cast; ring)⟩
    · rintro z ⟨n, rfl⟩
      exact ⟨(n : Surreal), ⟨n, rfl⟩, le_of_eq (by push_cast; ring)⟩
  | succ m ih =>
    have hsplit : ω^ (1 : Surreal) * ((m + 1 + 1 : ℕ) : Surreal) =
        ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal) + ω^ (1 : Surreal) := by
      push_cast; ring
    rw [hsplit, ofSets_left_add ih wpow_one_eq_ofSets_natCast]
    apply ofSets_left_eq_of_cofinal
    · rintro z (⟨w, ⟨n, rfl⟩, rfl⟩ | ⟨w, ⟨n, rfl⟩, rfl⟩)
      · exact ⟨_, ⟨n, rfl⟩, le_of_eq (by push_cast; ring)⟩
      · exact ⟨_, ⟨n, rfl⟩, le_of_eq (by push_cast; ring)⟩
    · rintro z ⟨n, rfl⟩
      exact ⟨_, Set.mem_union_right _ (Set.mem_image_of_mem _ ⟨n, rfl⟩),
        le_of_eq (by push_cast; ring)⟩

/-! ### `exp (ω·m) = (ω^ω)^m` -/

private theorem hdiff_omega_mul (m n : ℕ) :
    ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal) -
      (ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + (n : Surreal)) =
      ω^ (1 : Surreal) - (n : Surreal) := by
  push_cast; ring

/-- **The exponential of every rung `ω·(m+1)` is `(ω^ω)^(m+1)`** (Gonshor). Precisely:
at the canonical representation `ω·(m+1) = !{ω·m + n | ∅}`, Gonshor's genetic formula —
seeded with the recursion's values `exp (ω·m + n) = (ω^ω)^m·eⁿ` at the left options —
evaluates to `(ω^ω)^(m+1)`. The `m = 0` case is `gonshorExp_omega` again; each rung's
seeds are the previous rung's values, so the limit-step theorem composes up Gonshor's
ladder. -/
theorem gonshorExp_omega_mul (m : ℕ) :
    (!{insert 0 (Set.range fun p : ℕ × ℕ ↦
        ((ω^ ω^ (1 : Surreal)) ^ m * ((Real.exp p.1 : ℝ) : Surreal)) *
          expPartial p.2 (ω^ (1 : Surreal) - (p.1 : Surreal))) | ∅} : Surreal)
      = (ω^ ω^ (1 : Surreal)) ^ (m + 1) := by
  have hv : ∀ n : ℕ, 0 < (ω^ ω^ (1 : Surreal)) ^ m * ((Real.exp n : ℝ) : Surreal) :=
    fun n ↦ mul_pos (pow_pos (wpow_pos _) m) (by simpa using Real.exp_pos n)
  have hs : ∀ n : ℕ, ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + (n : Surreal) <
      ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal) := by
    intro n
    have h1 : ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal) =
        ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + ω^ (1 : Surreal) := by push_cast; ring
    have h2 := natCast_lt_wpow_one n
    rw [h1]
    linarith
  have hinf : ∀ n : ℕ, ¬ IsFinite (ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal) -
      (ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + (n : Surreal))) := by
    intro n
    rw [hdiff_omega_mul]
    exact not_isFinite_wpow_one_sub_natCast n
  have h := gonshorCut_eq_wpow (a := ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal))
    (s := fun n : ℕ ↦ ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + (n : Surreal))
    (v := fun n : ℕ ↦ (ω^ ω^ (1 : Surreal)) ^ m * ((Real.exp n : ℝ) : Surreal))
    hv hs hinf
  have hwv : ∀ n : ℕ, wlog ((ω^ ω^ (1 : Surreal)) ^ m * ((Real.exp n : ℝ) : Surreal)) =
      ((m : ℕ) : Surreal) * ω^ (1 : Surreal) := by
    intro n
    rw [wlog_mul (pow_ne_zero m (wpow_ne_zero _))
      (ne_of_gt (by simpa using Real.exp_pos n)), wlog_pow, wlog_wpow, wlog_realCast,
      add_zero]
  have hwd : ∀ n : ℕ, wlog (ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal) -
      (ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + (n : Surreal))) = 1 := by
    intro n
    rw [hdiff_omega_mul]
    exact wlog_wpow_one_sub_natCast n
  -- Bridge from the statement's options (with the difference simplified to `ω − n`)
  -- to the theorem's options.
  have hL : (!{insert 0 (Set.range fun p : ℕ × ℕ ↦
      ((ω^ ω^ (1 : Surreal)) ^ m * ((Real.exp p.1 : ℝ) : Surreal)) *
        expPartial p.2 (ω^ (1 : Surreal) - (p.1 : Surreal))) | ∅} : Surreal) =
      !{insert 0 (Set.range fun p : ℕ × ℕ ↦
        ((ω^ ω^ (1 : Surreal)) ^ m * ((Real.exp p.1 : ℝ) : Surreal)) *
          expPartial p.2 (ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal) -
            (ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + (p.1 : Surreal)))) | ∅} := by
    apply ofSets_left_eq_of_cofinal
    · rintro z (rfl | ⟨⟨n, k⟩, rfl⟩)
      · exact ⟨0, Set.mem_insert 0 _, le_rfl⟩
      · exact ⟨_, Set.mem_insert_of_mem _ ⟨(n, k), rfl⟩,
          le_of_eq (by simp only [hdiff_omega_mul m n])⟩
    · rintro z (rfl | ⟨⟨n, k⟩, rfl⟩)
      · exact ⟨0, Set.mem_insert 0 _, le_rfl⟩
      · exact ⟨_, Set.mem_insert_of_mem _ ⟨(n, k), rfl⟩,
          le_of_eq (by simp only [hdiff_omega_mul m n])⟩
  -- Identify the exponent cut with `ω·(m+1)`.
  have hexp : (!{Set.range fun p : ℕ × ℕ ↦
      wlog ((ω^ ω^ (1 : Surreal)) ^ m * ((Real.exp p.1 : ℝ) : Surreal)) +
        (p.2 : Surreal) * wlog (ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal) -
          (ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + (p.1 : Surreal))) | ∅} : Surreal) =
      ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal) := by
    conv_rhs => rw [wpow_one_mul_natCast_rep m]
    apply ofSets_left_eq_of_cofinal
    · rintro z ⟨⟨n, k⟩, rfl⟩
      refine ⟨_, ⟨k, rfl⟩, le_of_eq ?_⟩
      show wlog ((ω^ ω^ (1 : Surreal)) ^ m * ((Real.exp n : ℝ) : Surreal)) +
        ((k : ℕ) : Surreal) * wlog (ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal) -
          (ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + (n : Surreal))) =
        ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + ((k : ℕ) : Surreal)
      rw [hwv n, hwd n, mul_one, mul_comm]
    · rintro z ⟨n, rfl⟩
      refine ⟨_, ⟨((0 : ℕ), n), rfl⟩, le_of_eq ?_⟩
      show ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + ((n : ℕ) : Surreal) =
        wlog ((ω^ ω^ (1 : Surreal)) ^ m * ((Real.exp (0 : ℕ) : ℝ) : Surreal)) +
        ((n : ℕ) : Surreal) * wlog (ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal) -
          (ω^ (1 : Surreal) * ((m : ℕ) : Surreal) + ((0 : ℕ) : Surreal)))
      rw [hwv 0, hwd 0, mul_one, mul_comm]
  calc (!{insert 0 (Set.range fun p : ℕ × ℕ ↦
        ((ω^ ω^ (1 : Surreal)) ^ m * ((Real.exp p.1 : ℝ) : Surreal)) *
          expPartial p.2 (ω^ (1 : Surreal) - (p.1 : Surreal))) | ∅} : Surreal)
      = _ := hL
    _ = _ := h
    _ = ω^ (ω^ (1 : Surreal) * ((m + 1 : ℕ) : Surreal)) := by rw [hexp]
    _ = (ω^ ω^ (1 : Surreal)) ^ (m + 1) := by
        rw [mul_comm (ω^ (1 : Surreal)) _, wpow_natCast_mul]

/-! ### `ω²` as a limit of limits -/

/-- `2` is the left-cut of `{1}` (Conway's day-2 representation). -/
theorem two_eq_ofSets_one : (2 : Surreal) = !{({1} : Set Surreal) | ∅} := by
  haveI := numeric_ofSets_out_left ({1} : Set Surreal)
  rw [surreal_ofSets_left_rep ({1} : Set Surreal), ← one_add_one_eq_two,
    ← Surreal.mk_one, ← Surreal.mk_add]
  apply Surreal.mk_eq
  apply equiv_of_exists_le
  · rw [moves_add]
    rintro a (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩) <;> rw [leftMoves_one] at hw <;>
      rw [Set.mem_singleton_iff] at hw <;> subst hw
    · refine ⟨Surreal.out 1, ?_, ?_⟩
      · rw [leftMoves_ofSets]
        exact Set.mem_image_of_mem _ (Set.mem_singleton 1)
      · rw [← Surreal.mk_le_mk]
        simp
    · refine ⟨Surreal.out 1, ?_, ?_⟩
      · rw [leftMoves_ofSets]
        exact Set.mem_image_of_mem _ (Set.mem_singleton 1)
      · rw [← Surreal.mk_le_mk]
        simp
  · intro a ha
    rw [moves_add] at ha
    simp only [rightMoves_one, Set.image_empty, Set.union_self,
      Set.mem_empty_iff_false] at ha
  · rw [leftMoves_ofSets]
    rintro b ⟨w, hw, rfl⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    refine ⟨0 + 1, ?_, ?_⟩
    · refine add_right_mem_moves_add ?_ _
      rw [leftMoves_one]
      exact Set.mem_singleton 0
    · rw [← Surreal.mk_le_mk]
      simp
  · intro b hb
    rw [rightMoves_ofSets] at hb
    exact absurd hb (Set.notMem_empty b)

/-- **`ω²` is the left-cut of the rungs**: `ω^2 = !{ω·n | ∅}`. -/
theorem wpow_two_rep :
    ω^ (2 : Surreal) =
      !{Set.range (fun n : ℕ ↦ ω^ (1 : Surreal) * (n : Surreal)) | ∅} := by
  rw [two_eq_ofSets_one, wpow_ofSets]
  apply ofSets_left_eq_of_cofinal
  · rintro z (rfl | ⟨r, hr, x, hx, rfl⟩)
    · exact ⟨_, ⟨0, rfl⟩, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨j, hj⟩ := exists_nat_ge (r : ℚ)
      refine ⟨_, ⟨j, rfl⟩, ?_⟩
      show (r : Surreal) * ω^ (1 : Surreal) ≤ ω^ (1 : Surreal) * ((j : ℕ) : Surreal)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) (wpow_nonneg _)
  · rintro z ⟨k, rfl⟩
    refine ⟨(((k + 1 : ℕ) : Dyadic) : Surreal) * ω^ (1 : Surreal),
      Set.mem_insert_of_mem _ (Set.mem_image2_of_mem ?_ (Set.mem_singleton 1)), ?_⟩
    · rw [Set.mem_Ioi]
      exact_mod_cast Nat.succ_pos k
    · show ω^ (1 : Surreal) * ((k : ℕ) : Surreal) ≤
        (((k + 1 : ℕ) : Dyadic) : Surreal) * ω^ (1 : Surreal)
      rw [mul_comm (ω^ (1 : Surreal)) _]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (wpow_nonneg _)

/-! ### `exp (ω²) = ω^(ω²)` -/

theorem mk_wpow_lt_zero {x : Surreal} (hx : 0 < x) :
    ArchimedeanClass.mk (ω^ x) < 0 := by
  have h := archimedeanClassMk_wpow_strictAnti hx
  simpa using h

private theorem mk_wpow_two_sub (n : ℕ) :
    ArchimedeanClass.mk (ω^ (2 : Surreal) - ω^ (1 : Surreal) * (n : Surreal)) =
      ArchimedeanClass.mk (ω^ (2 : Surreal)) := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · rw [Nat.cast_zero, mul_zero, sub_zero]
  · rw [sub_eq_add_neg]
    apply ArchimedeanClass.mk_add_eq_mk_left
    rw [ArchimedeanClass.mk_neg, ArchimedeanClass.mk_mul, mk_natCast_eq_zero hn.ne',
      add_zero]
    exact archimedeanClassMk_wpow_strictAnti one_lt_two

private theorem not_isFinite_wpow_two_sub (n : ℕ) :
    ¬ IsFinite (ω^ (2 : Surreal) - ω^ (1 : Surreal) * (n : Surreal)) := by
  intro hfin
  have h0 := isFinite_def.1 hfin
  rw [mk_wpow_two_sub n] at h0
  exact absurd h0 (not_le.2 (mk_wpow_lt_zero two_pos))

private theorem wlog_wpow_two_sub (n : ℕ) :
    wlog (ω^ (2 : Surreal) - ω^ (1 : Surreal) * (n : Surreal)) = 2 := by
  have h := wlog_congr (veq_def.2 (mk_wpow_two_sub n))
  rw [h, wlog_wpow]

/-- **The exponential of `ω²` is `ω^(ω²)`** (Gonshor). At the representation
`ω² = !{ω·n | ∅}`, Gonshor's formula — seeded with the previous rungs' values
`exp (ω·n) = (ω^ω)^n` from `gonshorExp_omega_mul` — evaluates to `ω^(ω²)`. This is the
first rung whose left options are themselves infinite limits: the recursion genuinely
recursing. -/
theorem gonshorExp_omega_sq :
    (!{insert 0 (Set.range fun p : ℕ × ℕ ↦
        (ω^ ω^ (1 : Surreal)) ^ p.1 *
          expPartial p.2 (ω^ (2 : Surreal) - ω^ (1 : Surreal) * (p.1 : Surreal))) | ∅} : Surreal)
      = ω^ ω^ (2 : Surreal) := by
  have hv : ∀ n : ℕ, 0 < (ω^ ω^ (1 : Surreal)) ^ n := fun n ↦ pow_pos (wpow_pos _) n
  have hs : ∀ n : ℕ, ω^ (1 : Surreal) * (n : Surreal) < ω^ (2 : Surreal) := by
    intro n
    have h2 : ω^ (2 : Surreal) = ω^ (1 : Surreal) * ω^ (1 : Surreal) := by
      rw [← wpow_add, one_add_one_eq_two]
    rw [h2]
    exact mul_lt_mul_of_pos_left (natCast_lt_wpow_one n) (wpow_pos _)
  have h := gonshorCut_eq_wpow (a := ω^ (2 : Surreal))
    (s := fun n : ℕ ↦ ω^ (1 : Surreal) * (n : Surreal))
    (v := fun n : ℕ ↦ (ω^ ω^ (1 : Surreal)) ^ n)
    hv hs (fun n ↦ not_isFinite_wpow_two_sub n)
  have hwv : ∀ n : ℕ, wlog ((ω^ ω^ (1 : Surreal)) ^ n) =
      ((n : ℕ) : Surreal) * ω^ (1 : Surreal) := by
    intro n
    rw [wlog_pow, wlog_wpow]
  have hexp : (!{Set.range fun p : ℕ × ℕ ↦
      wlog ((ω^ ω^ (1 : Surreal)) ^ p.1) + (p.2 : Surreal) *
        wlog (ω^ (2 : Surreal) - ω^ (1 : Surreal) * (p.1 : Surreal)) | ∅} : Surreal) =
      ω^ (2 : Surreal) := by
    conv_rhs => rw [wpow_two_rep]
    apply ofSets_left_eq_of_cofinal
    · rintro z ⟨⟨n, k⟩, rfl⟩
      refine ⟨_, ⟨n + 1, rfl⟩, ?_⟩
      show wlog ((ω^ ω^ (1 : Surreal)) ^ n) + ((k : ℕ) : Surreal) *
          wlog (ω^ (2 : Surreal) - ω^ (1 : Surreal) * ((n : ℕ) : Surreal)) ≤
        ω^ (1 : Surreal) * ((n + 1 : ℕ) : Surreal)
      rw [hwv n, wlog_wpow_two_sub n]
      have h2k := natCast_lt_wpow_one (2 * k)
      have h2k' : ((k : ℕ) : Surreal) * 2 < ω^ (1 : Surreal) := by
        push_cast at h2k
        linarith
      have hgoal : ω^ (1 : Surreal) * ((n + 1 : ℕ) : Surreal) =
          ((n : ℕ) : Surreal) * ω^ (1 : Surreal) + ω^ (1 : Surreal) := by
        push_cast; ring
      rw [hgoal]
      linarith
    · rintro z ⟨j, rfl⟩
      refine ⟨_, ⟨(j, (0 : ℕ)), rfl⟩, ?_⟩
      show ω^ (1 : Surreal) * ((j : ℕ) : Surreal) ≤
        wlog ((ω^ ω^ (1 : Surreal)) ^ j) + ((0 : ℕ) : Surreal) *
          wlog (ω^ (2 : Surreal) - ω^ (1 : Surreal) * ((j : ℕ) : Surreal))
      rw [hwv j, wlog_wpow_two_sub j]
      apply le_of_eq
      push_cast
      ring
  exact h.trans (by rw [hexp])

end Surreal
