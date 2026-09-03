/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.GeometricUpper

/-!
# `ω/(ω−1)` is born by day `ω²`: the Conway-inverse cofinality

The geometric squeeze (`Infinity.GeometricUpper`) placed the canonical sum of `Σ ω⁻ᵏ`
in `[ω·2, ω²]`, but the birthday of the *conjectured value* `ω/(ω−1)` itself remained
unbounded: no cut with partial-sum options can pin it by order (every such cut has the
whole micro-halo as fits, and only simplicity — the conjecture itself — selects among
them). This file breaks that deadlock using the **Conway inverse game**: the value
`ω/(ω−1) = 1 + (ω−1)⁻¹` *is* `1 + W⁻¹` for the game `W = ω + (−1)`, and `W⁻¹`'s
option words obey the exact error recursion

  `value (invOption x y a) − x⁻¹ = (x − y)·(x⁻¹ − value a) / y`,

so every word sits at distance exactly `ω^k` (an integer power) from `(ω−1)⁻¹` — never
*inside* the micro-halo. Mutual cofinality with the partial-sum cut follows, and the
cut's options have birthdays of shape `ω·m + m`:

* `inv_move_class` — **the word-class invariant**, by the upstream `invRec` induction:
  every option of `W⁻¹` differs from `(ω−1)⁻¹` by exactly the class of `ω^k`, `k : ℤ`.
* `birthday_geomSum_limit_le_omega_mul_omega` — **`birthday (ω/(ω−1)) ≤ ω·ω`**.
* `hahnSum_geometric_eq_iff_birthday_le` — with the squeeze, the halo-minimality
  conjecture `hahnSum (Σ ω⁻ᵏ) = ω/(ω−1)` is **equivalent** to the single inequality
  `birthday (ω/(ω−1)) ≤ birthday (hahnSum (Σ ω⁻ᵏ))`, both sides now living in
  `[ω·2, ω²]`.
-/

open ArchimedeanClass IGame Set

noncomputable section

namespace Surreal

local notation "Ω" => NatOrdinal.of Ordinal.omega0
local notation "ε₀" => eps0

/-! ### The anchor game `W = ω + (−1)` and the value `u₀ = (ω−1)⁻¹` -/

private def Wgame : IGame.{0} := ω^ (1 : IGame) + (-1 : IGame)

instance : IGame.Numeric Wgame := by
  unfold Wgame
  infer_instance

private theorem mk_wpow_one₀ : Surreal.mk (ω^ (1 : IGame.{0})) = ω^ (1 : Surreal) := by
  rw [Surreal.mk_wpow]
  norm_num

private theorem mk_neg_one₀ : Surreal.mk (-1 : IGame.{0}) = -1 := by
  show Surreal.mk (-(1 : IGame.{0})) = -1
  rw [Surreal.mk_neg, Surreal.mk_one]

private theorem mk_W : Surreal.mk Wgame = ω^ (1 : Surreal) - 1 := by
  show Surreal.mk (ω^ (1 : IGame.{0}) + (-1 : IGame)) = _
  rw [Surreal.mk_add, mk_wpow_one₀, mk_neg_one₀]
  ring

private theorem one_lt_wpow_one₀ : (1 : Surreal.{0}) < ω^ (1 : Surreal) := by
  have h : ((1 : ℕ) : Surreal.{0}) < ω^ (1 : Surreal) := natCast_lt_wpow_one 1
  have h1 : ((1 : ℕ) : Surreal.{0}) = 1 := by push_cast; rfl
  rwa [h1] at h

private theorem xval_pos : (0 : Surreal.{0}) < ω^ (1 : Surreal) - 1 := by
  have := one_lt_wpow_one₀
  linarith

private theorem Wgame_pos : (0 : IGame.{0}) < Wgame := by
  rw [← @Surreal.mk_lt_mk 0 Wgame _ _, Surreal.mk_zero, mk_W]
  exact xval_pos

/-- The value of the inverse: `u₀ = (ω − 1)⁻¹`. -/
private def uval : Surreal.{0} := (ω^ (1 : Surreal) - 1)⁻¹

private theorem uval_pos : 0 < uval := by
  rw [uval]
  exact inv_pos.2 xval_pos

private theorem mk_inv_W : Surreal.mk (Wgame⁻¹) = uval := by
  rw [Surreal.mk_inv, mk_W, uval]

/-! ### Class toolkit -/

/-- Coarser class dominates: positives of strictly coarser class are strictly larger. -/
private theorem lt_of_mk_lt_mk' {a b : Surreal.{0}} (hb : 0 < b)
    (hmk : ArchimedeanClass.mk b < ArchimedeanClass.mk a) : a < b := by
  have h := (ArchimedeanClass.mk_lt_mk).1 hmk 1
  rw [one_smul] at h
  calc a ≤ |a| := le_abs_self a
    _ < |b| := h
    _ = b := abs_of_pos hb

private theorem mk_one_sub_infinitesimal {z : Surreal.{0}} (hz : Infinitesimal z) :
    ArchimedeanClass.mk (1 - z) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [stdPart_sub isFinite_one hz.isFinite, hz.stdPart_eq_zero,
    ArchimedeanClass.stdPart_one]
  norm_num

private theorem eps0_infinitesimal₀ : Infinitesimal (ε₀ : Surreal.{0}) := by
  rw [eps0_def]
  exact infinitesimal_inv_wpow one_pos

private theorem eps0_pos₀ : (0 : Surreal.{0}) < ε₀ := by
  rw [eps0_def]
  exact inv_pos.2 (wpow_pos _)

private theorem wpow_one_ne_zero₀ : (ω^ (1 : Surreal.{0})) ≠ 0 := (wpow_pos _).ne'

/-- `ω − q` has the class of `ω`, for every dyadic `q`. -/
private theorem mk_wpow_one_sub_dyadic (q : Dyadic) :
    ArchimedeanClass.mk (ω^ (1 : Surreal.{0}) - (q : Surreal))
      = ArchimedeanClass.mk (ω^ (1 : Surreal.{0})) := by
  have hfac : ω^ (1 : Surreal.{0}) - (q : Surreal)
      = ω^ (1 : Surreal) * (1 - (q : Surreal) * (ω^ (1 : Surreal))⁻¹) := by
    field_simp
  rw [hfac, ArchimedeanClass.mk_mul, mk_one_sub_infinitesimal, add_zero]
  have h : Infinitesimal ((q : Surreal.{0}) * ω^ (-1 : Surreal)) :=
    infinitesimal_dyadic_mul_wpow q
  rwa [show (ω^ (-1 : Surreal.{0})) = (ω^ (1 : Surreal.{0}))⁻¹ from by
    rw [show (-1 : Surreal.{0}) = -(1 : Surreal) from rfl, wpow_neg]] at h

/-- `mk (ω − 1) = mk ω`, hence `mk u₀ = mk (ω⁻¹)`. -/
private theorem mk_xval : ArchimedeanClass.mk (ω^ (1 : Surreal.{0}) - 1)
    = ArchimedeanClass.mk (ω^ (1 : Surreal.{0})) := by
  have h := mk_wpow_one_sub_dyadic 1
  rwa [dyadic_cast_one] at h

private theorem mk_uval : ArchimedeanClass.mk uval
    = ArchimedeanClass.mk (ω^ (((-1 : ℤ) : ℤ) : Surreal.{0})) := by
  rw [uval, ArchimedeanClass.mk_inv, mk_xval]
  have h1 : (((-1 : ℤ) : ℤ) : Surreal.{0}) = -(1 : Surreal) := by push_cast; ring
  rw [h1, wpow_neg, ArchimedeanClass.mk_inv]

/-- The `ℤ`-graded `ω`-power classes: adjacent exponents differ by `mk ω`. -/
private theorem mk_wpow_int_succ (k : ℤ) :
    ArchimedeanClass.mk (ω^ (((k + 1 : ℤ) : ℤ) : Surreal.{0}))
      = ArchimedeanClass.mk (ω^ (1 : Surreal.{0}))
        + ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0})) := by
  have h1 : (((k + 1 : ℤ) : ℤ) : Surreal.{0}) = 1 + ((k : ℤ) : Surreal) := by
    push_cast
    ring
  rw [h1, wpow_add, ArchimedeanClass.mk_mul]

private theorem mk_wpow_int_anti {k l : ℤ} (h : k < l) :
    ArchimedeanClass.mk (ω^ ((l : ℤ) : Surreal.{0}))
      < ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0})) := by
  refine archimedeanClassMk_wpow_strictAnti ?_
  exact_mod_cast h

private theorem mk_eps0_pow_int (n : ℕ) :
    ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ (n + 1))
      = ArchimedeanClass.mk (ω^ (((-(n + 1) : ℤ) : ℤ) : Surreal.{0})) := by
  have hval : (ε₀ : Surreal.{0}) ^ (n + 1) = ω^ (-(((n + 1) : ℕ) : Surreal.{0})) := by
    rw [eps0_def, wpow_neg, wpow_natCast, inv_pow]
  rw [hval]
  have h1 : (-(((n + 1) : ℕ) : Surreal.{0})) = (((-(n + 1) : ℤ) : ℤ) : Surreal.{0}) := by
    push_cast
    ring
  rw [h1]

private theorem mk_wpow_int_add (k l : ℤ) :
    ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0}))
        + ArchimedeanClass.mk (ω^ ((l : ℤ) : Surreal.{0}))
      = ArchimedeanClass.mk (ω^ (((k + l : ℤ) : ℤ) : Surreal.{0})) := by
  rw [← ArchimedeanClass.mk_mul, ← wpow_add]
  congr 2
  push_cast
  ring

private theorem mk_wpow_one_int : ArchimedeanClass.mk (ω^ (1 : Surreal.{0}))
    = ArchimedeanClass.mk (ω^ (((1 : ℤ) : ℤ) : Surreal.{0})) := by
  congr 2
  push_cast
  ring

private theorem mk_wpow_one_inv_int : ArchimedeanClass.mk ((ω^ (1 : Surreal.{0}))⁻¹)
    = ArchimedeanClass.mk (ω^ (((-1 : ℤ) : ℤ) : Surreal.{0})) := by
  rw [show (((-1 : ℤ) : ℤ) : Surreal.{0}) = -(1 : Surreal) from by push_cast; ring, wpow_neg]

private theorem mk_dyadic_ne_zero {c : Dyadic} (hc : c ≠ 0) :
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

/-! ### The moves of `W` -/

private theorem leftMoves_wpow_one₀ : (ω^ (1 : IGame.{0}))ᴸ =
    insert 0 ((fun r : Dyadic ↦ (r : IGame) * ω^ (0 : IGame)) '' Set.Ioi 0) := by
  have h1 : (1 : IGame.{0})ᴸ = {0} := by simp
  rw [leftMoves_wpow, h1, Set.image2_singleton_right]

private theorem rightMoves_wpow_one₀ : (ω^ (1 : IGame.{0}))ᴿ = ∅ := by
  have h1 : (1 : IGame.{0})ᴿ = ∅ := by simp
  rw [rightMoves_wpow, h1]
  simp

private theorem neg_one_leftMoves₀ : (-1 : IGame.{0})ᴸ = ∅ := by
  rw [show (-1 : IGame.{0}) = -(1 : IGame) from rfl]
  simp

private theorem neg_one_rightMoves₀ : (-1 : IGame.{0})ᴿ = {0} := by
  rw [show (-1 : IGame.{0}) = -(1 : IGame) from rfl]
  simp

private theorem mk_dyadic_mul_wpow_zero₀ (q : Dyadic) :
    Surreal.mk ((q : IGame.{0}) * ω^ (0 : IGame)) = (q : Surreal) := by
  rw [Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow, Surreal.mk_zero, wpow_zero, mul_one]

/-- Every move of `W` has value `q − 1` for a dyadic `q`, or value `ω`. -/
private theorem W_move_value (p : Player) (y : IGame.{0}) (hy : y ∈ Wgame.moves p) :
    (∃ q : Dyadic, @Surreal.mk y (IGame.Numeric.of_mem_moves hy) = (q : Surreal) - 1) ∨
      @Surreal.mk y (IGame.Numeric.of_mem_moves hy) = ω^ (1 : Surreal) := by
  haveI := IGame.Numeric.of_mem_moves hy
  have hy' : y ∈ (ω^ (1 : IGame.{0}) + (-1 : IGame)).moves p := hy
  rw [moves_add] at hy'
  rcases hy' with ⟨i, hi, rfl⟩ | ⟨z, hz, rfl⟩
  · -- a move of the `ω`-power side, plus `−1`
    cases p with
    | left =>
      rw [show (ω^ (1 : IGame.{0})).moves Player.left = (ω^ (1 : IGame.{0}))ᴸ from rfl,
        leftMoves_wpow_one₀, Set.mem_insert_iff] at hi
      rcases hi with rfl | ⟨q, hq, rfl⟩
      · refine .inl ⟨0, ?_⟩
        rw [show @Surreal.mk ((0 : IGame.{0}) + (-1 : IGame)) _
            = Surreal.mk (0 : IGame.{0}) + Surreal.mk (-1 : IGame.{0}) from Surreal.mk_add ..,
          Surreal.mk_zero, mk_neg_one₀, dyadic_cast_zero]
        ring
      · refine .inl ⟨q, ?_⟩
        rw [show @Surreal.mk ((q : IGame.{0}) * ω^ (0 : IGame) + (-1 : IGame)) _
            = Surreal.mk ((q : IGame.{0}) * ω^ (0 : IGame)) + Surreal.mk (-1 : IGame.{0})
            from Surreal.mk_add .., mk_dyadic_mul_wpow_zero₀, mk_neg_one₀]
        ring
    | right =>
      rw [show (ω^ (1 : IGame.{0})).moves Player.right = (ω^ (1 : IGame.{0}))ᴿ from rfl,
        rightMoves_wpow_one₀] at hi
      exact absurd hi (Set.notMem_empty i)
  · -- the `ω`-power, plus a move of `−1`
    cases p with
    | left =>
      rw [show (-1 : IGame.{0}).moves Player.left = (-1 : IGame.{0})ᴸ from rfl,
        neg_one_leftMoves₀] at hz
      exact absurd hz (Set.notMem_empty z)
    | right =>
      rw [show (-1 : IGame.{0}).moves Player.right = (-1 : IGame.{0})ᴿ from rfl,
        neg_one_rightMoves₀, Set.mem_singleton_iff] at hz
      subst hz
      refine .inr ?_
      rw [show @Surreal.mk (ω^ (1 : IGame.{0}) + (0 : IGame)) _
          = Surreal.mk (ω^ (1 : IGame.{0})) + Surreal.mk (0 : IGame.{0})
          from Surreal.mk_add .., mk_wpow_one₀, Surreal.mk_zero, add_zero]

/-! ### The word-class invariant -/

/-- **Every option of `W⁻¹` sits at distance exactly `ω^k` from `(ω−1)⁻¹`** for some
integer `k`: the Conway-inverse words never enter the micro-halo. Proof by the upstream
`invRec` induction with the exact error recursion
`value' − u₀ = (x − y)(u₀ − value)/y`. -/
private theorem inv_move_class :
    ∀ (p : Player) (y : IGame.{0}) (hy : y ∈ (Wgame⁻¹).moves p),
      ∃ k : ℤ, ArchimedeanClass.mk
          (@Surreal.mk y (IGame.Numeric.of_mem_moves hy) - uval)
        = ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0})) := by
  refine invRec Wgame_pos ?_ ?_
  · -- the zero option
    refine ⟨-1, ?_⟩
    have h0 : @Surreal.mk (0 : IGame.{0}) (IGame.Numeric.of_mem_moves
        (zero_mem_leftMoves_inv Wgame_pos)) = 0 := Surreal.mk_zero
    rw [h0, zero_sub, ArchimedeanClass.mk_neg, mk_uval]
  · -- the inductive step
    intro p₁ p₂ y hy0 hyx a ha IH
    obtain ⟨k, hk⟩ := IH
    haveI hyn : y.Numeric := IGame.Numeric.of_mem_moves hyx
    haveI han : a.Numeric := IGame.Numeric.of_mem_moves ha
    have hyv0 : (0 : Surreal) < Surreal.mk y := by
      rw [← Surreal.mk_zero]
      exact Surreal.mk_lt_mk.2 hy0
    -- the value of the new word
    have hval : @Surreal.mk (invOption Wgame y a)
        (IGame.Numeric.of_mem_moves (invOption_mem_moves_inv Wgame_pos hy0 hyx ha))
        = (1 + (Surreal.mk y - (ω^ (1 : Surreal) - 1)) * Surreal.mk a) / Surreal.mk y := by
      show Surreal.mk ((1 + (y - Wgame) * a) / y) = _
      rw [Surreal.mk_div, Surreal.mk_add, Surreal.mk_one, Surreal.mk_mul, Surreal.mk_sub, mk_W]
    -- the exact error recursion
    have herr : (1 + (Surreal.mk y - (ω^ (1 : Surreal) - 1)) * Surreal.mk a) / Surreal.mk y
          - uval
        = ((ω^ (1 : Surreal) - 1) - Surreal.mk y) * (uval - Surreal.mk a) / Surreal.mk y := by
      have hy' : Surreal.mk y ≠ 0 := hyv0.ne'
      have hx' : (ω^ (1 : Surreal.{0}) - 1) ≠ 0 := xval_pos.ne'
      have hx'' : (-1 + ω^ (1 : Surreal.{0})) ≠ 0 := by
        intro h0
        apply hx'
        linarith
      rw [uval]
      field_simp
      ring
    have hmk_ua : ArchimedeanClass.mk (uval - Surreal.mk a)
        = ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0})) := by
      rw [show uval - Surreal.mk a = -(Surreal.mk a - uval) from by ring,
        ArchimedeanClass.mk_neg]
      exact hk
    rcases W_move_value _ y hyx with ⟨q, hq⟩ | hω
    · -- a finite move: the error coarsens by one `ω`-power
      refine ⟨k + 1, ?_⟩
      rw [hval, herr]
      have hxy : (ω^ (1 : Surreal.{0}) - 1) - Surreal.mk y = ω^ (1 : Surreal) - (q : Surreal) := by
        rw [hq]
        ring
      have hyq : Surreal.mk y = ((q - 1 : Dyadic) : Surreal) := by
        rw [hq, dyadic_cast_sub', dyadic_cast_one]
      have hq1 : (q - 1 : Dyadic) ≠ 0 := by
        intro h0
        rw [h0, dyadic_cast_zero] at hyq
        exact hyv0.ne' hyq
      rw [div_eq_mul_inv, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
        ArchimedeanClass.mk_inv, hxy, mk_wpow_one_sub_dyadic, hmk_ua, hyq,
        mk_dyadic_ne_zero hq1, neg_zero, add_zero, mk_wpow_one_int, mk_wpow_int_add]
      congr 2
      push_cast
      ring
    · -- the `ω` move: the error refines by one `ω`-power
      refine ⟨k - 1, ?_⟩
      rw [show (k - 1 : ℤ) = k + (-1 : ℤ) from by ring]
      rw [hval, herr]
      have hxy : (ω^ (1 : Surreal.{0}) - 1) - Surreal.mk y = -1 := by
        rw [hω]
        ring
      rw [div_eq_mul_inv, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
        ArchimedeanClass.mk_inv, hxy, ArchimedeanClass.mk_neg, ArchimedeanClass.mk_one,
        zero_add, hmk_ua, hω]
      rw [show -ArchimedeanClass.mk (ω^ (1 : Surreal.{0}))
          = ArchimedeanClass.mk ((ω^ (1 : Surreal.{0}))⁻¹) from
          (ArchimedeanClass.mk_inv _).symm, mk_wpow_one_inv_int, mk_wpow_int_add]

/-! ### The value `v = (1 − ε₀)⁻¹ = 1 + u₀` and the partial-sum ladder -/

private theorem eps_ne_one₀ : (ε₀ : Surreal.{0}) ≠ 1 := by
  intro h
  have h2 := eps0_infinitesimal₀.stdPart_eq_zero
  rw [h] at h2
  rw [ArchimedeanClass.stdPart_one] at h2
  norm_num at h2

private theorem one_sub_eps_ne₀ : (1 : Surreal.{0}) - ε₀ ≠ 0 :=
  sub_ne_zero.2 (Ne.symm eps_ne_one₀)

private theorem infinitesimal_uval : Infinitesimal uval := by
  show 0 < ArchimedeanClass.mk uval
  rw [mk_uval, show (((-1 : ℤ) : ℤ) : Surreal.{0}) = -(1 : Surreal) from by push_cast; ring,
    wpow_neg, show ((ω^ (1 : Surreal.{0}))⁻¹) = ε₀ from by rw [eps0_def]]
  exact eps0_infinitesimal₀

private theorem uval_lt_one : uval < 1 := by
  have h := infinitesimal_uval.lt_ratCast (q := 1) (by norm_num)
  have h1 : ((1 : ℚ) : Surreal.{0}) = 1 := by norm_num
  rwa [h1] at h

/-- The closed form: `(1 − ε₀)⁻¹ = 1 + (ω − 1)⁻¹`. -/
private theorem v_eq : ((1 : Surreal.{0}) - ε₀)⁻¹ = 1 + uval := by
  have h0 : (ω^ (1 : Surreal.{0})) ≠ 0 := wpow_one_ne_zero₀
  have hx : (ω^ (1 : Surreal.{0}) - 1) ≠ 0 := xval_pos.ne'
  have h1 : (1 : Surreal.{0}) - ε₀ ≠ 0 := one_sub_eps_ne₀
  rw [uval]
  rw [eps0_def] at h1 ⊢
  field_simp
  ring

private theorem v_pos : (0 : Surreal.{0}) < (1 - ε₀)⁻¹ := by
  rw [v_eq]
  have := uval_pos
  linarith

private theorem v_lt_two : ((1 : Surreal.{0}) - ε₀)⁻¹ < 2 := by
  rw [v_eq]
  have := uval_lt_one
  linarith

private theorem mk_two_sub_v : ArchimedeanClass.mk (2 - ((1 : Surreal.{0}) - ε₀)⁻¹) = 0 := by
  have h : (2 : Surreal.{0}) - (1 - ε₀)⁻¹ = 1 - uval := by
    rw [v_eq]
    ring
  rw [h]
  exact mk_one_sub_infinitesimal infinitesimal_uval

private theorem mk_v : ArchimedeanClass.mk (((1 : Surreal.{0}) - ε₀)⁻¹) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [v_eq, stdPart_add_eq_left infinitesimal_uval, ArchimedeanClass.stdPart_one]
  norm_num

/-- The exact residual: chopping the geometric series after `n` terms leaves `ε₀ⁿ·v`. -/
private theorem sub_pS (n : ℕ) :
    ((1 : Surreal.{0}) - ε₀)⁻¹ - partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) n
      = ε₀ ^ n * (1 - ε₀)⁻¹ := by
  have h1 : (1 : Surreal.{0}) - ε₀ ≠ 0 := one_sub_eps_ne₀
  have h2 : (ε₀ : Surreal.{0}) - 1 ≠ 0 := sub_ne_zero.2 eps_ne_one₀
  rw [partialSum, geom_sum_eq eps_ne_one₀]
  field_simp
  ring

private theorem pS_lt_v (n : ℕ) :
    partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) n < (1 - ε₀)⁻¹ := by
  have h := sub_pS n
  have hp : (0 : Surreal.{0}) < ε₀ ^ n * (1 - ε₀)⁻¹ :=
    mul_pos (pow_pos eps0_pos₀ n) v_pos
  linarith

private theorem v_lt_rho (n : ℕ) :
    ((1 : Surreal.{0}) - ε₀)⁻¹
      < partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) n + 2 * ε₀ ^ n := by
  have h := sub_pS n
  have hlt : (ε₀ : Surreal.{0}) ^ n * (1 - ε₀)⁻¹ < 2 * ε₀ ^ n := by
    have := v_lt_two
    have hp := pow_pos eps0_pos₀ n
    nlinarith
  linarith

/-! ### The chain words: partial sums as left options, fine approximants as right
options of `W⁻¹` -/

private theorem hyR_mem : (ω^ (1 : IGame.{0}) + (0 : IGame)) ∈ Wgame.moves Player.right := by
  show _ ∈ (ω^ (1 : IGame.{0}) + (-1 : IGame)).moves Player.right
  refine add_left_mem_moves_add ?_ _
  rw [show (-1 : IGame.{0}).moves Player.right = (-1 : IGame.{0})ᴿ from rfl,
    neg_one_rightMoves₀]
  exact Set.mem_singleton _

private theorem mk_yR : Surreal.mk (ω^ (1 : IGame.{0}) + (0 : IGame)) = ω^ (1 : Surreal) := by
  rw [Surreal.mk_add, mk_wpow_one₀, Surreal.mk_zero, add_zero]

private theorem hyR_pos : (0 : IGame.{0}) < ω^ (1 : IGame.{0}) + (0 : IGame) := by
  rw [← @Surreal.mk_lt_mk 0 _ _ _, Surreal.mk_zero, mk_yR]
  exact wpow_pos _

private theorem hy2_mem : (((2 : Dyadic) : IGame.{0}) * ω^ (0 : IGame) + (-1 : IGame))
    ∈ Wgame.moves Player.left := by
  show _ ∈ (ω^ (1 : IGame.{0}) + (-1 : IGame)).moves Player.left
  refine add_right_mem_moves_add ?_ _
  rw [show (ω^ (1 : IGame.{0})).moves Player.left = (ω^ (1 : IGame.{0}))ᴸ from rfl,
    leftMoves_wpow_one₀]
  refine Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ ?_)
  norm_num

private theorem two_cast_eq₀ : ((2 : Dyadic) : Surreal.{0}) = 2 := by
  have h : ((2 : Dyadic) : Surreal.{0}) = (((2 : ℕ) : Dyadic) : Surreal) := by norm_num
  rw [h, dyadic_cast_natCast]
  norm_num

private theorem mk_y2 : Surreal.mk (((2 : Dyadic) : IGame.{0}) * ω^ (0 : IGame) + (-1 : IGame))
    = 1 := by
  rw [Surreal.mk_add, mk_dyadic_mul_wpow_zero₀, mk_neg_one₀, two_cast_eq₀]
  ring

private theorem hy2_pos : (0 : IGame.{0})
    < ((2 : Dyadic) : IGame.{0}) * ω^ (0 : IGame) + (-1 : IGame) := by
  rw [← @Surreal.mk_lt_mk 0 _ _ _, Surreal.mk_zero, mk_y2]
  norm_num

private theorem pS_mul_eps (m : ℕ) :
    partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 1) * ε₀
      = partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 2) - 1 := by
  induction m with
  | zero =>
    rw [show partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) 1 = 1 from by
        rw [partialSum, Finset.sum_range_one, pow_zero],
      show partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) 2 = 1 + ε₀ from by
        rw [partialSum, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]]
    ring
  | succ m ih =>
    rw [show partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 2)
        = partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 1) + ε₀ ^ (m + 1) from
        partialSum_succ _ _] at ih ⊢
    rw [show partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 3)
        = partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 2) + ε₀ ^ (m + 2) from
        partialSum_succ _ _,
      show partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 2)
        = partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 1) + ε₀ ^ (m + 1) from
        partialSum_succ _ _]
    have hpow : (ε₀ : Surreal.{0}) ^ (m + 1) * ε₀ = ε₀ ^ (m + 2) := by
      rw [← pow_succ]
    nlinarith [ih, hpow]

/-- The partial sums are left options of `W⁻¹`, shifted by `1`. -/
private theorem exists_chain_left_word (m : ℕ) :
    ∃ w, ∃ hw : w ∈ (Wgame⁻¹).moves Player.left,
      @Surreal.mk w (IGame.Numeric.of_mem_moves hw)
        = partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 1) - 1 := by
  induction m with
  | zero =>
    refine ⟨0, zero_mem_leftMoves_inv Wgame_pos, ?_⟩
    rw [show @Surreal.mk (0 : IGame.{0}) _ = 0 from Surreal.mk_zero,
      show partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) 1 = 1 from by
        rw [partialSum, Finset.sum_range_one, pow_zero]]
    ring
  | succ m ih =>
    obtain ⟨w, hw, hwv⟩ := ih
    haveI := IGame.Numeric.of_mem_moves hw
    have hyx : (ω^ (1 : IGame.{0}) + (0 : IGame))
        ∈ Wgame.moves (-(Player.left * Player.left)) := hyR_mem
    refine ⟨invOption Wgame (ω^ (1 : IGame.{0}) + (0 : IGame)) w,
      invOption_mem_moves_inv Wgame_pos hyR_pos hyx hw, ?_⟩
    haveI : (ω^ (1 : IGame.{0}) + (0 : IGame)).Numeric := IGame.Numeric.of_mem_moves hyx
    have hval : @Surreal.mk (invOption Wgame (ω^ (1 : IGame.{0}) + (0 : IGame)) w) _
        = (1 + (ω^ (1 : Surreal) - (ω^ (1 : Surreal) - 1))
            * (partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 1) - 1)) / ω^ (1 : Surreal) := by
      show Surreal.mk ((1 + ((ω^ (1 : IGame.{0}) + (0 : IGame)) - Wgame) * w)
          / (ω^ (1 : IGame.{0}) + (0 : IGame))) = _
      rw [Surreal.mk_div, Surreal.mk_add, Surreal.mk_one, Surreal.mk_mul, Surreal.mk_sub,
        mk_W, mk_yR, hwv]
    rw [hval]
    have hs : (1 : Surreal.{0}) + (ω^ (1 : Surreal) - (ω^ (1 : Surreal) - 1))
        * (partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 1) - 1)
        = partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 1) := by
      ring
    rw [hs, div_eq_mul_inv, show (ω^ (1 : Surreal.{0}))⁻¹ = ε₀ from by rw [eps0_def]]
    exact pS_mul_eps m

/-- Fine right approximants of `W⁻¹`: distance `(ω−2)·ε₀^(m+1)·v` above `u₀`. -/
private theorem exists_chain_right_word (m : ℕ) :
    ∃ w, ∃ hw : w ∈ (Wgame⁻¹).moves Player.right,
      @Surreal.mk w (IGame.Numeric.of_mem_moves hw)
        = uval + (ω^ (1 : Surreal) - 2) * ((ε₀ : Surreal.{0}) ^ (m + 1) * (1 - ε₀)⁻¹) := by
  obtain ⟨w, hw, hwv⟩ := exists_chain_left_word m
  haveI := IGame.Numeric.of_mem_moves hw
  have hyx : (((2 : Dyadic) : IGame.{0}) * ω^ (0 : IGame) + (-1 : IGame))
      ∈ Wgame.moves (-(Player.left * Player.right)) := hy2_mem
  refine ⟨invOption Wgame (((2 : Dyadic) : IGame.{0}) * ω^ (0 : IGame) + (-1 : IGame)) w,
    invOption_mem_moves_inv Wgame_pos hy2_pos hyx hw, ?_⟩
  haveI : (((2 : Dyadic) : IGame.{0}) * ω^ (0 : IGame) + (-1 : IGame)).Numeric :=
    IGame.Numeric.of_mem_moves hyx
  have hval : @Surreal.mk (invOption Wgame
      (((2 : Dyadic) : IGame.{0}) * ω^ (0 : IGame) + (-1 : IGame)) w) _
      = (1 + (1 - (ω^ (1 : Surreal) - 1))
          * (partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 1) - 1)) / 1 := by
    show Surreal.mk ((1 + ((((2 : Dyadic) : IGame.{0}) * ω^ (0 : IGame) + (-1 : IGame)) - Wgame)
        * w) / (((2 : Dyadic) : IGame.{0}) * ω^ (0 : IGame) + (-1 : IGame))) = _
    rw [Surreal.mk_div, Surreal.mk_add, Surreal.mk_one, Surreal.mk_mul, Surreal.mk_sub,
      mk_W, mk_y2, hwv]
  rw [hval, div_one]
  -- rearrange to the error form
  have hres := sub_pS (m + 1)
  have hveq := v_eq
  have hkey : partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 1) - 1
      = uval - ε₀ ^ (m + 1) * (1 - ε₀)⁻¹ := by
    have h : partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 1)
        = (1 - ε₀)⁻¹ - ε₀ ^ (m + 1) * (1 - ε₀)⁻¹ := by linarith
    rw [h, hveq]
    ring
  rw [hkey]
  have hxu : (ω^ (1 : Surreal.{0}) - 1) * uval = 1 := by
    rw [uval]
    exact mul_inv_cancel₀ xval_pos.ne'
  linear_combination -hxu

/-! ### The cofinality and the `ω²` bound for `ω/(ω−1)` -/

private theorem mk_eps0_pow_all (n : ℕ) :
    ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n)
      = ArchimedeanClass.mk (ω^ (((-(n : ℤ) : ℤ)) : Surreal.{0})) := by
  cases n with
  | zero =>
    rw [pow_zero]
    have h : (((-((0 : ℕ) : ℤ) : ℤ)) : Surreal.{0}) = 0 := by push_cast; ring
    rw [h, wpow_zero]
  | succ n =>
    have h := mk_eps0_pow_int n
    have hc : (((-(n + 1) : ℤ) : ℤ) : Surreal.{0}) = (((-((n + 1 : ℕ) : ℤ) : ℤ)) : Surreal.{0}) := by
      push_cast
      ring
    rwa [hc] at h

private theorem mk_two_natCast : ArchimedeanClass.mk ((2 : Surreal.{0})) = 0 := by
  have h : (2 : Surreal.{0}) = (((2 : ℕ) : ℝ) : Surreal) := by
    rw [Real.toSurreal_natCast]
    norm_num
  rw [h]
  exact mk_realCast (by norm_num)

private theorem mk_wpow_one_sub_two : ArchimedeanClass.mk (ω^ (1 : Surreal.{0}) - 2)
    = ArchimedeanClass.mk (ω^ (1 : Surreal.{0})) := by
  have h := mk_wpow_one_sub_dyadic 2
  rwa [two_cast_eq₀] at h

private theorem shape_succ_le_omega_sq (m : ℕ) :
    (NatOrdinal.of Ordinal.omega0 * ((m : ℕ) : NatOrdinal) + ((m : ℕ) : NatOrdinal)) + 1
      ≤ NatOrdinal.of Ordinal.omega0 * NatOrdinal.of Ordinal.omega0 := by
  refine omega_shape_le_omega_mul_omega (m + 1) ?_
  have hc : (((m + 1) : ℕ) : NatOrdinal) = ((m : ℕ) : NatOrdinal) + 1 := by
    push_cast
    ring
  rw [hc]
  calc NatOrdinal.of Ordinal.omega0 * ((m : ℕ) : NatOrdinal) + ((m : ℕ) : NatOrdinal) + 1
      = NatOrdinal.of Ordinal.omega0 * ((m : ℕ) : NatOrdinal) + (((m : ℕ) : NatOrdinal) + 1) := by
        rw [add_assoc]
    _ ≤ NatOrdinal.of Ordinal.omega0 * (((m : ℕ) : NatOrdinal) + 1)
          + (((m : ℕ) : NatOrdinal) + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left NatOrdinal.le_add_right bot_le) le_rfl

/-- **`ω/(ω−1)` is born by day `ω·ω`**: the game `1 + W⁻¹` is mutually cofinal with the
cut on the partial sums and their `2·ε₀ⁿ`-translates, all of birthday shape `ω·m + m` —
made possible by the word-class invariant, which keeps every Conway-inverse option
outside the micro-halo. -/
theorem birthday_geomSum_limit_le_omega_mul_omega :
    (((1 : Surreal.{0}) - ε₀)⁻¹).birthday
      ≤ NatOrdinal.of Ordinal.omega0 * NatOrdinal.of Ordinal.omega0 := by
  classical
  -- the option families
  have hLg : ∀ n : ℕ, ∃ (g : IGame.{0}) (_ : g.Numeric),
      Surreal.mk g = partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) n ∧
      ∃ m : ℕ, g.birthday ≤ NatOrdinal.of Ordinal.omega0 * (m : NatOrdinal) + (m : NatOrdinal) := by
    intro n
    obtain ⟨g, gn, gv, gb⟩ := birthday_eq_iGameBirthday
      (partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) n)
    obtain ⟨m, hm⟩ := birthday_partialSum_geometric_le n
    exact ⟨g, gn, gv, m, by rw [gb]; exact hm⟩
  have hRg : ∀ n : ℕ, ∃ (g : IGame.{0}) (_ : g.Numeric),
      Surreal.mk g = partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) n + 2 * ε₀ ^ n ∧
      ∃ m : ℕ, g.birthday ≤ NatOrdinal.of Ordinal.omega0 * (m : NatOrdinal) + (m : NatOrdinal) := by
    intro n
    obtain ⟨g, gn, gv, gb⟩ := birthday_eq_iGameBirthday
      (partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) n + 2 * ε₀ ^ n)
    obtain ⟨m₁, hm₁⟩ := birthday_partialSum_geometric_le n
    have hm₂ := birthday_eps0_pow_le n
    refine ⟨g, gn, gv, m₁ + 2 * (n + 1), ?_⟩
    rw [gb]
    refine (birthday_add_le _ _).trans ?_
    have h2 : ((2 : Surreal.{0}) * ε₀ ^ n).birthday ≤ (ε₀ ^ n).birthday + (ε₀ ^ n).birthday := by
      have he : (2 : Surreal.{0}) * ε₀ ^ n = ε₀ ^ n + ε₀ ^ n := by ring
      rw [he]
      exact birthday_add_le _ _
    refine (add_le_add hm₁ (h2.trans (add_le_add hm₂ hm₂))).trans (le_of_eq ?_)
    push_cast
    ring
  choose gL hgLn hgLv hgLb using hLg
  choose gR hgRn hgRv hgRb using hRg
  haveI : ∀ n, (gL n).Numeric := hgLn
  haveI : ∀ n, (gR n).Numeric := hgRn
  set C : IGame.{0} := !{Set.range gL | Set.range gR} with hC
  have hCL : Cᴸ = Set.range gL := leftMoves_ofSets ..
  have hCR : Cᴿ = Set.range gR := rightMoves_ofSets ..
  set v : Surreal.{0} := ((1 : Surreal.{0}) - ε₀)⁻¹ with hv
  have hvu : v = 1 + uval := v_eq
  -- the mutual cofinality
  have hequiv : (1 : IGame.{0}) + Wgame⁻¹ ≈ C := by
    apply equiv_of_exists_le
    · -- left moves of `1 + W⁻¹`
      rw [forall_moves_add]
      constructor
      · intro i hi
        rw [show (1 : IGame.{0}).moves Player.left = (1 : IGame.{0})ᴸ from rfl,
          show (1 : IGame.{0})ᴸ = {0} from by simp, Set.mem_singleton_iff] at hi
        subst hi
        refine ⟨gL 1, by rw [hCL]; exact Set.mem_range_self 1, ?_⟩
        rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_zero, mk_inv_W, zero_add, hgLv]
        rw [show partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) 1 = 1 from by
          rw [partialSum, Finset.sum_range_one, pow_zero]]
        exact uval_lt_one.le
      · intro w hw
        haveI := IGame.Numeric.of_mem_moves hw
        obtain ⟨k, hk⟩ := inv_move_class Player.left w hw
        have hwlt : Surreal.mk w < uval := by
          rw [← mk_inv_W]
          exact Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt hw)
        have he_pos : 0 < uval - Surreal.mk w := by linarith
        have hmke : ArchimedeanClass.mk (uval - Surreal.mk w)
            = ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0})) := by
          rw [show uval - Surreal.mk w = -(Surreal.mk w - uval) from by ring,
            ArchimedeanClass.mk_neg]
          exact hk
        rcases le_or_gt 0 k with hk0 | hk0
        · -- coarse error: the whole option sits below `1`
          refine ⟨gL 1, by rw [hCL]; exact Set.mem_range_self 1, ?_⟩
          rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_one, hgLv]
          rw [show partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) 1 = 1 from by
            rw [partialSum, Finset.sum_range_one, pow_zero]]
          have hlt : uval < uval - Surreal.mk w := by
            refine lt_of_mk_lt_mk' he_pos ?_
            rw [hmke, mk_uval]
            exact mk_wpow_int_anti (by omega)
          linarith
        · -- fine error: fit under the matching partial sum
          set n : ℕ := (-k).toNat with hn
          have hkn : k = -(n : ℤ) := by
            rw [hn]
            omega
          refine ⟨gL (n + 1), by rw [hCL]; exact Set.mem_range_self (n + 1), ?_⟩
          rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_one, hgLv]
          have hres := sub_pS (n + 1)
          have hgap : (0 : Surreal.{0}) < ε₀ ^ (n + 1) * (1 - ε₀)⁻¹ :=
            mul_pos (pow_pos eps0_pos₀ (n + 1)) v_pos
          have hlt : ε₀ ^ (n + 1) * (1 - ε₀)⁻¹ < uval - Surreal.mk w := by
            refine lt_of_mk_lt_mk' he_pos ?_
            rw [hmke, hkn, ArchimedeanClass.mk_mul, mk_v, add_zero, mk_eps0_pow_all]
            exact mk_wpow_int_anti (by omega)
          have hvv : (1 : Surreal.{0}) - ε₀ ≠ 0 := one_sub_eps_ne₀
          -- 1 + mk w ≤ pS (n+1) = v − ε₀^(n+1)·v
          have hps : partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (n + 1)
              = (1 - ε₀)⁻¹ - ε₀ ^ (n + 1) * (1 - ε₀)⁻¹ := by linarith
          rw [hps]
          have hvu' := v_eq
          linarith
    · -- right moves of `1 + W⁻¹`
      rw [forall_moves_add]
      constructor
      · intro i hi
        rw [show (1 : IGame.{0}).moves Player.right = (1 : IGame.{0})ᴿ from rfl,
          show (1 : IGame.{0})ᴿ = ∅ from by simp] at hi
        exact absurd hi (Set.notMem_empty i)
      · intro w hw
        haveI := IGame.Numeric.of_mem_moves hw
        obtain ⟨k, hk⟩ := inv_move_class Player.right w hw
        have hwgt : uval < Surreal.mk w := by
          rw [← mk_inv_W]
          exact Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right hw)
        have he_pos : 0 < Surreal.mk w - uval := by linarith
        rcases le_or_gt 0 k with hk0 | hk0
        · refine ⟨gR 1, by rw [hCR]; exact Set.mem_range_self 1, ?_⟩
          rw [← Surreal.mk_le_mk, hgRv, Surreal.mk_add, Surreal.mk_one]
          rw [show partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) 1 = 1 from by
            rw [partialSum, Finset.sum_range_one, pow_zero], pow_one]
          have h2e : (0 : Surreal.{0}) < 2 * ε₀ := by
            have := eps0_pos₀
            linarith
          have hlt : 2 * ε₀ < Surreal.mk w - uval := by
            refine lt_of_mk_lt_mk' he_pos ?_
            rw [hk, ArchimedeanClass.mk_mul, mk_two_natCast, zero_add]
            have h := mk_eps0_pow_all 1
            rw [pow_one] at h
            rw [h]
            exact mk_wpow_int_anti (by omega)
          have := uval_pos
          linarith
        · set n : ℕ := (-k).toNat with hn
          have hkn : k = -(n : ℤ) := by
            rw [hn]
            omega
          refine ⟨gR (n + 1), by rw [hCR]; exact Set.mem_range_self (n + 1), ?_⟩
          rw [← Surreal.mk_le_mk, hgRv, Surreal.mk_add, Surreal.mk_one]
          have hres := sub_pS (n + 1)
          have hgap : (0 : Surreal.{0}) < ε₀ ^ (n + 1) * (2 - (1 - ε₀)⁻¹) := by
            refine mul_pos (pow_pos eps0_pos₀ (n + 1)) ?_
            have := v_lt_two
            linarith
          have hlt : ε₀ ^ (n + 1) * (2 - (1 - ε₀)⁻¹) < Surreal.mk w - uval := by
            refine lt_of_mk_lt_mk' he_pos ?_
            rw [hk, hkn, ArchimedeanClass.mk_mul, mk_two_sub_v, add_zero, mk_eps0_pow_all]
            exact mk_wpow_int_anti (by omega)
          -- ρ_{n+1} = v + ε₀^{n+1}(2 − v) ≤ 1 + mk w
          have hrho : partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (n + 1) + 2 * ε₀ ^ (n + 1)
              = (1 - ε₀)⁻¹ + ε₀ ^ (n + 1) * (2 - (1 - ε₀)⁻¹) := by
            have h : partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (n + 1)
                = (1 - ε₀)⁻¹ - ε₀ ^ (n + 1) * (1 - ε₀)⁻¹ := by linarith
            rw [h]
            ring
          rw [hrho]
          have hvu' := v_eq
          linarith
    · -- cut lefts are dominated by chain words
      rw [hCL]
      rintro b ⟨n, rfl⟩
      cases n with
      | zero =>
        refine ⟨(0 : IGame.{0}) + Wgame⁻¹, ?_, ?_⟩
        · refine add_right_mem_moves_add ?_ _
          rw [show (1 : IGame.{0}).moves Player.left = (1 : IGame.{0})ᴸ from rfl,
            show (1 : IGame.{0})ᴸ = {0} from by simp]
          exact Set.mem_singleton _
        · rw [← Surreal.mk_le_mk, hgLv, Surreal.mk_add, Surreal.mk_zero, mk_inv_W, zero_add]
          rw [show partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) 0 = 0 from partialSum_zero _]
          exact uval_pos.le
      | succ m =>
        obtain ⟨w, hw, hwv⟩ := exists_chain_left_word m
        refine ⟨(1 : IGame.{0}) + w, add_left_mem_moves_add hw _, ?_⟩
        haveI := IGame.Numeric.of_mem_moves hw
        rw [← Surreal.mk_le_mk, hgLv, Surreal.mk_add, Surreal.mk_one, hwv]
        linarith [le_refl (partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) (m + 1))]
    · -- cut rights dominate fine right words
      rw [hCR]
      rintro b ⟨n, rfl⟩
      obtain ⟨w, hw, hwv⟩ := exists_chain_right_word (n + 1)
      rw [show n + 1 + 1 = n + 2 from rfl] at hwv
      refine ⟨(1 : IGame.{0}) + w, add_left_mem_moves_add hw _, ?_⟩
      haveI := IGame.Numeric.of_mem_moves hw
      rw [← Surreal.mk_le_mk, hgRv, Surreal.mk_add, Surreal.mk_one, hwv]
      -- 1 + u₀ + (ω−2)·ε₀^{n+2}·v ≤ pS n + 2·ε₀^n
      have hres := sub_pS n
      have hE_pos : (0 : Surreal.{0}) < (ω^ (1 : Surreal) - 2)
          * (ε₀ ^ (n + 2) * (1 - ε₀)⁻¹) := by
        refine mul_pos ?_ (mul_pos (pow_pos eps0_pos₀ (n + 2)) v_pos)
        have h2 := natCast_lt_wpow_one 2
        have h2' : ((2 : ℕ) : Surreal.{0}) = 2 := by push_cast; ring
        rw [h2'] at h2
        linarith
      have hgap_pos : (0 : Surreal.{0}) < ε₀ ^ n * (2 - (1 - ε₀)⁻¹) := by
        refine mul_pos (pow_pos eps0_pos₀ n) ?_
        have := v_lt_two
        linarith
      have hlt : (ω^ (1 : Surreal.{0}) - 2) * (ε₀ ^ (n + 2) * (1 - ε₀)⁻¹)
          < ε₀ ^ n * (2 - (1 - ε₀)⁻¹) := by
        refine lt_of_mk_lt_mk' hgap_pos ?_
        rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, mk_wpow_one_sub_two,
          ArchimedeanClass.mk_mul, mk_v, add_zero, mk_two_sub_v, add_zero,
          mk_eps0_pow_all, mk_eps0_pow_all, mk_wpow_one_int, mk_wpow_int_add]
        exact mk_wpow_int_anti (by omega)
      have hrho : partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) n + 2 * ε₀ ^ n
          = (1 - ε₀)⁻¹ + ε₀ ^ n * (2 - (1 - ε₀)⁻¹) := by
        have h : partialSum (fun k ↦ (ε₀ : Surreal.{0}) ^ k) n
            = (1 - ε₀)⁻¹ - ε₀ ^ n * (1 - ε₀)⁻¹ := by linarith
        rw [h]
        ring
      rw [hrho]
      have hvu' := v_eq
      linarith
  -- the cut is numeric
  have hCn : IGame.Numeric C := by
    refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
    · rw [hC, leftMoves_ofSets] at hy
      rw [hC, rightMoves_ofSets] at hz
      obtain ⟨n, rfl⟩ := hy
      obtain ⟨m, rfl⟩ := hz
      rw [← Surreal.mk_lt_mk, hgLv, hgRv]
      have h1 := pS_lt_v n
      have h2 := v_lt_rho m
      linarith
    · cases p with
      | left =>
        rw [hC, moves_ofSets] at hy
        obtain ⟨n, rfl⟩ := hy
        exact hgLn n
      | right =>
        rw [hC, moves_ofSets] at hy
        obtain ⟨n, rfl⟩ := hy
        exact hgRn n
  -- value and birthday
  have hval : ((1 : Surreal.{0}) - ε₀)⁻¹ = @Surreal.mk C hCn := by
    have h1 : Surreal.mk ((1 : IGame.{0}) + Wgame⁻¹) = ((1 : Surreal.{0}) - ε₀)⁻¹ := by
      rw [Surreal.mk_add, Surreal.mk_one, mk_inv_W, ← v_eq]
    rw [← h1]
    exact Surreal.mk_eq hequiv
  refine le_of_eq_of_le (congrArg birthday hval) ?_
  refine (birthday_mk_le _).trans ?_
  rw [hC, IGame.birthday_ofSets]
  refine max_le ?_ ?_
  · refine csSup_le' ?_
    rintro o ⟨g, ⟨n, rfl⟩, rfl⟩
    rw [Function.comp_apply, Order.succ_eq_add_one]
    obtain ⟨m, hm⟩ := hgLb n
    exact (add_le_add hm (le_refl 1)).trans (shape_succ_le_omega_sq m)
  · refine csSup_le' ?_
    rintro o ⟨g, ⟨n, rfl⟩, rfl⟩
    rw [Function.comp_apply, Order.succ_eq_add_one]
    obtain ⟨m, hm⟩ := hgRb n
    exact (add_le_add hm (le_refl 1)).trans (shape_succ_le_omega_sq m)

/-- The `ω/(ω−1)` form. -/
theorem birthday_omega_div_omega_sub_one_le :
    ((ω^ (1 : Surreal.{0})) / (ω^ (1 : Surreal) - 1)).birthday
      ≤ NatOrdinal.of Ordinal.omega0 * NatOrdinal.of Ordinal.omega0 := by
  rw [← geomSum_limit_eq]
  exact birthday_geomSum_limit_le_omega_mul_omega

/-- **The halo-minimality conjecture, reduced to one inequality**: given the squeeze
(`hahnSum` of the geometric series and `ω/(ω−1)` are both born in `[ω·2, ω²]`), the
conjecture `hahnSum (Σ ω⁻ᵏ) = ω/(ω−1)` holds **iff**
`birthday (ω/(ω−1)) ≤ birthday (hahnSum (Σ ω⁻ᵏ))`. -/
theorem hahnSum_geometric_eq_iff_birthday_le :
    hahnSum geometric_strict_dominating = ((1 : Surreal.{0}) - ε₀)⁻¹ ↔
      (((1 : Surreal.{0}) - ε₀)⁻¹).birthday
        ≤ (hahnSum geometric_strict_dominating).birthday := by
  constructor
  · intro h
    rw [h]
  · intro h
    exact hahnSum_eq_of_isHahnSum_of_birthday_le _ isHahnSum_geometric h

end Surreal

end
