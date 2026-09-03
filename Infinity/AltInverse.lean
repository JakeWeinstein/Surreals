/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.InverseBirthday
import Infinity.AltGeometric

/-!
# `(1+ω⁻¹)⁻¹` is born by day `ω²`: the Conway-inverse cofinality, mirrored

The alternating census (`Infinity.AltGeometric`) placed `v := (1+ω⁻¹)⁻¹ = ω/(ω+1)`
at birthday `≥ ω²`; this file supplies the matching upper bound by the Conway-inverse
device of `Infinity.InverseBirthday`, in its cleanest possible instance: invert the
game `X = 1 + ω^(−1)` (value `1 + ω⁻¹`) directly.

The structure is *simpler* than the `ω/(ω−1)` case. The value-`1` left option of `X`
gives `x − y = ω⁻¹`, so the `y = 1` word-chain from `a = 0` multiplies the error by
`−ω⁻¹` each step and generates **exactly the alternating partial sums**
`Sₙ = Σ_{k<n} (−1)ᵏω⁻ᵏ` (via `1 − ω⁻¹·Sₙ = Sₙ₊₁`), alternating sides of `X⁻¹`:
even-index sums below `v`, odd-index sums above. So the cheap two-sided cut is just
`!{S_even | S_odd}` — no translates, no manufactured right approximants.

* `inv_move_class` — the word-class invariant: every option of `X⁻¹` differs from `v`
  by exactly the class of `ω^k`, `k : ℤ` (options of value `ω⁻¹` coarsen by one power,
  the value-`1` option refines by one, dyadic options `1+q` keep the class).
* `birthday_inv_one_add_eps0_le` — **`birthday ((1+ω⁻¹)⁻¹) ≤ ω·ω`**.

With `AltGeometric.omega_sq_le_birthday_inv_one_add` this pins
`birthday ((1+ω⁻¹)⁻¹) = ω²` exactly.
-/

open ArchimedeanClass IGame Set

noncomputable section

namespace Surreal

local notation "Ω" => NatOrdinal.of Ordinal.omega0
local notation "ε₀" => eps0

/-! ### The anchor game `X = 1 + ω^(−1)` and its value `1 + ω⁻¹` -/

private def Xgame : IGame.{0} := 1 + ω^ (-1 : IGame)

instance : IGame.Numeric Xgame := by
  unfold Xgame
  infer_instance

private theorem mk_neg_one₀ : Surreal.mk (-1 : IGame.{0}) = -1 := by
  show Surreal.mk (-(1 : IGame.{0})) = -1
  rw [Surreal.mk_neg, Surreal.mk_one]

private theorem mk_wpow_neg_one₀ : Surreal.mk (ω^ (-1 : IGame.{0})) = ε₀ := by
  rw [Surreal.mk_wpow, mk_neg_one₀,
    show (-1 : Surreal.{0}) = -(1 : Surreal) from rfl, wpow_neg, eps0_def]

private theorem mk_X : Surreal.mk Xgame = (1 : Surreal.{0}) + ε₀ := by
  show Surreal.mk ((1 : IGame.{0}) + ω^ (-1 : IGame)) = _
  rw [Surreal.mk_add, Surreal.mk_one, mk_wpow_neg_one₀]

private theorem Xgame_pos : (0 : IGame.{0}) < Xgame := by
  rw [← @Surreal.mk_lt_mk 0 Xgame _ _, Surreal.mk_zero, mk_X]
  exact one_add_eps0_pos

private theorem mk_inv_X : Surreal.mk (Xgame⁻¹) = ((1 : Surreal.{0}) + ε₀)⁻¹ := by
  rw [Surreal.mk_inv, mk_X]

/-! ### Class toolkit (adapted from `Infinity.InverseBirthday`) -/

/-- Coarser class dominates: positives of strictly coarser class are strictly larger. -/
private theorem lt_of_mk_lt_mk' {a b : Surreal.{0}} (hb : 0 < b)
    (hmk : ArchimedeanClass.mk b < ArchimedeanClass.mk a) : a < b := by
  have h := (ArchimedeanClass.mk_lt_mk).1 hmk 1
  rw [one_smul] at h
  calc a ≤ |a| := le_abs_self a
    _ < |b| := h
    _ = b := abs_of_pos hb

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
    have hc : (((-(n + 1) : ℤ) : ℤ) : Surreal.{0})
        = (((-((n + 1 : ℕ) : ℤ) : ℤ)) : Surreal.{0}) := by
      push_cast
      ring
    rwa [hc] at h

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

/-- `ω⁻¹ − q` has class `0` for every nonzero dyadic `q`. -/
private theorem mk_eps0_sub_dyadic {q : Dyadic} (hq : q ≠ 0) :
    ArchimedeanClass.mk ((ε₀ : Surreal.{0}) - (q : Surreal)) = 0 := by
  have h : ArchimedeanClass.mk ((q : Surreal.{0}))
      < ArchimedeanClass.mk (ε₀ : Surreal.{0}) := by
    rw [mk_dyadic_cast_ne_zero hq]
    exact eps0_infinitesimal
  rw [ArchimedeanClass.mk_sub_eq_mk_right h, mk_dyadic_cast_ne_zero hq]

/-- `1 + q` has class `0` for every positive dyadic `q`. -/
private theorem mk_one_add_dyadic {q : Dyadic} (hq : 0 < q) :
    ArchimedeanClass.mk ((1 : Surreal.{0}) + (q : Surreal)) = 0 := by
  have hne : (1 + q : Dyadic) ≠ 0 := by
    have h1 : (0 : Dyadic) < 1 := one_pos
    intro h0
    rw [← h0] at h1
    linarith
  rw [show (1 : Surreal.{0}) + (q : Surreal) = (((1 + q : Dyadic)) : Surreal) from by
    rw [dyadic_cast_add', dyadic_cast_one]]
  exact mk_dyadic_cast_ne_zero hne

/-! ### The moves of `X` -/

private theorem neg_one_leftMoves₀ : (-1 : IGame.{0})ᴸ = ∅ := by
  rw [show (-1 : IGame.{0}) = -(1 : IGame) from rfl]
  simp

private theorem neg_one_rightMoves₀ : (-1 : IGame.{0})ᴿ = {0} := by
  rw [show (-1 : IGame.{0}) = -(1 : IGame) from rfl]
  simp

private theorem leftMoves_wpow_neg_one₀ : (ω^ (-1 : IGame.{0}))ᴸ = {0} := by
  rw [leftMoves_wpow, neg_one_leftMoves₀]
  simp

private theorem rightMoves_wpow_neg_one₀ : (ω^ (-1 : IGame.{0}))ᴿ =
    (fun r : Dyadic ↦ (r : IGame) * ω^ (0 : IGame)) '' Set.Ioi 0 := by
  rw [rightMoves_wpow, neg_one_rightMoves₀, Set.image2_singleton_right]

private theorem mk_dyadic_mul_wpow_zero₀ (q : Dyadic) :
    Surreal.mk ((q : IGame.{0}) * ω^ (0 : IGame)) = (q : Surreal) := by
  rw [Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow, Surreal.mk_zero, wpow_zero, mul_one]

/-- Every move of `X` has value `ω⁻¹`, `1`, or `1 + q` for a positive dyadic `q`. -/
private theorem X_move_value (p : Player) (y : IGame.{0}) (hy : y ∈ Xgame.moves p) :
    @Surreal.mk y (IGame.Numeric.of_mem_moves hy) = ε₀ ∨
      @Surreal.mk y (IGame.Numeric.of_mem_moves hy) = 1 ∨
      ∃ q : Dyadic, 0 < q ∧
        @Surreal.mk y (IGame.Numeric.of_mem_moves hy) = 1 + (q : Surreal) := by
  haveI := IGame.Numeric.of_mem_moves hy
  have hy' : y ∈ ((1 : IGame.{0}) + ω^ (-1 : IGame)).moves p := hy
  rw [moves_add] at hy'
  rcases hy' with ⟨i, hi, rfl⟩ | ⟨z, hz, rfl⟩
  · -- a move of the `1` side, plus `ω^(−1)`
    cases p with
    | left =>
      rw [show (1 : IGame.{0}).moves Player.left = (1 : IGame.{0})ᴸ from rfl,
        show (1 : IGame.{0})ᴸ = {0} from by simp, Set.mem_singleton_iff] at hi
      subst hi
      refine .inl ?_
      rw [show @Surreal.mk ((0 : IGame.{0}) + ω^ (-1 : IGame)) _
          = Surreal.mk (0 : IGame.{0}) + Surreal.mk (ω^ (-1 : IGame.{0}))
          from Surreal.mk_add .., Surreal.mk_zero, mk_wpow_neg_one₀, zero_add]
    | right =>
      rw [show (1 : IGame.{0}).moves Player.right = (1 : IGame.{0})ᴿ from rfl,
        show (1 : IGame.{0})ᴿ = ∅ from by simp] at hi
      exact absurd hi (Set.notMem_empty i)
  · -- the `1`, plus a move of `ω^(−1)`
    cases p with
    | left =>
      rw [show (ω^ (-1 : IGame.{0})).moves Player.left = (ω^ (-1 : IGame.{0}))ᴸ from rfl,
        leftMoves_wpow_neg_one₀, Set.mem_singleton_iff] at hz
      subst hz
      refine .inr (.inl ?_)
      rw [show @Surreal.mk ((1 : IGame.{0}) + (0 : IGame)) _
          = Surreal.mk (1 : IGame.{0}) + Surreal.mk (0 : IGame.{0})
          from Surreal.mk_add .., Surreal.mk_one, Surreal.mk_zero, add_zero]
    | right =>
      rw [show (ω^ (-1 : IGame.{0})).moves Player.right = (ω^ (-1 : IGame.{0}))ᴿ from rfl,
        rightMoves_wpow_neg_one₀] at hz
      obtain ⟨q, hq, rfl⟩ := hz
      refine .inr (.inr ⟨q, Set.mem_Ioi.1 hq, ?_⟩)
      rw [show @Surreal.mk ((1 : IGame.{0}) + (q : IGame) * ω^ (0 : IGame)) _
          = Surreal.mk (1 : IGame.{0}) + Surreal.mk ((q : IGame.{0}) * ω^ (0 : IGame))
          from Surreal.mk_add .., Surreal.mk_one, mk_dyadic_mul_wpow_zero₀]

/-! ### The word-class invariant -/

/-- **Every option of `X⁻¹` sits at distance exactly `ω^k` from `(1+ω⁻¹)⁻¹`** for some
integer `k`: the Conway-inverse words never enter the micro-halo. The `y = ω⁻¹` moves
coarsen the class by one `ω`-power, the `y = 1` move refines it by one, and the dyadic
moves `y = 1 + q` keep it. -/
private theorem inv_move_class :
    ∀ (p : Player) (y : IGame.{0}) (hy : y ∈ (Xgame⁻¹).moves p),
      ∃ k : ℤ, ArchimedeanClass.mk
          (@Surreal.mk y (IGame.Numeric.of_mem_moves hy) - ((1 : Surreal.{0}) + ε₀)⁻¹)
        = ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0})) := by
  refine invRec Xgame_pos ?_ ?_
  · -- the zero option: distance `v`, class `ω^0`
    refine ⟨0, ?_⟩
    rw [show @Surreal.mk (0 : IGame.{0}) (IGame.Numeric.of_mem_moves
        (zero_mem_leftMoves_inv Xgame_pos)) = 0 from Surreal.mk_zero,
      zero_sub, ArchimedeanClass.mk_neg, mk_inv_one_add_eps0,
      show (((0 : ℤ) : ℤ) : Surreal.{0}) = 0 from by push_cast; ring, wpow_zero,
      ArchimedeanClass.mk_one]
  · -- the inductive step
    intro p₁ p₂ y hy0 hyx a ha IH
    obtain ⟨k, hk⟩ := IH
    haveI hyn : y.Numeric := IGame.Numeric.of_mem_moves hyx
    haveI han : a.Numeric := IGame.Numeric.of_mem_moves ha
    have hyv0 : (0 : Surreal) < Surreal.mk y := by
      rw [← Surreal.mk_zero]
      exact Surreal.mk_lt_mk.2 hy0
    -- the value of the new word
    have hval : @Surreal.mk (invOption Xgame y a)
        (IGame.Numeric.of_mem_moves (invOption_mem_moves_inv Xgame_pos hy0 hyx ha))
        = (1 + (Surreal.mk y - ((1 : Surreal) + ε₀)) * Surreal.mk a) / Surreal.mk y := by
      show Surreal.mk ((1 + (y - Xgame) * a) / y) = _
      rw [Surreal.mk_div, Surreal.mk_add, Surreal.mk_one, Surreal.mk_mul, Surreal.mk_sub,
        mk_X]
    -- the exact error recursion
    have herr : (1 + (Surreal.mk y - ((1 : Surreal) + ε₀)) * Surreal.mk a) / Surreal.mk y
          - ((1 : Surreal.{0}) + ε₀)⁻¹
        = (((1 : Surreal) + ε₀) - Surreal.mk y)
            * (((1 : Surreal.{0}) + ε₀)⁻¹ - Surreal.mk a) / Surreal.mk y := by
      have hy' : Surreal.mk y ≠ 0 := hyv0.ne'
      have hx' : ((1 : Surreal.{0}) + ε₀) ≠ 0 := one_add_eps0_ne_zero
      have hx'' : (ε₀ + (1 : Surreal.{0})) ≠ 0 := by
        intro h0
        apply hx'
        linarith
      field_simp
      ring
    have hmk_va : ArchimedeanClass.mk (((1 : Surreal.{0}) + ε₀)⁻¹ - Surreal.mk a)
        = ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0})) := by
      rw [show ((1 : Surreal.{0}) + ε₀)⁻¹ - Surreal.mk a
          = -(Surreal.mk a - ((1 : Surreal.{0}) + ε₀)⁻¹) from by ring,
        ArchimedeanClass.mk_neg]
      exact hk
    rcases X_move_value _ y hyx with hqe | hq1 | ⟨q, hq0, hqv⟩
    · -- the `ω⁻¹` move: the error coarsens by one `ω`-power
      refine ⟨k + 1, ?_⟩
      rw [hval, herr]
      have hxy : ((1 : Surreal.{0}) + ε₀) - Surreal.mk y = 1 := by
        rw [hqe]
        ring
      rw [div_eq_mul_inv, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
        ArchimedeanClass.mk_inv, hxy, ArchimedeanClass.mk_one, zero_add, hmk_va, hqe]
      rw [show -ArchimedeanClass.mk (ε₀ : Surreal.{0})
          = ArchimedeanClass.mk ((ε₀ : Surreal.{0})⁻¹) from
          (ArchimedeanClass.mk_inv _).symm,
        show (ε₀ : Surreal.{0})⁻¹ = ω^ (1 : Surreal) from by rw [eps0_def, inv_inv],
        mk_wpow_one_int, mk_wpow_int_add]
    · -- the value-`1` move: the error refines by one `ω`-power
      refine ⟨k - 1, ?_⟩
      rw [hval, herr]
      have hxy : ((1 : Surreal.{0}) + ε₀) - Surreal.mk y = ε₀ := by
        rw [hq1]
        ring
      rw [div_eq_mul_inv, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
        ArchimedeanClass.mk_inv, hxy, hmk_va, hq1, ArchimedeanClass.mk_one, neg_zero,
        add_zero]
      rw [show ArchimedeanClass.mk (ε₀ : Surreal.{0})
          = ArchimedeanClass.mk (ω^ (((-1 : ℤ) : ℤ) : Surreal.{0})) from by
            rw [eps0_def]; exact mk_wpow_one_inv_int,
        mk_wpow_int_add]
      congr 2
      push_cast
      ring
    · -- a dyadic move `1 + q`: the error class is unchanged
      refine ⟨k, ?_⟩
      rw [hval, herr]
      have hxy : ((1 : Surreal.{0}) + ε₀) - Surreal.mk y = ε₀ - (q : Surreal) := by
        rw [hqv]
        ring
      rw [div_eq_mul_inv, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
        ArchimedeanClass.mk_inv, hxy, hmk_va, hqv, mk_one_add_dyadic hq0, neg_zero,
        add_zero, mk_eps0_sub_dyadic hq0.ne', zero_add]

/-! ### The alternating partial-sum ladder and the chain words -/

/-- The step identity of the alternating series: `1 − ω⁻¹·Sₙ = Sₙ₊₁`. -/
private theorem alt_step (n : ℕ) :
    (1 : Surreal.{0}) - ε₀ * monoS altCoeff n = monoS altCoeff (n + 1) := by
  have h := one_add_eps0_mul_monoS_alt n
  rw [monoS_succ n, altCoeff_cast, ← neg_pow]
  linear_combination -h

/-- Even partial sums sit exactly `ε₀^(2n)·v` below `v`. -/
private theorem monoS_alt_even (n : ℕ) :
    monoS altCoeff (2 * n)
      = ((1 : Surreal.{0}) + ε₀)⁻¹ - ε₀ ^ (2 * n) * (1 + ε₀)⁻¹ := by
  have h := sub_monoS_alt (2 * n)
  rw [Even.neg_pow (even_two_mul n)] at h
  linarith

/-- Odd partial sums sit exactly `ε₀^(2n+1)·v` above `v`. -/
private theorem monoS_alt_odd (n : ℕ) :
    monoS altCoeff (2 * n + 1)
      = ((1 : Surreal.{0}) + ε₀)⁻¹ + ε₀ ^ (2 * n + 1) * (1 + ε₀)⁻¹ := by
  have h := sub_monoS_alt (2 * n + 1)
  rw [Odd.neg_pow (odd_two_mul_add_one n), neg_mul] at h
  linarith

private theorem monoS_alt_even_lt (n : ℕ) :
    monoS altCoeff (2 * n) < ((1 : Surreal.{0}) + ε₀)⁻¹ := by
  rw [monoS_alt_even]
  have h := mul_pos (pow_pos eps0_pos (2 * n)) inv_one_add_eps0_pos
  linarith

private theorem lt_monoS_alt_odd (n : ℕ) :
    ((1 : Surreal.{0}) + ε₀)⁻¹ < monoS altCoeff (2 * n + 1) := by
  rw [monoS_alt_odd]
  have h := mul_pos (pow_pos eps0_pos (2 * n + 1)) inv_one_add_eps0_pos
  linarith

/-- The value-`1` left move of `X`. -/
private theorem hy1_mem : (1 : IGame.{0}) ∈ Xgame.moves Player.left := by
  have h0 : (0 : IGame.{0}) ∈ (ω^ (-1 : IGame.{0})).moves Player.left :=
    zero_mem_leftMoves_wpow _
  have h := add_left_mem_moves_add h0 (1 : IGame.{0})
  rw [add_zero] at h
  exact h

/-- One chain step: the value-`1` move sends a word of value `s` on one side to a word
of value `1 − ω⁻¹·s` on the other. -/
private theorem chain_step (p₁ p₂ : Player)
    (hp : (1 : IGame.{0}) ∈ Xgame.moves (-(p₁ * p₂)))
    (w : IGame.{0}) (hw : w ∈ (Xgame⁻¹).moves p₁) :
    ∃ w', ∃ hw' : w' ∈ (Xgame⁻¹).moves p₂,
      @Surreal.mk w' (IGame.Numeric.of_mem_moves hw')
        = 1 - ε₀ * @Surreal.mk w (IGame.Numeric.of_mem_moves hw) := by
  haveI := IGame.Numeric.of_mem_moves hw
  refine ⟨invOption Xgame 1 w,
    invOption_mem_moves_inv Xgame_pos IGame.zero_lt_one hp hw, ?_⟩
  have hval : @Surreal.mk (invOption Xgame 1 w)
      (IGame.Numeric.of_mem_moves
        (invOption_mem_moves_inv Xgame_pos IGame.zero_lt_one hp hw))
      = (1 + ((1 : Surreal) - ((1 : Surreal) + ε₀)) * Surreal.mk w) / 1 := by
    show Surreal.mk ((1 + ((1 : IGame.{0}) - Xgame) * w) / (1 : IGame.{0})) = _
    rw [Surreal.mk_div, Surreal.mk_add, Surreal.mk_one, Surreal.mk_mul, Surreal.mk_sub,
      mk_X, Surreal.mk_one]
  rw [hval, div_one]
  ring

/-- **The chain words**: every alternating partial sum is realized by a word of `X⁻¹` —
even-index sums as left options, odd-index sums as right options. -/
private theorem exists_chain_words (m : ℕ) :
    (∃ w, ∃ hw : w ∈ (Xgame⁻¹).moves Player.left,
      @Surreal.mk w (IGame.Numeric.of_mem_moves hw) = monoS altCoeff (2 * m)) ∧
    (∃ w, ∃ hw : w ∈ (Xgame⁻¹).moves Player.right,
      @Surreal.mk w (IGame.Numeric.of_mem_moves hw) = monoS altCoeff (2 * m + 1)) := by
  induction m with
  | zero =>
    have hL : ∃ w, ∃ hw : w ∈ (Xgame⁻¹).moves Player.left,
        @Surreal.mk w (IGame.Numeric.of_mem_moves hw) = monoS altCoeff (2 * 0) := by
      refine ⟨0, zero_mem_leftMoves_inv Xgame_pos, ?_⟩
      rw [show @Surreal.mk (0 : IGame.{0}) (IGame.Numeric.of_mem_moves
          (zero_mem_leftMoves_inv Xgame_pos)) = 0 from Surreal.mk_zero,
        show (2 * 0 : ℕ) = 0 from rfl, monoS_zero]
    refine ⟨hL, ?_⟩
    obtain ⟨w, hw, hwv⟩ := hL
    obtain ⟨w', hw', hwv'⟩ := chain_step Player.left Player.right hy1_mem w hw
    refine ⟨w', hw', ?_⟩
    rw [hwv', hwv, show (2 * 0 + 1 : ℕ) = (2 * 0) + 1 from rfl]
    exact alt_step (2 * 0)
  | succ m ih =>
    obtain ⟨-, ⟨wR, hwR, hvR⟩⟩ := ih
    have hL : ∃ w, ∃ hw : w ∈ (Xgame⁻¹).moves Player.left,
        @Surreal.mk w (IGame.Numeric.of_mem_moves hw) = monoS altCoeff (2 * (m + 1)) := by
      obtain ⟨w', hw', hwv'⟩ := chain_step Player.right Player.left hy1_mem wR hwR
      refine ⟨w', hw', ?_⟩
      rw [hwv', hvR, show (2 * (m + 1) : ℕ) = (2 * m + 1) + 1 from by ring]
      exact alt_step (2 * m + 1)
    refine ⟨hL, ?_⟩
    obtain ⟨w, hw, hwv⟩ := hL
    obtain ⟨w', hw', hwv'⟩ := chain_step Player.left Player.right hy1_mem w hw
    refine ⟨w', hw', ?_⟩
    rw [hwv', hwv]
    exact alt_step (2 * (m + 1))

/-! ### Pricing the cut options -/

/-- Every alternating partial sum is born strictly inside `ω·ω`. -/
private theorem birthday_altS_succ_le (n : ℕ) :
    (monoS altCoeff n).birthday + 1 ≤ Ω * Ω := by
  cases n with
  | zero =>
    rw [monoS_zero, birthday_zero, zero_add]
    refine omega_shape_le_omega_mul_omega 1 ?_
    rw [Nat.cast_one, mul_one]
    exact NatOrdinal.le_add_left
  | succ B =>
    refine (birthday_monoS_add_one_le altCoeff_ne_zero B).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    exact (NatOrdinal.natCast_lt_omega0 (B + 1)).le

/-! ### The cofinality and the `ω²` bound -/

/-- **`(1+ω⁻¹)⁻¹` is born by day `ω·ω`**: the Conway inverse `X⁻¹` of `X = 1 + ω^(−1)`
is mutually cofinal with the two-sided cut on the alternating partial sums (evens on the
left, odds on the right) — the word-class invariant keeps every inverse option outside
the micro-halo, and the value-`1` word-chain supplies approximants at every scale on
both sides. Each partial sum costs `< ω·(n+1)`, so the cut is born by `ω·ω`. -/
theorem birthday_inv_one_add_eps0_le :
    (((1 : Surreal.{0}) + eps0)⁻¹).birthday
      ≤ NatOrdinal.of Ordinal.omega0 * NatOrdinal.of Ordinal.omega0 := by
  classical
  -- realizations of the partial sums
  have hLg : ∀ m : ℕ, ∃ (g : IGame.{0}) (_ : g.Numeric),
      Surreal.mk g = monoS altCoeff (2 * m) ∧ g.birthday + 1 ≤ Ω * Ω := by
    intro m
    obtain ⟨g, gn, gv, gb⟩ := birthday_eq_iGameBirthday (monoS altCoeff (2 * m))
    refine ⟨g, gn, gv, ?_⟩
    rw [gb]
    exact birthday_altS_succ_le (2 * m)
  have hRg : ∀ m : ℕ, ∃ (g : IGame.{0}) (_ : g.Numeric),
      Surreal.mk g = monoS altCoeff (2 * m + 1) ∧ g.birthday + 1 ≤ Ω * Ω := by
    intro m
    obtain ⟨g, gn, gv, gb⟩ := birthday_eq_iGameBirthday (monoS altCoeff (2 * m + 1))
    refine ⟨g, gn, gv, ?_⟩
    rw [gb]
    exact birthday_altS_succ_le (2 * m + 1)
  choose gL hgLn hgLv hgLb using hLg
  choose gR hgRn hgRv hgRb using hRg
  haveI : ∀ n, (gL n).Numeric := hgLn
  haveI : ∀ n, (gR n).Numeric := hgRn
  set C : IGame.{0} := !{Set.range gL | Set.range gR} with hC
  have hCL : Cᴸ = Set.range gL := leftMoves_ofSets ..
  have hCR : Cᴿ = Set.range gR := rightMoves_ofSets ..
  -- the mutual cofinality
  have hequiv : Xgame⁻¹ ≈ C := by
    apply equiv_of_exists_le
    · -- left moves of `X⁻¹` fit under even partial sums
      intro w hw
      haveI := IGame.Numeric.of_mem_moves hw
      obtain ⟨k, hk⟩ := inv_move_class Player.left w hw
      have hwlt : Surreal.mk w < ((1 : Surreal.{0}) + ε₀)⁻¹ := by
        rw [← mk_inv_X]
        exact Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt hw)
      have he_pos : (0 : Surreal.{0}) < ((1 : Surreal.{0}) + ε₀)⁻¹ - Surreal.mk w := by
        linarith
      have hmke : ArchimedeanClass.mk (((1 : Surreal.{0}) + ε₀)⁻¹ - Surreal.mk w)
          = ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0})) := by
        rw [show ((1 : Surreal.{0}) + ε₀)⁻¹ - Surreal.mk w
            = -(Surreal.mk w - ((1 : Surreal.{0}) + ε₀)⁻¹) from by ring,
          ArchimedeanClass.mk_neg]
        exact hk
      refine ⟨gL ((-k).toNat + 1), by rw [hCL]; exact Set.mem_range_self _, ?_⟩
      rw [← Surreal.mk_le_mk, hgLv, monoS_alt_even]
      have hlt : (ε₀ : Surreal.{0}) ^ (2 * ((-k).toNat + 1)) * ((1 : Surreal.{0}) + ε₀)⁻¹
          < ((1 : Surreal.{0}) + ε₀)⁻¹ - Surreal.mk w := by
        refine lt_of_mk_lt_mk' he_pos ?_
        rw [hmke, ArchimedeanClass.mk_mul, mk_inv_one_add_eps0, add_zero, mk_eps0_pow_all]
        exact mk_wpow_int_anti (by omega)
      linarith
    · -- right moves of `X⁻¹` dominate odd partial sums
      intro w hw
      haveI := IGame.Numeric.of_mem_moves hw
      obtain ⟨k, hk⟩ := inv_move_class Player.right w hw
      have hwgt : ((1 : Surreal.{0}) + ε₀)⁻¹ < Surreal.mk w := by
        rw [← mk_inv_X]
        exact Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right hw)
      have he_pos : (0 : Surreal.{0}) < Surreal.mk w - ((1 : Surreal.{0}) + ε₀)⁻¹ := by
        linarith
      refine ⟨gR ((-k).toNat), by rw [hCR]; exact Set.mem_range_self _, ?_⟩
      rw [← Surreal.mk_le_mk, hgRv, monoS_alt_odd]
      have hlt : (ε₀ : Surreal.{0}) ^ (2 * (-k).toNat + 1) * ((1 : Surreal.{0}) + ε₀)⁻¹
          < Surreal.mk w - ((1 : Surreal.{0}) + ε₀)⁻¹ := by
        refine lt_of_mk_lt_mk' he_pos ?_
        rw [hk, ArchimedeanClass.mk_mul, mk_inv_one_add_eps0, add_zero, mk_eps0_pow_all]
        exact mk_wpow_int_anti (by omega)
      linarith
    · -- cut lefts are matched by even chain words, exactly
      rw [hCL]
      rintro b ⟨m, rfl⟩
      obtain ⟨⟨w, hw, hwv⟩, -⟩ := exists_chain_words m
      refine ⟨w, hw, ?_⟩
      haveI := IGame.Numeric.of_mem_moves hw
      rw [← Surreal.mk_le_mk, hgLv, hwv]
    · -- cut rights are matched by odd chain words, exactly
      rw [hCR]
      rintro b ⟨m, rfl⟩
      obtain ⟨-, ⟨w, hw, hwv⟩⟩ := exists_chain_words m
      refine ⟨w, hw, ?_⟩
      haveI := IGame.Numeric.of_mem_moves hw
      rw [← Surreal.mk_le_mk, hgRv, hwv]
  -- the cut is numeric
  have hCn : IGame.Numeric C := by
    refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
    · rw [hC, leftMoves_ofSets] at hy
      rw [hC, rightMoves_ofSets] at hz
      obtain ⟨n, rfl⟩ := hy
      obtain ⟨m, rfl⟩ := hz
      rw [← Surreal.mk_lt_mk, hgLv, hgRv]
      exact (monoS_alt_even_lt n).trans (lt_monoS_alt_odd m)
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
  have hval : ((1 : Surreal.{0}) + ε₀)⁻¹ = @Surreal.mk C hCn := by
    rw [← mk_inv_X]
    exact Surreal.mk_eq hequiv
  refine le_of_eq_of_le (congrArg birthday hval) ?_
  refine (birthday_mk_le _).trans ?_
  rw [hC, IGame.birthday_ofSets]
  refine max_le ?_ ?_
  · refine csSup_le' ?_
    rintro o ⟨g, ⟨n, rfl⟩, rfl⟩
    rw [Function.comp_apply, Order.succ_eq_add_one]
    exact hgLb n
  · refine csSup_le' ?_
    rintro o ⟨g, ⟨n, rfl⟩, rfl⟩
    rw [Function.comp_apply, Order.succ_eq_add_one]
    exact hgRb n

end Surreal

end
