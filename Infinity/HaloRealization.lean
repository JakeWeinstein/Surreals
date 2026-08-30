import Infinity.DayOmega
import Infinity.Census

/-!
# Realizing the halo grid: `a + r·ω⁻¹` is born by day `ω + hgt r`

`Infinity.DayOmega` proved that the dyadic neighbours `d ± ω⁻¹` are born by day `ω`, by
exhibiting the Conway sum `d + ω^(−1)` as a two-sided cut with dyadic options. This file
runs the same *order-pinning* method (mutual cofinality via `equiv_of_exists_le`, no
simplicity theory) parametrically along the whole dyadic grid of the infinitesimal halo:

* `add_dyadic_mul_wpow_equiv_of_den_ne_one` / `add_dyadic_mul_wpow_equiv_intCast` — the
  **core cofinality computations**: for any numeric anchor game `x` whose options are
  separated from its value by rational gaps, the Conway sum `x + r·ω^(−1)` is mutually
  cofinal with a two-sided cut whose options realize `mk x + lower(r)·ω⁻¹` and
  `mk x + upper(r)·ω⁻¹` (respectively, for a positive integer `r = m`, with
  `mk x + (m−1)·ω⁻¹` on the left and the rational translates `mk x + q` on the right).
* `birthday_realCast_add_dyadic_mul_wpow_le` : for every real `a` and dyadic `r`,
  **`a + r·ω⁻¹` is born by day `ω + hgt r`** — the halo grid over any real anchor.
* `birthday_dyadic_add_dyadic_mul_wpow_le` : over a *dyadic* anchor the bound improves
  by one day: `d + r·ω⁻¹` is born by day `ω + (hgt r − 1)` for `r ≠ 0`. (For `r = ±1`
  this recovers the day-`ω` bound for `d ± ω⁻¹` from `Infinity.DayOmega`.)

These are the "realization" half of the day-`ω + n` censuses: they show the dyadic
`ω⁻¹`-grid around every real is born on the expected days. The converse half — nothing
*else* infinitesimally near a real is born below day `ω·2` — is the census induction of
`Infinity.GeometricBirthday`, whose candidate steps consume exactly these bounds.
-/

open ArchimedeanClass IGame Set

universe u

noncomputable section

namespace Surreal

/-! ### Prelude: moves of `ω^(−1)`, casts, and infinitesimal comparisons -/

/-- The left moves of the game `ω^ (−1)`. -/
theorem leftMoves_wpow_neg_one' : (ω^ (-1 : IGame.{u}))ᴸ = {0} := by
  have h1 : (-1 : IGame.{u})ᴸ = ∅ := by
    rw [show (-1 : IGame.{u}) = -(1 : IGame) from rfl]
    simp
  rw [leftMoves_wpow, h1]
  simp

/-- The right moves of the game `ω^ (−1)`. -/
theorem rightMoves_wpow_neg_one' : (ω^ (-1 : IGame.{u}))ᴿ =
    (fun r : Dyadic ↦ (r : IGame) * ω^ (0 : IGame)) '' Set.Ioi 0 := by
  have h1 : (-1 : IGame.{u})ᴿ = {0} := by
    rw [show (-1 : IGame.{u}) = -(1 : IGame) from rfl]
    simp
  rw [rightMoves_wpow, h1, Set.image2_singleton_right]

theorem mk_wpow_neg_one' : mk (ω^ (-1 : IGame.{u})) = ω^ (-1 : Surreal) := by
  rw [Surreal.mk_wpow]
  norm_num

theorem dyadic_cast_sub' (a b : Dyadic) :
    ((a - b : Dyadic) : Surreal) = (a : Surreal) - (b : Surreal) := by
  show (((a - b : Dyadic) : ℚ) : Surreal)
      = (((a : Dyadic) : ℚ) : Surreal) - (((b : Dyadic) : ℚ) : Surreal)
  have h : ((a - b : Dyadic) : ℚ) = (a : ℚ) - (b : ℚ) := by push_cast; ring
  rw [h, Rat.cast_sub]

theorem dyadic_cast_add' (a b : Dyadic) :
    ((a + b : Dyadic) : Surreal) = (a : Surreal) + (b : Surreal) := by
  show (((a + b : Dyadic) : ℚ) : Surreal)
      = (((a : Dyadic) : ℚ) : Surreal) + (((b : Dyadic) : ℚ) : Surreal)
  have h : ((a + b : Dyadic) : ℚ) = (a : ℚ) + (b : ℚ) := by push_cast; ring
  rw [h, Rat.cast_add]

theorem dyadic_cast_mul' (a b : Dyadic) :
    ((a * b : Dyadic) : Surreal) = (a : Surreal) * (b : Surreal) := by
  show (((a * b : Dyadic) : ℚ) : Surreal)
      = (((a : Dyadic) : ℚ) : Surreal) * (((b : Dyadic) : ℚ) : Surreal)
  have h : ((a * b : Dyadic) : ℚ) = (a : ℚ) * (b : ℚ) := by push_cast; ring
  rw [h, Rat.cast_mul]

theorem dyadic_cast_neg' (a : Dyadic) :
    ((-a : Dyadic) : Surreal) = -(a : Surreal) := by
  show (((-a : Dyadic) : ℚ) : Surreal) = -(((a : Dyadic) : ℚ) : Surreal)
  have h : ((-a : Dyadic) : ℚ) = -(a : ℚ) := by push_cast; ring
  rw [h, Rat.cast_neg]

theorem dyadic_cast_pos {q : Dyadic} (hq : 0 < q) : (0 : Surreal) < (q : Surreal) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  show (0 : Surreal) < ((q : ℚ) : Surreal)
  exact_mod_cast hq'

theorem dyadic_cast_lt {a b : Dyadic} (hab : a < b) : (a : Surreal) < (b : Surreal) := by
  have h : (0 : Dyadic) < b - a := sub_pos.2 hab
  have h2 := dyadic_cast_pos h
  rw [dyadic_cast_sub'] at h2
  linarith

/-- Any dyadic multiple of `ω⁻¹` is infinitesimal. -/
theorem infinitesimal_dyadic_mul_wpow (s : Dyadic) :
    Infinitesimal ((s : Surreal) * ω^ (-1 : Surreal)) := by
  have hfin : IsFinite ((s : Surreal)) := by
    have h : ((s : Dyadic) : Surreal) = (((s : ℚ) : ℝ) : Surreal) := by
      rw [← Real.toSurreal_ratCast]
    rw [h]
    exact isFinite_realCast _
  exact hfin.mul_infinitesimal infinitesimal_wpow_neg_one

/-- A dyadic multiple of `ω⁻¹` lies below every positive dyadic. -/
theorem dyadic_mul_wpow_lt {s q : Dyadic} (hq : 0 < q) :
    (s : Surreal) * ω^ (-1 : Surreal) < (q : Surreal) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  exact (infinitesimal_dyadic_mul_wpow s).lt_ratCast hq'

/-- A dyadic multiple of `ω⁻¹` lies above every negative dyadic. -/
theorem neg_dyadic_lt_dyadic_mul_wpow {s q : Dyadic} (hq : 0 < q) :
    -(q : Surreal) < (s : Surreal) * ω^ (-1 : Surreal) := by
  have h := dyadic_mul_wpow_lt (s := -s) hq
  rw [dyadic_cast_neg', neg_mul] at h
  linarith

/-- Monotonicity of the `ω⁻¹`-grid in the coefficient. -/
theorem dyadic_mul_wpow_lt_dyadic_mul_wpow {s t : Dyadic} (hst : s < t) :
    (s : Surreal) * ω^ (-1 : Surreal) < (t : Surreal) * ω^ (-1 : Surreal) := by
  have h := dyadic_cast_lt hst
  have hw := wpow_pos (-1 : Surreal)
  exact mul_lt_mul_of_pos_right h hw

private theorem mulOption_def (x y a b : IGame) :
    mulOption x y a b = a * y + x * b - a * b :=
  rfl

private theorem mk_mulOption' (y w a b : IGame.{u}) [IGame.Numeric y] [IGame.Numeric w]
    [IGame.Numeric a] [IGame.Numeric b] :
    Surreal.mk (mulOption y w a b)
      = Surreal.mk a * Surreal.mk w + Surreal.mk y * Surreal.mk b
        - Surreal.mk a * Surreal.mk b := by
  show Surreal.mk (a * w + y * b - a * b) = _
  rw [Surreal.mk_sub, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_mul, Surreal.mk_mul]

private theorem mk_dyadic_mul_wpow_zero (q : Dyadic) :
    Surreal.mk ((q : IGame.{u}) * ω^ (0 : IGame)) = (q : Surreal) := by
  rw [Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow, Surreal.mk_zero, wpow_zero, mul_one]

/-! ### The value of the sum's product moves -/

section Core

variable {x : IGame.{u}} [IGame.Numeric x]

private theorem mk_add_mulOption_zero (x : IGame.{u}) [IGame.Numeric x] (r s : Dyadic) :
    Surreal.mk (x + mulOption (r : IGame) (ω^ (-1 : IGame)) (s : IGame) 0)
      = Surreal.mk x + (s : Surreal) * ω^ (-1 : Surreal) := by
  rw [Surreal.mk_add, mk_mulOption', Surreal.mk_dyadic, Surreal.mk_dyadic,
    mk_wpow_neg_one', Surreal.mk_zero]
  ring

private theorem mk_add_mulOption_q (x : IGame.{u}) [IGame.Numeric x] (r s q : Dyadic) :
    Surreal.mk (x + mulOption (r : IGame) (ω^ (-1 : IGame)) (s : IGame)
        ((q : IGame) * ω^ (0 : IGame)))
      = Surreal.mk x + (s : Surreal) * ω^ (-1 : Surreal)
        + ((r : Surreal) - (s : Surreal)) * (q : Surreal) := by
  rw [Surreal.mk_add, mk_mulOption', mk_dyadic_mul_wpow_zero, Surreal.mk_dyadic,
    Surreal.mk_dyadic, mk_wpow_neg_one']
  ring

/-- The anchor separation hypothesis for the left: every left option of `x` sits below
`mk x` at (at least) a rational distance. Both `Real.toIGame` and `Dyadic.toIGame`
anchors satisfy this. -/
def LeftSep (x : IGame.{u}) [IGame.Numeric x] : Prop :=
  ∀ i (hi : i ∈ xᴸ), ∃ q : Dyadic, 0 < q ∧
    @Surreal.mk i (IGame.Numeric.of_mem_moves hi) + (q : Surreal) ≤ Surreal.mk x

/-- The anchor separation hypothesis for the right. -/
def RightSep (x : IGame.{u}) [IGame.Numeric x] : Prop :=
  ∀ j (hj : j ∈ xᴿ), ∃ q : Dyadic, 0 < q ∧
    Surreal.mk x + (q : Surreal) ≤ @Surreal.mk j (IGame.Numeric.of_mem_moves hj)

/-- **The core cofinality computation** (non-integer case): the Conway sum
`x + r·ω^(−1)` is mutually cofinal with the two-sided cut whose options realize the
values `mk x + lower(r)·ω⁻¹` and `mk x + upper(r)·ω⁻¹`. All comparisons happen at the
level of surreal values; no simplicity theory enters. -/
theorem add_dyadic_mul_wpow_equiv_of_den_ne_one {r : Dyadic} (hden : r.den ≠ 1)
    {gL gU : IGame.{u}} [IGame.Numeric gL] [IGame.Numeric gU]
    (hgL : Surreal.mk gL = Surreal.mk x + (r.lower : Surreal) * ω^ (-1 : Surreal))
    (hgU : Surreal.mk gU = Surreal.mk x + (r.upper : Surreal) * ω^ (-1 : Surreal))
    (hxL : LeftSep x) (hxR : RightSep x) :
    x + (r : IGame) * ω^ (-1 : IGame) ≈ !{{gL} | {gU}} := by
  have hCL : (!{{gL} | {gU}} : IGame.{u})ᴸ = {gL} := leftMoves_ofSets ..
  have hCR : (!{{gL} | {gU}} : IGame.{u})ᴿ = {gU} := rightMoves_ofSets ..
  have hrl : (r : IGame.{u})ᴸ = {((r.lower : Dyadic) : IGame)} := by
    rw [Dyadic.toIGame_of_den_ne_one hden, leftMoves_ofSets]
  have hrr : (r : IGame.{u})ᴿ = {((r.upper : Dyadic) : IGame)} := by
    rw [Dyadic.toIGame_of_den_ne_one hden, rightMoves_ofSets]
  -- the key infinitesimal-versus-rational comparisons
  have hlow : ∀ q : Dyadic, 0 < q →
      (r : Surreal) * ω^ (-1 : Surreal) - (r.lower : Surreal) * ω^ (-1 : Surreal)
        < (q : Surreal) := by
    intro q hq
    have h := dyadic_mul_wpow_lt (s := r - r.lower) hq
    rwa [dyadic_cast_sub', sub_mul] at h
  have hupp : ∀ q : Dyadic, 0 < q →
      (r.upper : Surreal) * ω^ (-1 : Surreal) - (r : Surreal) * ω^ (-1 : Surreal)
        < (q : Surreal) := by
    intro q hq
    have h := dyadic_mul_wpow_lt (s := r.upper - r) hq
    rwa [dyadic_cast_sub', sub_mul] at h
  have hgap : ∀ q : Dyadic, 0 < q →
      (r.upper : Surreal) * ω^ (-1 : Surreal) - (r.lower : Surreal) * ω^ (-1 : Surreal)
        < ((r : Surreal) - (r.lower : Surreal)) * (q : Surreal) := by
    intro q hq
    have hql : (0 : Dyadic) < q * (r - r.lower) := by
      have h1 : (0 : Dyadic) < r - r.lower := sub_pos.2 (Dyadic.lower_lt r)
      positivity
    have h2 := dyadic_mul_wpow_lt (s := r.upper - r.lower) hql
    rw [dyadic_cast_sub', sub_mul, dyadic_cast_mul', dyadic_cast_sub'] at h2
    calc (r.upper : Surreal) * ω^ (-1 : Surreal) - (r.lower : Surreal) * ω^ (-1 : Surreal)
        < (q : Surreal) * ((r : Surreal) - (r.lower : Surreal)) := h2
      _ = ((r : Surreal) - (r.lower : Surreal)) * (q : Surreal) := by ring
  have hgapU : ∀ q : Dyadic, 0 < q →
      (r.upper : Surreal) * ω^ (-1 : Surreal) - (r.lower : Surreal) * ω^ (-1 : Surreal)
        < ((r.upper : Surreal) - (r : Surreal)) * (q : Surreal) := by
    intro q hq
    have hql : (0 : Dyadic) < q * (r.upper - r) := by
      have h1 : (0 : Dyadic) < r.upper - r := sub_pos.2 (Dyadic.lt_upper r)
      positivity
    have h2 := dyadic_mul_wpow_lt (s := r.upper - r.lower) hql
    rw [dyadic_cast_sub', sub_mul, dyadic_cast_mul', dyadic_cast_sub'] at h2
    calc (r.upper : Surreal) * ω^ (-1 : Surreal) - (r.lower : Surreal) * ω^ (-1 : Surreal)
        < (q : Surreal) * ((r.upper : Surreal) - (r : Surreal)) := h2
      _ = ((r.upper : Surreal) - (r : Surreal)) * (q : Surreal) := by ring
  apply equiv_of_exists_le
  · -- every left move of the sum is ≤ the left option gL
    rw [forall_moves_add]
    constructor
    · intro i hi
      refine ⟨gL, by rw [hCL]; exact Set.mem_singleton _, ?_⟩
      haveI := IGame.Numeric.of_mem_moves hi
      obtain ⟨q, hq, hle⟩ := hxL i hi
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_dyadic,
        mk_wpow_neg_one', hgL]
      have h1 := hlow q hq
      linarith
    · rw [forall_moves_mul]
      intro p' a ha b hb
      cases p' with
      | left =>
        rw [hrl, Set.mem_singleton_iff] at ha
        subst ha
        rw [show Player.left * Player.left = Player.left from rfl] at hb
        rw [show (ω^ (-1 : IGame.{u})).moves Player.left = (ω^ (-1 : IGame.{u}))ᴸ from rfl,
          leftMoves_wpow_neg_one', Set.mem_singleton_iff] at hb
        subst hb
        refine ⟨gL, by rw [hCL]; exact Set.mem_singleton _, ?_⟩
        rw [← Surreal.mk_le_mk, mk_add_mulOption_zero, hgL]
      | right =>
        rw [hrr, Set.mem_singleton_iff] at ha
        subst ha
        rw [show Player.right * Player.left = Player.right from rfl] at hb
        rw [show (ω^ (-1 : IGame.{u})).moves Player.right = (ω^ (-1 : IGame.{u}))ᴿ from rfl,
          rightMoves_wpow_neg_one'] at hb
        obtain ⟨q, hq, rfl⟩ := hb
        refine ⟨gL, by rw [hCL]; exact Set.mem_singleton _, ?_⟩
        rw [← Surreal.mk_le_mk, mk_add_mulOption_q, hgL]
        -- A + upper·ε + (r − upper)·q ≤ A + lower·ε
        have h2 := hgapU q hq
        have h3 : ((r : Surreal) - (r.upper : Surreal)) * (q : Surreal)
            = -(((r.upper : Surreal) - (r : Surreal)) * (q : Surreal)) := by ring
        linarith
  · -- every right move of the sum is ≥ the right option gU
    rw [forall_moves_add]
    constructor
    · intro j hj
      refine ⟨gU, by rw [hCR]; exact Set.mem_singleton _, ?_⟩
      haveI := IGame.Numeric.of_mem_moves hj
      obtain ⟨q, hq, hle⟩ := hxR j hj
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_dyadic,
        mk_wpow_neg_one', hgU]
      have h1 := hupp q hq
      linarith
    · rw [forall_moves_mul]
      intro p' a ha b hb
      cases p' with
      | left =>
        rw [hrl, Set.mem_singleton_iff] at ha
        subst ha
        rw [show Player.left * Player.right = Player.right from rfl] at hb
        rw [show (ω^ (-1 : IGame.{u})).moves Player.right = (ω^ (-1 : IGame.{u}))ᴿ from rfl,
          rightMoves_wpow_neg_one'] at hb
        obtain ⟨q, hq, rfl⟩ := hb
        refine ⟨gU, by rw [hCR]; exact Set.mem_singleton _, ?_⟩
        rw [← Surreal.mk_le_mk, mk_add_mulOption_q, hgU]
        -- A + upper·ε ≤ A + lower·ε + (r − lower)·q
        have h2 := hgap q hq
        linarith
      | right =>
        rw [hrr, Set.mem_singleton_iff] at ha
        subst ha
        rw [show Player.right * Player.right = Player.left from rfl] at hb
        rw [show (ω^ (-1 : IGame.{u})).moves Player.left = (ω^ (-1 : IGame.{u}))ᴸ from rfl,
          leftMoves_wpow_neg_one', Set.mem_singleton_iff] at hb
        subst hb
        refine ⟨gU, by rw [hCR]; exact Set.mem_singleton _, ?_⟩
        rw [← Surreal.mk_le_mk, mk_add_mulOption_zero, hgU]
  · -- the left option gL is ≤ some left move of the sum
    rw [hCL]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine ⟨x + mulOption (r : IGame) (ω^ (-1 : IGame)) ((r.lower : Dyadic) : IGame) 0,
      add_left_mem_moves_add (mulOption_mem_moves_mul (px := Player.left) (py := Player.left)
        (by rw [hrl]; exact Set.mem_singleton _)
        (by rw [show (ω^ (-1 : IGame.{u})).moves Player.left = (ω^ (-1 : IGame.{u}))ᴸ from rfl,
          leftMoves_wpow_neg_one']; exact Set.mem_singleton _)) _, ?_⟩
    rw [← Surreal.mk_le_mk, mk_add_mulOption_zero, hgL]
  · -- the right option gU is ≥ some right move of the sum
    rw [hCR]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine ⟨x + mulOption (r : IGame) (ω^ (-1 : IGame)) ((r.upper : Dyadic) : IGame) 0,
      add_left_mem_moves_add (mulOption_mem_moves_mul (px := Player.right) (py := Player.left)
        (by rw [hrr]; exact Set.mem_singleton _)
        (by rw [show (ω^ (-1 : IGame.{u})).moves Player.left = (ω^ (-1 : IGame.{u}))ᴸ from rfl,
          leftMoves_wpow_neg_one']; exact Set.mem_singleton _)) _, ?_⟩
    rw [← Surreal.mk_le_mk, mk_add_mulOption_zero, hgU]

end Core

/-! ### The core cofinality computation, positive-integer case -/

theorem dyadic_cast_natCast (n : ℕ) : ((n : Dyadic) : Surreal) = (n : Surreal) := by
  show (((n : Dyadic) : ℚ) : Surreal) = _
  rw [Dyadic.coe_natCast]
  exact_mod_cast rfl

private theorem half_pos' : (0 : Dyadic) < Dyadic.half := by
  rw [← Dyadic.coe_lt_coe]
  rw [Dyadic.coe_half]
  norm_num

private theorem half_add_half (q : Dyadic) : q * Dyadic.half + q * Dyadic.half = q := by
  ext
  push_cast [Dyadic.coe_half]
  ring

private theorem mk_add_mulOption_nat_zero (x : IGame.{u}) [IGame.Numeric x] (k : ℕ) :
    Surreal.mk (x + mulOption (((k + 1 : ℕ) : IGame)) (ω^ (-1 : IGame)) ((k : ℕ) : IGame) 0)
      = Surreal.mk x + (k : Surreal) * ω^ (-1 : Surreal) := by
  rw [Surreal.mk_add, mk_mulOption', Surreal.mk_natCast, Surreal.mk_natCast,
    mk_wpow_neg_one', Surreal.mk_zero]
  ring

private theorem mk_add_mulOption_nat_q (x : IGame.{u}) [IGame.Numeric x] (k : ℕ) (q : Dyadic) :
    Surreal.mk (x + mulOption (((k + 1 : ℕ) : IGame)) (ω^ (-1 : IGame)) ((k : ℕ) : IGame)
        ((q : IGame) * ω^ (0 : IGame)))
      = Surreal.mk x + (k : Surreal) * ω^ (-1 : Surreal) + (q : Surreal) := by
  rw [Surreal.mk_add, mk_mulOption', mk_dyadic_mul_wpow_zero, Surreal.mk_natCast,
    Surreal.mk_natCast, mk_wpow_neg_one']
  have h : ((k + 1 : ℕ) : Surreal) = (k : Surreal) + 1 := by push_cast; ring
  rw [h]
  ring

section CoreInt

variable {x : IGame.{u}} [IGame.Numeric x]

/-- **The core cofinality computation** (positive-integer case): the Conway sum
`x + (k+1)·ω^(−1)` is mutually cofinal with the cut whose left option realizes
`mk x + k·ω⁻¹` and whose right options realize the rational translates `mk x + q`. -/
theorem add_natCast_succ_mul_wpow_equiv (k : ℕ)
    {gL : IGame.{u}} [IGame.Numeric gL]
    (gR : Dyadic → IGame.{u})
    (hgRn : ∀ q : Dyadic, 0 < q → (gR q).Numeric)
    (hgL : Surreal.mk gL = Surreal.mk x + (k : Surreal) * ω^ (-1 : Surreal))
    (hgR : ∀ q (hq : 0 < q), @Surreal.mk (gR q) (hgRn q hq) = Surreal.mk x + (q : Surreal))
    (hxL : LeftSep x) (hxR : RightSep x) :
    x + ((k + 1 : ℕ) : IGame) * ω^ (-1 : IGame) ≈ !{{gL} | gR '' Set.Ioi 0} := by
  have hCL : (!{{gL} | gR '' Set.Ioi 0} : IGame.{u})ᴸ = {gL} := leftMoves_ofSets ..
  have hCR : (!{{gL} | gR '' Set.Ioi 0} : IGame.{u})ᴿ = gR '' Set.Ioi 0 := rightMoves_ofSets ..
  have hnl : (((k + 1 : ℕ) : IGame.{u}))ᴸ = {((k : ℕ) : IGame)} := leftMoves_natCast_succ k
  have hnr : (((k + 1 : ℕ) : IGame.{u}))ᴿ = ∅ := rightMoves_natCast _
  have hknn : (0 : Surreal) ≤ (k : Surreal) * ω^ (-1 : Surreal) := by
    have h1 : (0 : Surreal) ≤ (k : Surreal) := by exact_mod_cast Nat.zero_le k
    exact mul_nonneg h1 (wpow_pos _).le
  have hkq : ∀ q : Dyadic, 0 < q →
      (k : Surreal) * ω^ (-1 : Surreal) < (q : Surreal) := by
    intro q hq
    have h := dyadic_mul_wpow_lt (s := (k : Dyadic)) hq
    rwa [dyadic_cast_natCast] at h
  apply equiv_of_exists_le
  · rw [forall_moves_add]
    constructor
    · intro i hi
      refine ⟨gL, by rw [hCL]; exact Set.mem_singleton _, ?_⟩
      haveI := IGame.Numeric.of_mem_moves hi
      obtain ⟨q, hq, hle⟩ := hxL i hi
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_natCast,
        mk_wpow_neg_one', hgL]
      have h1 := wpow_neg_one_lt_dyadic hq
      have h2 : ((k + 1 : ℕ) : Surreal) = (k : Surreal) + 1 := by push_cast; ring
      rw [h2]
      nlinarith [wpow_pos (-1 : Surreal)]
    · rw [forall_moves_mul]
      intro p' a ha b hb
      cases p' with
      | left =>
        rw [hnl, Set.mem_singleton_iff] at ha
        subst ha
        rw [show Player.left * Player.left = Player.left from rfl] at hb
        rw [show (ω^ (-1 : IGame.{u})).moves Player.left = (ω^ (-1 : IGame.{u}))ᴸ from rfl,
          leftMoves_wpow_neg_one', Set.mem_singleton_iff] at hb
        subst hb
        refine ⟨gL, by rw [hCL]; exact Set.mem_singleton _, ?_⟩
        rw [← Surreal.mk_le_mk, mk_add_mulOption_nat_zero, hgL]
      | right =>
        rw [hnr] at ha
        exact absurd ha (Set.notMem_empty a)
  · rw [forall_moves_add]
    constructor
    · intro j hj
      haveI := IGame.Numeric.of_mem_moves hj
      obtain ⟨q, hq, hle⟩ := hxR j hj
      haveI := hgRn q hq
      refine ⟨gR q, by rw [hCR]; exact Set.mem_image_of_mem _ hq, ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_natCast,
        mk_wpow_neg_one', hgR q hq]
      have h2 : ((k + 1 : ℕ) : Surreal) = (k : Surreal) + 1 := by push_cast; ring
      rw [h2]
      nlinarith [wpow_pos (-1 : Surreal), hknn]
    · rw [forall_moves_mul]
      intro p' a ha b hb
      cases p' with
      | left =>
        rw [hnl, Set.mem_singleton_iff] at ha
        subst ha
        rw [show Player.left * Player.right = Player.right from rfl] at hb
        rw [show (ω^ (-1 : IGame.{u})).moves Player.right = (ω^ (-1 : IGame.{u}))ᴿ from rfl,
          rightMoves_wpow_neg_one'] at hb
        obtain ⟨q, hq, rfl⟩ := hb
        haveI := hgRn q hq
        refine ⟨gR q, by rw [hCR]; exact Set.mem_image_of_mem _ hq, ?_⟩
        rw [← Surreal.mk_le_mk, mk_add_mulOption_nat_q, hgR q hq]
        linarith [hknn]
      | right =>
        rw [hnr] at ha
        exact absurd ha (Set.notMem_empty a)
  · rw [hCL]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine ⟨x + mulOption (((k + 1 : ℕ) : IGame)) (ω^ (-1 : IGame)) ((k : ℕ) : IGame) 0,
      add_left_mem_moves_add (mulOption_mem_moves_mul (px := Player.left) (py := Player.left)
        (by rw [hnl]; exact Set.mem_singleton _)
        (by rw [show (ω^ (-1 : IGame.{u})).moves Player.left = (ω^ (-1 : IGame.{u}))ᴸ from rfl,
          leftMoves_wpow_neg_one']; exact Set.mem_singleton _)) _, ?_⟩
    rw [← Surreal.mk_le_mk, mk_add_mulOption_nat_zero, hgL]
  · rw [hCR]
    intro b hb
    obtain ⟨q, hq, rfl⟩ := hb
    haveI := hgRn q hq
    have hqh : (0 : Dyadic) < q * Dyadic.half := mul_pos hq half_pos'
    refine ⟨x + mulOption (((k + 1 : ℕ) : IGame)) (ω^ (-1 : IGame)) ((k : ℕ) : IGame)
        (((q * Dyadic.half : Dyadic) : IGame) * ω^ (0 : IGame)),
      add_left_mem_moves_add (mulOption_mem_moves_mul (px := Player.left) (py := Player.right)
        (by rw [hnl]; exact Set.mem_singleton _)
        (by rw [show (ω^ (-1 : IGame.{u})).moves Player.right = (ω^ (-1 : IGame.{u}))ᴿ from rfl,
          rightMoves_wpow_neg_one']; exact Set.mem_image_of_mem _ hqh)) _, ?_⟩
    rw [← Surreal.mk_le_mk, mk_add_mulOption_nat_q, hgR q hq]
    -- A + k·ε + q/2 ≤ A + q
    have h1 := hkq (q * Dyadic.half) hqh
    have h2 : ((q * Dyadic.half : Dyadic) : Surreal) + ((q * Dyadic.half : Dyadic) : Surreal)
        = (q : Surreal) := by
      rw [← dyadic_cast_add', half_add_half]
    linarith

end CoreInt

/-! ### The anchors: separation for real and dyadic cast games -/

/-- Below any positive real there is a positive dyadic. -/
private theorem exists_dyadic_pos_lt {x : ℝ} (hx : 0 < x) :
    ∃ q : Dyadic, 0 < q ∧ ((q : ℚ) : ℝ) < x := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨Dyadic.half ^ n, pow_pos half_pos' n, ?_⟩
  have hcast : (((Dyadic.half ^ n : Dyadic) : ℚ) : ℝ) = (1 / 2 : ℝ) ^ n := by
    push_cast [Dyadic.coe_half]
    norm_num
  rw [hcast]
  exact hn

theorem leftSep_realCast (a : ℝ) : LeftSep (Real.toIGame.{u} a) := by
  intro i hi
  rw [Real.leftMoves_toIGame] at hi
  obtain ⟨d, hd, rfl⟩ := hi
  rw [Set.mem_ofPred_eq] at hd
  obtain ⟨q, hq, hqlt⟩ := exists_dyadic_pos_lt (sub_pos.2 hd)
  refine ⟨q, hq, ?_⟩
  have hkey : ((d : ℚ) : ℝ) + ((q : ℚ) : ℝ) ≤ a := by linarith
  have hcast := Real.toSurreal_le_iff.2 hkey
  rw [Real.toSurreal_add, Real.toSurreal_ratCast, Real.toSurreal_ratCast] at hcast
  show @Surreal.mk _ _ + _ ≤ Surreal.mk (Real.toIGame a)
  rw [Surreal.mk_dyadic]
  exact hcast

theorem rightSep_realCast (a : ℝ) : RightSep (Real.toIGame.{u} a) := by
  intro j hj
  rw [Real.rightMoves_toIGame] at hj
  obtain ⟨d, hd, rfl⟩ := hj
  rw [Set.mem_ofPred_eq] at hd
  obtain ⟨q, hq, hqlt⟩ := exists_dyadic_pos_lt (sub_pos.2 hd)
  refine ⟨q, hq, ?_⟩
  have hkey : a + ((q : ℚ) : ℝ) ≤ ((d : ℚ) : ℝ) := by linarith
  have hcast := Real.toSurreal_le_iff.2 hkey
  rw [Real.toSurreal_add, Real.toSurreal_ratCast, Real.toSurreal_ratCast] at hcast
  show Surreal.mk (Real.toIGame a) + _ ≤ @Surreal.mk _ _
  rw [Surreal.mk_dyadic]
  exact hcast

theorem leftSep_dyadic (d : Dyadic) : LeftSep ((d : Dyadic) : IGame.{u}) := by
  intro i hi
  have hil := Dyadic.eq_lower_of_mem_leftMoves_toIGame hi
  subst hil
  refine ⟨d - d.lower, sub_pos.2 (Dyadic.lower_lt d), ?_⟩
  show @Surreal.mk _ _ + _ ≤ Surreal.mk (d : IGame)
  rw [Surreal.mk_dyadic, Surreal.mk_dyadic, ← dyadic_cast_add']
  have h : d.lower + (d - d.lower) = d := by ring
  rw [h]

theorem rightSep_dyadic (d : Dyadic) : RightSep ((d : Dyadic) : IGame.{u}) := by
  intro j hj
  have hju := Dyadic.eq_upper_of_mem_rightMoves_toIGame hj
  subst hju
  refine ⟨d.upper - d, sub_pos.2 (Dyadic.lt_upper d), ?_⟩
  show Surreal.mk (d : IGame) + _ ≤ @Surreal.mk _ _
  rw [Surreal.mk_dyadic, Surreal.mk_dyadic, ← dyadic_cast_add']
  have h : d + (d.upper - d) = d.upper := by ring
  rw [h]

/-- The canonical real game is born by day `ω`, at the level of `IGame` birthdays. -/
theorem birthday_toIGame_realCast_le (x : ℝ) :
    (Real.toIGame.{u} x).birthday ≤ NatOrdinal.of Ordinal.omega0 := by
  rw [Real.toIGame, IGame.birthday_ofSets]
  refine max_le ?_ ?_ <;>
  · refine csSup_le' ?_
    rintro o ⟨z, ⟨q, hq, rfl⟩, rfl⟩
    refine Order.succ_le_of_lt ?_
    exact IGame.short_iff_birthday_finite.1 (IGame.Short.dyadic q)

/-! ### The birthday induction along the dyadic grid -/

theorem dyadic_cast_zero : ((0 : Dyadic) : Surreal) = 0 := by
  show (((0 : Dyadic) : ℚ) : Surreal) = 0
  norm_num

private theorem lower_nonneg_of_pos {r : Dyadic} (hr : 0 < r) : 0 ≤ r.lower := by
  have hnum : 0 < r.num := by
    have h : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr
    exact Rat.num_pos.2 h
  have hd : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.den_pos
  rw [← Dyadic.coe_le_coe]
  show (0 : ℚ) ≤ ((r.lower : Dyadic) : ℚ)
  rw [Dyadic.coe_lower]
  have hr' : (r : ℚ) = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den _).symm
  have key : (r : ℚ) - ((r.den : ℚ))⁻¹ = ((r.num : ℚ) - 1) / (r.den : ℚ) := by
    rw [hr']
    field_simp
  rw [key]
  refine div_nonneg ?_ hd.le
  have h1 : (1 : ℚ) ≤ (r.num : ℚ) := by exact_mod_cast hnum
  linarith

private theorem nat_cast_mono {i j : ℕ} (h : i ≤ j) :
    ((i : ℕ) : NatOrdinal) ≤ ((j : ℕ) : NatOrdinal) := by
  exact_mod_cast h

private theorem omega_add_nat_succ (i : ℕ) :
    (NatOrdinal.of Ordinal.omega0 + (i : NatOrdinal)) + 1
      = NatOrdinal.of Ordinal.omega0 + ((i + 1 : ℕ) : NatOrdinal) := by
  rw [add_assoc]
  congr 1
  exact_mod_cast rfl

section Wrap

variable {x : IGame.{u}} [IGame.Numeric x]

/-- **The parametric grid bound.** Given an anchor game `x` whose rational translates are
all realizable with birthday bound `ω + c₀` (exclusive), each positive grid point
`mk x + r·ω⁻¹` is born by day `ω + (hgt r − 1) + c₀`. The induction unwinds the dyadic
birth tree: integers step down by one, non-integers step to their parents, and each step
costs exactly one day via a two-sided cut pinned by the core cofinality computations. -/
private theorem grid_aux (hxL : LeftSep x) (hxR : RightSep x) (c₀ : ℕ)
    (hgames : ∀ q : Dyadic, 0 ≤ q → ∃ (g : IGame.{u}) (_ : g.Numeric),
      Surreal.mk g = Surreal.mk x + (q : Surreal) ∧
        g.birthday + 1 ≤ NatOrdinal.of Ordinal.omega0 + (c₀ : NatOrdinal)) :
    ∀ n : ℕ, ∀ r : Dyadic, 0 < r → Dyadic.hgt r ≤ n →
      (Surreal.mk x + (r : Surreal) * ω^ (-1 : Surreal)).birthday
        ≤ NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt r - 1 + c₀ : ℕ) : NatOrdinal) := by
  intro n
  induction n with
  | zero =>
    intro r hr hrn
    have := Dyadic.hgt_pos_of_ne_zero hr.ne'
    omega
  | succ n ih =>
    intro r hr hrn
    -- a realization of `mk x + s·ω⁻¹` for any nonnegative `s` simpler than `r`
    have hrealize : ∀ s : Dyadic, 0 ≤ s → Dyadic.hgt s + 1 ≤ Dyadic.hgt r →
        ∃ (g : IGame.{u}) (_ : g.Numeric),
          Surreal.mk g = Surreal.mk x + (s : Surreal) * ω^ (-1 : Surreal) ∧
            g.birthday + 1
              ≤ NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt r - 1 + c₀ : ℕ) : NatOrdinal) := by
      intro s hs hsr
      rcases eq_or_lt_of_le hs with h0 | hpos
      · obtain ⟨g, hgn, hgv, hgb⟩ := hgames 0 le_rfl
        refine ⟨g, hgn, ?_, ?_⟩
        · rw [hgv, ← h0, dyadic_cast_zero, zero_mul, add_zero]
        · refine hgb.trans (add_le_add le_rfl (nat_cast_mono ?_))
          omega
      · have hb := ih s hpos (by omega)
        obtain ⟨g, hgn, hgv, hgb⟩ := birthday_eq_iGameBirthday
          (Surreal.mk x + (s : Surreal) * ω^ (-1 : Surreal))
        refine ⟨g, hgn, hgv, ?_⟩
        rw [hgb]
        have h1 : (Surreal.mk x + (s : Surreal) * ω^ (-1 : Surreal)).birthday + 1
            ≤ (NatOrdinal.of Ordinal.omega0
                + ((Dyadic.hgt s - 1 + c₀ : ℕ) : NatOrdinal)) + 1 :=
          add_le_add hb (le_refl 1)
        refine h1.trans ?_
        rw [omega_add_nat_succ]
        refine add_le_add le_rfl (nat_cast_mono ?_)
        have := Dyadic.hgt_pos_of_ne_zero hpos.ne'
        omega
    by_cases hden : r.den = 1
    · -- the integer case: `r = k + 1`
      have hnum : 0 < r.num := by
        have h : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr
        exact Rat.num_pos.2 h
      obtain ⟨k, hk⟩ : ∃ k : ℕ, r.num = ((k + 1 : ℕ) : ℤ) :=
        ⟨r.num.toNat - 1, by omega⟩
      have hreq : r = ((k + 1 : ℕ) : Dyadic) := by
        rw [Dyadic.eq_intCast_of_den_eq_one hden, hk]
        push_cast
        rfl
      subst hreq
      -- realizations for the cut options
      obtain ⟨gL, hgLn, hgLv, hgLb⟩ := hrealize ((k : ℕ) : Dyadic)
        (by exact_mod_cast Nat.zero_le k)
        (by rw [Dyadic.hgt_natCast, Dyadic.hgt_natCast])
      choose gR hgRn hgRv hgRb using fun q : Dyadic ↦ hgames q
      let gR' : Dyadic → IGame.{u} := fun q ↦ if h : 0 ≤ q then gR q h else 0
      have hgR'n : ∀ q : Dyadic, 0 < q → (gR' q).Numeric := by
        intro q hq
        show (if h : 0 ≤ q then gR q h else 0).Numeric
        rw [dif_pos hq.le]
        exact hgRn q hq.le
      have hgR'v : ∀ q (hq : 0 < q), @Surreal.mk (gR' q) (hgR'n q hq)
          = Surreal.mk x + (q : Surreal) := by
        intro q hq
        have h : gR' q = gR q hq.le := dif_pos hq.le
        rw [show @Surreal.mk (gR' q) (hgR'n q hq)
          = @Surreal.mk (gR q hq.le) (hgRn q hq.le) from by congr 1]
        exact hgRv q hq.le
      haveI := hgLn
      have hgLv' : Surreal.mk gL = Surreal.mk x + ((k : ℕ) : Surreal) * ω^ (-1 : Surreal) := by
        rw [hgLv, dyadic_cast_natCast]
      have hequiv := add_natCast_succ_mul_wpow_equiv (x := x) k (gR := gR') hgR'n hgLv'
        hgR'v hxL hxR
      -- the cut is numeric
      have hCn : IGame.Numeric (!{{gL} | gR' '' Set.Ioi 0} : IGame.{u}) := by
        refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
        · rw [leftMoves_ofSets, Set.mem_singleton_iff] at hy
          rw [rightMoves_ofSets] at hz
          obtain ⟨q, hq, rfl⟩ := hz
          subst hy
          haveI := hgR'n q hq
          rw [← Surreal.mk_lt_mk, hgLv', hgR'v q hq]
          have h1 : ((k : ℕ) : Surreal) * ω^ (-1 : Surreal) < (q : Surreal) := by
            have h := dyadic_mul_wpow_lt (s := (k : Dyadic)) hq
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
            exact hgR'n q hq
      -- value and birthday
      have hmkgame : Surreal.mk (x + (((k + 1 : ℕ) : IGame.{u})) * ω^ (-1 : IGame))
          = Surreal.mk x + (((k + 1 : ℕ) : Dyadic) : Surreal) * ω^ (-1 : Surreal) := by
        rw [Surreal.mk_add, Surreal.mk_mul, Surreal.mk_natCast, mk_wpow_neg_one',
          dyadic_cast_natCast]
      have hval : Surreal.mk x + (((k + 1 : ℕ) : Dyadic) : Surreal) * ω^ (-1 : Surreal)
          = @Surreal.mk _ hCn := by
        haveI := hCn
        rw [← hmkgame]
        exact Surreal.mk_eq hequiv
      refine le_of_eq_of_le (congrArg birthday hval) ?_
      refine (birthday_mk_le _).trans ?_
      rw [IGame.birthday_ofSets]
      refine max_le ?_ ?_
      · refine csSup_le' ?_
        rintro o ⟨g, hg, rfl⟩
        rw [Set.mem_singleton_iff] at hg
        subst hg
        rw [Function.comp_apply, Order.succ_eq_add_one]
        refine hgLb.trans (add_le_add le_rfl (nat_cast_mono ?_))
        rw [Dyadic.hgt_natCast]
      · refine csSup_le' ?_
        rintro o ⟨g, ⟨q, hq, rfl⟩, rfl⟩
        rw [Function.comp_apply, Order.succ_eq_add_one]
        have h : gR' q = gR q hq.le := dif_pos hq.le
        rw [show (gR' q).birthday = (gR q hq.le).birthday from by rw [h]]
        refine (hgRb q hq.le).trans (add_le_add le_rfl (nat_cast_mono ?_))
        omega
    · -- the non-integer case: recurse to the parents
      have hlow0 : 0 ≤ r.lower := lower_nonneg_of_pos hr
      have hup0 : 0 ≤ r.upper := (hlow0.trans (Dyadic.lower_lt r).le).trans (Dyadic.lt_upper r).le
      have hgtl := Dyadic.hgt_lower_lt hden
      have hgtu := Dyadic.hgt_upper_lt hden
      obtain ⟨gL, hgLn, hgLv, hgLb⟩ := hrealize r.lower hlow0 (by omega)
      obtain ⟨gU, hgUn, hgUv, hgUb⟩ := hrealize r.upper hup0 (by omega)
      haveI := hgLn
      haveI := hgUn
      have hequiv := add_dyadic_mul_wpow_equiv_of_den_ne_one (x := x) hden hgLv hgUv hxL hxR
      have hCn : IGame.Numeric (!{{gL} | {gU}} : IGame.{u}) := by
        refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
        · rw [leftMoves_ofSets, Set.mem_singleton_iff] at hy
          rw [rightMoves_ofSets, Set.mem_singleton_iff] at hz
          subst hy
          subst hz
          rw [← Surreal.mk_lt_mk, hgLv, hgUv]
          have h1 := dyadic_mul_wpow_lt_dyadic_mul_wpow (Dyadic.lower_lt_upper r)
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
      have hmkgame : Surreal.mk (x + (r : IGame.{u}) * ω^ (-1 : IGame))
          = Surreal.mk x + (r : Surreal) * ω^ (-1 : Surreal) := by
        rw [Surreal.mk_add, Surreal.mk_mul, Surreal.mk_dyadic, mk_wpow_neg_one']
      have hval : Surreal.mk x + (r : Surreal) * ω^ (-1 : Surreal) = @Surreal.mk _ hCn := by
        haveI := hCn
        rw [← hmkgame]
        exact Surreal.mk_eq hequiv
      refine le_of_eq_of_le (congrArg birthday hval) ?_
      refine (birthday_mk_le _).trans ?_
      rw [IGame.birthday_ofSets]
      refine max_le ?_ ?_
      · refine csSup_le' ?_
        rintro o ⟨g, hg, rfl⟩
        rw [Set.mem_singleton_iff] at hg
        subst hg
        rw [Function.comp_apply, Order.succ_eq_add_one]
        exact hgLb
      · refine csSup_le' ?_
        rintro o ⟨g, hg, rfl⟩
        rw [Set.mem_singleton_iff] at hg
        subst hg
        rw [Function.comp_apply, Order.succ_eq_add_one]
        exact hgUb

end Wrap

/-! ### The public grid bounds -/

/-- **The halo grid over a real anchor**: `a + r·ω⁻¹` is born by day `ω + hgt r`, for
every real `a` and every dyadic `r`. -/
theorem birthday_realCast_add_dyadic_mul_wpow_le (a : ℝ) (r : Dyadic) :
    ((a : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)).birthday
      ≤ NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt r : ℕ) : NatOrdinal) := by
  have hgames : ∀ b : ℝ, ∀ q : Dyadic, 0 ≤ q → ∃ (g : IGame) (_ : g.Numeric),
      Surreal.mk g = Surreal.mk (Real.toIGame b) + (q : Surreal) ∧
        g.birthday + 1 ≤ NatOrdinal.of Ordinal.omega0 + ((1 : ℕ) : NatOrdinal) := by
    intro b q _
    refine ⟨Real.toIGame (b + ((q : ℚ) : ℝ)), inferInstance, ?_, ?_⟩
    · rw [Surreal.mk_real_toIGame, Surreal.mk_real_toIGame, Real.toSurreal_add,
        Real.toSurreal_ratCast]
    · have h := birthday_toIGame_realCast_le (b + ((q : ℚ) : ℝ))
      have h1 : ((1 : ℕ) : NatOrdinal) = 1 := by exact_mod_cast rfl
      rw [h1]
      exact add_le_add h (le_refl 1)
  have main : ∀ b : ℝ, ∀ s : Dyadic, 0 < s →
      ((b : Surreal) + (s : Surreal) * ω^ (-1 : Surreal)).birthday
        ≤ NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt s : ℕ) : NatOrdinal) := by
    intro b s hs
    have h := grid_aux (x := Real.toIGame b) (leftSep_realCast b) (rightSep_realCast b) 1
      (hgames b) (Dyadic.hgt s) s hs le_rfl
    rw [Surreal.mk_real_toIGame] at h
    refine h.trans (add_le_add le_rfl (nat_cast_mono ?_))
    have := Dyadic.hgt_pos_of_ne_zero hs.ne'
    omega
  rcases lt_trichotomy r 0 with hr | hr | hr
  · -- negative coefficients by symmetry
    have h := main (-a) (-r) (by rwa [neg_pos])
    have hval : ((-a : ℝ) : Surreal) + ((-r : Dyadic) : Surreal) * ω^ (-1 : Surreal)
        = -((a : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)) := by
      rw [dyadic_cast_neg']
      have hna : ((-a : ℝ) : Surreal) = -(a : Surreal) := by
        exact_mod_cast Real.toSurreal_neg a
      rw [hna]
      ring
    rw [hval, birthday_neg, Dyadic.hgt_neg] at h
    exact h
  · subst hr
    rw [dyadic_cast_zero, zero_mul, add_zero, Dyadic.hgt_zero]
    have h := birthday_realCast_le a
    refine h.trans ?_
    have h0 : ((0 : ℕ) : NatOrdinal) = 0 := by exact_mod_cast rfl
    rw [h0, add_zero]
  · exact main a r hr

/-- **The halo grid over a dyadic anchor**: `d + r·ω⁻¹` is born by day `ω + (hgt r − 1)`
for every dyadic `d` and nonzero dyadic `r` — one day sharper than over a general real
anchor. For `r = ±1` this is the day-`ω` bound for the census neighbours `d ± ω⁻¹`. -/
theorem birthday_dyadic_add_dyadic_mul_wpow_le (d : Dyadic) {r : Dyadic} (hr : r ≠ 0) :
    ((d : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)).birthday
      ≤ NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt r - 1 : ℕ) : NatOrdinal) := by
  have hgames : ∀ e : Dyadic, ∀ q : Dyadic, 0 ≤ q → ∃ (g : IGame) (_ : g.Numeric),
      Surreal.mk g = Surreal.mk (e : IGame) + (q : Surreal) ∧
        g.birthday + 1 ≤ NatOrdinal.of Ordinal.omega0 + ((0 : ℕ) : NatOrdinal) := by
    intro e q _
    refine ⟨((e + q : Dyadic) : IGame), inferInstance, ?_, ?_⟩
    · rw [Surreal.mk_dyadic, Surreal.mk_dyadic, dyadic_cast_add']
    · have h : ((e + q : Dyadic) : IGame).birthday < NatOrdinal.of Ordinal.omega0 :=
        IGame.short_iff_birthday_finite.1 (IGame.Short.dyadic _)
      have h0 : ((0 : ℕ) : NatOrdinal) = 0 := by exact_mod_cast rfl
      rw [h0, add_zero, ← Order.succ_eq_add_one]
      exact Order.succ_le_of_lt h
  have main : ∀ e : Dyadic, ∀ s : Dyadic, 0 < s →
      ((e : Surreal) + (s : Surreal) * ω^ (-1 : Surreal)).birthday
        ≤ NatOrdinal.of Ordinal.omega0 + ((Dyadic.hgt s - 1 : ℕ) : NatOrdinal) := by
    intro e s hs
    have h := grid_aux (x := (e : IGame)) (leftSep_dyadic e) (rightSep_dyadic e) 0
      (hgames e) (Dyadic.hgt s) s hs le_rfl
    rw [Surreal.mk_dyadic] at h
    refine h.trans (add_le_add le_rfl (nat_cast_mono (by omega)))
  rcases lt_trichotomy r 0 with hrn | hrn | hrn
  · have h := main (-d) (-r) (by rwa [neg_pos])
    have hval : ((-d : Dyadic) : Surreal) + ((-r : Dyadic) : Surreal) * ω^ (-1 : Surreal)
        = -((d : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)) := by
      rw [dyadic_cast_neg', dyadic_cast_neg']
      ring
    rw [hval, birthday_neg, Dyadic.hgt_neg] at h
    exact h
  · exact absurd hrn hr
  · exact main d r hrn

end Surreal

end
