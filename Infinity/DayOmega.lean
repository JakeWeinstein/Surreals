import Infinity.Identification
import Infinity.ExpFin

/-!
# The day-`ω` census, finite branch: birthdays of `d ± ω⁻¹`

`Infinity.Identification` classified the *infinite* surreals born by day `ω`: only `±ω`.
This file begins the classification of the *finite* ones — Conway's day-`ω` census
(ONAG, ch. 2: the numbers born on day `ω` are the non-dyadic reals, `±ω`, and the
neighbours `d ± 1/ω` of the dyadics) — by constructing the exceptional elements and
computing their birthdays:

* `dyadicPlusInv d` — the two-sided cut `!{d | d + q}` (over positive dyadic `q`) as an
  explicit game with dyadic options;
* `dyadic_add_wpow_neg_one_eq` — its value **is** `d + ω⁻¹`: Conway addition of the
  canonical dyadic game and CG's genetic `ω`-power game `ω^(−1)` is mutually cofinal
  with the two-sided cut (a pure order computation, no simplicity);
* `birthday_dyadic_add_wpow_neg_one_le` / `birthday_dyadic_sub_wpow_neg_one_le` :
  **`d ± ω⁻¹` is born by day `ω`** — the first birthday bounds in this development for
  surreals that are neither dyadic, real, ordinal, nor `ω`-power shaped;
* `birthday_wpow_neg_one` : **`birthday (ω⁻¹) = ω`** exactly (the case `d = 0`,
  with the lower bound from the infinitesimal-halo bound of `Infinity.BirthdayHahn`).

These are the missing "upper bound" ingredients for the finite day-`ω` classification
(`Infinity.DayOmegaClass`): a surreal born by day `ω` that is infinitesimally close to a
dyadic `d` but distinct from it can only be `d ± ω⁻¹`, because those two are born by day
`ω` and simplest-fit uniqueness (`Cut.eq_of_fits_of_birthday_le`) leaves no room for
anything else.
-/

open ArchimedeanClass Filter Finset IGame Set

universe u

noncomputable section

namespace Surreal

/-! ### Order helpers for `ω⁻¹` -/

theorem infinitesimal_wpow_neg_one : Infinitesimal (ω^ (-1 : Surreal)) := by
  rw [show (-1 : Surreal) = -(1 : Surreal) from rfl, wpow_neg]
  exact infinitesimal_inv_wpow one_pos

theorem wpow_neg_one_lt_dyadic {q : Dyadic} (hq : 0 < q) :
    ω^ (-1 : Surreal) < (q : Surreal) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  exact infinitesimal_wpow_neg_one.lt_ratCast hq'

private theorem dyadic_cast_sub (a b : Dyadic) :
    ((a - b : Dyadic) : Surreal) = (a : Surreal) - (b : Surreal) := by
  show (((a - b : Dyadic) : ℚ) : Surreal) = (((a : Dyadic) : ℚ) : Surreal) - (((b : Dyadic) : ℚ) : Surreal)
  have h : ((a - b : Dyadic) : ℚ) = (a : ℚ) - (b : ℚ) := by push_cast; ring
  rw [h, Rat.cast_sub]

private theorem dyadic_cast_add (a b : Dyadic) :
    ((a + b : Dyadic) : Surreal) = (a : Surreal) + (b : Surreal) := by
  show (((a + b : Dyadic) : ℚ) : Surreal) = (((a : Dyadic) : ℚ) : Surreal) + (((b : Dyadic) : ℚ) : Surreal)
  have h : ((a + b : Dyadic) : ℚ) = (a : ℚ) + (b : ℚ) := by push_cast; ring
  rw [h, Rat.cast_add]

private theorem dyadic_cast_neg (a : Dyadic) :
    ((-a : Dyadic) : Surreal) = -(a : Surreal) := by
  show (((-a : Dyadic) : ℚ) : Surreal) = -(((a : Dyadic) : ℚ) : Surreal)
  have h : ((-a : Dyadic) : ℚ) = -(a : ℚ) := by push_cast; ring
  rw [h, Rat.cast_neg]

/-! ### The two-sided cut `!{d | d + q}` as an explicit game -/

/-- The game `!{d | d + q : 0 < q dyadic}` — the canonical representation of `d + ω⁻¹`
by dyadic options. -/
private def dyadicPlusInv (d : Dyadic) : IGame.{u} :=
  !{{(d : IGame)} | (fun q : Dyadic ↦ ((d + q : Dyadic) : IGame)) '' Set.Ioi 0}

private theorem numeric_dyadicPlusInv (d : Dyadic) : Numeric (dyadicPlusInv d) := by
  rw [dyadicPlusInv]
  refine Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
  · rw [leftMoves_ofSets] at hy
    rw [rightMoves_ofSets] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Dyadic.toIGame_lt_toIGame.2 (lt_add_of_pos_right d hq)
  · cases p with
    | left =>
      rw [moves_ofSets] at hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      infer_instance
    | right =>
      rw [moves_ofSets] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      infer_instance

/-- The moves of the game `ω^ (-1)`. -/
private theorem leftMoves_wpow_neg_one : (ω^ (-1 : IGame))ᴸ = {0} := by
  have h1 : (-1 : IGame)ᴸ = ∅ := by
    rw [show (-1 : IGame) = -(1 : IGame) from rfl]
    simp
  rw [leftMoves_wpow, h1]
  simp

private theorem rightMoves_wpow_neg_one : (ω^ (-1 : IGame))ᴿ =
    (fun r : Dyadic ↦ (r : IGame) * ω^ (0 : IGame)) '' Set.Ioi 0 := by
  have h1 : (-1 : IGame)ᴿ = {0} := by
    rw [show (-1 : IGame) = -(1 : IGame) from rfl]
    simp
  rw [rightMoves_wpow, h1, Set.image2_singleton_right]

private theorem mk_wpow_neg_one : mk (ω^ (-1 : IGame)) = ω^ (-1 : Surreal) := by
  rw [Surreal.mk_wpow]
  norm_num

/-- **Conway addition meets the two-sided cut**: the game sum `d + ω^(−1)` is mutually
cofinal with the cut `!{d | d + q}`. -/
private theorem add_wpow_neg_one_equiv (d : Dyadic) :
    (d : IGame) + ω^ (-1 : IGame) ≈ dyadicPlusInv d := by
  haveI := numeric_dyadicPlusInv d
  have hRHSL : (dyadicPlusInv d)ᴸ = {(d : IGame)} := by
    rw [dyadicPlusInv, leftMoves_ofSets]
  have hRHSR : (dyadicPlusInv d)ᴿ = (fun q : Dyadic ↦ ((d + q : Dyadic) : IGame)) '' Set.Ioi 0 := by
    rw [dyadicPlusInv, rightMoves_ofSets]
  apply equiv_of_exists_le
  · -- every left move of the sum is below the left option `d`
    rw [forall_moves_add]
    constructor
    · intro a ha
      have hal := Dyadic.eq_lower_of_mem_leftMoves_toIGame ha
      subst hal
      refine ⟨(d : IGame), by rw [hRHSL]; exact Set.mem_singleton _, ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_dyadic, Surreal.mk_dyadic,
        mk_wpow_neg_one]
      have hgap : (0 : Dyadic) < d - d.lower := sub_pos.2 (Dyadic.lower_lt d)
      have h2 := wpow_neg_one_lt_dyadic hgap
      rw [dyadic_cast_sub] at h2
      linarith
    · intro b hb
      rw [leftMoves_wpow_neg_one, Set.mem_singleton_iff] at hb
      subst hb
      refine ⟨(d : IGame), by rw [hRHSL]; exact Set.mem_singleton _, ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_dyadic, Surreal.mk_zero]
      simp
  · -- every right move of the sum is above some right option `d + q`
    rw [forall_moves_add]
    constructor
    · intro a ha
      have hau := Dyadic.eq_upper_of_mem_rightMoves_toIGame ha
      subst hau
      have hq : (0 : Dyadic) < d.upper - d := sub_pos.2 (Dyadic.lt_upper d)
      refine ⟨((d + (d.upper - d) : Dyadic) : IGame),
        by rw [hRHSR]; exact Set.mem_image_of_mem _ hq, ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_dyadic, Surreal.mk_dyadic,
        mk_wpow_neg_one, dyadic_cast_add, dyadic_cast_sub]
      have h2 := (wpow_pos (-1 : Surreal)).le
      linarith
    · intro b hb
      rw [rightMoves_wpow_neg_one] at hb
      obtain ⟨r, hr, rfl⟩ := hb
      refine ⟨((d + r : Dyadic) : IGame),
        by rw [hRHSR]; exact Set.mem_image_of_mem _ hr, ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_dyadic, Surreal.mk_dyadic,
        Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow, Surreal.mk_zero,
        dyadic_cast_add, wpow_zero, mul_one]
  · -- the left option `d` is below the sum's left move `d + 0`
    rw [hRHSL]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine ⟨(d : IGame) + 0, add_left_mem_moves_add (by rw [leftMoves_wpow_neg_one]; rfl) _, ?_⟩
    rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_zero]
    simp
  · -- each right option `d + q` is above the sum's right move `d + q·ω⁰`
    rw [hRHSR]
    intro b hb
    obtain ⟨q, hq, rfl⟩ := hb
    refine ⟨(d : IGame) + ((q : IGame) * ω^ (0 : IGame)),
      add_left_mem_moves_add (by rw [rightMoves_wpow_neg_one]; exact Set.mem_image_of_mem _ hq) _, ?_⟩
    rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_dyadic, Surreal.mk_mul,
      Surreal.mk_dyadic, Surreal.mk_wpow, Surreal.mk_zero, Surreal.mk_dyadic,
      dyadic_cast_add, wpow_zero, mul_one]

/-- The value of the two-sided cut `!{d | d + q}` is `d + ω⁻¹`. -/
theorem dyadic_add_wpow_neg_one_eq (d : Dyadic) :
    (d : Surreal) + ω^ (-1 : Surreal) =
      @Surreal.mk (dyadicPlusInv d) (numeric_dyadicPlusInv d) := by
  haveI := numeric_dyadicPlusInv d
  rw [← Surreal.mk_dyadic d, ← mk_wpow_neg_one, ← Surreal.mk_add]
  exact Surreal.mk_eq (add_wpow_neg_one_equiv d)

/-- **`d + ω⁻¹` is born by day `ω`** for every dyadic `d`. -/
theorem birthday_dyadic_add_wpow_neg_one_le (d : Dyadic) :
    ((d : Surreal) + ω^ (-1 : Surreal)).birthday ≤ NatOrdinal.of Ordinal.omega0 := by
  haveI := numeric_dyadicPlusInv d
  refine le_of_eq_of_le (congrArg birthday (dyadic_add_wpow_neg_one_eq d)) ?_
  refine (birthday_mk_le _).trans ?_
  rw [dyadicPlusInv, IGame.birthday_ofSets]
  have hbound : ∀ x : Dyadic, (x : IGame).birthday < NatOrdinal.of Ordinal.omega0 :=
    fun x ↦ IGame.short_iff_birthday_finite.1 (IGame.Short.dyadic x)
  refine max_le ?_ ?_
  · refine csSup_le' ?_
    rintro o ⟨g, hg, rfl⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact Order.succ_le_of_lt (hbound d)
  · refine csSup_le' ?_
    rintro o ⟨g, ⟨q, hq, rfl⟩, rfl⟩
    exact Order.succ_le_of_lt (hbound (d + q))

/-- **`d − ω⁻¹` is born by day `ω`** for every dyadic `d` (by symmetry). -/
theorem birthday_dyadic_sub_wpow_neg_one_le (d : Dyadic) :
    ((d : Surreal) - ω^ (-1 : Surreal)).birthday ≤ NatOrdinal.of Ordinal.omega0 := by
  have h := birthday_dyadic_add_wpow_neg_one_le (-d)
  rw [dyadic_cast_neg] at h
  have heq : (d : Surreal) - ω^ (-1 : Surreal) = -(-(d : Surreal) + ω^ (-1 : Surreal)) := by
    ring
  rw [heq, birthday_neg]
  exact h

/-- **The birthday of `ω⁻¹` is exactly `ω`**: at most `ω` by the cut representation
(`d = 0`), at least `ω` because a nonzero infinitesimal is not dyadic. -/
theorem birthday_wpow_neg_one :
    (ω^ (-1 : Surreal)).birthday = NatOrdinal.of Ordinal.omega0 := by
  refine le_antisymm ?_ ?_
  · have h := birthday_dyadic_add_wpow_neg_one_le 0
    have h0 : ((0 : Dyadic) : Surreal) = 0 := by
      show (((0 : Dyadic) : ℚ) : Surreal) = 0
      norm_num
    rwa [h0, zero_add] at h
  · refine omega0_le_birthday_of_infinitesimal_sub (c := 0) ?_ ?_ (wpow_ne_zero _)
    · rw [birthday_zero]
      exact NatOrdinal.of_pos.2 Ordinal.omega0_pos
    · rw [sub_zero]
      exact infinitesimal_wpow_neg_one

end Surreal

end
