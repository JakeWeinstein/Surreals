import Infinity.Exp
import Infinity.MicroKernel

/-!
# Gonshor's exponential at limit arguments: `exp ω = ω^ω`

Gonshor (An Introduction to the Theory of Surreal Numbers, ch. 10, after Kruskal) defines
the exponential on all of `No` by the genetic recursion

  `exp a = !{0, exp(aᴸ)·Eₙ(a − aᴸ), exp(aᴿ)·E₂ₙ₊₁(a − aᴿ) |
            exp(aᴿ)/Eₙ(aᴿ − a), exp(aᴸ)/E₂ₙ₊₁(aᴸ − a)}`

where `Eₙ(x) = Σ_{k ≤ n} xᵏ/k!` are the partial sums of the exponential series and on each
side only indices with `E₂ₙ₊₁(·) > 0` are admitted (Mantova–Matusinski survey, Thm 2.15).

This file verifies the recursion's **evaluation at limit-type arguments**: when
`a = !{s₀, s₁, … | ∅}` with each `a − sₙ` infinite, the right options vanish (the odd
partial sums at negative infinite arguments are negative, `expPartial_odd_neg`) and the
formula reduces to a left-only cut, which we prove equals a power of `ω` whose exponent is
itself a cut assembled from the `wlog`-data of the seed values (`gonshorCut_eq_wpow`).
Specialized at `ω = !{ℕ | ∅}` with the true seed values `exp n = eⁿ`, this yields the
survey's flagship computation, machine-checked (`gonshorExp_omega`):

  **`!{0, eⁿ·Eₖ(ω − n) | ∅} = ω^ω`** — the value of Gonshor's formula at `ω`.

What is *not* proved here: well-definedness/uniformity of the full recursion, or `exp` as
a total function on `No` — see `notes/gonshor-exp-design.md` for the honest scope and the
route map.

## Contents

* `Surreal.expPartial` — the partial sums `Eₙ`, with positivity, the dominant-term class
  computation `mk_expPartial` (`Eₙ(y) ~ yⁿ/n!` for infinite `y`), and the negativity of
  odd partial sums at negative infinite arguments.
* `Surreal.ofSets_left_eq_of_cofinal` — mutually cofinal left-cuts are equal (the
  simplicity-free cofinality bridge, descended from `IGame.equiv_of_exists_le`).
* `Surreal.wpow_ofSets` — CG's genetic `wpow` computed on a `Surreal`-level left-cut:
  `ω^ !{A | ∅} = !{{0} ∪ {r·ω^x : 0 < r dyadic, x ∈ A} | ∅}`.
* `Surreal.gonshorCut_eq_wpow` — the limit-step evaluation theorem.
* `Surreal.gonshorExp_omega` — the flagship: Gonshor's cut at `ω` equals `ω^ω^1`.
-/

open Set IGame

noncomputable section

namespace Surreal

/-! ### The exponential partial sums `Eₙ` -/

/-- `Eₙ(x) = Σ_{k ≤ n} xᵏ/k!`, the `n`-th partial sum of the exponential series
(Gonshor's `[x]ₙ`). -/
def expPartial (n : ℕ) (x : Surreal) : Surreal :=
  ∑ k ∈ Finset.range (n + 1), x ^ k / ((k.factorial : ℕ) : Surreal)

@[simp]
theorem expPartial_zero (x : Surreal) : expPartial 0 x = 1 := by
  simp [expPartial]

theorem expPartial_succ (n : ℕ) (x : Surreal) :
    expPartial (n + 1) x = expPartial n x + x ^ (n + 1) / (((n + 1).factorial : ℕ) : Surreal) :=
  Finset.sum_range_succ _ _

private theorem factorial_cast_pos (k : ℕ) : (0 : Surreal) < ((k.factorial : ℕ) : Surreal) := by
  exact_mod_cast k.factorial_pos

/-- Partial sums of the exponential series are positive at positive arguments (hence, in
Gonshor's formula, *all* indices `n` are admitted among the left options at a limit
argument). -/
theorem expPartial_pos {x : Surreal} (hx : 0 < x) (n : ℕ) : 0 < expPartial n x :=
  Finset.sum_pos (fun k _ ↦ div_pos (pow_pos hx k) (factorial_cast_pos k))
    (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero n))

theorem ne_zero_of_not_isFinite {y : Surreal} (h : ¬ IsFinite y) : y ≠ 0 :=
  fun h0 ↦ h (h0 ▸ isFinite_zero)

/-- Powers of an infinite surreal are strictly increasing in magnitude class
(the dual of `mk_pow_lt_mk_pow_succ'`). -/
theorem mk_pow_succ_lt_mk_pow {y : Surreal} (h : ¬ IsFinite y) (n : ℕ) :
    ArchimedeanClass.mk (y ^ (n + 1)) < ArchimedeanClass.mk (y ^ n) := by
  rw [ArchimedeanClass.mk_lt_mk]
  intro m
  have hy0 : y ≠ 0 := ne_zero_of_not_isFinite h
  have habs : (0 : Surreal) < |y| := abs_pos.2 hy0
  have hm : ((m : ℕ) : Surreal) < |y| := by
    by_contra hle
    exact h (isFinite_iff.2 ⟨m, not_lt.1 hle⟩)
  calc m • |y ^ n| = (m : Surreal) * |y| ^ n := by rw [nsmul_eq_mul, abs_pow]
    _ < |y| * |y| ^ n := by
        exact mul_lt_mul_of_pos_right hm (pow_pos habs n)
    _ = |y ^ (n + 1)| := by rw [abs_pow, pow_succ, mul_comm]

/-- The class of the `k`-th exponential-series term is that of `yᵏ`. -/
private theorem mk_expTerm (y : Surreal) (k : ℕ) :
    ArchimedeanClass.mk (y ^ k / ((k.factorial : ℕ) : Surreal)) =
      ArchimedeanClass.mk (y ^ k) := by
  rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero]

/-- **Dominant-term asymptotics**: at an infinite argument, the partial sum `Eₙ(y)` lives
in the magnitude class of its top term `yⁿ/n!`. -/
theorem mk_expPartial {y : Surreal} (h : ¬ IsFinite y) (n : ℕ) :
    ArchimedeanClass.mk (expPartial n y) = ArchimedeanClass.mk (y ^ n) := by
  induction n with
  | zero => rw [expPartial_zero, pow_zero]
  | succ n ih =>
    rw [expPartial_succ, ArchimedeanClass.mk_add_eq_mk_right, mk_expTerm]
    rw [mk_expTerm, ih]
    exact mk_pow_succ_lt_mk_pow h n

/-- Strict domination in class plus positivity of the dominator gives strict order:
if `b` strictly dominates `a` and `b > 0` then `a < b`. -/
theorem lt_of_mk_lt_of_pos {a b : Surreal}
    (h : ArchimedeanClass.mk b < ArchimedeanClass.mk a) (hb : 0 < b) : a < b :=
  lt_of_le_of_lt (le_abs_self a) (abs_of_pos hb ▸ abs_lt_abs_of_mk_lt h)

/-- **Odd partial sums are negative at negative infinite arguments.** This is the reason
Gonshor's right options `exp(aᴸ)/E₂ₙ₊₁(aᴸ − a)` vanish at a limit argument: the
admissibility condition `E₂ₙ₊₁(aᴸ − a) > 0` fails for every `n` (survey, computation of
`exp ω`: "since `E₂ₙ₊₁(n − ω) < 0` for any `n`"). -/
theorem expPartial_odd_neg {y : Surreal} (hy : y < 0) (hinf : ¬ IsFinite y) (k : ℕ) :
    expPartial (2 * k + 1) y < 0 := by
  rw [expPartial_succ]
  set t := y ^ (2 * k + 1) / (((2 * k + 1).factorial : ℕ) : Surreal) with ht
  have htneg : t < 0 :=
    div_neg_of_neg_of_pos (Odd.pow_neg ⟨k, by ring⟩ hy) (factorial_cast_pos _)
  have habs : |expPartial (2 * k) y| < |t| := by
    apply abs_lt_abs_of_mk_lt
    rw [ht, mk_expTerm, mk_expPartial hinf]
    exact mk_pow_succ_lt_mk_pow hinf (2 * k)
  have h1 : expPartial (2 * k) y ≤ |expPartial (2 * k) y| := le_abs_self _
  rw [abs_of_neg htneg] at habs
  linarith

/-! ### Cofinal left-cuts are equal

The simplicity-free cofinality bridge: two surreal cuts with no right options and mutually
`≤`-cofinal left sets are the *same* surreal. Descends `IGame.equiv_of_exists_le` through
the `Game` and `Surreal` quotients. -/

private theorem game_image_mk_out (S : Set Game) : Game.mk '' (Game.out '' S) = S := by
  rw [Set.image_image]
  simp only [Game.out_eq, Set.image_id']

/-- `OfSets` congruence over set equality (the `Small` and validity arguments are
propositional, so this is proof irrelevance). -/
private theorem game_ofSets_congr {S S' T T' : Set Game} [Small.{u} S] [Small.{u} S']
    [Small.{u} T] [Small.{u} T'] (hS : S = S') (hT : T = T') :
    (!{S | T} : Game) = !{S' | T'} := by
  subst hS; subst hT; rfl

private theorem game_ofSets_left_rep (S : Set Game) [Small.{u} S] :
    (!{S | ∅} : Game) = Game.mk !{Game.out '' S | (∅ : Set IGame)} := by
  rw [Game.mk_ofSets]
  exact game_ofSets_congr (game_image_mk_out S).symm (Set.image_empty _).symm

private theorem game_ofSets_left_eq {S T : Set Game} [Small.{u} S] [Small.{u} T]
    (hST : ∀ s ∈ S, ∃ t ∈ T, s ≤ t) (hTS : ∀ t ∈ T, ∃ s ∈ S, t ≤ s) :
    (!{S | ∅} : Game) = !{T | ∅} := by
  rw [game_ofSets_left_rep S, game_ofSets_left_rep T]
  apply Game.mk_eq
  apply equiv_of_exists_le
  · rw [leftMoves_ofSets, leftMoves_ofSets]
    rintro a ⟨s, hs, rfl⟩
    obtain ⟨t, ht, hst⟩ := hST s hs
    exact ⟨t.out, Set.mem_image_of_mem _ ht,
      by rw [← Game.mk_le_mk, Game.out_eq, Game.out_eq]; exact hst⟩
  · rw [rightMoves_ofSets]
    rintro a ha
    exact absurd ha (Set.notMem_empty a)
  · rw [leftMoves_ofSets, leftMoves_ofSets]
    rintro a ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hts⟩ := hTS t ht
    exact ⟨s.out, Set.mem_image_of_mem _ hs,
      by rw [← Game.mk_le_mk, Game.out_eq, Game.out_eq]; exact hts⟩
  · rw [rightMoves_ofSets]
    rintro a ha
    exact absurd ha (Set.notMem_empty a)

/-- **Mutually cofinal left-cuts are equal.** If every element of `A` is below some element
of `B` and vice versa, then `!{A | ∅} = !{B | ∅}`. -/
theorem ofSets_left_eq_of_cofinal {A B : Set Surreal} [Small.{u} A] [Small.{u} B]
    (hAB : ∀ a ∈ A, ∃ b ∈ B, a ≤ b) (hBA : ∀ b ∈ B, ∃ a ∈ A, b ≤ a) :
    (!{A | ∅} : Surreal) = !{B | ∅} := by
  rw [← toGame_inj, toGame_ofSets, toGame_ofSets]
  simp only [Set.image_empty]
  apply game_ofSets_left_eq
  · rintro s ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hab⟩ := hAB a ha
    exact ⟨toGame b, Set.mem_image_of_mem _ hb, toGame_le_iff.2 hab⟩
  · rintro t ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hba⟩ := hBA b hb
    exact ⟨toGame a, Set.mem_image_of_mem _ ha, toGame_le_iff.2 hba⟩

/-! ### `ω^` of a left-cut -/

private theorem numeric_ofSets_out_left (A : Set Surreal) [Small.{u} A] :
    Numeric (!{Surreal.out '' A | (∅ : Set IGame)}) := by
  refine Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
  · rw [rightMoves_ofSets] at hz
    exact absurd hz (Set.notMem_empty z)
  · cases p with
    | left =>
      rw [moves_ofSets] at hy
      obtain ⟨a, _, rfl⟩ := hy
      infer_instance
    | right =>
      rw [moves_ofSets] at hy
      exact absurd hy (Set.notMem_empty y)

/-- Every left-cut of surreals is represented by the corresponding left-cut of
representatives. -/
private theorem surreal_ofSets_left_rep (A : Set Surreal) [Small.{u} A] :
    (!{A | ∅} : Surreal) =
      @Surreal.mk (!{Surreal.out '' A | (∅ : Set IGame)}) (numeric_ofSets_out_left A) := by
  rw [← toGame_inj, toGame_ofSets, toGame_mk]
  refine (game_ofSets_congr rfl (Set.image_empty _)).trans ?_
  rw [game_ofSets_left_rep]
  apply Game.mk_eq
  apply equiv_of_exists_le
  · rw [leftMoves_ofSets, leftMoves_ofSets]
    rintro a ⟨s, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x.out, Set.mem_image_of_mem _ hx, ?_⟩
    rw [← Game.mk_le_mk, Game.out_eq, gameMk_out]
  · rw [rightMoves_ofSets]
    rintro a ha
    exact absurd ha (Set.notMem_empty a)
  · rw [leftMoves_ofSets, leftMoves_ofSets]
    rintro a ⟨x, hx, rfl⟩
    refine ⟨(toGame x).out, Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hx), ?_⟩
    rw [← Game.mk_le_mk, Game.out_eq, gameMk_out]
  · rw [rightMoves_ofSets]
    rintro a ha
    exact absurd ha (Set.notMem_empty a)

/-- **The `ω`-map on a left-cut**: CG's genetic definition of `ω^ ·` computed at the
`Surreal` level. The left options of `ω^ !{A | ∅}` are `0` together with all positive
dyadic multiples of `ω`-powers of elements of `A`, and there are no right options. -/
theorem wpow_ofSets (A : Set Surreal) [Small.{u} A] :
    ω^ (!{A | ∅} : Surreal) =
      !{insert 0 (Set.image2 (fun (r : Dyadic) (x : Surreal) ↦ (r : Surreal) * ω^ x)
        (Set.Ioi 0) A) | ∅} := by
  haveI := numeric_ofSets_out_left A
  haveI := numeric_ofSets_out_left (insert 0 (Set.image2 (fun (r : Dyadic) (x : Surreal) ↦
    (r : Surreal) * ω^ x) (Set.Ioi 0) A))
  rw [surreal_ofSets_left_rep A, ← Surreal.mk_wpow,
    surreal_ofSets_left_rep (insert 0 (Set.image2 (fun (r : Dyadic) (x : Surreal) ↦
      (r : Surreal) * ω^ x) (Set.Ioi 0) A))]
  apply Surreal.mk_eq
  apply equiv_of_exists_le
  · rw [leftMoves_wpow, leftMoves_ofSets, leftMoves_ofSets]
    rintro a (rfl | ⟨r, hr, y, ⟨x, hx, rfl⟩, rfl⟩)
    · refine ⟨Surreal.out 0, Set.mem_image_of_mem _ (Set.mem_insert 0 _), ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.out_eq]
      simp
    · refine ⟨Surreal.out ((r : Surreal) * ω^ x),
        Set.mem_image_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_image2_of_mem hr hx)), ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.out_eq, Surreal.mk_mul, Surreal.mk_dyadic,
        Surreal.mk_wpow, Surreal.out_eq]
  · rw [rightMoves_wpow, rightMoves_ofSets, Set.image2_empty_right]
    rintro a ha
    exact absurd ha (Set.notMem_empty a)
  · rw [leftMoves_wpow, leftMoves_ofSets, leftMoves_ofSets]
    rintro a ⟨b, hb, rfl⟩
    rcases hb with rfl | ⟨r, hr, x, hx, rfl⟩
    · refine ⟨0, Set.mem_insert 0 _, ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.out_eq]
      simp
    · refine ⟨(r : IGame) * ω^ (Surreal.out x),
        Set.mem_insert_of_mem _ (Set.mem_image2_of_mem hr (Set.mem_image_of_mem _ hx)), ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.out_eq, Surreal.mk_mul, Surreal.mk_dyadic,
        Surreal.mk_wpow, Surreal.out_eq]
  · rw [rightMoves_ofSets]
    rintro a ha
    exact absurd ha (Set.notMem_empty a)

/-! ### The limit-step evaluation theorem -/

/-- The `ω`-logarithm of an infinite surreal is positive. -/
theorem wlog_pos {u : Surreal} (h : ¬ IsFinite u) : 0 < wlog u := by
  have hu : u ≠ 0 := ne_zero_of_not_isFinite h
  have h2 : ArchimedeanClass.mk (ω^ wlog u) < ArchimedeanClass.mk (ω^ (0 : Surreal)) := by
    rw [archimedeanClassMk_wpow_wlog hu, wpow_zero, ArchimedeanClass.mk_one]
    exact not_le.1 fun hle ↦ h hle
  exact archimedeanClassMk_wpow_strictAnti.lt_iff_gt.1 h2

/-- `ω`-powers at natural multiples are iterated powers. -/
theorem wpow_natCast_mul (d : Surreal) (k : ℕ) : ω^ ((k : Surreal) * d) = (ω^ d) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, wpow_add, ih, pow_succ]

/-- The magnitude class of a Gonshor option `v · Eₖ(y)`: it is that of
`ω^(wlog v + k · wlog y)`. -/
private theorem mk_gonshor_option {v y : Surreal} (hv0 : v ≠ 0) (hy : ¬ IsFinite y) (k : ℕ) :
    ArchimedeanClass.mk (v * expPartial k y) =
      ArchimedeanClass.mk (ω^ (wlog v + (k : Surreal) * wlog y)) := by
  rw [ArchimedeanClass.mk_mul, mk_expPartial hy, ArchimedeanClass.mk_pow,
    wpow_add, wpow_natCast_mul, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_pow,
    archimedeanClassMk_wpow_wlog hv0,
    archimedeanClassMk_wpow_wlog (ne_zero_of_not_isFinite hy)]

private theorem mk_dyadic_cast {r : Dyadic} (hr : r ≠ 0) :
    ArchimedeanClass.mk ((r : Surreal)) = 0 := by
  rw [← Real.toSurreal_ratCast]
  exact mk_realCast (by exact_mod_cast hr)

/-- **The limit-step evaluation theorem.** Let `a` be any surreal, `s n < a` approximants
with each gap `a − s n` infinite, and `v n > 0` "seed values". Then the left-only cut
whose options are `0` and all `v n · Eₖ(a − s n)` equals the `ω`-power of the cut of
exponents `wlog (v n) + k · wlog (a − s n)`.

Interpretation (Gonshor ch. 10, survey Thm 2.15): when `a = !{s₀, s₁, … | ∅}` and
`v n = exp (s n)` are the recursion's already-known values, the LHS is exactly Gonshor's
genetic formula for `exp a` — its right options vanish by `expPartial_odd_neg` — and the
RHS displays the value as `ω^(cut of exponents)`, the mechanism behind Gonshor's
`g`-function. The theorem itself is representation-free: only the domination structure of
the options matters. -/
theorem gonshorCut_eq_wpow {a : Surreal} {s v : ℕ → Surreal}
    (hv : ∀ n, 0 < v n) (hs : ∀ n, s n < a) (hinf : ∀ n, ¬ IsFinite (a - s n)) :
    (!{insert 0 (Set.range fun p : ℕ × ℕ ↦ v p.1 * expPartial p.2 (a - s p.1)) | ∅} : Surreal)
      = ω^ (!{Set.range fun p : ℕ × ℕ ↦
          wlog (v p.1) + (p.2 : Surreal) * wlog (a - s p.1) | ∅} : Surreal) := by
  rw [wpow_ofSets]
  apply ofSets_left_eq_of_cofinal
  · rintro z (rfl | ⟨⟨n, k⟩, rfl⟩)
    · exact ⟨0, Set.mem_insert 0 _, le_rfl⟩
    · refine ⟨((1 : Dyadic) : Surreal) *
          ω^ (wlog (v n) + ((k + 1 : ℕ) : Surreal) * wlog (a - s n)),
        Set.mem_insert_of_mem _
          (Set.mem_image2_of_mem (by norm_num) ⟨(n, k + 1), rfl⟩), ?_⟩
      have hone : ((1 : Dyadic) : Surreal) = 1 := by norm_cast
      rw [hone, one_mul]
      refine le_of_lt (lt_of_mk_lt_of_pos ?_ (wpow_pos _))
      rw [mk_gonshor_option (hv n).ne' (hinf n)]
      apply archimedeanClassMk_wpow_strictAnti
      have hd : 0 < wlog (a - s n) := wlog_pos (hinf n)
      have hk : ((k : ℕ) : Surreal) < ((k + 1 : ℕ) : Surreal) := by
        exact_mod_cast k.lt_succ_self
      have hmul := mul_lt_mul_of_pos_right hk hd
      show wlog (v n) + ((k : ℕ) : Surreal) * wlog (a - s n) <
        wlog (v n) + ((k + 1 : ℕ) : Surreal) * wlog (a - s n)
      linarith
  · rintro z (rfl | ⟨r, hr, e, ⟨⟨n, k⟩, rfl⟩, rfl⟩)
    · exact ⟨0, Set.mem_insert 0 _, le_rfl⟩
    · refine ⟨v n * expPartial (k + 1) (a - s n),
        Set.mem_insert_of_mem _ ⟨(n, k + 1), rfl⟩, ?_⟩
      have hy : 0 < a - s n := sub_pos.2 (hs n)
      refine le_of_lt (lt_of_mk_lt_of_pos ?_
        (mul_pos (hv n) (expPartial_pos hy (k + 1))))
      rw [mk_gonshor_option (hv n).ne' (hinf n), ArchimedeanClass.mk_mul,
        mk_dyadic_cast (ne_of_gt hr), zero_add]
      apply archimedeanClassMk_wpow_strictAnti
      have hd : 0 < wlog (a - s n) := wlog_pos (hinf n)
      have hk : ((k : ℕ) : Surreal) < ((k + 1 : ℕ) : Surreal) := by
        exact_mod_cast k.lt_succ_self
      have hmul := mul_lt_mul_of_pos_right hk hd
      show wlog (v n) + ((k : ℕ) : Surreal) * wlog (a - s n) <
        wlog (v n) + ((k + 1 : ℕ) : Surreal) * wlog (a - s n)
      linarith

end Surreal
