import Infinity.BirthdayHahn
import Infinity.ExpLog
import Infinity.CauchyProduct

/-!
# Canonical sums by game cofinality: the multiplicativity theorem

The canonical transfinite sum `hahnSum t` of a strictly dominating series was defined in
`Infinity.CanonicalSum` as the birthday-simplest Hahn sum, via `Cut.simplestBtwn`. The
existence proof in `Infinity.Summation` built a *different* object: the Conway cut
`!{sₙ − 2|tₙ| ∣ sₙ + 2|tₙ|}` of partial sums sandwiched within twice their current term.
This file proves that the two coincide, and turns that identification into an *engine*:

* `Surreal.optionGame t` — the option game `!{sₙ − 2|tₙ| ∣ sₙ + 2|tₙ|}` as an `IGame`;
  `Surreal.numeric_optionGame` (it is numeric for strictly dominating `t`).
* **The bridge** `Surreal.mk_optionGame_eq_hahnSum`: `Surreal.mk (optionGame t) = hahnSum t`.
  The value of the option game is a Hahn sum, and every Hahn sum *fits* the option game
  (the next-index estimate `Surreal.abs_sub_partialSum_lt`: `|w − sₙ| < 2|tₙ|`, because
  `w − sₙ = tₙ + (w − sₙ₊₁)` with `|w − sₙ₊₁| ≪ |tₙ|`), so by the simplicity theorem
  (`Cut.simplestBtwn_supLeft_infRight`, `Cut.birthday_simplestBtwn_le_of_fits`) the option
  game's value is the birthday-minimal Hahn sum.
* **The identification engine** `Surreal.hahnSum_eq_of_isHahnSum_of_moves_le`: if a numeric
  game `G` has a Hahn-sum value and every option of `G` is beaten by an option of the option
  game, then `hahnSum t = Surreal.mk G`. This is `IGame.Fits.equiv_of_forall_moves` applied
  to `G` and the option game — one simplicity-theorem application, no birthday census.
* **The product engine** `Surreal.hahnSum_eq_mul_of_cofinal` and **the multiplicativity
  theorem** `Surreal.hahnSum_mul_hahnSum_eq_hahnSum_cauchyMul`: for strictly dominating
  `t, u` whose Cauchy product `c` is strictly dominating, satisfies the floor hypothesis of
  `IsHahnSum.mul`, and is *cofinal* in the products (`∀ m n, ∃ N, mk (tₘ uₙ) < mk (c N)`),
  `hahnSum t * hahnSum u = hahnSum c`. The engine is applied to the Conway product of the two
  option games: each of its options differs from the product value by a positive quantity of
  class exactly `mk (tₘ uₙ)`, which cofinality places beyond some option of the `c`-game.
* **The comparable-class exponential functional equation**
  `Surreal.expInf_add_eq_mul_of_comparable`: for positive infinitesimals `σ, τ` with
  comparable Archimedean classes (`mk σ ≤ K • mk τ` and `mk τ ≤ K • mk σ` for some `K : ℕ`),
  `expInf (σ + τ) = expInf σ * expInf τ`. Corollaries: the equal-class case
  `Surreal.expInf_add_eq_mul_of_mk_eq`, the squaring law `Surreal.expInf_add_self_eq_mul`,
  and a one-line re-derivation `Surreal.expInf_add_logOmega_eq_mul'` of the lattice instance
  proved by census in `Infinity.ExpFibre`.
* **The sum engine and the additivity theorem** `Surreal.hahnSum_eq_add_of_cofinal`,
  `Surreal.hahnSum_add_hahnSum_eq_hahnSum_add`: the same argument on the Conway sum of the
  two option games gives `hahnSum t + hahnSum u = hahnSum (t + u)` under no cancellation
  (`mk (tₙ + uₙ) ≤ min (mk tₙ) (mk uₙ)`) and cofinality of `t + u` in both `t` and `u`.

The lesson (recorded in `tasks/lessons.md`): identification of canonical sums is a
*cofinality* statement about option games, and never needs a birthday census.
-/

open ArchimedeanClass Finset IGame

universe u

noncomputable section

namespace Surreal

variable {t : ℕ → Surreal.{u}}

/-! ### The option values and the next-index estimate -/

/-- The lower option `sₙ − 2|tₙ|` of the summation cut. -/
def optLo (t : ℕ → Surreal) (n : ℕ) : Surreal :=
  partialSum t n - 2 * |t n|

/-- The upper option `sₙ + 2|tₙ|` of the summation cut. -/
def optHi (t : ℕ → Surreal) (n : ℕ) : Surreal :=
  partialSum t n + 2 * |t n|

/-- **The next-index estimate**: a Hahn sum `w` of a strictly dominating series satisfies the
*strict* bound `|w − sₙ| < 2|tₙ|` at every index, because `w − sₙ = tₙ + (w − sₙ₊₁)` and
the residual at the next index is strictly dominated by `tₙ`. -/
theorem abs_sub_partialSum_lt
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {w : Surreal} (hw : IsHahnSum t w) (n : ℕ) :
    |w - partialSum t n| < 2 * |t n| := by
  have h1 : ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (w - partialSum t (n + 1)) :=
    (ht n).trans_le (hw (n + 1))
  have h2 := abs_lt.1 (abs_lt_abs_of_mk_lt h1)
  have hs : w - partialSum t n = t n + (w - partialSum t (n + 1)) := by
    rw [partialSum_succ]; ring
  rw [hs]
  have h3 := neg_abs_le (t n)
  have h4 := le_abs_self (t n)
  exact abs_lt.2 ⟨by linarith [h2.1], by linarith [h2.2]⟩

theorem optLo_lt_of_isHahnSum
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {w : Surreal} (hw : IsHahnSum t w) (n : ℕ) : optLo t n < w := by
  have h := (abs_lt.1 (abs_sub_partialSum_lt ht hw n)).1
  unfold optLo
  linarith

theorem lt_optHi_of_isHahnSum
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {w : Surreal} (hw : IsHahnSum t w) (n : ℕ) : w < optHi t n := by
  have h := (abs_lt.1 (abs_sub_partialSum_lt ht hw n)).2
  unfold optHi
  linarith

/-- Conversely, anything strictly between all the options is a Hahn sum. -/
theorem isHahnSum_of_forall_opt {w : Surreal}
    (h : ∀ n, optLo t n < w ∧ w < optHi t n) : IsHahnSum t w := by
  intro n
  obtain ⟨h1, h2⟩ := h n
  unfold optLo at h1
  unfold optHi at h2
  rw [ArchimedeanClass.mk_le_mk]
  refine ⟨2, ?_⟩
  calc |w - partialSum t n| ≤ 2 * |t n| := abs_le.2 ⟨by linarith, by linarith⟩
    _ = 2 • |t n| := by rw [two_nsmul, two_mul]

/-- The two option sets of the summation cut are separated. -/
theorem optLo_lt_optHi
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) (m n : ℕ) :
    optLo t m < optHi t n :=
  (optLo_lt_of_isHahnSum ht (isHahnSum_hahnSum ht) m).trans
    (lt_optHi_of_isHahnSum ht (isHahnSum_hahnSum ht) n)

/-! ### The option game -/

/-- **The option game** of a series: the Conway cut `!{sₙ − 2|tₙ| ∣ sₙ + 2|tₙ|}` of
`Infinity.Summation`, as an explicit `IGame` whose options are (representatives of) the
surreal option values. -/
def optionGame (t : ℕ → Surreal.{u}) : IGame.{u} :=
  !{Set.range (fun n ↦ (optLo t n).out) | Set.range (fun n ↦ (optHi t n).out)}

theorem leftMoves_optionGame (t : ℕ → Surreal.{u}) :
    (optionGame t)ᴸ = Set.range (fun n ↦ (optLo t n).out) :=
  leftMoves_ofSets ..

theorem rightMoves_optionGame (t : ℕ → Surreal.{u}) :
    (optionGame t)ᴿ = Set.range (fun n ↦ (optHi t n).out) :=
  rightMoves_ofSets ..

theorem optLo_out_mem_leftMoves_optionGame (t : ℕ → Surreal.{u}) (n : ℕ) :
    (optLo t n).out ∈ (optionGame t)ᴸ := by
  rw [leftMoves_optionGame]
  exact ⟨n, rfl⟩

theorem optHi_out_mem_rightMoves_optionGame (t : ℕ → Surreal.{u}) (n : ℕ) :
    (optHi t n).out ∈ (optionGame t)ᴿ := by
  rw [rightMoves_optionGame]
  exact ⟨n, rfl⟩

/-- The option game of a strictly dominating series is numeric. -/
theorem numeric_optionGame
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    (optionGame t).Numeric := by
  refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
  · rw [leftMoves_optionGame] at hy
    rw [rightMoves_optionGame] at hz
    obtain ⟨m, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := hz
    rw [← Surreal.mk_lt_mk, out_eq, out_eq]
    exact optLo_lt_optHi ht m n
  · cases p with
    | left =>
      rw [optionGame, moves_ofSets] at hy
      obtain ⟨n, rfl⟩ := hy
      infer_instance
    | right =>
      rw [optionGame, moves_ofSets] at hy
      obtain ⟨n, rfl⟩ := hy
      infer_instance

/-! ### The bridge: the option game's value is the canonical sum -/

/-- The value of the option game is a Hahn sum: it lies strictly between all its options. -/
theorem isHahnSum_mk_optionGame
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    IsHahnSum t (@Surreal.mk (optionGame t) (numeric_optionGame ht)) := by
  haveI := numeric_optionGame ht
  refine isHahnSum_of_forall_opt fun n ↦ ⟨?_, ?_⟩
  · have h := Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt (optLo_out_mem_leftMoves_optionGame t n))
    rwa [out_eq] at h
  · have h := Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right (optHi_out_mem_rightMoves_optionGame t n))
    rwa [out_eq] at h

/-- **The simplicity theorem, value form**: if (a representative of) the surreal `w` fits the
numeric game `G`, then the value of `G` is born no later than `w`. -/
theorem birthday_mk_le_of_fits {G : IGame.{u}} [G.Numeric] {w : Surreal.{u}}
    (h : w.out.Fits G) : (Surreal.mk G).birthday ≤ w.birthday := by
  have hfit : Cut.Fits w (Cut.supLeft G) (Cut.infRight G) := by
    rw [← out_eq w]
    exact (Cut.fits_supLeft_infRight).2 h
  have h1 := Cut.birthday_simplestBtwn_le_of_fits hfit
  have h2 : Cut.simplestBtwn hfit.lt = Surreal.mk G := by
    rw [← toGame_inj, Cut.simplestBtwn_supLeft_infRight hfit.lt, toGame_mk]
  rwa [h2] at h1

/-- Every numeric game whose value is a Hahn sum fits the option game (the next-index
estimate in game clothing). -/
theorem fits_optionGame_of_isHahnSum
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {w : Surreal.{u}} (hw : IsHahnSum t w) {x : IGame.{u}} [x.Numeric]
    (hx : Surreal.mk x = w) : x.Fits (optionGame t) := by
  constructor
  · intro z hz
    rw [leftMoves_optionGame] at hz
    obtain ⟨n, rfl⟩ := hz
    refine IGame.Numeric.not_le.2 ?_
    rw [← Surreal.mk_lt_mk, out_eq, hx]
    exact optLo_lt_of_isHahnSum ht hw n
  · intro z hz
    rw [rightMoves_optionGame] at hz
    obtain ⟨n, rfl⟩ := hz
    refine IGame.Numeric.not_le.2 ?_
    rw [← Surreal.mk_lt_mk, out_eq, hx]
    exact lt_optHi_of_isHahnSum ht hw n

/-- **The bridge**: the value of the option game `!{sₙ − 2|tₙ| ∣ sₙ + 2|tₙ|}` is the canonical
transfinite sum. Its value is a Hahn sum, and every Hahn sum fits it, so by the simplicity
theorem its value is the birthday-minimal Hahn sum. -/
theorem mk_optionGame_eq_hahnSum
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    @Surreal.mk (optionGame t) (numeric_optionGame ht) = hahnSum ht := by
  haveI := numeric_optionGame ht
  symm
  rw [hahnSum_eq_iff]
  refine ⟨isHahnSum_mk_optionGame ht, fun w hw ↦ ?_⟩
  exact birthday_mk_le_of_fits (fits_optionGame_of_isHahnSum ht hw (out_eq w))

/-- The birthday of the canonical sum is bounded by the birthday of the option game. -/
theorem birthday_hahnSum_le_birthday_optionGame
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    (hahnSum ht).birthday ≤ (optionGame t).birthday := by
  haveI := numeric_optionGame ht
  rw [← mk_optionGame_eq_hahnSum ht]
  exact birthday_mk_le _

/-! ### The identification engine -/

/-- **The identification engine**: to identify the canonical sum with the value of a numeric
game `G`, it suffices that the value be a Hahn sum and that every option of `G` be beaten by
an option of the option game. Then `G` fits the option game and
`IGame.Fits.equiv_of_forall_moves` (the simplicity theorem) gives `G ≈ optionGame t`. -/
theorem hahnSum_eq_of_isHahnSum_of_moves_le
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {G : IGame.{u}} [G.Numeric] (hG : IsHahnSum t (Surreal.mk G))
    (hl : ∀ a ∈ Gᴸ, ∃ n, a ≤ (optLo t n).out)
    (hr : ∀ b ∈ Gᴿ, ∃ n, (optHi t n).out ≤ b) :
    hahnSum ht = Surreal.mk G := by
  haveI := numeric_optionGame ht
  have hfit : G.Fits (optionGame t) := fits_optionGame_of_isHahnSum ht hG rfl
  have hequiv : G ≈ optionGame t := by
    refine hfit.equiv_of_forall_moves ?_ ?_
    · intro a ha
      obtain ⟨n, hn⟩ := hl a ha
      exact ⟨(optLo t n).out, optLo_out_mem_leftMoves_optionGame t n, hn⟩
    · intro b hb
      obtain ⟨n, hn⟩ := hr b hb
      exact ⟨(optHi t n).out, optHi_out_mem_rightMoves_optionGame t n, hn⟩
  rw [← mk_optionGame_eq_hahnSum ht]
  exact (Surreal.mk_eq hequiv).symm

/-- The identification engine with the option comparisons stated at the level of surreal
values. -/
theorem hahnSum_eq_of_isHahnSum_of_mk_moves_le
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {G : IGame.{u}} [G.Numeric] (hG : IsHahnSum t (Surreal.mk G))
    (hl : ∀ a (ha : a ∈ Gᴸ), ∃ n, @Surreal.mk a (IGame.Numeric.of_mem_moves ha) ≤ optLo t n)
    (hr : ∀ b (hb : b ∈ Gᴿ), ∃ n, optHi t n ≤ @Surreal.mk b (IGame.Numeric.of_mem_moves hb)) :
    hahnSum ht = Surreal.mk G := by
  refine hahnSum_eq_of_isHahnSum_of_moves_le ht hG ?_ ?_
  · intro a ha
    obtain ⟨n, hn⟩ := hl a ha
    haveI := IGame.Numeric.of_mem_moves ha
    refine ⟨n, ?_⟩
    rw [← Surreal.mk_le_mk, out_eq]
    exact hn
  · intro b hb
    obtain ⟨n, hn⟩ := hr b hb
    haveI := IGame.Numeric.of_mem_moves hb
    refine ⟨n, ?_⟩
    rw [← Surreal.mk_le_mk, out_eq]
    exact hn

/-! ### The product engine -/

/-- The value of a general product option, at the level of surreals. -/
theorem mk_mulOption (x y a b : IGame.{u}) [x.Numeric] [y.Numeric] [a.Numeric] [b.Numeric] :
    Surreal.mk (mulOption x y a b) =
      Surreal.mk a * Surreal.mk y + Surreal.mk x * Surreal.mk b - Surreal.mk a * Surreal.mk b :=
  rfl

private theorem four_nsmul_eq (a : Surreal) : (4 : ℕ) • |a| = 4 * |a| := by
  rw [nsmul_eq_mul]; norm_num

/-- A Hahn sum sits a definite multiple of `|tₘ|` above the lower option `sₘ − 2|tₘ|`:
`|tₘ| < 2 (x − optLo)` and `x − optLo < 4 |tₘ|`. -/
theorem sub_optLo_bounds
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {x : Surreal} (hx : IsHahnSum t x) (m : ℕ) :
    |t m| < 2 * (x - optLo t m) ∧ x - optLo t m < 4 * |t m| := by
  have h1 : ArchimedeanClass.mk (t m) < ArchimedeanClass.mk (x - partialSum t (m + 1)) :=
    (ht m).trans_le (hx (m + 1))
  have h2 := (ArchimedeanClass.mk_lt_mk.1 h1) 2
  rw [two_nsmul] at h2
  have hs : x - optLo t m = t m + 2 * |t m| + (x - partialSum t (m + 1)) := by
    unfold optLo; rw [partialSum_succ]; ring
  rw [hs]
  have h3 := neg_abs_le (t m)
  have h4 := le_abs_self (t m)
  have h5 := neg_abs_le (x - partialSum t (m + 1))
  have h6 := le_abs_self (x - partialSum t (m + 1))
  have h7 := abs_nonneg (t m)
  constructor <;> linarith

/-- A Hahn sum sits a definite multiple of `|tₘ|` below the upper option `sₘ + 2|tₘ|`. -/
theorem optHi_sub_bounds
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {x : Surreal} (hx : IsHahnSum t x) (m : ℕ) :
    |t m| < 2 * (optHi t m - x) ∧ optHi t m - x < 4 * |t m| := by
  have h1 : ArchimedeanClass.mk (t m) < ArchimedeanClass.mk (x - partialSum t (m + 1)) :=
    (ht m).trans_le (hx (m + 1))
  have h2 := (ArchimedeanClass.mk_lt_mk.1 h1) 2
  rw [two_nsmul] at h2
  have hs : optHi t m - x = 2 * |t m| - t m - (x - partialSum t (m + 1)) := by
    unfold optHi; rw [partialSum_succ]; ring
  rw [hs]
  have h3 := neg_abs_le (t m)
  have h4 := le_abs_self (t m)
  have h5 := neg_abs_le (x - partialSum t (m + 1))
  have h6 := le_abs_self (x - partialSum t (m + 1))
  have h7 := abs_nonneg (t m)
  constructor <;> linarith

private theorem pos_of_bounds {a v : Surreal} (h1 : |a| < 2 * v) : 0 < v := by
  have := abs_nonneg a
  linarith

/-- Two-sided bounds by multiples of `|a|` pin the Archimedean class. -/
theorem mk_eq_of_bounds {a v : Surreal} (h1 : |a| < 2 * v) (h2 : v < 4 * |a|) :
    ArchimedeanClass.mk v = ArchimedeanClass.mk a := by
  have hv : 0 < v := pos_of_bounds h1
  apply le_antisymm
  · rw [ArchimedeanClass.mk_le_mk]
    refine ⟨2, ?_⟩
    rw [abs_of_pos hv, two_nsmul]
    linarith
  · rw [ArchimedeanClass.mk_le_mk]
    refine ⟨4, ?_⟩
    rw [abs_of_pos hv, four_nsmul_eq]
    linarith

/-- **The option estimate, lower side**: if `P` is a Hahn sum of `c` and `D > 0` is of
strictly coarser class than `c N`, then `P − D` lies below the lower option `optLo c N`. -/
theorem sub_le_optLo_of_mk_lt {c : ℕ → Surreal.{u}}
    (hc : ∀ n, ArchimedeanClass.mk (c n) < ArchimedeanClass.mk (c (n + 1)))
    {P : Surreal} (hP : IsHahnSum c P) {D : Surreal} (hD : 0 < D) {N : ℕ}
    (hN : ArchimedeanClass.mk D < ArchimedeanClass.mk (c N)) :
    P - D ≤ optLo c N := by
  have h1 := abs_lt.1 (abs_sub_partialSum_lt hc hP N)
  have h2 := (ArchimedeanClass.mk_lt_mk.1 hN) 4
  rw [abs_of_pos hD, four_nsmul_eq] at h2
  unfold optLo
  linarith [h1.2]

/-- **The option estimate, upper side**. -/
theorem optHi_le_add_of_mk_lt {c : ℕ → Surreal.{u}}
    (hc : ∀ n, ArchimedeanClass.mk (c n) < ArchimedeanClass.mk (c (n + 1)))
    {P : Surreal} (hP : IsHahnSum c P) {D : Surreal} (hD : 0 < D) {N : ℕ}
    (hN : ArchimedeanClass.mk D < ArchimedeanClass.mk (c N)) :
    optHi c N ≤ P + D := by
  have h1 := abs_lt.1 (abs_sub_partialSum_lt hc hP N)
  have h2 := (ArchimedeanClass.mk_lt_mk.1 hN) 4
  rw [abs_of_pos hD, four_nsmul_eq] at h2
  unfold optHi
  linarith [h1.1]

/-- **The product engine**: if the product of two canonical sums is a Hahn sum of a strictly
dominating series `c` which is *cofinal* in the products of terms
(`∀ m n, ∃ N, mk (tₘ uₙ) < mk (c N)`), then the product *is* the canonical sum of `c`.

Proof: apply the identification engine to the Conway product of the two option games. Each
left option of the product has value `x·y − D` with `D > 0` of class `mk (tₘ uₙ)` (a product
of two residuals `x − optLo t m`, `y − optLo u n`, or of two `optHi − x`-type residuals),
and each right option has value `x·y + D` for such a `D`; cofinality supplies an `N` with
`mk D < mk (c N)`, and the option estimate places `x·y ∓ D` beyond the `N`-th option of the
`c`-game. -/
theorem hahnSum_eq_mul_of_cofinal {t u c : ℕ → Surreal.{u}}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (hc : ∀ n, ArchimedeanClass.mk (c n) < ArchimedeanClass.mk (c (n + 1)))
    (hP : IsHahnSum c (hahnSum ht * hahnSum hu))
    (hcof : ∀ m n, ∃ N, ArchimedeanClass.mk (t m * u n) < ArchimedeanClass.mk (c N)) :
    hahnSum hc = hahnSum ht * hahnSum hu := by
  haveI := numeric_optionGame ht
  haveI := numeric_optionGame hu
  have hx : IsHahnSum t (hahnSum ht) := isHahnSum_hahnSum ht
  have hy : IsHahnSum u (hahnSum hu) := isHahnSum_hahnSum hu
  have hG : Surreal.mk (optionGame t * optionGame u) = hahnSum ht * hahnSum hu := by
    rw [Surreal.mk_mul, mk_optionGame_eq_hahnSum ht, mk_optionGame_eq_hahnSum hu]
  rw [← hG]
  refine hahnSum_eq_of_isHahnSum_of_moves_le hc (by rwa [hG]) ?_ ?_
  · -- left options: both-left or both-right pairs
    rw [forall_moves_mul]
    intro p a ha b hb
    cases p with
    | left =>
      rw [Player.left_mul] at hb
      rw [leftMoves_optionGame] at ha hb
      obtain ⟨m, rfl⟩ := ha
      obtain ⟨n, rfl⟩ := hb
      obtain ⟨N, hN⟩ := hcof m n
      refine ⟨N, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, mk_mulOption, out_eq, out_eq,
        mk_optionGame_eq_hahnSum ht, mk_optionGame_eq_hahnSum hu]
      have h1 := sub_optLo_bounds ht hx m
      have h2 := sub_optLo_bounds hu hy n
      have hDpos : 0 < (hahnSum ht - optLo t m) * (hahnSum hu - optLo u n) :=
        mul_pos (pos_of_bounds h1.1) (pos_of_bounds h2.1)
      have hDmk : ArchimedeanClass.mk ((hahnSum ht - optLo t m) * (hahnSum hu - optLo u n)) <
          ArchimedeanClass.mk (c N) := by
        rw [ArchimedeanClass.mk_mul, mk_eq_of_bounds h1.1 h1.2, mk_eq_of_bounds h2.1 h2.2,
          ← ArchimedeanClass.mk_mul]
        exact hN
      have key := sub_le_optLo_of_mk_lt hc hP hDpos hDmk
      have hid : optLo t m * hahnSum hu + hahnSum ht * optLo u n - optLo t m * optLo u n =
          hahnSum ht * hahnSum hu -
            (hahnSum ht - optLo t m) * (hahnSum hu - optLo u n) := by ring
      rw [hid]
      exact key
    | right =>
      rw [Player.right_mul, Player.neg_left] at hb
      rw [rightMoves_optionGame] at ha hb
      obtain ⟨m, rfl⟩ := ha
      obtain ⟨n, rfl⟩ := hb
      obtain ⟨N, hN⟩ := hcof m n
      refine ⟨N, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, mk_mulOption, out_eq, out_eq,
        mk_optionGame_eq_hahnSum ht, mk_optionGame_eq_hahnSum hu]
      have h1 := optHi_sub_bounds ht hx m
      have h2 := optHi_sub_bounds hu hy n
      have hDpos : 0 < (optHi t m - hahnSum ht) * (optHi u n - hahnSum hu) :=
        mul_pos (pos_of_bounds h1.1) (pos_of_bounds h2.1)
      have hDmk : ArchimedeanClass.mk ((optHi t m - hahnSum ht) * (optHi u n - hahnSum hu)) <
          ArchimedeanClass.mk (c N) := by
        rw [ArchimedeanClass.mk_mul, mk_eq_of_bounds h1.1 h1.2, mk_eq_of_bounds h2.1 h2.2,
          ← ArchimedeanClass.mk_mul]
        exact hN
      have key := sub_le_optLo_of_mk_lt hc hP hDpos hDmk
      have hid : optHi t m * hahnSum hu + hahnSum ht * optHi u n - optHi t m * optHi u n =
          hahnSum ht * hahnSum hu -
            (optHi t m - hahnSum ht) * (optHi u n - hahnSum hu) := by ring
      rw [hid]
      exact key
  · -- right options: mixed pairs
    rw [forall_moves_mul]
    intro p a ha b hb
    cases p with
    | left =>
      rw [Player.left_mul] at hb
      rw [leftMoves_optionGame] at ha
      rw [rightMoves_optionGame] at hb
      obtain ⟨m, rfl⟩ := ha
      obtain ⟨n, rfl⟩ := hb
      obtain ⟨N, hN⟩ := hcof m n
      refine ⟨N, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, mk_mulOption, out_eq, out_eq,
        mk_optionGame_eq_hahnSum ht, mk_optionGame_eq_hahnSum hu]
      have h1 := sub_optLo_bounds ht hx m
      have h2 := optHi_sub_bounds hu hy n
      have hDpos : 0 < (hahnSum ht - optLo t m) * (optHi u n - hahnSum hu) :=
        mul_pos (pos_of_bounds h1.1) (pos_of_bounds h2.1)
      have hDmk : ArchimedeanClass.mk ((hahnSum ht - optLo t m) * (optHi u n - hahnSum hu)) <
          ArchimedeanClass.mk (c N) := by
        rw [ArchimedeanClass.mk_mul, mk_eq_of_bounds h1.1 h1.2, mk_eq_of_bounds h2.1 h2.2,
          ← ArchimedeanClass.mk_mul]
        exact hN
      have key := optHi_le_add_of_mk_lt hc hP hDpos hDmk
      have hid : optLo t m * hahnSum hu + hahnSum ht * optHi u n - optLo t m * optHi u n =
          hahnSum ht * hahnSum hu +
            (hahnSum ht - optLo t m) * (optHi u n - hahnSum hu) := by ring
      rw [hid]
      exact key
    | right =>
      rw [Player.right_mul, Player.neg_right] at hb
      rw [rightMoves_optionGame] at ha
      rw [leftMoves_optionGame] at hb
      obtain ⟨m, rfl⟩ := ha
      obtain ⟨n, rfl⟩ := hb
      obtain ⟨N, hN⟩ := hcof m n
      refine ⟨N, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, mk_mulOption, out_eq, out_eq,
        mk_optionGame_eq_hahnSum ht, mk_optionGame_eq_hahnSum hu]
      have h1 := optHi_sub_bounds ht hx m
      have h2 := sub_optLo_bounds hu hy n
      have hDpos : 0 < (optHi t m - hahnSum ht) * (hahnSum hu - optLo u n) :=
        mul_pos (pos_of_bounds h1.1) (pos_of_bounds h2.1)
      have hDmk : ArchimedeanClass.mk ((optHi t m - hahnSum ht) * (hahnSum hu - optLo u n)) <
          ArchimedeanClass.mk (c N) := by
        rw [ArchimedeanClass.mk_mul, mk_eq_of_bounds h1.1 h1.2, mk_eq_of_bounds h2.1 h2.2,
          ← ArchimedeanClass.mk_mul]
        exact hN
      have key := optHi_le_add_of_mk_lt hc hP hDpos hDmk
      have hid : optHi t m * hahnSum hu + hahnSum ht * optLo u n - optHi t m * optLo u n =
          hahnSum ht * hahnSum hu +
            (optHi t m - hahnSum ht) * (hahnSum hu - optLo u n) := by ring
      rw [hid]
      exact key

/-- **The multiplicativity theorem for canonical sums**: for strictly dominating `t, u` whose
Cauchy product `c = cauchyMul t u` is strictly dominating, satisfies the floor hypothesis of
`IsHahnSum.mul` (`mk (c n) ≤ mk (tᵢ uⱼ)` whenever `n ≤ i + j`), and is cofinal in the term
products (`∀ m n, ∃ N, mk (tₘ uₙ) < mk (c N)`), the canonical sum multiplies:
`hahnSum t * hahnSum u = hahnSum c`. -/
theorem hahnSum_mul_hahnSum_eq_hahnSum_cauchyMul {t u : ℕ → Surreal.{u}}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (hc : ∀ n, ArchimedeanClass.mk (cauchyMul t u n) <
      ArchimedeanClass.mk (cauchyMul t u (n + 1)))
    (H : ∀ n i j : ℕ, n ≤ i + j →
      ArchimedeanClass.mk (cauchyMul t u n) ≤ ArchimedeanClass.mk (t i * u j))
    (hcof : ∀ m n, ∃ N, ArchimedeanClass.mk (t m * u n) <
      ArchimedeanClass.mk (cauchyMul t u N)) :
    hahnSum ht * hahnSum hu = hahnSum hc :=
  (hahnSum_eq_mul_of_cofinal ht hu hc
    ((isHahnSum_hahnSum ht).mul (isHahnSum_hahnSum hu) H) hcof).symm

/-! ### The comparable-class exponential functional equation -/

/-- The class of an exponential-series term. -/
private theorem mk_expTerm {ε : Surreal} (k : ℕ) :
    ArchimedeanClass.mk (ε ^ k / ((k.factorial : ℕ) : Surreal)) =
      k • ArchimedeanClass.mk ε := by
  rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero, ArchimedeanClass.mk_pow]

/-- **Cofinality of the exponential series** at `σ + τ` in the products of terms at `σ` and
at `τ`, when the classes of `σ` and `τ` are comparable (`mk σ ≤ K • mk τ` and
`mk τ ≤ K • mk σ`): the term `(σ+τ)^N/N!` with `N = (m + n)(K + 1) + 1` is strictly finer
than `σ^m τ^n/(m! n!)`. -/
theorem expSeries_cofinal {σ τ : Surreal} (hσ : Infinitesimal σ) (hτ : Infinitesimal τ)
    (hσ0 : 0 < σ) (hτ0 : 0 < τ) (K : ℕ)
    (hστ : ArchimedeanClass.mk σ ≤ K • ArchimedeanClass.mk τ)
    (hτσ : ArchimedeanClass.mk τ ≤ K • ArchimedeanClass.mk σ) (m n : ℕ) :
    ∃ N, ArchimedeanClass.mk (σ ^ m / ((m.factorial : ℕ) : Surreal) *
        (τ ^ n / ((n.factorial : ℕ) : Surreal))) <
      ArchimedeanClass.mk ((σ + τ) ^ N / ((N.factorial : ℕ) : Surreal)) := by
  have hμσ : ArchimedeanClass.mk (σ + τ) ≤ ArchimedeanClass.mk σ :=
    ArchimedeanClass.mk_antitoneOn (Set.mem_Ici.2 hσ0.le)
      (Set.mem_Ici.2 (by positivity)) (by linarith)
  have hμτ : ArchimedeanClass.mk (σ + τ) ≤ ArchimedeanClass.mk τ :=
    ArchimedeanClass.mk_antitoneOn (Set.mem_Ici.2 hτ0.le)
      (Set.mem_Ici.2 (by positivity)) (by linarith)
  have hmin : min (ArchimedeanClass.mk σ) (ArchimedeanClass.mk τ) ≤
      ArchimedeanClass.mk (σ + τ) := ArchimedeanClass.min_le_mk_add σ τ
  -- both classes are bounded by `(K+1)` times the class of the sum
  have h1 : ArchimedeanClass.mk σ ≤ (K + 1) • ArchimedeanClass.mk (σ + τ) ∧
      ArchimedeanClass.mk τ ≤ (K + 1) • ArchimedeanClass.mk (σ + τ) := by
    rcases le_total (ArchimedeanClass.mk σ) (ArchimedeanClass.mk τ) with h | h
    · rw [min_eq_left h] at hmin
      rw [le_antisymm hμσ hmin]
      constructor
      · calc ArchimedeanClass.mk σ = 1 • ArchimedeanClass.mk σ := (one_nsmul _).symm
          _ ≤ (K + 1) • ArchimedeanClass.mk σ := nsmul_le_nsmul_left hσ.le (by omega)
      · exact hτσ.trans (nsmul_le_nsmul_left hσ.le (Nat.le_succ K))
    · rw [min_eq_right h] at hmin
      rw [le_antisymm hμτ hmin]
      constructor
      · exact hστ.trans (nsmul_le_nsmul_left hτ.le (Nat.le_succ K))
      · calc ArchimedeanClass.mk τ = 1 • ArchimedeanClass.mk τ := (one_nsmul _).symm
          _ ≤ (K + 1) • ArchimedeanClass.mk τ := nsmul_le_nsmul_left hτ.le (by omega)
  refine ⟨(m + n) * (K + 1) + 1, ?_⟩
  rw [ArchimedeanClass.mk_mul, mk_expTerm, mk_expTerm, mk_expTerm]
  calc m • ArchimedeanClass.mk σ + n • ArchimedeanClass.mk τ
      ≤ m • ((K + 1) • ArchimedeanClass.mk (σ + τ)) +
          n • ((K + 1) • ArchimedeanClass.mk (σ + τ)) :=
        add_le_add (nsmul_le_nsmul_right h1.1 m) (nsmul_le_nsmul_right h1.2 n)
    _ = ((m + n) * (K + 1)) • ArchimedeanClass.mk (σ + τ) := by
        rw [← mul_nsmul', ← mul_nsmul', ← add_nsmul, add_mul]
    _ < ((m + n) * (K + 1) + 1) • ArchimedeanClass.mk (σ + τ) := by
        rw [← ArchimedeanClass.mk_pow, ← ArchimedeanClass.mk_pow]
        exact mk_pow_lt_mk_pow_succ (hσ.add hτ) (by positivity) _

/-- **THE COMPARABLE-CLASS EXPONENTIAL FUNCTIONAL EQUATION**: for positive infinitesimals
`σ, τ` whose Archimedean classes are comparable — `mk σ ≤ K • mk τ` and `mk τ ≤ K • mk σ`
for some `K : ℕ`, i.e. neither is infinitely finer than every power of the other —
the canonical exponential is multiplicative: `expInf (σ + τ) = expInf σ * expInf τ`.

Proof: the product `expInf σ * expInf τ` is a Hahn sum of the exponential series at `σ + τ`
(`isHahnSum_expInf_mul`), and that series is cofinal in the products of terms
(`expSeries_cofinal`), so the product engine identifies the product with the canonical sum.
This subsumes the lattice, grid and mixed instances proved by census in
`Infinity.ExpFibre`, `Infinity.ExpLadder`, `Infinity.ExpLogGrid` and `Infinity.ExpMixedFE`. -/
theorem expInf_add_eq_mul_of_comparable {σ τ : Surreal.{u}}
    (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) (hσ0 : 0 < σ) (hτ0 : 0 < τ) (K : ℕ)
    (hστ : ArchimedeanClass.mk σ ≤ K • ArchimedeanClass.mk τ)
    (hτσ : ArchimedeanClass.mk τ ≤ K • ArchimedeanClass.mk σ) :
    expInf (σ + τ) (hσ.add hτ) (by positivity) =
      expInf σ hσ hσ0.ne' * expInf τ hτ hτ0.ne' := by
  unfold expInf
  exact hahnSum_eq_mul_of_cofinal _ _ _ (isHahnSum_expInf_mul hσ hτ hσ0 hτ0)
    (expSeries_cofinal hσ hτ hσ0 hτ0 K hστ hτσ)

/-- The equal-class case of the functional equation. -/
theorem expInf_add_eq_mul_of_mk_eq {σ τ : Surreal.{u}}
    (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) (hσ0 : 0 < σ) (hτ0 : 0 < τ)
    (h : ArchimedeanClass.mk σ = ArchimedeanClass.mk τ) :
    expInf (σ + τ) (hσ.add hτ) (by positivity) =
      expInf σ hσ hσ0.ne' * expInf τ hτ hτ0.ne' :=
  expInf_add_eq_mul_of_comparable hσ hτ hσ0 hτ0 1 (by rw [one_nsmul, h]) (by rw [one_nsmul, h])

/-- The squaring law: `expInf (σ + σ) = expInf σ * expInf σ` for every positive
infinitesimal `σ`. -/
theorem expInf_add_self_eq_mul {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : 0 < σ) :
    expInf (σ + σ) (hσ.add hσ) (by positivity) = expInf σ hσ hσ0.ne' * expInf σ hσ hσ0.ne' :=
  expInf_add_eq_mul_of_mk_eq hσ hσ hσ0 hσ0 rfl

/-- The lattice instance `expInf (2·logOmega) = expInf logOmega ^ 2` of `Infinity.ExpFibre`
(there proved by a birthday census through the monomial tube theorem), re-derived in one
line from the comparable-class functional equation. -/
theorem expInf_add_logOmega_eq_mul' :
    expInf (logOmega + logOmega : Surreal.{0})
        (logOmega_infinitesimal.add logOmega_infinitesimal)
        (add_pos logOmega_pos logOmega_pos).ne' =
      expInf logOmega logOmega_infinitesimal logOmega_pos.ne' *
        expInf logOmega logOmega_infinitesimal logOmega_pos.ne' :=
  expInf_add_self_eq_mul logOmega_infinitesimal logOmega_pos

/-! ### The sum game: additivity by cofinality -/

/-- **The sum engine**: if the sum of two canonical sums is a Hahn sum of a strictly
dominating series `c` which is cofinal in the terms of both series, then the sum *is* the
canonical sum of `c`. Proof: the identification engine on the Conway sum of the two option
games, whose options have values `x + y ∓ D` with `D > 0` of class `mk (tₘ)` or `mk (uₙ)`. -/
theorem hahnSum_eq_add_of_cofinal {t u c : ℕ → Surreal.{u}}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (hc : ∀ n, ArchimedeanClass.mk (c n) < ArchimedeanClass.mk (c (n + 1)))
    (hP : IsHahnSum c (hahnSum ht + hahnSum hu))
    (hcoft : ∀ m, ∃ N, ArchimedeanClass.mk (t m) < ArchimedeanClass.mk (c N))
    (hcofu : ∀ n, ∃ N, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (c N)) :
    hahnSum hc = hahnSum ht + hahnSum hu := by
  haveI := numeric_optionGame ht
  haveI := numeric_optionGame hu
  have hx : IsHahnSum t (hahnSum ht) := isHahnSum_hahnSum ht
  have hy : IsHahnSum u (hahnSum hu) := isHahnSum_hahnSum hu
  have hG : Surreal.mk (optionGame t + optionGame u) = hahnSum ht + hahnSum hu := by
    rw [Surreal.mk_add, mk_optionGame_eq_hahnSum ht, mk_optionGame_eq_hahnSum hu]
  rw [← hG]
  refine hahnSum_eq_of_isHahnSum_of_moves_le hc (by rwa [hG]) ?_ ?_
  · rw [forall_moves_add]
    constructor
    · intro a ha
      rw [leftMoves_optionGame] at ha
      obtain ⟨m, rfl⟩ := ha
      obtain ⟨N, hN⟩ := hcoft m
      refine ⟨N, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, mk_optionGame_eq_hahnSum hu]
      have h1 := sub_optLo_bounds ht hx m
      have hDmk : ArchimedeanClass.mk (hahnSum ht - optLo t m) < ArchimedeanClass.mk (c N) := by
        rw [mk_eq_of_bounds h1.1 h1.2]; exact hN
      have key := sub_le_optLo_of_mk_lt hc hP (pos_of_bounds h1.1) hDmk
      have hid : optLo t m + hahnSum hu =
          hahnSum ht + hahnSum hu - (hahnSum ht - optLo t m) := by ring
      rw [hid]
      exact key
    · intro b hb
      rw [leftMoves_optionGame] at hb
      obtain ⟨n, rfl⟩ := hb
      obtain ⟨N, hN⟩ := hcofu n
      refine ⟨N, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, mk_optionGame_eq_hahnSum ht]
      have h2 := sub_optLo_bounds hu hy n
      have hDmk : ArchimedeanClass.mk (hahnSum hu - optLo u n) < ArchimedeanClass.mk (c N) := by
        rw [mk_eq_of_bounds h2.1 h2.2]; exact hN
      have key := sub_le_optLo_of_mk_lt hc hP (pos_of_bounds h2.1) hDmk
      have hid : hahnSum ht + optLo u n =
          hahnSum ht + hahnSum hu - (hahnSum hu - optLo u n) := by ring
      rw [hid]
      exact key
  · rw [forall_moves_add]
    constructor
    · intro a ha
      rw [rightMoves_optionGame] at ha
      obtain ⟨m, rfl⟩ := ha
      obtain ⟨N, hN⟩ := hcoft m
      refine ⟨N, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, mk_optionGame_eq_hahnSum hu]
      have h1 := optHi_sub_bounds ht hx m
      have hDmk : ArchimedeanClass.mk (optHi t m - hahnSum ht) < ArchimedeanClass.mk (c N) := by
        rw [mk_eq_of_bounds h1.1 h1.2]; exact hN
      have key := optHi_le_add_of_mk_lt hc hP (pos_of_bounds h1.1) hDmk
      have hid : optHi t m + hahnSum hu =
          hahnSum ht + hahnSum hu + (optHi t m - hahnSum ht) := by ring
      rw [hid]
      exact key
    · intro b hb
      rw [rightMoves_optionGame] at hb
      obtain ⟨n, rfl⟩ := hb
      obtain ⟨N, hN⟩ := hcofu n
      refine ⟨N, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, mk_optionGame_eq_hahnSum ht]
      have h2 := optHi_sub_bounds hu hy n
      have hDmk : ArchimedeanClass.mk (optHi u n - hahnSum hu) < ArchimedeanClass.mk (c N) := by
        rw [mk_eq_of_bounds h2.1 h2.2]; exact hN
      have key := optHi_le_add_of_mk_lt hc hP (pos_of_bounds h2.1) hDmk
      have hid : hahnSum ht + optHi u n =
          hahnSum ht + hahnSum hu + (optHi u n - hahnSum hu) := by ring
      rw [hid]
      exact key

/-- **The additivity theorem for canonical sums**: for strictly dominating `t, u` with no
cancellation (`mk (tₙ + uₙ) ≤ min (mk tₙ) (mk uₙ)`) whose termwise sum is cofinal in both
(`∀ m, ∃ N, mk tₘ < mk (t N + u N)` and likewise for `u`), the canonical sum is additive:
`hahnSum t + hahnSum u = hahnSum (t + u)`. -/
theorem hahnSum_add_hahnSum_eq_hahnSum_add {t u : ℕ → Surreal.{u}}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (h : ∀ n, ArchimedeanClass.mk (t n + u n) ≤
      min (ArchimedeanClass.mk (t n)) (ArchimedeanClass.mk (u n)))
    (hcoft : ∀ m, ∃ N, ArchimedeanClass.mk (t m) < ArchimedeanClass.mk (t N + u N))
    (hcofu : ∀ n, ∃ N, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (t N + u N)) :
    hahnSum ht + hahnSum hu = hahnSum (strict_dominating_add ht hu h) :=
  (hahnSum_eq_add_of_cofinal ht hu (strict_dominating_add ht hu h)
    ((isHahnSum_hahnSum ht).add (isHahnSum_hahnSum hu) h) hcoft hcofu).symm

end Surreal

end
