import Infinity.GameCofinality
import Infinity.NormalForm

/-!
# The transfinite option game: additivity of the canonical sum at every ordinal length

`Infinity.GameCofinality` identified the length-`ω` canonical sum `hahnSum t` with the value
of its option game `!{sₙ − 2|tₙ| ∣ sₙ + 2|tₙ|}` and turned that into an identification
engine. This file runs the same argument at **every limit ordinal**, with the canonical
transfinite partial sums `hahnSumO t β` of `Infinity.TransfiniteSum` as anchors, and then
uses it inside a transfinite induction to prove that the canonical transfinite sum is
**additive** — the first piece of Conway's normal-form evaluation as a ring homomorphism.

* `Surreal.optionGameO t γ` — the transfinite option game
  `!{hahnSumO t β − 2|t β| ∣ hahnSumO t β + 2|t β|}_{β < γ}`;
  `Surreal.numeric_optionGameO` (numeric for strictly dominating `t` and limit `γ`).
* **The limit-stage bridge** `Surreal.mk_optionGameO_eq_hahnSumO`:
  `Surreal.mk (optionGameO t γ) = hahnSumO t γ`. The value is a Hahn sum of the length-`γ`
  prefix, and every Hahn sum fits the game (the transfinite next-index estimate
  `Surreal.abs_sub_hahnSumO_lt`: `|w − hahnSumO t β| < 2|t β|` because
  `w − hahnSumO t β = t β + (w − hahnSumO t (β+1))`), so by the simplicity theorem and the
  characterization `hahnSumO_eq_iff` the value is the birthday-minimal Hahn sum.
* **The transfinite identification engine**
  `Surreal.hahnSumO_eq_of_isHahnSumO_of_moves_le` / `_of_mk_moves_le` /
  `Surreal.hahnSumO_eq_of_isHahnSumO_of_mk_sub_lt`: a numeric game whose value is a Hahn sum
  of the length-`γ` prefix and whose options are each beaten by an option of the transfinite
  option game (equivalently: each differs from the value by a positive quantity strictly
  coarser than some later term) has the canonical sum as its value.
* **THE ADDITIVITY THEOREM** `Surreal.hahnSumO_add` / `Surreal.hahnSumO_add_eq`: for
  strictly dominating `t, u` below `α` with termwise no cancellation
  (`mk (t β + u β) ≤ min (mk (t β)) (mk (u β))`) and mutually cofinal classes below every
  limit `γ ≤ α` (`IsCofinalDom t u γ ∧ IsCofinalDom u t γ`),
  `hahnSumO (t + u) α = hahnSumO t α + hahnSumO u α`. Proof: transfinite induction on `α`;
  the successor step is algebra, and at a limit stage the engine is applied to the Conway
  sum of the two transfinite option games, whose options have values `S + U ∓ D` with
  `D > 0` of class `mk (t β)` or `mk (u β)`, which cofinality places strictly above a later
  term of `t + u`. Corollaries: `Surreal.hahnSumO_add_of_interleaved` (the classes of each
  series are within one step of the other's) and `Surreal.hahnSumO_add_of_mk_eq` (equal
  classes — the same-support case of Hahn-series addition).
* **THE BLOCK THEOREM** `Surreal.hahnSumO_omega0_add_omega0_eq_hahnSum₂`: at length
  `ω + ω`, the canonical transfinite sum equals the block-compositional
  `hahnSum₂ = hahnSum (coarse block) + hahnSum (fine block)` of `Infinity.OrdinalSum` — the
  question `Infinity.NormalForm` reduced to birthday-minimality of `hahnSum₂`
  (`hahnSumO_eq_hahnSum₂_iff`) is closed affirmatively: `hahnSum₂` **is** birthday-minimal
  (`Surreal.birthday_hahnSum₂_le_of_isHahnSum₂`). Proof: the engine at the single limit
  stage `ω + ω`, applied to the Conway sum of the two ω-length option games of
  `Infinity.GameCofinality`.
* **Hahn-series evaluation adds on a common support**
  `Surreal.evalHahn_add_of_exp_eq`: for `SurrealHahnSeries` `x, y` of the same length and
  the same exponent enumeration with no coefficient cancellation,
  `evalHahn (x + y) = evalHahn x + evalHahn y` — the first ring-homomorphism law for
  `evalHahn`, via `hahnSumO_add_of_mk_eq` and the support/exponent bookkeeping of the
  library's `SurrealHahnSeries`. (See the end of the file for the exact hypotheses.)

Everything is the sum-game argument of `Infinity.GameCofinality` transplanted to ordinal
stages; no birthday census is used anywhere.
-/

open ArchimedeanClass IGame Order

universe u

noncomputable section

namespace Surreal

variable {t : Ordinal.{u} → Surreal.{u}}

/-! ### Limit ordinals: successors stay below -/

/-- Below a limit ordinal, the successor of any smaller ordinal is still smaller. -/
theorem _root_.Order.IsSuccLimit.add_one_lt_of_ordinal {γ β : Ordinal.{u}}
    (hγ : IsSuccLimit γ) (hβ : β < γ) : β + 1 < γ := by
  rw [← succ_eq_add_one]
  exact hγ.succ_lt hβ

/-! ### The option values and the transfinite next-index estimate -/

/-- The lower option `hahnSumO t β − 2|t β|` of the transfinite summation cut. -/
def optLoO (t : Ordinal.{u} → Surreal.{u}) (β : Ordinal.{u}) : Surreal.{u} :=
  hahnSumO t β - 2 * |t β|

/-- The upper option `hahnSumO t β + 2|t β|` of the transfinite summation cut. -/
def optHiO (t : Ordinal.{u} → Surreal.{u}) (β : Ordinal.{u}) : Surreal.{u} :=
  hahnSumO t β + 2 * |t β|

/-- **The transfinite next-index estimate**: a Hahn sum `w` of the length-`γ` prefix of a
strictly dominating series satisfies the *strict* bound `|w − hahnSumO t β| < 2|t β|` at
every stage `β` with `β + 1 < γ`, because `w − hahnSumO t β = t β + (w − hahnSumO t (β+1))`
and the residual at the next stage is strictly dominated by `t β`. -/
theorem abs_sub_hahnSumO_lt {γ : Ordinal.{u}} (ht : IsStrictDom t γ) {w : Surreal.{u}}
    (hw : IsHahnSumO t γ w) {β : Ordinal.{u}} (hβ : β + 1 < γ) :
    |w - hahnSumO t β| < 2 * |t β| := by
  have h1 : ArchimedeanClass.mk (t β) < ArchimedeanClass.mk (w - hahnSumO t (β + 1)) :=
    (ht (lt_add_one_iff.2 le_rfl) hβ).trans_le (hw (β + 1) hβ)
  have h2 := abs_lt.1 (abs_lt_abs_of_mk_lt h1)
  have hs : w - hahnSumO t β = t β + (w - hahnSumO t (β + 1)) := by
    rw [hahnSumO_add_one]; ring
  rw [hs]
  have h3 := neg_abs_le (t β)
  have h4 := le_abs_self (t β)
  exact abs_lt.2 ⟨by linarith [h2.1], by linarith [h2.2]⟩

theorem optLoO_lt_of_isHahnSumO {γ : Ordinal.{u}} (ht : IsStrictDom t γ) {w : Surreal.{u}}
    (hw : IsHahnSumO t γ w) {β : Ordinal.{u}} (hβ : β + 1 < γ) : optLoO t β < w := by
  have h := (abs_lt.1 (abs_sub_hahnSumO_lt ht hw hβ)).1
  unfold optLoO
  linarith

theorem lt_optHiO_of_isHahnSumO {γ : Ordinal.{u}} (ht : IsStrictDom t γ) {w : Surreal.{u}}
    (hw : IsHahnSumO t γ w) {β : Ordinal.{u}} (hβ : β + 1 < γ) : w < optHiO t β := by
  have h := (abs_lt.1 (abs_sub_hahnSumO_lt ht hw hβ)).2
  unfold optHiO
  linarith

/-- Conversely, anything strictly between all the options of stages `< γ` is a Hahn sum of
the length-`γ` prefix. -/
theorem isHahnSumO_of_forall_opt {γ : Ordinal.{u}} {w : Surreal.{u}}
    (h : ∀ β < γ, optLoO t β < w ∧ w < optHiO t β) : IsHahnSumO t γ w := by
  intro β hβ
  obtain ⟨h1, h2⟩ := h β hβ
  unfold optLoO at h1
  unfold optHiO at h2
  rw [ArchimedeanClass.mk_le_mk]
  refine ⟨2, ?_⟩
  calc |w - hahnSumO t β| ≤ 2 * |t β| := abs_le.2 ⟨by linarith, by linarith⟩
    _ = 2 • |t β| := by rw [two_nsmul, two_mul]

/-- Below a limit ordinal, the two option sets of the transfinite summation cut are
separated. -/
theorem optLoO_lt_optHiO {γ : Ordinal.{u}} (hγ : IsSuccLimit γ) (ht : IsStrictDom t γ)
    {β δ : Ordinal.{u}} (hβ : β < γ) (hδ : δ < γ) : optLoO t β < optHiO t δ :=
  (optLoO_lt_of_isHahnSumO ht (isHahnSumO_hahnSumO ht) (hγ.add_one_lt_of_ordinal hβ)).trans
    (lt_optHiO_of_isHahnSumO ht (isHahnSumO_hahnSumO ht) (hγ.add_one_lt_of_ordinal hδ))

/-! ### The transfinite option game -/

/-- **The transfinite option game** of a series at stage `γ`: the Conway cut
`!{hahnSumO t β − 2|t β| ∣ hahnSumO t β + 2|t β|}_{β < γ}` of the limit case of the
Transfinite Summation Theorem, as an explicit `IGame` whose options are (representatives
of) the surreal option values. -/
def optionGameO (t : Ordinal.{u} → Surreal.{u}) (γ : Ordinal.{u}) : IGame.{u} :=
  !{Set.range (fun β : Set.Iio γ ↦ (optLoO t β.1).out) |
    Set.range (fun β : Set.Iio γ ↦ (optHiO t β.1).out)}

theorem leftMoves_optionGameO (t : Ordinal.{u} → Surreal.{u}) (γ : Ordinal.{u}) :
    (optionGameO t γ)ᴸ = Set.range (fun β : Set.Iio γ ↦ (optLoO t β.1).out) :=
  leftMoves_ofSets ..

theorem rightMoves_optionGameO (t : Ordinal.{u} → Surreal.{u}) (γ : Ordinal.{u}) :
    (optionGameO t γ)ᴿ = Set.range (fun β : Set.Iio γ ↦ (optHiO t β.1).out) :=
  rightMoves_ofSets ..

theorem optLoO_out_mem_leftMoves_optionGameO (t : Ordinal.{u} → Surreal.{u})
    {γ β : Ordinal.{u}} (hβ : β < γ) : (optLoO t β).out ∈ (optionGameO t γ)ᴸ := by
  rw [leftMoves_optionGameO]
  exact ⟨⟨β, hβ⟩, rfl⟩

theorem optHiO_out_mem_rightMoves_optionGameO (t : Ordinal.{u} → Surreal.{u})
    {γ β : Ordinal.{u}} (hβ : β < γ) : (optHiO t β).out ∈ (optionGameO t γ)ᴿ := by
  rw [rightMoves_optionGameO]
  exact ⟨⟨β, hβ⟩, rfl⟩

/-- The transfinite option game of a strictly dominating series at a limit stage is
numeric. -/
theorem numeric_optionGameO {γ : Ordinal.{u}} (hγ : IsSuccLimit γ) (ht : IsStrictDom t γ) :
    (optionGameO t γ).Numeric := by
  refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
  · rw [leftMoves_optionGameO] at hy
    rw [rightMoves_optionGameO] at hz
    obtain ⟨⟨β, hβ⟩, rfl⟩ := hy
    obtain ⟨⟨δ, hδ⟩, rfl⟩ := hz
    rw [← Surreal.mk_lt_mk, out_eq, out_eq]
    exact optLoO_lt_optHiO hγ ht hβ hδ
  · cases p with
    | left =>
      rw [optionGameO, moves_ofSets] at hy
      obtain ⟨β, rfl⟩ := hy
      infer_instance
    | right =>
      rw [optionGameO, moves_ofSets] at hy
      obtain ⟨β, rfl⟩ := hy
      infer_instance

/-! ### The limit-stage bridge -/

/-- The value of the transfinite option game is a Hahn sum of the length-`γ` prefix: it
lies strictly between all its options. -/
theorem isHahnSumO_mk_optionGameO {γ : Ordinal.{u}} (hγ : IsSuccLimit γ)
    (ht : IsStrictDom t γ) :
    IsHahnSumO t γ (@Surreal.mk (optionGameO t γ) (numeric_optionGameO hγ ht)) := by
  haveI := numeric_optionGameO hγ ht
  refine isHahnSumO_of_forall_opt fun β hβ ↦ ⟨?_, ?_⟩
  · have h := Surreal.mk_lt_mk.2
      (IGame.Numeric.left_lt (optLoO_out_mem_leftMoves_optionGameO t hβ))
    rwa [out_eq] at h
  · have h := Surreal.mk_lt_mk.2
      (IGame.Numeric.lt_right (optHiO_out_mem_rightMoves_optionGameO t hβ))
    rwa [out_eq] at h

/-- Every numeric game whose value is a Hahn sum of the length-`γ` prefix fits the
transfinite option game (the next-index estimate in game clothing). -/
theorem fits_optionGameO_of_isHahnSumO {γ : Ordinal.{u}} (hγ : IsSuccLimit γ)
    (ht : IsStrictDom t γ) {w : Surreal.{u}} (hw : IsHahnSumO t γ w) {x : IGame.{u}}
    [x.Numeric] (hx : Surreal.mk x = w) : x.Fits (optionGameO t γ) := by
  constructor
  · intro z hz
    rw [leftMoves_optionGameO] at hz
    obtain ⟨⟨β, hβ⟩, rfl⟩ := hz
    refine IGame.Numeric.not_le.2 ?_
    rw [← Surreal.mk_lt_mk, out_eq, hx]
    exact optLoO_lt_of_isHahnSumO ht hw (hγ.add_one_lt_of_ordinal hβ)
  · intro z hz
    rw [rightMoves_optionGameO] at hz
    obtain ⟨⟨β, hβ⟩, rfl⟩ := hz
    refine IGame.Numeric.not_le.2 ?_
    rw [← Surreal.mk_lt_mk, out_eq, hx]
    exact lt_optHiO_of_isHahnSumO ht hw (hγ.add_one_lt_of_ordinal hβ)

/-- Conversely, the value of any numeric game fitting the transfinite option game is a
Hahn sum of the length-`γ` prefix. -/
theorem isHahnSumO_of_fits_optionGameO {γ : Ordinal.{u}} {x : IGame.{u}} [x.Numeric]
    (hx : x.Fits (optionGameO t γ)) : IsHahnSumO t γ (Surreal.mk x) := by
  refine isHahnSumO_of_forall_opt fun β hβ ↦ ⟨?_, ?_⟩
  · have h := Surreal.mk_lt_mk.2
      (IGame.Numeric.not_le.1 (hx.1 _ (optLoO_out_mem_leftMoves_optionGameO t hβ)))
    rwa [out_eq] at h
  · have h := Surreal.mk_lt_mk.2
      (IGame.Numeric.not_le.1 (hx.2 _ (optHiO_out_mem_rightMoves_optionGameO t hβ)))
    rwa [out_eq] at h

/-- **The transfinite fits characterization**: a numeric game fits the transfinite option
game at a limit stage `γ` iff its value is a Hahn sum of the length-`γ` prefix. -/
theorem fits_optionGameO_iff {γ : Ordinal.{u}} (hγ : IsSuccLimit γ) (ht : IsStrictDom t γ)
    {x : IGame.{u}} [x.Numeric] :
    x.Fits (optionGameO t γ) ↔ IsHahnSumO t γ (Surreal.mk x) :=
  ⟨isHahnSumO_of_fits_optionGameO, fun h ↦ fits_optionGameO_of_isHahnSumO hγ ht h rfl⟩

/-- **The limit-stage bridge**: at every limit ordinal `γ`, the value of the transfinite
option game `!{hahnSumO t β − 2|t β| ∣ hahnSumO t β + 2|t β|}_{β<γ}` is the canonical
transfinite sum `hahnSumO t γ`. Its value is a Hahn sum of the prefix, and every Hahn sum
fits it, so by the simplicity theorem its value is the birthday-minimal Hahn sum — which
is `hahnSumO t γ` by `hahnSumO_eq_iff`. -/
theorem mk_optionGameO_eq_hahnSumO {γ : Ordinal.{u}} (hγ : IsSuccLimit γ)
    (ht : IsStrictDom t γ) :
    @Surreal.mk (optionGameO t γ) (numeric_optionGameO hγ ht) = hahnSumO t γ := by
  haveI := numeric_optionGameO hγ ht
  symm
  rw [hahnSumO_eq_iff hγ (ht.ne_zero_of_isSuccLimit hγ) ⟨_, isHahnSumO_hahnSumO ht⟩]
  refine ⟨isHahnSumO_mk_optionGameO hγ ht, fun w hw ↦ ?_⟩
  exact birthday_mk_le_of_fits (fits_optionGameO_of_isHahnSumO hγ ht hw (out_eq w))

/-- The birthday of the canonical transfinite sum is bounded by the birthday of the
transfinite option game. -/
theorem birthday_hahnSumO_le_birthday_optionGameO {γ : Ordinal.{u}} (hγ : IsSuccLimit γ)
    (ht : IsStrictDom t γ) :
    (hahnSumO t γ).birthday ≤ (optionGameO t γ).birthday := by
  haveI := numeric_optionGameO hγ ht
  rw [← mk_optionGameO_eq_hahnSumO hγ ht]
  exact birthday_mk_le _

/-! ### The transfinite identification engine -/

/-- **The transfinite identification engine**: to identify the canonical sum at a limit
stage `γ` with the value of a numeric game `G`, it suffices that the value be a Hahn sum
of the length-`γ` prefix and that every option of `G` be beaten by an option of the
transfinite option game. -/
theorem hahnSumO_eq_of_isHahnSumO_of_moves_le {γ : Ordinal.{u}} (hγ : IsSuccLimit γ)
    (ht : IsStrictDom t γ) {G : IGame.{u}} [G.Numeric] (hG : IsHahnSumO t γ (Surreal.mk G))
    (hl : ∀ a ∈ Gᴸ, ∃ β < γ, a ≤ (optLoO t β).out)
    (hr : ∀ b ∈ Gᴿ, ∃ β < γ, (optHiO t β).out ≤ b) :
    hahnSumO t γ = Surreal.mk G := by
  haveI := numeric_optionGameO hγ ht
  have hfit : G.Fits (optionGameO t γ) := fits_optionGameO_of_isHahnSumO hγ ht hG rfl
  have hequiv : G ≈ optionGameO t γ := by
    refine hfit.equiv_of_forall_moves ?_ ?_
    · intro a ha
      obtain ⟨β, hβ, h⟩ := hl a ha
      exact ⟨(optLoO t β).out, optLoO_out_mem_leftMoves_optionGameO t hβ, h⟩
    · intro b hb
      obtain ⟨β, hβ, h⟩ := hr b hb
      exact ⟨(optHiO t β).out, optHiO_out_mem_rightMoves_optionGameO t hβ, h⟩
  rw [← mk_optionGameO_eq_hahnSumO hγ ht]
  exact (Surreal.mk_eq hequiv).symm

/-- The transfinite identification engine with the option comparisons stated at the level
of surreal values. -/
theorem hahnSumO_eq_of_isHahnSumO_of_mk_moves_le {γ : Ordinal.{u}} (hγ : IsSuccLimit γ)
    (ht : IsStrictDom t γ) {G : IGame.{u}} [G.Numeric] (hG : IsHahnSumO t γ (Surreal.mk G))
    (hl : ∀ a (ha : a ∈ Gᴸ), ∃ β < γ,
      @Surreal.mk a (IGame.Numeric.of_mem_moves ha) ≤ optLoO t β)
    (hr : ∀ b (hb : b ∈ Gᴿ), ∃ β < γ,
      optHiO t β ≤ @Surreal.mk b (IGame.Numeric.of_mem_moves hb)) :
    hahnSumO t γ = Surreal.mk G := by
  refine hahnSumO_eq_of_isHahnSumO_of_moves_le hγ ht hG ?_ ?_
  · intro a ha
    obtain ⟨β, hβ, h⟩ := hl a ha
    haveI := IGame.Numeric.of_mem_moves ha
    refine ⟨β, hβ, ?_⟩
    rw [← Surreal.mk_le_mk, out_eq]
    exact h
  · intro b hb
    obtain ⟨β, hβ, h⟩ := hr b hb
    haveI := IGame.Numeric.of_mem_moves hb
    refine ⟨β, hβ, ?_⟩
    rw [← Surreal.mk_le_mk, out_eq]
    exact h

/-! ### Option estimates at ordinal stages -/

private theorem four_nsmul_eq' (a : Surreal) : (4 : ℕ) • |a| = 4 * |a| := by
  rw [nsmul_eq_mul]; norm_num

private theorem pos_of_bounds' {a v : Surreal} (h1 : |a| < 2 * v) : 0 < v := by
  have := abs_nonneg a
  linarith

/-- A Hahn sum of the length-`γ` prefix sits a definite multiple of `|t β|` above the lower
option `hahnSumO t β − 2|t β|`, for every `β` with `β + 1 < γ`. -/
theorem sub_optLoO_bounds {γ : Ordinal.{u}} (ht : IsStrictDom t γ) {x : Surreal.{u}}
    (hx : IsHahnSumO t γ x) {β : Ordinal.{u}} (hβ : β + 1 < γ) :
    |t β| < 2 * (x - optLoO t β) ∧ x - optLoO t β < 4 * |t β| := by
  have h1 : ArchimedeanClass.mk (t β) < ArchimedeanClass.mk (x - hahnSumO t (β + 1)) :=
    (ht (lt_add_one_iff.2 le_rfl) hβ).trans_le (hx (β + 1) hβ)
  have h2 := (ArchimedeanClass.mk_lt_mk.1 h1) 2
  rw [two_nsmul] at h2
  have hs : x - optLoO t β = t β + 2 * |t β| + (x - hahnSumO t (β + 1)) := by
    unfold optLoO; rw [hahnSumO_add_one]; ring
  rw [hs]
  have h3 := neg_abs_le (t β)
  have h4 := le_abs_self (t β)
  have h5 := neg_abs_le (x - hahnSumO t (β + 1))
  have h6 := le_abs_self (x - hahnSumO t (β + 1))
  have h7 := abs_nonneg (t β)
  constructor <;> linarith

/-- A Hahn sum of the length-`γ` prefix sits a definite multiple of `|t β|` below the upper
option `hahnSumO t β + 2|t β|`. -/
theorem optHiO_sub_bounds {γ : Ordinal.{u}} (ht : IsStrictDom t γ) {x : Surreal.{u}}
    (hx : IsHahnSumO t γ x) {β : Ordinal.{u}} (hβ : β + 1 < γ) :
    |t β| < 2 * (optHiO t β - x) ∧ optHiO t β - x < 4 * |t β| := by
  have h1 : ArchimedeanClass.mk (t β) < ArchimedeanClass.mk (x - hahnSumO t (β + 1)) :=
    (ht (lt_add_one_iff.2 le_rfl) hβ).trans_le (hx (β + 1) hβ)
  have h2 := (ArchimedeanClass.mk_lt_mk.1 h1) 2
  rw [two_nsmul] at h2
  have hs : optHiO t β - x = 2 * |t β| - t β - (x - hahnSumO t (β + 1)) := by
    unfold optHiO; rw [hahnSumO_add_one]; ring
  rw [hs]
  have h3 := neg_abs_le (t β)
  have h4 := le_abs_self (t β)
  have h5 := neg_abs_le (x - hahnSumO t (β + 1))
  have h6 := le_abs_self (x - hahnSumO t (β + 1))
  have h7 := abs_nonneg (t β)
  constructor <;> linarith

/-- The residual of a Hahn sum against the lower option at stage `β` is positive of class
exactly `mk (t β)`. -/
theorem sub_optLoO_pos_mk_eq {γ : Ordinal.{u}} (ht : IsStrictDom t γ) {x : Surreal.{u}}
    (hx : IsHahnSumO t γ x) {β : Ordinal.{u}} (hβ : β + 1 < γ) :
    0 < x - optLoO t β ∧
      ArchimedeanClass.mk (x - optLoO t β) = ArchimedeanClass.mk (t β) :=
  ⟨pos_of_bounds' (sub_optLoO_bounds ht hx hβ).1,
    mk_eq_of_bounds (sub_optLoO_bounds ht hx hβ).1 (sub_optLoO_bounds ht hx hβ).2⟩

/-- The residual of the upper option at stage `β` against a Hahn sum is positive of class
exactly `mk (t β)`. -/
theorem optHiO_sub_pos_mk_eq {γ : Ordinal.{u}} (ht : IsStrictDom t γ) {x : Surreal.{u}}
    (hx : IsHahnSumO t γ x) {β : Ordinal.{u}} (hβ : β + 1 < γ) :
    0 < optHiO t β - x ∧
      ArchimedeanClass.mk (optHiO t β - x) = ArchimedeanClass.mk (t β) :=
  ⟨pos_of_bounds' (optHiO_sub_bounds ht hx hβ).1,
    mk_eq_of_bounds (optHiO_sub_bounds ht hx hβ).1 (optHiO_sub_bounds ht hx hβ).2⟩

/-- **The option estimate, lower side**: if `P` is a Hahn sum of the length-`γ` prefix and
`D > 0` is of strictly coarser class than `t β` (with `β + 1 < γ`), then `P − D` lies below
the lower option `optLoO t β`. -/
theorem sub_le_optLoO_of_mk_lt {γ : Ordinal.{u}} (ht : IsStrictDom t γ) {P : Surreal.{u}}
    (hP : IsHahnSumO t γ P) {D : Surreal.{u}} (hD : 0 < D) {β : Ordinal.{u}}
    (hβ : β + 1 < γ) (hDβ : ArchimedeanClass.mk D < ArchimedeanClass.mk (t β)) :
    P - D ≤ optLoO t β := by
  have h1 := abs_lt.1 (abs_sub_hahnSumO_lt ht hP hβ)
  have h2 := (ArchimedeanClass.mk_lt_mk.1 hDβ) 4
  rw [abs_of_pos hD, four_nsmul_eq'] at h2
  unfold optLoO
  linarith [h1.2]

/-- **The option estimate, upper side**. -/
theorem optHiO_le_add_of_mk_lt {γ : Ordinal.{u}} (ht : IsStrictDom t γ) {P : Surreal.{u}}
    (hP : IsHahnSumO t γ P) {D : Surreal.{u}} (hD : 0 < D) {β : Ordinal.{u}}
    (hβ : β + 1 < γ) (hDβ : ArchimedeanClass.mk D < ArchimedeanClass.mk (t β)) :
    optHiO t β ≤ P + D := by
  have h1 := abs_lt.1 (abs_sub_hahnSumO_lt ht hP hβ)
  have h2 := (ArchimedeanClass.mk_lt_mk.1 hDβ) 4
  rw [abs_of_pos hD, four_nsmul_eq'] at h2
  unfold optHiO
  linarith [h1.1]

/-- **The transfinite identification engine, class form**: a numeric game whose value is a
Hahn sum of the length-`γ` prefix, and each of whose options differs from that value by a
positive quantity strictly coarser than some term `t β` (`β < γ`), has the canonical sum as
its value. -/
theorem hahnSumO_eq_of_isHahnSumO_of_mk_sub_lt {γ : Ordinal.{u}} (hγ : IsSuccLimit γ)
    (ht : IsStrictDom t γ) {G : IGame.{u}} [G.Numeric] (hG : IsHahnSumO t γ (Surreal.mk G))
    (hl : ∀ a (ha : a ∈ Gᴸ), ∃ β < γ,
      0 < Surreal.mk G - @Surreal.mk a (IGame.Numeric.of_mem_moves ha) ∧
        ArchimedeanClass.mk (Surreal.mk G - @Surreal.mk a (IGame.Numeric.of_mem_moves ha)) <
          ArchimedeanClass.mk (t β))
    (hr : ∀ b (hb : b ∈ Gᴿ), ∃ β < γ,
      0 < @Surreal.mk b (IGame.Numeric.of_mem_moves hb) - Surreal.mk G ∧
        ArchimedeanClass.mk (@Surreal.mk b (IGame.Numeric.of_mem_moves hb) - Surreal.mk G) <
          ArchimedeanClass.mk (t β)) :
    hahnSumO t γ = Surreal.mk G := by
  refine hahnSumO_eq_of_isHahnSumO_of_mk_moves_le hγ ht hG ?_ ?_
  · intro a ha
    obtain ⟨β, hβ, hpos, hmk⟩ := hl a ha
    refine ⟨β, hβ, ?_⟩
    have key := sub_le_optLoO_of_mk_lt ht hG hpos (hγ.add_one_lt_of_ordinal hβ) hmk
    rwa [sub_sub_cancel] at key
  · intro b hb
    obtain ⟨β, hβ, hpos, hmk⟩ := hr b hb
    refine ⟨β, hβ, ?_⟩
    have key := optHiO_le_add_of_mk_lt ht hG hpos (hγ.add_one_lt_of_ordinal hβ) hmk
    rwa [add_sub_cancel] at key

/-! ### Termwise sums of strictly dominating series -/

variable {u : Ordinal.{u} → Surreal.{u}}

/-- Under termwise no cancellation, the class of a termwise sum is the minimum of the
classes. -/
theorem mk_add_eq_min_of_le {β : Ordinal.{u}}
    (h : ArchimedeanClass.mk (t β + u β) ≤
      min (ArchimedeanClass.mk (t β)) (ArchimedeanClass.mk (u β))) :
    ArchimedeanClass.mk (t β + u β) =
      min (ArchimedeanClass.mk (t β)) (ArchimedeanClass.mk (u β)) :=
  le_antisymm h (ArchimedeanClass.min_le_mk_add ..)

/-- Classes of a strictly dominating series are monotone below the bound. -/
theorem IsStrictDom.mk_le_of_le {α β δ : Ordinal.{u}} (ht : IsStrictDom t α) (hβδ : β ≤ δ)
    (hδ : δ < α) : ArchimedeanClass.mk (t β) ≤ ArchimedeanClass.mk (t δ) := by
  rcases hβδ.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (ht h hδ).le

/-- Termwise no cancellation preserves strict domination. -/
theorem IsStrictDom.add {α : Ordinal.{u}} (ht : IsStrictDom t α) (hu : IsStrictDom u α)
    (h : ∀ β < α, ArchimedeanClass.mk (t β + u β) ≤
      min (ArchimedeanClass.mk (t β)) (ArchimedeanClass.mk (u β))) :
    IsStrictDom (fun β ↦ t β + u β) α := by
  intro β δ hβδ hδ
  dsimp only
  rw [mk_add_eq_min_of_le (h β (hβδ.trans hδ)), mk_add_eq_min_of_le (h δ hδ)]
  exact min_lt_min (ht hβδ hδ) (hu hβδ hδ)

/-- **Hahn sums add** at ordinal length, given termwise no cancellation and agreement of
the canonical partial sums of the termwise sum with the sums of the partial sums at every
earlier stage (which the additivity theorem supplies inductively). -/
theorem isHahnSumO_add_of_forall_eq {γ : Ordinal.{u}} {x y : Surreal.{u}}
    (hx : IsHahnSumO t γ x) (hy : IsHahnSumO u γ y)
    (h : ∀ β < γ, ArchimedeanClass.mk (t β + u β) ≤
      min (ArchimedeanClass.mk (t β)) (ArchimedeanClass.mk (u β)))
    (hV : ∀ β < γ, hahnSumO (fun β ↦ t β + u β) β = hahnSumO t β + hahnSumO u β) :
    IsHahnSumO (fun β ↦ t β + u β) γ (x + y) := by
  intro β hβ
  have hsplit : x + y - hahnSumO (fun β ↦ t β + u β) β =
      (x - hahnSumO t β) + (y - hahnSumO u β) := by
    rw [hV β hβ]; ring
  show ArchimedeanClass.mk (t β + u β) ≤ _
  rw [hsplit]
  exact le_trans (h β hβ) (le_trans (min_le_min (hx β hβ) (hy β hβ))
    (ArchimedeanClass.min_le_mk_add ..))

/-! ### Cofinality of classes -/

/-- The classes of `u` are **cofinal** in the classes of `t` below `γ`: every term of `t`
below `γ` is strictly coarser than some term of `u` below `γ`. This is what a term of `t`
needs in order to be beaten by a later term of `t + u` at a limit stage — without it the
canonical sum of `t + u` can be blind to `t` (cf. `expInf_add_eq_of_forall_nsmul_lt` in
`Infinity.ExpDichotomy`). -/
def IsCofinalDom (t u : Ordinal.{u} → Surreal.{u}) (γ : Ordinal.{u}) : Prop :=
  ∀ β < γ, ∃ β' < γ, ArchimedeanClass.mk (t β) < ArchimedeanClass.mk (u β')

/-- Below a limit ordinal, cofinality of `u` in `t` produces, for every stage `β`, a later
stage `β'` (with `β' + 1 < γ`) at which the termwise sum `t + u` is strictly finer than
`t β`. -/
theorem IsCofinalDom.exists_mk_add_lt {γ : Ordinal.{u}} (hγ : IsSuccLimit γ)
    (ht : IsStrictDom t γ) (hu : IsStrictDom u γ)
    (h : ∀ β < γ, ArchimedeanClass.mk (t β + u β) ≤
      min (ArchimedeanClass.mk (t β)) (ArchimedeanClass.mk (u β)))
    (hcof : IsCofinalDom t u γ) {β : Ordinal.{u}} (hβ : β < γ) :
    ∃ β', β' + 1 < γ ∧ ArchimedeanClass.mk (t β) < ArchimedeanClass.mk (t β' + u β') := by
  obtain ⟨β₁, hβ₁, hlt⟩ := hcof β hβ
  refine ⟨max β₁ (β + 1), ?_, ?_⟩
  · exact hγ.add_one_lt_of_ordinal (max_lt hβ₁ (hγ.add_one_lt_of_ordinal hβ))
  · have hmax : max β₁ (β + 1) < γ := max_lt hβ₁ (hγ.add_one_lt_of_ordinal hβ)
    rw [mk_add_eq_min_of_le (h _ hmax)]
    refine lt_min ?_ ?_
    · exact ht ((lt_add_one_iff.2 le_rfl).trans_le (le_max_right _ _)) hmax
    · exact hlt.trans_le (hu.mk_le_of_le (le_max_left _ _) hmax)

/-! ### THE ADDITIVITY THEOREM -/

private theorem hahnSumO_add_aux (t u : Ordinal.{u} → Surreal.{u}) (α : Ordinal.{u}) :
    IsStrictDom t α → IsStrictDom u α →
    (∀ β < α, ArchimedeanClass.mk (t β + u β) ≤
      min (ArchimedeanClass.mk (t β)) (ArchimedeanClass.mk (u β))) →
    (∀ γ ≤ α, IsSuccLimit γ → IsCofinalDom t u γ ∧ IsCofinalDom u t γ) →
    hahnSumO (fun β ↦ t β + u β) α = hahnSumO t α + hahnSumO u α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro _ _ _ _
    rw [hahnSumO_zero, hahnSumO_zero, hahnSumO_zero, add_zero]
  | add_one δ ih =>
    intro ht hu h hcof
    have hδ : δ < δ + 1 := lt_add_one_iff.2 le_rfl
    rw [hahnSumO_add_one, hahnSumO_add_one, hahnSumO_add_one,
      ih (ht.mono hδ.le) (hu.mono hδ.le) (fun β hβ ↦ h β (hβ.trans hδ))
        (fun γ hγ ↦ hcof γ (hγ.trans hδ.le))]
    ring
  | limit γ hγ ih =>
    intro ht hu h hcof
    obtain ⟨hcoftu, hcofut⟩ := hcof γ le_rfl hγ
    have hV : ∀ β < γ, hahnSumO (fun β ↦ t β + u β) β = hahnSumO t β + hahnSumO u β :=
      fun β hβ ↦ ih β hβ (ht.mono hβ.le) (hu.mono hβ.le) (fun δ hδ ↦ h δ (hδ.trans hβ))
        (fun δ hδ ↦ hcof δ (hδ.trans hβ.le))
    have htu : IsStrictDom (fun β ↦ t β + u β) γ := ht.add hu h
    haveI := numeric_optionGameO hγ ht
    haveI := numeric_optionGameO hγ hu
    have hS : IsHahnSumO t γ (hahnSumO t γ) := isHahnSumO_hahnSumO ht
    have hU : IsHahnSumO u γ (hahnSumO u γ) := isHahnSumO_hahnSumO hu
    have hP : IsHahnSumO (fun β ↦ t β + u β) γ (hahnSumO t γ + hahnSumO u γ) :=
      isHahnSumO_add_of_forall_eq hS hU h hV
    have hG : Surreal.mk (optionGameO t γ + optionGameO u γ) =
        hahnSumO t γ + hahnSumO u γ := by
      rw [Surreal.mk_add, mk_optionGameO_eq_hahnSumO hγ ht, mk_optionGameO_eq_hahnSumO hγ hu]
    rw [← hG]
    refine hahnSumO_eq_of_isHahnSumO_of_moves_le hγ htu (by rwa [hG]) ?_ ?_
    · rw [forall_moves_add]
      constructor
      · intro a ha
        rw [leftMoves_optionGameO] at ha
        obtain ⟨⟨β, hβ⟩, rfl⟩ := ha
        obtain ⟨β', hβ', hlt⟩ := hcoftu.exists_mk_add_lt hγ ht hu h hβ
        refine ⟨β', (lt_add_one_iff.2 le_rfl).trans hβ', ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq,
          mk_optionGameO_eq_hahnSumO hγ hu]
        obtain ⟨hDpos, hDmk⟩ := sub_optLoO_pos_mk_eq ht hS (hγ.add_one_lt_of_ordinal hβ)
        have key := sub_le_optLoO_of_mk_lt htu hP hDpos hβ' (by rw [hDmk]; exact hlt)
        have hid : optLoO t β + hahnSumO u γ =
            hahnSumO t γ + hahnSumO u γ - (hahnSumO t γ - optLoO t β) := by ring
        rw [hid]
        exact key
      · intro b hb
        rw [leftMoves_optionGameO] at hb
        obtain ⟨⟨β, hβ⟩, rfl⟩ := hb
        obtain ⟨β', hβ', hlt⟩ := hcofut.exists_mk_add_lt hγ hu ht
          (fun δ hδ ↦ by rw [add_comm, min_comm]; exact h δ hδ) hβ
        refine ⟨β', (lt_add_one_iff.2 le_rfl).trans hβ', ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq,
          mk_optionGameO_eq_hahnSumO hγ ht]
        obtain ⟨hDpos, hDmk⟩ := sub_optLoO_pos_mk_eq hu hU (hγ.add_one_lt_of_ordinal hβ)
        have hlt' : ArchimedeanClass.mk (hahnSumO u γ - optLoO u β) <
            ArchimedeanClass.mk (t β' + u β') := by
          rw [hDmk, add_comm]; exact hlt
        have key := sub_le_optLoO_of_mk_lt htu hP hDpos hβ' hlt'
        have hid : hahnSumO t γ + optLoO u β =
            hahnSumO t γ + hahnSumO u γ - (hahnSumO u γ - optLoO u β) := by ring
        rw [hid]
        exact key
    · rw [forall_moves_add]
      constructor
      · intro a ha
        rw [rightMoves_optionGameO] at ha
        obtain ⟨⟨β, hβ⟩, rfl⟩ := ha
        obtain ⟨β', hβ', hlt⟩ := hcoftu.exists_mk_add_lt hγ ht hu h hβ
        refine ⟨β', (lt_add_one_iff.2 le_rfl).trans hβ', ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq,
          mk_optionGameO_eq_hahnSumO hγ hu]
        obtain ⟨hDpos, hDmk⟩ := optHiO_sub_pos_mk_eq ht hS (hγ.add_one_lt_of_ordinal hβ)
        have key := optHiO_le_add_of_mk_lt htu hP hDpos hβ' (by rw [hDmk]; exact hlt)
        have hid : optHiO t β + hahnSumO u γ =
            hahnSumO t γ + hahnSumO u γ + (optHiO t β - hahnSumO t γ) := by ring
        rw [hid]
        exact key
      · intro b hb
        rw [rightMoves_optionGameO] at hb
        obtain ⟨⟨β, hβ⟩, rfl⟩ := hb
        obtain ⟨β', hβ', hlt⟩ := hcofut.exists_mk_add_lt hγ hu ht
          (fun δ hδ ↦ by rw [add_comm, min_comm]; exact h δ hδ) hβ
        refine ⟨β', (lt_add_one_iff.2 le_rfl).trans hβ', ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq,
          mk_optionGameO_eq_hahnSumO hγ ht]
        obtain ⟨hDpos, hDmk⟩ := optHiO_sub_pos_mk_eq hu hU (hγ.add_one_lt_of_ordinal hβ)
        have hlt' : ArchimedeanClass.mk (optHiO u β - hahnSumO u γ) <
            ArchimedeanClass.mk (t β' + u β') := by
          rw [hDmk, add_comm]; exact hlt
        have key := optHiO_le_add_of_mk_lt htu hP hDpos hβ' hlt'
        have hid : hahnSumO t γ + optHiO u β =
            hahnSumO t γ + hahnSumO u γ + (optHiO u β - hahnSumO u γ) := by ring
        rw [hid]
        exact key

/-- **THE ADDITIVITY THEOREM FOR THE CANONICAL TRANSFINITE SUM**: for strictly dominating
`t, u` below `α` with termwise no cancellation (`mk (t β + u β) ≤ min (mk (t β)) (mk (u β))`)
whose classes are mutually cofinal below every limit ordinal `γ ≤ α`, the canonical
transfinite sum is additive at every ordinal length:
`hahnSumO (t + u) α = hahnSumO t α + hahnSumO u α`.

Proof: transfinite induction on `α`. Zero and successor stages are algebra. At a limit
stage the transfinite identification engine is applied to the Conway sum of the two
transfinite option games: its value is `hahnSumO t γ + hahnSumO u γ`, which is a Hahn sum
of `t + u` by the induction hypothesis (the anchors agree at every earlier stage), and each
of its options differs from the value by a positive quantity of class `mk (t β)` or
`mk (u β)`, which cofinality places strictly above a later term of `t + u`. -/
theorem hahnSumO_add {α : Ordinal.{u}} (ht : IsStrictDom t α) (hu : IsStrictDom u α)
    (h : ∀ β < α, ArchimedeanClass.mk (t β + u β) ≤
      min (ArchimedeanClass.mk (t β)) (ArchimedeanClass.mk (u β)))
    (hcof : ∀ γ ≤ α, IsSuccLimit γ → IsCofinalDom t u γ ∧ IsCofinalDom u t γ) :
    hahnSumO (fun β ↦ t β + u β) α = hahnSumO t α + hahnSumO u α :=
  hahnSumO_add_aux t u α ht hu h hcof

/-- The additivity theorem for the pointwise sum `t + u` of the series. -/
theorem hahnSumO_add_eq {α : Ordinal.{u}} (ht : IsStrictDom t α) (hu : IsStrictDom u α)
    (h : ∀ β < α, ArchimedeanClass.mk (t β + u β) ≤
      min (ArchimedeanClass.mk (t β)) (ArchimedeanClass.mk (u β)))
    (hcof : ∀ γ ≤ α, IsSuccLimit γ → IsCofinalDom t u γ ∧ IsCofinalDom u t γ) :
    hahnSumO (t + u) α = hahnSumO t α + hahnSumO u α :=
  hahnSumO_add ht hu h hcof

/-- **Additivity for interleaved series**: if each term of either series is strictly
coarser than the *next* term of the other (`mk (t β) < mk (u (β+1))` and
`mk (u β) < mk (t (β+1))` whenever `β + 1 < α`), cofinality holds below every limit, and
the canonical sum is additive. -/
theorem hahnSumO_add_of_interleaved {α : Ordinal.{u}} (ht : IsStrictDom t α)
    (hu : IsStrictDom u α)
    (h : ∀ β < α, ArchimedeanClass.mk (t β + u β) ≤
      min (ArchimedeanClass.mk (t β)) (ArchimedeanClass.mk (u β)))
    (hint : ∀ β, β + 1 < α →
      ArchimedeanClass.mk (t β) < ArchimedeanClass.mk (u (β + 1)) ∧
        ArchimedeanClass.mk (u β) < ArchimedeanClass.mk (t (β + 1))) :
    hahnSumO (fun β ↦ t β + u β) α = hahnSumO t α + hahnSumO u α := by
  refine hahnSumO_add ht hu h fun γ hγα hγ ↦ ⟨fun β hβ ↦ ?_, fun β hβ ↦ ?_⟩
  · exact ⟨β + 1, hγ.add_one_lt_of_ordinal hβ,
      (hint β ((hγ.add_one_lt_of_ordinal hβ).trans_le hγα)).1⟩
  · exact ⟨β + 1, hγ.add_one_lt_of_ordinal hβ,
      (hint β ((hγ.add_one_lt_of_ordinal hβ).trans_le hγα)).2⟩

/-- **Additivity for series of equal classes** (the same-support case of Hahn-series
addition): if `mk (t β) = mk (u β)` for all `β < α` and no term cancels
(`mk (t β + u β) ≤ mk (t β)`), then `hahnSumO (t + u) α = hahnSumO t α + hahnSumO u α`. -/
theorem hahnSumO_add_of_mk_eq {α : Ordinal.{u}} (ht : IsStrictDom t α) (hu : IsStrictDom u α)
    (heq : ∀ β < α, ArchimedeanClass.mk (t β) = ArchimedeanClass.mk (u β))
    (h : ∀ β < α, ArchimedeanClass.mk (t β + u β) ≤ ArchimedeanClass.mk (t β)) :
    hahnSumO (fun β ↦ t β + u β) α = hahnSumO t α + hahnSumO u α := by
  refine hahnSumO_add_of_interleaved ht hu (fun β hβ ↦ ?_) (fun β hβ ↦ ?_)
  · rw [← heq β hβ, min_self]
    exact h β hβ
  · have hβ' : β < α := (lt_add_one_iff.2 le_rfl).trans hβ
    constructor
    · rw [heq β hβ']
      exact hu (lt_add_one_iff.2 le_rfl) hβ
    · rw [← heq β hβ']
      exact ht (lt_add_one_iff.2 le_rfl) hβ

/-! ### THE BLOCK THEOREM: length `ω + ω` -/

section Block

private theorem isSuccLimit_omega0_add_omega0' :
    IsSuccLimit (Ordinal.omega0 + Ordinal.omega0) :=
  Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0

private theorem natCast_add_one_lt_omega0_add_omega0 (m : ℕ) :
    (m : Ordinal.{u}) + 1 < Ordinal.omega0 + Ordinal.omega0 := by
  rw [← Nat.cast_add_one]
  exact (Ordinal.natCast_lt_omega0 _).trans_le le_self_add

private theorem omega0_add_natCast_add_one_lt (n : ℕ) :
    Ordinal.omega0 + (n : Ordinal.{u}) + 1 < Ordinal.omega0 + Ordinal.omega0 := by
  rw [add_assoc, ← Nat.cast_add_one]
  exact add_lt_add_right (Ordinal.natCast_lt_omega0 _) _

/-- **The block theorem, general form**: at length `ω + ω`, the canonical transfinite sum
equals the block-compositional `hahnSum₂` — the canonical sum of the coarse block
`k ↦ t k` plus the canonical sum of the fine block `k ↦ t (ω + k)` — for any proofs of
strict domination of the two blocks. Proof: the transfinite identification engine at the
limit stage `ω + ω`, applied to the Conway sum of the two ω-length option games of
`Infinity.GameCofinality`: its value is `hahnSum₂`, which is an `ω + ω` sum
(`isHahnSum₂_hahnSum₂` + `isHahnSumO_omega0_add_omega0_iff`), and each option differs from
it by a positive quantity of class `mk (t m)` or `mk (t (ω + n))`, beaten by the
transfinite option at stage `m + 1` or `ω + n + 1`. -/
theorem hahnSumO_omega0_add_omega0_eq_hahnSum₂'
    (ht : IsStrictDom t (Ordinal.omega0 + Ordinal.omega0))
    (ht₁ : ∀ n, ArchimedeanClass.mk ((fun k : ℕ ↦ t k) n) <
      ArchimedeanClass.mk ((fun k : ℕ ↦ t k) (n + 1)))
    (ht₂ : ∀ n, ArchimedeanClass.mk ((fun k : ℕ ↦ t (Ordinal.omega0 + k)) n) <
      ArchimedeanClass.mk ((fun k : ℕ ↦ t (Ordinal.omega0 + k)) (n + 1))) :
    hahnSumO t (Ordinal.omega0 + Ordinal.omega0) = hahnSum₂ ht₁ ht₂ := by
  have hγ := isSuccLimit_omega0_add_omega0'
  haveI := numeric_optionGame ht₁
  haveI := numeric_optionGame ht₂
  have hX : IsHahnSum (fun k : ℕ ↦ t k) (hahnSum ht₁) := isHahnSum_hahnSum ht₁
  have hY : IsHahnSum (fun k : ℕ ↦ t (Ordinal.omega0 + k)) (hahnSum ht₂) :=
    isHahnSum_hahnSum ht₂
  have hG : Surreal.mk (optionGame (fun k : ℕ ↦ t k) +
      optionGame (fun k : ℕ ↦ t (Ordinal.omega0 + k))) = hahnSum₂ ht₁ ht₂ := by
    rw [Surreal.mk_add, mk_optionGame_eq_hahnSum ht₁, mk_optionGame_eq_hahnSum ht₂]
    rfl
  have hP : IsHahnSumO t (Ordinal.omega0 + Ordinal.omega0) (hahnSum₂ ht₁ ht₂) :=
    (isHahnSumO_omega0_add_omega0_iff ht).2 (isHahnSum₂_hahnSum₂ ht₁ ht₂)
  rw [← hG]
  refine hahnSumO_eq_of_isHahnSumO_of_moves_le hγ ht (by rwa [hG]) ?_ ?_
  · rw [forall_moves_add]
    constructor
    · -- coarse-block lower options, beaten at stage `m + 1`
      intro a ha
      rw [leftMoves_optionGame] at ha
      obtain ⟨m, rfl⟩ := ha
      have hβ := natCast_add_one_lt_omega0_add_omega0.{u} m
      refine ⟨(m : Ordinal.{u}) + 1, hβ, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, mk_optionGame_eq_hahnSum ht₂]
      have h1 := sub_optLo_bounds ht₁ hX m
      have hDmk : ArchimedeanClass.mk (hahnSum ht₁ - optLo (fun k : ℕ ↦ t k) m) <
          ArchimedeanClass.mk (t ((m : Ordinal.{u}) + 1)) := by
        rw [mk_eq_of_bounds h1.1 h1.2]
        exact ht (lt_add_one_iff.2 le_rfl) hβ
      have key := sub_le_optLoO_of_mk_lt ht hP (pos_of_bounds' h1.1)
        (hγ.add_one_lt_of_ordinal hβ) hDmk
      have hid : optLo (fun k : ℕ ↦ t k) m + hahnSum ht₂ =
          hahnSum₂ ht₁ ht₂ - (hahnSum ht₁ - optLo (fun k : ℕ ↦ t k) m) := by
        unfold hahnSum₂; ring
      rw [hid]
      exact key
    · -- fine-block lower options, beaten at stage `ω + n + 1`
      intro b hb
      rw [leftMoves_optionGame] at hb
      obtain ⟨n, rfl⟩ := hb
      have hβ := omega0_add_natCast_add_one_lt.{u} n
      refine ⟨Ordinal.omega0 + (n : Ordinal.{u}) + 1, hβ, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, mk_optionGame_eq_hahnSum ht₁]
      have h2 := sub_optLo_bounds ht₂ hY n
      have hDmk : ArchimedeanClass.mk
          (hahnSum ht₂ - optLo (fun k : ℕ ↦ t (Ordinal.omega0 + k)) n) <
          ArchimedeanClass.mk (t (Ordinal.omega0 + (n : Ordinal.{u}) + 1)) := by
        rw [mk_eq_of_bounds h2.1 h2.2]
        exact ht (lt_add_one_iff.2 le_rfl) hβ
      have key := sub_le_optLoO_of_mk_lt ht hP (pos_of_bounds' h2.1)
        (hγ.add_one_lt_of_ordinal hβ) hDmk
      have hid : hahnSum ht₁ + optLo (fun k : ℕ ↦ t (Ordinal.omega0 + k)) n =
          hahnSum₂ ht₁ ht₂ -
            (hahnSum ht₂ - optLo (fun k : ℕ ↦ t (Ordinal.omega0 + k)) n) := by
        unfold hahnSum₂; ring
      rw [hid]
      exact key
  · rw [forall_moves_add]
    constructor
    · -- coarse-block upper options
      intro a ha
      rw [rightMoves_optionGame] at ha
      obtain ⟨m, rfl⟩ := ha
      have hβ := natCast_add_one_lt_omega0_add_omega0.{u} m
      refine ⟨(m : Ordinal.{u}) + 1, hβ, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, mk_optionGame_eq_hahnSum ht₂]
      have h1 := optHi_sub_bounds ht₁ hX m
      have hDmk : ArchimedeanClass.mk (optHi (fun k : ℕ ↦ t k) m - hahnSum ht₁) <
          ArchimedeanClass.mk (t ((m : Ordinal.{u}) + 1)) := by
        rw [mk_eq_of_bounds h1.1 h1.2]
        exact ht (lt_add_one_iff.2 le_rfl) hβ
      have key := optHiO_le_add_of_mk_lt ht hP (pos_of_bounds' h1.1)
        (hγ.add_one_lt_of_ordinal hβ) hDmk
      have hid : optHi (fun k : ℕ ↦ t k) m + hahnSum ht₂ =
          hahnSum₂ ht₁ ht₂ + (optHi (fun k : ℕ ↦ t k) m - hahnSum ht₁) := by
        unfold hahnSum₂; ring
      rw [hid]
      exact key
    · -- fine-block upper options
      intro b hb
      rw [rightMoves_optionGame] at hb
      obtain ⟨n, rfl⟩ := hb
      have hβ := omega0_add_natCast_add_one_lt.{u} n
      refine ⟨Ordinal.omega0 + (n : Ordinal.{u}) + 1, hβ, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, mk_optionGame_eq_hahnSum ht₁]
      have h2 := optHi_sub_bounds ht₂ hY n
      have hDmk : ArchimedeanClass.mk
          (optHi (fun k : ℕ ↦ t (Ordinal.omega0 + k)) n - hahnSum ht₂) <
          ArchimedeanClass.mk (t (Ordinal.omega0 + (n : Ordinal.{u}) + 1)) := by
        rw [mk_eq_of_bounds h2.1 h2.2]
        exact ht (lt_add_one_iff.2 le_rfl) hβ
      have key := optHiO_le_add_of_mk_lt ht hP (pos_of_bounds' h2.1)
        (hγ.add_one_lt_of_ordinal hβ) hDmk
      have hid : hahnSum ht₁ + optHi (fun k : ℕ ↦ t (Ordinal.omega0 + k)) n =
          hahnSum₂ ht₁ ht₂ +
            (optHi (fun k : ℕ ↦ t (Ordinal.omega0 + k)) n - hahnSum ht₂) := by
        unfold hahnSum₂; ring
      rw [hid]
      exact key

/-- **THE BLOCK THEOREM**: the canonical transfinite sum at length `ω + ω` **is** the
block-compositional sum `hahnSum₂ = hahnSum (coarse block) + hahnSum (fine block)` of
`Infinity.OrdinalSum`. This closes the question left open there and in
`Infinity.NormalForm` (`hahnSumO_eq_hahnSum₂_iff`): the compositional formula computes the
birthday-minimal `ω + ω` sum. -/
theorem hahnSumO_omega0_add_omega0_eq_hahnSum₂
    (ht : IsStrictDom t (Ordinal.omega0 + Ordinal.omega0)) :
    hahnSumO t (Ordinal.omega0 + Ordinal.omega0) =
      hahnSum₂ (ht.natCast_succ le_self_add) ht.fine_natCast_succ :=
  hahnSumO_omega0_add_omega0_eq_hahnSum₂' ht _ _

/-- **`hahnSum₂` is birthday-minimal**: the compositional `ω + ω` sum is the
birthday-simplest `ω + ω` sum — the translation-equivariance question of
`Infinity.OrdinalSum`, answered affirmatively for canonical sums. -/
theorem birthday_hahnSum₂_le_of_isHahnSum₂
    (ht : IsStrictDom t (Ordinal.omega0 + Ordinal.omega0)) {z : Surreal.{u}}
    (hz : IsHahnSum₂ (ht.natCast_succ le_self_add) (fun k ↦ t (Ordinal.omega0 + k)) z) :
    (hahnSum₂ (ht.natCast_succ le_self_add) ht.fine_natCast_succ).birthday ≤ z.birthday :=
  (hahnSumO_eq_hahnSum₂_iff ht).1 (hahnSumO_omega0_add_omega0_eq_hahnSum₂ ht) z hz

/-- The canonical partial sums of an `ω + ω`-series at the stages `ω + n` and at `ω + ω`
are both block-compositional: this is `hahnSumO_omega0_add_natCast` extended to the limit
stage. -/
theorem hahnSumO_omega0_add_omega0_eq_add
    (ht : IsStrictDom t (Ordinal.omega0 + Ordinal.omega0)) :
    hahnSumO t (Ordinal.omega0 + Ordinal.omega0) =
      hahnSum (ht.natCast_succ le_self_add) + hahnSum ht.fine_natCast_succ :=
  hahnSumO_omega0_add_omega0_eq_hahnSum₂ ht

end Block

end Surreal

/-! ### Hahn-series evaluation adds on a common support

The library's `SurrealHahnSeries` adds coefficientwise. When two series have the *same*
support and no coefficient cancels, the sum has the same support, the same length, the
same exponent enumeration, and termwise-added terms — so the equal-class additivity
theorem applies to the term sequences and `evalHahn` is additive. -/

namespace SurrealHahnSeries

/-- Equal supports give equal lengths. -/
theorem length_eq_of_support_eq {x y : SurrealHahnSeries.{u}} (h : x.support = y.support) :
    x.length = y.length :=
  le_antisymm (length_mono h.le) (length_mono h.ge)

/-- `typein` on a subtype of the surreals depends only on the underlying set. -/
private theorem typein_congr_of_eq {S T : Set Surreal.{u}} (h : S = T)
    [IsWellOrder S (· > ·)] [IsWellOrder T (· > ·)] {e : Surreal.{u}} (heS : e ∈ S)
    (heT : e ∈ T) :
    Ordinal.typein (· > · : S → S → Prop) ⟨e, heS⟩ =
      Ordinal.typein (· > · : T → T → Prop) ⟨e, heT⟩ := by
  subst h; rfl

/-- **The exponent enumeration depends only on the support**: two series with the same
support enumerate the same exponents, index by index. -/
theorem exp_eq_of_support_eq {x y : SurrealHahnSeries.{u}} (h : x.support = y.support)
    {i : Ordinal.{u}} (hx : i < x.length) (hy : i < y.length) :
    (x.exp ⟨i, hx⟩).1 = (y.exp ⟨i, hy⟩).1 := by
  have heS : (x.exp ⟨i, hx⟩).1 ∈ x.support := (x.exp ⟨i, hx⟩).2
  have heT : (x.exp ⟨i, hx⟩).1 ∈ y.support := h ▸ heS
  have h1 : Ordinal.typein (· > · : x.support → x.support → Prop) ⟨(x.exp ⟨i, hx⟩).1, heS⟩ =
      Ordinal.lift.{u + 1} i := by
    rw [typein_support]
    have : (⟨(x.exp ⟨i, hx⟩).1, heS⟩ : x.support) = x.exp ⟨i, hx⟩ := rfl
    rw [this, RelIso.symm_apply_apply]
  have h2 : Ordinal.typein (· > · : y.support → y.support → Prop) ⟨(x.exp ⟨i, hx⟩).1, heT⟩ =
      Ordinal.lift.{u + 1} i := by
    rw [← typein_congr_of_eq h heS heT]; exact h1
  rw [typein_support, Ordinal.lift_inj] at h2
  have h3 : y.exp.symm ⟨(x.exp ⟨i, hx⟩).1, heT⟩ = ⟨i, hy⟩ := Subtype.ext h2
  have h4 := congrArg y.exp h3
  rw [RelIso.apply_symm_apply] at h4
  rw [← h4]

/-- A coefficient below the length is nonzero. -/
theorem coeffIdx_ne_zero {x : SurrealHahnSeries.{u}} {i : Ordinal.{u}} (hi : i < x.length) :
    x.coeffIdx i ≠ 0 :=
  fun h0 ↦ absurd (coeffIdx_eq_zero_iff.1 h0) hi.not_ge

/-- The support of a sum of two series with the same support and no coefficient
cancellation is that common support. -/
theorem support_add_of_support_eq {x y : SurrealHahnSeries.{u}} (h : x.support = y.support)
    (hnc : ∀ i ∈ x.support, x.coeff i + y.coeff i ≠ 0) : (x + y).support = x.support := by
  apply Set.Subset.antisymm
  · intro i hi
    have := support_add_subset hi
    rwa [← h, Set.union_self] at this
  · intro i hi
    rw [mem_support_iff, coeff_add_apply]
    exact hnc i hi

/-- **Terms add** for series with the same support and no coefficient cancellation. -/
theorem term_add_of_support_eq {x y : SurrealHahnSeries.{u}} (h : x.support = y.support)
    (hnc : ∀ i ∈ x.support, x.coeff i + y.coeff i ≠ 0) {i : Ordinal.{u}}
    (hi : i < x.length) : (x + y).term i = x.term i + y.term i := by
  have hs := support_add_of_support_eq h hnc
  have hxy : i < (x + y).length := (length_eq_of_support_eq hs).symm ▸ hi
  have hy : i < y.length := length_eq_of_support_eq h ▸ hi
  rw [term_of_lt hxy, term_of_lt hi, term_of_lt hy, coeffIdx_of_lt hxy, coeffIdx_of_lt hi,
    coeffIdx_of_lt hy, exp_eq_of_support_eq hs hxy hi, ← exp_eq_of_support_eq h hi hy,
    coeff_add_apply, Real.toSurreal_add, add_mul]

end SurrealHahnSeries

namespace Surreal

/-- **Hahn-series evaluation adds on a common support**: for surreal Hahn series `x, y`
with the same support and no coefficient cancellation, `evalHahn (x + y) = evalHahn x +
evalHahn y`. The first ring-homomorphism law for the evaluation map of
`Infinity.NormalForm`, from the equal-class additivity theorem `hahnSumO_add_of_mk_eq`
applied to the term sequences. -/
theorem evalHahn_add_of_support_eq {x y : SurrealHahnSeries.{u}} (h : x.support = y.support)
    (hnc : ∀ i ∈ x.support, x.coeff i + y.coeff i ≠ 0) :
    evalHahn (x + y) = evalHahn x + evalHahn y := by
  have hs := SurrealHahnSeries.support_add_of_support_eq h hnc
  have hlxy := SurrealHahnSeries.length_eq_of_support_eq hs
  have hlyx := SurrealHahnSeries.length_eq_of_support_eq h
  unfold evalHahn
  rw [hlxy, ← hlyx, hahnSumO_congr (t' := fun β ↦ x.term β + y.term β)
    (fun β hβ ↦ SurrealHahnSeries.term_add_of_support_eq h hnc hβ)]
  refine hahnSumO_add_of_mk_eq x.isStrictDom_term (y.isStrictDom_term.mono hlyx.le) ?_ ?_
  · intro β hβ
    have hy : β < y.length := hlyx ▸ hβ
    rw [SurrealHahnSeries.term_of_lt hβ, SurrealHahnSeries.term_of_lt hy,
      ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
      mk_realCast (SurrealHahnSeries.coeffIdx_ne_zero hβ),
      mk_realCast (SurrealHahnSeries.coeffIdx_ne_zero hy),
      SurrealHahnSeries.exp_eq_of_support_eq h hβ hy]
  · intro β hβ
    have hxy : β < (x + y).length := hlxy.symm ▸ hβ
    rw [← SurrealHahnSeries.term_add_of_support_eq h hnc hβ, SurrealHahnSeries.term_of_lt hxy,
      SurrealHahnSeries.term_of_lt hβ, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
      mk_realCast (SurrealHahnSeries.coeffIdx_ne_zero hxy),
      mk_realCast (SurrealHahnSeries.coeffIdx_ne_zero hβ),
      SurrealHahnSeries.exp_eq_of_support_eq hs hxy hβ]

end Surreal

end
