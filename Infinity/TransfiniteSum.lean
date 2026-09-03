/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.CanonicalSum

/-!
# Transfinite summation of arbitrary ordinal length

The summation theory built so far climbs three rungs: length `ω` (`Infinity.Series`,
`Infinity.Summation`), the canonical length-`ω` sum (`Infinity.CanonicalSum`), and the
hand-built lengths `ω + ω` and `ω·3` (`Infinity.OrdinalSum`). This file makes the length
**arbitrary**: for every ordinal `α` and every `α`-indexed series of surreals, we define
the canonical partial sums of *every* stage `β ≤ α` by a single transfinite recursion, and
prove the full Transfinite Summation Theorem — every strictly dominating series of any
ordinal length has a Hahn sum, canonically.

**The recursion** (`hahnSumO t β`, the canonical sum of the prefix of `t` below `β`):

* stage `0` : the empty sum is `0`;
* stage `β + 1` : the previous stage plus the term, `hahnSumO t β + t β`;
* limit stage `γ` : the partial sums so far do not converge — they *cannot*
  (`tendstoSurreal_atTop_iff_eventuallyEq`) — so the stage-`γ` value must be **chosen**:
  it is the birthday-simplest surreal lying in every domination band
  `{z | z − hahnSumO t β = O(t β)}` for `β < γ`, obtained as `Cut.simplestBtwn` of the cuts
  `sumLoO`/`sumHiO` bounding the band intersection (generalizing the `sumLo`/`sumHi`
  construction of `Infinity.CanonicalSum` from anchors `partialSum t n` to anchors
  `hahnSumO t β`). When the bands do not separate — the series was not summable — the
  recursion takes the junk value `0`, which keeps `hahnSumO` **total**: no proof obligations
  ride along inside the recursion, and all theorems are guarded by hypotheses instead.

This realizes, as a genuine transfinite recursion, the design that `Infinity.OrdinalSum`
built by hand at `ω + ω`: *the principled partial sum at a limit stage is the canonical
sum of the prefix*, well-defined because canonicity (birthday-minimality, unique by
`Cut.eq_of_fits_of_birthday_le`) pins what mere Hahn-sum-ness leaves floating.

**Main definitions.**

* `Surreal.hahnSumO t α` : the canonical transfinite sum of the length-`α` prefix of
  `t : Ordinal → Surreal` — a *total* function of `t` and `α`.
* `Surreal.IsHahnSumO t α x` : `x` is a Hahn sum of the length-`α` prefix of `t` — every
  residual `x - hahnSumO t β` (`β < α`) is dominated by the first omitted term `t β`.
* `Surreal.IsStrictDom t α` : strict domination below `α` — each term lies at a strictly
  finer scale (strictly larger Archimedean class) than every earlier one.

**Main theorems.**

* `Surreal.isHahnSumO_hahnSumO` : **the Transfinite Summation Theorem** — for every
  ordinal `α`, every strictly dominating series of length `α` has a Hahn sum, namely the
  canonical one. The proof is a transfinite induction; at limit stages the sandwich cut
  `!{hahnSumO t β − 2|t β| | hahnSumO t β + 2|t β|}` of `Infinity.Summation` reappears
  with canonical partial sums as anchors, and its separation is again pure domination
  calculus.
* `Surreal.IsHahnSumO.mk_sub_le` : uniqueness modulo every term's class.
* `Surreal.birthday_hahnSumO_le` : at limit lengths, the canonical sum is the
  birthday-minimal Hahn sum.
* `Surreal.hahnSumO_natCast` / `Surreal.isHahnSumO_omega0_iff` /
  `Surreal.hahnSumO_omega0` : the theory restricts on the nose to the finite partial sums,
  to `IsHahnSum`, and to the canonical `hahnSum` at length `ω`.

`Infinity.NormalForm` continues with the `ω + ω` compatibility theorems, the ω-power
payoff (arbitrary-length base-`ω` expansions denote surreals) and the evaluation of the
library's `SurrealHahnSeries`.

The informal mathematics is Conway's and Gonshor's normal-form/Hahn-series theory
(ONAG ch. 3; Gonshor ch. 5); the contribution here is the first formalization, and the
definitional route through the canonical-partial-sum recursion with the cut-interval
`simplestBtwn` at limits.
-/

open ArchimedeanClass Order

universe u

noncomputable section

namespace Surreal

/-! ### Domination bands at an arbitrary anchor

`Infinity.CanonicalSum` built the cuts `bandLo`/`bandHi` bounding the band
`{z | z − partialSum t n = O(t n)}`. The transfinite theory needs the same bands anchored
at arbitrary partial sums, so we factor out the anchor. -/

/-- The cut at the lower edge of the domination band `{z | z − s = O(w)}` around the
anchor `s` at the scale of `w`. -/
def bandLoAt (s w : Surreal) : Cut :=
  ⨅ k : ℕ, Cut.rightSurreal (s - (k + 1) • |w|)

/-- The cut at the upper edge of the domination band around the anchor `s` at the scale
of `w`. -/
def bandHiAt (s w : Surreal) : Cut :=
  ⨆ k : ℕ, Cut.leftSurreal (s + (k + 1) • |w|)

/-- The `ℕ`-indexed bands of `Infinity.CanonicalSum` are the anchored bands at the finite
partial sums. -/
theorem bandLo_eq_bandLoAt (t : ℕ → Surreal) (n : ℕ) :
    bandLo t n = bandLoAt (partialSum t n) (t n) :=
  rfl

theorem bandHi_eq_bandHiAt (t : ℕ → Surreal) (n : ℕ) :
    bandHi t n = bandHiAt (partialSum t n) (t n) :=
  rfl

/-- Membership in the anchored band, unfolded to inequalities: within some multiple of
`|w|` of the anchor iff dominated by `w`. -/
private theorem bandAt_iff {z s w : Surreal} (h0 : w ≠ 0) :
    ((∃ k : ℕ, s - (k + 1) • |w| < z) ∧ (∃ k : ℕ, z < s + (k + 1) • |w|)) ↔
      ArchimedeanClass.mk w ≤ ArchimedeanClass.mk (z - s) := by
  rw [ArchimedeanClass.mk_le_mk]
  constructor
  · rintro ⟨⟨k₁, h1⟩, ⟨k₂, h2⟩⟩
    refine ⟨max k₁ k₂ + 1, ?_⟩
    have hm1 : (k₁ + 1) • |w| ≤ (max k₁ k₂ + 1) • |w| :=
      nsmul_le_nsmul_left (abs_nonneg _) (by omega)
    have hm2 : (k₂ + 1) • |w| ≤ (max k₁ k₂ + 1) • |w| :=
      nsmul_le_nsmul_left (abs_nonneg _) (by omega)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · rintro ⟨k, hk⟩
    have hpos : (0 : Surreal) < |w| := abs_pos.2 h0
    have hlt : |z - s| < (k + 1) • |w| := by
      refine hk.trans_lt ?_
      rw [succ_nsmul]
      linarith
    rw [abs_sub_lt_iff] at hlt
    exact ⟨⟨k, by linarith [hlt.2]⟩, ⟨k, by linarith [hlt.1]⟩⟩

/-- `Cut.simplestBtwn`, totalized with junk value `0` when the cuts do not separate. This
is what lets the transfinite recursion below carry no proof obligations. -/
def simplestBtwnD (x y : Cut) : Surreal :=
  if h : x < y then Cut.simplestBtwn h else 0

theorem simplestBtwnD_of_lt {x y : Cut} (h : x < y) :
    simplestBtwnD x y = Cut.simplestBtwn h :=
  dif_pos h

/-! ### The canonical transfinite partial-sum recursion -/

/-- **The canonical transfinite sum** of the length-`α` prefix of the series
`t : Ordinal → Surreal`, by transfinite recursion on `α`: the empty sum is `0`; the sum of
one more term is added on; and at a limit stage the sum is the birthday-simplest surreal
lying in every earlier domination band `{z | z − hahnSumO t β = O(t β)}` (junk value `0`
if the bands do not separate, which never happens for strictly dominating series —
`isHahnSumO_hahnSumO`).

Simultaneously, `hahnSumO t β` for `β < α` serves as the canonical *partial* sum at stage
`β` — the transfinite generalization of `partialSum`, and the anchor for the residual
conditions of `IsHahnSumO`. This is the `Infinity.OrdinalSum` design ("the stage-`ω`
partial sum is the canonical sum of the coarse block"), iterated by recursion instead of
by hand. -/
def hahnSumO (t : Ordinal.{u} → Surreal.{u}) (α : Ordinal.{u}) : Surreal.{u} :=
  Ordinal.limitRecOn (motive := fun _ ↦ Surreal.{u}) α 0 (fun β S ↦ S + t β)
    fun γ _ ih ↦
      simplestBtwnD (⨆ β : Set.Iio γ, bandLoAt (ih β.1 β.2) (t β.1))
        (⨅ β : Set.Iio γ, bandHiAt (ih β.1 β.2) (t β.1))

@[simp]
theorem hahnSumO_zero (t : Ordinal.{u} → Surreal.{u}) : hahnSumO t 0 = 0 :=
  Ordinal.limitRecOn_zero ..

@[simp]
theorem hahnSumO_add_one (t : Ordinal.{u} → Surreal.{u}) (β : Ordinal.{u}) :
    hahnSumO t (β + 1) = hahnSumO t β + t β :=
  Ordinal.limitRecOn_add_one ..

/-- The cut just below all the domination bands of stages `< γ`, anchored at the canonical
partial sums — the transfinite `sumLo`. -/
def sumLoO (t : Ordinal.{u} → Surreal.{u}) (γ : Ordinal.{u}) : Cut :=
  ⨆ β : Set.Iio γ, bandLoAt (hahnSumO t β.1) (t β.1)

/-- The cut just above all the domination bands of stages `< γ` — the transfinite
`sumHi`. -/
def sumHiO (t : Ordinal.{u} → Surreal.{u}) (γ : Ordinal.{u}) : Cut :=
  ⨅ β : Set.Iio γ, bandHiAt (hahnSumO t β.1) (t β.1)

/-- The limit-stage equation of the recursion: at a limit ordinal, the canonical sum is
the simplest surreal between the band cuts. -/
theorem hahnSumO_of_isSuccLimit (t : Ordinal.{u} → Surreal.{u}) {γ : Ordinal.{u}}
    (hγ : IsSuccLimit γ) :
    hahnSumO t γ = simplestBtwnD (sumLoO t γ) (sumHiO t γ) := by
  unfold sumLoO sumHiO hahnSumO
  rw [Ordinal.limitRecOn_limit _ _ _ _ hγ]

/-! ### The summation predicate and strict domination -/

/-- `x` is a **Hahn sum of the length-`α` prefix of `t`**: at every stage `β < α`, the
residual of `x` against the canonical partial sum is dominated by the first omitted term
`t β` (its Archimedean class is at least `mk (t β)`; recall larger class = smaller
magnitude). At `α = ω` this is exactly `IsHahnSum` (`isHahnSumO_omega0_iff`); at limit
stages the anchor `hahnSumO t β` is the canonical prefix sum, which is what makes the
condition well-posed where finite partial sums do not exist. -/
def IsHahnSumO (t : Ordinal.{u} → Surreal.{u}) (α : Ordinal.{u}) (x : Surreal.{u}) : Prop :=
  ∀ β < α, ArchimedeanClass.mk (t β) ≤ ArchimedeanClass.mk (x - hahnSumO t β)

/-- Hahn-sum-ness restricts to shorter prefixes. -/
theorem IsHahnSumO.mono {t : Ordinal.{u} → Surreal.{u}} {α α' : Ordinal.{u}}
    {x : Surreal.{u}} (hx : IsHahnSumO t α x) (h : α' ≤ α) : IsHahnSumO t α' x :=
  fun β hβ ↦ hx β (hβ.trans_le h)

/-- **Uniqueness modulo every term's class**: two Hahn sums of the same length-`α` prefix
differ by a quantity dominated by every single term. -/
theorem IsHahnSumO.mk_sub_le {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    {x y : Surreal.{u}} (hx : IsHahnSumO t α x) (hy : IsHahnSumO t α y)
    {β : Ordinal.{u}} (hβ : β < α) :
    ArchimedeanClass.mk (t β) ≤ ArchimedeanClass.mk (x - y) := by
  have hxy : x - y = (x - hahnSumO t β) + -(y - hahnSumO t β) := by ring
  rw [hxy]
  refine le_trans (le_min (hx β hβ) ?_) (ArchimedeanClass.min_le_mk_add ..)
  rw [ArchimedeanClass.mk_neg]
  exact hy β hβ

/-- The series `t` is **strictly dominating below `α`**: each term lies at a strictly
finer scale (strictly larger Archimedean class) than every earlier one. This is the
summability hypothesis of the Transfinite Summation Theorem. -/
def IsStrictDom (t : Ordinal.{u} → Surreal.{u}) (α : Ordinal.{u}) : Prop :=
  ∀ ⦃β γ : Ordinal.{u}⦄, β < γ → γ < α →
    ArchimedeanClass.mk (t β) < ArchimedeanClass.mk (t γ)

theorem IsStrictDom.mono {t : Ordinal.{u} → Surreal.{u}} {α α' : Ordinal.{u}}
    (ht : IsStrictDom t α) (h : α' ≤ α) : IsStrictDom t α' :=
  fun _ _ hβγ hγ ↦ ht hβγ (hγ.trans_le h)

/-- A term with a strictly later term below the bound is nonzero. -/
theorem IsStrictDom.ne_zero {t : Ordinal.{u} → Surreal.{u}} {α β : Ordinal.{u}}
    (ht : IsStrictDom t α) (hβ : β + 1 < α) : t β ≠ 0 := by
  intro h0
  have h1 := ht (lt_add_one_iff.2 le_rfl) hβ
  rw [h0, show ArchimedeanClass.mk (0 : Surreal) = ⊤ from
    ArchimedeanClass.mk_eq_top_iff.2 rfl] at h1
  exact not_top_lt h1

/-- Below a limit bound, every term of a strictly dominating series is nonzero. -/
theorem IsStrictDom.ne_zero_of_isSuccLimit {t : Ordinal.{u} → Surreal.{u}}
    {α : Ordinal.{u}} (ht : IsStrictDom t α) (hα : IsSuccLimit α) :
    ∀ β < α, t β ≠ 0 := by
  intro β hβ
  refine ht.ne_zero ?_
  rw [← succ_eq_add_one]
  exact hα.succ_lt hβ

/-! ### The fits characterization at limit stages -/

/-- **The transfinite fits characterization**: a surreal lies between the cuts
`sumLoO`/`sumHiO` at stage `γ` iff it is a Hahn sum of the length-`γ` prefix — the
lattice laws of `Cut` turn the intersection of all the anchored bands into a single cut
interval, exactly as in `fits_iff_isHahnSum`. -/
theorem fits_sumO_iff {t : Ordinal.{u} → Surreal.{u}} {γ : Ordinal.{u}}
    (ht0 : ∀ β < γ, t β ≠ 0) {z : Surreal.{u}} :
    Cut.Fits z (sumLoO t γ) (sumHiO t γ) ↔ IsHahnSumO t γ z := by
  rw [Cut.Fits, Set.mem_inter_iff, ← Cut.notMem_left_iff]
  unfold sumLoO sumHiO bandLoAt bandHiAt
  simp only [Cut.left_iSup, Cut.left_iInf, Cut.left_rightSurreal, Cut.left_leftSurreal,
    Set.mem_iUnion, Set.mem_iInter, Set.mem_Iic, Set.mem_Iio, not_exists, not_forall,
    not_le]
  constructor
  · rintro ⟨h1, h2⟩ β hβ
    exact (bandAt_iff (ht0 β hβ)).1 ⟨h1 ⟨β, hβ⟩, h2 ⟨β, hβ⟩⟩
  · intro h
    exact ⟨fun β ↦ ((bandAt_iff (ht0 β.1 β.2)).2 (h β.1 β.2)).1,
      fun β ↦ ((bandAt_iff (ht0 β.1 β.2)).2 (h β.1 β.2)).2⟩

/-! ### Domination calculus helpers -/

private theorem le_mk_add' {c : ArchimedeanClass Surreal} {a b : Surreal}
    (ha : c ≤ ArchimedeanClass.mk a) (hb : c ≤ ArchimedeanClass.mk b) :
    c ≤ ArchimedeanClass.mk (a + b) :=
  le_trans (le_min ha hb) (ArchimedeanClass.min_le_mk_add ..)

private theorem lt_mk_add' {c : ArchimedeanClass Surreal} {a b : Surreal}
    (ha : c < ArchimedeanClass.mk a) (hb : c < ArchimedeanClass.mk b) :
    c < ArchimedeanClass.mk (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (ArchimedeanClass.min_le_mk_add ..)

private theorem mk_two' : ArchimedeanClass.mk (2 : Surreal) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [show (2 : Surreal) = ((2 : ℕ) : Surreal) by norm_cast,
    ArchimedeanClass.stdPart_natCast]
  norm_num

private theorem mk_two_mul_abs' (a : Surreal) :
    ArchimedeanClass.mk (2 * |a|) = ArchimedeanClass.mk a := by
  rw [ArchimedeanClass.mk_mul, mk_two', zero_add, ArchimedeanClass.mk_abs]

/-! ### The Transfinite Summation Theorem -/

private theorem isHahnSumO_hahnSumO_aux (t : Ordinal.{u} → Surreal.{u}) (α : Ordinal.{u}) :
    IsStrictDom t α → IsHahnSumO t α (hahnSumO t α) := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro _ β hβ
    exact absurd hβ not_lt_bot
  | add_one δ ih =>
    intro ht β hβ
    rw [hahnSumO_add_one]
    rcases (le_of_lt_add_one hβ).eq_or_lt with rfl | hlt
    · rw [add_sub_cancel_left]
    · have h1 : hahnSumO t δ + t δ - hahnSumO t β =
          (hahnSumO t δ - hahnSumO t β) + t δ := by ring
      rw [h1]
      exact le_mk_add' (ih (ht.mono (lt_add_one_iff.2 le_rfl).le) β hlt)
        (ht hlt (lt_add_one_iff.2 le_rfl)).le
  | limit γ hγ ih =>
    intro ht
    have ht0 : ∀ β < γ, t β ≠ 0 := ht.ne_zero_of_isSuccLimit hγ
    -- The key decomposition: between stages `β < δ < γ`, the canonical partial sums
    -- differ by `t β` plus strictly dominated junk.
    have key : ∀ β δ : Ordinal.{u}, β < δ → δ < γ →
        ArchimedeanClass.mk (t β) <
          ArchimedeanClass.mk (hahnSumO t δ - hahnSumO t (β + 1)) := by
      intro β δ hβδ hδγ
      rcases (add_one_le_iff.2 hβδ).eq_or_lt with heq | hlt
      · rw [← heq, sub_self,
          show ArchimedeanClass.mk (0 : Surreal) = ⊤ from
            ArchimedeanClass.mk_eq_top_iff.2 rfl]
        exact lt_top_iff_ne_top.2 fun htop ↦
          ht0 β (hβδ.trans hδγ) (ArchimedeanClass.mk_eq_top_iff.1 htop)
      · have h1 := ih δ hδγ (ht.mono hδγ.le) (β + 1) hlt
        exact (ht (lt_add_one_iff.2 le_rfl) (hlt.trans hδγ)).trans_le h1
    -- Separation of the sandwich cut, with canonical partial sums as anchors.
    have H : ∀ a ∈ Set.range (fun β : Set.Iio γ ↦ hahnSumO t β.1 - 2 * |t β.1|),
        ∀ b ∈ Set.range (fun β : Set.Iio γ ↦ hahnSumO t β.1 + 2 * |t β.1|), a < b := by
      rintro a ⟨⟨β, hβ⟩, rfl⟩ b ⟨⟨δ, hδ⟩, rfl⟩
      dsimp only
      rcases lt_trichotomy β δ with hβδ | rfl | hδβ
      -- `β < δ`: the gap is `t β` plus junk strictly dominated by `t β`.
      · have hdec : hahnSumO t δ =
            hahnSumO t β + t β + (hahnSumO t δ - hahnSumO t (β + 1)) := by
          rw [hahnSumO_add_one]; ring
        have hD : ArchimedeanClass.mk (t β) <
            ArchimedeanClass.mk ((hahnSumO t δ - hahnSumO t (β + 1)) + 2 * |t δ|) := by
          refine lt_mk_add' (key β δ hβδ hδ) ?_
          rw [mk_two_mul_abs']
          exact ht hβδ hδ
        have habs := abs_lt.1 (abs_lt_abs_of_mk_lt hD)
        have h1 : -|t β| ≤ t β := neg_abs_le _
        rw [hdec]
        linarith [habs.1]
      -- `β = δ`: the interval has positive width.
      · have := abs_pos.2 (ht0 β hβ)
        linarith
      -- `δ < β`: symmetric, the `-2|t β|` absorbed into the dominated junk.
      · have hdec : hahnSumO t β =
            hahnSumO t δ + t δ + (hahnSumO t β - hahnSumO t (δ + 1)) := by
          rw [hahnSumO_add_one]; ring
        have hD : ArchimedeanClass.mk (t δ) <
            ArchimedeanClass.mk ((hahnSumO t β - hahnSumO t (δ + 1)) + -(2 * |t β|)) := by
          refine lt_mk_add' (key δ β hδβ hβ) ?_
          rw [ArchimedeanClass.mk_neg, mk_two_mul_abs']
          exact ht hδβ hβ
        have habs := abs_lt.1 (abs_lt_abs_of_mk_lt hD)
        have h1 : t δ ≤ |t δ| := le_abs_self _
        rw [hdec]
        linarith [habs.2]
    -- The sandwich cut is a Hahn sum of the length-`γ` prefix.
    have hz : ∃ z, IsHahnSumO t γ z := by
      refine ⟨!{Set.range (fun β : Set.Iio γ ↦ hahnSumO t β.1 - 2 * |t β.1|) |
        Set.range (fun β : Set.Iio γ ↦ hahnSumO t β.1 + 2 * |t β.1|)}'H, fun β hβ ↦ ?_⟩
      have hl := lt_ofSets_of_mem_left (H := H) ⟨⟨β, hβ⟩, rfl⟩
      have hr := ofSets_lt_of_mem_right (H := H) ⟨⟨β, hβ⟩, rfl⟩
      dsimp only at hl hr
      rw [ArchimedeanClass.mk_le_mk]
      refine ⟨2, ?_⟩
      have habs : |(!{_ | _}'H) - hahnSumO t β| ≤ 2 * |t β| :=
        abs_le.2 ⟨by linarith, by linarith⟩
      calc |(!{_ | _}'H) - hahnSumO t β| ≤ 2 * |t β| := habs
        _ = 2 • |t β| := by rw [two_nsmul, two_mul]
    -- Hence the band cuts separate, and the simplest fit is the canonical sum.
    obtain ⟨z, hz⟩ := hz
    have hfits := (fits_sumO_iff ht0).2 hz
    rw [hahnSumO_of_isSuccLimit t hγ, simplestBtwnD_of_lt hfits.lt]
    exact (fits_sumO_iff ht0).1 (Cut.fits_simplestBtwn hfits.lt)

/-- **The Transfinite Summation Theorem**: for every ordinal `α`, every strictly
dominating series of length `α` has a Hahn sum — the canonical one produced by the
transfinite partial-sum recursion. This subsumes `exists_isHahnSum` (length `ω`) and the
hand-built lengths of `Infinity.OrdinalSum`, and gives transfinite summation on the
surreals at every ordinal length for the first time. -/
theorem isHahnSumO_hahnSumO {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    (ht : IsStrictDom t α) : IsHahnSumO t α (hahnSumO t α) :=
  isHahnSumO_hahnSumO_aux t α ht

/-- Existence form of the Transfinite Summation Theorem. -/
theorem exists_isHahnSumO {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    (ht : IsStrictDom t α) : ∃ x, IsHahnSumO t α x :=
  ⟨hahnSumO t α, isHahnSumO_hahnSumO ht⟩

/-- **Canonicity at limit lengths**: the canonical sum is the birthday-minimal Hahn sum of
any limit-length prefix. (At successor lengths minimality can genuinely fail — appending a
term is a translation, and simplicity is not translation-equivariant; see the discussion
in `Infinity.OrdinalSum`.) -/
theorem birthday_hahnSumO_le {t : Ordinal.{u} → Surreal.{u}} {γ : Ordinal.{u}}
    (hγ : IsSuccLimit γ) (ht0 : ∀ β < γ, t β ≠ 0) {z : Surreal.{u}}
    (hz : IsHahnSumO t γ z) : (hahnSumO t γ).birthday ≤ z.birthday := by
  have hfits := (fits_sumO_iff ht0).2 hz
  rw [hahnSumO_of_isSuccLimit t hγ, simplestBtwnD_of_lt hfits.lt]
  exact Cut.birthday_simplestBtwn_le_of_fits hfits

/-! ### Length `ω`: agreement with the classical theory

The transfinite theory restricts on the nose to `Infinity.Series`/`Infinity.CanonicalSum`:
finite-stage canonical partial sums are the finite partial sums, `IsHahnSumO` at `ω` is
`IsHahnSum`, and the canonical sum at `ω` is `hahnSum`. -/

/-- At finite stages, the canonical partial sums are the honest finite partial sums. -/
@[simp]
theorem hahnSumO_natCast (t : Ordinal.{u} → Surreal.{u}) (n : ℕ) :
    hahnSumO t n = partialSum (fun k ↦ t k) n := by
  induction n with
  | zero => rw [Nat.cast_zero, hahnSumO_zero, partialSum_zero]
  | succ n ih => rw [Nat.cast_add_one, hahnSumO_add_one, ih, partialSum_succ]

/-- **`IsHahnSumO` at `ω` is `IsHahnSum`**, unconditionally. -/
theorem isHahnSumO_omega0_iff {t : Ordinal.{u} → Surreal.{u}} {x : Surreal.{u}} :
    IsHahnSumO t Ordinal.omega0 x ↔ IsHahnSum (fun n ↦ t n) x := by
  constructor
  · intro h n
    have h1 := h n (Ordinal.natCast_lt_omega0 n)
    rwa [hahnSumO_natCast] at h1
  · intro h β hβ
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hβ
    rw [hahnSumO_natCast]
    exact h n

/-- Strict domination below any bound `≥ ω` restricts to strict domination of the
`ℕ`-indexed prefix. -/
theorem IsStrictDom.natCast_succ {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    (ht : IsStrictDom t α) (hω : Ordinal.omega0 ≤ α) (n : ℕ) :
    ArchimedeanClass.mk ((fun k : ℕ ↦ t k) n) <
      ArchimedeanClass.mk ((fun k : ℕ ↦ t k) (n + 1)) := by
  have h1 : ((n : Ordinal.{u})) < ((n + 1 : ℕ) : Ordinal.{u}) := by
    rw [Nat.cast_add_one]
    exact lt_add_one_iff.2 le_rfl
  exact ht h1 ((Ordinal.natCast_lt_omega0 (n + 1)).trans_le hω)

private theorem sumLoO_omega0 (t : Ordinal.{u} → Surreal.{u}) :
    sumLoO t Ordinal.omega0 = sumLo fun n ↦ t n := by
  have hpt : ∀ n : ℕ, bandLo (fun k ↦ t k) n = bandLoAt (hahnSumO t n) (t n) := by
    intro n
    rw [bandLo_eq_bandLoAt, hahnSumO_natCast]
  apply le_antisymm
  · refine iSup_le fun β ↦ ?_
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 β.2
    refine le_trans (le_of_eq ?_) (le_iSup (fun n : ℕ ↦ bandLo (fun k ↦ t k) n) n)
    rw [hpt n, hn]
  · refine iSup_le fun n ↦ ?_
    refine le_trans (le_of_eq (hpt n)) ?_
    exact le_iSup_of_le ⟨(n : Ordinal.{u}), Ordinal.natCast_lt_omega0 n⟩ le_rfl

private theorem sumHiO_omega0 (t : Ordinal.{u} → Surreal.{u}) :
    sumHiO t Ordinal.omega0 = sumHi fun n ↦ t n := by
  have hpt : ∀ n : ℕ, bandHi (fun k ↦ t k) n = bandHiAt (hahnSumO t n) (t n) := by
    intro n
    rw [bandHi_eq_bandHiAt, hahnSumO_natCast]
  apply le_antisymm
  · refine le_iInf fun n ↦ ?_
    refine le_trans ?_ (le_of_eq (hpt n).symm)
    exact iInf_le_of_le ⟨(n : Ordinal.{u}), Ordinal.natCast_lt_omega0 n⟩ le_rfl
  · refine le_iInf fun β ↦ ?_
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 β.2
    refine le_trans (iInf_le (fun n : ℕ ↦ bandHi (fun k ↦ t k) n) n) (le_of_eq ?_)
    rw [hpt n, hn]

/-- **The canonical sum at `ω` is the canonical sum**: `hahnSumO` at length `ω` recovers
`Infinity.CanonicalSum`'s birthday-simplest `hahnSum` exactly. -/
theorem hahnSumO_omega0 {t : Ordinal.{u} → Surreal.{u}}
    (ht : IsStrictDom t Ordinal.omega0) :
    hahnSumO t Ordinal.omega0 = hahnSum (ht.natCast_succ le_rfl) := by
  rw [hahnSumO_of_isSuccLimit t Ordinal.isSuccLimit_omega0, sumLoO_omega0, sumHiO_omega0,
    simplestBtwnD_of_lt (sumLo_lt_sumHi (ht.natCast_succ le_rfl))]
  rfl

/-! ### The canonical sum depends only on the prefix -/

private theorem hahnSumO_congr_aux (t t' : Ordinal.{u} → Surreal.{u}) (α : Ordinal.{u}) :
    (∀ β < α, t β = t' β) → hahnSumO t α = hahnSumO t' α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro _
    rw [hahnSumO_zero, hahnSumO_zero]
  | add_one δ ih =>
    intro h
    rw [hahnSumO_add_one, hahnSumO_add_one,
      ih fun β hβ ↦ h β (hβ.trans (lt_add_one_iff.2 le_rfl)),
      h δ (lt_add_one_iff.2 le_rfl)]
  | limit γ hγ ih =>
    intro h
    have hlo : sumLoO t γ = sumLoO t' γ := by
      unfold sumLoO
      exact iSup_congr fun β ↦ by
        rw [ih β.1 β.2 fun δ hδ ↦ h δ (hδ.trans β.2), h β.1 β.2]
    have hhi : sumHiO t γ = sumHiO t' γ := by
      unfold sumHiO
      exact iInf_congr fun β ↦ by
        rw [ih β.1 β.2 fun δ hδ ↦ h δ (hδ.trans β.2), h β.1 β.2]
    rw [hahnSumO_of_isSuccLimit t hγ, hahnSumO_of_isSuccLimit t' hγ, hlo, hhi]

/-- **The canonical sum depends only on the terms below `α`**: `hahnSumO t α` is a
well-defined function of the length-`α` prefix of `t`, so the total-function signature
loses no generality over `Π β : Iio α, Surreal`. -/
theorem hahnSumO_congr {t t' : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    (h : ∀ β < α, t β = t' β) : hahnSumO t α = hahnSumO t' α :=
  hahnSumO_congr_aux t t' α h

end Surreal
