/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.TransfiniteGame
import Infinity.HaloGame
import Infinity.ExpDichotomy

/-!
# Coarse representability and the concatenation theorem

`Infinity.TransfiniteGame` proved that the canonical transfinite sum `hahnSumO` is additive and
that the `ω + ω` sum is block-compositional. The next law of Conway's normal-form evaluation is
**concatenation**: the canonical sum of a series split at any ordinal `α` should be the canonical
sum of the first block plus the canonical sum of the (shifted) second block,

  `hahnSumO t (α + β) = hahnSumO t α + hahnSumO (fun δ ↦ t (α + δ)) β`.

This is **false in general** (the counterexample is at the end of the file), and this file
isolates the one concept that makes it true.

* **Coarse representability** `Surreal.CoarseRep X c`: `X` is the value of a numeric game all of
  whose options sit at distance *not finer than* the class `c` (`mk (X − a) ≤ c`; recall that in
  `ArchimedeanClass` larger means smaller magnitude, so this says every option is at least
  `c`-far from `X`). Closure lemmas: `CoarseRep.mono` (weaker at coarser `c`), `coarseRep_zero`,
  `CoarseRep.add` (the Conway sum game), `coarseRep_hahnSumO_of_isSuccLimit` (the transfinite
  option game at a limit stage), `CoarseRep.wpow` (the `ω`-power game `ω^ y` is coarsely
  representable at its own class), `CoarseRep.realCast_mul` (the Conway product with a real's
  game), hence `coarseRep_monomial` (every normal-form monomial `r · ω^ y` at the class
  `mk (ω^ y)`), and the induction `coarseRep_hahnSumO`: a canonical sum of every ordinal
  length is coarsely representable at any class bounding all its terms' classes and coarse
  representatives.
* **THE CONCATENATION THEOREM** `Surreal.hahnSumO_concat`: for `t` strictly dominating below
  `α + β`, if the first block's canonical sum is coarsely representable at the class of the
  first term `t α` of the second block, then
  `hahnSumO t (α + β) = hahnSumO t α + hahnSumO (fun δ ↦ t (α + δ)) β`. Proof: transfinite
  induction on `β`; at a limit stage the transfinite identification engine is applied to the
  Conway sum of a coarse representative of the first block and the transfinite option game of
  the second: the coarse options are beaten at stage `α + 1`, the option-game options at stage
  `α + δ + 1`. Corollary `Surreal.hahnSumO_concat_of_monomial`: **concatenation holds
  unconditionally for normal-form series** `Σ r_β · ω^(y_β)`.
* **The `ω`-length shift law** `Surreal.hahnSum_eq_add_hahnSum_shift`:
  `hahnSum t = t 0 + hahnSum (n ↦ t (n + 1))` whenever `t 0` is coarsely representable at
  `mk (t 1)` — the concatenation theorem at `α = 1`, read through the bridge `Surreal.ofSeq`
  from `ℕ`-indexed to ordinal-indexed series.
* **Halo simplicity of canonical sums** `Surreal.haloSimple_hahnSum` /
  `Surreal.haloSimple_hahnSumO`: a canonical sum is the birthday-simplest point of its own deep
  halo at any scale `ε` some power of which is finer than each term.
* **THE BOUNDARY** `Surreal.hahnSum_bdSeq_ne_add_hahnSum_shift` /
  `Surreal.exists_isStrictDom_hahnSumO_ne_concat`: with first term `ω⁻¹ + ω^(−ω)` followed by
  `ω⁻², ω⁻³, …`, the canonical sum of the whole series is **not** the first term plus the
  canonical sum of the rest — the `ω^(−ω)` tail of the first term is invisible to the canonical
  sum of the remaining series. So coarse representability is necessary, and it is exactly what
  fails: `ω⁻¹ + ω^(−ω)` is not coarsely representable at the class of `ω⁻²`
  (`Surreal.not_coarseRep_wpow_neg_one_add_wpow_neg_omega`, from the shift law read
  backwards). Proof of the boundary: both `(ω⁻¹ + ω^(−ω)) + Y` and
  `ω⁻¹ + Y` are Hahn sums of the series; the latter is the canonical sum of `Σ ω^(−(n+1))`
  (the shift law, with `CoarseRep.wpow`) and hence halo-simple at scale `ω⁻¹`; if the former
  were the canonical sum it would be birthday-minimal, so both would be the halo value of the
  same deep halo, forcing `ω^(−ω) = 0`.

Everything is the game-cofinality method of `Infinity.GameCofinality` and
`Infinity.TransfiniteGame`; no birthday census is used.
-/

open ArchimedeanClass IGame Order

universe u

noncomputable section

namespace Surreal

/-! ### Coarse representability -/

/-- **Coarse representability**: the surreal `X` is the value of a numeric game `G` every one of
whose options lies at distance from `X` of Archimedean class at most `c` — i.e. not finer than
`c` (larger class = smaller magnitude; a game with no options on a side satisfies the condition
on that side vacuously). Such a representative is what lets `X` be the first block of a
concatenated canonical sum whose second block has all its terms at classes `≥ c`. -/
def CoarseRep (X : Surreal.{u}) (c : ArchimedeanClass Surreal.{u}) : Prop :=
  ∃ G : IGame.{u}, ∃ _ : G.Numeric, Surreal.mk G = X ∧
    (∀ a ∈ Gᴸ, ∀ [a.Numeric], ArchimedeanClass.mk (X - Surreal.mk a) ≤ c) ∧
    (∀ b ∈ Gᴿ, ∀ [b.Numeric], ArchimedeanClass.mk (Surreal.mk b - X) ≤ c)

/-- Coarse representability is monotone in the class: a representative at `c` is a
representative at any finer `c'` (`c ≤ c'`). -/
theorem CoarseRep.mono {X : Surreal.{u}} {c c' : ArchimedeanClass Surreal.{u}}
    (h : CoarseRep X c) (hc : c ≤ c') : CoarseRep X c' := by
  obtain ⟨G, hG, hGX, hl, hr⟩ := h
  exact ⟨G, hG, hGX, fun a ha _ ↦ (hl a ha).trans hc, fun b hb _ ↦ (hr b hb).trans hc⟩

/-- `0` is coarsely representable at every class (the game `0` has no options). -/
theorem coarseRep_zero (c : ArchimedeanClass Surreal.{u}) : CoarseRep (0 : Surreal.{u}) c := by
  refine ⟨0, inferInstance, rfl, ?_, ?_⟩
  · intro a ha
    simp at ha
  · intro b hb
    simp at hb

/-- **Sums**: coarse representatives add (the Conway sum game, whose options are `a + H` and
`G + b`, sits at the same distances as the summands' options). -/
theorem CoarseRep.add {X Y : Surreal.{u}} {c : ArchimedeanClass Surreal.{u}}
    (hX : CoarseRep X c) (hY : CoarseRep Y c) : CoarseRep (X + Y) c := by
  obtain ⟨G, hG, hGX, hGl, hGr⟩ := hX
  obtain ⟨H, hH, hHY, hHl, hHr⟩ := hY
  refine ⟨G + H, inferInstance, by rw [Surreal.mk_add, hGX, hHY], ?_, ?_⟩
  · rw [forall_moves_add]
    constructor
    · intro a ha _
      haveI := IGame.Numeric.of_mem_moves ha
      rw [Surreal.mk_add, hHY, show X + Y - (Surreal.mk a + Y) = X - Surreal.mk a by ring]
      exact hGl a ha
    · intro b hb _
      haveI := IGame.Numeric.of_mem_moves hb
      rw [Surreal.mk_add, hGX, show X + Y - (X + Surreal.mk b) = Y - Surreal.mk b by ring]
      exact hHl b hb
  · rw [forall_moves_add]
    constructor
    · intro a ha _
      haveI := IGame.Numeric.of_mem_moves ha
      rw [Surreal.mk_add, hHY, show Surreal.mk a + Y - (X + Y) = Surreal.mk a - X by ring]
      exact hGr a ha
    · intro b hb _
      haveI := IGame.Numeric.of_mem_moves hb
      rw [Surreal.mk_add, hGX, show X + Surreal.mk b - (X + Y) = Surreal.mk b - Y by ring]
      exact hHr b hb

/-- **Limit-stage canonical sums are coarsely representable** at any class bounding the classes
of all the terms: the transfinite option game `optionGameO t γ` represents `hahnSumO t γ`, and
its option at stage `β` sits at distance of class exactly `mk (t β)`. -/
theorem coarseRep_hahnSumO_of_isSuccLimit {t : Ordinal.{u} → Surreal.{u}} {γ : Ordinal.{u}}
    (hγ : IsSuccLimit γ) (ht : IsStrictDom t γ) {c : ArchimedeanClass Surreal.{u}}
    (hc : ∀ β < γ, ArchimedeanClass.mk (t β) ≤ c) : CoarseRep (hahnSumO t γ) c := by
  haveI := numeric_optionGameO hγ ht
  have hS : IsHahnSumO t γ (hahnSumO t γ) := isHahnSumO_hahnSumO ht
  refine ⟨optionGameO t γ, inferInstance, mk_optionGameO_eq_hahnSumO hγ ht, ?_, ?_⟩
  · intro a ha _
    rw [leftMoves_optionGameO] at ha
    obtain ⟨⟨β, hβ⟩, rfl⟩ := ha
    rw [out_eq, (sub_optLoO_pos_mk_eq ht hS (hγ.add_one_lt_of_ordinal hβ)).2]
    exact hc β hβ
  · intro b hb _
    rw [rightMoves_optionGameO] at hb
    obtain ⟨⟨β, hβ⟩, rfl⟩ := hb
    rw [out_eq, (optHiO_sub_pos_mk_eq ht hS (hγ.add_one_lt_of_ordinal hβ)).2]
    exact hc β hβ

private theorem coarseRep_hahnSumO_aux (t : Ordinal.{u} → Surreal.{u})
    (c : ArchimedeanClass Surreal.{u}) (α : Ordinal.{u}) :
    IsStrictDom t α → (∀ β < α, ArchimedeanClass.mk (t β) ≤ c) →
    (∀ β < α, CoarseRep (t β) c) → CoarseRep (hahnSumO t α) c := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro _ _ _
    rw [hahnSumO_zero]
    exact coarseRep_zero c
  | add_one δ ih =>
    intro ht hc hrep
    have hδ : δ < δ + 1 := lt_add_one_iff.2 le_rfl
    rw [hahnSumO_add_one]
    exact (ih (ht.mono hδ.le) (fun β hβ ↦ hc β (hβ.trans hδ))
      (fun β hβ ↦ hrep β (hβ.trans hδ))).add (hrep δ hδ)
  | limit γ hγ _ =>
    intro ht hc _
    exact coarseRep_hahnSumO_of_isSuccLimit hγ ht hc

/-- **Canonical sums of every length are coarsely representable**: if every term of a strictly
dominating series below `α` is coarsely representable at `c` and has class `≤ c`, then so is the
canonical sum `hahnSumO t α`. Induction on `α`: sums at successors, the transfinite option game
at limits. -/
theorem coarseRep_hahnSumO {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    (ht : IsStrictDom t α) {c : ArchimedeanClass Surreal.{u}}
    (hc : ∀ β < α, ArchimedeanClass.mk (t β) ≤ c) (hrep : ∀ β < α, CoarseRep (t β) c) :
    CoarseRep (hahnSumO t α) c :=
  coarseRep_hahnSumO_aux t c α ht hc hrep

/-! ### Shifted series -/

/-- Strict domination below `α + β` restricts to the shifted second block `δ ↦ t (α + δ)`
below `β`. -/
theorem IsStrictDom.shift {t : Ordinal.{u} → Surreal.{u}} {α β : Ordinal.{u}}
    (ht : IsStrictDom t (α + β)) : IsStrictDom (fun δ ↦ t (α + δ)) β :=
  fun _ _ h12 h2 ↦ ht ((add_lt_add_iff_left α).2 h12) ((add_lt_add_iff_left α).2 h2)

/-! ### THE CONCATENATION THEOREM -/

private theorem hahnSumO_concat_aux (t t' : Ordinal.{u} → Surreal.{u}) (α : Ordinal.{u})
    (ht'eq : ∀ δ, t' δ = t (α + δ)) (β : Ordinal.{u}) :
    IsStrictDom t (α + β) → (0 < β → CoarseRep (hahnSumO t α) (ArchimedeanClass.mk (t α))) →
    hahnSumO t (α + β) = hahnSumO t α + hahnSumO t' β := by
  induction β using Ordinal.limitRecOn with
  | zero =>
    intro _ _
    rw [add_zero, hahnSumO_zero, add_zero]
  | add_one δ ih =>
    intro ht hX
    have hδ : δ < δ + 1 := lt_add_one_iff.2 le_rfl
    rw [← add_assoc, hahnSumO_add_one, hahnSumO_add_one,
      ih (ht.mono (add_le_add_right hδ.le α)) (fun h0 ↦ hX (h0.trans hδ)), ht'eq, add_assoc]
  | limit β' hβ' ih =>
    intro ht hX
    have h0β : 0 < β' := hβ'.pos
    have hX := hX h0β
    have hγ : IsSuccLimit (α + β') := Ordinal.isSuccLimit_add α hβ'
    have ht' : IsStrictDom t' β' := by
      intro δ₁ δ₂ h12 h2
      rw [ht'eq, ht'eq]
      exact ht ((add_lt_add_iff_left α).2 h12) ((add_lt_add_iff_left α).2 h2)
    have hXα : IsHahnSumO t α (hahnSumO t α) := isHahnSumO_hahnSumO (ht.mono le_self_add)
    have hY : IsHahnSumO t' β' (hahnSumO t' β') := isHahnSumO_hahnSumO ht'
    have hV : ∀ δ < β', hahnSumO t (α + δ) = hahnSumO t α + hahnSumO t' δ := fun δ hδ ↦
      ih δ hδ (ht.mono (add_le_add_right hδ.le α)) (fun _ ↦ hX)
    obtain ⟨GX, hGXn, hGX, hGXl, hGXr⟩ := hX
    haveI := hGXn
    haveI := numeric_optionGameO hβ' ht'
    have h1β : 1 < β' := by
      have := hβ'.add_one_lt_of_ordinal h0β
      rwa [zero_add] at this
    have hα1 : α + 1 < α + β' := (add_lt_add_iff_left α).2 h1β
    have hαβ : α < α + β' := lt_add_of_pos_right α h0β
    -- The value `X + Y` is a Hahn sum of the whole series: at stages below `α` the residual is
    -- the first block's residual plus `Y`, which is finer than every first-block term; at stages
    -- `α + δ` it is the second block's residual, by the induction hypothesis on the anchors.
    have hP : IsHahnSumO t (α + β') (hahnSumO t α + hahnSumO t' β') := by
      intro ζ hζ
      rcases lt_or_ge ζ α with hζα | hαζ
      · have h1 : hahnSumO t α + hahnSumO t' β' - hahnSumO t ζ =
            (hahnSumO t α - hahnSumO t ζ) + hahnSumO t' β' := by ring
        rw [h1]
        refine le_trans (le_min (hXα ζ hζα) ?_) (ArchimedeanClass.min_le_mk_add ..)
        have h2 := hY 0 h0β
        rw [hahnSumO_zero, sub_zero, ht'eq, add_zero] at h2
        exact (ht hζα hαβ).le.trans h2
      · obtain ⟨δ, rfl⟩ : ∃ δ, ζ = α + δ := ⟨ζ - α, (Ordinal.add_sub_cancel_of_le hαζ).symm⟩
        have hδ : δ < β' := (add_lt_add_iff_left α).1 hζ
        rw [hV δ hδ, show hahnSumO t α + hahnSumO t' β' - (hahnSumO t α + hahnSumO t' δ) =
          hahnSumO t' β' - hahnSumO t' δ by ring, ← ht'eq]
        exact hY δ hδ
    have hG : Surreal.mk (GX + optionGameO t' β') = hahnSumO t α + hahnSumO t' β' := by
      rw [Surreal.mk_add, hGX, mk_optionGameO_eq_hahnSumO hβ' ht']
    rw [← hG]
    refine hahnSumO_eq_of_isHahnSumO_of_moves_le hγ ht (by rwa [hG]) ?_ ?_
    · rw [forall_moves_add]
      constructor
      · -- coarse options of the first block, beaten at stage `α + 1`
        intro a ha
        haveI := IGame.Numeric.of_mem_moves ha
        refine ⟨α + 1, hα1, ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, mk_optionGameO_eq_hahnSumO hβ' ht']
        have hpos : 0 < hahnSumO t α - Surreal.mk a := by
          rw [sub_pos, ← hGX]
          exact Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt ha)
        have hmk : ArchimedeanClass.mk (hahnSumO t α - Surreal.mk a) <
            ArchimedeanClass.mk (t (α + 1)) :=
          (hGXl a ha).trans_lt (ht (lt_add_one_iff.2 le_rfl) hα1)
        have key := sub_le_optLoO_of_mk_lt ht hP hpos (hγ.add_one_lt_of_ordinal hα1) hmk
        rw [show Surreal.mk a + hahnSumO t' β' =
          hahnSumO t α + hahnSumO t' β' - (hahnSumO t α - Surreal.mk a) by ring]
        exact key
      · -- options of the second block's option game, beaten at stage `α + δ + 1`
        intro b hb
        rw [leftMoves_optionGameO] at hb
        obtain ⟨⟨δ, hδ⟩, rfl⟩ := hb
        have hδ1 : α + δ + 1 < α + β' := by
          rw [add_assoc]
          exact (add_lt_add_iff_left α).2 (hβ'.add_one_lt_of_ordinal hδ)
        refine ⟨α + δ + 1, hδ1, ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, hGX]
        obtain ⟨hDpos, hDmk⟩ := sub_optLoO_pos_mk_eq ht' hY (hβ'.add_one_lt_of_ordinal hδ)
        have hmk : ArchimedeanClass.mk (hahnSumO t' β' - optLoO t' δ) <
            ArchimedeanClass.mk (t (α + δ + 1)) := by
          rw [hDmk, ht'eq]
          exact ht (lt_add_one_iff.2 le_rfl) hδ1
        have key := sub_le_optLoO_of_mk_lt ht hP hDpos (hγ.add_one_lt_of_ordinal hδ1) hmk
        rw [show hahnSumO t α + optLoO t' δ =
          hahnSumO t α + hahnSumO t' β' - (hahnSumO t' β' - optLoO t' δ) by ring]
        exact key
    · rw [forall_moves_add]
      constructor
      · intro a ha
        haveI := IGame.Numeric.of_mem_moves ha
        refine ⟨α + 1, hα1, ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, mk_optionGameO_eq_hahnSumO hβ' ht']
        have hpos : 0 < Surreal.mk a - hahnSumO t α := by
          rw [sub_pos, ← hGX]
          exact Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right ha)
        have hmk : ArchimedeanClass.mk (Surreal.mk a - hahnSumO t α) <
            ArchimedeanClass.mk (t (α + 1)) :=
          (hGXr a ha).trans_lt (ht (lt_add_one_iff.2 le_rfl) hα1)
        have key := optHiO_le_add_of_mk_lt ht hP hpos (hγ.add_one_lt_of_ordinal hα1) hmk
        rw [show Surreal.mk a + hahnSumO t' β' =
          hahnSumO t α + hahnSumO t' β' + (Surreal.mk a - hahnSumO t α) by ring]
        exact key
      · intro b hb
        rw [rightMoves_optionGameO] at hb
        obtain ⟨⟨δ, hδ⟩, rfl⟩ := hb
        have hδ1 : α + δ + 1 < α + β' := by
          rw [add_assoc]
          exact (add_lt_add_iff_left α).2 (hβ'.add_one_lt_of_ordinal hδ)
        refine ⟨α + δ + 1, hδ1, ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, hGX]
        obtain ⟨hDpos, hDmk⟩ := optHiO_sub_pos_mk_eq ht' hY (hβ'.add_one_lt_of_ordinal hδ)
        have hmk : ArchimedeanClass.mk (optHiO t' δ - hahnSumO t' β') <
            ArchimedeanClass.mk (t (α + δ + 1)) := by
          rw [hDmk, ht'eq]
          exact ht (lt_add_one_iff.2 le_rfl) hδ1
        have key := optHiO_le_add_of_mk_lt ht hP hDpos (hγ.add_one_lt_of_ordinal hδ1) hmk
        rw [show hahnSumO t α + optHiO t' δ =
          hahnSumO t α + hahnSumO t' β' + (optHiO t' δ - hahnSumO t' β') by ring]
        exact key

/-- **THE CONCATENATION THEOREM**: for a series `t` strictly dominating below `α + β` whose
first-block canonical sum `hahnSumO t α` is coarsely representable at the class of the first
term `t α` of the second block, the canonical sum splits at `α`:
`hahnSumO t (α + β) = hahnSumO t α + hahnSumO (fun δ ↦ t (α + δ)) β`.

Proof: transfinite induction on `β`. Zero and successor stages are algebra. At a limit stage
`β'` the transfinite identification engine is applied at stage `α + β'` to the Conway sum of a
coarse representative `G_X` of the first block and the transfinite option game of the shifted
second block: its value `X + Y` is a Hahn sum of the whole series, the options of `G_X` differ
from it by a positive quantity of class `≤ mk (t α) < mk (t (α + 1))` and are beaten at stage
`α + 1`, and the options of the option game differ by a quantity of class `mk (t (α + δ))` and
are beaten at stage `α + δ + 1`.

The hypothesis is only needed when `0 < β`; it is **necessary** in general — see the
boundary theorem `exists_isStrictDom_hahnSumO_ne_concat` at the end of the file — and it holds
unconditionally for normal-form series (`hahnSumO_concat_of_monomial`). -/
theorem hahnSumO_concat {t : Ordinal.{u} → Surreal.{u}} {α β : Ordinal.{u}}
    (ht : IsStrictDom t (α + β))
    (hX : 0 < β → CoarseRep (hahnSumO t α) (ArchimedeanClass.mk (t α))) :
    hahnSumO t (α + β) = hahnSumO t α + hahnSumO (fun δ ↦ t (α + δ)) β :=
  hahnSumO_concat_aux t (fun δ ↦ t (α + δ)) α (fun _ ↦ rfl) β ht hX

/-- The concatenation theorem with the coarse-representability hypothesis unguarded. -/
theorem hahnSumO_concat' {t : Ordinal.{u} → Surreal.{u}} {α β : Ordinal.{u}}
    (ht : IsStrictDom t (α + β))
    (hX : CoarseRep (hahnSumO t α) (ArchimedeanClass.mk (t α))) :
    hahnSumO t (α + β) = hahnSumO t α + hahnSumO (fun δ ↦ t (α + δ)) β :=
  hahnSumO_concat ht fun _ ↦ hX

/-! ### Monomials are coarsely representable -/

/-- A strictly finer perturbation does not change the class: `mk (x − y) = mk x` when
`mk x < mk y`. -/
private theorem mk_sub_eq_mk_left' {x y : Surreal.{u}}
    (h : ArchimedeanClass.mk x < ArchimedeanClass.mk y) :
    ArchimedeanClass.mk (x - y) = ArchimedeanClass.mk x := by
  rw [sub_eq_add_neg, ArchimedeanClass.mk_add_eq_mk_left]
  rwa [ArchimedeanClass.mk_neg]

/-- The class of a positive dyadic multiple of an `ω`-power is the class of the `ω`-power. -/
private theorem mk_dyadic_mul_wpow {r : Dyadic} (hr : 0 < r) (z : Surreal.{u}) :
    ArchimedeanClass.mk (((r : ℚ) : Surreal) * ω^ z) = ArchimedeanClass.mk (ω^ z) := by
  rw [ArchimedeanClass.mk_mul, ← Real.toSurreal_ratCast, mk_realCast, zero_add]
  exact_mod_cast hr.ne'

/-- **The `ω`-power game is coarsely representable at its own class**: the options of the game
`ω^ y` are `0`, `r · ω^ yᴸ` (strictly finer than `ω^ y`, so at distance of class exactly
`mk (ω^ y)`) and `r · ω^ yᴿ` (strictly coarser). -/
theorem CoarseRep.wpow (y : Surreal.{u}) : CoarseRep (ω^ y) (ArchimedeanClass.mk (ω^ y)) := by
  refine ⟨ω^ y.out, inferInstance, by rw [Surreal.mk_wpow, out_eq], ?_, ?_⟩
  · rw [forall_leftMoves_wpow]
    constructor
    · intro _
      rw [show Surreal.mk (0 : IGame) = 0 from rfl, sub_zero]
    · intro r hr z hz _
      haveI := IGame.Numeric.of_mem_moves hz
      rw [Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow]
      have hzy : Surreal.mk z < y := by
        have := Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt hz)
        rwa [out_eq] at this
      have hlt : ArchimedeanClass.mk (ω^ y) <
          ArchimedeanClass.mk (((r : ℚ) : Surreal) * ω^ (Surreal.mk z)) := by
        rw [mk_dyadic_mul_wpow hr]
        exact archimedeanClassMk_wpow_strictAnti hzy
      exact (mk_sub_eq_mk_left' hlt).le
  · rw [forall_rightMoves_wpow]
    intro r hr z hz _
    haveI := IGame.Numeric.of_mem_moves hz
    rw [Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow]
    have hyz : y < Surreal.mk z := by
      have := Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right hz)
      rwa [out_eq] at this
    have hlt : ArchimedeanClass.mk (((r : ℚ) : Surreal) * ω^ (Surreal.mk z)) <
        ArchimedeanClass.mk (ω^ y) := by
      rw [mk_dyadic_mul_wpow hr]
      exact archimedeanClassMk_wpow_strictAnti hyz
    rw [mk_sub_eq_mk_left' hlt]
    exact hlt.le

/-- The difference of a real and a dyadic other than it has class `0`. -/
private theorem mk_realCast_sub_dyadic {r : ℝ} {q : Dyadic} (h : ((q : ℚ) : ℝ) ≠ r) :
    ArchimedeanClass.mk ((r : Surreal.{u}) - ((q : ℚ) : Surreal)) = 0 := by
  rw [← Real.toSurreal_ratCast, ← Real.toSurreal_sub]
  exact mk_realCast (sub_ne_zero.2 h.symm)

/-- The product option `a·X + r·b − a·b` of the game `r · G` (with `a` a dyadic option of the
real `r` and `b` an option of `G`) differs from `r · X` by `(r − a)(X − b)`, of class
`mk (X − b)`. -/
private theorem mk_mulOption_le {r : ℝ} {q : Dyadic} (hq : ((q : ℚ) : ℝ) ≠ r) {X b : Surreal.{u}}
    {c : ArchimedeanClass Surreal.{u}} (hb : ArchimedeanClass.mk (X - b) ≤ c) :
    ArchimedeanClass.mk ((r : Surreal) * X -
      (((q : ℚ) : Surreal) * X + (r : Surreal) * b - ((q : ℚ) : Surreal) * b)) ≤ c ∧
    ArchimedeanClass.mk ((((q : ℚ) : Surreal) * X + (r : Surreal) * b - ((q : ℚ) : Surreal) * b) -
      (r : Surreal) * X) ≤ c := by
  have h1 : (r : Surreal) * X -
      (((q : ℚ) : Surreal) * X + (r : Surreal) * b - ((q : ℚ) : Surreal) * b) =
      ((r : Surreal) - ((q : ℚ) : Surreal)) * (X - b) := by ring
  have h2 : (((q : ℚ) : Surreal) * X + (r : Surreal) * b - ((q : ℚ) : Surreal) * b) -
      (r : Surreal) * X = -(((r : Surreal) - ((q : ℚ) : Surreal)) * (X - b)) := by ring
  rw [h1, h2, ArchimedeanClass.mk_neg, ArchimedeanClass.mk_mul, mk_realCast_sub_dyadic hq,
    zero_add]
  exact ⟨hb, hb⟩

/-- **Real multiples**: coarse representatives are closed under multiplication by the game of
any real. Each option of the Conway product `r · G` is a `mulOption` differing from `r·X` by
`(r − a)(X − b)` with `r − a` a nonzero real (`a` a dyadic option of `r`), hence of class
`mk (X − b) ≤ c`. -/
theorem CoarseRep.realCast_mul {X : Surreal.{u}} {c : ArchimedeanClass Surreal.{u}}
    (hX : CoarseRep X c) (r : ℝ) : CoarseRep ((r : Surreal) * X) c := by
  obtain ⟨G, hG, hGX, hGl, hGr⟩ := hX
  refine ⟨(r : IGame) * G, inferInstance,
    by rw [Surreal.mk_mul, Surreal.mk_real_toIGame, hGX], ?_, ?_⟩
  · rw [forall_moves_mul]
    intro p
    cases p with
    | left =>
      intro a ha b hb _
      rw [Player.left_mul] at hb
      rw [Real.leftMoves_toIGame] at ha
      obtain ⟨q, hq, rfl⟩ := ha
      have hq' : ((q : ℚ) : ℝ) < r := hq
      haveI := IGame.Numeric.of_mem_moves hb
      rw [Surreal.mk_mulOption, Surreal.mk_real_toIGame, hGX, Surreal.mk_dyadic]
      exact (mk_mulOption_le hq'.ne (hGl b hb)).1
    | right =>
      intro a ha b hb _
      rw [Player.right_mul, Player.neg_left] at hb
      rw [Real.rightMoves_toIGame] at ha
      obtain ⟨q, hq, rfl⟩ := ha
      have hq' : r < ((q : ℚ) : ℝ) := hq
      haveI := IGame.Numeric.of_mem_moves hb
      rw [Surreal.mk_mulOption, Surreal.mk_real_toIGame, hGX, Surreal.mk_dyadic]
      refine (mk_mulOption_le hq'.ne' ?_).1
      rw [ArchimedeanClass.mk_sub_comm]
      exact hGr b hb
  · rw [forall_moves_mul]
    intro p
    cases p with
    | left =>
      intro a ha b hb _
      rw [Player.left_mul] at hb
      rw [Real.leftMoves_toIGame] at ha
      obtain ⟨q, hq, rfl⟩ := ha
      have hq' : ((q : ℚ) : ℝ) < r := hq
      haveI := IGame.Numeric.of_mem_moves hb
      rw [Surreal.mk_mulOption, Surreal.mk_real_toIGame, hGX, Surreal.mk_dyadic]
      refine (mk_mulOption_le hq'.ne ?_).2
      rw [ArchimedeanClass.mk_sub_comm]
      exact hGr b hb
    | right =>
      intro a ha b hb _
      rw [Player.right_mul, Player.neg_right] at hb
      rw [Real.rightMoves_toIGame] at ha
      obtain ⟨q, hq, rfl⟩ := ha
      have hq' : r < ((q : ℚ) : ℝ) := hq
      haveI := IGame.Numeric.of_mem_moves hb
      rw [Surreal.mk_mulOption, Surreal.mk_real_toIGame, hGX, Surreal.mk_dyadic]
      exact (mk_mulOption_le hq'.ne' (hGl b hb)).2

/-- **Normal-form monomials are coarsely representable at their own class**: for every real
`r` and surreal `y`, `r · ω^ y` is coarsely representable at `mk (ω^ y)`. -/
theorem coarseRep_monomial (r : ℝ) (y : Surreal.{u}) :
    CoarseRep ((r : Surreal) * ω^ y) (ArchimedeanClass.mk (ω^ y)) :=
  (CoarseRep.wpow y).realCast_mul r

/-- Every real is coarsely representable at the class `0` of the reals. -/
theorem coarseRep_realCast (r : ℝ) : CoarseRep (r : Surreal.{u}) 0 := by
  have h := coarseRep_monomial.{u} r 0
  rwa [wpow_zero, mul_one, ArchimedeanClass.mk_one] at h

/-- **Concatenation holds unconditionally for normal-form series**: for a series of monomials
`r_ζ · ω^(y_ζ)` with nonzero real coefficients and strictly decreasing exponents below
`α + β`, the canonical sum splits at `α`. The first block's canonical sum is coarsely
representable at the class of the first term of the second block by `coarseRep_hahnSumO` and
`coarseRep_monomial`. -/
theorem hahnSumO_concat_of_monomial {α β : Ordinal.{u}} {y : Ordinal.{u} → Surreal.{u}}
    {r : Ordinal.{u} → ℝ} (hy : ∀ ⦃ζ η⦄, ζ < η → η < α + β → y η < y ζ)
    (hr : ∀ ζ < α + β, r ζ ≠ 0) :
    hahnSumO (fun ζ ↦ (r ζ : Surreal.{u}) * ω^ (y ζ)) (α + β) =
      hahnSumO (fun ζ ↦ (r ζ : Surreal.{u}) * ω^ (y ζ)) α +
        hahnSumO (fun δ ↦ (r (α + δ) : Surreal.{u}) * ω^ (y (α + δ))) β := by
  have ht := isStrictDom_omegaPow hy hr
  refine hahnSumO_concat ht fun hβ ↦ ?_
  have hαβ : α < α + β := lt_add_of_pos_right α hβ
  refine coarseRep_hahnSumO (ht.mono le_self_add) (fun ζ hζ ↦ (ht hζ hαβ).le) fun ζ hζ ↦ ?_
  refine (coarseRep_monomial (r ζ) (y ζ)).mono ?_
  show ArchimedeanClass.mk (ω^ (y ζ)) ≤ ArchimedeanClass.mk ((r α : Surreal) * ω^ (y α))
  rw [ArchimedeanClass.mk_mul, mk_realCast (hr α hαβ), zero_add]
  exact (archimedeanClassMk_wpow_strictAnti (hy hζ hαβ)).le

/-! ### Halo simplicity of canonical sums -/

/-- A point whose distance from a Hahn sum is dominated by every term is again a Hahn sum. -/
theorem IsHahnSum.of_mk_sub_le {t : ℕ → Surreal.{u}} {x y : Surreal.{u}} (hx : IsHahnSum t x)
    (h : ∀ n, ArchimedeanClass.mk (t n) ≤ ArchimedeanClass.mk (y - x)) : IsHahnSum t y := by
  intro n
  rw [show y - partialSum t n = (y - x) + (x - partialSum t n) by ring]
  exact le_trans (le_min (h n) (hx n)) (ArchimedeanClass.min_le_mk_add ..)

/-- **Canonical sums are halo-simple**: at any scale `ε` such that every term of the series is
strictly coarser than some power of `ε`, the canonical sum `hahnSum t` is the birthday-simplest
point of its own deep halo — every point of the deep halo is again a Hahn sum, and the
canonical sum is the birthday-minimal Hahn sum. -/
theorem haloSimple_hahnSum {t : ℕ → Surreal.{u}}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) {ε : Surreal.{u}}
    (hcof : ∀ n, ∃ N : ℕ, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (ε ^ N)) :
    HaloSimple ε (hahnSum ht) := by
  intro z hz
  refine birthday_hahnSum_le ht ((isHahnSum_hahnSum ht).of_mk_sub_le fun n ↦ ?_)
  obtain ⟨N, hN⟩ := hcof n
  exact (hN.trans (hz N)).le

/-- The transfinite version: at a limit stage, the canonical sum is halo-simple at any scale
some power of which is finer than each term. -/
theorem haloSimple_hahnSumO {t : Ordinal.{u} → Surreal.{u}} {γ : Ordinal.{u}}
    (hγ : IsSuccLimit γ) (ht : IsStrictDom t γ) {ε : Surreal.{u}}
    (hcof : ∀ β < γ, ∃ N : ℕ, ArchimedeanClass.mk (t β) < ArchimedeanClass.mk (ε ^ N)) :
    HaloSimple ε (hahnSumO t γ) := by
  intro z hz
  refine birthday_hahnSumO_le hγ (ht.ne_zero_of_isSuccLimit hγ) fun β hβ ↦ ?_
  have hS := isHahnSumO_hahnSumO ht β hβ
  rw [show z - hahnSumO t β = (z - hahnSumO t γ) + (hahnSumO t γ - hahnSumO t β) by ring]
  obtain ⟨N, hN⟩ := hcof β hβ
  exact le_trans (le_min (hN.trans (hz N)).le hS) (ArchimedeanClass.min_le_mk_add ..)

/-! ### `ℕ`-indexed series as ordinal-indexed series -/

/-- An `ℕ`-indexed series read as an ordinal-indexed one (junk value `0` at stages `≥ ω`). -/
def ofSeq (s : ℕ → Surreal.{u}) (β : Ordinal.{u}) : Surreal.{u} :=
  if h : β < Ordinal.omega0 then s (Classical.choose (Ordinal.lt_omega0.1 h)) else 0

@[simp]
theorem ofSeq_natCast (s : ℕ → Surreal.{u}) (n : ℕ) : ofSeq s n = s n := by
  have h : (n : Ordinal.{u}) < Ordinal.omega0 := Ordinal.natCast_lt_omega0 n
  rw [ofSeq, dif_pos h]
  congr 1
  exact Nat.cast_injective (Classical.choose_spec (Ordinal.lt_omega0.1 h)).symm

theorem ofSeq_zero (s : ℕ → Surreal.{u}) : ofSeq s 0 = s 0 := by
  have := ofSeq_natCast s 0
  rwa [Nat.cast_zero] at this

theorem ofSeq_one (s : ℕ → Surreal.{u}) : ofSeq s 1 = s 1 := by
  have := ofSeq_natCast s 1
  rwa [Nat.cast_one] at this

/-- The shifted series `δ ↦ ofSeq s (1 + δ)` at finite stages is the shift `n ↦ s (n + 1)`. -/
theorem ofSeq_one_add_natCast (s : ℕ → Surreal.{u}) (n : ℕ) :
    ofSeq s (1 + n) = s (n + 1) := by
  rw [← Nat.cast_add_one_comm, ← Nat.cast_add_one, ofSeq_natCast]

theorem isStrictDom_ofSeq {s : ℕ → Surreal.{u}}
    (hs : ∀ n, ArchimedeanClass.mk (s n) < ArchimedeanClass.mk (s (n + 1))) :
    IsStrictDom (ofSeq s) Ordinal.omega0 := by
  intro β γ hβγ hγ
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hγ
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.1 (hβγ.trans hγ)
  rw [ofSeq_natCast, ofSeq_natCast]
  exact strictMono_nat_of_lt_succ hs (Nat.cast_lt.1 hβγ)

private theorem hahnSum_ext {s s' : ℕ → Surreal.{u}} (h : s = s')
    (hs : ∀ n, ArchimedeanClass.mk (s n) < ArchimedeanClass.mk (s (n + 1)))
    (hs' : ∀ n, ArchimedeanClass.mk (s' n) < ArchimedeanClass.mk (s' (n + 1))) :
    hahnSum hs = hahnSum hs' := by
  subst h; rfl

/-- The canonical sum at `ω` of an `ℕ`-indexed series read as an ordinal-indexed one is its
canonical sum `hahnSum`. -/
theorem hahnSumO_ofSeq_omega0 {s : ℕ → Surreal.{u}}
    (hs : ∀ n, ArchimedeanClass.mk (s n) < ArchimedeanClass.mk (s (n + 1))) :
    hahnSumO (ofSeq s) Ordinal.omega0 = hahnSum hs := by
  rw [hahnSumO_omega0 (isStrictDom_ofSeq hs)]
  exact hahnSum_ext (funext fun n ↦ ofSeq_natCast s n) _ _

theorem hahnSumO_ofSeq_one (s : ℕ → Surreal.{u}) : hahnSumO (ofSeq s) 1 = s 0 := by
  rw [← zero_add (1 : Ordinal.{u}), hahnSumO_add_one, hahnSumO_zero, zero_add, ofSeq_zero]

/-- The canonical sum at `ω` of the shifted series `δ ↦ ofSeq s (1 + δ)` is the canonical sum
of the shift `n ↦ s (n + 1)`. -/
theorem hahnSumO_ofSeq_shift_omega0 {s : ℕ → Surreal.{u}}
    (hs : ∀ n, ArchimedeanClass.mk (s n) < ArchimedeanClass.mk (s (n + 1))) :
    hahnSumO (fun δ ↦ ofSeq s (1 + δ)) Ordinal.omega0 =
      hahnSum (t := fun n ↦ s (n + 1)) (fun n ↦ hs (n + 1)) := by
  have ht : IsStrictDom (fun δ ↦ ofSeq s (1 + δ)) Ordinal.omega0 := by
    refine IsStrictDom.shift (α := 1) ?_
    rw [Ordinal.one_add_omega0]
    exact isStrictDom_ofSeq hs
  rw [hahnSumO_omega0 ht]
  exact hahnSum_ext (funext fun n ↦ ofSeq_one_add_natCast s n) _ _

/-- **The `ω`-length shift law**: `hahnSum t = t 0 + hahnSum (n ↦ t (n + 1))` whenever the
first term is coarsely representable at the class of the second — the concatenation theorem
at `α = 1`, `β = ω`, read through `ofSeq`. -/
theorem hahnSum_eq_add_hahnSum_shift {s : ℕ → Surreal.{u}}
    (hs : ∀ n, ArchimedeanClass.mk (s n) < ArchimedeanClass.mk (s (n + 1)))
    (hX : CoarseRep (s 0) (ArchimedeanClass.mk (s 1))) :
    hahnSum hs = s 0 + hahnSum (t := fun n ↦ s (n + 1)) (fun n ↦ hs (n + 1)) := by
  have ht : IsStrictDom (ofSeq s) (1 + Ordinal.omega0) := by
    rw [Ordinal.one_add_omega0]
    exact isStrictDom_ofSeq hs
  have h := hahnSumO_concat' ht (by rw [hahnSumO_ofSeq_one, ofSeq_one]; exact hX)
  rwa [Ordinal.one_add_omega0, hahnSumO_ofSeq_omega0 hs, hahnSumO_ofSeq_one,
    hahnSumO_ofSeq_shift_omega0 hs] at h

/-! ### THE BOUNDARY: why coarse representability is necessary

The series `ω⁻¹ + ω^(−ω), ω⁻², ω⁻³, …` is strictly dominating, but its canonical sum is **not**
its first term plus the canonical sum of the rest: `(ω⁻¹ + ω^(−ω)) + Y` and `ω⁻¹ + Y` (with
`Y = hahnSum (Σ ω^(−(n+2)))`) are both Hahn sums of the series, differing by `ω^(−ω)`, which is
finer than every term; the second is the canonical sum of `Σ ω^(−(n+1))` (the shift law, since
`ω⁻¹` *is* coarsely representable) and hence halo-simple at scale `ω⁻¹`; if the first were the
canonical sum it would be birthday-minimal, so both would be the halo value of one deep halo
and `ω^(−ω)` would vanish. -/

/-- The boundary series: first term `ω⁻¹ + ω^(−ω)`, then `ω⁻², ω⁻³, …`. -/
def bdSeq : ℕ → Surreal.{u}
  | 0 => ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal.{u})))
  | n + 1 => ω^ (-((n : Surreal.{u}) + 2))

/-- The tail `n ↦ bdSeq (n + 1) = ω^(−(n+2))` of the boundary series. -/
def bdTail (n : ℕ) : Surreal.{u} := bdSeq (n + 1)

/-- The clean series `Σ ω^(−(n+1)) = ω⁻¹ + ω⁻² + ⋯`: the first term `ω⁻¹` followed by the tail
of the boundary series. -/
def bdClean : ℕ → Surreal.{u}
  | 0 => ω^ (-1 : Surreal.{u})
  | n + 1 => bdTail n

theorem bdSeq_zero : bdSeq 0 = ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal.{u}))) := rfl

theorem bdSeq_succ (n : ℕ) : bdSeq (n + 1) = ω^ (-((n : Surreal.{u}) + 2)) := rfl

private theorem mk_wpow_lt_mk_wpow {a b : Surreal.{u}} (h : b < a) :
    ArchimedeanClass.mk (ω^ a) < ArchimedeanClass.mk (ω^ b) :=
  archimedeanClassMk_wpow_strictAnti h

theorem mk_bdSeq_zero :
    ArchimedeanClass.mk (bdSeq 0) = ArchimedeanClass.mk (ω^ (-1 : Surreal.{u})) :=
  mk_wpow_neg_one_add_wpow_neg_omega

theorem bdSeq_strict (n : ℕ) :
    ArchimedeanClass.mk (bdSeq n) < ArchimedeanClass.mk (bdSeq (n + 1)) := by
  cases n with
  | zero =>
    rw [mk_bdSeq_zero, bdSeq_succ]
    apply mk_wpow_lt_mk_wpow
    push_cast
    norm_num
  | succ n =>
    rw [bdSeq_succ, bdSeq_succ]
    apply mk_wpow_lt_mk_wpow
    push_cast
    linarith

theorem bdTail_strict (n : ℕ) :
    ArchimedeanClass.mk (bdTail n) < ArchimedeanClass.mk (bdTail (n + 1)) :=
  bdSeq_strict (n + 1)

theorem bdClean_zero : bdClean 0 = ω^ (-1 : Surreal.{u}) := rfl

/-- The shift of the clean series is the tail of the boundary series. -/
theorem bdClean_succ (n : ℕ) : bdClean (n + 1) = bdTail n := rfl

theorem bdClean_strict (n : ℕ) :
    ArchimedeanClass.mk (bdClean n) < ArchimedeanClass.mk (bdClean (n + 1)) := by
  cases n with
  | zero =>
    rw [bdClean_zero, bdClean_succ, bdTail, bdSeq_succ]
    apply mk_wpow_lt_mk_wpow
    push_cast
    norm_num
  | succ n =>
    rw [bdClean_succ, bdClean_succ]
    exact bdTail_strict n

/-- Every term of the boundary series is strictly coarser than `ω^(−ω)`. -/
theorem mk_bdSeq_lt_mk_wpow_neg_omega (n : ℕ) :
    ArchimedeanClass.mk (bdSeq n) < ArchimedeanClass.mk (ω^ (-(ω^ (1 : Surreal.{u})))) := by
  cases n with
  | zero =>
    rw [mk_bdSeq_zero]
    have := forall_nsmul_mk_wpow_neg_one_lt.{u} 1
    rwa [one_nsmul] at this
  | succ n =>
    rw [bdSeq_succ]
    apply mk_wpow_lt_mk_wpow
    rw [neg_lt_neg_iff]
    have := natCast_lt_wpow_one.{u} (n + 2)
    push_cast at this
    exact this

/-- Partial sums of a series are the first term plus partial sums of the shift. -/
private theorem partialSum_succ' (s : ℕ → Surreal.{u}) (n : ℕ) :
    partialSum s (n + 1) = s 0 + partialSum (fun k ↦ s (k + 1)) n := by
  induction n with
  | zero => rw [partialSum_succ, partialSum_zero, partialSum_zero, zero_add, add_zero]
  | succ n ih => rw [partialSum_succ, ih, partialSum_succ, add_assoc]

/-- **Prepending a term to a Hahn sum**: if `Y` is a Hahn sum of the shift `n ↦ s (n + 1)` and
`mk (s 0) < mk (s 1)`, then `s 0 + Y` is a Hahn sum of `s`. -/
theorem IsHahnSum.cons {s : ℕ → Surreal.{u}}
    (h01 : ArchimedeanClass.mk (s 0) < ArchimedeanClass.mk (s 1)) {Y : Surreal.{u}}
    (hY : IsHahnSum (fun n ↦ s (n + 1)) Y) : IsHahnSum s (s 0 + Y) := by
  intro n
  cases n with
  | zero =>
    have h1 := hY 0
    rw [partialSum_zero, sub_zero] at h1
    rw [partialSum_zero, sub_zero, ArchimedeanClass.mk_add_eq_mk_left (h01.trans_le h1)]
  | succ n =>
    rw [partialSum_succ', show s 0 + Y - (s 0 + partialSum (fun k ↦ s (k + 1)) n) =
      Y - partialSum (fun k ↦ s (k + 1)) n by ring]
    exact hY n

/-- `ω⁻¹ + hahnSum (Σ ω^(−(n+2)))` is the canonical sum of the clean series `Σ ω^(−(n+1))`:
the shift law, with `ω⁻¹` coarsely representable at scale `ω⁻²` by `CoarseRep.wpow`. -/
theorem hahnSum_bdClean_eq :
    hahnSum bdClean_strict = ω^ (-1 : Surreal.{u}) + hahnSum bdTail_strict := by
  rw [hahnSum_eq_add_hahnSum_shift bdClean_strict ?_, bdClean_zero]
  · exact congrArg (ω^ (-1 : Surreal.{u}) + ·) (hahnSum_ext (funext bdClean_succ) _ _)
  · rw [bdClean_zero, bdClean_succ, bdTail, bdSeq_succ]
    refine (CoarseRep.wpow (-1 : Surreal.{u})).mono ?_
    apply (mk_wpow_lt_mk_wpow _).le
    push_cast
    norm_num

/-- **THE BOUNDARY**: for the series `ω⁻¹ + ω^(−ω), ω⁻², ω⁻³, …`, the canonical sum is **not**
the first term plus the canonical sum of the rest — the `ω^(−ω)` tail of the first term is
invisible to the canonical sum of the remaining series. Concatenation genuinely needs coarse
representability of the first block (`not_coarseRep_bdSeq_zero`). -/
theorem hahnSum_bdSeq_ne_add_hahnSum_shift :
    hahnSum bdSeq_strict.{u} ≠ bdSeq.{u} 0 + hahnSum bdTail_strict.{u} := by
  intro heq
  have hε : Infinitesimal (ω^ (-1 : Surreal.{u})) := infinitesimal_wpow_neg_one
  have hε0 : (0 : Surreal.{u}) < ω^ (-1 : Surreal.{u}) := wpow_pos _
  -- Both `z₁ = (ω⁻¹ + ω^(−ω)) + Y` and `z₂ = ω⁻¹ + Y` are Hahn sums of the series.
  have hz₁ : IsHahnSum bdSeq (bdSeq 0 + hahnSum bdTail_strict) :=
    IsHahnSum.cons (bdSeq_strict 0) (isHahnSum_hahnSum bdTail_strict)
  have hz₂ : IsHahnSum bdSeq (ω^ (-1 : Surreal.{u}) + hahnSum bdTail_strict) := by
    refine hz₁.of_mk_sub_le fun n ↦ ?_
    rw [show ω^ (-1 : Surreal.{u}) + hahnSum bdTail_strict - (bdSeq 0 + hahnSum bdTail_strict) =
      -ω^ (-(ω^ (1 : Surreal.{u}))) by rw [bdSeq_zero]; ring, ArchimedeanClass.mk_neg]
    exact (mk_bdSeq_lt_mk_wpow_neg_omega n).le
  -- If `z₁` were the canonical sum it would be birthday-minimal.
  have hmin : (bdSeq 0 + hahnSum bdTail_strict).birthday ≤
      (ω^ (-1 : Surreal.{u}) + hahnSum bdTail_strict).birthday :=
    ((hahnSum_eq_iff bdSeq_strict).1 heq).2 _ hz₂
  -- `z₂` is the canonical sum of the clean series, hence halo-simple at scale `ω⁻¹`.
  have hsimple : HaloSimple (ω^ (-1 : Surreal.{u}))
      (ω^ (-1 : Surreal.{u}) + hahnSum bdTail_strict) := by
    rw [← hahnSum_bdClean_eq]
    refine haloSimple_hahnSum bdClean_strict fun n ↦ ?_
    cases n with
    | zero =>
      refine ⟨2, ?_⟩
      rw [bdClean_zero, ← wpow_neg_natCast_eq_pow]
      apply mk_wpow_lt_mk_wpow
      push_cast
      norm_num
    | succ n =>
      refine ⟨n + 3, ?_⟩
      rw [bdClean_succ, bdTail, bdSeq_succ, ← wpow_neg_natCast_eq_pow]
      apply mk_wpow_lt_mk_wpow
      push_cast
      linarith
  -- `z₁` lies in the deep halo of `z₂` at scale `ω⁻¹`: they differ by `ω^(−ω)`.
  have hdeep : DeepHalo (ω^ (-1 : Surreal.{u})) (ω^ (-1 : Surreal.{u}) + hahnSum bdTail_strict)
      (bdSeq 0 + hahnSum bdTail_strict) := by
    intro N
    rw [ArchimedeanClass.mk_pow, show bdSeq 0 + hahnSum bdTail_strict -
      (ω^ (-1 : Surreal.{u}) + hahnSum bdTail_strict) = ω^ (-(ω^ (1 : Surreal.{u}))) by
        rw [bdSeq_zero]; ring]
    exact forall_nsmul_mk_wpow_neg_one_lt N
  -- So both are the halo value of the same deep halo.
  have h1 : haloValue (ω^ (-1 : Surreal.{u})) (bdSeq 0 + hahnSum bdTail_strict) hε0 =
      ω^ (-1 : Surreal.{u}) + hahnSum bdTail_strict :=
    haloValue_eq_of_deepHalo_of_haloSimple hε hε0 hdeep.symm hsimple
  have h2 : haloValue (ω^ (-1 : Surreal.{u})) (bdSeq 0 + hahnSum bdTail_strict) hε0 =
      bdSeq 0 + hahnSum bdTail_strict :=
    (haloValue_eq_iff hε hε0).2 ⟨DeepHalo.refl hε0.ne' _,
      fun z hz ↦ hmin.trans (hsimple z (hdeep.trans hz))⟩
  have h3 := h2.symm.trans h1
  rw [bdSeq_zero] at h3
  have := wpow_pos (-(ω^ (1 : Surreal.{u})))
  linarith

/-- **Coarse representability is exactly what fails**: `ω⁻¹ + ω^(−ω)` is not coarsely
representable at the class of the next term `ω⁻²` (otherwise the shift law would apply). -/
theorem not_coarseRep_bdSeq_zero :
    ¬ CoarseRep (bdSeq 0) (ArchimedeanClass.mk (bdSeq 1)) :=
  fun h ↦ hahnSum_bdSeq_ne_add_hahnSum_shift (hahnSum_eq_add_hahnSum_shift bdSeq_strict h)

/-- The same, concretely: `ω⁻¹ + ω^(−ω)` is not coarsely representable at `mk (ω⁻²)`. -/
theorem not_coarseRep_wpow_neg_one_add_wpow_neg_omega :
    ¬ CoarseRep (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal.{u}))))
      (ArchimedeanClass.mk (ω^ (-2 : Surreal.{u}))) := by
  have h := not_coarseRep_bdSeq_zero.{u}
  have e : -(((0 : ℕ) : Surreal.{u}) + 2) = -2 := by push_cast; ring
  rwa [bdSeq_zero, bdSeq_succ, e] at h

/-- The boundary in the language of the concatenation theorem: for the boundary series read as
an ordinal-indexed series, `hahnSumO t (1 + ω) ≠ hahnSumO t 1 + hahnSumO (δ ↦ t (1 + δ)) ω`. -/
theorem hahnSumO_ofSeq_bdSeq_ne_concat :
    hahnSumO (ofSeq bdSeq) (1 + Ordinal.omega0) ≠
      hahnSumO (ofSeq bdSeq) 1 + hahnSumO (fun δ ↦ ofSeq bdSeq (1 + δ)) Ordinal.omega0 := by
  rw [Ordinal.one_add_omega0, hahnSumO_ofSeq_omega0 bdSeq_strict, hahnSumO_ofSeq_one,
    hahnSumO_ofSeq_shift_omega0 bdSeq_strict]
  exact hahnSum_bdSeq_ne_add_hahnSum_shift

/-- **Concatenation fails without coarse representability**: there is a strictly dominating
series of length `1 + ω` whose canonical sum is not the canonical sum of its first block plus
the canonical sum of the shifted second block. -/
theorem exists_isStrictDom_hahnSumO_ne_concat :
    ∃ t : Ordinal.{u} → Surreal.{u}, IsStrictDom t (1 + Ordinal.omega0) ∧
      hahnSumO t (1 + Ordinal.omega0) ≠
        hahnSumO t 1 + hahnSumO (fun δ ↦ t (1 + δ)) Ordinal.omega0 :=
  ⟨ofSeq bdSeq, by rw [Ordinal.one_add_omega0]; exact isStrictDom_ofSeq bdSeq_strict,
    hahnSumO_ofSeq_bdSeq_ne_concat⟩

end Surreal

end
