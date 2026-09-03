/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.GameCofinality
import Infinity.ExpDichotomy
import Infinity.ExpNegLog
import Infinity.ExpLogGrid
import Infinity.DayOmega
import Infinity.NegGrid

/-!
# The halo game: the reflection law, and `exp ∘ log` as halo simplification

`Infinity.GameCofinality` identified products of canonical sums by one application of the
simplicity theorem to the Conway product of two option games. This file introduces a second,
even smaller game and plugs it into the same engine.

* **The deep halo** `Surreal.DeepHalo ε p z`: `z − p` is strictly finer than every power of
  the scale `ε` (`∀ N, mk (ε^N) < mk (z − p)`). It is an equivalence relation on surreals
  (`DeepHalo.refl`, `.symm`, `.trans`), and for a positive infinitesimal scale it is the
  two-sided estimate `∀ N, |z − p| < ε^N` (`deepHalo_of_forall_abs_sub_lt`,
  `DeepHalo.abs_sub_lt`).
* **The halo game** `Surreal.haloGame ε p := !{p − εᴺ ∣ p + εᴺ}` and its value
  `Surreal.haloValue ε p`. A numeric game fits the halo game iff its value lies in the deep
  halo (`fits_haloGame_iff`), so by the simplicity theorem the halo value is **the
  birthday-simplest point of the deep halo** (`haloValue_eq_iff`). `Surreal.HaloSimple ε p`
  says `p` itself is that simplest point (`haloValue_eq_self_iff`).
* **Reals are halo-simple** at every scale (`haloSimple_realCast`, `haloSimple_one`): a
  dyadic in the deep halo of a real *is* that real, and everything non-dyadic is born at day
  `ω` or later. The day-`ω` neighbours `d + ω⁻¹` are halo-simple at every scale that reaches
  `ω⁻¹` (`haloSimple_dyadic_add_wpow_neg_one`).
* **The halo identification engine** `Surreal.mk_eq_haloValue_of_moves_le`: a numeric game
  whose value lies in the deep halo of `p`, and whose options are beaten by the options
  `p ∓ εᴺ`, has value `haloValue ε p` — hence value `p` whenever `p` is halo-simple
  (`mk_eq_of_moves_le_of_haloSimple`), and value `q` whenever `q` is a halo-simple point of
  the deep halo (`mk_eq_of_moves_le_of_deepHalo_of_haloSimple`).
* **THE REFLECTION LAW** `Surreal.expInf_mul_expInf_neg`:
  `expInf σ * expInf (−σ) = 1` for **every** nonzero infinitesimal `σ`, of either sign.
  The product of the two option games has value in the deep halo of `1` at scale `|σ|`
  (truncated `E(X)·E(−X) ≡ 1 mod Xⁿ` plus the Hahn residuals), its options sit at distance of
  class `mk (σ^(m+n))` from the product, and `1` is halo-simple. Corollaries:
  `expInf_neg_eq_inv` (`expInf (−σ) = (expInf σ)⁻¹`), `expInf_pos`, and the ℤ-lattice law
  `expInf_zsmul` (`expInf (n • σ) = expInf σ ^ n` for every nonzero integer `n`).
* **EXP ∘ LOG IS HALO SIMPLIFICATION** `Surreal.expInf_eq_haloValue_of_isHahnSum_log`: for
  every nonzero infinitesimal `x` and every Hahn sum `σ` of the logarithm series at `x`,
  `expInf σ = haloValue |x| (1 + x)` — the exponential of a logarithm of `1 + x` is the
  birthday-simplest point of the deep halo of `1 + x`. The criterion
  `expInf_eq_one_add_iff_haloSimple`: `expInf σ = 1 + x ↔ HaloSimple |x| (1 + x)`; the grid
  theorem of `Infinity.ExpLogGrid` becomes the statement that `1 + a·ω⁻¹` is halo-simple
  (`haloSimple_one_add_dyadic_mul_eps0`); and at `x = ω⁻¹ + ω^(−ω)` the halo simplification
  is *visible*: `expInf σ = 1 + ω⁻¹ ≠ 1 + x` (`expInf_eq_one_add_wpow_neg_one_of_isHahnSum_log`,
  `expInf_ne_one_add_of_isHahnSum_log_wpow`).

The picture of the canonical exponential on infinitesimals is now complete: a group
homomorphism on each comparability cone (`Infinity.GameCofinality`, `Infinity.ExpDichotomy`),
inverse-closed (this file), with `exp ∘ log` = "take the simplest element of the halo".
-/

open ArchimedeanClass Finset IGame

universe u

noncomputable section

namespace Surreal

/-! ### The deep halo -/

/-- `z` lies in the **deep halo** of `p` at scale `ε`: the difference `z − p` is strictly
finer than every power of `ε`. (Recall `mk 0 = ⊤`, so `p` lies in its own deep halo whenever
`ε ≠ 0`; and `N = 0` says `z − p` is infinitesimal.) -/
def DeepHalo (ε p z : Surreal.{u}) : Prop :=
  ∀ N : ℕ, ArchimedeanClass.mk (ε ^ N) < ArchimedeanClass.mk (z - p)

theorem DeepHalo.refl {ε : Surreal.{u}} (hε0 : ε ≠ 0) (p : Surreal.{u}) : DeepHalo ε p p := by
  intro N
  rw [sub_self, ArchimedeanClass.mk_zero]
  exact lt_top_iff_ne_top.2 (ArchimedeanClass.mk_eq_top_iff.not.2 (pow_ne_zero N hε0))

theorem DeepHalo.symm {ε p z : Surreal.{u}} (h : DeepHalo ε p z) : DeepHalo ε z p := by
  intro N
  rw [ArchimedeanClass.mk_sub_comm]
  exact h N

theorem DeepHalo.trans {ε p q z : Surreal.{u}} (h1 : DeepHalo ε p q) (h2 : DeepHalo ε q z) :
    DeepHalo ε p z := by
  intro N
  have h : z - p = (z - q) + (q - p) := by ring
  rw [h]
  exact lt_of_lt_of_le (lt_min (h2 N) (h1 N)) (ArchimedeanClass.min_le_mk_add _ _)

/-- The `N = 0` instance: a point of the deep halo is infinitesimally close to the centre. -/
theorem DeepHalo.infinitesimal_sub {ε p z : Surreal.{u}} (h : DeepHalo ε p z) :
    Infinitesimal (z - p) := by
  have h0 := h 0
  rw [pow_zero, ArchimedeanClass.mk_one] at h0
  exact infinitesimal_def.2 h0

theorem DeepHalo.abs_sub_lt {ε p z : Surreal.{u}} (hε0 : 0 < ε) (h : DeepHalo ε p z) (N : ℕ) :
    |z - p| < ε ^ N := by
  have h1 := abs_lt_abs_of_mk_lt (h N)
  rwa [abs_of_pos (pow_pos hε0 N)] at h1

theorem DeepHalo.sub_lt {ε p z : Surreal.{u}} (hε0 : 0 < ε) (h : DeepHalo ε p z) (N : ℕ) :
    p - ε ^ N < z := by
  have h1 := (abs_lt.1 (h.abs_sub_lt hε0 N)).1
  linarith

theorem DeepHalo.lt_add {ε p z : Surreal.{u}} (hε0 : 0 < ε) (h : DeepHalo ε p z) (N : ℕ) :
    z < p + ε ^ N := by
  have h1 := (abs_lt.1 (h.abs_sub_lt hε0 N)).2
  linarith

/-- For a positive infinitesimal scale, the two-sided estimate `|z − p| < εᴺ` for all `N`
places `z` in the deep halo (use `N + 1` to get strictness of classes). -/
theorem deepHalo_of_forall_abs_sub_lt {ε p z : Surreal.{u}} (hε : Infinitesimal ε)
    (hε0 : 0 < ε) (h : ∀ N, |z - p| < ε ^ N) : DeepHalo ε p z := by
  intro N
  refine (mk_pow_lt_mk_pow_succ hε hε0 N).trans_le ?_
  rw [ArchimedeanClass.mk_le_mk]
  refine ⟨1, ?_⟩
  rw [one_nsmul, abs_of_pos (pow_pos hε0 _)]
  exact (h (N + 1)).le

/-! ### The halo game -/

/-- **The halo game** `!{p − εᴺ ∣ p + εᴺ}` of a surreal `p` at scale `ε`. -/
def haloGame (ε p : Surreal.{u}) : IGame.{u} :=
  !{Set.range (fun N : ℕ ↦ (p - ε ^ N).out) | Set.range (fun N : ℕ ↦ (p + ε ^ N).out)}

theorem leftMoves_haloGame (ε p : Surreal.{u}) :
    (haloGame ε p)ᴸ = Set.range (fun N : ℕ ↦ (p - ε ^ N).out) :=
  leftMoves_ofSets ..

theorem rightMoves_haloGame (ε p : Surreal.{u}) :
    (haloGame ε p)ᴿ = Set.range (fun N : ℕ ↦ (p + ε ^ N).out) :=
  rightMoves_ofSets ..

theorem sub_pow_out_mem_leftMoves_haloGame (ε p : Surreal.{u}) (N : ℕ) :
    (p - ε ^ N).out ∈ (haloGame ε p)ᴸ := by
  rw [leftMoves_haloGame]
  exact ⟨N, rfl⟩

theorem add_pow_out_mem_rightMoves_haloGame (ε p : Surreal.{u}) (N : ℕ) :
    (p + ε ^ N).out ∈ (haloGame ε p)ᴿ := by
  rw [rightMoves_haloGame]
  exact ⟨N, rfl⟩

/-- The halo game at a positive scale is numeric. -/
theorem numeric_haloGame {ε : Surreal.{u}} (hε0 : 0 < ε) (p : Surreal.{u}) :
    (haloGame ε p).Numeric := by
  refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun q y hy ↦ ?_)
  · rw [leftMoves_haloGame] at hy
    rw [rightMoves_haloGame] at hz
    obtain ⟨m, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := hz
    rw [← Surreal.mk_lt_mk, out_eq, out_eq]
    have h1 := pow_pos hε0 m
    have h2 := pow_pos hε0 n
    linarith
  · cases q with
    | left =>
      rw [haloGame, moves_ofSets] at hy
      obtain ⟨n, rfl⟩ := hy
      infer_instance
    | right =>
      rw [haloGame, moves_ofSets] at hy
      obtain ⟨n, rfl⟩ := hy
      infer_instance

/-- **A numeric game fits the halo game iff its value lies in the deep halo.** -/
theorem fits_haloGame_iff {ε p : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {x : IGame.{u}} [x.Numeric] : x.Fits (haloGame ε p) ↔ DeepHalo ε p (Surreal.mk x) := by
  constructor
  · intro hx
    refine deepHalo_of_forall_abs_sub_lt hε hε0 fun N ↦ ?_
    have h1 := hx.1 _ (sub_pow_out_mem_leftMoves_haloGame ε p N)
    have h2 := hx.2 _ (add_pow_out_mem_rightMoves_haloGame ε p N)
    rw [IGame.Numeric.not_le, ← Surreal.mk_lt_mk, out_eq] at h1
    rw [IGame.Numeric.not_le, ← Surreal.mk_lt_mk, out_eq] at h2
    exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  · intro hx
    constructor
    · intro z hz
      rw [leftMoves_haloGame] at hz
      obtain ⟨N, rfl⟩ := hz
      refine IGame.Numeric.not_le.2 ?_
      rw [← Surreal.mk_lt_mk, out_eq]
      exact hx.sub_lt hε0 N
    · intro z hz
      rw [rightMoves_haloGame] at hz
      obtain ⟨N, rfl⟩ := hz
      refine IGame.Numeric.not_le.2 ?_
      rw [← Surreal.mk_lt_mk, out_eq]
      exact hx.lt_add hε0 N

/-! ### The halo value: the simplest point of the deep halo -/

/-- **The halo value**: the surreal value of the halo game. -/
def haloValue (ε p : Surreal.{u}) (hε0 : 0 < ε) : Surreal.{u} :=
  @Surreal.mk (haloGame ε p) (numeric_haloGame hε0 p)

/-- The halo value lies in the deep halo. -/
theorem deepHalo_haloValue {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (p : Surreal.{u}) : DeepHalo ε p (haloValue ε p hε0) := by
  haveI := numeric_haloGame hε0 p
  exact (fits_haloGame_iff hε hε0).1 (Fits.refl _)

/-- The halo value is born no later than any point of the deep halo (the simplicity
theorem, value form). -/
theorem birthday_haloValue_le {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {p z : Surreal.{u}} (hz : DeepHalo ε p z) : (haloValue ε p hε0).birthday ≤ z.birthday := by
  haveI := numeric_haloGame hε0 p
  refine birthday_mk_le_of_fits ?_
  rw [fits_haloGame_iff hε hε0, out_eq]
  exact hz

/-- **The characterization of the halo value**: it is the unique point of the deep halo of
minimal birthday. -/
theorem haloValue_eq_iff {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {p q : Surreal.{u}} :
    haloValue ε p hε0 = q ↔
      DeepHalo ε p q ∧ ∀ z, DeepHalo ε p z → q.birthday ≤ z.birthday := by
  haveI := numeric_haloGame hε0 p
  constructor
  · rintro rfl
    exact ⟨deepHalo_haloValue hε hε0 p, fun z hz ↦ birthday_haloValue_le hε hε0 hz⟩
  · rintro ⟨hq, hmin⟩
    obtain ⟨g, hgn, hgq, hgb⟩ := birthday_eq_iGameBirthday q
    haveI := hgn
    have hfit : g.Fits (haloGame ε p) := by
      rw [fits_haloGame_iff hε hε0, hgq]
      exact hq
    have hequiv : g ≈ haloGame ε p := by
      refine hfit.equiv_of_forall_birthday_le fun z hzn hz ↦ ?_
      haveI := hzn
      rw [hgb]
      exact (hmin _ ((fits_haloGame_iff hε hε0).1 hz)).trans (birthday_mk_le z)
    rw [haloValue, ← hgq]
    exact (Surreal.mk_eq_mk.2 hequiv).symm

/-- `p` is **halo-simple** at scale `ε` when it is the birthday-simplest point of its own
deep halo. -/
def HaloSimple (ε p : Surreal.{u}) : Prop :=
  ∀ z, DeepHalo ε p z → p.birthday ≤ z.birthday

/-- The halo value is `p` itself iff `p` is halo-simple. -/
theorem haloValue_eq_self_iff {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {p : Surreal.{u}} : haloValue ε p hε0 = p ↔ HaloSimple ε p := by
  rw [haloValue_eq_iff hε hε0]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨DeepHalo.refl hε0.ne' p, h⟩⟩

/-- The halo value of `p` is any halo-simple point `q` of the deep halo of `p` (the deep
halos of `p` and `q` coincide). -/
theorem haloValue_eq_of_deepHalo_of_haloSimple {ε : Surreal.{u}} (hε : Infinitesimal ε)
    (hε0 : 0 < ε) {p q : Surreal.{u}} (hq : DeepHalo ε p q) (hqs : HaloSimple ε q) :
    haloValue ε p hε0 = q := by
  rw [haloValue_eq_iff hε hε0]
  exact ⟨hq, fun z hz ↦ hqs z (hq.symm.trans hz)⟩

/-! ### Reals are halo-simple -/

/-- A surreal born by day `ω` is halo-simple as soon as no dyadic other than itself enters
its deep halo: everything non-dyadic is born at day `ω` or later. -/
theorem haloSimple_of_birthday_le_omega0 {ε p : Surreal.{u}}
    (hp : p.birthday ≤ NatOrdinal.of Ordinal.omega0)
    (hd : ∀ d : Dyadic, DeepHalo ε p (d : Surreal) → (d : Surreal) = p) : HaloSimple ε p := by
  intro z hz
  rcases lt_or_ge z.birthday (NatOrdinal.of Ordinal.omega0) with h | h
  · obtain ⟨d, rfl⟩ := Surreal.birthday_lt_omega0_iff.1 h
    have hz' : DeepHalo ε p (d : Surreal) := hz
    show p.birthday ≤ (d : Surreal).birthday
    rw [hd d hz']
  · exact hp.trans h

private theorem ratCast_eq_of_infinitesimal_sub {p q : ℚ}
    (h : Infinitesimal (((p : ℚ) : Surreal.{u}) - ((q : ℚ) : Surreal))) : p = q := by
  rw [← Real.toSurreal_ratCast, ← Real.toSurreal_ratCast, ← Real.toSurreal_sub] at h
  have h2 := eq_zero_of_infinitesimal_realCast h
  have h3 : ((p : ℚ) : ℝ) = ((q : ℚ) : ℝ) := by linarith [sub_eq_zero.1 h2]
  exact_mod_cast h3

/-- **Every real is halo-simple at every scale**: a dyadic in the deep halo of `r` differs
from `r` by an infinitesimal real, hence is `r`; and `r` is born by day `ω`. -/
theorem haloSimple_realCast (ε : Surreal.{u}) (r : ℝ) : HaloSimple ε (r : Surreal) := by
  refine haloSimple_of_birthday_le_omega0 (birthday_realCast_le r) fun d hd ↦ ?_
  have h1 : (d : Surreal.{u}) = (((d : ℚ) : ℝ) : Surreal) := (Real.toSurreal_ratCast _).symm
  rw [h1] at hd ⊢
  have h2 := hd.infinitesimal_sub
  rw [← Real.toSurreal_sub] at h2
  rw [sub_eq_zero.1 (eq_zero_of_infinitesimal_realCast h2)]

/-- `1` is halo-simple at every scale. -/
theorem haloSimple_one (ε : Surreal.{u}) : HaloSimple ε 1 := by
  have h := haloSimple_realCast ε 1
  rwa [Real.toSurreal_one] at h

/-- **The day-`ω` neighbours are halo-simple** at every scale `ε` some power of which reaches
`ω⁻¹`: a dyadic `e` in the deep halo of `d + ω⁻¹` must be `d` (infinitesimal rational
difference), but `d − (d + ω⁻¹) = −ω⁻¹` is not finer than `εᴺ`. -/
theorem haloSimple_dyadic_add_wpow_neg_one {ε : Surreal.{u}} (d : Dyadic)
    (hε : ∃ N : ℕ, ArchimedeanClass.mk (ω^ (-1 : Surreal.{u})) ≤ ArchimedeanClass.mk (ε ^ N)) :
    HaloSimple ε ((d : Surreal) + ω^ (-1 : Surreal)) := by
  refine haloSimple_of_birthday_le_omega0 (birthday_dyadic_add_wpow_neg_one_le d) fun e he ↦ ?_
  exfalso
  obtain ⟨N, hN⟩ := hε
  have h0 := he.infinitesimal_sub
  have hed : Infinitesimal ((e : Surreal) - (d : Surreal)) := by
    have h : (e : Surreal) - (d : Surreal) =
        ((e : Surreal) - ((d : Surreal) + ω^ (-1 : Surreal))) + ω^ (-1 : Surreal) := by ring
    rw [h]
    exact h0.add infinitesimal_wpow_neg_one
  have hed' : (e : ℚ) = (d : ℚ) := ratCast_eq_of_infinitesimal_sub hed
  have h1 := he N
  have h2 : (e : Surreal) - ((d : Surreal) + ω^ (-1 : Surreal)) = -ω^ (-1 : Surreal) := by
    have h3 : (e : Surreal) = (d : Surreal) := by
      show ((e : ℚ) : Surreal) = ((d : ℚ) : Surreal)
      rw [hed']
    rw [h3]
    ring
  rw [h2, ArchimedeanClass.mk_neg] at h1
  exact absurd (hN.trans_lt h1) (lt_irrefl _)


/-! ### The halo identification engine -/

/-- **The halo identification engine**: a numeric game `G` whose value lies in the deep halo
of `p`, and each of whose options is beaten by some option `p ∓ εᴺ` of the halo game, has
value `haloValue ε p`. This is `IGame.Fits.equiv_of_forall_moves` (the simplicity theorem)
applied to `G` and the halo game. -/
theorem mk_eq_haloValue_of_moves_le {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {p : Surreal.{u}} {G : IGame.{u}} [G.Numeric] (hG : DeepHalo ε p (Surreal.mk G))
    (hl : ∀ a ∈ Gᴸ, ∃ N : ℕ, a ≤ (p - ε ^ N).out)
    (hr : ∀ b ∈ Gᴿ, ∃ N : ℕ, (p + ε ^ N).out ≤ b) :
    Surreal.mk G = haloValue ε p hε0 := by
  haveI := numeric_haloGame hε0 p
  have hfit : G.Fits (haloGame ε p) := (fits_haloGame_iff hε hε0).2 hG
  have hequiv : G ≈ haloGame ε p := by
    refine hfit.equiv_of_forall_moves ?_ ?_
    · intro a ha
      obtain ⟨N, hN⟩ := hl a ha
      exact ⟨(p - ε ^ N).out, sub_pow_out_mem_leftMoves_haloGame ε p N, hN⟩
    · intro b hb
      obtain ⟨N, hN⟩ := hr b hb
      exact ⟨(p + ε ^ N).out, add_pow_out_mem_rightMoves_haloGame ε p N, hN⟩
  exact Surreal.mk_eq_mk.2 hequiv

/-- The halo identification engine with the option comparisons stated at the level of
surreal values. -/
theorem mk_eq_haloValue_of_mk_moves_le {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {p : Surreal.{u}} {G : IGame.{u}} [G.Numeric] (hG : DeepHalo ε p (Surreal.mk G))
    (hl : ∀ a (ha : a ∈ Gᴸ), ∃ N : ℕ,
      @Surreal.mk a (IGame.Numeric.of_mem_moves ha) ≤ p - ε ^ N)
    (hr : ∀ b (hb : b ∈ Gᴿ), ∃ N : ℕ,
      p + ε ^ N ≤ @Surreal.mk b (IGame.Numeric.of_mem_moves hb)) :
    Surreal.mk G = haloValue ε p hε0 := by
  refine mk_eq_haloValue_of_moves_le hε hε0 hG ?_ ?_
  · intro a ha
    obtain ⟨N, hN⟩ := hl a ha
    haveI := IGame.Numeric.of_mem_moves ha
    refine ⟨N, ?_⟩
    rw [← Surreal.mk_le_mk, out_eq]
    exact hN
  · intro b hb
    obtain ⟨N, hN⟩ := hr b hb
    haveI := IGame.Numeric.of_mem_moves hb
    refine ⟨N, ?_⟩
    rw [← Surreal.mk_le_mk, out_eq]
    exact hN

/-- The engine at a halo-simple centre: the value is `p` itself. -/
theorem mk_eq_of_moves_le_of_haloSimple {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {p : Surreal.{u}} {G : IGame.{u}} [G.Numeric] (hG : DeepHalo ε p (Surreal.mk G))
    (hl : ∀ a ∈ Gᴸ, ∃ N : ℕ, a ≤ (p - ε ^ N).out)
    (hr : ∀ b ∈ Gᴿ, ∃ N : ℕ, (p + ε ^ N).out ≤ b) (hp : HaloSimple ε p) :
    Surreal.mk G = p :=
  (mk_eq_haloValue_of_moves_le hε hε0 hG hl hr).trans ((haloValue_eq_self_iff hε hε0).2 hp)

/-- The engine at a general centre: the value is any halo-simple point `q` of the deep halo. -/
theorem mk_eq_of_moves_le_of_deepHalo_of_haloSimple {ε : Surreal.{u}} (hε : Infinitesimal ε)
    (hε0 : 0 < ε) {p : Surreal.{u}} {G : IGame.{u}} [G.Numeric] (hG : DeepHalo ε p (Surreal.mk G))
    (hl : ∀ a ∈ Gᴸ, ∃ N : ℕ, a ≤ (p - ε ^ N).out)
    (hr : ∀ b ∈ Gᴿ, ∃ N : ℕ, (p + ε ^ N).out ≤ b) {q : Surreal.{u}}
    (hq : DeepHalo ε p q) (hqs : HaloSimple ε q) : Surreal.mk G = q :=
  (mk_eq_haloValue_of_moves_le hε hε0 hG hl hr).trans
    (haloValue_eq_of_deepHalo_of_haloSimple hε hε0 hq hqs)

/-! ### The option estimate at the halo scale -/

/-- **The option estimate, lower side**: if `P` lies in the deep halo of `p` and `D > 0` is
strictly coarser than `εᴺ`, then `P − D` lies below the halo option `p − εᴺ` (indeed
`(P − p) + εᴺ` is strictly finer than `D`, hence smaller in absolute value). -/
theorem sub_le_sub_pow_of_mk_lt {ε p P D : Surreal.{u}} (hP : DeepHalo ε p P) (hD : 0 < D)
    {N : ℕ} (hN : ArchimedeanClass.mk D < ArchimedeanClass.mk (ε ^ N)) :
    P - D ≤ p - ε ^ N := by
  have h1 : ArchimedeanClass.mk D < ArchimedeanClass.mk ((P - p) + ε ^ N) :=
    lt_of_lt_of_le (lt_min (hN.trans (hP N)) hN) (ArchimedeanClass.min_le_mk_add _ _)
  have h2 := abs_lt_abs_of_mk_lt h1
  rw [abs_of_pos hD] at h2
  have h3 := (abs_lt.1 h2).2
  linarith

/-- **The option estimate, upper side**. -/
theorem add_pow_le_add_of_mk_lt {ε p P D : Surreal.{u}} (hP : DeepHalo ε p P) (hD : 0 < D)
    {N : ℕ} (hN : ArchimedeanClass.mk D < ArchimedeanClass.mk (ε ^ N)) :
    p + ε ^ N ≤ P + D := by
  have h1 : ArchimedeanClass.mk D < ArchimedeanClass.mk ((P - p) - ε ^ N) :=
    lt_of_lt_of_le (lt_min (hN.trans (hP N)) hN) (ArchimedeanClass.min_le_mk_sub _ _)
  have h2 := abs_lt_abs_of_mk_lt h1
  rw [abs_of_pos hD] at h2
  have h3 := (abs_lt.1 h2).1
  linarith

private theorem pos_of_bounds' {a v : Surreal.{u}} (h1 : |a| < 2 * v) : 0 < v := by
  have := abs_nonneg a
  linarith

/-! ### Canonical sums at the halo scale -/

/-- **The sum engine at the halo scale**: a canonical sum lying in the deep halo of `p`,
each of whose terms is strictly coarser than some power of `ε`, is the halo value of `p`
(its option game's options `sₘ ∓ 2|tₘ|` sit at distance of class `mk tₘ` from the sum). -/
theorem hahnSum_eq_haloValue {t : ℕ → Surreal.{u}} {ε p : Surreal.{u}}
    (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hP : DeepHalo ε p (hahnSum ht))
    (hcof : ∀ m, ∃ N : ℕ, ArchimedeanClass.mk (t m) < ArchimedeanClass.mk (ε ^ N)) :
    hahnSum ht = haloValue ε p hε0 := by
  haveI := numeric_optionGame ht
  have hx : IsHahnSum t (hahnSum ht) := isHahnSum_hahnSum ht
  have hG : Surreal.mk (optionGame t) = hahnSum ht := mk_optionGame_eq_hahnSum ht
  rw [← hG]
  refine mk_eq_haloValue_of_moves_le hε hε0 (by rwa [hG]) ?_ ?_
  · intro a ha
    rw [leftMoves_optionGame] at ha
    obtain ⟨m, rfl⟩ := ha
    obtain ⟨N, hN⟩ := hcof m
    refine ⟨N, ?_⟩
    rw [← Surreal.mk_le_mk, out_eq, out_eq]
    have h1 := sub_optLo_bounds ht hx m
    have hDmk : ArchimedeanClass.mk (hahnSum ht - optLo t m) < ArchimedeanClass.mk (ε ^ N) := by
      rw [mk_eq_of_bounds h1.1 h1.2]; exact hN
    have key := sub_le_sub_pow_of_mk_lt hP (pos_of_bounds' h1.1) hDmk
    have hid : optLo t m = hahnSum ht - (hahnSum ht - optLo t m) := by ring
    rw [hid]
    exact key
  · intro b hb
    rw [rightMoves_optionGame] at hb
    obtain ⟨m, rfl⟩ := hb
    obtain ⟨N, hN⟩ := hcof m
    refine ⟨N, ?_⟩
    rw [← Surreal.mk_le_mk, out_eq, out_eq]
    have h1 := optHi_sub_bounds ht hx m
    have hDmk : ArchimedeanClass.mk (optHi t m - hahnSum ht) < ArchimedeanClass.mk (ε ^ N) := by
      rw [mk_eq_of_bounds h1.1 h1.2]; exact hN
    have key := add_pow_le_add_of_mk_lt hP (pos_of_bounds' h1.1) hDmk
    have hid : optHi t m = hahnSum ht + (optHi t m - hahnSum ht) := by ring
    rw [hid]
    exact key

/-- **The product engine at the halo scale**: if the product of two canonical sums lies in the
deep halo of `p`, and every product `tₘ uₙ` of terms is strictly coarser than some power of
`ε`, then the product is the halo value of `p`. Proof: the halo identification engine on the
Conway product of the two option games, whose options are `x·y ∓ D` with `D > 0` of class
`mk (tₘ uₙ)` (verbatim the option computation of
`Surreal.hahnSum_eq_mul_of_cofinal`). -/
theorem hahnSum_mul_hahnSum_eq_haloValue {t u : ℕ → Surreal.{u}} {ε p : Surreal.{u}}
    (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (hP : DeepHalo ε p (hahnSum ht * hahnSum hu))
    (hcof : ∀ m n, ∃ N : ℕ, ArchimedeanClass.mk (t m * u n) < ArchimedeanClass.mk (ε ^ N)) :
    hahnSum ht * hahnSum hu = haloValue ε p hε0 := by
  haveI := numeric_optionGame ht
  haveI := numeric_optionGame hu
  have hx : IsHahnSum t (hahnSum ht) := isHahnSum_hahnSum ht
  have hy : IsHahnSum u (hahnSum hu) := isHahnSum_hahnSum hu
  have hG : Surreal.mk (optionGame t * optionGame u) = hahnSum ht * hahnSum hu := by
    rw [Surreal.mk_mul, mk_optionGame_eq_hahnSum ht, mk_optionGame_eq_hahnSum hu]
  rw [← hG]
  refine mk_eq_haloValue_of_moves_le hε hε0 (by rwa [hG]) ?_ ?_
  · -- left options: both-left or both-right pairs
    rw [forall_moves_mul]
    intro q a ha b hb
    cases q with
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
        mul_pos (pos_of_bounds' h1.1) (pos_of_bounds' h2.1)
      have hDmk : ArchimedeanClass.mk ((hahnSum ht - optLo t m) * (hahnSum hu - optLo u n)) <
          ArchimedeanClass.mk (ε ^ N) := by
        rw [ArchimedeanClass.mk_mul, mk_eq_of_bounds h1.1 h1.2, mk_eq_of_bounds h2.1 h2.2,
          ← ArchimedeanClass.mk_mul]
        exact hN
      have key := sub_le_sub_pow_of_mk_lt hP hDpos hDmk
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
        mul_pos (pos_of_bounds' h1.1) (pos_of_bounds' h2.1)
      have hDmk : ArchimedeanClass.mk ((optHi t m - hahnSum ht) * (optHi u n - hahnSum hu)) <
          ArchimedeanClass.mk (ε ^ N) := by
        rw [ArchimedeanClass.mk_mul, mk_eq_of_bounds h1.1 h1.2, mk_eq_of_bounds h2.1 h2.2,
          ← ArchimedeanClass.mk_mul]
        exact hN
      have key := sub_le_sub_pow_of_mk_lt hP hDpos hDmk
      have hid : optHi t m * hahnSum hu + hahnSum ht * optHi u n - optHi t m * optHi u n =
          hahnSum ht * hahnSum hu -
            (optHi t m - hahnSum ht) * (optHi u n - hahnSum hu) := by ring
      rw [hid]
      exact key
  · -- right options: mixed pairs
    rw [forall_moves_mul]
    intro q a ha b hb
    cases q with
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
        mul_pos (pos_of_bounds' h1.1) (pos_of_bounds' h2.1)
      have hDmk : ArchimedeanClass.mk ((hahnSum ht - optLo t m) * (optHi u n - hahnSum hu)) <
          ArchimedeanClass.mk (ε ^ N) := by
        rw [ArchimedeanClass.mk_mul, mk_eq_of_bounds h1.1 h1.2, mk_eq_of_bounds h2.1 h2.2,
          ← ArchimedeanClass.mk_mul]
        exact hN
      have key := add_pow_le_add_of_mk_lt hP hDpos hDmk
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
        mul_pos (pos_of_bounds' h1.1) (pos_of_bounds' h2.1)
      have hDmk : ArchimedeanClass.mk ((optHi t m - hahnSum ht) * (hahnSum hu - optLo u n)) <
          ArchimedeanClass.mk (ε ^ N) := by
        rw [ArchimedeanClass.mk_mul, mk_eq_of_bounds h1.1 h1.2, mk_eq_of_bounds h2.1 h2.2,
          ← ArchimedeanClass.mk_mul]
        exact hN
      have key := add_pow_le_add_of_mk_lt hP hDpos hDmk
      have hid : optHi t m * hahnSum hu + hahnSum ht * optLo u n - optHi t m * optLo u n =
          hahnSum ht * hahnSum hu +
            (optHi t m - hahnSum ht) * (hahnSum hu - optLo u n) := by ring
      rw [hid]
      exact key

/-! ### The reflection law -/

private theorem mk_expTerm {σ : Surreal.{u}} (k : ℕ) :
    ArchimedeanClass.mk (σ ^ k / ((k.factorial : ℕ) : Surreal)) =
      ArchimedeanClass.mk (σ ^ k) := by
  rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero]

private theorem mk_neg_pow (σ : Surreal.{u}) (k : ℕ) :
    ArchimedeanClass.mk ((-σ) ^ k) = ArchimedeanClass.mk (σ ^ k) := by
  rw [ArchimedeanClass.mk_pow, ArchimedeanClass.mk_pow, ArchimedeanClass.mk_neg]

theorem Infinitesimal.abs {σ : Surreal.{u}} (h : Infinitesimal σ) : Infinitesimal |σ| := by
  show 0 < ArchimedeanClass.mk |σ|
  rw [ArchimedeanClass.mk_abs]
  exact h

/-- The canonical exponential value is finite (it is `1 + o(1)`). -/
theorem isFinite_expInf {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    IsFinite (expInf ε hε hε0) := by
  have h : expInf ε hε hε0 = 1 + (expInf ε hε hε0 - 1) := by ring
  rw [h]
  exact isFinite_one.add (infinitesimal_expInf_sub_one hε hε0).isFinite

/-- The partial sums of the exponential series at an infinitesimal are finite. -/
theorem isFinite_partialSum_expSeries {ε : Surreal.{u}} (hε : Infinitesimal ε) (n : ℕ) :
    IsFinite (partialSum (fun k ↦ ε ^ k / ((k.factorial : ℕ) : Surreal)) n) := by
  rw [partialSum_expSeries_eq_eval]
  exact isFinite_eval₂ _ hε.isFinite

/-- **The truncated reflection identity, evaluated**: `S_N(σ) · S_N(−σ) − 1 = σᴺ · Q(σ)` for a
real polynomial `Q` (`Infinity.ExpNegLog.X_pow_dvd_expPoly_mul_comp_neg`), so its class is at
least `mk (σᴺ)`. -/
theorem mk_pow_le_mk_partialSum_mul_partialSum_neg_sub_one {σ : Surreal.{u}}
    (hσ : Infinitesimal σ) (N : ℕ) :
    ArchimedeanClass.mk (σ ^ N) ≤ ArchimedeanClass.mk
      (partialSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) N *
        partialSum (fun k ↦ (-σ) ^ k / ((k.factorial : ℕ) : Surreal)) N - 1) := by
  obtain ⟨Q, hQ⟩ := X_pow_dvd_expPoly_mul_comp_neg N
  have hev := congrArg (Polynomial.eval₂ realHom σ) hQ
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_one,
    Polynomial.eval₂_X, Polynomial.eval₂_X_pow, Polynomial.eval₂_comp,
    Polynomial.eval₂_neg] at hev
  rw [partialSum_expSeries_eq_eval, partialSum_expSeries_eq_eval, hev, ArchimedeanClass.mk_mul]
  have hQfin : (0 : ArchimedeanClass Surreal) ≤ ArchimedeanClass.mk (Q.eval₂ realHom σ) :=
    isFinite_eval₂ _ hσ.isFinite
  calc ArchimedeanClass.mk (σ ^ N) = ArchimedeanClass.mk (σ ^ N) + 0 := (add_zero _).symm
    _ ≤ _ := add_le_add le_rfl hQfin

/-- The three-term decomposition
`x·y − 1 = (x − S)·y + S·(y − S') + (S·S' − 1)` transports a common class bound. -/
private theorem le_mk_mul_sub_one {c : ArchimedeanClass Surreal.{u}} {x y S S' : Surreal.{u}}
    (hx : c ≤ ArchimedeanClass.mk (x - S)) (hy : c ≤ ArchimedeanClass.mk (y - S'))
    (hyfin : 0 ≤ ArchimedeanClass.mk y) (hSfin : 0 ≤ ArchimedeanClass.mk S)
    (hSS : c ≤ ArchimedeanClass.mk (S * S' - 1)) :
    c ≤ ArchimedeanClass.mk (x * y - 1) := by
  have hsplit : x * y - 1 = (x - S) * y + (S * (y - S') + (S * S' - 1)) := by ring
  rw [hsplit]
  refine le_trans (le_min ?_ (le_min ?_ hSS))
    (le_trans (min_le_min le_rfl (ArchimedeanClass.min_le_mk_add _ _))
      (ArchimedeanClass.min_le_mk_add _ _))
  · rw [ArchimedeanClass.mk_mul]
    calc c = c + 0 := (add_zero _).symm
      _ ≤ _ := add_le_add hx hyfin
  · rw [ArchimedeanClass.mk_mul]
    calc c = 0 + c := (zero_add _).symm
      _ ≤ _ := add_le_add hSfin hy

/-- **The domination half of the reflection law**: `expInf σ · expInf (−σ) − 1` is at least
as fine as every power of `σ`. Write `P − 1 = (E_σ − S_N)·E_{−σ} + S_N·(E_{−σ} − S'_N) +
(S_N·S'_N − 1)`: the first two summands are Hahn-sum residuals times finite factors, the third
is the evaluated truncated reflection identity. -/
theorem mk_pow_le_mk_expInf_mul_expInf_neg_sub_one {σ : Surreal.{u}} (hσ : Infinitesimal σ)
    (hσ0 : σ ≠ 0) (N : ℕ) :
    ArchimedeanClass.mk (σ ^ N) ≤
      ArchimedeanClass.mk (expInf σ hσ hσ0 * expInf (-σ) hσ.neg (neg_ne_zero.2 hσ0) - 1) := by
  refine le_mk_mul_sub_one ?_ ?_ (isFinite_expInf hσ.neg _) (isFinite_partialSum_expSeries hσ N)
    (mk_pow_le_mk_partialSum_mul_partialSum_neg_sub_one hσ N)
  · have h := isHahnSum_expInf hσ hσ0 N
    rwa [mk_expTerm] at h
  · have h := isHahnSum_expInf hσ.neg (neg_ne_zero.2 hσ0) N
    rwa [mk_expTerm, mk_neg_pow] at h

/-- The product `expInf σ · expInf (−σ)` lies in the deep halo of `1` at scale `|σ|`. -/
theorem deepHalo_expInf_mul_expInf_neg {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : σ ≠ 0) :
    DeepHalo |σ| 1 (expInf σ hσ hσ0 * expInf (-σ) hσ.neg (neg_ne_zero.2 hσ0)) := by
  intro N
  rw [← abs_pow, ArchimedeanClass.mk_abs]
  exact (mk_pow_lt_mk_pow_succ' hσ hσ0 N).trans_le
    (mk_pow_le_mk_expInf_mul_expInf_neg_sub_one hσ hσ0 (N + 1))

/-- **THE REFLECTION LAW**: `expInf σ · expInf (−σ) = 1` for **every** nonzero infinitesimal
`σ`, of either sign.

Proof: the product of the option games of the exponential series at `σ` and at `−σ` has value
`expInf σ · expInf (−σ)`, which lies in the deep halo of `1` at scale `|σ|`
(`deepHalo_expInf_mul_expInf_neg`); the products of terms `σ^m/m! · (−σ)^n/n!` have class
`mk (σ^(m+n)) < mk (|σ|^(m+n+1))`, so the product engine at the halo scale identifies the
product with the halo value of `1`, and `1` is halo-simple (`haloSimple_one`). -/
theorem expInf_mul_expInf_neg {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : σ ≠ 0) :
    expInf σ hσ hσ0 * expInf (-σ) hσ.neg (neg_ne_zero.2 hσ0) = 1 := by
  have habs : Infinitesimal |σ| := hσ.abs
  have habs0 : 0 < |σ| := abs_pos.2 hσ0
  have hP := deepHalo_expInf_mul_expInf_neg hσ hσ0
  have hcof : ∀ m n, ∃ N : ℕ, ArchimedeanClass.mk
      (σ ^ m / ((m.factorial : ℕ) : Surreal) * ((-σ) ^ n / ((n.factorial : ℕ) : Surreal))) <
      ArchimedeanClass.mk (|σ| ^ N) := by
    intro m n
    refine ⟨m + n + 1, ?_⟩
    rw [ArchimedeanClass.mk_mul, mk_expTerm, mk_expTerm, mk_neg_pow, ← ArchimedeanClass.mk_mul,
      ← pow_add, ← abs_pow, ArchimedeanClass.mk_abs]
    exact mk_pow_lt_mk_pow_succ' hσ hσ0 (m + n)
  rw [← (haloValue_eq_self_iff habs habs0).2 (haloSimple_one |σ|)]
  exact hahnSum_mul_hahnSum_eq_haloValue habs habs0 _ _ hP hcof

/-- **The inverse law**: `expInf (−σ) = (expInf σ)⁻¹` for every nonzero infinitesimal `σ`. -/
theorem expInf_neg_eq_inv {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : σ ≠ 0) :
    expInf (-σ) hσ.neg (neg_ne_zero.2 hσ0) = (expInf σ hσ hσ0)⁻¹ :=
  eq_inv_of_mul_eq_one_right (expInf_mul_expInf_neg hσ hσ0)

/-- The canonical exponential is positive on every nonzero infinitesimal. -/
theorem expInf_pos {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : σ ≠ 0) :
    0 < expInf σ hσ hσ0 := by
  rw [← expInf'_of_ne hσ hσ0]
  exact expInf'_pos hσ

theorem expInf_ne_zero {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : σ ≠ 0) :
    expInf σ hσ hσ0 ≠ 0 :=
  (expInf_pos hσ hσ0).ne'

/-- The exponential of a negative infinitesimal lies strictly below `1`. -/
theorem expInf_lt_one_of_neg {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : σ < 0) :
    expInf σ hσ hσ0.ne < 1 := by
  have hpos : 0 < -σ := neg_pos.2 hσ0
  have h1 := one_lt_expInf hσ.neg hpos
  have h2 := expInf_mul_expInf_neg hσ hσ0.ne
  have h3 := expInf_pos hσ hσ0.ne
  by_contra h
  rw [not_lt] at h
  have : 1 < expInf σ hσ hσ0.ne * expInf (-σ) hσ.neg (neg_ne_zero.2 hσ0.ne) :=
    one_lt_mul_of_le_of_lt h h1
  rw [h2] at this
  exact lt_irrefl _ this

/-! ### The ℤ-lattice law -/

theorem Infinitesimal.zsmul {σ : Surreal.{u}} (hσ : Infinitesimal σ) (n : ℤ) :
    Infinitesimal (n • σ) := by
  rw [zsmul_eq_mul]
  exact IsFinite.mul_infinitesimal (ArchimedeanClass.mk_intCast_nonneg n) hσ

theorem zsmul_ne_zero_of_pos {σ : Surreal.{u}} (hσ0 : 0 < σ) {n : ℤ} (hn : n ≠ 0) :
    n • σ ≠ 0 := by
  rw [zsmul_eq_mul]
  exact mul_ne_zero (Int.cast_ne_zero.2 hn) hσ0.ne'

/-- **The ℤ-lattice law**: `expInf (n • σ) = expInf σ ^ n` for every positive infinitesimal
`σ` and every nonzero integer `n` — positive `n` by the iterate law of
`Infinity.ExpDichotomy`, negative `n` by the reflection law. -/
theorem expInf_zsmul {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : 0 < σ) {n : ℤ}
    (hn : n ≠ 0) :
    expInf (n • σ) (hσ.zsmul n) (zsmul_ne_zero_of_pos hσ0 hn) = expInf σ hσ hσ0.ne' ^ n := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n.natAbs = k + 1 :=
    ⟨n.natAbs - 1, by have := Int.natAbs_ne_zero.2 hn; omega⟩
  have hpos : Infinitesimal ((k + 1) • σ) := hσ.nsmul (k + 1)
  have hpos0 : 0 < (k + 1) • σ := by positivity
  rcases Int.natAbs_eq n with h | h
  · rw [hk] at h
    have e1 : n • σ = (k + 1) • σ := by rw [h, natCast_zsmul]
    rw [expInf_congr e1 _ _ hpos hpos0.ne', expInf_succ_nsmul hσ hσ0 k, h, zpow_natCast]
  · rw [hk] at h
    have e1 : n • σ = -((k + 1) • σ) := by rw [h, neg_zsmul, natCast_zsmul]
    rw [expInf_congr e1 _ _ hpos.neg (neg_ne_zero.2 hpos0.ne'), expInf_neg_eq_inv hpos hpos0.ne',
      expInf_succ_nsmul hσ hσ0 k, h, zpow_neg, zpow_natCast]

/-! ### `exp ∘ log` is halo simplification -/

/-- **EXP ∘ LOG IS HALO SIMPLIFICATION**: for every nonzero infinitesimal `x` and every Hahn
sum `σ` of the logarithm series at `x`, the canonical exponential of `σ` is the halo value
of `1 + x` at scale `|x|` — the birthday-simplest point of the deep halo of `1 + x`.

Proof: `expInf σ` and `1 + x` are both Hahn sums of the exponential series at `σ`
(`Infinity.ExpLogGrid.isHahnSum_expSeries_one_add_of_isHahnSum_log`), so they differ below
every term class `mk (σ^N) = mk (x^N)`; and the terms are cofinal in the powers of `|x|`. -/
theorem expInf_eq_haloValue_of_isHahnSum_log {x σ : Surreal.{u}} (hx : Infinitesimal x)
    (hx0 : x ≠ 0) (hσ : IsHahnSum (logSeriesAt x) σ) :
    expInf σ (infinitesimal_of_isHahnSum_log hx hx0 hσ) (ne_zero_of_isHahnSum_log hx hx0 hσ) =
      haloValue |x| (1 + x) (abs_pos.2 hx0) := by
  have hσmk : ArchimedeanClass.mk σ = ArchimedeanClass.mk x := mk_of_isHahnSum_log hx hx0 hσ
  have hv := isHahnSum_expSeries_one_add_of_isHahnSum_log hx hx0 hσ
  have hpow : ∀ k : ℕ, ArchimedeanClass.mk (σ ^ k) = ArchimedeanClass.mk (x ^ k) := fun k ↦ by
    rw [ArchimedeanClass.mk_pow, ArchimedeanClass.mk_pow, hσmk]
  have ht := expSeries_strict_dominating (infinitesimal_of_isHahnSum_log hx hx0 hσ)
    (ne_zero_of_isHahnSum_log hx hx0 hσ)
  unfold expInf
  refine hahnSum_eq_haloValue hx.abs (abs_pos.2 hx0) ht ?_ ?_
  · intro N
    have h := IsHahnSum.mk_sub_le (isHahnSum_hahnSum ht) hv (N + 1)
    rw [mk_expTerm, hpow] at h
    rw [← abs_pow, ArchimedeanClass.mk_abs]
    exact (mk_pow_lt_mk_pow_succ' hx hx0 N).trans_le h
  · intro m
    refine ⟨m + 1, ?_⟩
    rw [mk_expTerm, hpow, ← abs_pow, ArchimedeanClass.mk_abs]
    exact mk_pow_lt_mk_pow_succ' hx hx0 m

/-- **The criterion**: `exp (log (1 + x)) = 1 + x` exactly when `1 + x` is halo-simple at
scale `|x|`. -/
theorem expInf_eq_one_add_iff_haloSimple {x σ : Surreal.{u}} (hx : Infinitesimal x)
    (hx0 : x ≠ 0) (hσ : IsHahnSum (logSeriesAt x) σ) :
    expInf σ (infinitesimal_of_isHahnSum_log hx hx0 hσ) (ne_zero_of_isHahnSum_log hx hx0 hσ) =
        1 + x ↔
      HaloSimple |x| (1 + x) := by
  rw [expInf_eq_haloValue_of_isHahnSum_log hx hx0 hσ]
  exact haloValue_eq_self_iff hx.abs (abs_pos.2 hx0)

theorem expInf_eq_one_add_of_haloSimple {x σ : Surreal.{u}} (hx : Infinitesimal x)
    (hx0 : x ≠ 0) (hσ : IsHahnSum (logSeriesAt x) σ) (h : HaloSimple |x| (1 + x)) :
    expInf σ (infinitesimal_of_isHahnSum_log hx hx0 hσ) (ne_zero_of_isHahnSum_log hx hx0 hσ) =
      1 + x :=
  (expInf_eq_one_add_iff_haloSimple hx hx0 hσ).2 h

/-- The exponential of a logarithm of `1 + x` is any halo-simple point of the deep halo of
`1 + x`. -/
theorem expInf_eq_of_deepHalo_of_haloSimple_of_isHahnSum_log {x σ : Surreal.{u}}
    (hx : Infinitesimal x) (hx0 : x ≠ 0) (hσ : IsHahnSum (logSeriesAt x) σ) {q : Surreal.{u}}
    (hq : DeepHalo |x| (1 + x) q) (hqs : HaloSimple |x| q) :
    expInf σ (infinitesimal_of_isHahnSum_log hx hx0 hσ) (ne_zero_of_isHahnSum_log hx hx0 hσ) =
      q := by
  rw [expInf_eq_haloValue_of_isHahnSum_log hx hx0 hσ]
  exact haloValue_eq_of_deepHalo_of_haloSimple hx.abs (abs_pos.2 hx0) hq hqs

/-- **The grid theorem, read backwards**: `Infinity.ExpLogGrid.expInf_eq_one_add_of_isHahnSum_log`
says exactly that `1 + a·ω⁻¹` is halo-simple at scale `|a·ω⁻¹|` for every nonzero dyadic
`a`. -/
theorem haloSimple_one_add_dyadic_mul_eps0 (a : Dyadic) (ha : a ≠ 0) :
    HaloSimple |(a : Surreal.{0}) * eps0| (1 + (a : Surreal) * eps0) :=
  (expInf_eq_one_add_iff_haloSimple (dyadic_mul_eps0_infinitesimal' a)
    (dyadic_mul_eps0_ne_zero' ha) (isHahnSum_logGrid a ha)).1 (expInf_logGrid_eq a ha)

/-! ### A visible halo simplification: `x = ω⁻¹ + ω^(−ω)` -/

theorem infinitesimal_wpow_neg_one_add_wpow_neg_omega :
    Infinitesimal (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal)))) :=
  infinitesimal_wpow_neg_one.add infinitesimal_wpow_neg_omega

theorem wpow_neg_one_add_wpow_neg_omega_ne_zero :
    ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal))) ≠ 0 :=
  (add_pos (wpow_pos _) (wpow_pos _)).ne'

theorem mk_wpow_neg_one_add_wpow_neg_omega :
    ArchimedeanClass.mk (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal)))) =
      ArchimedeanClass.mk (ω^ (-1 : Surreal.{u})) :=
  mk_add_eq_of_forall_nsmul_lt forall_nsmul_mk_wpow_neg_one_lt

/-- `1 + ω⁻¹` lies in the deep halo of `1 + (ω⁻¹ + ω^(−ω))` at scale `|ω⁻¹ + ω^(−ω)|`. -/
theorem deepHalo_one_add_wpow_neg_one :
    DeepHalo |ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal)))|
      (1 + (ω^ (-1 : Surreal) + ω^ (-(ω^ (1 : Surreal))))) (1 + ω^ (-1 : Surreal)) := by
  intro N
  rw [← abs_pow, ArchimedeanClass.mk_abs, ArchimedeanClass.mk_pow,
    mk_wpow_neg_one_add_wpow_neg_omega]
  have h : (1 + ω^ (-1 : Surreal.{u})) - (1 + (ω^ (-1 : Surreal) + ω^ (-(ω^ (1 : Surreal))))) =
      -ω^ (-(ω^ (1 : Surreal))) := by ring
  rw [h, ArchimedeanClass.mk_neg]
  exact forall_nsmul_mk_wpow_neg_one_lt N

private theorem dyadic_one_cast : ((1 : Dyadic) : Surreal.{u}) = 1 := by
  show (((1 : Dyadic) : ℚ) : Surreal) = 1
  norm_num

/-- `1 + ω⁻¹` is halo-simple at scale `|ω⁻¹ + ω^(−ω)|` (whose first power already reaches
`ω⁻¹`). -/
theorem haloSimple_one_add_wpow_neg_one :
    HaloSimple |ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal)))| (1 + ω^ (-1 : Surreal)) := by
  have h := haloSimple_dyadic_add_wpow_neg_one
    (ε := |ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal)))|) 1 ⟨1, ?_⟩
  · rwa [dyadic_one_cast] at h
  · rw [pow_one, ArchimedeanClass.mk_abs, mk_wpow_neg_one_add_wpow_neg_omega]

/-- **A visible halo simplification**: at `x = ω⁻¹ + ω^(−ω)`, the exponential of every
logarithm of `1 + x` is `1 + ω⁻¹` — the simplest point of the deep halo of `1 + x`. -/
theorem expInf_eq_one_add_wpow_neg_one_of_isHahnSum_log {σ : Surreal.{u}}
    (hσ : IsHahnSum (logSeriesAt (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal))))) σ) :
    expInf σ (infinitesimal_of_isHahnSum_log infinitesimal_wpow_neg_one_add_wpow_neg_omega
        wpow_neg_one_add_wpow_neg_omega_ne_zero hσ)
      (ne_zero_of_isHahnSum_log infinitesimal_wpow_neg_one_add_wpow_neg_omega
        wpow_neg_one_add_wpow_neg_omega_ne_zero hσ) =
      1 + ω^ (-1 : Surreal) :=
  expInf_eq_of_deepHalo_of_haloSimple_of_isHahnSum_log
    infinitesimal_wpow_neg_one_add_wpow_neg_omega wpow_neg_one_add_wpow_neg_omega_ne_zero hσ
    deepHalo_one_add_wpow_neg_one haloSimple_one_add_wpow_neg_one

/-- **`exp ∘ log ≠ id`, concretely**: at `x = ω⁻¹ + ω^(−ω)`, `exp (log (1 + x)) ≠ 1 + x`. -/
theorem expInf_ne_one_add_of_isHahnSum_log_wpow {σ : Surreal.{u}}
    (hσ : IsHahnSum (logSeriesAt (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal))))) σ) :
    expInf σ (infinitesimal_of_isHahnSum_log infinitesimal_wpow_neg_one_add_wpow_neg_omega
        wpow_neg_one_add_wpow_neg_omega_ne_zero hσ)
      (ne_zero_of_isHahnSum_log infinitesimal_wpow_neg_one_add_wpow_neg_omega
        wpow_neg_one_add_wpow_neg_omega_ne_zero hσ) ≠
      1 + (ω^ (-1 : Surreal) + ω^ (-(ω^ (1 : Surreal)))) := by
  rw [expInf_eq_one_add_wpow_neg_one_of_isHahnSum_log hσ]
  intro h
  have := wpow_pos (-(ω^ (1 : Surreal.{u})))
  linarith

end Surreal

end
