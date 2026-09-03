/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.DerivRules
import Infinity.Limits
import Mathlib.Algebra.Field.GeomSum

/-!
# Transfinite summation on the surreals: summing what cannot converge

By `Surreal.tendstoSurreal_atTop_iff_eventuallyEq`, an ℕ-indexed series of surreals can never
converge topologically to its sum unless its terms are eventually zero. And yet Conway's `No`
*does* sum infinite series — `Σ_{k<ω} ω⁻ᵏ` "obviously" equals `ω/(ω-1)` — via a semantics of
domination rather than approximation: `x` sums the series when every residual `x - (partial
sum)` is dominated by (has the Archimedean class of, or smaller than) the first omitted term.
This is the finite-length shadow of Conway normal form / Hahn series evaluation.

This file formalizes that semantics and verifies the flagship instance:

* `Surreal.IsHahnSum t x`: each residual `x - partialSum t n` has Archimedean class at least
  that of `t n` (in `ArchimedeanClass`'s order, larger class = smaller magnitude).
* `Surreal.IsHahnSum.mk_sub_le`: any two sums of the same series agree modulo every term's
  class — uniqueness up to terms smaller than the whole tail.
* `Surreal.isHahnSum_geometric`: `(1 - ω⁻¹)⁻¹` (that is, `ω/(ω-1)`) is a Hahn sum of the
  geometric series `Σ ω⁻ᵏ` — with the residual's class *exactly* that of the first omitted
  term (`Surreal.mk_sub_partialSum_geometric`).
* `Surreal.not_tendstoSurreal_partialSum`: no series with nonzero terms has topologically
  convergent partial sums.
* `Surreal.geometric_summable_not_convergent`: the punchline, in one statement — the
  geometric series has a Hahn sum but its partial sums converge to no surreal whatsoever.

Summation and convergence genuinely come apart on `No`; this is, to our knowledge, the first
machine-checked witness of that phenomenon.
-/

open ArchimedeanClass Filter Finset

universe u

noncomputable section

namespace Surreal

/-- The `n`-th partial sum of a surreal series. -/
def partialSum (t : ℕ → Surreal) (n : ℕ) : Surreal :=
  ∑ k ∈ range n, t k

@[simp]
theorem partialSum_zero (t : ℕ → Surreal) : partialSum t 0 = 0 :=
  sum_range_zero _

theorem partialSum_succ (t : ℕ → Surreal) (n : ℕ) :
    partialSum t (n + 1) = partialSum t n + t n :=
  sum_range_succ _ _

/-- `x` is a **Hahn sum** (transfinite sum in Conway's sense) of the series `t` when every
residual `x - partialSum t n` is dominated by the first omitted term: its Archimedean class is
at least `mk (t n)`. (Recall that in `ArchimedeanClass`, *larger* means *smaller magnitude*:
`mk 0 = ⊤`.) This is domination semantics, not approximation semantics — by
`tendstoSurreal_atTop_iff_eventuallyEq`, approximation is impossible. -/
def IsHahnSum (t : ℕ → Surreal) (x : Surreal) : Prop :=
  ∀ n, ArchimedeanClass.mk (t n) ≤ ArchimedeanClass.mk (x - partialSum t n)

/-- Two Hahn sums of the same series agree up to every term's Archimedean class: the
difference is dominated by every single term of the series. -/
theorem IsHahnSum.mk_sub_le {t : ℕ → Surreal} {x y : Surreal}
    (hx : IsHahnSum t x) (hy : IsHahnSum t y) (n : ℕ) :
    ArchimedeanClass.mk (t n) ≤ ArchimedeanClass.mk (x - y) := by
  have hxy : x - y = (x - partialSum t n) - (y - partialSum t n) := by ring
  rw [hxy, sub_eq_add_neg]
  refine le_trans (le_min (hx n) ?_) (ArchimedeanClass.min_le_mk_add ..)
  rw [ArchimedeanClass.mk_neg]
  exact hy n

/-- A series with nonzero terms has partial sums that are not eventually constant, hence —
by the eventual constancy theorem — no surreal topological limit. -/
theorem not_tendstoSurreal_partialSum {t : ℕ → Surreal} (ht : ∀ n, t n ≠ 0) (y : Surreal) :
    ¬ TendstoSurreal (partialSum t) atTop y := by
  rw [tendstoSurreal_atTop_iff_eventuallyEq]
  intro hev
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have h1 : partialSum t (N + 1) = partialSum t N := (hN _ (Nat.le_succ N)).trans (hN N le_rfl).symm
  rw [partialSum_succ, add_eq_left] at h1
  exact ht N h1

/-! ### The geometric series `Σ ω⁻ᵏ` -/

/-- The canonical infinitesimal `1/ω` (pinned to universe `0`). -/
def eps0 : Surreal.{0} :=
  (ω^ (1 : Surreal))⁻¹

@[simp]
theorem eps0_def : eps0 = (ω^ (1 : Surreal))⁻¹ :=
  rfl

local notation "ε₀" => eps0

private theorem eps_infinitesimal : Infinitesimal ε₀ :=
  show Infinitesimal (ω^ (1 : Surreal))⁻¹ from infinitesimal_inv_wpow one_pos

private theorem eps_ne_one : ε₀ ≠ 1 := by
  intro h
  have := eps_infinitesimal.stdPart_eq_zero
  rw [h] at this
  simp at this

private theorem eps_ne_zero : ε₀ ≠ 0 :=
  show (ω^ (1 : Surreal))⁻¹ ≠ 0 from inv_ne_zero (wpow_pos (1 : Surreal)).ne'

private theorem wpow_one_ne_one : (ω^ (1 : Surreal.{0})) ≠ 1 := by
  intro h
  refine eps_ne_one ?_
  show (ω^ (1 : Surreal))⁻¹ = 1
  rw [h, inv_one]

/-- The standard part of `(1 - ω⁻¹)⁻¹` is `1`; in particular it lies in the Archimedean
class of `1`. -/
private theorem mk_geomSum_limit : ArchimedeanClass.mk (1 - ε₀)⁻¹ = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [ArchimedeanClass.stdPart_inv, stdPart_sub isFinite_one eps_infinitesimal.isFinite,
    eps_infinitesimal.stdPart_eq_zero]
  norm_num

/-- The residual identity: chopping the geometric series after `n` terms leaves exactly
`ω⁻ⁿ` times the full sum. -/
private theorem sub_partialSum_geometric (n : ℕ) :
    (1 - ε₀)⁻¹ - partialSum (fun k ↦ ε₀ ^ k) n = ε₀ ^ n * (1 - ε₀)⁻¹ := by
  have h0 : (ω^ (1 : Surreal)) ≠ 0 := (wpow_pos _).ne'
  have h1 : (1 : Surreal) - ε₀ ≠ 0 := sub_ne_zero.2 (Ne.symm eps_ne_one)
  have h2 : ε₀ - 1 ≠ 0 := sub_ne_zero.2 eps_ne_one
  have h3 : (ω^ (1 : Surreal)) - 1 ≠ 0 := sub_ne_zero.2 wpow_one_ne_one
  have h4 : (1 : Surreal) - ω^ (1 : Surreal) ≠ 0 := sub_ne_zero.2 (Ne.symm wpow_one_ne_one)
  rw [partialSum, geom_sum_eq eps_ne_one]
  simp only [eps0_def] at h1 h2 ⊢
  field_simp
  ring

/-- **The residual class identity**: the `n`-th residual of the geometric series at its sum
`(1 - ω⁻¹)⁻¹` has *exactly* the Archimedean class of the first omitted term `ω⁻ⁿ`. -/
theorem mk_sub_partialSum_geometric (n : ℕ) :
    ArchimedeanClass.mk ((1 - ε₀)⁻¹ - partialSum (fun k ↦ ε₀ ^ k) n) =
      ArchimedeanClass.mk (ε₀ ^ n) := by
  rw [sub_partialSum_geometric, ArchimedeanClass.mk_mul, mk_geomSum_limit, add_zero]

/-- **The geometric series sums**: `(1 - ω⁻¹)⁻¹ = ω/(ω-1)` is a Hahn sum of `Σ_{k<ω} ω⁻ᵏ`. -/
theorem isHahnSum_geometric : IsHahnSum (fun k ↦ ε₀ ^ k) (1 - ε₀)⁻¹ := fun n ↦
  (mk_sub_partialSum_geometric n).ge

/-- For the record: `(1 - ω⁻¹)⁻¹` really is `ω/(ω-1)`. -/
theorem geomSum_limit_eq : (1 - ε₀)⁻¹ = ω^ (1 : Surreal) / (ω^ (1 : Surreal) - 1) := by
  have h0 : (ω^ (1 : Surreal)) ≠ 0 := (wpow_pos _).ne'
  have key : (1 : Surreal) - ε₀ = (ω^ (1 : Surreal) - 1) / ω^ (1 : Surreal) := by
    simp only [eps0_def]
    field_simp
  rw [key, inv_div]

/-- **Summation without convergence.** The geometric series `Σ_{k<ω} ω⁻ᵏ` has a Hahn sum —
`ω/(ω-1)` — even though its partial sums converge to no surreal number at all. On `No`,
transfinite summation is a matter of domination, not approximation: the first machine-checked
witness that these semantics genuinely come apart. -/
theorem geometric_summable_not_convergent :
    IsHahnSum (fun k ↦ ε₀ ^ k) (1 - ε₀)⁻¹ ∧
      ∀ y : Surreal, ¬ TendstoSurreal (partialSum fun k ↦ ε₀ ^ k) atTop y :=
  ⟨isHahnSum_geometric,
    not_tendstoSurreal_partialSum fun n ↦ pow_ne_zero n eps_ne_zero⟩

end Surreal
