/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.Limits

/-!
# The Riemann collapse: on the surreals, every number integrates every function

The classical Riemann integral reads: `I` is the integral of `f` over `[0,1]` when for every
`ε > 0` there is a `δ > 0` such that every tagged partition of mesh `< δ` has Riemann sum
within `ε` of `I`. On the surreal numbers this definition **collapses**: a finite partition
of `[0,1]` into `n` pieces always has a piece of width at least `1/n`, so *no* partition has
infinitesimal mesh — and taking `δ = 1/ω` the condition is satisfied *vacuously*, by every
surreal `I`, for every function `f`.

* `Surreal.no_infinitesimal_mesh` — no finite partition of `[0,1]` has all pieces bounded by
  an infinitesimal.
* `Surreal.IsRiemannIntegral` — the classical ε–δ definition, verbatim.
* `Surreal.riemann_integral_collapse` — **every surreal is a Riemann integral of every
  function**. In particular (`example`s) the integral of `x` on `[0,1]` "is" `ω`, and also
  `0`, and also anything else.

Together with `tendstoSurreal_atTop_iff_eventuallyEq` (no limits) and `exists_isHahnSum`
(domination-semantics sums exist), this completes the formal case that integration on `No`
must be built on domination semantics: the approximation-based definition is not merely
hard to satisfy — it is degenerate.
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

/-- **No infinitesimal mesh**: a finite partition of `[0,1]` (points `p 0 = 0`, `p n = 1`)
cannot have all its pieces bounded by an infinitesimal — `n` pieces of infinitesimal width
sum to an infinitesimal, not to `1`. -/
theorem no_infinitesimal_mesh {n : ℕ} {p : ℕ → Surreal} (h0 : p 0 = 0) (h1 : p n = 1)
    {δ : Surreal} (hδ : Infinitesimal δ) (hmesh : ∀ i < n, p (i + 1) - p i ≤ δ) :
    False := by
  have htel : ∑ i ∈ range n, (p (i + 1) - p i) = 1 := by
    rw [Finset.sum_range_sub, h0, h1, sub_zero]
  have hbound : (1 : Surreal) ≤ n • δ := by
    rw [← htel]
    exact Finset.sum_le_card_nsmul _ _ _ (fun i hi ↦ hmesh i (mem_range.1 hi)) |>.trans
      (by rw [card_range])
  have habs : n • δ ≤ n • |δ| := nsmul_le_nsmul_right (le_abs_self δ) n
  have hlt : n • |δ| < 1 := infinitesimal_iff.1 hδ n
  exact absurd (hbound.trans_lt (habs.trans_lt hlt)) (lt_irrefl _)

/-- The classical ε–δ Riemann integral over `[0,1]`, stated verbatim on the surreals:
partitions are point sequences `p 0 = 0, …, p n = 1` with mesh below `δ`, tagged by `tag`,
and the Riemann sum must land within `ε` of `I`. -/
def IsRiemannIntegral (f : Surreal → Surreal) (I : Surreal) : Prop :=
  ∀ ε : Surreal, 0 < ε → ∃ δ : Surreal, 0 < δ ∧
    ∀ (n : ℕ) (p tag : ℕ → Surreal), p 0 = 0 → p n = 1 →
      (∀ i < n, p (i + 1) - p i ≤ δ) →
      |(∑ i ∈ range n, f (tag i) * (p (i + 1) - p i)) - I| < ε

/-- **The Riemann collapse**: on the surreals, *every* number is a Riemann integral of
*every* function — the classical definition is vacuously satisfied by taking `δ = 1/ω`,
which no finite partition can undercut. Approximation-based integration is degenerate
on `No`. -/
theorem riemann_integral_collapse (f : Surreal → Surreal) (I : Surreal) :
    IsRiemannIntegral f I := by
  intro ε hε
  refine ⟨(ω^ (1 : Surreal))⁻¹, inv_pos.2 (wpow_pos _), ?_⟩
  intro n p tag h0 h1 hmesh
  exact (no_infinitesimal_mesh h0 h1 (infinitesimal_inv_wpow one_pos) hmesh).elim

/-- The Riemann integral of `x` on `[0,1]` "is" `ω`. -/
example : IsRiemannIntegral (fun x ↦ x) (ω^ (1 : Surreal)) :=
  riemann_integral_collapse _ _

/-- …and also `0`. The definition carries no information. -/
example : IsRiemannIntegral (fun x ↦ x) 0 :=
  riemann_integral_collapse _ _

end Surreal
