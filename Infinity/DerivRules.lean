import Infinity.Derivative

/-!
# The differential calculus toolkit on the surreals

We define what it means for a surreal function `f : Surreal → Surreal` to have derivative
`d : ℝ` at a real point `x`, in the style of nonstandard analysis: *every* nonzero
infinitesimal increment `ε` produces a finite difference quotient with standard part `d`.

Quantifying over all infinitesimals (rather than fixing one) is what makes the calculus
compose: the chain rule works because the inner function's increment
`δ = f (x + ε) - f x` is itself an infinitesimal that can be fed to the outer derivative.

* `Surreal.HasDerivAt f d x`: the derivative predicate.
* `hasDerivAt_const`, `hasDerivAt_id`, `HasDerivAt.add/neg/sub/const_mul`: linearity.
* `HasDerivAt.mul`: the Leibniz product rule.
* `HasDerivAt.inv`: the reciprocal rule (hence quotients).
* `HasDerivAt.comp`: the chain rule.
* `HasDerivAt.hasDerivAt_polynomial`: polynomials have their classical derivatives.
* `HasDerivAt.unique`: the derivative is unique (witnessed by `ε = 1/ω`).
-/

open Polynomial ArchimedeanClass Finset

noncomputable section

namespace Surreal

/-- If a surreal is infinitesimal, its standard part vanishes. -/
theorem Infinitesimal.stdPart_eq_zero {x : Surreal} (h : Infinitesimal x) : stdPart x = 0 :=
  ArchimedeanClass.stdPart_eq_zero.2 h.ne'

/-- A surreal with nonzero standard part sits in the Archimedean class of `1`. -/
theorem mk_eq_zero_of_stdPart_ne_zero {x : Surreal} (h : stdPart x ≠ 0) :
    ArchimedeanClass.mk x = 0 := by
  rw [Ne, ArchimedeanClass.stdPart_eq_zero] at h
  exact not_not.1 h

/-- `f : Surreal → Surreal` has derivative `d : ℝ` at the real point `x` when every nonzero
infinitesimal increment produces a finite difference quotient with standard part `d`.

(Derivatives at general surreal points await the theory of surreal-valued limits; at real
points, this is the nonstandard-analysis definition carried out inside `No`.) -/
def HasDerivAt (f : Surreal → Surreal) (d : ℝ) (x : ℝ) : Prop :=
  ∀ ⦃ε : Surreal⦄, Infinitesimal ε → ε ≠ 0 →
    IsFinite ((f (x + ε) - f x) / ε) ∧ stdPart ((f (x + ε) - f x) / ε) = d

/-- The canonical nonzero infinitesimal `1/ω`, used to witness uniqueness. -/
theorem exists_infinitesimal_ne_zero : ∃ ε : Surreal, Infinitesimal ε ∧ ε ≠ 0 :=
  ⟨(ω^ (1 : Surreal))⁻¹, infinitesimal_inv_wpow one_pos,
    inv_ne_zero (wpow_pos (1 : Surreal)).ne'⟩

/-- The derivative is unique. -/
theorem HasDerivAt.unique {f : Surreal → Surreal} {a b : ℝ} {x : ℝ}
    (ha : HasDerivAt f a x) (hb : HasDerivAt f b x) : a = b := by
  obtain ⟨ε, hε, hε0⟩ := exists_infinitesimal_ne_zero
  rw [← (ha hε hε0).2, ← (hb hε hε0).2]

/-- Differentiability forces infinitesimal continuity: the function moves only
infinitesimally under an infinitesimal increment. -/
theorem HasDerivAt.infinitesimal_sub {f : Surreal → Surreal} {d : ℝ} {x : ℝ}
    (hf : HasDerivAt f d x) {ε : Surreal} (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    Infinitesimal (f (x + ε) - f x) := by
  have h := (hf hε hε0).1
  have : f (x + ε) - f x = (f (x + ε) - f x) / ε * ε := (div_mul_cancel₀ _ hε0).symm
  rw [this]
  exact h.mul_infinitesimal hε

theorem hasDerivAt_const (c : Surreal) (x : ℝ) : HasDerivAt (fun _ ↦ c) 0 x := by
  intro ε hε hε0
  simp

theorem hasDerivAt_id (x : ℝ) : HasDerivAt (fun s ↦ s) 1 x := by
  intro ε hε hε0
  rw [add_sub_cancel_left, div_self hε0]
  simp

theorem HasDerivAt.add {f g : Surreal → Surreal} {a b : ℝ} {x : ℝ}
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    HasDerivAt (fun s ↦ f s + g s) (a + b) x := by
  intro ε hε hε0
  have hq : (f (x + ε) + g (x + ε) - (f x + g x)) / ε =
      (f (x + ε) - f x) / ε + (g (x + ε) - g x) / ε := by
    rw [add_sub_add_comm, add_div]
  rw [hq]
  exact ⟨(hf hε hε0).1.add (hg hε hε0).1,
    by rw [stdPart_add (hf hε hε0).1 (hg hε hε0).1, (hf hε hε0).2, (hg hε hε0).2]⟩

theorem HasDerivAt.neg {f : Surreal → Surreal} {a : ℝ} {x : ℝ} (hf : HasDerivAt f a x) :
    HasDerivAt (fun s ↦ -f s) (-a) x := by
  intro ε hε hε0
  have hq : (-f (x + ε) - -f x) / ε = -((f (x + ε) - f x) / ε) := by ring
  rw [hq]
  exact ⟨(hf hε hε0).1.neg, by rw [stdPart_neg, (hf hε hε0).2]⟩

theorem HasDerivAt.sub {f g : Surreal → Surreal} {a b : ℝ} {x : ℝ}
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    HasDerivAt (fun s ↦ f s - g s) (a - b) x := by
  have h := hf.add hg.neg
  simpa [sub_eq_add_neg] using h

theorem HasDerivAt.const_mul {f : Surreal → Surreal} {a : ℝ} {x : ℝ} (c : ℝ)
    (hf : HasDerivAt f a x) : HasDerivAt (fun s ↦ (c : Surreal) * f s) (c * a) x := by
  intro ε hε hε0
  have hq : ((c : Surreal) * f (x + ε) - (c : Surreal) * f x) / ε =
      (c : Surreal) * ((f (x + ε) - f x) / ε) := by ring
  rw [hq]
  exact ⟨(isFinite_realCast c).mul (hf hε hε0).1,
    by rw [stdPart_mul (isFinite_realCast c) (hf hε hε0).1, stdPart_realCast, (hf hε hε0).2]⟩

/-- **The Leibniz product rule.** If `f` and `g` are differentiable at `x` with finite values
there, the product is differentiable with the classical Leibniz derivative. -/
theorem HasDerivAt.mul {f g : Surreal → Surreal} {a b : ℝ} {x : ℝ}
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x)
    (hf0 : IsFinite (f x)) (hg0 : IsFinite (g x)) :
    HasDerivAt (fun s ↦ f s * g s) (stdPart (f x) * b + stdPart (g x) * a) x := by
  intro ε hε hε0
  -- `f' g' - f g = f' (g' - g) + g (f' - f)`, so the quotient splits.
  have hq : (f (x + ε) * g (x + ε) - f x * g x) / ε =
      f (x + ε) * ((g (x + ε) - g x) / ε) + g x * ((f (x + ε) - f x) / ε) := by
    field_simp
    ring
  have hδ : Infinitesimal (f (x + ε) - f x) := hf.infinitesimal_sub hε hε0
  have hf' : IsFinite (f (x + ε)) := by
    have : f (x + ε) = f x + (f (x + ε) - f x) := by ring
    rw [this]
    exact hf0.add hδ.isFinite
  have hstf' : stdPart (f (x + ε)) = stdPart (f x) := by
    have : f (x + ε) = f x + (f (x + ε) - f x) := by ring
    rw [this, stdPart_add_eq_left hδ]
  rw [hq]
  refine ⟨(hf'.mul (hg hε hε0).1).add (hg0.mul (hf hε hε0).1), ?_⟩
  rw [stdPart_add (hf'.mul (hg hε hε0).1) (hg0.mul (hf hε hε0).1),
    stdPart_mul hf' (hg hε hε0).1, stdPart_mul hg0 (hf hε hε0).1,
    hstf', (hf hε hε0).2, (hg hε hε0).2]

/-- **The reciprocal rule.** If `f` is differentiable at `x` with finite value of nonzero
standard part, then `1/f` is differentiable with the classical derivative `-a / (st (f x))²`. -/
theorem HasDerivAt.inv {f : Surreal → Surreal} {a : ℝ} {x : ℝ}
    (hf : HasDerivAt f a x) (hf0 : IsFinite (f x)) (hc : stdPart (f x) ≠ 0) :
    HasDerivAt (fun s ↦ (f s)⁻¹) (-a / stdPart (f x) ^ 2) x := by
  intro ε hε hε0
  have hδ : Infinitesimal (f (x + ε) - f x) := hf.infinitesimal_sub hε hε0
  have hf' : IsFinite (f (x + ε)) := by
    have h : f (x + ε) = f x + (f (x + ε) - f x) := by ring
    rw [h]
    exact hf0.add hδ.isFinite
  have hstf' : stdPart (f (x + ε)) = stdPart (f x) := by
    have h : f (x + ε) = f x + (f (x + ε) - f x) := by ring
    rw [h, stdPart_add_eq_left hδ]
  -- Neither value is zero, since the standard part is nonzero.
  have hfx0 : f x ≠ 0 := fun h ↦ hc (by rw [h]; simp)
  have hfx0' : f (x + ε) ≠ 0 := fun h ↦ hc (by rw [← hstf', h]; simp)
  -- The product `f (x+ε) * f x` lies exactly in the class of `1`.
  have hmkprod : ArchimedeanClass.mk (f (x + ε) * f x) = 0 := by
    rw [ArchimedeanClass.mk_mul,
      mk_eq_zero_of_stdPart_ne_zero (hstf' ▸ hc : stdPart (f (x + ε)) ≠ 0),
      mk_eq_zero_of_stdPart_ne_zero hc, add_zero]
  have hprodfin : IsFinite (f (x + ε) * f x) := hmkprod.ge
  have hq : ((f (x + ε))⁻¹ - (f x)⁻¹) / ε =
      -((f (x + ε) - f x) / ε) / (f (x + ε) * f x) := by
    rw [inv_sub_inv hfx0' hfx0]
    field_simp
    ring
  rw [hq]
  have hnumfin : IsFinite (-((f (x + ε) - f x) / ε)) := (hf hε hε0).1.neg
  refine ⟨?_, ?_⟩
  · rw [IsFinite, ArchimedeanClass.mk_div, hmkprod, sub_zero]
    exact hnumfin
  · rw [stdPart_div hnumfin (by rw [hmkprod]; simp), stdPart_neg, (hf hε hε0).2,
      stdPart_mul hf' hf0, hstf', ← sq]

/-- **The chain rule.** If `f` has derivative `a` at `x` with real value `f ↑x = ↑y`, and `g`
has derivative `b` at `y`, then `g ∘ f` has derivative `b * a` at `x`.

This is where quantifying over *all* infinitesimal increments earns its keep: the inner
increment `δ = f (x + ε) - f x` is an infinitesimal (possibly zero!), and when nonzero it is a
legitimate increment for `g` at `y`. -/
theorem HasDerivAt.comp {f g : Surreal → Surreal} {a b : ℝ} {x y : ℝ}
    (hg : HasDerivAt g b y) (hf : HasDerivAt f a x) (hfx : f x = y) :
    HasDerivAt (fun s ↦ g (f s)) (b * a) x := by
  intro ε hε hε0
  set δ : Surreal := f (x + ε) - f x with hδdef
  have hδ : Infinitesimal δ := hf.infinitesimal_sub hε hε0
  have hval : f (x + ε) = (y : Surreal) + δ := by rw [hδdef, ← hfx]; ring
  obtain hδ0 | hδ0 := eq_or_ne δ 0
  -- Degenerate increment: `f` did not move, which forces `a = 0`.
  · have ha : a = 0 := by
      have h := (hf hε hε0).2
      rwa [← hδdef, hδ0, zero_div, stdPart_zero, eq_comm] at h
    have hnum : g (f (x + ε)) - g (f x) = 0 := by
      rw [hval, hδ0, add_zero, hfx, sub_self]
    rw [hnum, zero_div]
    simp [ha]
  -- Genuine increment: compose the two difference quotients.
  · have hq : (g (f (x + ε)) - g (f x)) / ε =
        (g ((y : Surreal) + δ) - g y) / δ * (δ / ε) := by
      rw [hval, hfx, div_mul_div_comm, mul_comm δ ε, mul_div_mul_right _ _ hδ0]
    have hgq := hg hδ hδ0
    have hfq : IsFinite (δ / ε) ∧ stdPart (δ / ε) = a := by
      rw [hδdef]
      exact hf hε hε0
    rw [hq]
    exact ⟨hgq.1.mul hfq.1,
      by rw [stdPart_mul hgq.1 hfq.1, hgq.2, hfq.2]⟩

/-- Real polynomials are differentiable everywhere, with their classical derivatives. -/
theorem hasDerivAt_polynomial (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun s ↦ p.eval₂ realHom s) (p.derivative.eval x) x :=
  fun _ hε hε0 ↦ isFinite_diffQuot_and_stdPart_diffQuot p x hε hε0

/-- **The quotient rule**, in classical form. -/
theorem HasDerivAt.div {f g : Surreal → Surreal} {a b : ℝ} {x : ℝ}
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x)
    (hf0 : IsFinite (f x)) (hg0 : IsFinite (g x)) (hc : stdPart (g x) ≠ 0) :
    HasDerivAt (fun s ↦ f s / g s)
      ((a * stdPart (g x) - stdPart (f x) * b) / stdPart (g x) ^ 2) x := by
  have hginv : IsFinite ((g x : Surreal)⁻¹) := by
    rw [IsFinite, ArchimedeanClass.mk_inv, mk_eq_zero_of_stdPart_ne_zero hc, neg_zero]
  have h := hf.mul (hg.inv hg0 hc) hf0 hginv
  have hD : stdPart (f x) * (-b / stdPart (g x) ^ 2) + stdPart ((g x : Surreal)⁻¹) * a =
      (a * stdPart (g x) - stdPart (f x) * b) / stdPart (g x) ^ 2 := by
    rw [ArchimedeanClass.stdPart_inv]
    field_simp
    ring
  rw [← hD]
  simpa [div_eq_mul_inv] using h

/-- The toolkit composes: the derivative of `s ↦ s * s` at `1` is `2`, by the product rule. -/
example : HasDerivAt (fun s : Surreal ↦ s * s) 2 (1 : ℝ) := by
  have h := (hasDerivAt_id 1).mul (hasDerivAt_id 1)
    (isFinite_realCast 1) (isFinite_realCast 1)
  rw [show (2 : ℝ) = 1 + 1 by norm_num]
  simpa using h

end Surreal
