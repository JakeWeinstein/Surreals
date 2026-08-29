import Infinity.Summation
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The derivative at every surreal point — and the Galaxy Kernel obstruction

Toward integration of general surreal functions, this file builds the derivative that makes
sense at **every** surreal point `x` with **surreal** derivative values: `HasDerivS f x d`
holds when the Taylor error `f (x + ε) - f x - d * ε` is bounded by `C * ε²` uniformly over
all infinitesimal increments `ε`, for some constant `C` (depending on `x`). At infinite
points the naive difference quotient fails (`(x³)′` at `ω` has quotient error `3ωε`, not
infinitesimal), but the `O(ε²)` formulation works — and pins the derivative uniquely,
because below every positive surreal there is a positive infinitesimal
(`exists_pos_infinitesimal_lt`).

Main results:

* `HasDerivS.unique` — the derivative is unique.
* `hasDerivS_polynomial` — every polynomial **with surreal coefficients** is differentiable
  at **every surreal point**, with derivative the formal one. (Proof: exact Taylor
  expansion; all error terms are `≤ |ε|² ≤ ε²`-dominated since `|ε| ≤ 1`.)
* **The Galaxy Kernel Theorem** (`hasDerivS_galaxyStep`, `not_antideriv_unique`):
  the indicator of the infinite galaxy — `0` on finite surreals, `1` on infinite ones — has
  derivative **zero at every point** (infinitesimal increments never leave a galaxy), yet is
  not constant. Hence *antiderivatives on the class of all differentiable functions are not
  unique up to constants*, and **no Fundamental-Theorem-style integral can be well-defined
  on arbitrary surreal functions**. This is the Conway–Kruskal–Norton difficulty, isolated
  as a theorem: any surreal integral must restrict to a class of functions rigid enough to
  see across galaxies (polynomials, and eventually analyzable functions — the
  Costin–Ehrlich–Friedman program).
-/

open Polynomial ArchimedeanClass Finset

noncomputable section

namespace Surreal

/-! ### Below every positive surreal there is a positive infinitesimal -/

theorem exists_pos_infinitesimal_lt {w : Surreal} (hw : 0 < w) :
    ∃ ε : Surreal, Infinitesimal ε ∧ 0 < ε ∧ ε < w := by
  have hio : Infinitesimal ((ω^ (1 : Surreal))⁻¹ : Surreal) := infinitesimal_inv_wpow one_pos
  have hio0 : (0 : Surreal) < (ω^ (1 : Surreal))⁻¹ := inv_pos.2 (wpow_pos _)
  have hio1 : ((ω^ (1 : Surreal))⁻¹ : Surreal) < 1 := by
    have h := infinitesimal_iff.1 hio 1
    rwa [one_nsmul, abs_of_pos hio0] at h
  by_cases h : Infinitesimal w
  · exact ⟨w * (ω^ (1 : Surreal))⁻¹, h.mul_isFinite hio.isFinite,
      mul_pos hw hio0, mul_lt_of_lt_one_right hw hio1⟩
  · have h1 : ArchimedeanClass.mk w < ArchimedeanClass.mk ((ω^ (1 : Surreal))⁻¹ : Surreal) :=
      lt_of_le_of_lt (not_lt.1 h) hio
    have h2 := abs_lt_abs_of_mk_lt h1
    rw [abs_of_pos hw, abs_of_pos hio0] at h2
    exact ⟨(ω^ (1 : Surreal))⁻¹, hio, hio0, h2⟩

/-! ### The derivative at surreal points -/

/-- `f` has derivative `d` at the surreal point `x` when the Taylor error is `O(ε²)`
uniformly over all infinitesimal increments: `|f (x + ε) - f x - d * ε| ≤ C * ε²` for some
constant `C`. This is the formulation that works at infinite and infinitesimal points alike,
where naive difference quotients fail. -/
def HasDerivS (f : Surreal → Surreal) (x d : Surreal) : Prop :=
  ∃ C : Surreal, ∀ ε : Surreal, Infinitesimal ε → |f (x + ε) - f x - d * ε| ≤ C * ε ^ 2

/-- The surreal-point derivative is unique. -/
theorem HasDerivS.unique {f : Surreal → Surreal} {x d d' : Surreal}
    (h : HasDerivS f x d) (h' : HasDerivS f x d') : d = d' := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  by_contra hne
  have hw0 : 0 < |d - d'| := abs_pos.2 (sub_ne_zero.2 hne)
  have hK0 : (0 : Surreal) < |C| + |C'| + 1 := by positivity
  obtain ⟨ε, hεinf, hε0, hεlt⟩ := exists_pos_infinitesimal_lt (div_pos hw0 hK0)
  have h3 : |(d - d') * ε| ≤ (C' + C) * ε ^ 2 := by
    have hsplit : (d - d') * ε =
        (f (x + ε) - f x - d' * ε) - (f (x + ε) - f x - d * ε) := by ring
    rw [hsplit, sub_eq_add_neg]
    calc |(f (x + ε) - f x - d' * ε) + -(f (x + ε) - f x - d * ε)|
        ≤ |f (x + ε) - f x - d' * ε| + |f (x + ε) - f x - d * ε| := by
          rw [← abs_neg (f (x + ε) - f x - d * ε)]
          exact abs_add_le _ _
      _ ≤ C' * ε ^ 2 + C * ε ^ 2 := add_le_add (hC' ε hεinf) (hC ε hεinf)
      _ = (C' + C) * ε ^ 2 := by ring
  have h4 : |d - d'| * ε ≤ ((|C| + |C'| + 1) * ε) * ε := by
    rw [abs_mul, abs_of_pos hε0] at h3
    refine h3.trans ?_
    rw [mul_assoc, ← sq]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg ε)
    have hc1 := le_abs_self C
    have hc2 := le_abs_self C'
    linarith
  have h5 : |d - d'| ≤ (|C| + |C'| + 1) * ε := le_of_mul_le_mul_right h4 hε0
  have h6 : (|C| + |C'| + 1) * ε < |d - d'| := by
    have h7 := (lt_div_iff₀ hK0).1 hεlt
    linarith
  exact absurd (h5.trans_lt h6) (lt_irrefl _)

/-- Subtracting a constant preserves the derivative. -/
theorem HasDerivS.sub_const {f : Surreal → Surreal} {x d : Surreal} (h : HasDerivS f x d)
    (c : Surreal) : HasDerivS (fun s ↦ f s - c) x d := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun ε hε ↦ ?_⟩
  have h1 := hC ε hε
  convert h1 using 2
  ring

/-! ### Polynomials differentiate at every surreal point -/

/-- **Every surreal-coefficient polynomial is differentiable at every surreal point**, with
the formal derivative. The proof is the exact Taylor expansion: every term beyond the linear
one carries `ε^k` with `k ≥ 2`, and `|ε|^k ≤ |ε|² = ε²` since infinitesimals satisfy
`|ε| ≤ 1`. -/
theorem hasDerivS_polynomial (P : Polynomial Surreal) (x : Surreal) :
    HasDerivS (fun s ↦ P.eval s) x (P.derivative.eval x) := by
  refine ⟨∑ k ∈ Ico 2 (P.natDegree + 2), |(taylor x P).coeff k|, fun ε hε ↦ ?_⟩
  have hval : P.eval (x + ε) =
      ∑ k ∈ range (P.natDegree + 2), (taylor x P).coeff k * ε ^ k := by
    have h1 : P.eval (x + ε) = (taylor x P).eval ε := by rw [taylor_eval, add_comm]
    rw [h1, eval_eq_sum_range' (n := P.natDegree + 2)
      (lt_of_le_of_lt (natDegree_taylor P x).le (by omega)) ε]
  have hsplit : ∑ k ∈ range (P.natDegree + 2), (taylor x P).coeff k * ε ^ k =
      ((taylor x P).coeff 0 + (taylor x P).coeff 1 * ε) +
        ∑ k ∈ Ico 2 (P.natDegree + 2), (taylor x P).coeff k * ε ^ k := by
    rw [range_eq_Ico, ← sum_Ico_consecutive _ (by omega : (0 : ℕ) ≤ 2) (by omega),
      Nat.Ico_zero_eq_range]
    congr 1
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    ring
  have herr : P.eval (x + ε) - P.eval x - P.derivative.eval x * ε =
      ∑ k ∈ Ico 2 (P.natDegree + 2), (taylor x P).coeff k * ε ^ k := by
    rw [hval, hsplit, taylor_coeff_zero, taylor_coeff_one]
    ring
  rw [herr]
  have hε1 : |ε| ≤ 1 := by
    have h := infinitesimal_iff.1 hε 1
    rw [one_nsmul] at h
    exact h.le
  calc |∑ k ∈ Ico 2 (P.natDegree + 2), (taylor x P).coeff k * ε ^ k|
      ≤ ∑ k ∈ Ico 2 (P.natDegree + 2), |(taylor x P).coeff k * ε ^ k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Ico 2 (P.natDegree + 2), |(taylor x P).coeff k| * ε ^ 2 := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        rw [abs_mul, abs_pow, show ε ^ 2 = |ε| ^ 2 from (sq_abs ε).symm]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (abs_nonneg ε) hε1 (mem_Ico.1 hk).1) (abs_nonneg _)
    _ = (∑ k ∈ Ico 2 (P.natDegree + 2), |(taylor x P).coeff k|) * ε ^ 2 :=
        (Finset.sum_mul ..).symm

/-! ### The Galaxy Kernel Theorem -/

/-- Adding an infinitesimal never changes finiteness: infinitesimal increments cannot cross
between galaxies. -/
theorem isFinite_add_infinitesimal_iff {x ε : Surreal} (hε : Infinitesimal ε) :
    IsFinite (x + ε) ↔ IsFinite x := by
  constructor
  · intro h
    have h2 : x = (x + ε) + -ε := by ring
    rw [h2]
    exact h.add hε.isFinite.neg
  · intro h
    exact h.add hε.isFinite

open Classical in
/-- The galaxy indicator: `0` on finite surreals, `1` on infinite ones. -/
def galaxyStep : Surreal → Surreal := fun x ↦ if IsFinite x then 0 else 1

/-- **The Galaxy Kernel Theorem, part 1**: the galaxy indicator has derivative zero at
every surreal point — an infinitesimal increment never changes which galaxy you are in. -/
theorem galaxyStep_of_isFinite {x : Surreal} (h : IsFinite x) : galaxyStep x = 0 := by
  unfold galaxyStep
  exact if_pos h

theorem galaxyStep_of_not_isFinite {x : Surreal} (h : ¬ IsFinite x) : galaxyStep x = 1 := by
  unfold galaxyStep
  exact if_neg h

theorem hasDerivS_galaxyStep (x : Surreal) : HasDerivS galaxyStep x 0 := by
  refine ⟨1, fun ε hε ↦ ?_⟩
  have h : galaxyStep (x + ε) = galaxyStep x := by
    by_cases hx : IsFinite x
    · rw [galaxyStep_of_isFinite ((isFinite_add_infinitesimal_iff hε).2 hx),
        galaxyStep_of_isFinite hx]
    · rw [galaxyStep_of_not_isFinite (fun hh ↦ hx ((isFinite_add_infinitesimal_iff hε).1 hh)),
        galaxyStep_of_not_isFinite hx]
  rw [h, zero_mul, sub_zero, sub_self, abs_zero, one_mul]
  positivity

/-- `ω` is not finite. -/
theorem not_isFinite_wpow_one : ¬ IsFinite (ω^ (1 : Surreal)) := by
  rw [IsFinite, not_le]
  have h := archimedeanClassMk_wpow_strictAnti (one_pos : (0 : Surreal) < 1)
  simpa [wpow_zero, ArchimedeanClass.mk_one] using h

/-- **The Galaxy Kernel Theorem, part 2**: the galaxy indicator is not constant. Hence the
kernel of the surreal derivative contains nonconstant functions. -/
theorem galaxyStep_not_const : galaxyStep (ω^ (1 : Surreal)) ≠ galaxyStep 0 := by
  rw [galaxyStep_of_isFinite isFinite_zero, galaxyStep_of_not_isFinite not_isFinite_wpow_one]
  norm_num

/-- **No Fundamental-Theorem integral exists for arbitrary surreal functions**: there are
two functions with derivative zero everywhere whose increments over `[0, ω]` disagree — so
"`∫ₐᵇ f := F(b) − F(a)` for an antiderivative `F`" is not well-defined on the class of all
differentiable functions. Integration on `No` must restrict to a smaller, more rigid class
(polynomials here; analyzable functions in the Costin–Ehrlich–Friedman program). This is
the Conway–Kruskal–Norton difficulty, isolated as a theorem. -/
theorem not_antideriv_unique :
    ∃ F G : Surreal → Surreal, (∀ x, HasDerivS F x 0) ∧ (∀ x, HasDerivS G x 0) ∧
      F (ω^ (1 : Surreal)) - F 0 ≠ G (ω^ (1 : Surreal)) - G 0 := by
  refine ⟨galaxyStep, fun _ ↦ 0, hasDerivS_galaxyStep, fun x ↦ ⟨1, fun ε hε ↦ ?_⟩, ?_⟩
  · rw [zero_mul, sub_zero, sub_self, abs_zero, one_mul]
    positivity
  · rw [sub_zero]
    intro h
    exact galaxyStep_not_const (sub_eq_zero.1 (by simpa using h))

end Surreal
