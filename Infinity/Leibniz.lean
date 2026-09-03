/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.KernelSeparation

/-!
# The Leibniz rule for the surreal-point derivative

`HasDerivS` (Infinity.GeneralDeriv) is the derivative that works at every surreal point.
The toolkit so far: `add`, `neg`, `sub_const`, `comp_sub_const` (Infinity.KernelSeparation)
and `comp_inv` (Infinity.Laurent). This file adds the product rule:

* `HasDerivS.mul` : `(f·g)′ = f′·g + f·g′` at every surreal point, with the explicit
  constant `(|f x| + |df| + |Cf|)·|Cg| + |g x|·|Cf| + |dg|·(|df| + |Cf|)`.

The proof is the classical three-term split
`f₊g₊ − fg − (f′g + fg′)ε = f₊·[g-error] + g·[f-error] + g′ε·[f₊ − f]`, made quantitative
with the two facts special to infinitesimal increments: `|ε| ≤ 1` and `ε² ≤ |ε|`.

With `add`, `neg`, `mul`, and the polynomial and inversion rules, the functions
S-differentiable at every point of a region form a ring closed under the calculus —
the substrate for extending the integrable classes beyond `Infinity.Laurent`.
-/

open ArchimedeanClass

noncomputable section

namespace Surreal

set_option maxHeartbeats 800000 in
/-- **The Leibniz rule at every surreal point**: if `f` and `g` have surreal-point
derivatives `df` and `dg` at `x`, then `f·g` has derivative `df·g x + f x·dg` there. -/
theorem HasDerivS.mul {f g : Surreal → Surreal} {x df dg : Surreal}
    (hf : HasDerivS f x df) (hg : HasDerivS g x dg) :
    HasDerivS (fun s ↦ f s * g s) x (df * g x + f x * dg) := by
  obtain ⟨Cf, hCf⟩ := hf
  obtain ⟨Cg, hCg⟩ := hg
  refine ⟨(|f x| + |df| + |Cf|) * |Cg| + |g x| * |Cf| + |dg| * (|df| + |Cf|),
    fun ε hε ↦ ?_⟩
  have hε1 : |ε| ≤ 1 := by
    have h := infinitesimal_iff.1 hε 1
    rw [one_nsmul] at h
    exact h.le
  have hε2 : ε ^ 2 ≤ |ε| := by
    calc ε ^ 2 = |ε| * |ε| := by rw [← sq_abs, pow_two]
      _ ≤ |ε| * 1 := mul_le_mul_of_nonneg_left hε1 (abs_nonneg ε)
      _ = |ε| := mul_one _
  have hε2' : (0 : Surreal) ≤ ε ^ 2 := sq_nonneg ε
  have hfe := hCf ε hε
  have hge := hCg ε hε
  -- `Cf`, `Cg` may be replaced by their absolute values
  have hfe' : |f (x + ε) - f x - df * ε| ≤ |Cf| * ε ^ 2 :=
    hfe.trans (mul_le_mul_of_nonneg_right (le_abs_self Cf) hε2')
  have hge' : |g (x + ε) - g x - dg * ε| ≤ |Cg| * ε ^ 2 :=
    hge.trans (mul_le_mul_of_nonneg_right (le_abs_self Cg) hε2')
  -- the value of `f` at the displaced point is bounded
  have hfb : |f (x + ε)| ≤ |f x| + |df| + |Cf| := by
    have h2 : |f (x + ε)| ≤ |f (x + ε) - f x - df * ε| + |f x + df * ε| := by
      calc |f (x + ε)| = |(f (x + ε) - f x - df * ε) + (f x + df * ε)| := by
            congr 1
            ring
        _ ≤ |f (x + ε) - f x - df * ε| + |f x + df * ε| := abs_add_le _ _
    have h3 : |f x + df * ε| ≤ |f x| + |df| * |ε| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
    have h5 : |Cf| * ε ^ 2 ≤ |Cf| * 1 :=
      mul_le_mul_of_nonneg_left (hε2.trans hε1) (abs_nonneg Cf)
    have h6 : |df| * |ε| ≤ |df| * 1 := mul_le_mul_of_nonneg_left hε1 (abs_nonneg df)
    have h7 := hfe'
    linarith
  -- the increment of `f` is `O(ε)`
  have hfi : |f (x + ε) - f x| ≤ (|df| + |Cf|) * |ε| := by
    have h2 : |f (x + ε) - f x| ≤ |f (x + ε) - f x - df * ε| + |df| * |ε| := by
      calc |f (x + ε) - f x| = |(f (x + ε) - f x - df * ε) + df * ε| := by
            congr 1
            ring
        _ ≤ |f (x + ε) - f x - df * ε| + |df * ε| := abs_add_le _ _
        _ = |f (x + ε) - f x - df * ε| + |df| * |ε| := by rw [abs_mul]
    have h5 : |Cf| * ε ^ 2 ≤ |Cf| * |ε| := mul_le_mul_of_nonneg_left hε2 (abs_nonneg Cf)
    have h7 := hfe'
    have h8 : (|df| + |Cf|) * |ε| = |df| * |ε| + |Cf| * |ε| := by ring
    linarith
  -- the three-term split
  show |f (x + ε) * g (x + ε) - f x * g x - (df * g x + f x * dg) * ε| ≤ _
  have hsplit : f (x + ε) * g (x + ε) - f x * g x - (df * g x + f x * dg) * ε =
      f (x + ε) * (g (x + ε) - g x - dg * ε) + g x * (f (x + ε) - f x - df * ε) +
        dg * ε * (f (x + ε) - f x) := by
    ring
  rw [hsplit]
  have ht1 : |f (x + ε) * (g (x + ε) - g x - dg * ε)| ≤
      (|f x| + |df| + |Cf|) * |Cg| * ε ^ 2 := by
    rw [abs_mul]
    calc |f (x + ε)| * |g (x + ε) - g x - dg * ε| ≤
          (|f x| + |df| + |Cf|) * (|Cg| * ε ^ 2) :=
        mul_le_mul hfb hge' (abs_nonneg _) (by positivity)
      _ = (|f x| + |df| + |Cf|) * |Cg| * ε ^ 2 := by ring
  have ht2 : |g x * (f (x + ε) - f x - df * ε)| ≤ |g x| * |Cf| * ε ^ 2 := by
    rw [abs_mul]
    calc |g x| * |f (x + ε) - f x - df * ε| ≤ |g x| * (|Cf| * ε ^ 2) :=
        mul_le_mul_of_nonneg_left hfe' (abs_nonneg _)
      _ = |g x| * |Cf| * ε ^ 2 := by ring
  have ht3 : |dg * ε * (f (x + ε) - f x)| ≤ |dg| * (|df| + |Cf|) * ε ^ 2 := by
    rw [abs_mul, abs_mul]
    calc |dg| * |ε| * |f (x + ε) - f x| ≤ |dg| * |ε| * ((|df| + |Cf|) * |ε|) := by
          refine mul_le_mul_of_nonneg_left hfi ?_
          positivity
      _ = |dg| * (|df| + |Cf|) * (|ε| * |ε|) := by ring
      _ = |dg| * (|df| + |Cf|) * ε ^ 2 := by rw [← pow_two, sq_abs]
  calc |f (x + ε) * (g (x + ε) - g x - dg * ε) + g x * (f (x + ε) - f x - df * ε) +
        dg * ε * (f (x + ε) - f x)|
      ≤ |f (x + ε) * (g (x + ε) - g x - dg * ε) + g x * (f (x + ε) - f x - df * ε)| +
          |dg * ε * (f (x + ε) - f x)| := abs_add_le _ _
    _ ≤ |f (x + ε) * (g (x + ε) - g x - dg * ε)| + |g x * (f (x + ε) - f x - df * ε)| +
          |dg * ε * (f (x + ε) - f x)| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (|f x| + |df| + |Cf|) * |Cg| * ε ^ 2 + |g x| * |Cf| * ε ^ 2 +
          |dg| * (|df| + |Cf|) * ε ^ 2 := add_le_add (add_le_add ht1 ht2) ht3
    _ = ((|f x| + |df| + |Cf|) * |Cg| + |g x| * |Cf| + |dg| * (|df| + |Cf|)) * ε ^ 2 := by
        ring

end Surreal

end
