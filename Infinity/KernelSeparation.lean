import Infinity.MicroKernel

/-!
# The Kernel Separation Theorem

`Infinity.GeneralDeriv` proved that the kernel of surreal differentiation contains a
nonconstant function (the galaxy indicator); `Infinity.MicroKernel` showed the phenomenon
is fractal, recurring inside every halo. This file proves the definitive form:
**the derivative on `No` carries no global information whatsoever** — for every pair of
distinct surreals `a ≠ b` there is a function with derivative zero at every surreal point
taking different values at `a` and `b`.

The construction parametrizes the micro-halo of `Infinity.MicroKernel` by an arbitrary
nonzero scale `y` : `ScaleInner y w` says `w` is dominated by every power `y ^ n`, and
`scaleStep y` is the indicator of the complement of this halo. Jumping the halo forces the
increment `ε` to be at least `y ^ n`-sized for some `n` (the same two-sided pincer as in
`MicroKernel`); a single uniform constant then beats every jump — namely `ω * C₀`, where
`C₀` is a strict upper bound of the countable family `n ↦ ((|y| ^ n)⁻¹) ^ 2`. Such a bound
exists because **no countable family is cofinal in `No`** (`exists_forall_lt`, the mirror
of the coinitiality lemma `exists_pos_forall_lt` of `Infinity.Limits`), and `ω` absorbs
the Archimedean multiplier `k²` via `natCast_lt_wpow_one`. Translating the halo so that it
sits at `a` and testing it at `b` finishes the theorem.

Main results:

* `exists_forall_lt` — **countable non-cofinality**: every `ℕ`-indexed family of surreals
  has a strict upper bound, the Conway cut `!{Set.range f | ∅}`.
* `hasDerivS_scaleStep` — for every nonzero scale `y`, the halo indicator `scaleStep y`
  has derivative zero at every surreal point, with one uniform constant.
* **The Kernel Separation Theorem** (`kernel_separates_points`) : for all `a ≠ b` there
  is `F` with `HasDerivS F x 0` at every `x` and `F a ≠ F b`. Zero-derivative functions
  separate every pair of surreals.
* `not_antideriv_unique_between` — antiderivative increments are ill-defined over **every**
  nondegenerate interval, however positioned and however small.
* `HasDerivS.add` / `HasDerivS.neg` — derivatives add and negate, so the kernel of
  differentiation is an additive subgroup of `Surreal → Surreal` — one that, by the above,
  contains a family separating every pair of points.

Consequence: any Fundamental-Theorem-style integration on a class of surreal functions
must, for *every* pair of points, exclude some zero-derivative function jumping between
them. The rigidity integration requires is not merely cross-galaxy (`GeneralDeriv`) or
within-halo (`MicroKernel`): it must be enforced between every two surreals simultaneously.
-/

open ArchimedeanClass

noncomputable section

namespace Surreal

/-! ### No countable family is cofinal -/

/-- **Countable non-cofinality**: every `ℕ`-indexed family of surreals has a strict upper
bound — the Conway cut with the range on the left and nothing on the right. The mirror of
the coinitiality lemma `exists_pos_forall_lt` of `Infinity.Limits`. -/
theorem exists_forall_lt (f : ℕ → Surreal) : ∃ B : Surreal, ∀ n, f n < B := by
  have H : ∀ x ∈ Set.range f, ∀ y ∈ (∅ : Set Surreal), x < y := by
    rintro x - y hy
    exact absurd hy (Set.notMem_empty y)
  exact ⟨!{Set.range f | ∅}'H, fun n ↦ lt_ofSets_of_mem_left (H := H) ⟨n, rfl⟩⟩

/-! ### The halo at scale `y`, and its indicator -/

/-- `w` is **inner at scale `y`** when it is dominated by every power `y ^ n` : it lies in
the halo of `0` below every scale the powers of `y` can name. For `y = (ω^ 1)⁻¹` this is
`MicroInner` of `Infinity.MicroKernel`. -/
def ScaleInner (y w : Surreal) : Prop :=
  ∀ n : ℕ, ArchimedeanClass.mk (y ^ n) < ArchimedeanClass.mk w

open Classical in
/-- The halo indicator at scale `y` : `0` on the halo `ScaleInner y`, `1` everywhere
else. -/
def scaleStep (y : Surreal) : Surreal → Surreal := fun w ↦ if ScaleInner y w then 0 else 1

theorem scaleInner_zero {y : Surreal} (hy : y ≠ 0) : ScaleInner y 0 := by
  intro n
  rw [ArchimedeanClass.mk_eq_top_iff.2 rfl]
  exact lt_top_iff_ne_top.2 fun h ↦ pow_ne_zero n hy (ArchimedeanClass.mk_eq_top_iff.1 h)

theorem not_scaleInner_self (y : Surreal) : ¬ ScaleInner y y := by
  intro h
  have h1 := h 1
  rw [pow_one] at h1
  exact lt_irrefl _ h1

theorem scaleStep_zero {y : Surreal} (hy : y ≠ 0) : scaleStep y 0 = 0 := by
  unfold scaleStep
  exact if_pos (scaleInner_zero hy)

theorem scaleStep_self (y : Surreal) : scaleStep y y = 1 := by
  unfold scaleStep
  exact if_neg (not_scaleInner_self y)

/-! ### Jumping the halo requires a `y ^ n`-sized increment -/

private theorem scale_of_inner_outer {y x ε : Surreal} (hx : ScaleInner y x)
    (hxe : ¬ ScaleInner y (x + ε)) :
    ∃ n : ℕ, ArchimedeanClass.mk ε ≤ ArchimedeanClass.mk (y ^ n) := by
  rw [ScaleInner] at hxe
  push Not at hxe
  obtain ⟨n, hn⟩ := hxe
  refine ⟨n, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  exact absurd (lt_of_lt_of_le (lt_min (hx n) hlt) (ArchimedeanClass.min_le_mk_add ..))
    (not_lt.2 hn)

private theorem scale_of_outer_inner {y x ε : Surreal} (hx : ¬ ScaleInner y x)
    (hxe : ScaleInner y (x + ε)) :
    ∃ n : ℕ, ArchimedeanClass.mk ε ≤ ArchimedeanClass.mk (y ^ n) := by
  rw [ScaleInner] at hx
  push Not at hx
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hx2 : x = (x + ε) + -ε := by ring
  refine absurd ?_ (not_lt.2 hn)
  rw [hx2]
  refine lt_of_lt_of_le (lt_min (hxe n) ?_) (ArchimedeanClass.min_le_mk_add ..)
  rwa [ArchimedeanClass.mk_neg]

/-! ### One constant beats every jump -/

/-- If the increment is at least `y ^ n`-sized, then `ω * C₀` times its square is at least
`1`, where `C₀` is any strict upper bound of the family `((|y| ^ m)⁻¹) ^ 2` : from
`|ε| ≥ |y|ⁿ / k` we get `(ω C₀) ε² ≥ (ω C₀) |y|²ⁿ / k² ≥ 1`, since `k² ((|y|ⁿ)⁻¹)² <
ω C₀` — the `ω` absorbing `k²` and the `C₀` absorbing the scale. -/
private theorem one_le_bound_mul_sq {y C₀ ε : Surreal} {n : ℕ} (hy : y ≠ 0)
    (hC₀ : ∀ m : ℕ, ((|y| ^ m)⁻¹) ^ 2 < C₀)
    (h : ArchimedeanClass.mk ε ≤ ArchimedeanClass.mk (y ^ n)) :
    1 ≤ ω^ (1 : Surreal) * C₀ * ε ^ 2 := by
  have hy' : (0 : Surreal) < |y| := abs_pos.2 hy
  have hC₀0 : (0 : Surreal) < C₀ := lt_trans one_pos (by simpa using hC₀ 0)
  obtain ⟨k, hk⟩ := ArchimedeanClass.mk_le_mk.1 h
  rw [abs_pow, nsmul_eq_mul] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, zero_mul] at hk
    exact absurd hk (not_le.2 (pow_pos hy' n))
  have hkS : (0 : Surreal) < (k : ℕ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk0)
  -- `|ε| ≥ |y|ⁿ / k`
  have hle : |y| ^ n / (k : ℕ) ≤ |ε| := by
    rw [div_le_iff₀ hkS, mul_comm]
    exact hk
  -- `k² · ((|y|ⁿ)⁻¹)² < ω · C₀` : `ω` beats `k²`, `C₀` beats the scale
  have hchain : ((k : ℕ) : Surreal) ^ 2 * ((|y| ^ n)⁻¹) ^ 2 < ω^ (1 : Surreal) * C₀ := by
    calc ((k : ℕ) : Surreal) ^ 2 * ((|y| ^ n)⁻¹) ^ 2
        < ω^ (1 : Surreal) * ((|y| ^ n)⁻¹) ^ 2 := by
          refine mul_lt_mul_of_pos_right ?_ (pow_pos (inv_pos.2 (pow_pos hy' n)) 2)
          have h1 := natCast_lt_wpow_one (k ^ 2)
          push_cast at h1
          exact h1
      _ ≤ ω^ (1 : Surreal) * C₀ :=
          mul_le_mul_of_nonneg_left (hC₀ n).le (wpow_pos _).le
  -- hence `k² ≤ (ω · C₀) · (|y|ⁿ)²`
  have h2 : ((k : ℕ) : Surreal) ^ 2 ≤ ω^ (1 : Surreal) * C₀ * (|y| ^ n) ^ 2 := by
    have hcancel : ((k : ℕ) : Surreal) ^ 2 * ((|y| ^ n)⁻¹) ^ 2 * (|y| ^ n) ^ 2 =
        ((k : ℕ) : Surreal) ^ 2 := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (pow_ne_zero n (abs_ne_zero.2 hy)),
        one_pow, mul_one]
    calc ((k : ℕ) : Surreal) ^ 2
        = ((k : ℕ) : Surreal) ^ 2 * ((|y| ^ n)⁻¹) ^ 2 * (|y| ^ n) ^ 2 := hcancel.symm
      _ ≤ ω^ (1 : Surreal) * C₀ * (|y| ^ n) ^ 2 :=
          mul_le_mul_of_nonneg_right hchain.le (sq_nonneg _)
  -- assemble
  have hstep : (1 : Surreal) ≤ ω^ (1 : Surreal) * C₀ * (|y| ^ n / (k : ℕ)) ^ 2 := by
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hkS 2), one_mul]
    exact h2
  refine hstep.trans ?_
  rw [show ε ^ 2 = |ε| ^ 2 from (sq_abs ε).symm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hle 2)
    (mul_pos (wpow_pos _) hC₀0).le

/-! ### Every halo indicator is in the kernel -/

/-- **For every nonzero scale `y`, the halo indicator has derivative zero at every surreal
point**, with the single uniform constant `ω * C₀`, where `C₀` strictly bounds the
countable family `((|y| ^ n)⁻¹) ^ 2` — a bound only a field with no countable cofinal
family could supply (`exists_forall_lt`). -/
theorem hasDerivS_scaleStep {y : Surreal} (hy : y ≠ 0) (x : Surreal) :
    HasDerivS (scaleStep y) x 0 := by
  obtain ⟨C₀, hC₀⟩ := exists_forall_lt fun m ↦ ((|y| ^ m)⁻¹) ^ 2
  have hC₀0 : (0 : Surreal) < C₀ := lt_trans one_pos (by simpa using hC₀ 0)
  refine ⟨ω^ (1 : Surreal) * C₀, fun ε hε ↦ ?_⟩
  rw [zero_mul, sub_zero]
  unfold scaleStep
  by_cases hx : ScaleInner y x <;> by_cases hxe : ScaleInner y (x + ε)
  · rw [if_pos hxe, if_pos hx, sub_self, abs_zero]
    exact mul_nonneg (mul_pos (wpow_pos _) hC₀0).le (sq_nonneg ε)
  · obtain ⟨n, hn⟩ := scale_of_inner_outer hx hxe
    rw [if_neg hxe, if_pos hx, sub_zero, abs_one]
    exact one_le_bound_mul_sq hy hC₀ hn
  · obtain ⟨n, hn⟩ := scale_of_outer_inner hx hxe
    rw [if_pos hxe, if_neg hx, zero_sub, abs_neg, abs_one]
    exact one_le_bound_mul_sq hy hC₀ hn
  · rw [if_neg hxe, if_neg hx, sub_self, abs_zero]
    exact mul_nonneg (mul_pos (wpow_pos _) hC₀0).le (sq_nonneg ε)

/-! ### Translating a kernel element -/

/-- Precomposition with a translation shifts the base point of the derivative: the
increments on the two sides are literally identical. -/
theorem HasDerivS.comp_sub_const {G : Surreal → Surreal} {x a d : Surreal}
    (h : HasDerivS G (x - a) d) : HasDerivS (fun z ↦ G (z - a)) x d := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun ε hε ↦ ?_⟩
  have h1 := hC ε hε
  have h2 : x + ε - a = x - a + ε := by ring
  show |G (x + ε - a) - G (x - a) - d * ε| ≤ C * ε ^ 2
  rw [h2]
  exact h1

/-! ### The Kernel Separation Theorem -/

/-- **The Kernel Separation Theorem**: for every pair of distinct surreals there is a
function with derivative zero at every surreal point that takes different values at the
two. The derivative on `No` carries no global information whatsoever: its kernel separates
every pair of points. -/
theorem kernel_separates_points (a b : Surreal) (hab : a ≠ b) :
    ∃ F : Surreal → Surreal, (∀ x, HasDerivS F x 0) ∧ F a ≠ F b := by
  have hy : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  refine ⟨fun z ↦ scaleStep (b - a) (z - a), fun x ↦ ?_, ?_⟩
  · exact (hasDerivS_scaleStep hy (x - a)).comp_sub_const
  · show scaleStep (b - a) (a - a) ≠ scaleStep (b - a) (b - a)
    rw [sub_self, scaleStep_zero hy, scaleStep_self]
    norm_num

/-- **Antiderivative increments are ill-defined over every nondegenerate interval**: for
all `a ≠ b`, two functions with derivative zero everywhere whose increments over `[a, b]`
disagree. This subsumes `not_antideriv_unique` (`GeneralDeriv`) and
`not_antideriv_unique_infinitesimal` (`MicroKernel`). -/
theorem not_antideriv_unique_between (a b : Surreal) (hab : a ≠ b) :
    ∃ F G : Surreal → Surreal, (∀ x, HasDerivS F x 0) ∧ (∀ x, HasDerivS G x 0) ∧
      F b - F a ≠ G b - G a := by
  obtain ⟨F, hF, hFab⟩ := kernel_separates_points a b hab
  refine ⟨F, fun _ ↦ 0, hF, fun x ↦ ⟨1, fun ε hε ↦ ?_⟩, ?_⟩
  · rw [zero_mul, sub_zero, sub_self, abs_zero, one_mul]
    positivity
  · show F b - F a ≠ 0 - 0
    rw [sub_zero]
    intro h
    exact hFab (sub_eq_zero.1 h).symm

/-! ### The kernel is an additive subgroup -/

/-- Derivatives add: the error constants add, via the triangle inequality. -/
theorem HasDerivS.add {f g : Surreal → Surreal} {x df dg : Surreal}
    (hf : HasDerivS f x df) (hg : HasDerivS g x dg) :
    HasDerivS (fun s ↦ f s + g s) x (df + dg) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun ε hε ↦ ?_⟩
  have hsplit : f (x + ε) + g (x + ε) - (f x + g x) - (df + dg) * ε =
      (f (x + ε) - f x - df * ε) + (g (x + ε) - g x - dg * ε) := by ring
  show |f (x + ε) + g (x + ε) - (f x + g x) - (df + dg) * ε| ≤ (C + D) * ε ^ 2
  rw [hsplit]
  calc |(f (x + ε) - f x - df * ε) + (g (x + ε) - g x - dg * ε)|
      ≤ |f (x + ε) - f x - df * ε| + |g (x + ε) - g x - dg * ε| := abs_add_le _ _
    _ ≤ C * ε ^ 2 + D * ε ^ 2 := add_le_add (hC ε hε) (hD ε hε)
    _ = (C + D) * ε ^ 2 := by ring

/-- Derivatives negate. With `HasDerivS.add`, the functions differentiable at every point
form an additive group on which the derivative is additive — and the kernel of this map,
by `kernel_separates_points`, contains a family separating every pair of surreals. -/
theorem HasDerivS.neg {f : Surreal → Surreal} {x d : Surreal} (h : HasDerivS f x d) :
    HasDerivS (fun s ↦ -f s) x (-d) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun ε hε ↦ ?_⟩
  have hsplit : -f (x + ε) - -f x - -d * ε = -(f (x + ε) - f x - d * ε) := by ring
  show |-f (x + ε) - -f x - -d * ε| ≤ C * ε ^ 2
  rw [hsplit, abs_neg]
  exact hC ε hε

end Surreal
