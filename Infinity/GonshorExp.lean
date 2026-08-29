import Infinity.Exp
import Infinity.MicroKernel

/-!
# Gonshor's exponential at limit arguments: `exp ω = ω^ω`

Gonshor (An Introduction to the Theory of Surreal Numbers, ch. 10, after Kruskal) defines
the exponential on all of `No` by the genetic recursion

  `exp a = !{0, exp(aᴸ)·Eₙ(a − aᴸ), exp(aᴿ)·E₂ₙ₊₁(a − aᴿ) |
            exp(aᴿ)/Eₙ(aᴿ − a), exp(aᴸ)/E₂ₙ₊₁(aᴸ − a)}`

where `Eₙ(x) = Σ_{k ≤ n} xᵏ/k!` are the partial sums of the exponential series and on each
side only indices with `E₂ₙ₊₁(·) > 0` are admitted (Mantova–Matusinski survey, Thm 2.15).

This file verifies the recursion's **evaluation at limit-type arguments**: when
`a = !{s₀, s₁, … | ∅}` with each `a − sₙ` infinite, the right options vanish (the odd
partial sums at negative infinite arguments are negative, `expPartial_odd_neg`) and the
formula reduces to a left-only cut, which we prove equals a power of `ω` whose exponent is
itself a cut assembled from the `wlog`-data of the seed values (`gonshorCut_eq_wpow`).
Specialized at `ω = !{ℕ | ∅}` with the true seed values `exp n = eⁿ`, this yields the
survey's flagship computation, machine-checked (`gonshorExp_omega`):

  **`!{0, eⁿ·Eₖ(ω − n) | ∅} = ω^ω`** — the value of Gonshor's formula at `ω`.

What is *not* proved here: well-definedness/uniformity of the full recursion, or `exp` as
a total function on `No` — see `notes/gonshor-exp-design.md` for the honest scope and the
route map.

## Contents

* `Surreal.expPartial` — the partial sums `Eₙ`, with positivity, the dominant-term class
  computation `mk_expPartial` (`Eₙ(y) ~ yⁿ/n!` for infinite `y`), and the negativity of
  odd partial sums at negative infinite arguments.
* `Surreal.ofSets_left_eq_of_cofinal` — mutually cofinal left-cuts are equal (the
  simplicity-free cofinality bridge, descended from `IGame.equiv_of_exists_le`).
* `Surreal.wpow_ofSets` — CG's genetic `wpow` computed on a `Surreal`-level left-cut:
  `ω^ !{A | ∅} = !{{0} ∪ {r·ω^x : 0 < r dyadic, x ∈ A} | ∅}`.
* `Surreal.gonshorCut_eq_wpow` — the limit-step evaluation theorem.
* `Surreal.gonshorExp_omega` — the flagship: Gonshor's cut at `ω` equals `ω^ω^1`.
-/

open Set IGame

noncomputable section

namespace Surreal

/-! ### The exponential partial sums `Eₙ` -/

/-- `Eₙ(x) = Σ_{k ≤ n} xᵏ/k!`, the `n`-th partial sum of the exponential series
(Gonshor's `[x]ₙ`). -/
def expPartial (n : ℕ) (x : Surreal) : Surreal :=
  ∑ k ∈ Finset.range (n + 1), x ^ k / ((k.factorial : ℕ) : Surreal)

@[simp]
theorem expPartial_zero (x : Surreal) : expPartial 0 x = 1 := by
  simp [expPartial]

theorem expPartial_succ (n : ℕ) (x : Surreal) :
    expPartial (n + 1) x = expPartial n x + x ^ (n + 1) / (((n + 1).factorial : ℕ) : Surreal) :=
  Finset.sum_range_succ _ _

private theorem factorial_cast_pos (k : ℕ) : (0 : Surreal) < ((k.factorial : ℕ) : Surreal) := by
  exact_mod_cast k.factorial_pos

/-- Partial sums of the exponential series are positive at positive arguments (hence, in
Gonshor's formula, *all* indices `n` are admitted among the left options at a limit
argument). -/
theorem expPartial_pos {x : Surreal} (hx : 0 < x) (n : ℕ) : 0 < expPartial n x :=
  Finset.sum_pos (fun k _ ↦ div_pos (pow_pos hx k) (factorial_cast_pos k))
    (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero n))

theorem ne_zero_of_not_isFinite {y : Surreal} (h : ¬ IsFinite y) : y ≠ 0 :=
  fun h0 ↦ h (h0 ▸ isFinite_zero)

/-- Powers of an infinite surreal are strictly increasing in magnitude class
(the dual of `mk_pow_lt_mk_pow_succ'`). -/
theorem mk_pow_succ_lt_mk_pow {y : Surreal} (h : ¬ IsFinite y) (n : ℕ) :
    ArchimedeanClass.mk (y ^ (n + 1)) < ArchimedeanClass.mk (y ^ n) := by
  rw [ArchimedeanClass.mk_lt_mk]
  intro m
  have hy0 : y ≠ 0 := ne_zero_of_not_isFinite h
  have habs : (0 : Surreal) < |y| := abs_pos.2 hy0
  have hm : ((m : ℕ) : Surreal) < |y| := by
    by_contra hle
    exact h (isFinite_iff.2 ⟨m, not_lt.1 hle⟩)
  calc m • |y ^ n| = (m : Surreal) * |y| ^ n := by rw [nsmul_eq_mul, abs_pow]
    _ < |y| * |y| ^ n := by
        exact mul_lt_mul_of_pos_right hm (pow_pos habs n)
    _ = |y ^ (n + 1)| := by rw [abs_pow, pow_succ, mul_comm]

/-- The class of the `k`-th exponential-series term is that of `yᵏ`. -/
private theorem mk_expTerm (y : Surreal) (k : ℕ) :
    ArchimedeanClass.mk (y ^ k / ((k.factorial : ℕ) : Surreal)) =
      ArchimedeanClass.mk (y ^ k) := by
  rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero]

/-- **Dominant-term asymptotics**: at an infinite argument, the partial sum `Eₙ(y)` lives
in the magnitude class of its top term `yⁿ/n!`. -/
theorem mk_expPartial {y : Surreal} (h : ¬ IsFinite y) (n : ℕ) :
    ArchimedeanClass.mk (expPartial n y) = ArchimedeanClass.mk (y ^ n) := by
  induction n with
  | zero => rw [expPartial_zero, pow_zero]
  | succ n ih =>
    rw [expPartial_succ, ArchimedeanClass.mk_add_eq_mk_right, mk_expTerm]
    rw [mk_expTerm, ih]
    exact mk_pow_succ_lt_mk_pow h n

/-- Strict domination in class plus positivity of the dominator gives strict order:
if `b` strictly dominates `a` and `b > 0` then `a < b`. -/
theorem lt_of_mk_lt_of_pos {a b : Surreal}
    (h : ArchimedeanClass.mk b < ArchimedeanClass.mk a) (hb : 0 < b) : a < b :=
  lt_of_le_of_lt (le_abs_self a) (abs_of_pos hb ▸ abs_lt_abs_of_mk_lt h)

/-- **Odd partial sums are negative at negative infinite arguments.** This is the reason
Gonshor's right options `exp(aᴸ)/E₂ₙ₊₁(aᴸ − a)` vanish at a limit argument: the
admissibility condition `E₂ₙ₊₁(aᴸ − a) > 0` fails for every `n` (survey, computation of
`exp ω`: "since `E₂ₙ₊₁(n − ω) < 0` for any `n`"). -/
theorem expPartial_odd_neg {y : Surreal} (hy : y < 0) (hinf : ¬ IsFinite y) (k : ℕ) :
    expPartial (2 * k + 1) y < 0 := by
  rw [expPartial_succ]
  set t := y ^ (2 * k + 1) / (((2 * k + 1).factorial : ℕ) : Surreal) with ht
  have htneg : t < 0 :=
    div_neg_of_neg_of_pos (Odd.pow_neg ⟨k, by ring⟩ hy) (factorial_cast_pos _)
  have habs : |expPartial (2 * k) y| < |t| := by
    apply abs_lt_abs_of_mk_lt
    rw [ht, mk_expTerm, mk_expPartial hinf]
    exact mk_pow_succ_lt_mk_pow hinf (2 * k)
  have h1 : expPartial (2 * k) y ≤ |expPartial (2 * k) y| := le_abs_self _
  rw [abs_of_neg htneg] at habs
  linarith

end Surreal
