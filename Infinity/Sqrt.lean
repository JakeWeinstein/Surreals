/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.CanonicalSum
import CombinatorialGames.Surreal.Leading
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Real.Sqrt

/-!
# Square roots on the surreals: exact roots of monomials, and `√(1+u)` as a canonical sum

First steps toward `RealClosedField Surreal`. The multiplicative structure of `No` splits a
positive number as `r·ω^x·(1+u)` — real leading coefficient, ω-power scale, infinitesimal
correction — and this file takes square roots of all three layers.

**Exact roots of monomials.** The ω-map turns halving into square roots:
`(ω^ (x/2))² = ω^ x` (`wpow_half_sq`), and `realHom` transports `Real.sqrt`, so every
`r·ω^x` with `0 < r` has an exact positive square root
(`exists_sq_eq_realCast_mul_wpow`), in particular every positive leading term
(`exists_sq_eq_leadingTerm`).

**The binomial series `√(1+u)`.** Rather than fighting generalized binomial coefficients,
the Taylor coefficients of `√(1+X)` are *defined* by the square condition: `sqrtCoeff 0 = 1`
and each next coefficient is chosen so that the Cauchy convolution square telescopes —
whence the convolution identity `Σ_{i+j=k} cᵢcⱼ = [k ≤ 1]` holds by construction
(`sqrtCoeff_conv`). A sign analysis shows all coefficients are nonzero
(`sqrtCoeff_ne_zero`), so at a nonzero infinitesimal `u` the series `Σ cₖ uᵏ` is strictly
dominating (`sqrtSeries_strict_dominating`), and the Transfinite Summation Theorem plus
the canonical-sum machinery of `Infinity.CanonicalSum` yield an honest function

* `sqrtOneAdd u := hahnSum (Σ cₖ uᵏ)` — **the canonical square root of `1 + u`** — with
  `stdPart_sqrtOneAdd : st (√(1+u)) = 1`, positivity, and the first-order expansion
  `√(1+u) = 1 + u/2 + O(u²)` (`mk_sqrtOneAdd_sub_one_sub_half`).

**The square condition, mod domination.** The payoff (`mk_pow_le_mk_sq_sqrtOneAdd_sub`):
`(√(1+u))² − (1+u)` is dominated by `uⁿ` for *every* `n` — the square is `1 + u` up to an
error below every scale of the series. The proof is the partial-sum Cauchy square: the
convolution identity makes the low triangle collapse to exactly `1 + u`, and everything
else lives at class `≥ n • mk u`. Moreover the domination-level root is *unique*: any two
positive surreals whose squares hit `1 + u` below every scale agree below every scale
(`mk_pow_le_mk_sub_of_sq_approx`).

**Toward exactness.** `isHahnSum_sqrtSeries_of_sq_eq`: any exact positive square root of
`1 + u` is itself a Hahn sum of the series — so the canonical value `sqrtOneAdd u` is
birthday-minimal among all exact roots (`birthday_sqrtOneAdd_le_of_sq_eq`), agrees with
any exact root below every scale (`mk_pow_le_mk_sqrtOneAdd_sub_of_sq_eq`), and an exact
positive root is unique if it exists (`sq_eq_unique`).

**The capstone** (`exists_sq_sub_dominated`): combining all three layers, *every* positive
surreal `x` has a positive square root modulo an error dominated below `mk x` by every
power of the relative remainder `x / leadingTerm x − 1` — exact when `x` is its own
leading term.

Whether `sqrtOneAdd u` squares to *exactly* `1 + u` — the simplicity-theorem argument via
`Cut.simplestBtwn` on the cut pair `{z ≥ 0 : z² < 1+u} | {z > 0 : 1+u < z²}` — remains
open here, as does general real-closedness (`RealClosedField Surreal`).
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

/-! ### Tier 1: exact square roots of ω-powers and their real multiples -/

/-- **Halving the exponent is a square root**: `(ω^ (x/2))² = ω^ x`. -/
theorem wpow_half_sq (x : Surreal) : (ω^ (x / 2)) ^ 2 = ω^ x := by
  rw [sq, ← wpow_add, add_halves]

/-- Every ω-power has an exact positive square root. -/
theorem exists_sq_eq_wpow (x : Surreal) : ∃ z, 0 < z ∧ z ^ 2 = ω^ x :=
  ⟨ω^ (x / 2), wpow_pos _, wpow_half_sq x⟩

/-- `Real.sqrt` transports along `realHom`: the cast of `√r` squares to the cast of `r`. -/
theorem realCast_sqrt_sq {r : ℝ} (hr : 0 ≤ r) :
    ((Real.sqrt r : ℝ) : Surreal) ^ 2 = (r : Surreal) := by
  rw [← realHom_apply, ← map_pow, Real.sq_sqrt hr, realHom_apply]

/-- Exact square roots of monomials `r·ω^x`: `(√r · ω^(x/2))² = r · ω^x`. -/
theorem realCast_sqrt_mul_wpow_half_sq {r : ℝ} (hr : 0 ≤ r) (x : Surreal) :
    (((Real.sqrt r : ℝ) : Surreal) * ω^ (x / 2)) ^ 2 = (r : Surreal) * ω^ x := by
  rw [mul_pow, realCast_sqrt_sq hr, wpow_half_sq]

/-- **Every monomial `r·ω^x` with `0 < r` has an exact positive square root.** -/
theorem exists_sq_eq_realCast_mul_wpow {r : ℝ} (hr : 0 < r) (x : Surreal) :
    ∃ z, 0 < z ∧ z ^ 2 = (r : Surreal) * ω^ x := by
  refine ⟨((Real.sqrt r : ℝ) : Surreal) * ω^ (x / 2), ?_, realCast_sqrt_mul_wpow_half_sq hr.le x⟩
  exact mul_pos (by exact_mod_cast Real.sqrt_pos.2 hr) (wpow_pos _)

/-- **Every positive leading term has an exact positive square root**: the first layer of
real-closedness, via `wlog`-halving and `Real.sqrt` on the leading coefficient. -/
theorem exists_sq_eq_leadingTerm {x : Surreal} (hx : 0 < x) :
    ∃ z, 0 < z ∧ z ^ 2 = leadingTerm x := by
  rw [leadingTerm]
  exact exists_sq_eq_realCast_mul_wpow (leadingCoeff_pos_iff.2 hx) x.wlog

/-! ### Tier 2, part I: the square-root coefficients, defined by the square condition

The Taylor coefficients of `√(1+X)` are defined recursively so that the Cauchy convolution
identity holds *by construction*: `sqrtCoeff 0 = 1`, and each `sqrtCoeff k` (`k ≥ 1`) is
exactly what is needed to make `Σ_{i+j=k} cᵢcⱼ` equal `1` for `k = 1` and `0` for `k ≥ 2`.
No generalized binomial coefficients are ever mentioned. -/

/-- The Taylor coefficients of `√(1+X)`, defined by the square condition: the `k`-th
coefficient (`k ≥ 2`) kills the `k`-th convolution layer of the square. -/
def sqrtCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => 1 / 2
  | k + 2 =>
    -(∑ i ∈ (Finset.Ioo 0 (k + 2)).attach, sqrtCoeff i.1 * sqrtCoeff (k + 2 - i.1)) / 2
decreasing_by
  · exact (Finset.mem_Ioo.1 i.2).2
  · have h := Finset.mem_Ioo.1 i.2
    omega

@[simp]
theorem sqrtCoeff_zero : sqrtCoeff 0 = 1 := by
  rw [sqrtCoeff]

@[simp]
theorem sqrtCoeff_one : sqrtCoeff 1 = 1 / 2 := by
  rw [sqrtCoeff]

theorem sqrtCoeff_add_two (k : ℕ) :
    sqrtCoeff (k + 2) =
      -(∑ i ∈ Finset.Ioo 0 (k + 2), sqrtCoeff i * sqrtCoeff (k + 2 - i)) / 2 := by
  rw [sqrtCoeff]
  congr 1
  congr 1
  exact Finset.sum_attach _ fun j ↦ sqrtCoeff j * sqrtCoeff (k + 2 - j)

/-- The recursion, repackaged: for `k ≥ 1`, twice the coefficient plus the interior
convolution sum is `1` at `k = 1` and `0` beyond. -/
theorem two_mul_sqrtCoeff_add_conv {k : ℕ} (hk : 1 ≤ k) :
    2 * sqrtCoeff k + ∑ i ∈ Finset.Ioo 0 k, sqrtCoeff i * sqrtCoeff (k - i) =
      if k = 1 then 1 else 0 := by
  obtain rfl | ⟨m, rfl⟩ : k = 1 ∨ ∃ m, k = m + 2 := by
    rcases k with _ | _ | m
    · omega
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl⟩
  · rw [Finset.sum_eq_zero fun i hi ↦ by rw [Finset.mem_Ioo] at hi; omega]
    norm_num
  · rw [sqrtCoeff_add_two, if_neg (by omega)]
    ring

private theorem Ico_zero_add_one_eq_Ioo (k : ℕ) : Finset.Ico (0 + 1) k = Finset.Ioo 0 k := by
  ext i
  simp only [Finset.mem_Ico, Finset.mem_Ioo]
  omega

/-- The interior sum peeled from the antidiagonal: for `0 < k`, the full convolution layer
is twice the top coefficient plus the interior sum. -/
private theorem antidiagonal_sum_sqrtCoeff {k : ℕ} (hk : 0 < k) :
    ∑ p ∈ Finset.antidiagonal k, sqrtCoeff p.1 * sqrtCoeff p.2 =
      2 * sqrtCoeff k + ∑ i ∈ Finset.Ioo 0 k, sqrtCoeff i * sqrtCoeff (k - i) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  dsimp only
  rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk,
    Ico_zero_add_one_eq_Ioo, Nat.sub_zero, Nat.sub_self, sqrtCoeff_zero, one_mul, mul_one]
  ring

/-- **The convolution identity, by construction**: the Cauchy square of the coefficient
sequence is `1 + X` — the `k`-th convolution layer is `1` for `k ≤ 1` and `0` beyond. -/
theorem sqrtCoeff_conv (k : ℕ) :
    ∑ p ∈ Finset.antidiagonal k, sqrtCoeff p.1 * sqrtCoeff p.2 =
      if k ≤ 1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [antidiagonal_sum_sqrtCoeff hk, two_mul_sqrtCoeff_add_conv hk]
    split_ifs <;> first | rfl | (exfalso; omega)

private theorem neg_one_pow_congr {a b : ℕ} (h : a % 2 = b % 2) :
    (-1 : ℝ) ^ a = (-1 : ℝ) ^ b := by
  rcases Nat.even_or_odd a with ha | ha
  · have ha' := Nat.even_iff.1 ha
    rw [ha.neg_one_pow, (Nat.even_iff.2 (by omega)).neg_one_pow]
  · have ha' := Nat.odd_iff.1 ha
    rw [ha.neg_one_pow, (Nat.odd_iff.2 (by omega)).neg_one_pow]

/-- The sign pattern: `(−1)^(k+1) · sqrtCoeff k > 0` for `k ≥ 1` — coefficients alternate
in sign and never vanish. Proved by strong induction directly from the recursion: interior
products all share the sign `(−1)^k`, so the interior sum is strictly one-signed. -/
theorem neg_one_pow_mul_sqrtCoeff_pos :
    ∀ k : ℕ, 1 ≤ k → 0 < (-1 : ℝ) ^ (k + 1) * sqrtCoeff k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain rfl | ⟨m, rfl⟩ : k = 1 ∨ ∃ m, k = m + 2 := by
      rcases k with _ | _ | m
      · omega
      · exact Or.inl rfl
      · exact Or.inr ⟨m, rfl⟩
    · norm_num
    · have hS : 0 < (-1 : ℝ) ^ (m + 2) *
          ∑ i ∈ Finset.Ioo 0 (m + 2), sqrtCoeff i * sqrtCoeff (m + 2 - i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_pos (fun i hi ↦ ?_) ⟨1, Finset.mem_Ioo.2 ⟨one_pos, by omega⟩⟩
        rw [Finset.mem_Ioo] at hi
        have h1 : 0 < (-1 : ℝ) ^ (i + 1) * sqrtCoeff i := ih i (by omega) (by omega)
        have h2 : 0 < (-1 : ℝ) ^ ((m + 2 - i) + 1) * sqrtCoeff (m + 2 - i) :=
          ih (m + 2 - i) (by omega) (by omega)
        have hkey : (-1 : ℝ) ^ (m + 2) * (sqrtCoeff i * sqrtCoeff (m + 2 - i)) =
            ((-1 : ℝ) ^ (i + 1) * sqrtCoeff i) *
              ((-1 : ℝ) ^ ((m + 2 - i) + 1) * sqrtCoeff (m + 2 - i)) := by
          rw [mul_mul_mul_comm, ← pow_add,
            neg_one_pow_congr (a := m + 2) (b := (i + 1) + ((m + 2 - i) + 1)) (by omega)]
        rw [hkey]
        exact mul_pos h1 h2
      rw [sqrtCoeff_add_two]
      have hgoal : (-1 : ℝ) ^ (m + 2 + 1) *
          (-(∑ i ∈ Finset.Ioo 0 (m + 2), sqrtCoeff i * sqrtCoeff (m + 2 - i)) / 2) =
          ((-1 : ℝ) ^ (m + 2) *
            ∑ i ∈ Finset.Ioo 0 (m + 2), sqrtCoeff i * sqrtCoeff (m + 2 - i)) / 2 := by
        rw [pow_succ]
        ring
      rw [hgoal]
      exact div_pos hS two_pos

/-- **All square-root coefficients are nonzero** — the key hypothesis for strict
domination of the series. -/
theorem sqrtCoeff_ne_zero (k : ℕ) : sqrtCoeff k ≠ 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · intro h0
    have h := neg_one_pow_mul_sqrtCoeff_pos k hk
    rw [h0, mul_zero] at h
    exact lt_irrefl 0 h

/-- Sanity check, kernel-computed: the recursion reproduces `(1/2 choose 2) = −1/8`. -/
example : sqrtCoeff 2 = -(1 / 8) := by
  have h : Finset.Ioo 0 2 = {1} := by decide
  rw [show (2 : ℕ) = 0 + 2 from rfl, sqrtCoeff_add_two, h, Finset.sum_singleton]
  norm_num

/-- Sanity check, kernel-computed: the recursion reproduces `(1/2 choose 3) = 1/16`. -/
example : sqrtCoeff 3 = 1 / 16 := by
  have h2 : sqrtCoeff 2 = -(1 / 8) := by
    have h : Finset.Ioo 0 2 = {1} := by decide
    rw [show (2 : ℕ) = 0 + 2 from rfl, sqrtCoeff_add_two, h, Finset.sum_singleton]
    norm_num
  have h : Finset.Ioo 0 3 = {1, 2} := by decide
  rw [show (3 : ℕ) = 1 + 2 from rfl, sqrtCoeff_add_two, h]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h2]

/-! ### Tier 2, part II: the series `Σ cₖ uᵏ` and its canonical sum `√(1+u)` -/

/-- The square-root series at `u`: the `k`-th term is `sqrtCoeff k · uᵏ`. -/
def sqrtSeries (u : Surreal) (k : ℕ) : Surreal :=
  (sqrtCoeff k : Surreal) * u ^ k

theorem sqrtSeries_apply (u : Surreal) (k : ℕ) :
    sqrtSeries u k = (sqrtCoeff k : Surreal) * u ^ k :=
  rfl

/-- The class of a series term: `mk (cₖ uᵏ) = k • mk u` (the coefficients never vanish). -/
theorem mk_sqrtSeries (u : Surreal) (k : ℕ) :
    ArchimedeanClass.mk (sqrtSeries u k) = k • ArchimedeanClass.mk u := by
  rw [sqrtSeries, ArchimedeanClass.mk_mul, mk_realCast (sqrtCoeff_ne_zero k), zero_add,
    ArchimedeanClass.mk_pow]

/-- The square-root series at a nonzero infinitesimal is strictly dominating. -/
theorem sqrtSeries_strict_dominating {u : Surreal} (hu : Infinitesimal u) (hu0 : u ≠ 0)
    (k : ℕ) :
    ArchimedeanClass.mk (sqrtSeries u k) < ArchimedeanClass.mk (sqrtSeries u (k + 1)) := by
  rw [mk_sqrtSeries, mk_sqrtSeries, ← ArchimedeanClass.mk_pow, ← ArchimedeanClass.mk_pow]
  exact mk_pow_lt_mk_pow_succ' hu hu0 k

/-- **The square-root series sums**: at any nonzero infinitesimal, `Σ cₖ uᵏ` has a
transfinite (Hahn) sum in `No`. -/
theorem exists_isHahnSum_sqrtSeries {u : Surreal} (hu : Infinitesimal u) (hu0 : u ≠ 0) :
    ∃ x, IsHahnSum (sqrtSeries u) x :=
  exists_isHahnSum (sqrtSeries_strict_dominating hu hu0)

/-- **The canonical square root of `1 + u`**, for `u` a nonzero infinitesimal: the
birthday-simplest transfinite sum of the square-root series `Σ cₖ uᵏ`. -/
def sqrtOneAdd (u : Surreal) (hu : Infinitesimal u) (hu0 : u ≠ 0) : Surreal :=
  hahnSum (sqrtSeries_strict_dominating hu hu0)

theorem isHahnSum_sqrtOneAdd {u : Surreal} (hu : Infinitesimal u) (hu0 : u ≠ 0) :
    IsHahnSum (sqrtSeries u) (sqrtOneAdd u hu hu0) :=
  isHahnSum_hahnSum _

/-- The canonical square root is the birthday-minimal Hahn sum of the series. -/
theorem birthday_sqrtOneAdd_le {u : Surreal} (hu : Infinitesimal u) (hu0 : u ≠ 0)
    {z : Surreal} (hz : IsHahnSum (sqrtSeries u) z) :
    (sqrtOneAdd u hu hu0).birthday ≤ z.birthday :=
  birthday_hahnSum_le _ hz

/-! #### Standard part and first-order behavior -/

private theorem sqrtSeries_apply_zero (u : Surreal) : sqrtSeries u 0 = 1 := by
  rw [sqrtSeries, sqrtCoeff_zero, pow_zero, mul_one, Real.toSurreal_one]

private theorem sqrtSeries_apply_one (u : Surreal) : sqrtSeries u 1 = u / 2 := by
  have h2 : ((1 / 2 : ℝ) : Surreal) = 1 / 2 := by norm_num
  rw [sqrtSeries, sqrtCoeff_one, pow_one, h2]
  ring

/-- Terms of the square-root series at an infinitesimal are finite. -/
private theorem isFinite_sqrtSeries {u : Surreal} (hu : Infinitesimal u) (k : ℕ) :
    IsFinite (sqrtSeries u k) := by
  rw [IsFinite, mk_sqrtSeries]
  exact nsmul_nonneg hu.le k

/-- The standard part of a partial sum: `0` at stage `0`, and `1` from stage `1` on. -/
private theorem stdPart_partialSum_sqrtSeries {u : Surreal} (hu : Infinitesimal u) (m : ℕ) :
    stdPart (partialSum (sqrtSeries u) m) = if 1 ≤ m then 1 else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [partialSum_zero, if_neg (by omega), ArchimedeanClass.stdPart_zero]
  · rw [partialSum, stdPart_sum fun k _ ↦ isFinite_sqrtSeries hu k,
      Finset.sum_eq_single_of_mem 0 (mem_range.2 hm) ?_, if_pos (show 1 ≤ m by omega)]
    · rw [sqrtSeries_apply_zero, ArchimedeanClass.stdPart_one]
    · intro k _ hk
      apply Infinitesimal.stdPart_eq_zero
      rw [Infinitesimal, mk_sqrtSeries]
      have h1 : (0 : ArchimedeanClass Surreal) < 1 • ArchimedeanClass.mk u := by
        rwa [one_nsmul]
      exact h1.trans_le (nsmul_le_nsmul_left hu.le (by omega))

/-- Partial sums (from stage `1` on) lie in the class of `1`. -/
private theorem mk_partialSum_sqrtSeries {u : Surreal} (hu : Infinitesimal u) {m : ℕ}
    (hm : 1 ≤ m) :
    ArchimedeanClass.mk (partialSum (sqrtSeries u) m) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [stdPart_partialSum_sqrtSeries hu, if_pos hm]
  norm_num

/-- **`st √(1+u) = 1`**: the canonical square root is infinitesimally close to `1`. -/
theorem stdPart_sqrtOneAdd {u : Surreal} (hu : Infinitesimal u) (hu0 : u ≠ 0) :
    stdPart (sqrtOneAdd u hu hu0) = 1 := by
  have h := isHahnSum_sqrtOneAdd hu hu0 1
  have hps : partialSum (sqrtSeries u) 1 = 1 := by
    rw [partialSum, Finset.sum_range_one, sqrtSeries_apply_zero]
  rw [hps, mk_sqrtSeries, one_nsmul] at h
  have hres : Infinitesimal (sqrtOneAdd u hu hu0 - 1) := lt_of_lt_of_le hu h
  have hsplit : sqrtOneAdd u hu hu0 = 1 + (sqrtOneAdd u hu hu0 - 1) := by ring
  rw [hsplit, stdPart_add_eq_left hres, ArchimedeanClass.stdPart_one]

/-- The canonical square root lies in the class of `1`. -/
theorem mk_sqrtOneAdd {u : Surreal} (hu : Infinitesimal u) (hu0 : u ≠ 0) :
    ArchimedeanClass.mk (sqrtOneAdd u hu hu0) = 0 :=
  mk_eq_zero_of_stdPart_ne_zero (by rw [stdPart_sqrtOneAdd]; norm_num)

/-- **The canonical square root is positive.** -/
theorem sqrtOneAdd_pos {u : Surreal} (hu : Infinitesimal u) (hu0 : u ≠ 0) :
    0 < sqrtOneAdd u hu hu0 := by
  have hfin : IsFinite (sqrtOneAdd u hu hu0) := by
    rw [IsFinite, mk_sqrtOneAdd]
  have hres : Infinitesimal (sqrtOneAdd u hu hu0 - 1) := by
    have h := infinitesimal_sub_stdPart hfin
    rwa [stdPart_sqrtOneAdd, Real.toSurreal_one] at h
  have habs : |sqrtOneAdd u hu hu0 - 1| < ((1 / 2 : ℚ) : Surreal) :=
    hres.abs_lt_ratCast (by norm_num)
  have h1 := abs_lt.1 habs
  have hq : ((1 / 2 : ℚ) : Surreal) < 1 := by
    rw [show (1 : Surreal) = ((1 : ℚ) : Surreal) by norm_num]
    exact_mod_cast (by norm_num : (1 / 2 : ℚ) < 1)
  linarith [h1.1]

/-- **First-order expansion**: `√(1+u) = 1 + u/2 + O(u²)` — the residual beyond the linear
truncation is dominated by `u²`. -/
theorem mk_sqrtOneAdd_sub_one_sub_half {u : Surreal} (hu : Infinitesimal u) (hu0 : u ≠ 0) :
    ArchimedeanClass.mk (u ^ 2) ≤
      ArchimedeanClass.mk (sqrtOneAdd u hu hu0 - (1 + u / 2)) := by
  have h := isHahnSum_sqrtOneAdd hu hu0 2
  have hps : partialSum (sqrtSeries u) 2 = 1 + u / 2 := by
    rw [partialSum, Finset.sum_range_succ, Finset.sum_range_one, sqrtSeries_apply_zero,
      sqrtSeries_apply_one]
  rw [hps] at h
  refine le_trans (le_of_eq ?_) h
  rw [mk_sqrtSeries, ArchimedeanClass.mk_pow]

/-! ### Tier 2, part III: the square condition modulo domination

The partial-sum Cauchy square: the convolution identity `sqrtCoeff_conv` collapses the low
triangle `{(i,j) : i+j < n}` of the product of partial sums to exactly `1 + u`, so the
square of the canonical sum misses `1 + u` only by terms of total degree `≥ n` — for
every `n`. -/

private theorem le_mk_add {c : ArchimedeanClass Surreal} {a b : Surreal}
    (ha : c ≤ ArchimedeanClass.mk a) (hb : c ≤ ArchimedeanClass.mk b) :
    c ≤ ArchimedeanClass.mk (a + b) :=
  le_trans (le_min ha hb) (ArchimedeanClass.min_le_mk_add ..)

private theorem le_mk_sum {ι : Type*} {c : ArchimedeanClass Surreal} {s : Finset ι}
    {u : ι → Surreal} (h : ∀ i ∈ s, c ≤ ArchimedeanClass.mk (u i)) :
    c ≤ ArchimedeanClass.mk (∑ i ∈ s, u i) := by
  induction s using Finset.cons_induction with
  | empty =>
    have h0 : ArchimedeanClass.mk (0 : Surreal) = ⊤ := ArchimedeanClass.mk_eq_top_iff.2 rfl
    rw [Finset.sum_empty, h0]
    exact le_top
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact le_mk_add (h a (Finset.mem_cons_self ..))
      (ih fun i hi ↦ h i (Finset.mem_cons_of_mem hi))

/-- The triangle `{(i,j) : i+j < n}` is the union of the antidiagonals below `n`. -/
private theorem triangle_eq_biUnion (n : ℕ) :
    ((range n ×ˢ range n).filter fun p ↦ p.1 + p.2 < n) =
      (range n).biUnion Finset.antidiagonal := by
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_biUnion,
    Finset.mem_antidiagonal]
  constructor
  · rintro ⟨⟨_, _⟩, h⟩
    exact ⟨i + j, h, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    omega

/-- One convolution layer of the square, evaluated: `Σ_{i+j=k} (cᵢuⁱ)(cⱼuʲ)` is `uᵏ` times
the layer of the coefficient convolution — `1·uᵏ` for `k ≤ 1`, and `0` beyond. -/
private theorem sqrtSeries_layer (u : Surreal) (k : ℕ) :
    ∑ p ∈ Finset.antidiagonal k, sqrtSeries u p.1 * sqrtSeries u p.2 =
      ((if k ≤ 1 then 1 else 0 : ℝ) : Surreal) * u ^ k := by
  have hterm : ∀ p ∈ Finset.antidiagonal k,
      sqrtSeries u p.1 * sqrtSeries u p.2 =
        ((sqrtCoeff p.1 * sqrtCoeff p.2 : ℝ) : Surreal) * u ^ k := by
    rintro ⟨i, j⟩ hp
    rw [Finset.mem_antidiagonal] at hp
    dsimp only
    rw [sqrtSeries, sqrtSeries, Real.toSurreal_mul, ← hp, pow_add]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  congr 1
  rw [← sqrtCoeff_conv k]
  exact (map_sum realHom _ _).symm

/-- Summing the layers up to any stage `n ≥ 2` gives exactly `1 + u`. -/
private theorem sum_sqrtSeries_layers (u : Surreal) {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ range n, ((if k ≤ 1 then 1 else 0 : ℝ) : Surreal) * u ^ k = 1 + u := by
  have hzero : ∀ k ∈ range n, k ∉ range 2 →
      ((if k ≤ 1 then 1 else 0 : ℝ) : Surreal) * u ^ k = 0 := by
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [if_neg (by omega), Real.toSurreal_zero, zero_mul]
  have hsub : range 2 ⊆ range n := fun x hx ↦
    Finset.mem_range.2 (by have := Finset.mem_range.1 hx; omega)
  rw [← Finset.sum_subset hsub hzero, Finset.sum_range_succ,
    Finset.sum_range_one, if_pos (by omega : (0 : ℕ) ≤ 1), if_pos (by omega : (1 : ℕ) ≤ 1),
    Real.toSurreal_one, pow_zero, pow_one, mul_one, one_mul]

/-- The partial-sum Cauchy square: for `n ≥ 2`, the square of the `n`-th partial sum
misses `1 + u` by exactly the high-degree corner `{(i,j) : i,j < n ≤ i+j}` of the square
of indices. -/
private theorem partialSum_sq_sub (u : Surreal) {n : ℕ} (hn : 2 ≤ n) :
    partialSum (sqrtSeries u) n * partialSum (sqrtSeries u) n - (1 + u) =
      ∑ p ∈ (range n ×ˢ range n).filter fun p ↦ ¬ p.1 + p.2 < n,
        sqrtSeries u p.1 * sqrtSeries u p.2 := by
  have hsq : partialSum (sqrtSeries u) n * partialSum (sqrtSeries u) n =
      ∑ p ∈ range n ×ˢ range n, sqrtSeries u p.1 * sqrtSeries u p.2 := by
    rw [partialSum, Finset.sum_mul_sum, Finset.sum_product]
  have hdisj : ∀ a ∈ range n, ∀ b ∈ range n, a ≠ b →
      Disjoint (Finset.antidiagonal a) (Finset.antidiagonal b) := by
    intro a _ b _ hab
    simp only [Finset.disjoint_left, Finset.mem_antidiagonal]
    rintro ⟨i, j⟩ h1 h2
    exact hab (h1 ▸ h2)
  have hP : (1 : Surreal) + u =
      ∑ p ∈ (range n ×ˢ range n).filter fun p ↦ p.1 + p.2 < n,
        sqrtSeries u p.1 * sqrtSeries u p.2 := by
    rw [triangle_eq_biUnion, Finset.sum_biUnion hdisj, ← sum_sqrtSeries_layers u hn]
    exact (Finset.sum_congr rfl fun k _ ↦ sqrtSeries_layer u k).symm
  rw [hsq, hP, ← Finset.sum_filter_add_sum_filter_not (range n ×ˢ range n)
    fun p ↦ p.1 + p.2 < n]
  ring

/-- **The square condition, modulo domination** (the main theorem): for a nonzero
infinitesimal `u`, the square of the canonical square root misses `1 + u` by less than
*every* power of `u` — the error `(√(1+u))² − (1+u)` is dominated by `uⁿ` for all `n`.
(No positivity of `u` is needed: squaring a single series admits no cancellation between
scales.) -/
theorem mk_pow_le_mk_sq_sqrtOneAdd_sub {u : Surreal} (hu : Infinitesimal u) (hu0 : u ≠ 0)
    (n : ℕ) :
    ArchimedeanClass.mk (u ^ n) ≤
      ArchimedeanClass.mk (sqrtOneAdd u hu hu0 ^ 2 - (1 + u)) := by
  have hm0 : (0 : ArchimedeanClass Surreal) ≤ ArchimedeanClass.mk u := hu.le
  -- work at stage `N := n + 2 ≥ 2`, which dominates stage `n`
  have hstep : ((n + 2 : ℕ)) • ArchimedeanClass.mk u ≤
      ArchimedeanClass.mk (sqrtOneAdd u hu hu0 ^ 2 - (1 + u)) := by
    have hsplit : sqrtOneAdd u hu hu0 ^ 2 - (1 + u) =
        (sqrtOneAdd u hu hu0 - partialSum (sqrtSeries u) (n + 2)) *
            (sqrtOneAdd u hu hu0 + partialSum (sqrtSeries u) (n + 2)) +
          (partialSum (sqrtSeries u) (n + 2) * partialSum (sqrtSeries u) (n + 2) -
            (1 + u)) := by
      ring
    rw [hsplit]
    refine le_mk_add ?_ ?_
    -- the factored part: the Hahn residual enters once, the cofactor is finite
    · rw [ArchimedeanClass.mk_mul]
      have h1 : ((n + 2 : ℕ)) • ArchimedeanClass.mk u ≤
          ArchimedeanClass.mk (sqrtOneAdd u hu hu0 - partialSum (sqrtSeries u) (n + 2)) := by
        have h := isHahnSum_sqrtOneAdd hu hu0 (n + 2)
        rwa [mk_sqrtSeries] at h
      have h2 : (0 : ArchimedeanClass Surreal) ≤
          ArchimedeanClass.mk (sqrtOneAdd u hu hu0 + partialSum (sqrtSeries u) (n + 2)) := by
        refine IsFinite.add ?_ ?_
        · rw [IsFinite, mk_sqrtOneAdd]
        · exact isFinite_sum fun k _ ↦ isFinite_sqrtSeries hu k
      calc ((n + 2 : ℕ)) • ArchimedeanClass.mk u
          = ((n + 2 : ℕ)) • ArchimedeanClass.mk u + 0 := (add_zero _).symm
        _ ≤ _ := add_le_add h1 h2
    -- the high-degree corner: every term has total degree ≥ n + 2
    · rw [partialSum_sq_sub u (by omega)]
      refine le_mk_sum fun p hp ↦ ?_
      obtain ⟨-, hsum⟩ := Finset.mem_filter.1 hp
      rw [not_lt] at hsum
      rw [ArchimedeanClass.mk_mul, mk_sqrtSeries, mk_sqrtSeries, ← add_nsmul]
      exact nsmul_le_nsmul_left hm0 hsum
  calc ArchimedeanClass.mk (u ^ n) = (n : ℕ) • ArchimedeanClass.mk u :=
        ArchimedeanClass.mk_pow n u
    _ ≤ ((n + 2 : ℕ)) • ArchimedeanClass.mk u := nsmul_le_nsmul_left hm0 (by omega)
    _ ≤ _ := hstep

/-! ### Tier 3: toward exactness — exact roots are Hahn sums of the series

The full simplicity argument (that `sqrtOneAdd u` squares to *exactly* `1 + u`) is open
here; what we can prove is the converse pincer: **any** exact positive square root of
`1 + u` is a Hahn sum of the square-root series. Hence the canonical value is
birthday-minimal among all exact roots, agrees with any exact root below every scale of
the series, and exact positive roots are unique. -/

/-- Squaring is injective on positive surreals. -/
theorem sq_eq_unique {y z : Surreal} (hy : 0 < y) (hz : 0 < z) (h : y ^ 2 = z ^ 2) :
    y = z := by
  have h1 : (y - z) * (y + z) = 0 := by
    have h2 : (y - z) * (y + z) = y ^ 2 - z ^ 2 := by ring
    rw [h2, h, sub_self]
  rcases mul_eq_zero.1 h1 with h | h
  · exact sub_eq_zero.1 h
  · linarith

/-- For `n ≥ 1`, the defect of the `n`-th partial sum from `1 + u` sits at class
`≥ n • mk u`. -/
private theorem le_mk_one_add_sub_partialSum_sq {u : Surreal} (hu : Infinitesimal u)
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℕ) • ArchimedeanClass.mk u ≤
      ArchimedeanClass.mk
        ((1 + u) - partialSum (sqrtSeries u) n * partialSum (sqrtSeries u) n) := by
  rcases eq_or_lt_of_le hn with h1 | h2
  · -- stage 1: the defect is exactly `u`
    subst h1
    have hps : partialSum (sqrtSeries u) 1 = 1 := by
      rw [partialSum, Finset.sum_range_one, sqrtSeries_apply_zero]
    rw [hps, one_mul, show (1 : Surreal) + u - 1 = u by ring, one_nsmul]
  · -- stage ≥ 2: the Cauchy-square identity
    have hkey : (1 + u) - partialSum (sqrtSeries u) n * partialSum (sqrtSeries u) n =
        -(partialSum (sqrtSeries u) n * partialSum (sqrtSeries u) n - (1 + u)) := by
      ring
    rw [hkey, ArchimedeanClass.mk_neg, partialSum_sq_sub u h2]
    refine le_mk_sum fun p hp ↦ ?_
    obtain ⟨-, hsum⟩ := Finset.mem_filter.1 hp
    rw [not_lt] at hsum
    rw [ArchimedeanClass.mk_mul, mk_sqrtSeries, mk_sqrtSeries, ← add_nsmul]
    exact nsmul_le_nsmul_left hu.le hsum

/-- A positive surreal whose square is infinitesimally close to `1 + u` is itself finite
with standard part `1`. -/
private theorem isFinite_and_stdPart_eq_one_of_sq {u r : Surreal} (hu : Infinitesimal u)
    (hr : 0 < r) (h : Infinitesimal (r ^ 2 - (1 + u))) :
    IsFinite r ∧ stdPart r = 1 := by
  have h1u : ArchimedeanClass.mk (1 + u) = 0 :=
    mk_eq_zero_of_stdPart_ne_zero (by
      rw [ArchimedeanClass.stdPart_add_eq_left hu, ArchimedeanClass.stdPart_one]
      norm_num)
  have hsplit : r ^ 2 = (1 + u) + (r ^ 2 - (1 + u)) := by ring
  -- the square lies in the class of `1`
  have hsq0 : ArchimedeanClass.mk (r ^ 2) = 0 := by
    rcases eq_or_ne (r ^ 2 - (1 + u)) 0 with he | he
    · rw [hsplit, he, add_zero]
      exact h1u
    · have hlt : ArchimedeanClass.mk (1 + u) < ArchimedeanClass.mk (r ^ 2 - (1 + u)) := by
        rw [h1u]
        exact h
      rw [hsplit, ArchimedeanClass.mk_add_eq_mk_left hlt]
      exact h1u
  have hsum0 : ArchimedeanClass.mk r + ArchimedeanClass.mk r = 0 := by
    rw [← ArchimedeanClass.mk_mul, ← sq]
    exact hsq0
  -- `mk r = 0` by trichotomy: a nonzero class doubles to a nonzero class
  have hmkr : ArchimedeanClass.mk r = 0 := by
    rcases lt_trichotomy (ArchimedeanClass.mk r) 0 with hlt | heq | hgt
    · exfalso
      have hle : ArchimedeanClass.mk r + ArchimedeanClass.mk r ≤
          ArchimedeanClass.mk r + 0 := add_le_add_right hlt.le _
      rw [add_zero, hsum0] at hle
      exact absurd (hle.trans_lt hlt) (lt_irrefl 0)
    · exact heq
    · exfalso
      have hle : ArchimedeanClass.mk r + 0 ≤
          ArchimedeanClass.mk r + ArchimedeanClass.mk r := add_le_add_right hgt.le _
      rw [add_zero, hsum0] at hle
      exact absurd (hgt.trans_le hle) (lt_irrefl 0)
  have hfin : IsFinite r := by rw [IsFinite, hmkr]
  -- `st r = 1`: the nonnegative root of `st ((1+u) + infinitesimal) = 1`
  have hstd2 : stdPart r ^ 2 = 1 := by
    rw [← stdPart_pow hfin, hsplit, ArchimedeanClass.stdPart_add_eq_left h,
      ArchimedeanClass.stdPart_add_eq_left hu, ArchimedeanClass.stdPart_one]
  refine ⟨hfin, ?_⟩
  have hnn : (0 : ℝ) ≤ stdPart r := ArchimedeanClass.stdPart_nonneg hr.le
  have hfact : (stdPart r - 1) * (stdPart r + 1) = 0 := by
    have h2 : (stdPart r - 1) * (stdPart r + 1) = stdPart r ^ 2 - 1 := by ring
    rw [h2, hstd2, sub_self]
  rcases mul_eq_zero.1 hfact with h | h
  · linarith
  · linarith

/-- **Exact roots are Hahn sums**: any positive surreal squaring to exactly `1 + u` is a
Hahn sum of the square-root series. (So if the classical simplicity argument produces an
exact root, it is already in the domination band of the canonical series.) -/
theorem isHahnSum_sqrtSeries_of_sq_eq {u r : Surreal} (hu : Infinitesimal u)
    (hr : 0 < r) (hsq : r ^ 2 = 1 + u) : IsHahnSum (sqrtSeries u) r := by
  have hrr : r * r = 1 + u := (sq r).symm.trans hsq
  obtain ⟨hfin, hstd⟩ := isFinite_and_stdPart_eq_one_of_sq hu hr
    (by rw [hsq, sub_self]; exact infinitesimal_zero)
  have hmkr : ArchimedeanClass.mk r = 0 :=
    mk_eq_zero_of_stdPart_ne_zero (by rw [hstd]; norm_num)
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [partialSum_zero, sub_zero, mk_sqrtSeries, zero_nsmul, hmkr]
  · -- factor the defect: `(r − sₙ)(r + sₙ) = (1+u) − sₙ²`, and `r + sₙ` has class 0
    have hfins : IsFinite (partialSum (sqrtSeries u) n) := by
      rw [partialSum]
      exact isFinite_sum fun k _ ↦ isFinite_sqrtSeries hu k
    have hmkadd : ArchimedeanClass.mk (r + partialSum (sqrtSeries u) n) = 0 :=
      mk_eq_zero_of_stdPart_ne_zero (by
        rw [ArchimedeanClass.stdPart_add hfin hfins, hstd,
          stdPart_partialSum_sqrtSeries hu, if_pos (show 1 ≤ n by omega)]
        norm_num)
    have hfactor : (r - partialSum (sqrtSeries u) n) * (r + partialSum (sqrtSeries u) n) =
        (1 + u) - partialSum (sqrtSeries u) n * partialSum (sqrtSeries u) n := by
      rw [← hrr]
      ring
    have hmk : ArchimedeanClass.mk (r - partialSum (sqrtSeries u) n) =
        ArchimedeanClass.mk
          ((1 + u) - partialSum (sqrtSeries u) n * partialSum (sqrtSeries u) n) := by
      rw [← hfactor, ArchimedeanClass.mk_mul, hmkadd, add_zero]
    rw [mk_sqrtSeries, hmk]
    exact le_mk_one_add_sub_partialSum_sq hu hn

/-- **Birthday minimality against exact roots**: the canonical series sum is at least as
simple as any exact positive square root of `1 + u`. -/
theorem birthday_sqrtOneAdd_le_of_sq_eq {u r : Surreal} (hu : Infinitesimal u) (hu0 : u ≠ 0)
    (hr : 0 < r) (hsq : r ^ 2 = 1 + u) :
    (sqrtOneAdd u hu hu0).birthday ≤ r.birthday :=
  birthday_sqrtOneAdd_le hu hu0 (isHahnSum_sqrtSeries_of_sq_eq hu hr hsq)

/-- The canonical square root agrees with any exact positive root below every scale:
`√(1+u) − r` is dominated by `uⁿ` for all `n`. -/
theorem mk_pow_le_mk_sqrtOneAdd_sub_of_sq_eq {u r : Surreal} (hu : Infinitesimal u)
    (hu0 : u ≠ 0) (hr : 0 < r) (hsq : r ^ 2 = 1 + u) (n : ℕ) :
    ArchimedeanClass.mk (u ^ n) ≤ ArchimedeanClass.mk (sqrtOneAdd u hu hu0 - r) := by
  have h := IsHahnSum.mk_sub_le (isHahnSum_sqrtOneAdd hu hu0)
    (isHahnSum_sqrtSeries_of_sq_eq hu hr hsq) n
  refine le_trans (le_of_eq ?_) h
  rw [mk_sqrtSeries, ArchimedeanClass.mk_pow]

/-- **Approximate square roots agree below every scale**: any two positive surreals whose
squares both differ from `1 + u` by less than every power of `u` differ from *each other*
by less than every power of `u`. The domination-level square root of `1 + u` is unique. -/
theorem mk_pow_le_mk_sub_of_sq_approx {u y z : Surreal} (hu : Infinitesimal u)
    (hy : 0 < y) (hz : 0 < z)
    (hy2 : ∀ n : ℕ, ArchimedeanClass.mk (u ^ n) ≤ ArchimedeanClass.mk (y ^ 2 - (1 + u)))
    (hz2 : ∀ n : ℕ, ArchimedeanClass.mk (u ^ n) ≤ ArchimedeanClass.mk (z ^ 2 - (1 + u)))
    (n : ℕ) :
    ArchimedeanClass.mk (u ^ n) ≤ ArchimedeanClass.mk (y - z) := by
  -- both square-defects are infinitesimal, so both roots have standard part 1
  have hIy : Infinitesimal (y ^ 2 - (1 + u)) := by
    have h := hy2 1
    rw [pow_one] at h
    exact lt_of_lt_of_le hu h
  have hIz : Infinitesimal (z ^ 2 - (1 + u)) := by
    have h := hz2 1
    rw [pow_one] at h
    exact lt_of_lt_of_le hu h
  obtain ⟨hfy, hsty⟩ := isFinite_and_stdPart_eq_one_of_sq hu hy hIy
  obtain ⟨hfz, hstz⟩ := isFinite_and_stdPart_eq_one_of_sq hu hz hIz
  -- so `y + z` has standard part 2, hence class 0
  have hmkadd : ArchimedeanClass.mk (y + z) = 0 :=
    mk_eq_zero_of_stdPart_ne_zero (by
      rw [ArchimedeanClass.stdPart_add hfy hfz, hsty, hstz]
      norm_num)
  -- and `(y − z)(y + z)` is the difference of the two defects
  have hdiff : (y - z) * (y + z) = (y ^ 2 - (1 + u)) - (z ^ 2 - (1 + u)) := by ring
  have hmk : ArchimedeanClass.mk (y - z) =
      ArchimedeanClass.mk ((y ^ 2 - (1 + u)) - (z ^ 2 - (1 + u))) := by
    rw [← hdiff, ArchimedeanClass.mk_mul, hmkadd, add_zero]
  rw [hmk, sub_eq_add_neg]
  refine le_mk_add (hy2 n) ?_
  rw [ArchimedeanClass.mk_neg]
  exact hz2 n

/-- Any approximate square root of `1 + u` (positive, square hitting `1 + u` below every
scale) agrees with the canonical `sqrtOneAdd u` below every scale. -/
theorem mk_pow_le_mk_sqrtOneAdd_sub_of_sq_approx {u z : Surreal} (hu : Infinitesimal u)
    (hu0 : u ≠ 0) (hz : 0 < z)
    (hz2 : ∀ n : ℕ, ArchimedeanClass.mk (u ^ n) ≤ ArchimedeanClass.mk (z ^ 2 - (1 + u)))
    (n : ℕ) :
    ArchimedeanClass.mk (u ^ n) ≤ ArchimedeanClass.mk (sqrtOneAdd u hu hu0 - z) :=
  mk_pow_le_mk_sub_of_sq_approx hu (sqrtOneAdd_pos hu hu0) hz
    (mk_pow_le_mk_sq_sqrtOneAdd_sub hu hu0) hz2 n

/-! ### The capstone: square roots of arbitrary positive surreals, modulo domination

Combining all three layers: any positive `x` factors as `leadingTerm x · (1 + u)` with `u`
infinitesimal; Tier 1 takes an exact root of the leading term, and `sqrtOneAdd` handles
the infinitesimal correction. The result squares to `x` up to an error dominated below
`mk x` by every power of the relative remainder. -/

/-- **Every positive surreal has a square root modulo sub-all-scales error**: there is a
positive `z` with `mk (z² − x)` at least `mk x + n • mk (x / leadingTerm x − 1)` for every
`n` — infinitely far below the scale of `x` itself. When `x` equals its own leading term
the root is exact. -/
theorem exists_sq_sub_dominated {x : Surreal} (hx : 0 < x) :
    ∃ z, 0 < z ∧ ∀ n : ℕ,
      ArchimedeanClass.mk x + n • ArchimedeanClass.mk (x / leadingTerm x - 1) ≤
        ArchimedeanClass.mk (z ^ 2 - x) := by
  have hne : leadingTerm x ≠ 0 := (leadingTerm_pos_iff.2 hx).ne'
  set u := x / leadingTerm x - 1 with hu_def
  have hdecomp : x - leadingTerm x = u * leadingTerm x := by
    rw [hu_def]
    field_simp
  rcases eq_or_ne u 0 with h0 | h0
  · -- `x` is its own leading term: the Tier-1 root is exact
    have hx0 : x - leadingTerm x = 0 := by rw [hdecomp, h0, zero_mul]
    have hxlt : x = leadingTerm x := sub_eq_zero.1 hx0
    obtain ⟨z, hz, hz2⟩ := exists_sq_eq_leadingTerm hx
    refine ⟨z, hz, fun n ↦ ?_⟩
    rw [hz2, ← hxlt, sub_self,
      show ArchimedeanClass.mk (0 : Surreal) = ⊤ from ArchimedeanClass.mk_eq_top_iff.2 rfl]
    exact le_top
  · -- generic case: `u` is a nonzero infinitesimal
    have hu : Infinitesimal u := by
      by_contra hcon
      rw [infinitesimal_def, not_lt] at hcon
      have hle : ArchimedeanClass.mk u + ArchimedeanClass.mk (leadingTerm x) ≤
          0 + ArchimedeanClass.mk (leadingTerm x) := add_le_add_left hcon _
      rw [zero_add, ← ArchimedeanClass.mk_mul, ← hdecomp, mk_leadingTerm] at hle
      exact absurd ((mk_lt_mk_sub_leadingTerm hx.ne').trans_le hle) (lt_irrefl _)
    obtain ⟨z₀, hz₀, hz₀2⟩ := exists_sq_eq_leadingTerm hx
    refine ⟨z₀ * sqrtOneAdd u hu h0, mul_pos hz₀ (sqrtOneAdd_pos hu h0), fun n ↦ ?_⟩
    have hx' : leadingTerm x * (1 + u) = x := by
      rw [hu_def]
      field_simp
      ring
    have hkey : (z₀ * sqrtOneAdd u hu h0) ^ 2 - x =
        leadingTerm x * (sqrtOneAdd u hu h0 ^ 2 - (1 + u)) := by
      rw [mul_pow, hz₀2, mul_sub, hx']
    rw [hkey, ArchimedeanClass.mk_mul, mk_leadingTerm]
    refine add_le_add_right ?_ _
    exact le_trans (le_of_eq (ArchimedeanClass.mk_pow n u).symm)
      (mk_pow_le_mk_sq_sqrtOneAdd_sub hu h0 n)

end Surreal
