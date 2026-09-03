/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.Identification
import Infinity.IntegralS

/-!
# The genetic experiment: a Conway-style cut integral, tested

The genetic (cut-recursive) approach to surreal integration — Conway and Norton's
program from the 1970s — defines `∫ₐᵇ f` as the simplest surreal lying between families
of lower and upper approximating sums. This file implements the most transparent member
of that family for the integrand `f = id`: the **Darboux cut integral**, whose left
options are all lower Darboux sums and whose right options are all upper Darboux sums
over *finite* surreal partitions, and whose value is the birthday-simplest surreal
between them (`Cut.simplestBtwn` — the same simplicity principle that powers every
genetic definition). Two theorems, one for each horn of the experiment:

* **Agreement on finite intervals** (`darbouxIntegralId_zero_two`):
  `∫₀² x dx = 2` — the Darboux-genetic value *equals* the FTC integral
  (`darbouxIntegralId_eq_integralS`). The proof is a genuine simplicity argument, not an
  approximation argument: uniform partitions pin every fit to the halo `2 + infinitesimal`,
  and the identification machinery (`Infinity.Identification`) shows the dyadic center of
  a halo is its unique simplest point. The Riemann collapse theorem
  (`Infinity.Riemann`) showed ε–δ approximation is vacuous on **No**; this shows what
  replaces it: *the mesh cannot reach zero, but simplicity finishes the job on finite
  intervals.*

* **Indeterminacy over infinite intervals** (`fits_mid_add_wpow_darboux`,
  `darboux_indeterminate`): over `[0, ω]`, both `ω²/2` *and* `ω²/2 + ω` fit strictly
  between all lower and all upper Darboux sums. Any finite partition of `[0, ω]` has a
  piece of length `≥ ω/n`, so every upper sum overshoots the midpoint value by more than
  `ω` — the cut is loose at scale `ω`, and *analysis alone cannot determine the genetic
  integral over an infinite interval*: the value is whatever the simplicity principle
  selects from an `ω`-wide interval of candidates. This is the cut-integral face of the
  same phenomenon isolated by `Infinity.BirthdayHahn` for canonical sums (which value in
  a halo is simplest?) — the two open programs bottleneck on the same question. It is
  also, in miniature, the geometry behind Norton's famous wrong value for
  `∫₀^ω exp`: over infinite intervals a genetic integral is decided by simplicity, not
  by approximation, and nothing forces simplicity to respect the calculus.

The historical genetic definitions (Conway ONAG ch. 16; Norton's refinement; see also
Costin–Ehrlich, arXiv:2208.14331, §1 for the modern account of why they fail) use richer
option families, but share this structure: approximating sums + simplest-fit. The
agreement result here is, to our knowledge, the first machine-checked evaluation of a
genetic-style surreal integral; the indeterminacy result is the first machine-checked
localization of where the genetic program's difficulty lives.
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

/-! ### Partitions and Darboux sums for the identity integrand -/

/-- `x 0, …, x n` is a monotone partition of `[a, b]`. -/
def IsPartitionOn (x : ℕ → Surreal) (n : ℕ) (a b : Surreal) : Prop :=
  x 0 = a ∧ x n = b ∧ ∀ i < n, x i ≤ x (i + 1)

/-- The lower Darboux sum of the identity function: left tags. -/
def lowerSumId (x : ℕ → Surreal) (n : ℕ) : Surreal :=
  ∑ i ∈ Finset.range n, x i * (x (i + 1) - x i)

/-- The upper Darboux sum of the identity function: right tags. -/
def upperSumId (x : ℕ → Surreal) (n : ℕ) : Surreal :=
  ∑ i ∈ Finset.range n, x (i + 1) * (x (i + 1) - x i)

/-- The lower sum falls short of the midpoint value `(xₙ² − x₀²)/2` by exactly half the
sum of squared mesh lengths. -/
theorem mid_sub_lowerSumId (x : ℕ → Surreal) (n : ℕ) :
    (x n ^ 2 - x 0 ^ 2) / 2 - lowerSumId x n =
      ∑ i ∈ Finset.range n, (x (i + 1) - x i) ^ 2 / 2 := by
  have ht : x n ^ 2 - x 0 ^ 2 = ∑ i ∈ Finset.range n, (x (i + 1) ^ 2 - x i ^ 2) :=
    (Finset.sum_range_sub (fun i ↦ x i ^ 2) n).symm
  rw [ht, lowerSumId, div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- The upper sum overshoots the midpoint value by exactly half the sum of squared mesh
lengths. -/
theorem upperSumId_sub_mid (x : ℕ → Surreal) (n : ℕ) :
    upperSumId x n - (x n ^ 2 - x 0 ^ 2) / 2 =
      ∑ i ∈ Finset.range n, (x (i + 1) - x i) ^ 2 / 2 := by
  have ht : x n ^ 2 - x 0 ^ 2 = ∑ i ∈ Finset.range n, (x (i + 1) ^ 2 - x i ^ 2) :=
    (Finset.sum_range_sub (fun i ↦ x i ^ 2) n).symm
  rw [ht, upperSumId, div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- On a nondegenerate interval, the squared-mesh defect is strictly positive. -/
theorem sum_sq_half_pos {x : ℕ → Surreal} {n : ℕ}
    (hmono : ∀ i < n, x i ≤ x (i + 1)) (hlt : x 0 < x n) :
    0 < ∑ i ∈ Finset.range n, (x (i + 1) - x i) ^ 2 / 2 := by
  have hne : ∃ i ∈ Finset.range n, x i < x (i + 1) := by
    by_contra h
    push Not at h
    have hsum : x n - x 0 = ∑ i ∈ Finset.range n, (x (i + 1) - x i) :=
      (Finset.sum_range_sub x n).symm
    have hz : ∑ i ∈ Finset.range n, (x (i + 1) - x i) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by
        have h1 := h i hi
        have h2 := hmono i (Finset.mem_range.1 hi)
        linarith
    rw [hz] at hsum
    linarith
  obtain ⟨i0, hi0, hlt0⟩ := hne
  refine Finset.sum_pos' (fun i _ ↦ by positivity) ⟨i0, hi0, ?_⟩
  have h : 0 < x (i0 + 1) - x i0 := sub_pos.2 hlt0
  positivity

/-- Every lower sum lies strictly below the midpoint value. -/
theorem lowerSumId_lt_mid {x : ℕ → Surreal} {n : ℕ} {a b : Surreal}
    (hp : IsPartitionOn x n a b) (hab : a < b) :
    lowerSumId x n < (b ^ 2 - a ^ 2) / 2 := by
  obtain ⟨h0, hn, hmono⟩ := hp
  have h := mid_sub_lowerSumId x n
  have hpos := sum_sq_half_pos hmono (by rw [h0, hn]; exact hab)
  rw [← h0, ← hn]
  linarith

/-- Every upper sum lies strictly above the midpoint value. -/
theorem mid_lt_upperSumId {x : ℕ → Surreal} {n : ℕ} {a b : Surreal}
    (hp : IsPartitionOn x n a b) (hab : a < b) :
    (b ^ 2 - a ^ 2) / 2 < upperSumId x n := by
  obtain ⟨h0, hn, hmono⟩ := hp
  have h := upperSumId_sub_mid x n
  have hpos := sum_sq_half_pos hmono (by rw [h0, hn]; exact hab)
  rw [← h0, ← hn]
  linarith

/-! ### The Darboux cut and the genetic integral -/

/-- The cut just above all lower Darboux sums of the identity on `[a, b]`. -/
def darbouxLoId (a b : Surreal) : Cut :=
  ⨆ p : {q : (ℕ → Surreal) × ℕ // IsPartitionOn q.1 q.2 a b},
    Cut.rightSurreal (lowerSumId p.1.1 p.1.2)

/-- The cut just below all upper Darboux sums of the identity on `[a, b]`. -/
def darbouxHiId (a b : Surreal) : Cut :=
  ⨅ p : {q : (ℕ → Surreal) × ℕ // IsPartitionOn q.1 q.2 a b},
    Cut.leftSurreal (upperSumId p.1.1 p.1.2)

/-- A surreal fits between the Darboux cuts iff it lies strictly between every lower and
every upper Darboux sum. -/
theorem fits_darboux_iff {a b z : Surreal} :
    Cut.Fits z (darbouxLoId a b) (darbouxHiId a b) ↔
      ∀ x n, IsPartitionOn x n a b → lowerSumId x n < z ∧ z < upperSumId x n := by
  rw [Cut.Fits, Set.mem_inter_iff, ← Cut.notMem_left_iff]
  unfold darbouxLoId darbouxHiId
  simp only [Cut.left_iSup, Cut.left_iInf, Cut.left_rightSurreal, Cut.left_leftSurreal,
    Set.mem_iUnion, Set.mem_iInter, Set.mem_Iic, Set.mem_Iio, not_exists, not_le]
  constructor
  · rintro ⟨h1, h2⟩ x n hp
    exact ⟨h1 ⟨(x, n), hp⟩, h2 ⟨(x, n), hp⟩⟩
  · intro h
    exact ⟨fun p ↦ (h p.1.1 p.1.2 p.2).1, fun p ↦ (h p.1.1 p.1.2 p.2).2⟩

/-- The midpoint value `(b² − a²)/2` — the FTC value — always fits. -/
theorem fits_mid_darboux {a b : Surreal} (hab : a < b) :
    Cut.Fits ((b ^ 2 - a ^ 2) / 2) (darbouxLoId a b) (darbouxHiId a b) :=
  fits_darboux_iff.2 fun _ _ hp ↦ ⟨lowerSumId_lt_mid hp hab, mid_lt_upperSumId hp hab⟩

theorem darbouxLoId_lt_darbouxHiId {a b : Surreal} (hab : a < b) :
    darbouxLoId a b < darbouxHiId a b :=
  (fits_mid_darboux hab).lt

/-- **The Darboux-genetic integral of the identity**: the birthday-simplest surreal lying
strictly between all lower and all upper Darboux sums — the Conway-style simplest-value
principle applied to Darboux data. -/
def darbouxIntegralId (a b : Surreal) (hab : a < b) : Surreal :=
  Cut.simplestBtwn (darbouxLoId_lt_darbouxHiId hab)

/-! ### The uniform partitions of `[0, 2]` -/

/-- The uniform `n`-piece partition of `[0, 2]`. -/
def unifTwo (n : ℕ) : ℕ → Surreal := fun i ↦ 2 * ((min i n : ℕ) : Surreal) / n

theorem isPartitionOn_unifTwo {n : ℕ} (hn : n ≠ 0) : IsPartitionOn (unifTwo n) n 0 2 := by
  have hn' : ((n : ℕ) : Surreal) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨by simp [unifTwo], ?_, ?_⟩
  · show 2 * ((min n n : ℕ) : Surreal) / n = 2
    rw [min_self]
    field_simp
  · intro i hi
    show 2 * ((min i n : ℕ) : Surreal) / n ≤ 2 * ((min (i + 1) n : ℕ) : Surreal) / n
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (Nat.cast_nonneg n))
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact Nat.cast_le.2 (by omega)

theorem unifTwo_step {n : ℕ} {i : ℕ} (hi : i < n) :
    unifTwo n (i + 1) - unifTwo n i = 2 / n := by
  have hn' : ((n : ℕ) : Surreal) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold unifTwo
  rw [min_eq_left (by omega : i ≤ n), min_eq_left (by omega : i + 1 ≤ n)]
  push_cast
  field_simp
  ring

private theorem sum_range_cast_gauss (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : Surreal)) * 2 = (n : Surreal) ^ 2 - n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast
    ring

theorem lowerSumId_unifTwo {n : ℕ} (hn : n ≠ 0) :
    lowerSumId (unifTwo n) n = 2 - 2 / n := by
  have hn' : ((n : ℕ) : Surreal) ≠ 0 := Nat.cast_ne_zero.2 hn
  unfold lowerSumId
  have hstep : ∀ i ∈ Finset.range n, unifTwo n i * (unifTwo n (i + 1) - unifTwo n i) =
      (i : Surreal) * (4 / ((n : Surreal) * n)) := by
    intro i hi
    rw [unifTwo_step (Finset.mem_range.1 hi)]
    unfold unifTwo
    rw [min_eq_left (by have := Finset.mem_range.1 hi; omega : i ≤ n)]
    field_simp
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
  have hg := sum_range_cast_gauss n
  have hkey : (∑ i ∈ Finset.range n, (i : Surreal)) = ((n : Surreal) ^ 2 - n) / 2 := by
    rw [eq_div_iff (by norm_num : (2 : Surreal) ≠ 0), hg]
  rw [hkey]
  field_simp
  ring

theorem upperSumId_unifTwo {n : ℕ} (hn : n ≠ 0) :
    upperSumId (unifTwo n) n = 2 + 2 / n := by
  have hn' : ((n : ℕ) : Surreal) ≠ 0 := Nat.cast_ne_zero.2 hn
  unfold upperSumId
  have hstep : ∀ i ∈ Finset.range n, unifTwo n (i + 1) * (unifTwo n (i + 1) - unifTwo n i) =
      ((i : Surreal) + 1) * (4 / ((n : Surreal) * n)) := by
    intro i hi
    rw [unifTwo_step (Finset.mem_range.1 hi)]
    unfold unifTwo
    rw [min_eq_left (by have := Finset.mem_range.1 hi; omega : i + 1 ≤ n)]
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
  have hsum : (∑ i ∈ Finset.range n, ((i : Surreal) + 1)) =
      ((n : Surreal) ^ 2 - n) / 2 + n := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    congr 1
    rw [eq_div_iff (by norm_num : (2 : Surreal) ≠ 0), sum_range_cast_gauss n]
  rw [hsum]
  field_simp
  ring

/-! ### Agreement on a finite interval: `∫₀² x dx = 2` -/

/-- Every fit of the Darboux cut on `[0, 2]` is infinitesimally close to `2`: the uniform
partitions squeeze it. -/
theorem infinitesimal_sub_two_of_fits {z : Surreal}
    (hz : Cut.Fits z (darbouxLoId 0 2) (darbouxHiId 0 2)) : Infinitesimal (z - 2) := by
  rw [fits_darboux_iff] at hz
  rw [infinitesimal_iff]
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hn : (4 * m : ℕ) ≠ 0 := by omega
    obtain ⟨hlow, hup⟩ := hz (unifTwo (4 * m)) (4 * m) (isPartitionOn_unifTwo hn)
    rw [lowerSumId_unifTwo hn] at hlow
    rw [upperSumId_unifTwo hn] at hup
    have habs : |z - 2| < 2 / ((4 * m : ℕ) : Surreal) :=
      abs_lt.2 ⟨by linarith, by linarith⟩
    have hm' : (0 : Surreal) < m := by exact_mod_cast hm
    rw [nsmul_eq_mul]
    calc (m : Surreal) * |z - 2| < m * (2 / ((4 * m : ℕ) : Surreal)) :=
          mul_lt_mul_of_pos_left habs hm'
      _ = 1 / 2 := by
          push_cast
          field_simp
          ring
      _ < 1 := by norm_num

private theorem birthday_two_lt :
    (2 : Surreal).birthday < NatOrdinal.of Ordinal.omega0 := by
  have h : (2 : Surreal) = ((2 : ℕ) : Surreal) := by norm_num
  rw [h, birthday_natCast, ← NatOrdinal.of_natCast, NatOrdinal.of_lt_iff]
  exact_mod_cast Ordinal.natCast_lt_omega0 2

/-- **The genetic experiment, agreement horn**: the Darboux-genetic integral of the
identity over `[0, 2]` is exactly `2` — the FTC value. The proof is pure simplicity
theory: every fit is `2 + infinitesimal`, `2` itself fits, and a dyadic is the unique
simplest point of its halo. -/
theorem darbouxIntegralId_zero_two : darbouxIntegralId 0 2 (by norm_num) = 2 := by
  have h2 : ((2 : Surreal) ^ 2 - 0 ^ 2) / 2 = 2 := by norm_num
  have hfits : Cut.Fits 2 (darbouxLoId 0 2) (darbouxHiId 0 2) := by
    have h := fits_mid_darboux (a := 0) (b := 2) (by norm_num)
    rwa [h2] at h
  rw [darbouxIntegralId, Cut.simplestBtwn_eq_iff]
  refine ⟨hfits, fun w hw ↦ ?_⟩
  rcases eq_or_ne w 2 with rfl | hne
  · exact le_rfl
  · exact birthday_two_lt.le.trans (omega0_le_birthday_of_infinitesimal_sub birthday_two_lt
      (infinitesimal_sub_two_of_fits hw) hne)

/-- The Darboux-genetic value agrees with the FTC integral on `[0, 2]`. -/
theorem darbouxIntegralId_eq_integralS :
    darbouxIntegralId 0 2 (by norm_num) = integralS Polynomial.X 0 2 := by
  rw [darbouxIntegralId_zero_two, integralS_X]
  norm_num

/-! ### Indeterminacy over an infinite interval -/

/-- Over `[0, ω]`, the value `ω²/2 + ω` — the FTC value *plus* `ω` — also fits strictly
between all lower and all upper Darboux sums: any finite partition has a piece of length
at least `ω/n`, so every upper sum overshoots `ω²/2` by more than `ω`. -/
theorem fits_mid_add_wpow_darboux :
    Cut.Fits ((ω^ (1 : Surreal)) ^ 2 / 2 + ω^ (1 : Surreal))
      (darbouxLoId 0 (ω^ (1 : Surreal))) (darbouxHiId 0 (ω^ (1 : Surreal))) := by
  have hω : (0 : Surreal) < ω^ (1 : Surreal) := wpow_pos _
  rw [fits_darboux_iff]
  intro x n hp
  have hmid : ((ω^ (1 : Surreal)) ^ 2 - (0 : Surreal) ^ 2) / 2 =
      (ω^ (1 : Surreal)) ^ 2 / 2 := by ring
  constructor
  · have h := lowerSumId_lt_mid hp hω
    rw [hmid] at h
    linarith
  · -- the upper sum exceeds `ω²/2 + ω`
    obtain ⟨h0, hn, hmono⟩ := hp
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hω.ne' (by rw [← hn, h0])
    have hncast : (0 : Surreal) < n := by
      have := Nat.pos_of_ne_zero hn0
      exact_mod_cast this
    -- some piece has length at least `ω/n`
    have hbig : ∃ i ∈ Finset.range n, ω^ (1 : Surreal) / n ≤ x (i + 1) - x i := by
      by_contra h
      push Not at h
      have hsum : ∑ i ∈ Finset.range n, (x (i + 1) - x i) = ω^ (1 : Surreal) := by
        rw [Finset.sum_range_sub, hn, h0, sub_zero]
      have hlt : ∑ i ∈ Finset.range n, (x (i + 1) - x i) <
          ∑ _i ∈ Finset.range n, ω^ (1 : Surreal) / n :=
        Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 hn0) fun i hi ↦ h i hi
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_div_cancel₀ _ hncast.ne'] at hlt
      rw [hsum] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨i0, hi0mem, hi0⟩ := hbig
    -- hence the squared-mesh defect exceeds `ω`
    have hstep : (ω^ (1 : Surreal) / n) ^ 2 / 2 ≤ (x (i0 + 1) - x i0) ^ 2 / 2 := by
      have h1 : (0 : Surreal) ≤ ω^ (1 : Surreal) / n := div_nonneg hω.le (Nat.cast_nonneg n)
      have h2 : (ω^ (1 : Surreal) / n) ^ 2 ≤ (x (i0 + 1) - x i0) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_le_mul hi0 hi0 h1 (h1.trans hi0)
      linarith
    have hsingle := Finset.single_le_sum (f := fun i ↦ (x (i + 1) - x i) ^ 2 / 2)
      (fun i _ ↦ by positivity) hi0mem
    have hω2 : ω^ (1 : Surreal) < (ω^ (1 : Surreal) / n) ^ 2 / 2 := by
      have hcast := natCast_lt_wpow_one (2 * n ^ 2)
      have h2n : ((2 * n ^ 2 : ℕ) : Surreal) = 2 * (n : Surreal) ^ 2 := by push_cast; ring
      rw [h2n] at hcast
      rw [div_pow, div_div, lt_div_iff₀ (by positivity)]
      calc ω^ (1 : Surreal) * ((n : Surreal) ^ 2 * 2) =
            (2 * (n : Surreal) ^ 2) * ω^ (1 : Surreal) := by ring
        _ < ω^ (1 : Surreal) * ω^ (1 : Surreal) :=
            mul_lt_mul_of_pos_right hcast hω
        _ = (ω^ (1 : Surreal)) ^ 2 := by ring
    have hdefect := upperSumId_sub_mid x n
    rw [h0, hn, hmid] at hdefect
    linarith

/-- **The genetic experiment, indeterminacy horn**: over `[0, ω]` the Darboux cut admits
two fits a full `ω` apart — the FTC value `ω²/2` and `ω²/2 + ω`. Approximation leaves
the genetic integral over an infinite interval undetermined at scale `ω`; only the
simplicity principle decides it, and which value is simplest in that interval is
precisely the halo-simplicity question left open by `Infinity.BirthdayHahn`. -/
theorem darboux_indeterminate :
    Cut.Fits ((ω^ (1 : Surreal)) ^ 2 / 2)
        (darbouxLoId 0 (ω^ (1 : Surreal))) (darbouxHiId 0 (ω^ (1 : Surreal))) ∧
      Cut.Fits ((ω^ (1 : Surreal)) ^ 2 / 2 + ω^ (1 : Surreal))
        (darbouxLoId 0 (ω^ (1 : Surreal))) (darbouxHiId 0 (ω^ (1 : Surreal))) := by
  constructor
  · have h := fits_mid_darboux (a := 0) (b := ω^ (1 : Surreal)) (wpow_pos _)
    have hmid : ((ω^ (1 : Surreal)) ^ 2 - (0 : Surreal) ^ 2) / 2 =
        (ω^ (1 : Surreal)) ^ 2 / 2 := by ring
    rwa [hmid] at h
  · exact fits_mid_add_wpow_darboux

end Surreal

end
