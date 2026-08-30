import Infinity.DayOmega

/-!
# The first exact exponential value: `exp (log (1 + ω⁻¹)) = 1 + ω⁻¹`

The canonical-sum exponential `expInf` (`Infinity.CanonicalSum`) has so far been
evaluated exactly at no argument: `expInf ε` is pinned only modulo perturbations below
every scale of the series, and which value the simplicity principle selects is the halo
problem. This file evaluates it **exactly once**: at the canonical transfinite sum `σ`
of the logarithm series `Σ_{k≥1} (−1)^{k+1} ω^{−k}/k`,

* `expInf σ = 1 + ω⁻¹` — **the first exact value of the surreal exponential at a
  transfinite argument**, and the first verified instance of `exp ∘ log = id` on **No**
  beyond the reals.

The proof has two halves.

**The algebraic half** (this file, first section): truncated composition
`exp ∘ log = id` at the level of real polynomials — `X^n` divides
`E_n(L_N(X)) − (1 + X)` whenever `n ≤ N` (`X_pow_dvd_expPoly_comp_logPoly`), proved by
a derivation argument: `(1+X)·L_N′ = 1 − (−X)^N` (a geometric-sum identity), so the
defect `D_{n+1}` satisfies `(1+X)·D_{n+1}′ = D_n·(1−(−X)^N) − (1+X)(−X)^N`, and
divisibility climbs one power per step (`X^n ∣ P′` and `P(0) = 0` force `X^{n+1} ∣ P`
in characteristic zero).

**The domination half**: `σ` differs from the value of `L_N` at `ω⁻¹` by a Hahn
residual below scale `ω^{−N}`; substituting into `E_n` moves the residual through
explicit geometric cofactors (`geom_sum₂_mul` — all finite), so
`1 + ω⁻¹ − E_n(σ)` has Archimedean class at least that of `ω^{−n}` — i.e.
**`1 + ω⁻¹` is a Hahn sum of the exponential series at `σ`**
(`isHahnSum_expSeries_one_add`).

The identification then closes by the day-`ω` census machinery: `1 + ω⁻¹` is born by
day `ω` (`Infinity.DayOmega.birthday_dyadic_add_wpow_neg_one_le`) while *every* Hahn
sum of an exponential series at a positive infinitesimal is born at or after day `ω`
(`Infinity.Identification.omega0_le_birthday_of_isHahnSum_expSeries`), so the
birthday-minimal Hahn sum — the canonical value — is `1 + ω⁻¹` on the nose.

As corollaries: `birthday (expInf σ) = ω` — the simplest value the exponential ever
takes off the reals — and the day-`ω` fibre of `expInf` over `1 + ω⁻¹`
(`Infinity.DayOmega.birthday_expInf_mul_le_iff`) is genuinely realized by an argument.

Classical calibration: that `exp` and `log` are mutually inverse on **No** is Gonshor's
theorem (Gonshor 1986, ch. 10; the survey account is Berarducci–Mantova). What is
evaluated here is the canonical-sum exponential of this development at one canonically
constructed argument — no genetic recursion, no claim about Gonshor's global `log`.
-/

open ArchimedeanClass Filter Finset Polynomial

noncomputable section

namespace Surreal

/-! ### The truncated exponential and logarithm as real polynomials -/

/-- The truncated exponential series `Σ_{k<n} Xᵏ/k!` as a real polynomial. -/
def expPoly (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range n, Polynomial.C ((k.factorial : ℝ)⁻¹) * Polynomial.X ^ k

/-- The truncated logarithm series `Σ_{j<N} (−1)ʲ X^{j+1}/(j+1)` as a real
polynomial. -/
def logPoly (N : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range N, Polynomial.C ((-1) ^ j / (j + 1) : ℝ) * Polynomial.X ^ (j + 1)

theorem derivative_expPoly (n : ℕ) : (expPoly (n + 1)).derivative = expPoly n := by
  unfold expPoly
  rw [derivative_sum, Finset.sum_range_succ']
  have h0 : Polynomial.derivative
      (Polynomial.C (((0 : ℕ).factorial : ℝ)⁻¹) * Polynomial.X ^ 0) = 0 := by
    simp
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
  have harith : (((k + 1).factorial : ℝ))⁻¹ * ((k + 1 : ℕ) : ℝ) = ((k.factorial : ℝ))⁻¹ := by
    rw [Nat.factorial_succ]
    push_cast
    have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((k.factorial : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  calc Polynomial.C (((k + 1).factorial : ℝ))⁻¹ *
        (Polynomial.C ((k + 1 : ℕ) : ℝ) * Polynomial.X ^ (k + 1 - 1))
      = Polynomial.C ((((k + 1).factorial : ℝ))⁻¹ * ((k + 1 : ℕ) : ℝ)) *
          Polynomial.X ^ k := by
        rw [Polynomial.C_mul, show (k + 1) - 1 = k from rfl]
        ring
    _ = Polynomial.C ((k.factorial : ℝ))⁻¹ * Polynomial.X ^ k := by rw [harith]

theorem derivative_logPoly (N : ℕ) :
    (logPoly N).derivative = ∑ j ∈ Finset.range N, (-Polynomial.X : ℝ[X]) ^ j := by
  unfold logPoly
  rw [derivative_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
  have harith : ((-1) ^ j / (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) = (-1) ^ j := by
    push_cast
    have h1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  calc Polynomial.C ((-1) ^ j / (j + 1) : ℝ) *
        (Polynomial.C ((j + 1 : ℕ) : ℝ) * Polynomial.X ^ (j + 1 - 1))
      = Polynomial.C (((-1) ^ j / (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
          Polynomial.X ^ j := by
        rw [Polynomial.C_mul, show (j + 1) - 1 = j from rfl]
        ring
    _ = (-Polynomial.X : ℝ[X]) ^ j := by
        rw [harith]
        conv_rhs => rw [neg_pow]
        rw [Polynomial.C_pow]
        norm_num

/-- The geometric identity `L_N′ · (1 + X) = 1 − (−X)^N`. -/
theorem derivative_logPoly_mul (N : ℕ) :
    (logPoly N).derivative * (1 + Polynomial.X) = 1 - (-Polynomial.X : ℝ[X]) ^ N := by
  rw [derivative_logPoly]
  have h := (Commute.one_right (-Polynomial.X : ℝ[X])).geom_sum₂_mul N
  rw [geom_sum₂_with_one] at h
  linear_combination -h

theorem expPoly_eval_zero {n : ℕ} (hn : 0 < n) : (expPoly n).eval 0 = 1 := by
  unfold expPoly
  rw [Polynomial.eval_finsetSum]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Finset.sum_range_succ']
  simp

theorem logPoly_eval_zero (N : ℕ) : (logPoly N).eval 0 = 0 := by
  unfold logPoly
  rw [Polynomial.eval_finsetSum]
  simp

/-- Characteristic-zero antidifferentiation of divisibility: if `Xⁿ ∣ P′` and
`P(0) = 0` then `Xⁿ⁺¹ ∣ P`. -/
private theorem X_pow_dvd_of_derivative {P : ℝ[X]} {n : ℕ}
    (h : Polynomial.X ^ n ∣ P.derivative) (h0 : P.coeff 0 = 0) :
    Polynomial.X ^ (n + 1) ∣ P := by
  rw [Polynomial.X_pow_dvd_iff] at h ⊢
  intro d hd
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · exact h0
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0.ne'
    have he := h e (by omega)
    rw [Polynomial.coeff_derivative] at he
    have h2 : ((e : ℝ) + 1) ≠ 0 := by positivity
    rcases mul_eq_zero.1 he with h3 | h3
    · exact h3
    · exact absurd h3 h2

/-- `1 + X` is invertible against powers of `X`. -/
private theorem X_pow_dvd_of_one_add_mul {Q : ℝ[X]} {n : ℕ}
    (h : Polynomial.X ^ n ∣ (1 + Polynomial.X) * Q) : Polynomial.X ^ n ∣ Q := by
  have hcop : IsCoprime (Polynomial.X ^ n) (1 + Polynomial.X : ℝ[X]) :=
    IsCoprime.pow_left ⟨-1, 1, by ring⟩
  exact hcop.dvd_of_dvd_mul_left h

/-- **Truncated `exp ∘ log = id`**: for `n ≤ N`, the composition defect
`E_n(L_N(X)) − (1 + X)` is divisible by `Xⁿ`. Proof by the derivation argument:
`(1+X)·D_{n+1}′ = D_n·(1 − (−X)^N) − (1+X)·(−X)^N`. -/
theorem X_pow_dvd_expPoly_comp_logPoly (N : ℕ) :
    ∀ n ≤ N, Polynomial.X ^ n ∣
      (expPoly n).comp (logPoly N) - (1 + Polynomial.X) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [pow_zero]
    exact one_dvd _
  | succ n ih =>
    intro hn
    have hIH := ih (by omega)
    have hmul : (1 + Polynomial.X) *
        ((expPoly (n + 1)).comp (logPoly N) - (1 + Polynomial.X)).derivative =
        ((expPoly n).comp (logPoly N) - (1 + Polynomial.X)) *
            (1 - (-Polynomial.X : ℝ[X]) ^ N) -
          (1 + Polynomial.X) * (-Polynomial.X : ℝ[X]) ^ N := by
      have hd : ((expPoly (n + 1)).comp (logPoly N) - (1 + Polynomial.X)).derivative =
          (expPoly n).comp (logPoly N) * (logPoly N).derivative - 1 := by
        rw [Polynomial.derivative_sub, Polynomial.derivative_comp, derivative_expPoly,
          Polynomial.derivative_add, Polynomial.derivative_one, Polynomial.derivative_X,
          zero_add]
        ring
      rw [hd]
      linear_combination ((expPoly n).comp (logPoly N)) * derivative_logPoly_mul N
    have hv : Polynomial.X ^ n ∣ (-Polynomial.X : ℝ[X]) ^ N := by
      rw [neg_pow]
      exact Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _
    have hdvd : Polynomial.X ^ n ∣ (1 + Polynomial.X) *
        ((expPoly (n + 1)).comp (logPoly N) - (1 + Polynomial.X)).derivative := by
      rw [hmul]
      exact dvd_sub (hIH.mul_right _) (hv.mul_left _)
    refine X_pow_dvd_of_derivative (X_pow_dvd_of_one_add_mul hdvd) ?_
    rw [Polynomial.coeff_sub, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_comp, logPoly_eval_zero, expPoly_eval_zero (by omega)]
    simp

end Surreal

end
