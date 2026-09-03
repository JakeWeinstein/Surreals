/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.DayOmega
import Infinity.FiniteDeriv

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

/-! ### The logarithm series and its canonical sum -/

/-- The Maclaurin series of `log (1 + x)` at `x = ω⁻¹`:
`t k = (−1)ᵏ ω^{−(k+1)}/(k+1)`. -/
def logSeries (k : ℕ) : Surreal :=
  (((-1) ^ k / (k + 1) : ℝ) : Surreal) * ((ω^ (1 : Surreal))⁻¹) ^ (k + 1)

private theorem logCoeff_ne_zero (k : ℕ) : ((-1) ^ k / (k + 1) : ℝ) ≠ 0 := by
  refine div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)

private theorem inv_wpow_infinitesimal : Infinitesimal ((ω^ (1 : Surreal))⁻¹) :=
  infinitesimal_inv_wpow one_pos

private theorem inv_wpow_pos : (0 : Surreal) < (ω^ (1 : Surreal))⁻¹ :=
  inv_pos.2 (wpow_pos _)

theorem logSeries_strict_dominating (k : ℕ) :
    ArchimedeanClass.mk (logSeries k) < ArchimedeanClass.mk (logSeries (k + 1)) := by
  unfold logSeries
  rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, mk_realCast (logCoeff_ne_zero k),
    mk_realCast (logCoeff_ne_zero (k + 1)), zero_add, zero_add]
  exact mk_pow_lt_mk_pow_succ inv_wpow_infinitesimal inv_wpow_pos (k + 1)

/-- **The canonical logarithm of `1 + ω⁻¹`**: the canonical (birthday-simplest)
transfinite sum of the Maclaurin series of `log (1 + x)` at `ω⁻¹`. -/
def logOmega : Surreal :=
  hahnSum logSeries_strict_dominating

theorem isHahnSum_logSeries_logOmega : IsHahnSum logSeries logOmega :=
  isHahnSum_hahnSum _

/-- The partial sums of the logarithm series are the truncated-logarithm values. -/
theorem partialSum_logSeries_eq (N : ℕ) :
    partialSum logSeries N = (logPoly N).eval₂ realHom ((ω^ (1 : Surreal))⁻¹) := by
  rw [partialSum, logPoly, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  rfl

private theorem partialSum_logSeries_one :
    partialSum logSeries 1 = (ω^ (1 : Surreal))⁻¹ := by
  rw [partialSum, Finset.sum_range_one]
  unfold logSeries
  norm_num

private theorem mk_logSeries (n : ℕ) : ArchimedeanClass.mk (logSeries n) =
    ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ (n + 1)) := by
  unfold logSeries
  rw [ArchimedeanClass.mk_mul, mk_realCast (logCoeff_ne_zero n), zero_add]

/-- The canonical logarithm is `ω⁻¹` to leading order. -/
theorem mk_lt_mk_logOmega_sub_inv :
    ArchimedeanClass.mk ((ω^ (1 : Surreal))⁻¹) <
      ArchimedeanClass.mk (logOmega - (ω^ (1 : Surreal))⁻¹) := by
  have h := isHahnSum_logSeries_logOmega 1
  rw [partialSum_logSeries_one] at h
  calc ArchimedeanClass.mk ((ω^ (1 : Surreal))⁻¹)
      = ArchimedeanClass.mk (logSeries 0) := by
        rw [mk_logSeries, zero_add, pow_one]
    _ < ArchimedeanClass.mk (logSeries 1) := logSeries_strict_dominating 0
    _ ≤ _ := h

theorem mk_logOmega : ArchimedeanClass.mk logOmega =
    ArchimedeanClass.mk ((ω^ (1 : Surreal))⁻¹) := by
  have h : logOmega = (ω^ (1 : Surreal))⁻¹ + (logOmega - (ω^ (1 : Surreal))⁻¹) := by ring
  rw [h, ArchimedeanClass.mk_add_eq_mk_left mk_lt_mk_logOmega_sub_inv]

theorem logOmega_infinitesimal : Infinitesimal logOmega := by
  rw [infinitesimal_def, mk_logOmega]
  exact inv_wpow_infinitesimal

theorem logOmega_pos : 0 < logOmega := by
  have habs := abs_lt_abs_of_mk_lt mk_lt_mk_logOmega_sub_inv
  rw [abs_of_pos inv_wpow_pos] at habs
  have h := (abs_lt.1 habs).1
  linarith

theorem isFinite_logOmega : IsFinite logOmega :=
  logOmega_infinitesimal.isFinite

/-! ### The domination half: `1 + ω⁻¹` is a Hahn sum of the exponential series at
the canonical logarithm -/

private theorem mk_pow_congr {a b : Surreal}
    (h : ArchimedeanClass.mk a = ArchimedeanClass.mk b) (n : ℕ) :
    ArchimedeanClass.mk (a ^ n) = ArchimedeanClass.mk (b ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, ih, h]

/-- Sums of termwise-dominated surreals are dominated. -/
private theorem le_mk_sum' {c : ArchimedeanClass Surreal} {s : Finset ℕ} {f : ℕ → Surreal}
    (h : ∀ i ∈ s, c ≤ ArchimedeanClass.mk (f i)) :
    c ≤ ArchimedeanClass.mk (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, ArchimedeanClass.mk_zero]
    exact le_top
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact le_trans (le_min (h a (Finset.mem_cons_self ..))
      (ih fun i hi ↦ h i (Finset.mem_cons_of_mem hi))) (ArchimedeanClass.min_le_mk_add ..)

/-- The partial sums of the exponential series are the truncated-exponential values. -/
theorem partialSum_expSeries_eq_eval (x : Surreal) (n : ℕ) :
    partialSum (fun k ↦ x ^ k / ((k.factorial : ℕ) : Surreal)) n =
      (expPoly n).eval₂ realHom x := by
  rw [partialSum, expPoly, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, map_inv₀ realHom,
    realHom_apply, Real.toSurreal_natCast, div_eq_mul_inv, mul_comm]

/-- **`1 + ω⁻¹` satisfies the domination equations of the exponential series at the
canonical logarithm**: the residual at stage `n` combines the truncated-composition
defect (`X^n`-divisible, by the algebraic half) with the substitution error
`E_n(σ) − E_n(L_n(ω⁻¹))` (a multiple of the stage-`n` Hahn residual of `σ`, via the
geometric cofactors), both of class at least that of `ω^{−n}`. -/
theorem isHahnSum_expSeries_one_add :
    IsHahnSum (fun k ↦ logOmega ^ k / ((k.factorial : ℕ) : Surreal))
      (1 + (ω^ (1 : Surreal))⁻¹) := by
  intro n
  -- the polynomial factorization of the composition defect
  obtain ⟨P, hP⟩ := X_pow_dvd_expPoly_comp_logPoly n n le_rfl
  -- Term 1: `E_n(Lval) − (1 + ω⁻¹) = ω^{−n}·P(ω⁻¹)`
  have hterm1 : (expPoly n).eval₂ realHom (partialSum logSeries n) -
      (1 + (ω^ (1 : Surreal))⁻¹) =
      ((ω^ (1 : Surreal))⁻¹) ^ n * P.eval₂ realHom ((ω^ (1 : Surreal))⁻¹) := by
    have h := congrArg (Polynomial.eval₂ realHom ((ω^ (1 : Surreal))⁻¹)) hP
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_X,
      Polynomial.eval₂_comp, ← partialSum_logSeries_eq] at h
    exact h
  -- Term 2: `E_n(σ) − E_n(Lval)` is dominated by the stage-`n` Hahn residual
  have hLfin : IsFinite (partialSum logSeries n) := by
    rw [partialSum_logSeries_eq]
    exact isFinite_eval₂ _ inv_wpow_infinitesimal.isFinite
  have hterm2 : ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ n) ≤
      ArchimedeanClass.mk ((expPoly n).eval₂ realHom logOmega -
        (expPoly n).eval₂ realHom (partialSum logSeries n)) := by
    rw [← partialSum_expSeries_eq_eval, ← partialSum_expSeries_eq_eval,
      partialSum, partialSum, ← Finset.sum_sub_distrib]
    refine le_mk_sum' fun k _ ↦ ?_
    have hsplit : logOmega ^ k / ((k.factorial : ℕ) : Surreal) -
        (partialSum logSeries n) ^ k / ((k.factorial : ℕ) : Surreal) =
        (((k.factorial : ℕ) : Surreal))⁻¹ *
          ((∑ i ∈ Finset.range k,
            logOmega ^ i * (partialSum logSeries n) ^ (k - 1 - i)) *
            (logOmega - partialSum logSeries n)) := by
      rw [(Commute.all logOmega (partialSum logSeries n)).geom_sum₂_mul k]
      ring
    rw [hsplit, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul]
    have hinv0 : ArchimedeanClass.mk ((((k.factorial : ℕ) : Surreal))⁻¹) = 0 := by
      rw [ArchimedeanClass.mk_inv, mk_factorial, neg_zero]
    have hcof : (0 : ArchimedeanClass Surreal) ≤ ArchimedeanClass.mk
        (∑ i ∈ Finset.range k,
          logOmega ^ i * (partialSum logSeries n) ^ (k - 1 - i)) := by
      refine isFinite_sum fun i _ ↦ ?_
      exact (isFinite_logOmega.pow i).mul (hLfin.pow (k - 1 - i))
    have hres : ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ n) ≤
        ArchimedeanClass.mk (logOmega - partialSum logSeries n) := by
      refine le_trans ?_ (isHahnSum_logSeries_logOmega n)
      rw [mk_logSeries]
      exact (mk_pow_lt_mk_pow_succ inv_wpow_infinitesimal inv_wpow_pos n).le
    calc ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ n)
        = 0 + (0 + ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ n)) := by
          rw [zero_add, zero_add]
      _ ≤ ArchimedeanClass.mk ((((k.factorial : ℕ) : Surreal))⁻¹) +
          (ArchimedeanClass.mk (∑ i ∈ Finset.range k,
              logOmega ^ i * (partialSum logSeries n) ^ (k - 1 - i)) +
            ArchimedeanClass.mk (logOmega - partialSum logSeries n)) := by
          rw [hinv0]
          exact add_le_add le_rfl (add_le_add hcof hres)
  -- assemble the residual
  have hsplit : 1 + (ω^ (1 : Surreal))⁻¹ -
      partialSum (fun k ↦ logOmega ^ k / ((k.factorial : ℕ) : Surreal)) n =
      -((expPoly n).eval₂ realHom (partialSum logSeries n) - (1 + (ω^ (1 : Surreal))⁻¹)) +
      -((expPoly n).eval₂ realHom logOmega -
        (expPoly n).eval₂ realHom (partialSum logSeries n)) := by
    rw [partialSum_expSeries_eq_eval]
    ring
  have hmk1 : ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ n) ≤
      ArchimedeanClass.mk ((expPoly n).eval₂ realHom (partialSum logSeries n) -
        (1 + (ω^ (1 : Surreal))⁻¹)) := by
    rw [hterm1, ArchimedeanClass.mk_mul]
    have hPfin : (0 : ArchimedeanClass Surreal) ≤
        ArchimedeanClass.mk (P.eval₂ realHom ((ω^ (1 : Surreal))⁻¹)) :=
      isFinite_eval₂ _ inv_wpow_infinitesimal.isFinite
    calc ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ n)
        = ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ n) + 0 := (add_zero _).symm
      _ ≤ _ := add_le_add le_rfl hPfin
  have htarget : ArchimedeanClass.mk
      (logOmega ^ n / ((n.factorial : ℕ) : Surreal)) =
      ArchimedeanClass.mk (((ω^ (1 : Surreal))⁻¹) ^ n) := by
    rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero]
    exact mk_pow_congr mk_logOmega n
  show ArchimedeanClass.mk (logOmega ^ n / ((n.factorial : ℕ) : Surreal)) ≤ _
  rw [htarget, hsplit]
  refine le_trans (le_min ?_ ?_) (ArchimedeanClass.min_le_mk_add ..)
  · rwa [ArchimedeanClass.mk_neg]
  · rwa [ArchimedeanClass.mk_neg]

/-! ### The exact evaluation -/

/-- `1 + ω⁻¹` is born by day `ω` (transport of the census bound). -/
theorem birthday_one_add_inv_wpow_le :
    ((1 : Surreal) + (ω^ (1 : Surreal))⁻¹).birthday ≤ NatOrdinal.of Ordinal.omega0 := by
  have h := birthday_dyadic_add_wpow_neg_one_le 1
  have hone : ((1 : Dyadic) : Surreal) = 1 := by
    show (((1 : Dyadic) : ℚ) : Surreal) = 1
    norm_num
  have hwp : ω^ (-1 : Surreal) = (ω^ (1 : Surreal))⁻¹ := by
    rw [show (-1 : Surreal) = -(1 : Surreal) from rfl, wpow_neg]
  rwa [hone, hwp] at h

/-- **The first exact exponential value**: the canonical-sum exponential at the
canonical logarithm of `1 + ω⁻¹` is exactly `1 + ω⁻¹` — `exp (log (1 + ω⁻¹)) = 1 + ω⁻¹`
on **No**, machine-checked. The candidate is a Hahn sum by the two-half analysis; it is
born by day `ω` while every Hahn sum of the series is born at or after day `ω`; so it
is the birthday-minimal sum, i.e. the canonical value. -/
theorem expInf_logOmega_eq :
    expInf logOmega logOmega_infinitesimal logOmega_pos.ne' =
      1 + (ω^ (1 : Surreal))⁻¹ := by
  unfold expInf
  rw [hahnSum_eq_iff]
  refine ⟨isHahnSum_expSeries_one_add, fun w hw ↦ ?_⟩
  exact birthday_one_add_inv_wpow_le.trans
    (omega0_le_birthday_of_isHahnSum_expSeries logOmega_infinitesimal logOmega_pos hw)

/-- The exponential achieves the smallest transfinite birthday possible for it:
`birthday (expInf (logOmega)) = ω` exactly. -/
theorem birthday_expInf_logOmega :
    (expInf logOmega logOmega_infinitesimal logOmega_pos.ne').birthday =
      NatOrdinal.of Ordinal.omega0 := by
  refine le_antisymm ?_ (omega0_le_birthday_expInf logOmega_infinitesimal logOmega_pos)
  rw [expInf_logOmega_eq]
  exact birthday_one_add_inv_wpow_le

/-- The canonical logarithm is not `ω⁻¹` itself: the stage-2 domination equation
fails. -/
theorem logOmega_ne_inv : logOmega ≠ (ω^ (1 : Surreal))⁻¹ := by
  intro h
  have h2 := isHahnSum_logSeries_logOmega 2
  rw [h] at h2
  have hps : partialSum logSeries 2 = (ω^ (1 : Surreal))⁻¹ + logSeries 1 := by
    rw [partialSum, Finset.sum_range_succ, ← partialSum, partialSum_logSeries_one]
  rw [hps] at h2
  have hval : (ω^ (1 : Surreal))⁻¹ - ((ω^ (1 : Surreal))⁻¹ + logSeries 1) =
      -(logSeries 1) := by ring
  rw [hval, ArchimedeanClass.mk_neg] at h2
  exact absurd h2 (not_le.2 (logSeries_strict_dominating 1))

/-- **The exponential simplifies its argument**: the canonical logarithm of `1 + ω⁻¹`
is born at or after day `ω + 1` — strictly *later* than its own exponential value
(born on day `ω`, `birthday_expInf_logOmega`). By the census, a day-`ω` positive
infinitesimal could only be `ω⁻¹`, and `logOmega ≠ ω⁻¹`. Birthday order is not
preserved by `exp`. -/
theorem omega0_add_one_le_birthday_logOmega :
    NatOrdinal.of Ordinal.omega0 + 1 ≤ logOmega.birthday := by
  have h0 : ((0 : Dyadic) : Surreal) = 0 := by
    show (((0 : Dyadic) : ℚ) : Surreal) = 0
    norm_num
  have hω : NatOrdinal.of Ordinal.omega0 ≤ logOmega.birthday := by
    refine omega0_le_birthday_of_infinitesimal_sub (c := 0) ?_ ?_ logOmega_pos.ne'
    · rw [birthday_zero]
      exact NatOrdinal.of_pos.2 Ordinal.omega0_pos
    · rw [sub_zero]
      exact logOmega_infinitesimal
  refine Order.add_one_le_of_lt (hω.lt_of_ne ?_)
  intro heq
  have hinf : Infinitesimal (logOmega - ((0 : Dyadic) : Surreal)) := by
    rw [h0, sub_zero]
    exact logOmega_infinitesimal
  rcases day_omega_near_dyadic hinf heq.ge with h | h | h
  · rw [h0] at h
    exact logOmega_pos.ne' h
  · rw [h0, zero_add, show (-1 : Surreal) = -(1 : Surreal) from rfl, wpow_neg] at h
    exact logOmega_ne_inv h
  · have hp := logOmega_pos
    rw [h, h0, zero_sub] at hp
    have := wpow_pos (-1 : Surreal)
    linarith

end Surreal

end
