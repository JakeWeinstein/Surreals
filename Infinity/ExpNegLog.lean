import Infinity.Exp
import Infinity.ExpLog
import Infinity.AltGeometric

/-!
# The domination half of the inverse exponential value:
`(1+ω⁻¹)⁻¹` is a Hahn sum of the exponential series at `−log(1+ω⁻¹)`

`Infinity.ExpLog` evaluated `exp (log (1+ω⁻¹)) = 1+ω⁻¹`; the inverse value
`exp (−log (1+ω⁻¹)) = (1+ω⁻¹)⁻¹` needs the same two halves at the negated argument.
This file proves the **domination half**:

* `isHahnSum_expSeries_neg_logOmega` : **`(1+ω⁻¹)⁻¹` satisfies all the domination
  equations of the exponential series at `−logOmega`** — every residual
  `(1+ω⁻¹)⁻¹ − Σ_{k<n} (−logOmega)ᵏ/k!` has Archimedean class at least that of
  `(−logOmega)ⁿ/n!` (= that of `ω⁻ⁿ`).

The algebraic half is a **new polynomial identity** mirroring `ExpLog`'s truncated
`exp ∘ log = id`, built from two clean sub-identities:

* `X_pow_dvd_expPoly_mul_comp_neg` — **the reflection identity**
  `E_n(X)·E_n(−X) ≡ 1 (mod Xⁿ)`: the coefficient of `X^d` (`1 ≤ d < n`) of the
  product is `Σ_{i+j=d} (−1)ʲ/(i!·j!) = (1−1)^d/d! = 0` by the binomial theorem;
* `X_pow_dvd_one_add_mul_expPoly_comp_neg_logPoly` — composing the reflection
  identity at `L_n` (which has zero constant coefficient, so `Xⁿ ∣ Lₙⁿ`) and
  combining with the banked `X_pow_dvd_expPoly_comp_logPoly`
  (`E_n(L_n) ≡ 1 + X`) gives **`(1+X)·E_n(−L_n(X)) ≡ 1 (mod Xⁿ)`**.

The domination transport then runs exactly as in `ExpLog`: the composition defect is
`Xⁿ`-divisible with cofactor `(1+ω⁻¹)⁻¹` of class `0`, and the substitution error
`E_n(−logOmega) − E_n(−L_n(ω⁻¹))` peels through the geometric cofactors
(`Commute.geom_sum₂_mul`, all factors finite) against the stage-`n` Hahn residual of
`logOmega`.

Side lemmas banked for the identification half downstream:
`neg_logOmega_infinitesimal`, `neg_logOmega_ne_zero`, `mk_neg_logOmega`.
-/

open ArchimedeanClass Filter Finset Polynomial

noncomputable section

namespace Surreal

local notation "ε₀" => eps0

/-! ### The reflection identity `E_n(X)·E_n(−X) ≡ 1 (mod Xⁿ)` -/

/-- Coefficient extraction for range-indexed `C·Xᵏ` sums. -/
private theorem coeff_C_mul_X_pow_sum (f : ℕ → ℝ) (n d : ℕ) :
    (∑ k ∈ Finset.range n, Polynomial.C (f k) * Polynomial.X ^ k).coeff d =
      if d < n then f d else 0 := by
  rw [Polynomial.finsetSum_coeff]
  have h : ∀ k ∈ Finset.range n,
      (Polynomial.C (f k) * Polynomial.X ^ k).coeff d = if k = d then f k else 0 := by
    intro k _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hkd : k = d
    · simp [hkd]
    · simp [hkd, Ne.symm hkd]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (Finset.range n) d f]
  simp [Finset.mem_range]

private theorem coeff_expPoly (n d : ℕ) :
    (expPoly n).coeff d = if d < n then ((d.factorial : ℝ))⁻¹ else 0 := by
  unfold expPoly
  exact coeff_C_mul_X_pow_sum _ n d

/-- `E_n(−X)` in explicit range-sum form. -/
private theorem expPoly_comp_neg (n : ℕ) :
    (expPoly n).comp (-Polynomial.X) =
      ∑ k ∈ Finset.range n,
        Polynomial.C ((-1) ^ k * ((k.factorial : ℝ))⁻¹) * Polynomial.X ^ k := by
  show Polynomial.eval₂ Polynomial.C (-Polynomial.X) (expPoly n) = _
  unfold expPoly
  rw [Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hC : ((-1 : ℝ[X]) ^ k) = Polynomial.C ((-1 : ℝ) ^ k) := by
    rw [map_pow, map_neg, map_one]
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, neg_pow, hC,
    Polynomial.C_mul]
  ring

private theorem coeff_expPoly_comp_neg (n d : ℕ) :
    ((expPoly n).comp (-Polynomial.X)).coeff d =
      if d < n then (-1) ^ d * ((d.factorial : ℝ))⁻¹ else 0 := by
  rw [expPoly_comp_neg]
  exact coeff_C_mul_X_pow_sum _ n d

/-- The binomial cancellation `Σ_{k≤d} (−1)^{d−k}/(k!·(d−k)!) = (1−1)^d/d! = 0` for
`d ≥ 1`. -/
private theorem alternating_factorial_sum {d : ℕ} (hd : 0 < d) :
    ∑ k ∈ Finset.range (d + 1),
      ((k.factorial : ℝ))⁻¹ * ((-1) ^ (d - k) * (((d - k).factorial : ℝ))⁻¹) = 0 := by
  have hkey : ∀ k ∈ Finset.range (d + 1),
      ((k.factorial : ℝ))⁻¹ * ((-1) ^ (d - k) * (((d - k).factorial : ℝ))⁻¹) =
        (1 : ℝ) ^ k * (-1) ^ (d - k) * ((d.choose k : ℕ) : ℝ) *
          ((d.factorial : ℝ))⁻¹ := by
    intro k hk
    have hkd : k ≤ d := by
      have := Finset.mem_range.1 hk
      omega
    have h1 : ((k.factorial : ℝ)) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have h2 : (((d - k).factorial : ℝ)) ≠ 0 := by exact_mod_cast (d - k).factorial_ne_zero
    have h3 : ((d.factorial : ℝ)) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
    rw [Nat.cast_choose (K := ℝ) hkd]
    field_simp
    ring
  rw [Finset.sum_congr rfl hkey, ← Finset.sum_mul, ← add_pow, add_neg_cancel,
    zero_pow hd.ne', zero_mul]

/-- **The reflection identity**: `Xⁿ ∣ E_n(X)·E_n(−X) − 1` — truncated
`exp(y)·exp(−y) = 1`. -/
theorem X_pow_dvd_expPoly_mul_comp_neg (n : ℕ) :
    Polynomial.X ^ n ∣ expPoly n * (expPoly n).comp (-Polynomial.X) - 1 := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub, Polynomial.coeff_one]
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · rw [if_pos rfl, Polynomial.mul_coeff_zero, coeff_expPoly, coeff_expPoly_comp_neg,
      if_pos hd, if_pos hd]
    norm_num [Nat.factorial]
  · rw [if_neg hd0.ne', sub_zero, Polynomial.coeff_mul]
    have hcoe : ∀ p ∈ Finset.antidiagonal d,
        (expPoly n).coeff p.1 * ((expPoly n).comp (-Polynomial.X)).coeff p.2 =
          ((p.1.factorial : ℝ))⁻¹ * ((-1) ^ p.2 * ((p.2.factorial : ℝ))⁻¹) := by
      intro p hp
      have hpd := Finset.mem_antidiagonal.1 hp
      have h1 : p.1 < n := by omega
      have h2 : p.2 < n := by omega
      rw [coeff_expPoly, coeff_expPoly_comp_neg, if_pos h1, if_pos h2]
    calc ∑ p ∈ Finset.antidiagonal d,
          (expPoly n).coeff p.1 * ((expPoly n).comp (-Polynomial.X)).coeff p.2
        = ∑ k ∈ Finset.range (d + 1),
            ((k.factorial : ℝ))⁻¹ * ((-1) ^ (d - k) * (((d - k).factorial : ℝ))⁻¹) := by
          rw [Finset.sum_congr rfl hcoe]
          exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j ↦ ((i.factorial : ℝ))⁻¹ * ((-1) ^ j * ((j.factorial : ℝ))⁻¹)) d
      _ = 0 := alternating_factorial_sum hd0

/-! ### Composition at the truncated logarithm -/

/-- `L_N` has zero constant coefficient. -/
private theorem X_dvd_logPoly (N : ℕ) : Polynomial.X ∣ logPoly N := by
  unfold logPoly
  exact Finset.dvd_sum fun j _ ↦
    (dvd_pow_self Polynomial.X j.succ_ne_zero).mul_left _

/-- Composition at a polynomial with zero constant coefficient preserves
`Xⁿ`-divisibility. -/
private theorem X_pow_dvd_comp_logPoly {Q : ℝ[X]} {n : ℕ}
    (h : Polynomial.X ^ n ∣ Q) : Polynomial.X ^ n ∣ Q.comp (logPoly n) := by
  obtain ⟨S, rfl⟩ := h
  rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_logPoly n) n) _

/-- **The inverse polynomial identity**: `Xⁿ ∣ (1+X)·E_n(−L_n(X)) − 1` — truncated
`(1+x)·exp(−log(1+x)) = 1`. Proof: compose the reflection identity at `L_n` and
combine with the banked truncated `exp ∘ log = id`. -/
theorem X_pow_dvd_one_add_mul_expPoly_comp_neg_logPoly (n : ℕ) :
    Polynomial.X ^ n ∣
      (1 + Polynomial.X) * (expPoly n).comp (-logPoly n) - 1 := by
  have hA : Polynomial.X ^ n ∣
      (expPoly n).comp (logPoly n) * (expPoly n).comp (-logPoly n) - 1 := by
    have h := X_pow_dvd_comp_logPoly (X_pow_dvd_expPoly_mul_comp_neg n)
    rwa [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.one_comp,
      Polynomial.comp_assoc, Polynomial.neg_comp, Polynomial.X_comp] at h
  have hB : Polynomial.X ^ n ∣
      ((expPoly n).comp (logPoly n) - (1 + Polynomial.X)) *
        (expPoly n).comp (-logPoly n) :=
    (X_pow_dvd_expPoly_comp_logPoly n n le_rfl).mul_right _
  have hkey : (1 + Polynomial.X) * (expPoly n).comp (-logPoly n) - 1 =
      ((expPoly n).comp (logPoly n) * (expPoly n).comp (-logPoly n) - 1) -
      ((expPoly n).comp (logPoly n) - (1 + Polynomial.X)) *
        (expPoly n).comp (-logPoly n) := by
    ring
  rw [hkey]
  exact dvd_sub hA hB

/-! ### The negated canonical logarithm -/

theorem neg_logOmega_infinitesimal : Infinitesimal (-logOmega) :=
  logOmega_infinitesimal.neg

theorem neg_logOmega_ne_zero : (-logOmega) ≠ 0 :=
  neg_ne_zero.2 logOmega_pos.ne'

theorem mk_neg_logOmega : ArchimedeanClass.mk (-logOmega) =
    ArchimedeanClass.mk ((ω^ (1 : Surreal))⁻¹) := by
  rw [ArchimedeanClass.mk_neg, mk_logOmega]

private theorem mk_neg_logOmega_eps0 :
    ArchimedeanClass.mk (-logOmega) = ArchimedeanClass.mk (ε₀ : Surreal.{0}) :=
  mk_neg_logOmega

/-! ### Local domination-calculus helpers -/

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

private theorem logCoeff_ne_zero (k : ℕ) : ((-1) ^ k / (k + 1) : ℝ) ≠ 0 :=
  div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)

private theorem partialSum_logSeries_eq' (N : ℕ) :
    partialSum logSeries N = (logPoly N).eval₂ realHom (ε₀ : Surreal.{0}) :=
  partialSum_logSeries_eq N

private theorem mk_logSeries' (k : ℕ) :
    ArchimedeanClass.mk (logSeries k) =
      ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ (k + 1)) := by
  show ArchimedeanClass.mk
      ((((-1) ^ k / (k + 1) : ℝ) : Surreal) * (ε₀ : Surreal.{0}) ^ (k + 1)) = _
  rw [ArchimedeanClass.mk_mul, mk_realCast (logCoeff_ne_zero k), zero_add]

/-! ### The domination half -/

/-- **`(1+ω⁻¹)⁻¹` satisfies the domination equations of the exponential series at
`−logOmega`**: the residual at stage `n` combines the composition defect of the inverse
polynomial identity (`Xⁿ`-divisible, with the class-`0` cofactor `(1+ω⁻¹)⁻¹`) with the
substitution error `E_n(−logOmega) − E_n(−L_n(ω⁻¹))` (a multiple of the stage-`n` Hahn
residual of `logOmega`, via the geometric cofactors), both of class at least that of
`ω^{−n}`. -/
theorem isHahnSum_expSeries_neg_logOmega :
    IsHahnSum (fun k ↦ (-logOmega) ^ k / ((k.factorial : ℕ) : Surreal))
      (((1 : Surreal.{0}) + eps0)⁻¹) := by
  intro n
  -- the polynomial factorization of the composition defect
  obtain ⟨P, hP⟩ := X_pow_dvd_one_add_mul_expPoly_comp_neg_logPoly n
  -- Term 1: `E_n(−Lval) − (1+ω⁻¹)⁻¹ = (1+ω⁻¹)⁻¹·ω^{−n}·P(ω⁻¹)`
  have hterm1 : (expPoly n).eval₂ realHom (-(partialSum logSeries n)) - (1 + ε₀)⁻¹ =
      (1 + ε₀)⁻¹ * ((ε₀ : Surreal.{0}) ^ n * P.eval₂ realHom ε₀) := by
    have hev := congrArg (Polynomial.eval₂ realHom (ε₀ : Surreal.{0})) hP
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_add,
      Polynomial.eval₂_one, Polynomial.eval₂_X, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_comp, Polynomial.eval₂_neg] at hev
    rw [← partialSum_logSeries_eq'] at hev
    calc (expPoly n).eval₂ realHom (-(partialSum logSeries n)) - (1 + ε₀)⁻¹
        = (1 + ε₀)⁻¹ * ((1 + ε₀) *
            (expPoly n).eval₂ realHom (-(partialSum logSeries n)) - 1) := by
          rw [mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ one_add_eps0_ne_zero,
            one_mul]
      _ = (1 + ε₀)⁻¹ * ((ε₀ : Surreal.{0}) ^ n * P.eval₂ realHom ε₀) := by rw [hev]
  -- the composition defect is below scale `ω^{−n}`
  have hmk1 : ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n) ≤
      ArchimedeanClass.mk ((expPoly n).eval₂ realHom (-(partialSum logSeries n)) -
        (1 + ε₀)⁻¹) := by
    rw [hterm1, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, mk_inv_one_add_eps0,
      zero_add]
    have hPfin : (0 : ArchimedeanClass Surreal) ≤
        ArchimedeanClass.mk (P.eval₂ realHom (ε₀ : Surreal.{0})) :=
      isFinite_eval₂ _ eps0_infinitesimal.isFinite
    calc ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n)
        = ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n) + 0 := (add_zero _).symm
      _ ≤ _ := add_le_add le_rfl hPfin
  -- finiteness of the two substitution points
  have hLfin : IsFinite (-(partialSum logSeries n)) := by
    refine IsFinite.neg ?_
    rw [partialSum_logSeries_eq']
    exact isFinite_eval₂ _ eps0_infinitesimal.isFinite
  have hσfin : IsFinite (-logOmega) := isFinite_logOmega.neg
  -- Term 2: `E_n(−logOmega) − E_n(−Lval)` is dominated by the stage-`n` Hahn residual
  have hterm2 : ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n) ≤
      ArchimedeanClass.mk ((expPoly n).eval₂ realHom (-logOmega) -
        (expPoly n).eval₂ realHom (-(partialSum logSeries n))) := by
    rw [← partialSum_expSeries_eq_eval, ← partialSum_expSeries_eq_eval,
      partialSum, partialSum, ← Finset.sum_sub_distrib]
    refine le_mk_sum' fun k _ ↦ ?_
    have hsplit : (-logOmega) ^ k / ((k.factorial : ℕ) : Surreal) -
        (-(partialSum logSeries n)) ^ k / ((k.factorial : ℕ) : Surreal) =
        (((k.factorial : ℕ) : Surreal))⁻¹ *
          ((∑ i ∈ Finset.range k,
            (-logOmega) ^ i * (-(partialSum logSeries n)) ^ (k - 1 - i)) *
            (-logOmega - -(partialSum logSeries n))) := by
      rw [(Commute.all (-logOmega) (-(partialSum logSeries n))).geom_sum₂_mul k]
      ring
    rw [hsplit, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul]
    have hinv0 : ArchimedeanClass.mk ((((k.factorial : ℕ) : Surreal))⁻¹) = 0 := by
      rw [ArchimedeanClass.mk_inv, mk_factorial, neg_zero]
    have hcof : (0 : ArchimedeanClass Surreal) ≤ ArchimedeanClass.mk
        (∑ i ∈ Finset.range k,
          (-logOmega) ^ i * (-(partialSum logSeries n)) ^ (k - 1 - i)) := by
      refine isFinite_sum fun i _ ↦ ?_
      exact (hσfin.pow i).mul (hLfin.pow (k - 1 - i))
    have hres : ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n) ≤
        ArchimedeanClass.mk (-logOmega - -(partialSum logSeries n)) := by
      have hneg : -logOmega - -(partialSum logSeries n) =
          -(logOmega - partialSum logSeries n) := by ring
      rw [hneg, ArchimedeanClass.mk_neg]
      refine le_trans ?_ (isHahnSum_logSeries_logOmega n)
      rw [mk_logSeries']
      exact (mk_pow_lt_mk_pow_succ' eps0_infinitesimal eps0_pos.ne' n).le
    calc ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n)
        = 0 + (0 + ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n)) := by
          rw [zero_add, zero_add]
      _ ≤ ArchimedeanClass.mk ((((k.factorial : ℕ) : Surreal))⁻¹) +
          (ArchimedeanClass.mk (∑ i ∈ Finset.range k,
              (-logOmega) ^ i * (-(partialSum logSeries n)) ^ (k - 1 - i)) +
            ArchimedeanClass.mk (-logOmega - -(partialSum logSeries n))) := by
          rw [hinv0]
          exact add_le_add le_rfl (add_le_add hcof hres)
  -- assemble the residual
  have hsplit : ((1 : Surreal.{0}) + ε₀)⁻¹ -
      partialSum (fun k ↦ (-logOmega) ^ k / ((k.factorial : ℕ) : Surreal)) n =
      -((expPoly n).eval₂ realHom (-(partialSum logSeries n)) - (1 + ε₀)⁻¹) +
      -((expPoly n).eval₂ realHom (-logOmega) -
        (expPoly n).eval₂ realHom (-(partialSum logSeries n))) := by
    rw [partialSum_expSeries_eq_eval]
    ring
  have htarget : ArchimedeanClass.mk
      ((-logOmega) ^ n / ((n.factorial : ℕ) : Surreal)) =
      ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n) := by
    rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero]
    exact mk_pow_congr mk_neg_logOmega_eps0 n
  show ArchimedeanClass.mk ((-logOmega) ^ n / ((n.factorial : ℕ) : Surreal)) ≤ _
  rw [htarget, hsplit]
  refine le_trans (le_min ?_ ?_) (ArchimedeanClass.min_le_mk_add ..)
  · rwa [ArchimedeanClass.mk_neg]
  · rwa [ArchimedeanClass.mk_neg]

end Surreal

end
