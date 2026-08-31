import Infinity.MonomialCensus
import Infinity.ExpLog
import Infinity.ExpLadder

/-!
# `exp (log (1 + a·ω⁻¹)) = 1 + a·ω⁻¹` for every nonzero dyadic `a`

`Infinity.ExpLog` evaluated the canonical-sum exponential exactly once: at the
canonical logarithm of `1 + ω⁻¹`. This file generalizes both halves of that theorem
from the single anchor `ω⁻¹` to the **entire dyadic halo grid**, and strengthens the
identification from the canonical logarithm to *every* Hahn sum of the log series:

* `logSeriesAt x` — the Maclaurin series of `log (1+t)` at a general surreal `t = x`;
  strictly dominating for every nonzero infinitesimal `x`.
* `isHahnSum_expSeries_one_add_of_isHahnSum_log` — **the generic domination half**:
  for every nonzero infinitesimal `x` and *every* Hahn sum `σ` of `logSeriesAt x`,
  the value `1 + x` is a Hahn sum of the exponential series at `σ`. The polynomial
  identity of `ExpLog` (`X_pow_dvd_expPoly_comp_logPoly`) was already generic in the
  anchor; this ports the domination calculus to match.
* `expInf_eq_one_add_of_isHahnSum_log` — **THE EXP∘LOG GRID THEOREM**: for every
  nonzero dyadic `a` and every Hahn sum `σ` of the log series at `a·ω⁻¹`,
  **`expInf σ = 1 + a·ω⁻¹`** — the exponential inverts the logarithm on the whole
  day-`ω` halo grid, and *collapses the entire Hahn-sum fibre of the logarithm* to
  the single true value (`expInf_log_fibre`): it does not matter which log you take.
* `expInf_logGrid_eq` / `birthday_expInf_logGrid` — the canonical instances:
  `exp (log (1 + a·ω⁻¹)) = 1 + a·ω⁻¹` with `birthday = ω + (hgt a − 1)` **exactly** —
  a second infinite family of exact exponential values, this one indexed by the
  dyadic birth tree, with birthdays filling the entire block `[ω, ω·2)` rung by rung
  (compare the ladder of `Infinity.ExpLadder`, whose birthdays fill the blocks
  `ω, ω·2, ω·3, …`).

The identification is a day-`ω·2` census argument: every Hahn sum of the exponential
series at `σ` lies strictly inside every scale of the halo of `1 + a·ω⁻¹`
(`ladder_strict`, reused from the ladder — the census side is parametric); a Hahn sum
born before day `ω·2` is a grid point `b + r·ω⁻¹` by the uniform census
(`eq_grid_of_isFinite_of_birthday_le`), and sub-all-scales proximity forces `b = 1`
(standard parts) and then `r = a` (the `ω⁻¹` coefficient) — so it *is* the value; every
other Hahn sum is born at or after day `ω·2`, while the value is born by
`ω + (hgt a − 1) < ω·2`.
-/

open ArchimedeanClass Filter Finset IGame Polynomial Set

noncomputable section

namespace Surreal

local notation "ε₀" => eps0
local notation "Ω" => NatOrdinal.of Ordinal.omega0

/-! ### Local basics -/

private theorem eps0_inf : Infinitesimal ε₀ :=
  infinitesimal_inv_wpow one_pos

private theorem mk_pow_congr' {a b : Surreal}
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

private theorem dyadic_mul_eps0_infinitesimal (a : Dyadic) :
    Infinitesimal ((a : Surreal.{0}) * ε₀) := by
  have h := eps0_inf.mul_isFinite (isFinite_dyadic_cast a)
  rwa [mul_comm] at h

private theorem dyadic_cast_ne_zero' {a : Dyadic} (ha : a ≠ 0) : (a : Surreal.{0}) ≠ 0 := by
  intro h
  have hm := mk_dyadic_cast_ne_zero ha
  have htop : ArchimedeanClass.mk ((a : Dyadic) : Surreal.{0}) = ⊤ :=
    ArchimedeanClass.mk_eq_top_iff.2 h
  have h0 : (0 : ArchimedeanClass Surreal.{0}) = ⊤ := hm.symm.trans htop
  have h1 : ArchimedeanClass.mk (1 : Surreal.{0}) = ⊤ := mk_one_surreal.trans h0
  exact one_ne_zero (ArchimedeanClass.mk_eq_top_iff.1 h1)

private theorem dyadic_mul_eps0_ne_zero {a : Dyadic} (ha : a ≠ 0) :
    (a : Surreal.{0}) * ε₀ ≠ 0 :=
  mul_ne_zero (dyadic_cast_ne_zero' ha)
    (show (ω^ (1 : Surreal))⁻¹ ≠ 0 from inv_ne_zero (wpow_pos (1 : Surreal)).ne')

/-! ### The logarithm series at a general anchor -/

/-- The Maclaurin series of `log (1 + t)` at `t = x`:
`logSeriesAt x k = (−1)ᵏ x^{k+1}/(k+1)`. `Infinity.ExpLog`'s `logSeries` is the case
`x = ω⁻¹`. -/
def logSeriesAt (x : Surreal) (k : ℕ) : Surreal :=
  (((-1) ^ k / (k + 1) : ℝ) : Surreal) * x ^ (k + 1)

private theorem logCoeff_ne_zero' (k : ℕ) : ((-1) ^ k / (k + 1) : ℝ) ≠ 0 :=
  div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)

theorem mk_logSeriesAt (x : Surreal) (n : ℕ) :
    ArchimedeanClass.mk (logSeriesAt x n) = ArchimedeanClass.mk (x ^ (n + 1)) := by
  unfold logSeriesAt
  rw [ArchimedeanClass.mk_mul, mk_realCast (logCoeff_ne_zero' n), zero_add]

theorem logSeriesAt_strict_dominating {x : Surreal} (hx : Infinitesimal x) (hx0 : x ≠ 0)
    (k : ℕ) :
    ArchimedeanClass.mk (logSeriesAt x k) < ArchimedeanClass.mk (logSeriesAt x (k + 1)) := by
  rw [mk_logSeriesAt, mk_logSeriesAt]
  exact mk_pow_lt_mk_pow_succ' hx hx0 (k + 1)

/-- The partial sums of the log series at `x` are the truncated-logarithm values. -/
theorem partialSum_logSeriesAt_eq (x : Surreal) (N : ℕ) :
    partialSum (logSeriesAt x) N = (logPoly N).eval₂ realHom x := by
  rw [partialSum, logPoly, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  rfl

private theorem partialSum_logSeriesAt_one (x : Surreal) :
    partialSum (logSeriesAt x) 1 = x := by
  rw [partialSum, Finset.sum_range_one]
  unfold logSeriesAt
  norm_num

/-! ### Every Hahn sum of the log series has the class of the anchor -/

theorem mk_lt_mk_sub_of_isHahnSum_log {x σ : Surreal} (hx : Infinitesimal x) (hx0 : x ≠ 0)
    (hσ : IsHahnSum (logSeriesAt x) σ) :
    ArchimedeanClass.mk x < ArchimedeanClass.mk (σ - x) := by
  have h := hσ 1
  rw [partialSum_logSeriesAt_one] at h
  calc ArchimedeanClass.mk x
      = ArchimedeanClass.mk (logSeriesAt x 0) := by
        rw [mk_logSeriesAt, zero_add, pow_one]
    _ < ArchimedeanClass.mk (logSeriesAt x 1) := logSeriesAt_strict_dominating hx hx0 0
    _ ≤ _ := h

theorem mk_of_isHahnSum_log {x σ : Surreal} (hx : Infinitesimal x) (hx0 : x ≠ 0)
    (hσ : IsHahnSum (logSeriesAt x) σ) :
    ArchimedeanClass.mk σ = ArchimedeanClass.mk x := by
  have h : σ = x + (σ - x) := by ring
  rw [h, ArchimedeanClass.mk_add_eq_mk_left (mk_lt_mk_sub_of_isHahnSum_log hx hx0 hσ)]

theorem infinitesimal_of_isHahnSum_log {x σ : Surreal} (hx : Infinitesimal x) (hx0 : x ≠ 0)
    (hσ : IsHahnSum (logSeriesAt x) σ) : Infinitesimal σ := by
  rw [infinitesimal_def, mk_of_isHahnSum_log hx hx0 hσ]
  exact infinitesimal_def.1 hx

theorem ne_zero_of_isHahnSum_log {x σ : Surreal} (hx : Infinitesimal x) (hx0 : x ≠ 0)
    (hσ : IsHahnSum (logSeriesAt x) σ) : σ ≠ 0 := by
  intro h
  have habs := abs_lt_abs_of_mk_lt (mk_lt_mk_sub_of_isHahnSum_log hx hx0 hσ)
  rw [h, zero_sub, abs_neg] at habs
  exact lt_irrefl _ habs

/-! ### The generic domination half: `1 + x` is a Hahn sum of `exp` at any log -/

/-- **The generic domination half**: for every nonzero infinitesimal `x` and *every*
Hahn sum `σ` of the logarithm series at `x`, the value `1 + x` satisfies all the
domination equations of the exponential series at `σ`. The polynomial half is
`ExpLog`'s truncated `exp ∘ log = id` (generic in the anchor); the residual transfer
runs through the geometric cofactors exactly as at `ω⁻¹`. -/
theorem isHahnSum_expSeries_one_add_of_isHahnSum_log {x σ : Surreal}
    (hx : Infinitesimal x) (hx0 : x ≠ 0)
    (hσ : IsHahnSum (logSeriesAt x) σ) :
    IsHahnSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) (1 + x) := by
  intro n
  obtain ⟨P, hP⟩ := X_pow_dvd_expPoly_comp_logPoly n n le_rfl
  -- Term 1: `E_n(Lval) − (1 + x) = xⁿ·P(x)`
  have hterm1 : (expPoly n).eval₂ realHom (partialSum (logSeriesAt x) n) - (1 + x) =
      x ^ n * P.eval₂ realHom x := by
    have h := congrArg (Polynomial.eval₂ realHom x) hP
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_X,
      Polynomial.eval₂_comp, ← partialSum_logSeriesAt_eq] at h
    exact h
  have hLfin : IsFinite (partialSum (logSeriesAt x) n) := by
    rw [partialSum_logSeriesAt_eq]
    exact isFinite_eval₂ _ hx.isFinite
  have hσfin : IsFinite σ := (infinitesimal_of_isHahnSum_log hx hx0 hσ).isFinite
  -- Term 2: `E_n(σ) − E_n(Lval)` is dominated by the stage-`n` Hahn residual
  have hterm2 : ArchimedeanClass.mk (x ^ n) ≤
      ArchimedeanClass.mk ((expPoly n).eval₂ realHom σ -
        (expPoly n).eval₂ realHom (partialSum (logSeriesAt x) n)) := by
    rw [← partialSum_expSeries_eq_eval, ← partialSum_expSeries_eq_eval,
      partialSum, partialSum, ← Finset.sum_sub_distrib]
    refine le_mk_sum' fun k _ ↦ ?_
    have hsplit : σ ^ k / ((k.factorial : ℕ) : Surreal) -
        (partialSum (logSeriesAt x) n) ^ k / ((k.factorial : ℕ) : Surreal) =
        (((k.factorial : ℕ) : Surreal))⁻¹ *
          ((∑ i ∈ Finset.range k,
            σ ^ i * (partialSum (logSeriesAt x) n) ^ (k - 1 - i)) *
            (σ - partialSum (logSeriesAt x) n)) := by
      rw [(Commute.all σ (partialSum (logSeriesAt x) n)).geom_sum₂_mul k]
      ring
    rw [hsplit, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul]
    have hinv0 : ArchimedeanClass.mk ((((k.factorial : ℕ) : Surreal))⁻¹) = 0 := by
      rw [ArchimedeanClass.mk_inv, mk_factorial, neg_zero]
    have hcof : (0 : ArchimedeanClass Surreal) ≤ ArchimedeanClass.mk
        (∑ i ∈ Finset.range k,
          σ ^ i * (partialSum (logSeriesAt x) n) ^ (k - 1 - i)) := by
      refine isFinite_sum fun i _ ↦ ?_
      exact (hσfin.pow i).mul (hLfin.pow (k - 1 - i))
    have hres : ArchimedeanClass.mk (x ^ n) ≤
        ArchimedeanClass.mk (σ - partialSum (logSeriesAt x) n) := by
      refine le_trans ?_ (hσ n)
      rw [mk_logSeriesAt]
      exact (mk_pow_lt_mk_pow_succ' hx hx0 n).le
    calc ArchimedeanClass.mk (x ^ n)
        = 0 + (0 + ArchimedeanClass.mk (x ^ n)) := by
          rw [zero_add, zero_add]
      _ ≤ ArchimedeanClass.mk ((((k.factorial : ℕ) : Surreal))⁻¹) +
          (ArchimedeanClass.mk (∑ i ∈ Finset.range k,
              σ ^ i * (partialSum (logSeriesAt x) n) ^ (k - 1 - i)) +
            ArchimedeanClass.mk (σ - partialSum (logSeriesAt x) n)) := by
          rw [hinv0]
          exact add_le_add le_rfl (add_le_add hcof hres)
  -- assemble the residual
  have hsplit : 1 + x -
      partialSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) n =
      -((expPoly n).eval₂ realHom (partialSum (logSeriesAt x) n) - (1 + x)) +
      -((expPoly n).eval₂ realHom σ -
        (expPoly n).eval₂ realHom (partialSum (logSeriesAt x) n)) := by
    rw [partialSum_expSeries_eq_eval]
    ring
  have hmk1 : ArchimedeanClass.mk (x ^ n) ≤
      ArchimedeanClass.mk ((expPoly n).eval₂ realHom (partialSum (logSeriesAt x) n) -
        (1 + x)) := by
    rw [hterm1, ArchimedeanClass.mk_mul]
    have hPfin : (0 : ArchimedeanClass Surreal) ≤
        ArchimedeanClass.mk (P.eval₂ realHom x) :=
      isFinite_eval₂ _ hx.isFinite
    calc ArchimedeanClass.mk (x ^ n)
        = ArchimedeanClass.mk (x ^ n) + 0 := (add_zero _).symm
      _ ≤ _ := add_le_add le_rfl hPfin
  have htarget : ArchimedeanClass.mk
      (σ ^ n / ((n.factorial : ℕ) : Surreal)) =
      ArchimedeanClass.mk (x ^ n) := by
    rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero]
    exact mk_pow_congr' (mk_of_isHahnSum_log hx hx0 hσ) n
  show ArchimedeanClass.mk (σ ^ n / ((n.factorial : ℕ) : Surreal)) ≤ _
  rw [htarget, hsplit]
  refine le_trans (le_min ?_ ?_) (ArchimedeanClass.min_le_mk_add ..)
  · rwa [ArchimedeanClass.mk_neg]
  · rwa [ArchimedeanClass.mk_neg]

/-! ### The census identification below day `ω·2` -/

/-- **The census forcing**: a Hahn sum of the exponential series at `σ` (of class
`ω⁻¹`) born before day `ω·2` *is* the value `1 + a·ω⁻¹` — by the uniform grid census,
it is `b + r·ω⁻¹`; sub-all-scales proximity forces `b = 1` and `r = a`. -/
theorem eq_of_isHahnSum_expSeries_of_birthday_lt {a : Dyadic} {σ z : Surreal.{0}}
    (hσmk : ArchimedeanClass.mk σ = ArchimedeanClass.mk ε₀)
    (hv : IsHahnSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal))
      (1 + (a : Surreal) * ε₀))
    (hz : IsHahnSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) z)
    (hb : z.birthday < Ω * ((2 : ℕ) : NatOrdinal)) :
    z = 1 + (a : Surreal) * ε₀ := by
  have h0 : ArchimedeanClass.mk (ε₀ ^ 0) <
      ArchimedeanClass.mk (z - (1 + (a : Surreal) * ε₀)) := ladder_strict hσmk hv hz 0
  have h1 : ArchimedeanClass.mk (ε₀ ^ 1) <
      ArchimedeanClass.mk (z - (1 + (a : Surreal) * ε₀)) := ladder_strict hσmk hv hz 1
  rw [pow_zero, mk_one_surreal] at h0
  rw [pow_one] at h1
  have hzv_inf : Infinitesimal (z - (1 + (a : Surreal) * ε₀)) := infinitesimal_def.2 h0
  have hvfin : IsFinite ((1 : Surreal.{0}) + (a : Surreal) * ε₀) :=
    isFinite_one.add (dyadic_mul_eps0_infinitesimal a).isFinite
  have hzfin : IsFinite z := by
    have h : z = (1 + (a : Surreal) * ε₀) + (z - (1 + (a : Surreal) * ε₀)) := by ring
    rw [h]
    exact hvfin.add hzv_inf.isFinite
  -- the uniform census below `ω·2`
  obtain ⟨m, hm⟩ := lt_omega_mul_succ_decomp 1 hb
  have hm' : z.birthday ≤ Ω + (m : NatOrdinal) := by
    have h1' : Ω * ((1 : ℕ) : NatOrdinal) = Ω := by norm_num
    rwa [h1'] at hm
  obtain ⟨r, hzeq, -, -⟩ := eq_grid_of_isFinite_of_birthday_le m hzfin hm'
  rw [wpow_neg_one_eq_eps0] at hzeq
  set s : ℝ := stdPart z with hsdef
  -- the difference in grid coordinates
  have hdiff : z - (1 + (a : Surreal) * ε₀) =
      (((s - 1 : ℝ)) : Surreal) + ((r - a : Dyadic) : Surreal) * ε₀ := by
    have hcast : ((s - 1 : ℝ) : Surreal) = ((s : ℝ) : Surreal) - 1 := by
      rw [show ((s - 1 : ℝ) : Surreal) = realHom (s - 1) from rfl, map_sub, map_one]
      rfl
    rw [hzeq, hcast, dyadic_cast_sub']
    ring
  -- the standard part forces `s = 1`
  have hs1 : s = 1 := by
    by_contra hs
    have hmk : ArchimedeanClass.mk (z - (1 + (a : Surreal) * ε₀)) = 0 := by
      rw [hdiff, ArchimedeanClass.mk_add_eq_mk_left, mk_realCast (sub_ne_zero.2 hs)]
      rw [mk_realCast (sub_ne_zero.2 hs)]
      exact infinitesimal_def.1 (dyadic_mul_eps0_infinitesimal (r - a))
    rw [hmk] at h0
    exact lt_irrefl _ h0
  -- the `ω⁻¹` coefficient forces `r = a`
  have hra : r = a := by
    by_contra hr
    have hmk : ArchimedeanClass.mk (z - (1 + (a : Surreal) * ε₀)) =
        ArchimedeanClass.mk ε₀ := by
      rw [hdiff, hs1, sub_self]
      rw [show ((0 : ℝ) : Surreal) = 0 from by norm_num, zero_add,
        ArchimedeanClass.mk_mul, mk_dyadic_cast_ne_zero (sub_ne_zero.2 hr), zero_add]
    rw [hmk] at h1
    exact lt_irrefl _ h1
  have hzero : z - (1 + (a : Surreal) * ε₀) = 0 := by
    rw [hdiff, hs1, hra, sub_self, sub_self, dyadic_cast_zero, zero_mul, add_zero]
    norm_num
  linarith [sub_eq_zero.1 hzero]

/-! ### THE EXP∘LOG GRID THEOREM -/

/-- **THE EXP∘LOG GRID THEOREM**: for every nonzero dyadic `a` and **every** Hahn sum
`σ` of the logarithm series at `a·ω⁻¹`, the canonical-sum exponential evaluates to
exactly `1 + a·ω⁻¹`. The exponential inverts the logarithm on the whole day-`ω` halo
grid — and collapses the entire Hahn-sum fibre of the logarithm to the one true
value. -/
theorem expInf_eq_one_add_of_isHahnSum_log {a : Dyadic} (ha : a ≠ 0) {σ : Surreal.{0}}
    (hσinf : Infinitesimal σ) (hσ0 : σ ≠ 0)
    (hσ : IsHahnSum (logSeriesAt ((a : Surreal) * ε₀)) σ) :
    expInf σ hσinf hσ0 = 1 + (a : Surreal) * ε₀ := by
  have hx : Infinitesimal ((a : Surreal.{0}) * ε₀) := dyadic_mul_eps0_infinitesimal a
  have hx0 : (a : Surreal.{0}) * ε₀ ≠ 0 := dyadic_mul_eps0_ne_zero ha
  have hσmk : ArchimedeanClass.mk σ = ArchimedeanClass.mk ε₀ := by
    rw [mk_of_isHahnSum_log hx hx0 hσ, ArchimedeanClass.mk_mul,
      mk_dyadic_cast_ne_zero ha, zero_add]
  have hv : IsHahnSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal))
      (1 + (a : Surreal) * ε₀) :=
    isHahnSum_expSeries_one_add_of_isHahnSum_log hx hx0 hσ
  unfold expInf
  rw [hahnSum_eq_iff]
  refine ⟨hv, fun z hz ↦ ?_⟩
  rcases lt_or_ge z.birthday (Ω * ((2 : ℕ) : NatOrdinal)) with hlt | hge
  · rw [eq_of_isHahnSum_expSeries_of_birthday_lt hσmk hv hz hlt]
  · have hub : ((1 : Surreal.{0}) + (a : Surreal) * ε₀).birthday
        ≤ Ω + ((Dyadic.hgt a - 1 : ℕ) : NatOrdinal) := by
      have h := birthday_dyadic_add_dyadic_mul_wpow_le 1 ha
      rwa [dyadic_cast_one, wpow_neg_one_eq_eps0] at h
    refine hub.trans (le_trans ?_ hge)
    have h2 : Ω * ((2 : ℕ) : NatOrdinal) = Ω + Ω := by
      have hc : ((2 : ℕ) : NatOrdinal) = 1 + 1 := by norm_num
      rw [hc, mul_add, mul_one]
    rw [h2]
    exact add_le_add le_rfl (nat_lt_omega' _).le

/-- **The fibre collapse**: the exponential takes the *same* value at every Hahn sum of
the logarithm series — it cannot see which logarithm was chosen. -/
theorem expInf_log_fibre {a : Dyadic} (ha : a ≠ 0) {σ τ : Surreal.{0}}
    (hσinf : Infinitesimal σ) (hσ0 : σ ≠ 0) (hτinf : Infinitesimal τ) (hτ0 : τ ≠ 0)
    (hσ : IsHahnSum (logSeriesAt ((a : Surreal) * ε₀)) σ)
    (hτ : IsHahnSum (logSeriesAt ((a : Surreal) * ε₀)) τ) :
    expInf σ hσinf hσ0 = expInf τ hτinf hτ0 := by
  rw [expInf_eq_one_add_of_isHahnSum_log ha hσinf hσ0 hσ,
    expInf_eq_one_add_of_isHahnSum_log ha hτinf hτ0 hτ]

/-! ### The canonical instances -/

/-- The canonical logarithm of `1 + a·ω⁻¹`: the birthday-simplest Hahn sum of the
logarithm series at `a·ω⁻¹`. `Infinity.ExpLog`'s `logOmega` is (up to the anchor cast)
the case `a = 1`. -/
def logGrid (a : Dyadic) (ha : a ≠ 0) : Surreal.{0} :=
  hahnSum (logSeriesAt_strict_dominating (dyadic_mul_eps0_infinitesimal a)
    (dyadic_mul_eps0_ne_zero ha))

theorem isHahnSum_logGrid (a : Dyadic) (ha : a ≠ 0) :
    IsHahnSum (logSeriesAt ((a : Surreal) * ε₀)) (logGrid a ha) :=
  isHahnSum_hahnSum _

theorem logGrid_infinitesimal (a : Dyadic) (ha : a ≠ 0) : Infinitesimal (logGrid a ha) :=
  infinitesimal_of_isHahnSum_log (dyadic_mul_eps0_infinitesimal a)
    (dyadic_mul_eps0_ne_zero ha) (isHahnSum_logGrid a ha)

theorem logGrid_ne_zero (a : Dyadic) (ha : a ≠ 0) : logGrid a ha ≠ 0 :=
  ne_zero_of_isHahnSum_log (dyadic_mul_eps0_infinitesimal a)
    (dyadic_mul_eps0_ne_zero ha) (isHahnSum_logGrid a ha)

/-- **`exp (log (1 + a·ω⁻¹)) = 1 + a·ω⁻¹` for every nonzero dyadic `a`** — the second
infinite family of exact exponential values, indexed by the dyadic birth tree. -/
theorem expInf_logGrid_eq (a : Dyadic) (ha : a ≠ 0) :
    expInf (logGrid a ha) (logGrid_infinitesimal a ha) (logGrid_ne_zero a ha)
      = 1 + (a : Surreal) * ε₀ :=
  expInf_eq_one_add_of_isHahnSum_log ha _ _ (isHahnSum_logGrid a ha)

/-- **The grid values are priced exactly**:
`birthday (expInf (logGrid a)) = ω + (hgt a − 1)` — the exponential's values along the
grid fill the entire block `[ω, ω·2)`, rung by rung of the dyadic birth tree. -/
theorem birthday_expInf_logGrid (a : Dyadic) (ha : a ≠ 0) :
    (expInf (logGrid a ha) (logGrid_infinitesimal a ha) (logGrid_ne_zero a ha)).birthday
      = Ω + ((Dyadic.hgt a - 1 : ℕ) : NatOrdinal) := by
  rw [expInf_logGrid_eq]
  have h := birthday_grid_dyadic_eq 1 ha
  rwa [dyadic_cast_one, wpow_neg_one_eq_eps0] at h

end Surreal

end
