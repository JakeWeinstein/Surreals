import Infinity.NegGrid
import Infinity.NegGridInverse
import Infinity.ExpNegGrid

/-!
# The negative grid theorem: `exp (−log (1 + a·ω⁻¹)) = (1 + a·ω⁻¹)⁻¹`

Endgame of the Phase-23 fleet. With the three pillars —

* `NegGrid` : the alternating-at-`a` residual calculus, the census lower bounds, and
  the general deep-halo trap;
* `NegGridInverse` : `birthday ((1+a·ω⁻¹)⁻¹) ≤ ω²` for every positive dyadic `a`
  (the Conway-inverse device, parametric);
* `ExpNegGrid` : the generic negative domination half —

this file closes, for **every positive dyadic `a`** and **every Hahn sum `σ` of the
log series at `a·ω⁻¹`**:

* `expInf_neg_of_isHahnSum_log` — **THE NEGATIVE GRID THEOREM**:
  `exp (−σ) = (1 + a·ω⁻¹)⁻¹`, fibre-generally (exp cannot see which logarithm was
  negated);
* `expInf_mul_expInf_neg_of_isHahnSum_log` — **THE GRID REFLECTION LAW**:
  `exp σ · exp (−σ) = 1` across the entire positive-anchor day-`ω` log grid;
* `hahnSum_negGrid_eq` — **an infinite family of computed canonical sums**:
  `hahnSum (Σ (−a)ᵏ ω⁻ᵏ) = (1 + a·ω⁻¹)⁻¹`, all born exactly on day `ω²`
  (`birthday_hahnSum_negGrid`, `birthday_inv_one_add_dyadic_eq`);
* `birthday_expInf_neg_of_isHahnSum_log` — every negative-grid exponential value is
  born exactly on day `ω·ω`, while its positive mirror is born in `[ω, ω·2)`
  (`ExpLogGrid.birthday_expInf_logGrid`): **inverting the argument sends the whole
  grid to the limit block**.
-/

noncomputable section

namespace Surreal

open ArchimedeanClass

local notation "ε₀" => eps0
local notation "Ω" => NatOrdinal.of Ordinal.omega0

/-! ### Exact birthdays of the values -/

/-- `birthday ((1 + a·ω⁻¹)⁻¹) = ω·ω` exactly, for every positive dyadic `a`. -/
theorem birthday_inv_one_add_dyadic_eq {a : Dyadic} (ha : 0 < a) :
    ((((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹)).birthday = Ω * Ω :=
  le_antisymm (birthday_inv_one_add_dyadic_le ha)
    (omega_sq_le_birthday_inv_one_add_dyadic ha.ne')

/-! ### The canonical-sum family -/

/-- **The negative-grid canonical sums**: `hahnSum (Σ (−a)ᵏ ω⁻ᵏ) = (1 + a·ω⁻¹)⁻¹`
for every positive dyadic `a` — an infinite family of computed values of the canonical
transfinite summation operator. -/
theorem hahnSum_negGrid_eq {a : Dyadic} (ha : 0 < a) :
    hahnSum (monoTerm_strict_dominating (negCoeff_ne_zero ha.ne'))
      = ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ :=
  hahnSum_eq_of_isHahnSum_of_birthday_le _ (isHahnSum_negGrid ha.ne')
    ((birthday_inv_one_add_dyadic_le ha).trans
      (mono_omega_sq_le_birthday_hahnSum (negCoeff_ne_zero ha.ne')))

/-- Every member of the family is born exactly on day `ω·ω`. -/
theorem birthday_hahnSum_negGrid {a : Dyadic} (ha : 0 < a) :
    (hahnSum (monoTerm_strict_dominating (negCoeff_ne_zero ha.ne'))).birthday
      = Ω * Ω := by
  rw [hahnSum_negGrid_eq ha]
  exact birthday_inv_one_add_dyadic_eq ha

/-! ### The `ω²` pricing of the exponential Hahn sums -/

private theorem mk_pow_congr''' {a b : Surreal}
    (h : ArchimedeanClass.mk a = ArchimedeanClass.mk b) (n : ℕ) :
    ArchimedeanClass.mk (a ^ n) = ArchimedeanClass.mk (b ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, ih, h]

/-- Every Hahn sum of the exponential series at `−σ` (any Hahn-sum log at a nonzero
dyadic anchor) is born at or after day `ω²`: all of them sit in the deep halo of
`(1 + a·ω⁻¹)⁻¹`, where the general trap prices them. -/
theorem omega_sq_le_birthday_of_isHahnSum_expNegGrid {a : Dyadic} (ha : a ≠ 0)
    {σ : Surreal.{0}} (hσ : IsHahnSum (logSeriesAt ((a : Surreal) * ε₀)) σ)
    {w : Surreal.{0}}
    (hw : IsHahnSum (fun k ↦ (-σ) ^ k / ((k.factorial : ℕ) : Surreal)) w) :
    Ω * Ω ≤ w.birthday := by
  have hx : Infinitesimal ((a : Surreal.{0}) * ε₀) := dyadic_mul_eps0_infinitesimal' a
  have hx0 : (a : Surreal.{0}) * ε₀ ≠ 0 := dyadic_mul_eps0_ne_zero' ha
  have hv := isHahnSum_expSeries_inv_one_add_of_isHahnSum_log hx hx0 hσ
  have hmkσ : ArchimedeanClass.mk (-σ) = ArchimedeanClass.mk (ε₀ : Surreal.{0}) := by
    rw [ArchimedeanClass.mk_neg, mk_of_isHahnSum_log hx hx0 hσ, mk_dyadic_mul_eps0 ha]
  refine mono_omega_sq_le_birthday_of_forall_mk_lt (negCoeff_ne_zero ha)
    (isHahnSum_negGrid ha) fun n ↦ ?_
  calc ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n)
      < ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ (n + 1)) :=
        mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos n
    _ = ArchimedeanClass.mk ((-σ) ^ (n + 1) / (((n + 1).factorial : ℕ) : Surreal)) := by
        rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero, mk_pow_congr''' hmkσ]
    _ ≤ ArchimedeanClass.mk (w - ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹) :=
        hw.mk_sub_le hv (n + 1)

/-! ### The negative grid theorem and the reflection law -/

/-- **THE NEGATIVE GRID THEOREM**: for every positive dyadic `a` and *every* Hahn sum
`σ` of the logarithm series at `a·ω⁻¹`, the canonical-sum exponential evaluates at
`−σ` to exactly `(1 + a·ω⁻¹)⁻¹`. Fibre-general: the exponential cannot see which
logarithm was negated. -/
theorem expInf_neg_of_isHahnSum_log {a : Dyadic} (ha : 0 < a) {σ : Surreal.{0}}
    (hσinf : Infinitesimal (-σ)) (hσ0 : (-σ) ≠ 0)
    (hσ : IsHahnSum (logSeriesAt ((a : Surreal) * ε₀)) σ) :
    expInf (-σ) hσinf hσ0 = ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ := by
  have hx : Infinitesimal ((a : Surreal.{0}) * ε₀) := dyadic_mul_eps0_infinitesimal' a
  have hx0 : (a : Surreal.{0}) * ε₀ ≠ 0 := dyadic_mul_eps0_ne_zero' ha.ne'
  unfold expInf
  rw [hahnSum_eq_iff]
  refine ⟨isHahnSum_expSeries_inv_one_add_of_isHahnSum_log hx hx0 hσ, fun w hw ↦ ?_⟩
  exact (birthday_inv_one_add_dyadic_le ha).trans
    (omega_sq_le_birthday_of_isHahnSum_expNegGrid ha.ne' hσ hw)

/-- **THE GRID REFLECTION LAW**: `exp σ · exp (−σ) = 1` for every Hahn sum `σ` of the
log series at any positive dyadic grid anchor `a·ω⁻¹` — the multiplicative-inverse
identity for the surreal exponential, exact across the whole day-`ω` log grid. -/
theorem expInf_mul_expInf_neg_of_isHahnSum_log {a : Dyadic} (ha : 0 < a)
    {σ : Surreal.{0}} (h1 : Infinitesimal σ) (h2 : σ ≠ 0)
    (h3 : Infinitesimal (-σ)) (h4 : (-σ) ≠ 0)
    (hσ : IsHahnSum (logSeriesAt ((a : Surreal) * ε₀)) σ) :
    expInf σ h1 h2 * expInf (-σ) h3 h4 = 1 := by
  rw [expInf_eq_one_add_of_isHahnSum_log ha.ne' h1 h2 hσ,
    expInf_neg_of_isHahnSum_log ha h3 h4 hσ]
  exact mul_inv_cancel₀ (one_add_dyadic_mul_eps0_ne_zero a)

/-- **Inversion sends the whole grid to the limit block**: every negative-grid
exponential value is born exactly on day `ω·ω`, while its positive mirror is born in
`[ω, ω·2)`. -/
theorem birthday_expInf_neg_of_isHahnSum_log {a : Dyadic} (ha : 0 < a)
    {σ : Surreal.{0}} (hσinf : Infinitesimal (-σ)) (hσ0 : (-σ) ≠ 0)
    (hσ : IsHahnSum (logSeriesAt ((a : Surreal) * ε₀)) σ) :
    (expInf (-σ) hσinf hσ0).birthday = Ω * Ω := by
  rw [expInf_neg_of_isHahnSum_log ha hσinf hσ0 hσ]
  exact birthday_inv_one_add_dyadic_eq ha

end Surreal

end
