import Infinity.ExpLogGrid

/-!
# The mixed functional equation: `exp (log u + log v) = u·v` across the halo grid

`Infinity.ExpLadder` proved the functional equation exactly on the lattice
`ℕ⁺·logOmega` — equal anchors, iterated. `Infinity.ExpLogGrid` evaluated the
exponential at the logarithm of every grid point `1 + a·ω⁻¹`. This file crosses the
two: the functional equation holds **exactly between logarithms at different anchors**,

* `expInf_add_eq_mul_of_isHahnSum_logs` — **THE MIXED FUNCTIONAL EQUATION**: for all
  positive dyadics `a, b` and *any* Hahn sums `σ, τ` of the logarithm series at
  `a·ω⁻¹` and `b·ω⁻¹`,
  **`expInf (σ + τ) = expInf σ · expInf τ`** — both sides `(1+a·ω⁻¹)(1+b·ω⁻¹)`.
  A two-parameter family of exact FE instances, fibre-general in both logarithms.
* `expInf_logGrid_add_eq_mul` / `expInf_logGrid_add_eq` — the canonical instances:
  `exp (log (1+a·ω⁻¹) + log (1+b·ω⁻¹)) = (1+a·ω⁻¹)·(1+b·ω⁻¹)`.

The identification pattern is the by-now-standard three-step:

1. **Hahn-sum half for free**: the Cauchy product (`isHahnSum_expInf_mul`) plus the
   two grid evaluations make `(1+a·ω⁻¹)(1+b·ω⁻¹)` a Hahn sum of the exponential
   series at `σ + τ`.
2. **Grid price**: the product `1 + (a+b)·ω⁻¹ + ab·ω⁻²` is the level-`2` grid point of
   the **pair-padded series** `(1, a+b, ab, 1, 1, …)` — all coefficients nonzero
   dyadics since `a, b > 0` — so its birthday is at most `ω·2 + (hgt (ab) − 1)`.
3. **Tube policing**: every Hahn sum of the series at `σ + τ` born below day `ω·3` is
   forced by the monomial tube census (`mono_census`, block `1`) onto the `ω⁻²`-grid
   over the pair anchors, and sub-all-scales proximity pins the grid coefficient to
   `ab` — so it *is* the product; everything else is born at or after day `ω·3`,
   beyond the product's price.

The census core (`expInf_eq_prod_of_isHahnSum`) is again parametric in the argument
`ρ` — only `mk ρ = mk ω⁻¹` and the product being a Hahn sum enter — so it will
serve any future source of Hahn-sum halves (longer products, non-canonical logs,
composed arguments).
-/

open ArchimedeanClass IGame Set

noncomputable section

namespace Surreal

local notation "ε₀" => eps0
local notation "Ω" => NatOrdinal.of Ordinal.omega0

/-! ### Local basics -/

private theorem eps0_inf : Infinitesimal ε₀ :=
  infinitesimal_inv_wpow one_pos

private theorem eps0_pos' : (0 : Surreal.{0}) < ε₀ :=
  inv_pos.2 (wpow_pos _)

private theorem dyadic_mul_eps0_infinitesimal (a : Dyadic) :
    Infinitesimal ((a : Surreal.{0}) * ε₀) := by
  have h := eps0_inf.mul_isFinite (isFinite_dyadic_cast a)
  rwa [mul_comm] at h

/-- Hahn sums of the logarithm series at a positive anchor are positive. -/
theorem pos_of_isHahnSum_log {x σ : Surreal} (hx : Infinitesimal x) (hx0 : 0 < x)
    (hσ : IsHahnSum (logSeriesAt x) σ) : 0 < σ := by
  have habs := abs_lt_abs_of_mk_lt (mk_lt_mk_sub_of_isHahnSum_log hx hx0.ne' hσ)
  rw [abs_of_pos hx0] at habs
  have h := (abs_lt.1 habs).1
  linarith

/-! ### The pair-padded census series `(1, a+b, ab, 1, 1, …)` -/

/-- The pair-padded census coefficients: the expansion of `(1+a·ω⁻¹)(1+b·ω⁻¹)` padded
with a tail of ones. -/
def pairCoeff (a b : Dyadic) : ℕ → Dyadic := fun k ↦
  if k = 1 then a + b else if k = 2 then a * b else 1

theorem pairCoeff_ne_zero {a b : Dyadic} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (k : ℕ) : pairCoeff a b k ≠ 0 := by
  unfold pairCoeff
  split
  · exact hab
  · split
    · exact mul_ne_zero ha hb
    · exact one_ne_zero

private theorem monoS_pair_two (a b : Dyadic) :
    monoS (pairCoeff a b) 2 = 1 + ((a : Surreal) + (b : Surreal)) * ε₀ := by
  have h : monoS (pairCoeff a b) 2
      = monoS (pairCoeff a b) 1 + monoTerm (pairCoeff a b) 1 :=
    partialSum_succ (monoTerm (pairCoeff a b)) 1
  have h1 : monoS (pairCoeff a b) 1 = 1 := by
    rw [monoS_one, show pairCoeff a b 0 = 1 from rfl, dyadic_cast_one]
  have h2 : monoTerm (pairCoeff a b) 1 = ((a : Surreal) + (b : Surreal)) * ε₀ := by
    show ((pairCoeff a b 1 : Dyadic) : Surreal) * ε₀ ^ 1 = _
    rw [show pairCoeff a b 1 = a + b from rfl, dyadic_cast_add', pow_one]
  rw [h, h1, h2]

private theorem monoS_pair_grid (a b : Dyadic) :
    monoS (pairCoeff a b) 2 + ((a * b : Dyadic) : Surreal) * ε₀ ^ 2
      = (1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀) := by
  rw [monoS_pair_two, dyadic_cast_mul']
  ring

private theorem monoS_pair_full (a b : Dyadic) :
    monoS (pairCoeff a b) 3 = (1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀) := by
  have h : monoS (pairCoeff a b) 3
      = monoS (pairCoeff a b) 2 + monoTerm (pairCoeff a b) 2 :=
    partialSum_succ (monoTerm (pairCoeff a b)) 2
  have h2 : monoTerm (pairCoeff a b) 2 = ((a * b : Dyadic) : Surreal) * ε₀ ^ 2 := by
    show ((pairCoeff a b 2 : Dyadic) : Surreal) * ε₀ ^ 2 = _
    rw [show pairCoeff a b 2 = a * b from rfl]
  rw [h, h2, monoS_pair_grid]

/-! ### The tube forcing at block `1` -/

private theorem pair_tube_force {a b : Dyadic} (hc : ∀ k, pairCoeff a b k ≠ 0)
    {w z : Surreal.{0}} (hw : IsHahnSum (monoTerm (pairCoeff a b)) w) (m : ℕ)
    (hdist : ArchimedeanClass.mk (ε₀ ^ 1) < ArchimedeanClass.mk (z - w))
    (hb : z.birthday ≤ Ω * ((2 : ℕ) : NatOrdinal) + (m : NatOrdinal)) :
    ∃ t : Dyadic, z = monoS (pairCoeff a b) 2 + (t : Surreal) * ε₀ ^ 2 :=
  (mono_census hc hw 1 m hdist hb).imp fun _ ht ↦ ht.1

private theorem mk_pow_one_lt_three :
    ArchimedeanClass.mk (ε₀ ^ 1) < ArchimedeanClass.mk (ε₀ ^ 3) := by
  have ha : ArchimedeanClass.mk (ε₀ ^ 1) < ArchimedeanClass.mk (ε₀ ^ 2) :=
    mk_pow_lt_mk_pow_succ eps0_inf eps0_pos' 1
  have hb : ArchimedeanClass.mk (ε₀ ^ 2) < ArchimedeanClass.mk (ε₀ ^ 3) :=
    mk_pow_lt_mk_pow_succ eps0_inf eps0_pos' 2
  exact ha.trans hb

/-- **The census forcing at the pair**: a Hahn sum of the exponential series at `ρ`
(of class `ω⁻¹`) born before day `ω·3` *is* the product `(1+a·ω⁻¹)(1+b·ω⁻¹)`. -/
theorem eq_prod_of_isHahnSum_expSeries_of_birthday_lt {a b : Dyadic}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) {ρ z : Surreal.{0}}
    (hρmk : ArchimedeanClass.mk ρ = ArchimedeanClass.mk ε₀)
    (hv : IsHahnSum (fun k ↦ ρ ^ k / ((k.factorial : ℕ) : Surreal))
      ((1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀)))
    (hz : IsHahnSum (fun k ↦ ρ ^ k / ((k.factorial : ℕ) : Surreal)) z)
    (hbz : z.birthday < Ω * ((3 : ℕ) : NatOrdinal)) :
    z = (1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀) := by
  have hc : ∀ k, pairCoeff a b k ≠ 0 := pairCoeff_ne_zero ha hb hab
  set w := hahnSum (monoTerm_strict_dominating hc) with hwdef
  have hw : IsHahnSum (monoTerm (pairCoeff a b)) w := isHahnSum_hahnSum _
  -- `z` is at distance-class exactly `ω⁻³` from the padded canonical sum
  have hfull : monoS (pairCoeff a b) 3
      = (1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀) := monoS_pair_full a b
  have hdv : ArchimedeanClass.mk (monoS (pairCoeff a b) 3 - w)
      = ArchimedeanClass.mk (ε₀ ^ 3) := mk_monoS_sub hc hw 3
  have hv3 : ArchimedeanClass.mk (ε₀ ^ 3) <
      ArchimedeanClass.mk (z - (1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀)) :=
    ladder_strict hρmk hv hz 3
  have hsplit : z - w = (monoS (pairCoeff a b) 3 - w) +
      (z - (1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀)) := by
    rw [hfull]
    ring
  have hlt : ArchimedeanClass.mk (monoS (pairCoeff a b) 3 - w) <
      ArchimedeanClass.mk (z - (1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀)) := by
    rw [hdv]
    exact hv3
  have hzw : ArchimedeanClass.mk (z - w) = ArchimedeanClass.mk (ε₀ ^ 3) := by
    rw [hsplit, ArchimedeanClass.mk_add_eq_mk_left hlt, hdv]
  -- the tube census at block `1` puts `z` on the `ω⁻²`-grid
  have hdist : ArchimedeanClass.mk (ε₀ ^ 1) < ArchimedeanClass.mk (z - w) := by
    rw [hzw]
    exact mk_pow_one_lt_three
  obtain ⟨m, hm⟩ := lt_omega_mul_succ_decomp 2 hbz
  obtain ⟨t, hzeq⟩ := pair_tube_force hc hw m hdist hm
  -- sub-all-scales proximity pins the grid coefficient to `ab`
  have h2 := ladder_strict hρmk hv hz 2
  by_cases ht : t = a * b
  · rw [hzeq, ht, monoS_pair_grid]
  · exfalso
    have hval : z - (1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀)
        = ((t - a * b : Dyadic) : Surreal) * ε₀ ^ 2 := by
      rw [hzeq, ← monoS_pair_grid, dyadic_cast_sub']
      ring
    have hmk : ArchimedeanClass.mk
        (z - (1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀))
        = ArchimedeanClass.mk (ε₀ ^ 2) := by
      rw [hval, ArchimedeanClass.mk_mul,
        mk_dyadic_cast_ne_zero (sub_ne_zero.2 ht), zero_add]
    rw [hmk] at h2
    exact lt_irrefl _ h2

/-! ### The identification -/

/-- **The pair grid price**: the product is the level-`2` grid point of its own padded
series, so it is born by day `ω·2 + (hgt (ab) − 1)`. -/
theorem birthday_prod_le {a b : Dyadic} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    (((1 : Surreal.{0}) + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀)).birthday
      ≤ Ω * ((2 : ℕ) : NatOrdinal) + ((Dyadic.hgt (a * b) - 1 : ℕ) : NatOrdinal) := by
  have hc : ∀ k, pairCoeff a b k ≠ 0 := pairCoeff_ne_zero ha hb hab
  have h : (monoS (pairCoeff a b) 2 + ((a * b : Dyadic) : Surreal) * ε₀ ^ 2).birthday
      ≤ Ω * ((2 : ℕ) : NatOrdinal) + ((Dyadic.hgt (a * b) - 1 : ℕ) : NatOrdinal) :=
    birthday_monoS_add_dyadic_mul_le hc 1 (t := a * b) (mul_ne_zero ha hb)
  rwa [monoS_pair_grid] at h

/-- **The parametric pair identification**: for any argument `ρ` of class `ω⁻¹` for
which the product `(1+a·ω⁻¹)(1+b·ω⁻¹)` is a Hahn sum of the exponential series, the
canonical value *is* the product. -/
theorem expInf_eq_prod_of_isHahnSum {a b : Dyadic} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) {ρ : Surreal.{0}} (hρinf : Infinitesimal ρ) (hρ0 : ρ ≠ 0)
    (hρmk : ArchimedeanClass.mk ρ = ArchimedeanClass.mk ε₀)
    (hv : IsHahnSum (fun k ↦ ρ ^ k / ((k.factorial : ℕ) : Surreal))
      ((1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀))) :
    expInf ρ hρinf hρ0 = (1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀) := by
  unfold expInf
  rw [hahnSum_eq_iff]
  refine ⟨hv, fun z hz ↦ ?_⟩
  rcases lt_or_ge z.birthday (Ω * ((3 : ℕ) : NatOrdinal)) with hlt | hge
  · rw [eq_prod_of_isHahnSum_expSeries_of_birthday_lt ha hb hab hρmk hv hz hlt]
  · refine (birthday_prod_le ha hb hab).trans (le_trans ?_ hge)
    have h3 : Ω * ((3 : ℕ) : NatOrdinal) = Ω * ((2 : ℕ) : NatOrdinal) + Ω := by
      have hcast : ((3 : ℕ) : NatOrdinal) = ((2 : ℕ) : NatOrdinal) + 1 := by norm_num
      rw [hcast, mul_add, mul_one]
    rw [h3]
    exact add_le_add le_rfl (nat_lt_omega' _).le

/-! ### THE MIXED FUNCTIONAL EQUATION -/

/-- **THE MIXED FUNCTIONAL EQUATION**: for positive dyadics `a, b` and *any* Hahn sums
`σ, τ` of the logarithm series at `a·ω⁻¹` and `b·ω⁻¹`,
`expInf (σ + τ) = expInf σ · expInf τ` — exactly, both sides being
`(1+a·ω⁻¹)(1+b·ω⁻¹)`. A two-parameter family of exact functional-equation instances,
fibre-general in both logarithms. -/
theorem expInf_add_eq_mul_of_isHahnSum_logs {a b : Dyadic} (ha : 0 < a) (hb : 0 < b)
    {σ τ : Surreal.{0}} (hσinf : Infinitesimal σ) (hτinf : Infinitesimal τ)
    (hσpos : 0 < σ) (hτpos : 0 < τ)
    (hσ : IsHahnSum (logSeriesAt ((a : Surreal) * ε₀)) σ)
    (hτ : IsHahnSum (logSeriesAt ((b : Surreal) * ε₀)) τ) :
    expInf (σ + τ) (hσinf.add hτinf) (add_pos hσpos hτpos).ne' =
      expInf σ hσinf hσpos.ne' * expInf τ hτinf hτpos.ne' := by
  have hxa : Infinitesimal ((a : Surreal.{0}) * ε₀) := dyadic_mul_eps0_infinitesimal a
  have hxb : Infinitesimal ((b : Surreal.{0}) * ε₀) := dyadic_mul_eps0_infinitesimal b
  have hxa0 : (a : Surreal.{0}) * ε₀ ≠ 0 :=
    (mul_pos (dyadic_cast_pos ha) eps0_pos').ne'
  have hxb0 : (b : Surreal.{0}) * ε₀ ≠ 0 :=
    (mul_pos (dyadic_cast_pos hb) eps0_pos').ne'
  -- the exact values of the factors
  have hσval : expInf σ hσinf hσpos.ne' = 1 + (a : Surreal) * ε₀ :=
    expInf_eq_one_add_of_isHahnSum_log ha.ne' hσinf hσpos.ne' hσ
  have hτval : expInf τ hτinf hτpos.ne' = 1 + (b : Surreal) * ε₀ :=
    expInf_eq_one_add_of_isHahnSum_log hb.ne' hτinf hτpos.ne' hτ
  -- the Cauchy product supplies the Hahn-sum half at `σ + τ`
  have hmul := isHahnSum_expInf_mul hσinf hτinf hσpos hτpos
  rw [hσval, hτval] at hmul
  -- the class of `σ + τ`
  have hσmk : ArchimedeanClass.mk σ = ArchimedeanClass.mk ε₀ := by
    rw [mk_of_isHahnSum_log hxa hxa0 hσ, ArchimedeanClass.mk_mul,
      mk_dyadic_cast_ne_zero ha.ne', zero_add]
  have hτmk : ArchimedeanClass.mk τ = ArchimedeanClass.mk ε₀ := by
    rw [mk_of_isHahnSum_log hxb hxb0 hτ, ArchimedeanClass.mk_mul,
      mk_dyadic_cast_ne_zero hb.ne', zero_add]
  have hρmk : ArchimedeanClass.mk (σ + τ) = ArchimedeanClass.mk ε₀ := by
    refine le_antisymm ?_ ?_
    · calc ArchimedeanClass.mk (σ + τ)
          ≤ ArchimedeanClass.mk σ :=
            ArchimedeanClass.mk_antitoneOn (Set.mem_Ici.2 hσpos.le)
              (Set.mem_Ici.2 (add_pos hσpos hτpos).le) (by linarith)
        _ = ArchimedeanClass.mk ε₀ := hσmk
    · exact le_trans (le_min (le_of_eq hσmk.symm) (le_of_eq hτmk.symm))
        (ArchimedeanClass.min_le_mk_add ..)
  -- close by the parametric pair identification
  have h := expInf_eq_prod_of_isHahnSum ha.ne' hb.ne' (add_pos ha hb).ne'
    (hσinf.add hτinf) (add_pos hσpos hτpos).ne' hρmk hmul
  rw [h, hσval, hτval]

/-! ### The canonical instances -/

theorem logGrid_pos {a : Dyadic} (ha : 0 < a) : 0 < logGrid a ha.ne' :=
  pos_of_isHahnSum_log (dyadic_mul_eps0_infinitesimal a)
    (mul_pos (dyadic_cast_pos ha) eps0_pos') (isHahnSum_logGrid a ha.ne')

/-- **The canonical mixed instance**:
`exp (log (1+a·ω⁻¹) + log (1+b·ω⁻¹)) = exp (log (1+a·ω⁻¹)) · exp (log (1+b·ω⁻¹))`. -/
theorem expInf_logGrid_add_eq_mul {a b : Dyadic} (ha : 0 < a) (hb : 0 < b) :
    expInf (logGrid a ha.ne' + logGrid b hb.ne')
        ((logGrid_infinitesimal a ha.ne').add (logGrid_infinitesimal b hb.ne'))
        (add_pos (logGrid_pos ha) (logGrid_pos hb)).ne' =
      expInf (logGrid a ha.ne') (logGrid_infinitesimal a ha.ne')
          (logGrid_ne_zero a ha.ne') *
        expInf (logGrid b hb.ne') (logGrid_infinitesimal b hb.ne')
          (logGrid_ne_zero b hb.ne') :=
  expInf_add_eq_mul_of_isHahnSum_logs ha hb
    (logGrid_infinitesimal a ha.ne') (logGrid_infinitesimal b hb.ne')
    (logGrid_pos ha) (logGrid_pos hb)
    (isHahnSum_logGrid a ha.ne') (isHahnSum_logGrid b hb.ne')

/-- The value form: `exp (log (1+a·ω⁻¹) + log (1+b·ω⁻¹)) = (1+a·ω⁻¹)·(1+b·ω⁻¹)`. -/
theorem expInf_logGrid_add_eq {a b : Dyadic} (ha : 0 < a) (hb : 0 < b) :
    expInf (logGrid a ha.ne' + logGrid b hb.ne')
        ((logGrid_infinitesimal a ha.ne').add (logGrid_infinitesimal b hb.ne'))
        (add_pos (logGrid_pos ha) (logGrid_pos hb)).ne' =
      (1 + (a : Surreal) * ε₀) * (1 + (b : Surreal) * ε₀) := by
  rw [expInf_logGrid_add_eq_mul ha hb, expInf_logGrid_eq a ha.ne',
    expInf_logGrid_eq b hb.ne']

end Surreal

end
