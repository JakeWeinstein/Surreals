import Infinity.Exp

/-!
# The canonical transfinite sum, and the exponential as a function

The Transfinite Summation Theorem (`Infinity.Summation`) produces *a* Hahn sum for every
strictly dominating series, unique only modulo domination by every term. This file solves
the canonicity problem: among all Hahn sums of a series there is a distinguished one — the
**birthday-simplest** — and it is definable, because the set of Hahn sums is exactly the
set of surreals fitting between two explicit cuts:

* `bandLo`/`bandHi` : the cut-valued edges of the `n`-th domination band
  `{z | z − sₙ = O(tₙ)}`;
* `sumLo := ⨆ₙ bandLo`, `sumHi := ⨅ₙ bandHi` : by the `Cut` lattice laws, a surreal fits
  between them **iff** it is a Hahn sum (`fits_iff_isHahnSum`);
* `hahnSum := Cut.simplestBtwn` : **the canonical transfinite sum** — a genuine function of
  the series — with `isHahnSum_hahnSum` (it sums) and `birthday_hahnSum_le` (it is the
  birthday-minimal sum).

As the payoff, the exponential becomes an honest **function** on nonzero infinitesimals:

* `expInf ε := hahnSum (exponential series at ε)`, with `isHahnSum_expInf`,
  minimality, and `stdPart_expInf : st (expInf ε) = 1` — indeed
  `expInf ε = 1 + ε + O(ε²)` (`mk_expInf_sub_one_sub`).

This resolves the canonical-sum problem posed in `docs/HANDOFF.md` — with no sign-expansion
machinery at all: the library's `simplestBtwn` on cuts was the right tool.
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

variable {t : ℕ → Surreal}

/-! ### The domination bands as cut intervals -/

/-- The cut at the lower edge of the `n`-th domination band `{z | z − sₙ = O(tₙ)}`. -/
def bandLo (t : ℕ → Surreal) (n : ℕ) : Cut :=
  ⨅ k : ℕ, Cut.rightSurreal (partialSum t n - (k + 1) • |t n|)

/-- The cut at the upper edge of the `n`-th domination band. -/
def bandHi (t : ℕ → Surreal) (n : ℕ) : Cut :=
  ⨆ k : ℕ, Cut.leftSurreal (partialSum t n + (k + 1) • |t n|)

/-- The cut just below the set of all Hahn sums. -/
def sumLo (t : ℕ → Surreal) : Cut := ⨆ n, bandLo t n

/-- The cut just above the set of all Hahn sums. -/
def sumHi (t : ℕ → Surreal) : Cut := ⨅ n, bandHi t n

/-- Membership in the `n`-th band, unfolded to inequalities. -/
private theorem band_iff {z : Surreal} {n : ℕ} (h0 : t n ≠ 0) :
    ((∃ k : ℕ, partialSum t n - (k + 1) • |t n| < z) ∧
      (∃ k : ℕ, z < partialSum t n + (k + 1) • |t n|)) ↔
    ArchimedeanClass.mk (t n) ≤ ArchimedeanClass.mk (z - partialSum t n) := by
  rw [ArchimedeanClass.mk_le_mk]
  constructor
  · rintro ⟨⟨k₁, h1⟩, ⟨k₂, h2⟩⟩
    refine ⟨max k₁ k₂ + 1, ?_⟩
    have hm1 : (k₁ + 1) • |t n| ≤ (max k₁ k₂ + 1) • |t n| :=
      nsmul_le_nsmul_left (abs_nonneg _) (by omega)
    have hm2 : (k₂ + 1) • |t n| ≤ (max k₁ k₂ + 1) • |t n| :=
      nsmul_le_nsmul_left (abs_nonneg _) (by omega)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · rintro ⟨k, hk⟩
    have hpos : (0 : Surreal) < |t n| := abs_pos.2 h0
    have hlt : |z - partialSum t n| < (k + 1) • |t n| := by
      refine hk.trans_lt ?_
      rw [succ_nsmul]
      linarith
    rw [abs_sub_lt_iff] at hlt
    exact ⟨⟨k, by linarith [hlt.2]⟩, ⟨k, by linarith [hlt.1]⟩⟩

/-- **The characterization**: a surreal fits between the cuts `sumLo` and `sumHi` iff it is
a Hahn sum of the series. The lattice laws for `Cut` turn the intersection of all domination
bands into a single cut interval. -/
theorem fits_iff_isHahnSum (ht0 : ∀ n, t n ≠ 0) {z : Surreal} :
    Cut.Fits z (sumLo t) (sumHi t) ↔ IsHahnSum t z := by
  rw [Cut.Fits, Set.mem_inter_iff, ← Cut.notMem_left_iff]
  unfold sumLo sumHi bandLo bandHi
  simp only [Cut.left_iSup, Cut.left_iInf, Cut.left_rightSurreal, Cut.left_leftSurreal,
    Set.mem_iUnion, Set.mem_iInter, Set.mem_Iic, Set.mem_Iio, not_exists, not_forall, not_le]
  constructor
  · rintro ⟨h1, h2⟩ n
    exact (band_iff (ht0 n)).1 ⟨h1 n, h2 n⟩
  · intro h
    exact ⟨fun n ↦ ((band_iff (ht0 n)).2 (h n)).1, fun n ↦ ((band_iff (ht0 n)).2 (h n)).2⟩

/-- The cut interval of Hahn sums is nonempty (by the Transfinite Summation Theorem). -/
theorem sumLo_lt_sumHi (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    sumLo t < sumHi t := by
  obtain ⟨z, hz⟩ := exists_isHahnSum ht
  exact ((fits_iff_isHahnSum (ne_zero_of_strict_dominating ht)).2 hz).lt

/-! ### The canonical sum -/

/-- **The canonical transfinite sum** of a strictly dominating series: the birthday-simplest
surreal fitting between the cuts that bound all Hahn sums. -/
def hahnSum (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    Surreal :=
  Cut.simplestBtwn (sumLo_lt_sumHi ht)

/-- The canonical sum is a Hahn sum. -/
theorem isHahnSum_hahnSum
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    IsHahnSum t (hahnSum ht) :=
  (fits_iff_isHahnSum (ne_zero_of_strict_dominating ht)).1 (Cut.fits_simplestBtwn _)

/-- **Canonicity**: the canonical sum is the birthday-minimal Hahn sum. -/
theorem birthday_hahnSum_le
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    {z : Surreal} (hz : IsHahnSum t z) :
    (hahnSum ht).birthday ≤ z.birthday :=
  Cut.birthday_simplestBtwn_le_of_fits
    ((fits_iff_isHahnSum (ne_zero_of_strict_dominating ht)).2 hz)

/-! ### The exponential as a function -/

/-- **The exponential on nonzero infinitesimals, as an honest function**: the canonical
(birthday-simplest) transfinite sum of the exponential series `Σ εᵏ/k!`. -/
def expInf (ε : Surreal) (hε : Infinitesimal ε) (hε0 : ε ≠ 0) : Surreal :=
  hahnSum (expSeries_strict_dominating hε hε0)

theorem isHahnSum_expInf {ε : Surreal} (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    IsHahnSum (fun k ↦ ε ^ k / ((k.factorial : ℕ) : Surreal)) (expInf ε hε hε0) :=
  isHahnSum_hahnSum _

/-- The canonical exponential value is the birthday-minimal one. -/
theorem birthday_expInf_le {ε : Surreal} (hε : Infinitesimal ε) (hε0 : ε ≠ 0) {z : Surreal}
    (hz : IsHahnSum (fun k ↦ ε ^ k / ((k.factorial : ℕ) : Surreal)) z) :
    (expInf ε hε hε0).birthday ≤ z.birthday :=
  birthday_hahnSum_le _ hz

private theorem expSeries_apply_zero (ε : Surreal) :
    ε ^ 0 / (((0 : ℕ).factorial : ℕ) : Surreal) = 1 := by
  norm_num

private theorem expSeries_apply_one (ε : Surreal) :
    ε ^ 1 / (((1 : ℕ).factorial : ℕ) : Surreal) = ε := by
  norm_num

/-- `expInf ε = 1 + ε + O(ε²)`: the residual beyond the linear truncation is dominated by
`ε²`. -/
theorem mk_expInf_sub_one_sub {ε : Surreal} (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    ArchimedeanClass.mk (ε ^ 2) ≤
      ArchimedeanClass.mk (expInf ε hε hε0 - (1 + ε)) := by
  have h := isHahnSum_expInf hε hε0 2
  have hps : partialSum (fun k ↦ ε ^ k / ((k.factorial : ℕ) : Surreal)) 2 = 1 + ε := by
    rw [partialSum, Finset.sum_range_succ, Finset.sum_range_one,
      expSeries_apply_zero, expSeries_apply_one]
  rw [hps] at h
  refine le_trans (le_of_eq ?_) h
  rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero]

/-- The residual beyond the constant term is infinitesimal, hence
**`st (expInf ε) = 1`**: the exponential of an infinitesimal is infinitesimally close
to `1`, as it should be. -/
theorem stdPart_expInf {ε : Surreal} (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    stdPart (expInf ε hε hε0) = 1 := by
  have h := isHahnSum_expInf hε hε0 1
  have hps : partialSum (fun k ↦ ε ^ k / ((k.factorial : ℕ) : Surreal)) 1 = 1 := by
    rw [partialSum, Finset.sum_range_one, expSeries_apply_zero]
  rw [hps] at h
  have ht1 : ArchimedeanClass.mk (ε ^ 1 / (((1 : ℕ).factorial : ℕ) : Surreal)) =
      ArchimedeanClass.mk ε := by
    rw [expSeries_apply_one]
  rw [ht1] at h
  have hres : Infinitesimal (expInf ε hε hε0 - 1) := lt_of_lt_of_le hε h
  have hsplit : expInf ε hε hε0 = 1 + (expInf ε hε hε0 - 1) := by ring
  rw [hsplit, stdPart_add_eq_left hres, ArchimedeanClass.stdPart_one]

end Surreal
