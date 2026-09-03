/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.GameCofinality
import Infinity.HaloGame
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Scale evaluation: formal power series at a positive infinitesimal, as a ring homomorphism

The canonical sum of `Infinity.CanonicalSum` needs a *strictly dominating* series — every term
strictly finer than its predecessor — so it cannot evaluate a formal power series with a zero
coefficient, and its multiplicativity (`Infinity.GameCofinality`) needs a cofinality side
condition. This file removes both restrictions by letting the option game see the *scale*
`εᴺ` rather than the terms.

* **Scale sums** `Surreal.IsScaleSum ε f z` for `f : PowerSeries ℝ` and a scale `ε`: every
  residual `z − ∑_{k<N} fₖ εᵏ` is at least as fine as `εᴺ`. Zero coefficients are harmless:
  `IsScaleSum` is about the scale, not the terms.
* **The scale game** `Surreal.scaleGame ε f := !{Uₙ − (|fₙ| + 1) εⁿ ∣ Uₙ + (|fₙ| + 1) εⁿ}`
  (`Uₙ` the partial sums) and its value `Surreal.scaleEval ε f`. A numeric game fits the scale
  game iff its value is a scale sum (`fits_scaleGame_iff`: the next-index estimate
  `abs_sub_scalePartial_lt`), so by the simplicity theorem `scaleEval ε f` is **the
  birthday-simplest scale sum** (`scaleEval_eq_iff`), and the identification engine
  `mk_eq_scaleEval_of_moves_le` is one application of `IGame.Fits.equiv_of_forall_moves`.
* **THE SCALE EVALUATION RING HOMOMORPHISM** `Surreal.scaleEvalHom ε : PowerSeries ℝ →+* Surreal`
  for every positive infinitesimal `ε`, with **no side conditions**: `scaleEval_add`
  (the sum game), `scaleEval_mul` (the product game — the option computation of
  `Surreal.hahnSum_eq_mul_of_cofinal`, with the cofinality now automatic because each option
  sits at distance of class `mk (ε^(m+n))` from the product, beyond the `(m+n+1)`-st scale
  option), `scaleEval_one`, `scaleEval_zero`, `scaleEval_neg`, `scaleEval_sub`,
  `scaleEval_pow`, `scaleEval_C_mul`.
* **Polynomials are halo values**: `scaleEval_coe`
  (`scaleEval ε p = haloValue ε (p(ε))` for `p : Polynomial ℝ`), hence `scaleEval_C`
  (`scaleEval ε (C r) = r`, reals being halo-simple), `scaleEval_X`
  (`scaleEval ε X = haloValue ε ε`, `= ε` when `ε` is halo-simple), `scaleEval_C_add_C_mul_X`.
* **Compatibility with the canonical sum** `scaleEval_eq_hahnSum`: when every coefficient is
  nonzero, `scaleEval ε f` is the canonical sum of the strictly dominating series `fₖ εᵏ`.
* **The exponential** `expInf_eq_scaleEval_exp`: `expInf σ = scaleEval σ (PowerSeries.exp ℝ)`
  for every positive infinitesimal `σ`; more generally `scaleEval_rescale_exp`:
  `scaleEval σ (rescale r (exp ℝ)) = expInf (r σ)` for every nonzero real `r` (of either
  sign). Corollaries: the reflection law `expInf σ · expInf (−σ) = 1` from mathlib's
  `PowerSeries.exp_mul_exp_neg_eq_one` (`expInf_mul_expInf_neg'`), and — new — **the signed
  functional equation along every scale line** `expInf_realCast_mul_add`:
  `expInf (r σ) · expInf (s σ) = expInf ((r + s) σ)` for all nonzero reals `r, s` with
  `r + s ≠ 0`, from `PowerSeries.exp_mul_exp_eq_exp_add`. Mixed signs and irrational ratios
  are covered; none of the census or cofinality arguments reach them.

Canonical-sum semantics *is* formal-power-series semantics at every scale: this is the
bridge from the calculus on `No` to mathlib's `PowerSeries` (exp, log, substitution), and
the `ω`-length base case of normal-form evaluation.
-/

open ArchimedeanClass Finset IGame

universe u

noncomputable section

namespace Surreal

/-! ### Scale terms, partial sums, scale sums -/

/-- The `k`-th term `fₖ · εᵏ` of a real power series at scale `ε`. -/
def scaleTerm (ε : Surreal.{u}) (f : PowerSeries ℝ) (k : ℕ) : Surreal.{u} :=
  ((PowerSeries.coeff k f : ℝ) : Surreal) * ε ^ k

/-- The partial sum `Uₙ = ∑_{k<N} fₖ εᵏ`. -/
def scalePartial (ε : Surreal.{u}) (f : PowerSeries ℝ) (N : ℕ) : Surreal.{u} :=
  partialSum (scaleTerm ε f) N

theorem scalePartial_zero (ε : Surreal.{u}) (f : PowerSeries ℝ) : scalePartial ε f 0 = 0 :=
  partialSum_zero _

theorem scalePartial_succ (ε : Surreal.{u}) (f : PowerSeries ℝ) (N : ℕ) :
    scalePartial ε f (N + 1) = scalePartial ε f N + scaleTerm ε f N :=
  partialSum_succ _ _

/-- `z` is a **scale sum** of `f` at scale `ε`: every residual `z − Uₙ` is at least as fine as
`εᴺ`. Zero coefficients are allowed (if `fₙ = 0` then `z − Uₙ = z − Uₙ₊₁`). -/
def IsScaleSum (ε : Surreal.{u}) (f : PowerSeries ℝ) (z : Surreal.{u}) : Prop :=
  ∀ N : ℕ, ArchimedeanClass.mk (ε ^ N) ≤ ArchimedeanClass.mk (z - scalePartial ε f N)

/-- The option constant `|fₙ| + 1`. -/
def scaleConst (f : PowerSeries ℝ) (N : ℕ) : Surreal.{u} :=
  |((PowerSeries.coeff N f : ℝ) : Surreal)| + 1

theorem scaleConst_pos (f : PowerSeries ℝ) (N : ℕ) : (0 : Surreal.{u}) < scaleConst f N := by
  unfold scaleConst
  positivity

theorem isFinite_scaleConst (f : PowerSeries ℝ) (N : ℕ) : IsFinite (scaleConst.{u} f N) := by
  unfold scaleConst
  refine IsFinite.add ?_ isFinite_one
  show 0 ≤ ArchimedeanClass.mk |((PowerSeries.coeff N f : ℝ) : Surreal.{u})|
  rw [ArchimedeanClass.mk_abs]
  exact isFinite_realCast _

/-! ### Class bookkeeping at the scale -/

/-- Powers of a finite surreal are (weakly) increasingly fine. -/
theorem mk_pow_le_mk_pow_of_le {ε : Surreal.{u}} (hε : IsFinite ε) {M N : ℕ} (h : M ≤ N) :
    ArchimedeanClass.mk (ε ^ M) ≤ ArchimedeanClass.mk (ε ^ N) := by
  rw [ArchimedeanClass.mk_pow, ArchimedeanClass.mk_pow]
  exact nsmul_le_nsmul_left hε h

theorem mk_pow_le_mk_scaleTerm {ε : Surreal.{u}} (hε : IsFinite ε) (f : PowerSeries ℝ)
    {M N : ℕ} (h : M ≤ N) :
    ArchimedeanClass.mk (ε ^ M) ≤ ArchimedeanClass.mk (scaleTerm ε f N) := by
  unfold scaleTerm
  rw [ArchimedeanClass.mk_mul]
  calc ArchimedeanClass.mk (ε ^ M) = 0 + ArchimedeanClass.mk (ε ^ M) := (zero_add _).symm
    _ ≤ _ := add_le_add (isFinite_realCast _) (mk_pow_le_mk_pow_of_le hε h)

/-- The tail `U_N − U_M` (`M ≤ N`) is at least as fine as `εᴹ`. -/
theorem mk_pow_le_mk_scalePartial_sub {ε : Surreal.{u}} (hε : IsFinite ε) (f : PowerSeries ℝ)
    {M N : ℕ} (h : M ≤ N) :
    ArchimedeanClass.mk (ε ^ M) ≤
      ArchimedeanClass.mk (scalePartial ε f N - scalePartial ε f M) := by
  induction N, h using Nat.le_induction with
  | base =>
    rw [sub_self, ArchimedeanClass.mk_zero]
    exact le_top
  | succ N hMN ih =>
    rw [scalePartial_succ, add_sub_right_comm]
    exact le_trans (le_min ih (mk_pow_le_mk_scaleTerm hε f hMN))
      (ArchimedeanClass.min_le_mk_add _ _)

theorem isFinite_scaleTerm {ε : Surreal.{u}} (hε : IsFinite ε) (f : PowerSeries ℝ) (k : ℕ) :
    IsFinite (scaleTerm ε f k) :=
  (isFinite_realCast _).mul (hε.pow k)

theorem isFinite_scalePartial {ε : Surreal.{u}} (hε : IsFinite ε) (f : PowerSeries ℝ) (N : ℕ) :
    IsFinite (scalePartial ε f N) := by
  induction N with
  | zero =>
    rw [scalePartial_zero]
    exact isFinite_zero
  | succ N ih =>
    rw [scalePartial_succ]
    exact ih.add (isFinite_scaleTerm hε f N)

theorem mk_pow_le_mk_scaleConst_mul_pow (ε : Surreal.{u}) (f : PowerSeries ℝ) (N : ℕ) :
    ArchimedeanClass.mk (ε ^ N) ≤ ArchimedeanClass.mk (scaleConst f N * ε ^ N) := by
  rw [ArchimedeanClass.mk_mul]
  calc ArchimedeanClass.mk (ε ^ N) = 0 + ArchimedeanClass.mk (ε ^ N) := (zero_add _).symm
    _ ≤ _ := add_le_add (isFinite_scaleConst f N) le_rfl

/-- A scale sum is finite (the `N = 0` instance). -/
theorem IsScaleSum.isFinite {ε : Surreal.{u}} {f : PowerSeries ℝ} {z : Surreal.{u}}
    (hz : IsScaleSum ε f z) : IsFinite z := by
  have h := hz 0
  rwa [pow_zero, ArchimedeanClass.mk_one, scalePartial_zero, sub_zero] at h

/-! ### The next-index estimate -/

/-- **The next-index estimate**: if the residual at index `N + 1` is at least as fine as
`εᴺ⁺¹`, then `|z − Uₙ| < (|fₙ| + 1) εᴺ`, because `z − Uₙ = fₙ εᴺ + (z − Uₙ₊₁)` and
`|z − Uₙ₊₁| < εᴺ`. -/
theorem abs_sub_scalePartial_lt {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (f : PowerSeries ℝ) {z : Surreal.{u}} {N : ℕ}
    (hz : ArchimedeanClass.mk (ε ^ (N + 1)) ≤
      ArchimedeanClass.mk (z - scalePartial ε f (N + 1))) :
    |z - scalePartial ε f N| < scaleConst f N * ε ^ N := by
  have h1 : ArchimedeanClass.mk (ε ^ N) <
      ArchimedeanClass.mk (z - scalePartial ε f (N + 1)) :=
    (mk_pow_lt_mk_pow_succ hε hε0 N).trans_le hz
  have h2 := abs_lt_abs_of_mk_lt h1
  rw [abs_of_pos (pow_pos hε0 N)] at h2
  have hs : z - scalePartial ε f N =
      ((PowerSeries.coeff N f : ℝ) : Surreal) * ε ^ N + (z - scalePartial ε f (N + 1)) := by
    rw [scalePartial_succ, scaleTerm]; ring
  rw [hs]
  unfold scaleConst
  have h3 := abs_lt.1 h2
  have hpos := (pow_pos hε0 N).le
  have h5 := mul_le_mul_of_nonneg_right (neg_abs_le ((PowerSeries.coeff N f : ℝ) : Surreal)) hpos
  have h6 := mul_le_mul_of_nonneg_right (le_abs_self ((PowerSeries.coeff N f : ℝ) : Surreal)) hpos
  exact abs_lt.2 ⟨by linarith [h3.1], by linarith [h3.2]⟩

/-! ### The options -/

/-- The lower option `Uₙ − (|fₙ| + 1) εᴺ`. -/
def scaleOptLo (ε : Surreal.{u}) (f : PowerSeries ℝ) (N : ℕ) : Surreal.{u} :=
  scalePartial ε f N - scaleConst f N * ε ^ N

/-- The upper option `Uₙ + (|fₙ| + 1) εᴺ`. -/
def scaleOptHi (ε : Surreal.{u}) (f : PowerSeries ℝ) (N : ℕ) : Surreal.{u} :=
  scalePartial ε f N + scaleConst f N * ε ^ N

theorem scaleOptLo_lt_of_mk_le {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (f : PowerSeries ℝ) {z : Surreal.{u}} {N : ℕ}
    (hz : ArchimedeanClass.mk (ε ^ (N + 1)) ≤
      ArchimedeanClass.mk (z - scalePartial ε f (N + 1))) :
    scaleOptLo ε f N < z := by
  have h := (abs_lt.1 (abs_sub_scalePartial_lt hε hε0 f hz)).1
  unfold scaleOptLo
  linarith

theorem lt_scaleOptHi_of_mk_le {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (f : PowerSeries ℝ) {z : Surreal.{u}} {N : ℕ}
    (hz : ArchimedeanClass.mk (ε ^ (N + 1)) ≤
      ArchimedeanClass.mk (z - scalePartial ε f (N + 1))) :
    z < scaleOptHi ε f N := by
  have h := (abs_lt.1 (abs_sub_scalePartial_lt hε hε0 f hz)).2
  unfold scaleOptHi
  linarith

theorem scaleOptLo_lt_of_isScaleSum {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {z : Surreal.{u}} (hz : IsScaleSum ε f z) (N : ℕ) :
    scaleOptLo ε f N < z :=
  scaleOptLo_lt_of_mk_le hε hε0 f (hz (N + 1))

theorem lt_scaleOptHi_of_isScaleSum {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {z : Surreal.{u}} (hz : IsScaleSum ε f z) (N : ℕ) :
    z < scaleOptHi ε f N :=
  lt_scaleOptHi_of_mk_le hε hε0 f (hz (N + 1))

/-- Conversely, anything strictly between all the options is a scale sum. -/
theorem isScaleSum_of_forall_opt {ε : Surreal.{u}} {f : PowerSeries ℝ} {z : Surreal.{u}}
    (h : ∀ N, scaleOptLo ε f N < z ∧ z < scaleOptHi ε f N) : IsScaleSum ε f z := by
  intro N
  obtain ⟨h1, h2⟩ := h N
  unfold scaleOptLo at h1
  unfold scaleOptHi at h2
  refine (mk_pow_le_mk_scaleConst_mul_pow ε f N).trans (ArchimedeanClass.mk_le_mk_of_abs ?_)
  exact le_trans (abs_le.2 ⟨by linarith, by linarith⟩) (le_abs_self _)

/-- The two option sets are separated: both lie on either side of a late partial sum. -/
theorem scaleOptLo_lt_scaleOptHi {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (f : PowerSeries ℝ) (m n : ℕ) : scaleOptLo ε f m < scaleOptHi ε f n := by
  have hfin := hε.isFinite
  have hm : m + 1 ≤ max m n + 1 := by have := le_max_left m n; omega
  have hn : n + 1 ≤ max m n + 1 := by have := le_max_right m n; omega
  exact (scaleOptLo_lt_of_mk_le hε hε0 f (mk_pow_le_mk_scalePartial_sub hfin f hm)).trans
    (lt_scaleOptHi_of_mk_le hε hε0 f (mk_pow_le_mk_scalePartial_sub hfin f hn))

/-! ### The scale game -/

/-- **The scale game** `!{Uₙ − (|fₙ| + 1) εⁿ ∣ Uₙ + (|fₙ| + 1) εⁿ}`. -/
def scaleGame (ε : Surreal.{u}) (f : PowerSeries ℝ) : IGame.{u} :=
  !{Set.range (fun N ↦ (scaleOptLo ε f N).out) | Set.range (fun N ↦ (scaleOptHi ε f N).out)}

theorem leftMoves_scaleGame (ε : Surreal.{u}) (f : PowerSeries ℝ) :
    (scaleGame ε f)ᴸ = Set.range (fun N ↦ (scaleOptLo ε f N).out) :=
  leftMoves_ofSets ..

theorem rightMoves_scaleGame (ε : Surreal.{u}) (f : PowerSeries ℝ) :
    (scaleGame ε f)ᴿ = Set.range (fun N ↦ (scaleOptHi ε f N).out) :=
  rightMoves_ofSets ..

theorem scaleOptLo_out_mem_leftMoves_scaleGame (ε : Surreal.{u}) (f : PowerSeries ℝ) (N : ℕ) :
    (scaleOptLo ε f N).out ∈ (scaleGame ε f)ᴸ := by
  rw [leftMoves_scaleGame]
  exact ⟨N, rfl⟩

theorem scaleOptHi_out_mem_rightMoves_scaleGame (ε : Surreal.{u}) (f : PowerSeries ℝ) (N : ℕ) :
    (scaleOptHi ε f N).out ∈ (scaleGame ε f)ᴿ := by
  rw [rightMoves_scaleGame]
  exact ⟨N, rfl⟩

/-- The scale game at a positive infinitesimal scale is numeric. -/
theorem numeric_scaleGame {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (f : PowerSeries ℝ) : (scaleGame ε f).Numeric := by
  refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
  · rw [leftMoves_scaleGame] at hy
    rw [rightMoves_scaleGame] at hz
    obtain ⟨m, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := hz
    rw [← Surreal.mk_lt_mk, out_eq, out_eq]
    exact scaleOptLo_lt_scaleOptHi hε hε0 f m n
  · cases p with
    | left =>
      rw [scaleGame, moves_ofSets] at hy
      obtain ⟨n, rfl⟩ := hy
      infer_instance
    | right =>
      rw [scaleGame, moves_ofSets] at hy
      obtain ⟨n, rfl⟩ := hy
      infer_instance

/-- **A numeric game fits the scale game iff its value is a scale sum.** -/
theorem fits_scaleGame_iff {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {x : IGame.{u}} [x.Numeric] :
    x.Fits (scaleGame ε f) ↔ IsScaleSum ε f (Surreal.mk x) := by
  constructor
  · intro hx
    refine isScaleSum_of_forall_opt fun N ↦ ?_
    have h1 := hx.1 _ (scaleOptLo_out_mem_leftMoves_scaleGame ε f N)
    have h2 := hx.2 _ (scaleOptHi_out_mem_rightMoves_scaleGame ε f N)
    rw [IGame.Numeric.not_le, ← Surreal.mk_lt_mk, out_eq] at h1
    rw [IGame.Numeric.not_le, ← Surreal.mk_lt_mk, out_eq] at h2
    exact ⟨h1, h2⟩
  · intro hx
    constructor
    · intro z hz
      rw [leftMoves_scaleGame] at hz
      obtain ⟨N, rfl⟩ := hz
      refine IGame.Numeric.not_le.2 ?_
      rw [← Surreal.mk_lt_mk, out_eq]
      exact scaleOptLo_lt_of_isScaleSum hε hε0 hx N
    · intro z hz
      rw [rightMoves_scaleGame] at hz
      obtain ⟨N, rfl⟩ := hz
      refine IGame.Numeric.not_le.2 ?_
      rw [← Surreal.mk_lt_mk, out_eq]
      exact lt_scaleOptHi_of_isScaleSum hε hε0 hx N

/-! ### The scale evaluation: the simplest scale sum -/

/-- **The scale evaluation** of `f : PowerSeries ℝ` at the positive infinitesimal `ε`: the value
of the scale game. -/
def scaleEval (ε : Surreal.{u}) (f : PowerSeries ℝ) (hε : Infinitesimal ε) (hε0 : 0 < ε) :
    Surreal.{u} :=
  @Surreal.mk (scaleGame ε f) (numeric_scaleGame hε hε0 f)

theorem mk_scaleGame {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) (f : PowerSeries ℝ)
    [(scaleGame ε f).Numeric] : Surreal.mk (scaleGame ε f) = scaleEval ε f hε hε0 :=
  rfl

/-- The scale evaluation is a scale sum. -/
theorem isScaleSum_scaleEval {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (f : PowerSeries ℝ) : IsScaleSum ε f (scaleEval ε f hε hε0) := by
  haveI := numeric_scaleGame hε hε0 f
  exact (fits_scaleGame_iff hε hε0).1 (Fits.refl _)

/-- The scale evaluation is born no later than any scale sum (the simplicity theorem, value
form). -/
theorem birthday_scaleEval_le {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {z : Surreal.{u}} (hz : IsScaleSum ε f z) :
    (scaleEval ε f hε hε0).birthday ≤ z.birthday := by
  haveI := numeric_scaleGame hε hε0 f
  refine birthday_mk_le_of_fits ?_
  rw [fits_scaleGame_iff hε hε0, out_eq]
  exact hz

/-- **The characterization of the scale evaluation**: it is the unique scale sum of minimal
birthday. -/
theorem scaleEval_eq_iff {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {z : Surreal.{u}} :
    scaleEval ε f hε hε0 = z ↔
      IsScaleSum ε f z ∧ ∀ w, IsScaleSum ε f w → z.birthday ≤ w.birthday := by
  haveI := numeric_scaleGame hε hε0 f
  constructor
  · rintro rfl
    exact ⟨isScaleSum_scaleEval hε hε0 f, fun w hw ↦ birthday_scaleEval_le hε hε0 hw⟩
  · rintro ⟨hz, hmin⟩
    obtain ⟨g, hgn, hgq, hgb⟩ := birthday_eq_iGameBirthday z
    haveI := hgn
    have hfit : g.Fits (scaleGame ε f) := by
      rw [fits_scaleGame_iff hε hε0, hgq]
      exact hz
    have hequiv : g ≈ scaleGame ε f := by
      refine hfit.equiv_of_forall_birthday_le fun y hyn hy ↦ ?_
      haveI := hyn
      rw [hgb]
      exact (hmin _ ((fits_scaleGame_iff hε hε0).1 hy)).trans (birthday_mk_le y)
    rw [scaleEval, ← hgq]
    exact (Surreal.mk_eq_mk.2 hequiv).symm

/-- The scale evaluation respects propositional equality of the series. -/
theorem scaleEval_congr {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f g : PowerSeries ℝ} (h : f = g) : scaleEval ε f hε hε0 = scaleEval ε g hε hε0 := by
  subst h; rfl

/-! ### The identification engine -/

/-- **The scale identification engine**: a numeric game `G` whose value is a scale sum of
`f`, and each of whose options is beaten by some scale option, has value `scaleEval ε f`.
This is `IGame.Fits.equiv_of_forall_moves` applied to `G` and the scale game. -/
theorem mk_eq_scaleEval_of_moves_le {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {G : IGame.{u}} [G.Numeric] (hG : IsScaleSum ε f (Surreal.mk G))
    (hl : ∀ a ∈ Gᴸ, ∃ N : ℕ, a ≤ (scaleOptLo ε f N).out)
    (hr : ∀ b ∈ Gᴿ, ∃ N : ℕ, (scaleOptHi ε f N).out ≤ b) :
    Surreal.mk G = scaleEval ε f hε hε0 := by
  haveI := numeric_scaleGame hε hε0 f
  have hfit : G.Fits (scaleGame ε f) := (fits_scaleGame_iff hε hε0).2 hG
  have hequiv : G ≈ scaleGame ε f := by
    refine hfit.equiv_of_forall_moves ?_ ?_
    · intro a ha
      obtain ⟨N, hN⟩ := hl a ha
      exact ⟨(scaleOptLo ε f N).out, scaleOptLo_out_mem_leftMoves_scaleGame ε f N, hN⟩
    · intro b hb
      obtain ⟨N, hN⟩ := hr b hb
      exact ⟨(scaleOptHi ε f N).out, scaleOptHi_out_mem_rightMoves_scaleGame ε f N, hN⟩
  exact Surreal.mk_eq_mk.2 hequiv

/-- The engine with the option comparisons stated at the level of surreal values. -/
theorem mk_eq_scaleEval_of_mk_moves_le {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {G : IGame.{u}} [G.Numeric] (hG : IsScaleSum ε f (Surreal.mk G))
    (hl : ∀ a (ha : a ∈ Gᴸ), ∃ N : ℕ,
      @Surreal.mk a (IGame.Numeric.of_mem_moves ha) ≤ scaleOptLo ε f N)
    (hr : ∀ b (hb : b ∈ Gᴿ), ∃ N : ℕ,
      scaleOptHi ε f N ≤ @Surreal.mk b (IGame.Numeric.of_mem_moves hb)) :
    Surreal.mk G = scaleEval ε f hε hε0 := by
  refine mk_eq_scaleEval_of_moves_le hε hε0 hG ?_ ?_
  · intro a ha
    obtain ⟨N, hN⟩ := hl a ha
    haveI := IGame.Numeric.of_mem_moves ha
    refine ⟨N, ?_⟩
    rw [← Surreal.mk_le_mk, out_eq]
    exact hN
  · intro b hb
    obtain ⟨N, hN⟩ := hr b hb
    haveI := IGame.Numeric.of_mem_moves hb
    refine ⟨N, ?_⟩
    rw [← Surreal.mk_le_mk, out_eq]
    exact hN

/-! ### The option estimates -/

/-- **The option estimate, lower side**: if `P` is a scale sum and `D > 0` is strictly coarser
than `εᴺ`, then `P − D` lies below the lower option at index `N`. -/
theorem sub_le_scaleOptLo_of_mk_lt {ε : Surreal.{u}} {f : PowerSeries ℝ} {P D : Surreal.{u}}
    (hP : IsScaleSum ε f P) (hD : 0 < D) {N : ℕ}
    (hN : ArchimedeanClass.mk D < ArchimedeanClass.mk (ε ^ N)) :
    P - D ≤ scaleOptLo ε f N := by
  have h0 : ArchimedeanClass.mk (ε ^ N) ≤
      ArchimedeanClass.mk ((P - scalePartial ε f N) + scaleConst f N * ε ^ N) :=
    le_trans (le_min (hP N) (mk_pow_le_mk_scaleConst_mul_pow ε f N))
      (ArchimedeanClass.min_le_mk_add _ _)
  have h1 := abs_lt_abs_of_mk_lt (hN.trans_le h0)
  rw [abs_of_pos hD] at h1
  have h2 := (abs_lt.1 h1).2
  unfold scaleOptLo
  linarith

/-- **The option estimate, upper side**. -/
theorem scaleOptHi_le_add_of_mk_lt {ε : Surreal.{u}} {f : PowerSeries ℝ} {P D : Surreal.{u}}
    (hP : IsScaleSum ε f P) (hD : 0 < D) {N : ℕ}
    (hN : ArchimedeanClass.mk D < ArchimedeanClass.mk (ε ^ N)) :
    scaleOptHi ε f N ≤ P + D := by
  have h0 : ArchimedeanClass.mk (ε ^ N) ≤
      ArchimedeanClass.mk ((P - scalePartial ε f N) - scaleConst f N * ε ^ N) :=
    le_trans (le_min (hP N) (mk_pow_le_mk_scaleConst_mul_pow ε f N))
      (ArchimedeanClass.min_le_mk_sub _ _)
  have h1 := abs_lt_abs_of_mk_lt (hN.trans_le h0)
  rw [abs_of_pos hD] at h1
  have h2 := (abs_lt.1 h1).1
  unfold scaleOptHi
  linarith

/-! ### The option gaps: a scale sum sits at distance of class `mk (εᵐ)` from the options -/

/-- `εᵐ ≤ 2 (P − optLo m)` for a scale sum `P`: the gap is positive and at least half a
scale unit. -/
theorem pow_le_two_mul_sub_scaleOptLo {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {P : Surreal.{u}} (hP : IsScaleSum ε f P) (m : ℕ) :
    ε ^ m ≤ 2 * (P - scaleOptLo ε f m) := by
  have h1 : ArchimedeanClass.mk (ε ^ m) <
      ArchimedeanClass.mk (P - scalePartial ε f (m + 1)) :=
    (mk_pow_lt_mk_pow_succ hε hε0 m).trans_le (hP (m + 1))
  have h2 := (ArchimedeanClass.mk_lt_mk.1 h1) 2
  rw [two_nsmul, abs_of_pos (pow_pos hε0 m)] at h2
  have hs : P - scaleOptLo ε f m =
      ((PowerSeries.coeff m f : ℝ) : Surreal) * ε ^ m + (P - scalePartial ε f (m + 1)) +
        (|((PowerSeries.coeff m f : ℝ) : Surreal)| + 1) * ε ^ m := by
    unfold scaleOptLo scaleConst
    rw [scalePartial_succ, scaleTerm]; ring
  rw [hs]
  have h3 := neg_abs_le (P - scalePartial ε f (m + 1))
  have h5 := mul_le_mul_of_nonneg_right
    (neg_abs_le ((PowerSeries.coeff m f : ℝ) : Surreal)) (pow_pos hε0 m).le
  linarith

/-- `εᵐ ≤ 2 (optHi m − P)` for a scale sum `P`. -/
theorem pow_le_two_mul_scaleOptHi_sub {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {P : Surreal.{u}} (hP : IsScaleSum ε f P) (m : ℕ) :
    ε ^ m ≤ 2 * (scaleOptHi ε f m - P) := by
  have h1 : ArchimedeanClass.mk (ε ^ m) <
      ArchimedeanClass.mk (P - scalePartial ε f (m + 1)) :=
    (mk_pow_lt_mk_pow_succ hε hε0 m).trans_le (hP (m + 1))
  have h2 := (ArchimedeanClass.mk_lt_mk.1 h1) 2
  rw [two_nsmul, abs_of_pos (pow_pos hε0 m)] at h2
  have hs : scaleOptHi ε f m - P =
      (|((PowerSeries.coeff m f : ℝ) : Surreal)| + 1) * ε ^ m -
        ((PowerSeries.coeff m f : ℝ) : Surreal) * ε ^ m - (P - scalePartial ε f (m + 1)) := by
    unfold scaleOptHi scaleConst
    rw [scalePartial_succ, scaleTerm]; ring
  rw [hs]
  have h3 := le_abs_self (P - scalePartial ε f (m + 1))
  have h5 := mul_le_mul_of_nonneg_right
    (le_abs_self ((PowerSeries.coeff m f : ℝ) : Surreal)) (pow_pos hε0 m).le
  linarith

theorem sub_scaleOptLo_pos {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {P : Surreal.{u}} (hP : IsScaleSum ε f P) (m : ℕ) :
    0 < P - scaleOptLo ε f m := by
  have h := pow_le_two_mul_sub_scaleOptLo hε hε0 hP m
  have := pow_pos hε0 m
  linarith

theorem scaleOptHi_sub_pos {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {P : Surreal.{u}} (hP : IsScaleSum ε f P) (m : ℕ) :
    0 < scaleOptHi ε f m - P := by
  have h := pow_le_two_mul_scaleOptHi_sub hε hε0 hP m
  have := pow_pos hε0 m
  linarith

/-- The gap to the lower option at index `m` is at most as fine as `εᵐ`. -/
theorem mk_sub_scaleOptLo_le {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {P : Surreal.{u}} (hP : IsScaleSum ε f P) (m : ℕ) :
    ArchimedeanClass.mk (P - scaleOptLo ε f m) ≤ ArchimedeanClass.mk (ε ^ m) := by
  have h := pow_le_two_mul_sub_scaleOptLo hε hε0 hP m
  have hpos := sub_scaleOptLo_pos hε hε0 hP m
  rw [ArchimedeanClass.mk_le_mk]
  refine ⟨2, ?_⟩
  rw [abs_of_pos (pow_pos hε0 m), abs_of_pos hpos, two_nsmul]
  linarith

/-- The gap to the upper option at index `m` is at most as fine as `εᵐ`. -/
theorem mk_scaleOptHi_sub_le {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} {P : Surreal.{u}} (hP : IsScaleSum ε f P) (m : ℕ) :
    ArchimedeanClass.mk (scaleOptHi ε f m - P) ≤ ArchimedeanClass.mk (ε ^ m) := by
  have h := pow_le_two_mul_scaleOptHi_sub hε hε0 hP m
  have hpos := scaleOptHi_sub_pos hε hε0 hP m
  rw [ArchimedeanClass.mk_le_mk]
  refine ⟨2, ?_⟩
  rw [abs_of_pos (pow_pos hε0 m), abs_of_pos hpos, two_nsmul]
  linarith

/-! ### Additivity: the sum game -/

theorem scalePartial_add (ε : Surreal.{u}) (f g : PowerSeries ℝ) (N : ℕ) :
    scalePartial ε (f + g) N = scalePartial ε f N + scalePartial ε g N := by
  unfold scalePartial partialSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  unfold scaleTerm
  rw [map_add, Real.toSurreal_add, add_mul]

/-- Scale sums add (residuals add). -/
theorem IsScaleSum.add {ε : Surreal.{u}} {f g : PowerSeries ℝ} {x y : Surreal.{u}}
    (hx : IsScaleSum ε f x) (hy : IsScaleSum ε g y) : IsScaleSum ε (f + g) (x + y) := by
  intro N
  rw [scalePartial_add]
  have h : x + y - (scalePartial ε f N + scalePartial ε g N) =
      (x - scalePartial ε f N) + (y - scalePartial ε g N) := by ring
  rw [h]
  exact le_trans (le_min (hx N) (hy N)) (ArchimedeanClass.min_le_mk_add _ _)

/-- **Additivity, unconditional**: `scaleEval ε (f + g) = scaleEval ε f + scaleEval ε g`.
Proof: the Conway sum of the two scale games has value `S = scaleEval f + scaleEval g`, a
scale sum of `f + g`; its options are `S ∓ D` with `D > 0` of class at most `mk (εᵐ)`, which
lie beyond the `(m + 1)`-st options of the `(f + g)`-game. -/
theorem scaleEval_add {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (f g : PowerSeries ℝ) :
    scaleEval ε (f + g) hε hε0 = scaleEval ε f hε hε0 + scaleEval ε g hε hε0 := by
  haveI := numeric_scaleGame hε hε0 f
  haveI := numeric_scaleGame hε hε0 g
  have hx : IsScaleSum ε f (scaleEval ε f hε hε0) := isScaleSum_scaleEval hε hε0 f
  have hy : IsScaleSum ε g (scaleEval ε g hε hε0) := isScaleSum_scaleEval hε hε0 g
  have hG : Surreal.mk (scaleGame ε f + scaleGame ε g) =
      scaleEval ε f hε hε0 + scaleEval ε g hε hε0 := by
    rw [Surreal.mk_add, mk_scaleGame hε hε0 f, mk_scaleGame hε hε0 g]
  rw [← hG]
  symm
  refine mk_eq_scaleEval_of_moves_le hε hε0 (by rw [hG]; exact hx.add hy) ?_ ?_
  · rw [forall_moves_add]
    constructor
    · intro a ha
      rw [leftMoves_scaleGame] at ha
      obtain ⟨m, rfl⟩ := ha
      refine ⟨m + 1, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, mk_scaleGame hε hε0 g]
      have hDmk : ArchimedeanClass.mk (scaleEval ε f hε hε0 - scaleOptLo ε f m) <
          ArchimedeanClass.mk (ε ^ (m + 1)) :=
        (mk_sub_scaleOptLo_le hε hε0 hx m).trans_lt (mk_pow_lt_mk_pow_succ hε hε0 m)
      have key := sub_le_scaleOptLo_of_mk_lt (hx.add hy) (sub_scaleOptLo_pos hε hε0 hx m) hDmk
      have hid : scaleOptLo ε f m + scaleEval ε g hε hε0 =
          scaleEval ε f hε hε0 + scaleEval ε g hε hε0 -
            (scaleEval ε f hε hε0 - scaleOptLo ε f m) := by ring
      rw [hid]
      exact key
    · intro b hb
      rw [leftMoves_scaleGame] at hb
      obtain ⟨n, rfl⟩ := hb
      refine ⟨n + 1, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, mk_scaleGame hε hε0 f]
      have hDmk : ArchimedeanClass.mk (scaleEval ε g hε hε0 - scaleOptLo ε g n) <
          ArchimedeanClass.mk (ε ^ (n + 1)) :=
        (mk_sub_scaleOptLo_le hε hε0 hy n).trans_lt (mk_pow_lt_mk_pow_succ hε hε0 n)
      have key := sub_le_scaleOptLo_of_mk_lt (hx.add hy) (sub_scaleOptLo_pos hε hε0 hy n) hDmk
      have hid : scaleEval ε f hε hε0 + scaleOptLo ε g n =
          scaleEval ε f hε hε0 + scaleEval ε g hε hε0 -
            (scaleEval ε g hε hε0 - scaleOptLo ε g n) := by ring
      rw [hid]
      exact key
  · rw [forall_moves_add]
    constructor
    · intro a ha
      rw [rightMoves_scaleGame] at ha
      obtain ⟨m, rfl⟩ := ha
      refine ⟨m + 1, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, mk_scaleGame hε hε0 g]
      have hDmk : ArchimedeanClass.mk (scaleOptHi ε f m - scaleEval ε f hε hε0) <
          ArchimedeanClass.mk (ε ^ (m + 1)) :=
        (mk_scaleOptHi_sub_le hε hε0 hx m).trans_lt (mk_pow_lt_mk_pow_succ hε hε0 m)
      have key := scaleOptHi_le_add_of_mk_lt (hx.add hy) (scaleOptHi_sub_pos hε hε0 hx m) hDmk
      have hid : scaleOptHi ε f m + scaleEval ε g hε hε0 =
          scaleEval ε f hε hε0 + scaleEval ε g hε hε0 +
            (scaleOptHi ε f m - scaleEval ε f hε hε0) := by ring
      rw [hid]
      exact key
    · intro b hb
      rw [rightMoves_scaleGame] at hb
      obtain ⟨n, rfl⟩ := hb
      refine ⟨n + 1, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, out_eq, mk_scaleGame hε hε0 f]
      have hDmk : ArchimedeanClass.mk (scaleOptHi ε g n - scaleEval ε g hε hε0) <
          ArchimedeanClass.mk (ε ^ (n + 1)) :=
        (mk_scaleOptHi_sub_le hε hε0 hy n).trans_lt (mk_pow_lt_mk_pow_succ hε hε0 n)
      have key := scaleOptHi_le_add_of_mk_lt (hx.add hy) (scaleOptHi_sub_pos hε hε0 hy n) hDmk
      have hid : scaleEval ε f hε hε0 + scaleOptHi ε g n =
          scaleEval ε f hε hε0 + scaleEval ε g hε hε0 +
            (scaleOptHi ε g n - scaleEval ε g hε hε0) := by ring
      rw [hid]
      exact key

/-! ### Multiplicativity: the product game -/

/-- The partial sums are the evaluations of the truncations. -/
theorem scalePartial_eq_eval₂_trunc (ε : Surreal.{u}) (f : PowerSeries ℝ) (N : ℕ) :
    scalePartial ε f N = (PowerSeries.trunc N f).eval₂ realHom ε := by
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  rfl

/-- The truncated product defect `(trunc N f)(trunc N g) − trunc N (f g)` is divisible by
`X ^ N`: the two agree in every coefficient below `N`. -/
theorem X_pow_dvd_trunc_mul_trunc_sub (f g : PowerSeries ℝ) (N : ℕ) :
    (Polynomial.X ^ N : Polynomial ℝ) ∣
      PowerSeries.trunc N f * PowerSeries.trunc N g - PowerSeries.trunc N (f * g) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hd, ← Polynomial.coeff_coe,
    Polynomial.coe_mul, PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc f g hd, sub_self]

/-- **The product defect at the scale**: `U_N V_N − W_N` (`W` the partial sums of `f g`) is at
least as fine as `εᴺ` — it is `εᴺ · Q(ε)` for a real polynomial `Q`. -/
theorem mk_pow_le_mk_scalePartial_mul_sub {ε : Surreal.{u}} (hε : IsFinite ε)
    (f g : PowerSeries ℝ) (N : ℕ) :
    ArchimedeanClass.mk (ε ^ N) ≤ ArchimedeanClass.mk
      (scalePartial ε f N * scalePartial ε g N - scalePartial ε (f * g) N) := by
  obtain ⟨Q, hQ⟩ := X_pow_dvd_trunc_mul_trunc_sub f g N
  have hev := congrArg (Polynomial.eval₂ realHom ε) hQ
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow] at hev
  rw [scalePartial_eq_eval₂_trunc ε f N, scalePartial_eq_eval₂_trunc ε g N,
    scalePartial_eq_eval₂_trunc ε (f * g) N, hev, ArchimedeanClass.mk_mul]
  calc ArchimedeanClass.mk (ε ^ N) = ArchimedeanClass.mk (ε ^ N) + 0 := (add_zero _).symm
    _ ≤ _ := add_le_add le_rfl (isFinite_eval₂ Q hε)

/-- Scale sums multiply:
`x y − W_N = (x − U_N) y + U_N (y − V_N) + (U_N V_N − W_N)`. -/
theorem IsScaleSum.mul {ε : Surreal.{u}} (hε : IsFinite ε) {f g : PowerSeries ℝ}
    {x y : Surreal.{u}} (hx : IsScaleSum ε f x) (hy : IsScaleSum ε g y) :
    IsScaleSum ε (f * g) (x * y) := by
  intro N
  have hsplit : x * y - scalePartial ε (f * g) N =
      (x - scalePartial ε f N) * y +
        (scalePartial ε f N * (y - scalePartial ε g N) +
          (scalePartial ε f N * scalePartial ε g N - scalePartial ε (f * g) N)) := by ring
  rw [hsplit]
  refine le_trans (le_min ?_ (le_min ?_ (mk_pow_le_mk_scalePartial_mul_sub hε f g N)))
    (le_trans (min_le_min le_rfl (ArchimedeanClass.min_le_mk_add _ _))
      (ArchimedeanClass.min_le_mk_add _ _))
  · rw [ArchimedeanClass.mk_mul]
    calc ArchimedeanClass.mk (ε ^ N) = ArchimedeanClass.mk (ε ^ N) + 0 := (add_zero _).symm
      _ ≤ _ := add_le_add (hx N) hy.isFinite
  · rw [ArchimedeanClass.mk_mul]
    calc ArchimedeanClass.mk (ε ^ N) = 0 + ArchimedeanClass.mk (ε ^ N) := (zero_add _).symm
      _ ≤ _ := add_le_add (isFinite_scalePartial hε f N) (hy N)

/-- **Multiplicativity, unconditional**: `scaleEval ε (f g) = scaleEval ε f · scaleEval ε g`.

Proof: the Conway product of the two scale games has value `P = scaleEval f · scaleEval g`, a
scale sum of `f g` (`IsScaleSum.mul`). Each option of the product is `P ∓ D` with `D > 0` a
product of two option gaps, of class at most `mk (εᵐ) + mk (εⁿ) = mk (ε^(m+n))`, hence strictly
coarser than `ε^(m+n+1)`; the option estimates place it beyond the `(m+n+1)`-st option of the
`(f g)`-game. This is the option computation of `Surreal.hahnSum_eq_mul_of_cofinal`, with the
cofinality now automatic. -/
theorem scaleEval_mul {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (f g : PowerSeries ℝ) :
    scaleEval ε (f * g) hε hε0 = scaleEval ε f hε hε0 * scaleEval ε g hε hε0 := by
  haveI := numeric_scaleGame hε hε0 f
  haveI := numeric_scaleGame hε hε0 g
  have hx : IsScaleSum ε f (scaleEval ε f hε hε0) := isScaleSum_scaleEval hε hε0 f
  have hy : IsScaleSum ε g (scaleEval ε g hε hε0) := isScaleSum_scaleEval hε hε0 g
  have hxy : IsScaleSum ε (f * g) (scaleEval ε f hε hε0 * scaleEval ε g hε hε0) :=
    IsScaleSum.mul hε.isFinite hx hy
  have hG : Surreal.mk (scaleGame ε f * scaleGame ε g) =
      scaleEval ε f hε hε0 * scaleEval ε g hε hε0 := by
    rw [Surreal.mk_mul, mk_scaleGame hε hε0 f, mk_scaleGame hε hε0 g]
  rw [← hG]
  symm
  refine mk_eq_scaleEval_of_moves_le hε hε0 (by rw [hG]; exact hxy) ?_ ?_
  · -- left options: both-left or both-right pairs
    rw [forall_moves_mul]
    intro q a ha b hb
    cases q with
    | left =>
      rw [Player.left_mul] at hb
      rw [leftMoves_scaleGame] at ha hb
      obtain ⟨m, rfl⟩ := ha
      obtain ⟨n, rfl⟩ := hb
      refine ⟨m + n + 1, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, mk_mulOption, out_eq, out_eq, mk_scaleGame hε hε0 f,
        mk_scaleGame hε hε0 g]
      have hDpos : 0 < (scaleEval ε f hε hε0 - scaleOptLo ε f m) *
          (scaleEval ε g hε hε0 - scaleOptLo ε g n) :=
        mul_pos (sub_scaleOptLo_pos hε hε0 hx m) (sub_scaleOptLo_pos hε hε0 hy n)
      have hDmk : ArchimedeanClass.mk ((scaleEval ε f hε hε0 - scaleOptLo ε f m) *
          (scaleEval ε g hε hε0 - scaleOptLo ε g n)) <
          ArchimedeanClass.mk (ε ^ (m + n + 1)) := by
        rw [ArchimedeanClass.mk_mul]
        refine lt_of_le_of_lt (add_le_add (mk_sub_scaleOptLo_le hε hε0 hx m)
          (mk_sub_scaleOptLo_le hε hε0 hy n)) ?_
        rw [← ArchimedeanClass.mk_mul, ← pow_add]
        exact mk_pow_lt_mk_pow_succ hε hε0 (m + n)
      have key := sub_le_scaleOptLo_of_mk_lt hxy hDpos hDmk
      have hid : scaleOptLo ε f m * scaleEval ε g hε hε0 +
          scaleEval ε f hε hε0 * scaleOptLo ε g n - scaleOptLo ε f m * scaleOptLo ε g n =
          scaleEval ε f hε hε0 * scaleEval ε g hε hε0 -
            (scaleEval ε f hε hε0 - scaleOptLo ε f m) *
              (scaleEval ε g hε hε0 - scaleOptLo ε g n) := by ring
      rw [hid]
      exact key
    | right =>
      rw [Player.right_mul, Player.neg_left] at hb
      rw [rightMoves_scaleGame] at ha hb
      obtain ⟨m, rfl⟩ := ha
      obtain ⟨n, rfl⟩ := hb
      refine ⟨m + n + 1, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, mk_mulOption, out_eq, out_eq, mk_scaleGame hε hε0 f,
        mk_scaleGame hε hε0 g]
      have hDpos : 0 < (scaleOptHi ε f m - scaleEval ε f hε hε0) *
          (scaleOptHi ε g n - scaleEval ε g hε hε0) :=
        mul_pos (scaleOptHi_sub_pos hε hε0 hx m) (scaleOptHi_sub_pos hε hε0 hy n)
      have hDmk : ArchimedeanClass.mk ((scaleOptHi ε f m - scaleEval ε f hε hε0) *
          (scaleOptHi ε g n - scaleEval ε g hε hε0)) <
          ArchimedeanClass.mk (ε ^ (m + n + 1)) := by
        rw [ArchimedeanClass.mk_mul]
        refine lt_of_le_of_lt (add_le_add (mk_scaleOptHi_sub_le hε hε0 hx m)
          (mk_scaleOptHi_sub_le hε hε0 hy n)) ?_
        rw [← ArchimedeanClass.mk_mul, ← pow_add]
        exact mk_pow_lt_mk_pow_succ hε hε0 (m + n)
      have key := sub_le_scaleOptLo_of_mk_lt hxy hDpos hDmk
      have hid : scaleOptHi ε f m * scaleEval ε g hε hε0 +
          scaleEval ε f hε hε0 * scaleOptHi ε g n - scaleOptHi ε f m * scaleOptHi ε g n =
          scaleEval ε f hε hε0 * scaleEval ε g hε hε0 -
            (scaleOptHi ε f m - scaleEval ε f hε hε0) *
              (scaleOptHi ε g n - scaleEval ε g hε hε0) := by ring
      rw [hid]
      exact key
  · -- right options: mixed pairs
    rw [forall_moves_mul]
    intro q a ha b hb
    cases q with
    | left =>
      rw [Player.left_mul] at hb
      rw [leftMoves_scaleGame] at ha
      rw [rightMoves_scaleGame] at hb
      obtain ⟨m, rfl⟩ := ha
      obtain ⟨n, rfl⟩ := hb
      refine ⟨m + n + 1, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, mk_mulOption, out_eq, out_eq, mk_scaleGame hε hε0 f,
        mk_scaleGame hε hε0 g]
      have hDpos : 0 < (scaleEval ε f hε hε0 - scaleOptLo ε f m) *
          (scaleOptHi ε g n - scaleEval ε g hε hε0) :=
        mul_pos (sub_scaleOptLo_pos hε hε0 hx m) (scaleOptHi_sub_pos hε hε0 hy n)
      have hDmk : ArchimedeanClass.mk ((scaleEval ε f hε hε0 - scaleOptLo ε f m) *
          (scaleOptHi ε g n - scaleEval ε g hε hε0)) <
          ArchimedeanClass.mk (ε ^ (m + n + 1)) := by
        rw [ArchimedeanClass.mk_mul]
        refine lt_of_le_of_lt (add_le_add (mk_sub_scaleOptLo_le hε hε0 hx m)
          (mk_scaleOptHi_sub_le hε hε0 hy n)) ?_
        rw [← ArchimedeanClass.mk_mul, ← pow_add]
        exact mk_pow_lt_mk_pow_succ hε hε0 (m + n)
      have key := scaleOptHi_le_add_of_mk_lt hxy hDpos hDmk
      have hid : scaleOptLo ε f m * scaleEval ε g hε hε0 +
          scaleEval ε f hε hε0 * scaleOptHi ε g n - scaleOptLo ε f m * scaleOptHi ε g n =
          scaleEval ε f hε hε0 * scaleEval ε g hε hε0 +
            (scaleEval ε f hε hε0 - scaleOptLo ε f m) *
              (scaleOptHi ε g n - scaleEval ε g hε hε0) := by ring
      rw [hid]
      exact key
    | right =>
      rw [Player.right_mul, Player.neg_right] at hb
      rw [rightMoves_scaleGame] at ha
      rw [leftMoves_scaleGame] at hb
      obtain ⟨m, rfl⟩ := ha
      obtain ⟨n, rfl⟩ := hb
      refine ⟨m + n + 1, ?_⟩
      rw [← Surreal.mk_le_mk, out_eq, mk_mulOption, out_eq, out_eq, mk_scaleGame hε hε0 f,
        mk_scaleGame hε hε0 g]
      have hDpos : 0 < (scaleOptHi ε f m - scaleEval ε f hε hε0) *
          (scaleEval ε g hε hε0 - scaleOptLo ε g n) :=
        mul_pos (scaleOptHi_sub_pos hε hε0 hx m) (sub_scaleOptLo_pos hε hε0 hy n)
      have hDmk : ArchimedeanClass.mk ((scaleOptHi ε f m - scaleEval ε f hε hε0) *
          (scaleEval ε g hε hε0 - scaleOptLo ε g n)) <
          ArchimedeanClass.mk (ε ^ (m + n + 1)) := by
        rw [ArchimedeanClass.mk_mul]
        refine lt_of_le_of_lt (add_le_add (mk_scaleOptHi_sub_le hε hε0 hx m)
          (mk_sub_scaleOptLo_le hε hε0 hy n)) ?_
        rw [← ArchimedeanClass.mk_mul, ← pow_add]
        exact mk_pow_lt_mk_pow_succ hε hε0 (m + n)
      have key := scaleOptHi_le_add_of_mk_lt hxy hDpos hDmk
      have hid : scaleOptHi ε f m * scaleEval ε g hε hε0 +
          scaleEval ε f hε hε0 * scaleOptLo ε g n - scaleOptHi ε f m * scaleOptLo ε g n =
          scaleEval ε f hε hε0 * scaleEval ε g hε hε0 +
            (scaleOptHi ε f m - scaleEval ε f hε hε0) *
              (scaleEval ε g hε hε0 - scaleOptLo ε g n) := by ring
      rw [hid]
      exact key

/-! ### Polynomials are halo values -/

theorem scalePartial_coe_of_natDegree_lt (ε : Surreal.{u}) (p : Polynomial ℝ) {N : ℕ}
    (hN : p.natDegree < N) : scalePartial ε (p : PowerSeries ℝ) N = p.eval₂ realHom ε := by
  rw [scalePartial_eq_eval₂_trunc, PowerSeries.trunc_coe_eq_self hN]

/-- The scale sums of a polynomial `p` are exactly the deep halo of `p(ε)`. -/
theorem isScaleSum_coe_iff {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (p : Polynomial ℝ) {z : Surreal.{u}} :
    IsScaleSum ε (p : PowerSeries ℝ) z ↔ DeepHalo ε (p.eval₂ realHom ε) z := by
  constructor
  · intro hz N
    have hK : p.natDegree < max (N + 1) (p.natDegree + 1) :=
      lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    have h := hz (max (N + 1) (p.natDegree + 1))
    rw [scalePartial_coe_of_natDegree_lt ε p hK] at h
    exact ((mk_pow_lt_mk_pow_succ hε hε0 N).trans_le
      (mk_pow_le_mk_pow_of_le hε.isFinite (le_max_left _ _))).trans_le h
  · intro hz N
    have hK : p.natDegree < max N (p.natDegree + 1) :=
      lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    have h : z - scalePartial ε (p : PowerSeries ℝ) N =
        (z - p.eval₂ realHom ε) +
          (scalePartial ε (p : PowerSeries ℝ) (max N (p.natDegree + 1)) -
            scalePartial ε (p : PowerSeries ℝ) N) := by
      rw [scalePartial_coe_of_natDegree_lt ε p hK]; ring
    rw [h]
    exact le_trans (le_min (hz N).le
      (mk_pow_le_mk_scalePartial_sub hε.isFinite _ (le_max_left _ _)))
      (ArchimedeanClass.min_le_mk_add _ _)

/-- **Polynomials evaluate to halo values**: `scaleEval ε p = haloValue ε (p(ε))`, the
birthday-simplest point of the deep halo of `p(ε)`. -/
theorem scaleEval_coe {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) (p : Polynomial ℝ) :
    scaleEval ε (p : PowerSeries ℝ) hε hε0 = haloValue ε (p.eval₂ realHom ε) hε0 := by
  rw [scaleEval_eq_iff hε hε0]
  exact ⟨(isScaleSum_coe_iff hε hε0 p).2 (deepHalo_haloValue hε hε0 _),
    fun w hw ↦ birthday_haloValue_le hε hε0 ((isScaleSum_coe_iff hε hε0 p).1 hw)⟩

theorem scaleEval_coe_of_haloSimple {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (p : Polynomial ℝ) (h : HaloSimple ε (p.eval₂ realHom ε)) :
    scaleEval ε (p : PowerSeries ℝ) hε hε0 = p.eval₂ realHom ε := by
  rw [scaleEval_coe]
  exact (haloValue_eq_self_iff hε hε0).2 h

/-- **Constants**: `scaleEval ε (C r) = r` — reals are halo-simple at every scale. -/
theorem scaleEval_C {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) (r : ℝ) :
    scaleEval ε (PowerSeries.C r) hε hε0 = (r : Surreal) := by
  rw [← Polynomial.coe_C, scaleEval_coe, Polynomial.eval₂_C, realHom_apply]
  exact (haloValue_eq_self_iff hε hε0).2 (haloSimple_realCast ε r)

theorem scaleEval_one {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) :
    scaleEval ε 1 hε hε0 = 1 := by
  have h : (1 : PowerSeries ℝ) = PowerSeries.C 1 := (map_one _).symm
  rw [h, scaleEval_C, Real.toSurreal_one]

theorem scaleEval_zero {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) :
    scaleEval ε 0 hε hε0 = 0 := by
  have h : (0 : PowerSeries ℝ) = PowerSeries.C 0 := (map_zero _).symm
  rw [h, scaleEval_C, Real.toSurreal_zero]

/-- **The variable**: `scaleEval ε X = haloValue ε ε`. -/
theorem scaleEval_X {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) :
    scaleEval ε PowerSeries.X hε hε0 = haloValue ε ε hε0 := by
  rw [← Polynomial.coe_X, scaleEval_coe, Polynomial.eval₂_X]

theorem scaleEval_X_of_haloSimple {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (h : HaloSimple ε ε) : scaleEval ε PowerSeries.X hε hε0 = ε := by
  rw [scaleEval_X]
  exact (haloValue_eq_self_iff hε hε0).2 h

theorem scaleEval_C_add_C_mul_X {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (r s : ℝ) :
    scaleEval ε (PowerSeries.C r + PowerSeries.C s * PowerSeries.X) hε hε0 =
      haloValue ε ((r : Surreal) + (s : Surreal) * ε) hε0 := by
  have h : (PowerSeries.C r + PowerSeries.C s * PowerSeries.X : PowerSeries ℝ) =
      ((Polynomial.C r + Polynomial.C s * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) := by
    rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_C,
      Polynomial.coe_X]
  rw [h, scaleEval_coe, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_C, Polynomial.eval₂_X, realHom_apply, realHom_apply]

/-! ### The ring homomorphism -/

/-- **THE SCALE EVALUATION RING HOMOMORPHISM**: for every positive infinitesimal `ε`,
`f ↦ scaleEval ε f` is a ring homomorphism `PowerSeries ℝ →+* Surreal`, with no side
conditions — zero coefficients, cancellation, everything is handled by the scale game. -/
def scaleEvalHom (ε : Surreal.{u}) (hε : Infinitesimal ε) (hε0 : 0 < ε) :
    PowerSeries ℝ →+* Surreal.{u} where
  toFun f := scaleEval ε f hε hε0
  map_one' := scaleEval_one hε hε0
  map_mul' := scaleEval_mul hε hε0
  map_zero' := scaleEval_zero hε hε0
  map_add' := scaleEval_add hε hε0

@[simp]
theorem scaleEvalHom_apply (ε : Surreal.{u}) (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (f : PowerSeries ℝ) : scaleEvalHom ε hε hε0 f = scaleEval ε f hε hε0 :=
  rfl

theorem scaleEval_neg {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) (f : PowerSeries ℝ) :
    scaleEval ε (-f) hε hε0 = -scaleEval ε f hε hε0 :=
  map_neg (scaleEvalHom ε hε hε0) f

theorem scaleEval_sub {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (f g : PowerSeries ℝ) :
    scaleEval ε (f - g) hε hε0 = scaleEval ε f hε hε0 - scaleEval ε g hε hε0 :=
  map_sub (scaleEvalHom ε hε hε0) f g

theorem scaleEval_pow {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) (f : PowerSeries ℝ)
    (n : ℕ) : scaleEval ε (f ^ n) hε hε0 = scaleEval ε f hε hε0 ^ n :=
  map_pow (scaleEvalHom ε hε hε0) f n

theorem scaleEval_natCast {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) (n : ℕ) :
    scaleEval ε (n : PowerSeries ℝ) hε hε0 = n :=
  map_natCast (scaleEvalHom ε hε hε0) n

/-- Real scalars come out: `scaleEval ε (C r * f) = r · scaleEval ε f`. -/
theorem scaleEval_C_mul {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε) (r : ℝ)
    (f : PowerSeries ℝ) :
    scaleEval ε (PowerSeries.C r * f) hε hε0 = (r : Surreal) * scaleEval ε f hε hε0 := by
  rw [scaleEval_mul, scaleEval_C]

/-- The scale evaluation is finite. -/
theorem isFinite_scaleEval {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    (f : PowerSeries ℝ) : IsFinite (scaleEval ε f hε hε0) :=
  (isScaleSum_scaleEval hε hε0 f).isFinite

/-! ### Compatibility with the canonical sum -/

theorem mk_scaleTerm_of_ne_zero (ε : Surreal.{u}) {f : PowerSeries ℝ} {k : ℕ}
    (h : PowerSeries.coeff k f ≠ 0) :
    ArchimedeanClass.mk (scaleTerm ε f k) = ArchimedeanClass.mk (ε ^ k) := by
  unfold scaleTerm
  rw [ArchimedeanClass.mk_mul, mk_realCast h, zero_add]

/-- With all coefficients nonzero, the terms `fₖ εᵏ` are strictly dominating. -/
theorem scaleTerm_strict_dominating {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} (hf : ∀ k, PowerSeries.coeff k f ≠ 0) (k : ℕ) :
    ArchimedeanClass.mk (scaleTerm ε f k) < ArchimedeanClass.mk (scaleTerm ε f (k + 1)) := by
  rw [mk_scaleTerm_of_ne_zero ε (hf k), mk_scaleTerm_of_ne_zero ε (hf (k + 1))]
  exact mk_pow_lt_mk_pow_succ hε hε0 k

/-- With all coefficients nonzero, scale sums are exactly Hahn sums of the term series. -/
theorem isScaleSum_iff_isHahnSum (ε : Surreal.{u}) {f : PowerSeries ℝ}
    (hf : ∀ k, PowerSeries.coeff k f ≠ 0) {z : Surreal.{u}} :
    IsScaleSum ε f z ↔ IsHahnSum (scaleTerm ε f) z := by
  unfold IsScaleSum IsHahnSum scalePartial
  refine forall_congr' fun N ↦ ?_
  rw [mk_scaleTerm_of_ne_zero ε (hf N)]

/-- **Compatibility with the canonical sum**: with all coefficients nonzero, the scale
evaluation is the canonical transfinite sum of `Σ fₖ εᵏ`. -/
theorem scaleEval_eq_hahnSum {ε : Surreal.{u}} (hε : Infinitesimal ε) (hε0 : 0 < ε)
    {f : PowerSeries ℝ} (hf : ∀ k, PowerSeries.coeff k f ≠ 0) :
    scaleEval ε f hε hε0 = hahnSum (scaleTerm_strict_dominating hε hε0 hf) := by
  rw [scaleEval_eq_iff hε hε0]
  exact ⟨(isScaleSum_iff_isHahnSum ε hf).2 (isHahnSum_hahnSum _),
    fun w hw ↦ birthday_hahnSum_le _ ((isScaleSum_iff_isHahnSum ε hf).1 hw)⟩

/-! ### The exponential -/

theorem realCast_ne_zero {r : ℝ} (hr : r ≠ 0) : (r : Surreal.{u}) ≠ 0 :=
  fun h ↦ hr (Real.toSurreal_inj.1 (h.trans Real.toSurreal_zero.symm))

theorem infinitesimal_realCast_mul (r : ℝ) {σ : Surreal.{u}} (hσ : Infinitesimal σ) :
    Infinitesimal ((r : Surreal) * σ) :=
  (isFinite_realCast r).mul_infinitesimal hσ

theorem realCast_mul_ne_zero {r : ℝ} (hr : r ≠ 0) {σ : Surreal.{u}} (hσ0 : σ ≠ 0) :
    (r : Surreal) * σ ≠ 0 :=
  mul_ne_zero (realCast_ne_zero hr) hσ0

private theorem toSurreal_pow (r : ℝ) (k : ℕ) :
    ((r ^ k : ℝ) : Surreal.{u}) = (r : Surreal) ^ k :=
  map_pow realHom r k

/-- The terms of `rescale r (exp ℝ)` at scale `σ` are the exponential-series terms at `r σ`:
`(rᵏ/k!) σᵏ = (r σ)ᵏ / k!`. -/
theorem scaleTerm_rescale_exp (σ : Surreal.{u}) (r : ℝ) (k : ℕ) :
    scaleTerm σ (PowerSeries.rescale r (PowerSeries.exp ℝ)) k =
      ((r : Surreal) * σ) ^ k / ((k.factorial : ℕ) : Surreal) := by
  unfold scaleTerm
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, eq_ratCast, Real.toSurreal_mul,
    Real.toSurreal_ratCast, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, toSurreal_pow, mul_pow]
  ring

/-- The scale sums of `rescale r (exp ℝ)` at `σ` are the Hahn sums of the exponential series
at `r σ` (for `r ≠ 0`; the sign of `r` is arbitrary). -/
theorem isScaleSum_rescale_exp_iff (σ : Surreal.{u}) {r : ℝ} (hr : r ≠ 0) {z : Surreal.{u}} :
    IsScaleSum σ (PowerSeries.rescale r (PowerSeries.exp ℝ)) z ↔
      IsHahnSum (fun k ↦ ((r : Surreal) * σ) ^ k / ((k.factorial : ℕ) : Surreal)) z := by
  have ht : scaleTerm σ (PowerSeries.rescale r (PowerSeries.exp ℝ)) =
      fun k ↦ ((r : Surreal) * σ) ^ k / ((k.factorial : ℕ) : Surreal) :=
    funext (scaleTerm_rescale_exp σ r)
  unfold IsScaleSum IsHahnSum scalePartial
  simp only [ht]
  refine forall_congr' fun N ↦ ?_
  rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero, ArchimedeanClass.mk_pow,
    ArchimedeanClass.mk_pow, ArchimedeanClass.mk_mul, mk_realCast hr, zero_add]

/-- **The exponential along a scale line**: `scaleEval σ (rescale r (exp ℝ)) = expInf (r σ)`
for every positive infinitesimal `σ` and nonzero real `r`. -/
theorem scaleEval_rescale_exp {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : 0 < σ) {r : ℝ}
    (hr : r ≠ 0) :
    scaleEval σ (PowerSeries.rescale r (PowerSeries.exp ℝ)) hσ hσ0 =
      expInf ((r : Surreal) * σ) (infinitesimal_realCast_mul r hσ)
        (realCast_mul_ne_zero hr hσ0.ne') := by
  rw [scaleEval_eq_iff hσ hσ0]
  exact ⟨(isScaleSum_rescale_exp_iff σ hr).2 (isHahnSum_expInf _ _),
    fun w hw ↦ birthday_expInf_le _ _ ((isScaleSum_rescale_exp_iff σ hr).1 hw)⟩

/-- **THE EXPONENTIAL IS A SCALE EVALUATION**: `expInf σ = scaleEval σ (exp ℝ)` for every
positive infinitesimal `σ`. -/
theorem expInf_eq_scaleEval_exp {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : 0 < σ) :
    expInf σ hσ hσ0.ne' = scaleEval σ (PowerSeries.exp ℝ) hσ hσ0 := by
  have h := scaleEval_rescale_exp hσ hσ0 (one_ne_zero (α := ℝ))
  rw [PowerSeries.rescale_one, RingHom.id_apply] at h
  rw [h]
  exact expInf_congr (by rw [Real.toSurreal_one, one_mul]) _ _ _ _

/-- **The reflection law, from mathlib's `exp_mul_exp_neg_eq_one`**:
`expInf σ · expInf (−σ) = 1` for every positive infinitesimal `σ` (cf.
`Surreal.expInf_mul_expInf_neg` in `Infinity.HaloGame`, proved there by the halo engine). -/
theorem expInf_mul_expInf_neg' {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : 0 < σ) :
    expInf σ hσ hσ0.ne' * expInf (-σ) hσ.neg (neg_ne_zero.2 hσ0.ne') = 1 := by
  have h1 := expInf_eq_scaleEval_exp hσ hσ0
  have h2 := scaleEval_rescale_exp hσ hσ0 (neg_ne_zero.2 (one_ne_zero (α := ℝ)))
  have h3 : expInf (-σ) hσ.neg (neg_ne_zero.2 hσ0.ne') =
      expInf (((-1 : ℝ) : Surreal) * σ) (infinitesimal_realCast_mul (-1) hσ)
        (realCast_mul_ne_zero (neg_ne_zero.2 (one_ne_zero (α := ℝ))) hσ0.ne') :=
    expInf_congr (by rw [Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul]) _ _ _ _
  have h4 : PowerSeries.exp ℝ * PowerSeries.rescale (-1 : ℝ) (PowerSeries.exp ℝ) = 1 :=
    PowerSeries.exp_mul_exp_neg_eq_one
  rw [h1, h3, ← h2, ← scaleEval_mul, h4, scaleEval_one]

/-- **THE SIGNED FUNCTIONAL EQUATION ALONG EVERY SCALE LINE**: for every positive
infinitesimal `σ` and all nonzero reals `r, s` with `r + s ≠ 0`,
`expInf (r σ) · expInf (s σ) = expInf ((r + s) σ)`. Mixed signs and irrational ratios are
covered. From mathlib's `PowerSeries.exp_mul_exp_eq_exp_add` through the ring homomorphism. -/
theorem expInf_realCast_mul_add {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : 0 < σ)
    {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r + s ≠ 0) :
    expInf ((r : Surreal) * σ) (infinitesimal_realCast_mul r hσ)
        (realCast_mul_ne_zero hr hσ0.ne') *
      expInf ((s : Surreal) * σ) (infinitesimal_realCast_mul s hσ)
        (realCast_mul_ne_zero hs hσ0.ne') =
      expInf (((r + s : ℝ) : Surreal) * σ) (infinitesimal_realCast_mul (r + s) hσ)
        (realCast_mul_ne_zero hrs hσ0.ne') := by
  rw [← scaleEval_rescale_exp hσ hσ0 hr, ← scaleEval_rescale_exp hσ hσ0 hs,
    ← scaleEval_rescale_exp hσ hσ0 hrs, ← scaleEval_mul, PowerSeries.exp_mul_exp_eq_exp_add]

/-- The signed functional equation with the sum of casts on the right. -/
theorem expInf_realCast_mul_add' {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : 0 < σ)
    {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r + s ≠ 0) :
    expInf ((r : Surreal) * σ) (infinitesimal_realCast_mul r hσ)
        (realCast_mul_ne_zero hr hσ0.ne') *
      expInf ((s : Surreal) * σ) (infinitesimal_realCast_mul s hσ)
        (realCast_mul_ne_zero hs hσ0.ne') =
      expInf (((r : Surreal) + (s : Surreal)) * σ)
        (by rw [← Real.toSurreal_add]; exact infinitesimal_realCast_mul (r + s) hσ)
        (by rw [← Real.toSurreal_add]; exact realCast_mul_ne_zero hrs hσ0.ne') := by
  rw [expInf_realCast_mul_add hσ hσ0 hr hs hrs]
  exact expInf_congr (by rw [Real.toSurreal_add]) _ _ _ _

end Surreal

end
