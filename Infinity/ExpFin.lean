/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.Identification
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The exponential on the finite galaxy

`Infinity.CanonicalSum` produced `expInf`, the exponential as a function on nonzero
infinitesimals. This file extends it to **every finite surreal** via the standard-part
decomposition `x = st x + (x − st x)`:

* `expInf' ε` : a total version of `expInf` (equal to `expInf` on nonzero infinitesimals,
  `1` at `0`, junk elsewhere), so that the definition below needs no case split;
* `expFin x := exp (st x) · expInf' (x − st x)` — mathlib's `Real.exp` on the real part,
  the canonical transfinite sum on the infinitesimal part.

`expFin` is a genuine function `No → No` (junk-valued off the finite galaxy), and on
finite arguments it satisfies the honest calculus package:

* `expFin_realCast` : it extends the real exponential, exactly;
* `expFin_of_infinitesimal` : it extends `expInf`, exactly;
* `stdPart_expFin` : `st (expFin x) = exp (st x)` — the exponential commutes with the
  standard-part projection;
* `isFinite_expFin`, `expFin_pos` : values are finite and positive;
* `expFin_lt_expFin` : strict monotonicity across real parts (monotonicity at
  infinitesimal resolution is open — it needs control of the canonical sum below all
  series scales);
* `expFin_realCast_add` : the functional equation `expFin (r + y) = expFin r · expFin y`
  holds **exactly** when one argument is real — real-translation equivariance;
* `mk_expFin_add_sub_mul` : for arguments with positive infinitesimal parts, the general
  functional equation holds modulo domination by every term of the exponential series at
  the combined infinitesimal part — the finite-galaxy transport of
  `Infinity.ExpMul.mk_expInf_add_sub_mul`. (Its exact form is equivalent to a birthday
  inequality by `Infinity.BirthdayHahn.expInf_add_eq_mul_iff`, and holds outright if the
  product is born by day `ω`, by `Infinity.Identification.expInf_add_eq_mul_of_birthday_le`.)

Together with `expInf` this is, to our knowledge, the first exponential defined and
verified on an entire galaxy of the surreals in a proof assistant. The classical
exponential on all of **No** is Gonshor's genetic `exp` (Gonshor 1986, ch. 10); on finite
arguments Gonshor's function agrees with the decomposition used here (his Theorem 10.2ff:
`exp` is real-analytic-compatible on the finite part and multiplicative), so `expFin` is
the finite-galaxy shadow of the classical object, built without any genetic recursion.

Order lemmas proved on the way (independent interest): `pos_of_stdPart_pos`,
`lt_of_stdPart_lt` — the standard-part projection reflects strict order between
different real parts.
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

/-! ### Order from the standard part -/

/-- `1 + infinitesimal` is positive. -/
theorem one_add_infinitesimal_pos {i : Surreal} (hi : Infinitesimal i) : 0 < 1 + i := by
  have h := infinitesimal_iff.1 hi 1
  rw [one_nsmul] at h
  have := (abs_lt.1 h).1
  linarith

/-- A finite surreal with positive standard part is positive. -/
theorem pos_of_stdPart_pos {x : Surreal} (hx : IsFinite x) (h : 0 < stdPart x) :
    0 < x := by
  obtain ⟨q, hq0, hq⟩ := exists_rat_btwn h
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have habs := (infinitesimal_sub_stdPart hx).abs_lt_ratCast hq0'
  have h1 : (q : Surreal) < (stdPart x : Surreal) := by
    rw [← Real.toSurreal_ratCast]
    exact Real.toSurreal_lt_iff.2 hq
  have h2 := (abs_lt.1 habs).1
  linarith

/-- The standard part reflects strict order: `st x < st y` forces `x < y` for finite
surreals. -/
theorem lt_of_stdPart_lt {x y : Surreal} (hx : IsFinite x) (hy : IsFinite y)
    (h : stdPart x < stdPart y) : x < y := by
  have h1 : 0 < stdPart (y - x) := by
    rw [stdPart_sub hy hx]
    linarith
  linarith [pos_of_stdPart_pos (hy.sub hx) h1]

/-! ### A total version of `expInf` -/

open scoped Classical in
/-- The exponential of an infinitesimal, as a total function: `expInf` on nonzero
infinitesimals, `1` at `0` (as it should be), junk (`1`) elsewhere. -/
def expInf' (ε : Surreal) : Surreal :=
  if h : Infinitesimal ε ∧ ε ≠ 0 then expInf ε h.1 h.2 else 1

@[simp]
theorem expInf'_zero : expInf' 0 = 1 :=
  dif_neg (by simp)

theorem expInf'_of_ne {ε : Surreal} (hε : Infinitesimal ε) (h0 : ε ≠ 0) :
    expInf' ε = expInf ε hε h0 :=
  dif_pos ⟨hε, h0⟩

private theorem partialSum_expSeries_one' {σ : Surreal} :
    partialSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) 1 = 1 := by
  rw [partialSum, Finset.sum_range_one]
  norm_num

/-- `expInf' ε = 1 + O(ε)`: the residual beyond the constant term is infinitesimal. -/
theorem infinitesimal_expInf'_sub_one {ε : Surreal} (hε : Infinitesimal ε) :
    Infinitesimal (expInf' ε - 1) := by
  rcases eq_or_ne ε 0 with rfl | h0
  · rw [expInf'_zero, sub_self]
    exact infinitesimal_zero
  · rw [expInf'_of_ne hε h0]
    have h := isHahnSum_expInf hε h0 1
    rw [partialSum_expSeries_one'] at h
    have ht1 : ArchimedeanClass.mk (ε ^ 1 / (((1 : ℕ).factorial : ℕ) : Surreal)) =
        ArchimedeanClass.mk ε := by norm_num
    rw [ht1] at h
    exact lt_of_lt_of_le hε h

theorem isFinite_expInf' {ε : Surreal} (hε : Infinitesimal ε) :
    IsFinite (expInf' ε) := by
  have h : expInf' ε = 1 + (expInf' ε - 1) := by ring
  rw [h]
  exact isFinite_one.add (infinitesimal_expInf'_sub_one hε).isFinite

theorem expInf'_pos {ε : Surreal} (hε : Infinitesimal ε) : 0 < expInf' ε := by
  have h : expInf' ε = 1 + (expInf' ε - 1) := by ring
  rw [h]
  exact one_add_infinitesimal_pos (infinitesimal_expInf'_sub_one hε)

theorem stdPart_expInf' {ε : Surreal} (hε : Infinitesimal ε) :
    stdPart (expInf' ε) = 1 := by
  have h : expInf' ε = 1 + (expInf' ε - 1) := by ring
  rw [h, stdPart_add_eq_left (infinitesimal_expInf'_sub_one hε),
    ArchimedeanClass.stdPart_one]

/-! ### The exponential on the finite galaxy -/

/-- **The exponential on the finite galaxy**: `expFin x = exp (st x) · expInf' (x − st x)`
— the real exponential of the standard part times the canonical transfinite exponential of
the infinitesimal part. A total function `No → No`; its intended domain is the finite
surreals (elsewhere the infinitesimal-part factor degenerates to `1`). -/
def expFin (x : Surreal) : Surreal :=
  (Real.exp (stdPart x) : Surreal) * expInf' (x - (stdPart x : Surreal))

/-- `expFin` extends the real exponential, exactly. -/
@[simp]
theorem expFin_realCast (r : ℝ) : expFin (r : Surreal) = (Real.exp r : Surreal) := by
  unfold expFin
  rw [stdPart_realCast, sub_self, expInf'_zero, mul_one]

@[simp]
theorem expFin_zero : expFin 0 = 1 := by
  have h : (0 : Surreal) = ((0 : ℝ) : Surreal) := by simp
  rw [h, expFin_realCast, Real.exp_zero, Real.toSurreal_one]

/-- `expFin` extends `expInf`, exactly. -/
theorem expFin_of_infinitesimal {ε : Surreal} (hε : Infinitesimal ε) (h0 : ε ≠ 0) :
    expFin ε = expInf ε hε h0 := by
  unfold expFin
  rw [hε.stdPart_eq_zero, Real.exp_zero, Real.toSurreal_one, Real.toSurreal_zero,
    one_mul, sub_zero]
  exact expInf'_of_ne hε h0

/-- **The exponential commutes with the standard part**: `st (expFin x) = exp (st x)`. -/
theorem stdPart_expFin {x : Surreal} (hx : IsFinite x) :
    stdPart (expFin x) = Real.exp (stdPart x) := by
  unfold expFin
  have hi : Infinitesimal (expInf' (x - (stdPart x : Surreal)) - 1) :=
    infinitesimal_expInf'_sub_one (infinitesimal_sub_stdPart hx)
  have hsplit : (Real.exp (stdPart x) : Surreal) * expInf' (x - (stdPart x : Surreal)) =
      (Real.exp (stdPart x) : Surreal) +
        (Real.exp (stdPart x) : Surreal) * (expInf' (x - (stdPart x : Surreal)) - 1) := by
    ring
  rw [hsplit, stdPart_add_eq_left ((isFinite_realCast _).mul_infinitesimal hi),
    stdPart_realCast]

theorem isFinite_expFin {x : Surreal} (hx : IsFinite x) : IsFinite (expFin x) := by
  unfold expFin
  exact (isFinite_realCast _).mul (isFinite_expInf' (infinitesimal_sub_stdPart hx))

/-- The exponential is positive on the finite galaxy. -/
theorem expFin_pos {x : Surreal} (hx : IsFinite x) : 0 < expFin x :=
  pos_of_stdPart_pos (isFinite_expFin hx)
    (by rw [stdPart_expFin hx]; exact Real.exp_pos _)

/-- **Strict monotonicity across real parts**: `st x < st y` forces
`expFin x < expFin y`. (Monotonicity between arguments with equal standard parts is open:
it requires controlling the canonical sum below every scale of the series.) -/
theorem expFin_lt_expFin {x y : Surreal} (hx : IsFinite x) (hy : IsFinite y)
    (h : stdPart x < stdPart y) : expFin x < expFin y :=
  lt_of_stdPart_lt (isFinite_expFin hx) (isFinite_expFin hy)
    (by rw [stdPart_expFin hx, stdPart_expFin hy]; exact Real.exp_lt_exp.2 h)

/-! ### The functional equation -/

/-- **Real-translation equivariance, exact**: `expFin (r + y) = expFin r · expFin y` for
every real `r` and finite `y`. On the finite galaxy the exponential functional equation
holds *on the nose* whenever one argument is real. -/
theorem expFin_realCast_add (r : ℝ) {y : Surreal} (hy : IsFinite y) :
    expFin ((r : Surreal) + y) = expFin (r : Surreal) * expFin y := by
  unfold expFin
  rw [stdPart_add (isFinite_realCast r) hy, stdPart_realCast]
  have h1 : (r : Surreal) + y - ((r + stdPart y : ℝ) : Surreal) =
      y - (stdPart y : Surreal) := by
    rw [Real.toSurreal_add]
    ring
  rw [h1, sub_self, expInf'_zero, Real.exp_add, Real.toSurreal_mul]
  ring

/-- The difference form of the functional equation: the defect of multiplicativity on the
finite galaxy is exactly the infinitesimal-level defect, scaled by a positive real. -/
theorem expFin_add_sub_mul {x y : Surreal} (hx : IsFinite x) (hy : IsFinite y) :
    expFin (x + y) - expFin x * expFin y =
      (Real.exp (stdPart x + stdPart y) : Surreal) *
        (expInf' ((x - (stdPart x : Surreal)) + (y - (stdPart y : Surreal))) -
          expInf' (x - (stdPart x : Surreal)) * expInf' (y - (stdPart y : Surreal))) := by
  unfold expFin
  rw [stdPart_add hx hy]
  have hxy : x + y - ((stdPart x + stdPart y : ℝ) : Surreal) =
      (x - (stdPart x : Surreal)) + (y - (stdPart y : Surreal)) := by
    rw [Real.toSurreal_add]
    ring
  rw [hxy, Real.exp_add, Real.toSurreal_mul]
  ring

/-- **The functional equation on the finite galaxy, modulo domination**: for finite
arguments whose infinitesimal parts are positive, `expFin (x + y) − expFin x · expFin y`
is dominated by every term of the exponential series at the combined infinitesimal part.
This matches the honest scope of `Infinity.ExpMul` (positivity of the infinitesimal parts
is essential there), transported through the standard-part decomposition. -/
theorem mk_expFin_add_sub_mul {x y : Surreal} (hx : IsFinite x) (hy : IsFinite y)
    (hx0 : 0 < x - (stdPart x : Surreal)) (hy0 : 0 < y - (stdPart y : Surreal)) (n : ℕ) :
    ArchimedeanClass.mk
        (((x - (stdPart x : Surreal)) + (y - (stdPart y : Surreal))) ^ n /
          ((n.factorial : ℕ) : Surreal)) ≤
      ArchimedeanClass.mk (expFin (x + y) - expFin x * expFin y) := by
  have hε : Infinitesimal (x - (stdPart x : Surreal)) := infinitesimal_sub_stdPart hx
  have hδ : Infinitesimal (y - (stdPart y : Surreal)) := infinitesimal_sub_stdPart hy
  rw [expFin_add_sub_mul hx hy, expInf'_of_ne (hε.add hδ) (by positivity),
    expInf'_of_ne hε hx0.ne', expInf'_of_ne hδ hy0.ne', ArchimedeanClass.mk_mul,
    mk_realCast (Real.exp_pos _).ne', zero_add]
  exact mk_expInf_add_sub_mul hε hδ hx0 hy0 n

/-! ### The exponential differential equation at real points -/

private theorem partialSum_expSeries_three {σ : Surreal} :
    partialSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) 3 = 1 + σ + σ ^ 2 / 2 := by
  rw [partialSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num

/-- **A uniform quadratic bound for the infinitesimal exponential**:
`|expInf' ε − 1 − ε| ≤ (3/2)·ε²`, with a constant independent of `ε`. The Hahn-sum
residual bound at stage 3 gives `|expInf' ε − s₃| ≤ k·|ε³/6|` with `k` *depending on
`ε`* — but infinitesimality gives `k·|ε| < 1` for every natural `k`, so the dependence
cancels. This is the quantitative bridge from domination-order control to the honest
`O(ε²)` control that `HasDerivS` demands. -/
theorem abs_expInf'_sub_one_sub_le {ε : Surreal} (hε : Infinitesimal ε) :
    |expInf' ε - 1 - ε| ≤ 3 / 2 * ε ^ 2 := by
  rcases eq_or_ne ε 0 with rfl | h0
  · simp
  · rw [expInf'_of_ne hε h0]
    have h3 := isHahnSum_expInf hε h0 3
    rw [partialSum_expSeries_three] at h3
    obtain ⟨k, hk⟩ := ArchimedeanClass.mk_le_mk.1 h3
    simp only at hk
    have ht3 : (ε ^ 3 / (((3 : ℕ).factorial : ℕ) : Surreal)) = ε ^ 3 / 6 := by norm_num
    rw [ht3] at hk
    -- `k • |ε³/6| ≤ ε²` because `k·|ε| < 1`
    have hkε : (k : Surreal) * |ε| < 1 := by
      have h := infinitesimal_iff.1 hε k
      rwa [nsmul_eq_mul] at h
    have hbound : (k • |ε ^ 3 / 6| : Surreal) ≤ ε ^ 2 := by
      rw [nsmul_eq_mul]
      have h6 : |(6 : Surreal)| = 6 := abs_of_pos (by norm_num)
      have habs3 : |ε ^ 3 / 6| = ε ^ 2 * |ε| / 6 := by
        rw [abs_div, h6, abs_pow]
        rw [show |ε| ^ 3 = |ε| ^ 2 * |ε| by ring, sq_abs]
      rw [habs3]
      have h1 : (k : Surreal) * (ε ^ 2 * |ε| / 6) = (k * |ε|) * ε ^ 2 / 6 := by ring
      rw [h1]
      have h2 : (k : Surreal) * |ε| * ε ^ 2 ≤ 1 * ε ^ 2 :=
        mul_le_mul_of_nonneg_right hkε.le (sq_nonneg ε)
      rw [one_mul] at h2
      have h4 := sq_nonneg ε
      linarith
    have hres : |expInf ε hε h0 - (1 + ε + ε ^ 2 / 2)| ≤ ε ^ 2 := hk.trans hbound
    have hsplit : |expInf ε hε h0 - 1 - ε| ≤
        |expInf ε hε h0 - (1 + ε + ε ^ 2 / 2)| + |ε ^ 2 / 2| := by
      calc |expInf ε hε h0 - 1 - ε|
          = |(expInf ε hε h0 - (1 + ε + ε ^ 2 / 2)) + ε ^ 2 / 2| := by
            congr 1
            ring
        _ ≤ _ := abs_add_le _ _
    have habs2 : |ε ^ 2 / 2| = ε ^ 2 / 2 := by
      rw [abs_div, abs_of_nonneg (sq_nonneg ε)]
      norm_num
    rw [habs2] at hsplit
    linarith

/-- **The exponential differential equation at real points**: `expFin` has surreal-point
derivative `expFin r` at every real `r` — `exp′ = exp`, in the strong `O(ε²)` sense over
*all* infinitesimal increments. The first verified instance of the exponential ODE on the
surreals. (At finite points with nonzero infinitesimal part the same statement runs into
the canonical-sum variation problem recorded in `Infinity.Laurent`.) -/
theorem hasDerivS_expFin_realCast (r : ℝ) :
    HasDerivS expFin (r : Surreal) (expFin (r : Surreal)) := by
  refine ⟨|expFin (r : Surreal)| * (3 / 2), fun ε hε ↦ ?_⟩
  have hkey : expFin ((r : Surreal) + ε) = expFin (r : Surreal) * expInf' ε := by
    rcases eq_or_ne ε 0 with rfl | h0
    · rw [add_zero, expInf'_zero, mul_one]
    · rw [expFin_realCast_add r hε.isFinite, expFin_of_infinitesimal hε h0,
        expInf'_of_ne hε h0]
  calc |expFin ((r : Surreal) + ε) - expFin (r : Surreal) - expFin (r : Surreal) * ε|
      = |expFin (r : Surreal)| * |expInf' ε - 1 - ε| := by
        rw [hkey, ← abs_mul]
        congr 1
        ring
    _ ≤ |expFin (r : Surreal)| * (3 / 2 * ε ^ 2) :=
        mul_le_mul_of_nonneg_left (abs_expInf'_sub_one_sub_le hε) (abs_nonneg _)
    _ = |expFin (r : Surreal)| * (3 / 2) * ε ^ 2 := by ring

end Surreal

end
