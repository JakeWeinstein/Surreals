import Infinity.Expectation

/-!
# Pascal's Wager with infinitely many outcomes, and the surreal St. Petersburg game

Chen–Rubio (*Surreal Decisions*, PPR 2020) analyze Pascal's Wager with surreal utilities on
a **finite** state space and defer the infinite-state case to future work on "surreal
infinite sums". This file carries their program across that boundary: a Pascalian decision
problem with **countably many outcomes** — a near-certain mundane world, an
infinitesimal-probability salvation state, and an infinite tail of ever-less-likely exotic
theological hypotheses — receives a kernel-checked canonical expected utility, and the
classical Pascalian conclusions become theorems.

## The lottery

The probability weights are the telescoping series `pascalProb n = ω⁻ⁿ − ω⁻⁽ⁿ⁺¹⁾`:

* `pascalProb_pos` / `pascalProb_le_one` : each weight is a genuine probability;
* `pascalProb_infinitesimal` : every non-mundane outcome has **positive but infinitesimal**
  probability — the regularity desideratum of the non-Archimedean probability literature
  (Benci–Horsten–Wenmackers; Chen–Rubio's Rene case; Gallow's surreal probabilities),
  realized in `No`;
* `isHahnSum_pascalProb_one` / `hahnSum_pascalProb_eq_one` : **total probability one** —
  the canonical transfinite sum of the weights is exactly `1`. Countable additivity fails
  for limit-based summation on `No` (`Infinity.Limits`), but its domination-semantics
  replacement holds on the nose.

Wagering yields utility `ω²` in the salvation state (probability `≈ 1/ω`) and `10`
elsewhere; refusing yields `11` in the mundane state and `10` elsewhere. Expectation series
are summed in decreasing order of Archimedean scale — the Conway-normal-form convention —
which for the wager means transposing the first two outcomes (`wagerSorted`).

## The theorems

* `forall_realCast_lt_of_isHahnSum_wager` : **every** domination-consistent expected
  utility of wagering exceeds every real number — even though the credence assigned to
  salvation is infinitesimal. This is the Pascalian conclusion in its sharpest form: no
  real-valued payoff, however large, can match the wager, and the verdict is independent
  of which consistent value one takes (so it survives Pruss-style underdetermination).
* `wagerValue` / `refuseValue` : the canonical expected utilities (birthday-simplest
  consistent values); `wagerValue_birthday_le` and `exists_rival_wagerValue` instantiate
  the canonicity-and-underdetermination package at the wager itself.
* `stdPart_refuseValue = 11`, `refuseValue_lt_twelve`, `refuseValue_pos` : refusing has a
  classical (real) shadow — its canonical expected utility is `11 +` infinitesimal.
* `isHahnSum_refuse_lt_isHahnSum_wager` : **dominance**: every consistent value of
  refusing is strictly below every consistent value of wagering; in particular
  `refuseValue_lt_wagerValue`.
* `mixed_lt_wagerValue` : **the pure wager beats every real mixture** (Hájek's
  mixed-strategy objection, resolved as in Chen–Rubio: `γ·E(wager) + (1−γ)·E(refuse) <
  E(wager)` for every real `γ ∈ (0,1)`) — while `forall_realCast_lt_mixed` shows every
  such mixture still exceeds every real. Mixing loses to purity yet remains transfinitely
  valuable, exactly the surreal resolution.

(The mixtures here are formed at the level of canonical values. Whether the canonical
expectation operator is itself additive across lotteries — so that value-mixtures coincide
with canonical expectations of mixed lotteries — is precisely the open birthday-additivity
question isolated in `Infinity.BirthdayHahn` (`hahnSum_add_eq_iff`); at the level of
consistent values it holds by `IsHahnSum.add`.)

## The honest boundary: a fully surreal St. Petersburg game

* `stPetersburg_expectationSeries` : with the same telescoping infinitesimal probabilities
  and payoffs `stPetersburgUtility n ≈ ωⁿ` growing across all Archimedean scales, every
  probability-weighted term equals exactly `1` — an Archimedean-flat expectation series.
* `stPetersburg_collapse` : its domination-consistent expected utilities are **exactly the
  finite surreals**. Even with genuinely surreal probabilities and transfinite payoffs, a
  St. Petersburg-type lottery has no canonical expected utility: the scope restriction of
  the canonical theory tracks a real semantic boundary. Surreal decision theory as built
  here settles Pascal's Wager but does not (and honestly cannot, by this theorem) settle
  St. Petersburg by the same mechanism.
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

/-! ### Groundwork on the canonical infinitesimal `ε₀ = 1/ω` -/

local notation "ε₀" => eps0

private theorem heps_pos : (0 : Surreal.{0}) < ε₀ :=
  show (0 : Surreal) < (ω^ (1 : Surreal))⁻¹ from inv_pos.2 (wpow_pos _)

private theorem heps_inf : Infinitesimal ε₀ :=
  show Infinitesimal (ω^ (1 : Surreal))⁻¹ from infinitesimal_inv_wpow one_pos

private theorem heps_lt_one : ε₀ < 1 := by
  have h := heps_inf.lt_ratCast (q := 1) one_pos
  simpa using h

private theorem h_one_sub_eps_pos : (0 : Surreal.{0}) < 1 - ε₀ :=
  sub_pos.2 heps_lt_one

private theorem hW_ne_zero : (ω^ (1 : Surreal.{0})) ≠ 0 :=
  (wpow_pos _).ne'

private theorem mk_one_sub_eps0 : ArchimedeanClass.mk ((1 : Surreal.{0}) - ε₀) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [stdPart_sub isFinite_one heps_inf.isFinite, heps_inf.stdPart_eq_zero,
    ArchimedeanClass.stdPart_one]
  norm_num

/-- A surreal above every natural number lies in a strictly larger Archimedean galaxy than
`1`: its class is strictly negative. -/
private theorem mk_neg_of_forall_natCast_lt {x : Surreal.{0}}
    (h : ∀ j : ℕ, (j : Surreal) < x) : ArchimedeanClass.mk x < 0 := by
  have h0 : (0 : Surreal) < x := by simpa using h 0
  rw [← ArchimedeanClass.mk_one, ArchimedeanClass.mk_lt_mk]
  intro j
  rw [abs_one, abs_of_pos h0, nsmul_eq_mul, mul_one]
  exact h j

/-! ### The probability weights, and total probability one -/

/-- **The Pascalian probability weights**: `pascalProb n = ω⁻ⁿ − ω⁻⁽ⁿ⁺¹⁾`. Outcome `0` is
the mundane world (probability `1 − 1/ω`, infinitesimally short of certainty); outcome
`n ≥ 1` is the `n`-th theological hypothesis, with positive but infinitesimal probability
at scale `ω⁻ⁿ`. -/
def pascalProb : ℕ → Surreal.{0} :=
  fun n ↦ ε₀ ^ n - ε₀ ^ (n + 1)

theorem pascalProb_apply (n : ℕ) : pascalProb n = ε₀ ^ n * (1 - ε₀) := by
  rw [pascalProb]; ring

/-- Every outcome has positive probability. -/
theorem pascalProb_pos (n : ℕ) : 0 < pascalProb n := by
  rw [pascalProb_apply]
  exact mul_pos (pow_pos heps_pos n) h_one_sub_eps_pos

/-- Every probability weight is at most one. -/
theorem pascalProb_le_one (n : ℕ) : pascalProb n ≤ 1 := by
  rw [pascalProb_apply]
  exact mul_le_one₀ (pow_le_one₀ heps_pos.le heps_lt_one.le)
    h_one_sub_eps_pos.le (by linarith [heps_pos])

private theorem nsmul_mk_eps0_pos {n : ℕ} (hn : n ≠ 0) :
    0 < n • ArchimedeanClass.mk ε₀ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn)).symm⟩
  calc (0 : ArchimedeanClass Surreal.{0}) < ArchimedeanClass.mk ε₀ := heps_inf
    _ ≤ (m + 1) • ArchimedeanClass.mk ε₀ := by
        rw [succ_nsmul]
        exact le_add_of_nonneg_left (nsmul_nonneg heps_inf.le m)

private theorem mk_pascalProb (n : ℕ) :
    ArchimedeanClass.mk (pascalProb n) = n • ArchimedeanClass.mk ε₀ := by
  rw [pascalProb_apply, ArchimedeanClass.mk_mul, mk_one_sub_eps0, add_zero,
    ArchimedeanClass.mk_pow]

/-- **Regularity**: every non-mundane outcome has infinitesimal (but, by
`pascalProb_pos`, nonzero) probability. -/
theorem pascalProb_infinitesimal {n : ℕ} (hn : n ≠ 0) : Infinitesimal (pascalProb n) := by
  rw [infinitesimal_def, mk_pascalProb]
  exact nsmul_mk_eps0_pos hn

/-- The probability weights are strictly dominating: each successive outcome is less likely
by a whole Archimedean scale. -/
theorem pascalProb_strict_dominating (n : ℕ) :
    ArchimedeanClass.mk (pascalProb n) < ArchimedeanClass.mk (pascalProb (n + 1)) :=
  telescoping_strict_dominating n

/-- `1` is a domination-consistent total probability of the Pascalian weights. -/
theorem isHahnSum_pascalProb_one : IsHahnSum pascalProb 1 :=
  isHahnSum_telescoping

/-- **Total probability one**: the canonical transfinite sum of the probability weights is
exactly `1`. The countable lottery is normalized — not approximately, not modulo
domination, but on the nose, by the exact telescoping evaluation of
`Infinity.BirthdayHahn`. -/
theorem hahnSum_pascalProb_eq_one : hahnSum pascalProb_strict_dominating = 1 :=
  hahnSum_telescoping_eq_one

/-! ### The two acts and their expectation series -/

/-- Utilities if one **wagers**: `ω²` in the salvation state (outcome `1`), a mundane `10`
in every other state. -/
def wagerUtility : ℕ → Surreal.{0} :=
  fun n ↦ if n = 1 then (ω^ (1 : Surreal)) ^ 2 else 10

/-- Utilities if one **refuses to wager**: a slightly better mundane life (`11`) in the
mundane state, `10` elsewhere (no salvation anywhere). -/
def refuseUtility : ℕ → Surreal.{0} :=
  fun n ↦ if n = 0 then 11 else 10

/-- The expectation series of wagering, in outcome order. -/
def wagerSeries : ℕ → Surreal.{0} :=
  expectationSeries pascalProb wagerUtility

/-- The expectation series of refusing, in outcome order. -/
def refuseSeries : ℕ → Surreal.{0} :=
  expectationSeries pascalProb refuseUtility

/-- The expectation series of wagering, re-enumerated in decreasing order of Archimedean
scale (the Conway-normal-form convention for transfinite sums): the salvation term
`p₁·ω² = ω − 1` comes first, then the mundane term, then the tail. The re-enumeration is
the transposition of outcomes `0` and `1`. -/
def wagerSorted : ℕ → Surreal.{0} :=
  fun n ↦ wagerSeries (Equiv.swap 0 1 n)

theorem wagerSorted_zero : wagerSorted 0 = ω^ (1 : Surreal) - 1 := by
  rw [wagerSorted, Equiv.swap_apply_left, wagerSeries, expectationSeries_apply,
    wagerUtility, if_pos rfl, pascalProb]
  rw [eps0_def]
  have h0 : (ω^ (1 : Surreal)) ≠ 0 := hW_ne_zero
  have hinv : (ω^ (1 : Surreal)) * (ω^ (1 : Surreal))⁻¹ = 1 := mul_inv_cancel₀ h0
  calc ((ω^ (1 : Surreal))⁻¹ ^ 1 - (ω^ (1 : Surreal))⁻¹ ^ (1 + 1)) * (ω^ (1 : Surreal)) ^ 2
      = (ω^ (1 : Surreal) * (ω^ (1 : Surreal))⁻¹) * (ω^ (1 : Surreal)) -
          (ω^ (1 : Surreal) * (ω^ (1 : Surreal))⁻¹) *
            (ω^ (1 : Surreal) * (ω^ (1 : Surreal))⁻¹) := by ring
    _ = ω^ (1 : Surreal) - 1 := by rw [hinv, one_mul, mul_one]

theorem wagerSorted_one : wagerSorted 1 = 10 * pascalProb 0 := by
  rw [wagerSorted, Equiv.swap_apply_right, wagerSeries, expectationSeries_apply,
    wagerUtility]
  norm_num [mul_comm]

theorem wagerSorted_add_two (n : ℕ) : wagerSorted (n + 2) = 10 * pascalProb (n + 2) := by
  rw [wagerSorted, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega), wagerSeries,
    expectationSeries_apply, wagerUtility, if_neg (by omega), mul_comm]

private theorem mk_ten_mul_pascalProb (n : ℕ) :
    ArchimedeanClass.mk ((10 : Surreal.{0}) * pascalProb n) =
      n • ArchimedeanClass.mk ε₀ := by
  rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_ofNat, zero_add, mk_pascalProb]

private theorem mk_wagerSorted_zero_neg : ArchimedeanClass.mk (wagerSorted 0) < 0 := by
  rw [wagerSorted_zero]
  refine mk_neg_of_forall_natCast_lt fun j ↦ ?_
  have h := natCast_lt_wpow_one (j + 1)
  push_cast at h
  linarith

/-- The sorted wager series is strictly dominating: salvation at scale `ω`, the mundane
world at scale `1`, and the tail at scales `ω⁻², ω⁻³, …`. -/
theorem wagerSorted_strict_dominating (n : ℕ) :
    ArchimedeanClass.mk (wagerSorted n) < ArchimedeanClass.mk (wagerSorted (n + 1)) := by
  match n with
  | 0 =>
    rw [wagerSorted_one]
    calc ArchimedeanClass.mk (wagerSorted 0) < 0 := mk_wagerSorted_zero_neg
      _ = ArchimedeanClass.mk ((10 : Surreal) * pascalProb 0) := by
          rw [mk_ten_mul_pascalProb, zero_nsmul]
  | 1 =>
    rw [wagerSorted_one, show (1 + 1 : ℕ) = 0 + 2 from rfl, wagerSorted_add_two,
      mk_ten_mul_pascalProb, mk_ten_mul_pascalProb, zero_nsmul]
    exact nsmul_mk_eps0_pos (by omega)
  | (m + 2) =>
    rw [wagerSorted_add_two, show (m + 2 + 1 : ℕ) = (m + 1) + 2 from rfl,
      wagerSorted_add_two]
    exact mk_mul_lt_mk_mul_left (by norm_num) (pascalProb_strict_dominating (m + 2))

/-! ### The Pascalian punchline -/

/-- **Every consistent expected utility of wagering exceeds every real number.** The
credence in salvation is infinitesimal, yet no real-valued prospect can compete with the
wager — and this holds for *every* domination-consistent value, so the verdict is immune
to the underdetermination of the expectation. This is the Chen–Rubio conclusion carried to
a countable state space. -/
theorem forall_realCast_lt_of_isHahnSum_wager {x : Surreal.{0}}
    (hx : IsHahnSum wagerSorted x) (r : ℝ) : (r : Surreal) < x := by
  have h1 := hx 1
  have hps : partialSum wagerSorted 1 = ω^ (1 : Surreal) - 1 := by
    rw [partialSum, Finset.sum_range_one, wagerSorted_zero]
  rw [hps] at h1
  have hmk1 : ArchimedeanClass.mk (wagerSorted 1) = 0 := by
    rw [wagerSorted_one, mk_ten_mul_pascalProb, zero_nsmul]
  rw [hmk1] at h1
  obtain ⟨n, hn⟩ := isFinite_iff.1 h1
  have habs := abs_le.1 hn
  obtain ⟨N, hN⟩ := exists_nat_gt (r + 1 + n)
  have hcast : ((r + 1 + (n : ℝ) : ℝ) : Surreal) < (((N : ℕ) : ℝ) : Surreal) := by
    rw [Real.toSurreal_lt_iff]
    exact_mod_cast hN
  simp only [Real.toSurreal_add, Real.toSurreal_one, Real.toSurreal_natCast] at hcast
  have hNW : ((N : ℕ) : Surreal) < ω^ (1 : Surreal) := natCast_lt_wpow_one N
  linarith [habs.1]

/-- **No limit-based expected utility for the wager**: the partial expected utilities of
the Pascalian lottery converge to no surreal number — the value about to be constructed
canonically could not have been reached by approximation. -/
theorem not_tendstoSurreal_partialSum_wager (y : Surreal.{0}) :
    ¬ TendstoSurreal (partialSum wagerSorted) atTop y :=
  not_tendstoSurreal_partialSum
    (ne_zero_of_strict_dominating wagerSorted_strict_dominating) y

/-- **The canonical expected utility of wagering**: the birthday-simplest
domination-consistent value. -/
def wagerValue : Surreal.{0} :=
  hahnSum wagerSorted_strict_dominating

theorem isHahnSum_wagerValue : IsHahnSum wagerSorted wagerValue :=
  isHahnSum_hahnSum _

/-- The canonical expected utility of wagering exceeds every real number. -/
theorem forall_realCast_lt_wagerValue (r : ℝ) : (r : Surreal) < wagerValue :=
  forall_realCast_lt_of_isHahnSum_wager isHahnSum_wagerValue r

/-- Canonicity at the wager: `wagerValue` is a simplest consistent value. -/
theorem wagerValue_birthday_le {z : Surreal.{0}} (hz : IsHahnSum wagerSorted z) :
    wagerValue.birthday ≤ z.birthday :=
  birthday_hahnSum_le _ hz

/-- Underdetermination at the wager: rival consistent values exist — and each is strictly
more complex than the canonical one. -/
theorem exists_rival_wagerValue :
    ∃ y, IsHahnSum wagerSorted y ∧ y ≠ wagerValue ∧
      wagerValue.birthday < y.birthday :=
  exists_isHahnSum_ne_hahnSum _

/-! ### The refusing act -/

theorem refuseSeries_zero : refuseSeries 0 = pascalProb 0 * 11 := by
  rw [refuseSeries, expectationSeries_apply, refuseUtility]
  norm_num

theorem refuseSeries_succ (n : ℕ) : refuseSeries (n + 1) = pascalProb (n + 1) * 10 := by
  rw [refuseSeries, expectationSeries_apply, refuseUtility, if_neg (by omega)]

private theorem mk_refuseSeries_zero : ArchimedeanClass.mk (refuseSeries 0) = 0 := by
  rw [refuseSeries_zero, ArchimedeanClass.mk_mul, mk_pascalProb, zero_nsmul,
    ArchimedeanClass.mk_ofNat, add_zero]

private theorem mk_refuseSeries_succ (n : ℕ) :
    ArchimedeanClass.mk (refuseSeries (n + 1)) = (n + 1) • ArchimedeanClass.mk ε₀ := by
  rw [refuseSeries_succ, ArchimedeanClass.mk_mul, mk_pascalProb,
    ArchimedeanClass.mk_ofNat, add_zero]

/-- The refuse series is strictly dominating (it is already enumerated by decreasing
scale). -/
theorem refuseSeries_strict_dominating (n : ℕ) :
    ArchimedeanClass.mk (refuseSeries n) < ArchimedeanClass.mk (refuseSeries (n + 1)) := by
  match n with
  | 0 =>
    rw [mk_refuseSeries_zero, mk_refuseSeries_succ]
    exact nsmul_mk_eps0_pos (by omega)
  | (m + 1) =>
    have h : ArchimedeanClass.mk (pascalProb (m + 1) * 10) <
        ArchimedeanClass.mk (pascalProb (m + 2) * 10) := by
      rw [mul_comm, mul_comm (pascalProb (m + 2))]
      exact mk_mul_lt_mk_mul_left (by norm_num) (pascalProb_strict_dominating (m + 1))
    rw [refuseSeries_succ, show (m + 1 + 1 : ℕ) = m + 2 from rfl, refuseSeries_succ]
    exact h

/-- **The canonical expected utility of refusing.** -/
def refuseValue : Surreal.{0} :=
  hahnSum refuseSeries_strict_dominating

theorem isHahnSum_refuseValue : IsHahnSum refuseSeries refuseValue :=
  isHahnSum_hahnSum _

/-- Refusing has positive expected utility (the dominance principle at the leading
scale). -/
theorem refuseValue_pos : 0 < refuseValue :=
  pos_of_isHahnSum isHahnSum_refuseValue (refuseSeries_strict_dominating 0)
    (by rw [refuseSeries_zero]; exact mul_pos (pascalProb_pos 0) (by norm_num))

private theorem isFinite_eleven : IsFinite ((11 : Surreal.{0})) := by
  rw [isFinite_def]
  exact (ArchimedeanClass.mk_ofNat).ge

/-- **The classical shadow of refusing**: the standard part of its canonical expected
utility is exactly the classical expected utility `11` of its non-negligible part. -/
theorem stdPart_refuseValue : stdPart refuseValue = 11 := by
  have h := stdPart_eq_of_isHahnSum isHahnSum_refuseValue (k := 1)
    (by rw [mk_refuseSeries_succ]; exact nsmul_mk_eps0_pos (by omega))
  rw [h, partialSum, Finset.sum_range_one, refuseSeries_zero, pascalProb_apply,
    pow_zero, one_mul, sub_mul, one_mul]
  have hinf : Infinitesimal (ε₀ * 11) := heps_inf.mul_isFinite isFinite_eleven
  rw [stdPart_sub isFinite_eleven hinf.isFinite, hinf.stdPart_eq_zero, sub_zero]
  have h11 := stdPart_realCast (11 : ℝ)
  rw [show (((11 : ℝ)) : Surreal) = (11 : Surreal) by simp] at h11
  exact h11

/-- The canonical expected utility of refusing is below `12`: refusing is worth
`11 ± infinitesimal`. -/
theorem refuseValue_lt_twelve : refuseValue < 12 := by
  have h1 := isHahnSum_refuseValue 1
  have hres : Infinitesimal (refuseValue - partialSum refuseSeries 1) := by
    refine lt_of_lt_of_le ?_ h1
    rw [mk_refuseSeries_succ]
    exact nsmul_mk_eps0_pos (by omega)
  have habs : |refuseValue - partialSum refuseSeries 1| < 1 := by
    have := infinitesimal_iff.1 hres 1
    simpa using this
  have hps : partialSum refuseSeries 1 ≤ 11 := by
    rw [partialSum, Finset.sum_range_one, refuseSeries_zero]
    nlinarith [pascalProb_le_one 0, pascalProb_pos 0]
  have h2 := (abs_lt.1 habs).2
  linarith

/-! ### Dominance: wagering beats refusing -/

private theorem head_gap_mk_neg :
    ArchimedeanClass.mk (wagerSorted 0 - refuseSeries 0) < 0 := by
  refine mk_neg_of_forall_natCast_lt fun j ↦ ?_
  rw [wagerSorted_zero, refuseSeries_zero]
  have h := natCast_lt_wpow_one (j + 13)
  push_cast at h
  nlinarith [pascalProb_le_one 0, pascalProb_pos 0]

/-- **Dominance**: every consistent expected utility of refusing is strictly below every
consistent expected utility of wagering. The comparison holds across the entire
underdetermination interval of both acts, not merely at the canonical values. -/
theorem isHahnSum_refuse_lt_isHahnSum_wager {x y : Surreal.{0}}
    (hx : IsHahnSum refuseSeries x) (hy : IsHahnSum wagerSorted y) : x < y := by
  refine lt_of_isHahnSum_of_head_lt hx hy ?_ ?_ ?_
  · -- refuseSeries 0 < wagerSorted 0
    rw [wagerSorted_zero, refuseSeries_zero]
    have h := natCast_lt_wpow_one 13
    push_cast at h
    nlinarith [pascalProb_le_one 0, pascalProb_pos 0]
  · calc ArchimedeanClass.mk (wagerSorted 0 - refuseSeries 0) < 0 := head_gap_mk_neg
      _ < ArchimedeanClass.mk (refuseSeries 1) := by
          rw [mk_refuseSeries_succ]
          exact nsmul_mk_eps0_pos (by omega)
  · calc ArchimedeanClass.mk (wagerSorted 0 - refuseSeries 0) < 0 := head_gap_mk_neg
      _ = ArchimedeanClass.mk (wagerSorted 1) := by
          rw [wagerSorted_one, mk_ten_mul_pascalProb, zero_nsmul]

/-- Wagering canonically beats refusing. -/
theorem refuseValue_lt_wagerValue : refuseValue < wagerValue :=
  isHahnSum_refuse_lt_isHahnSum_wager isHahnSum_refuseValue isHahnSum_wagerValue

/-! ### Mixed strategies (Hájek's objection) -/

/-- **The pure wager beats every mixture**: for any real mixing weight `γ ∈ (0,1)`, the
`γ`-mixture of the two canonical expected utilities falls strictly below the pure wager's.
Surreal arithmetic is non-absorptive: diluting an infinite prospect genuinely costs. -/
theorem mixed_lt_wagerValue {γ : ℝ} (_h0 : 0 < γ) (h1 : γ < 1) :
    (γ : Surreal) * wagerValue + ((1 - γ : ℝ) : Surreal) * refuseValue < wagerValue := by
  have hb := refuseValue_lt_wagerValue
  have hg1 : ((1 - γ : ℝ) : Surreal) = 1 - (γ : Surreal) := by
    rw [Real.toSurreal_sub, Real.toSurreal_one]
  have hglt : (γ : Surreal) < 1 := by
    rw [show (1 : Surreal) = ((1 : ℝ) : Surreal) by norm_cast, Real.toSurreal_lt_iff]
    exact h1
  rw [hg1]
  nlinarith [mul_pos (sub_pos.2 hglt) (sub_pos.2 hb)]

/-- **Every mixture still exceeds every real**: mixing dilutes the wager but cannot bring
it down to any real value — a chance at a transfinite good remains transfinitely valuable.
(With `mixed_lt_wagerValue`: mixtures are dominated by purity yet remain beyond all
finite prospects — the two halves of the surreal answer to the mixed-strategy
objection.) -/
theorem forall_realCast_lt_mixed {γ : ℝ} (h0 : 0 < γ) (h1 : γ < 1) (r : ℝ) :
    (r : Surreal) < (γ : Surreal) * wagerValue + ((1 - γ : ℝ) : Surreal) * refuseValue := by
  have hg0 : (0 : Surreal) < (γ : Surreal) := by
    rw [show (0 : Surreal) = ((0 : ℝ) : Surreal) by norm_cast, Real.toSurreal_lt_iff]
    exact h0
  have ha := forall_realCast_lt_wagerValue (r / γ)
  have hdiv : ((r / γ : ℝ) : Surreal) = (r : Surreal) / (γ : Surreal) :=
    Real.toSurreal_div r γ
  rw [hdiv, div_lt_iff₀ hg0] at ha
  have hmix : 0 < ((1 - γ : ℝ) : Surreal) * refuseValue := by
    refine mul_pos ?_ refuseValue_pos
    rw [show (0 : Surreal) = ((0 : ℝ) : Surreal) by norm_cast, Real.toSurreal_lt_iff]
    linarith
  nlinarith

/-! ### The surreal St. Petersburg game -/

/-- **St. Petersburg payoffs across the Archimedean scales**: outcome `n` (of probability
`≈ ω⁻ⁿ`) pays `≈ ωⁿ`, so that each probability-weighted term is exactly `1`. -/
def stPetersburgUtility : ℕ → Surreal.{0} :=
  fun n ↦ (1 - ε₀)⁻¹ * (ω^ (1 : Surreal)) ^ n

theorem stPetersburgUtility_pos (n : ℕ) : 0 < stPetersburgUtility n :=
  mul_pos (inv_pos.2 h_one_sub_eps_pos) (pow_pos (wpow_pos _) n)

/-- The expectation series of the surreal St. Petersburg game is Archimedean-flat: every
term equals exactly `1`. -/
theorem stPetersburg_expectationSeries (n : ℕ) :
    expectationSeries pascalProb stPetersburgUtility n = 1 := by
  rw [expectationSeries_apply, pascalProb_apply, stPetersburgUtility]
  have h2 : ε₀ * ω^ (1 : Surreal) = 1 :=
    show (ω^ (1 : Surreal))⁻¹ * ω^ (1 : Surreal) = 1 from
      inv_mul_cancel₀ hW_ne_zero
  calc ε₀ ^ n * (1 - ε₀) * ((1 - ε₀)⁻¹ * (ω^ (1 : Surreal)) ^ n)
      = (ε₀ * ω^ (1 : Surreal)) ^ n * ((1 - ε₀) * (1 - ε₀)⁻¹) := by
        rw [mul_pow]; ring
    _ = 1 := by
        rw [h2, one_pow, mul_inv_cancel₀ h_one_sub_eps_pos.ne', one_mul]

/-- **The St. Petersburg collapse, in fully surreal form**: with infinitesimal
probabilities and payoffs growing across all Archimedean scales, the
domination-consistent expected utilities of the St. Petersburg lottery are exactly the
finite surreals — an entire galaxy of values, with no canonical selection. Surreal
expected utility as constructed here genuinely does not decide St. Petersburg; the
boundary is a theorem, not a modeling choice. -/
theorem stPetersburg_collapse (x : Surreal.{0}) :
    IsHahnSum (expectationSeries pascalProb stPetersburgUtility) x ↔ IsFinite x := by
  have hfun : expectationSeries pascalProb stPetersburgUtility = fun _ ↦ (1 : Surreal) :=
    funext stPetersburg_expectationSeries
  rw [hfun, isHahnSum_one_iff]

end Surreal

end
