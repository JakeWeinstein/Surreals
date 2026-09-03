/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.MonomialCensus
import Infinity.ExpLog
import Infinity.ExpMul
import Infinity.BirthdayHahn

/-!
# The FE ladder: `exp(n·logΩ) = (1+ω⁻¹)ⁿ` for every `n`, at birthday exactly `ω·n`

`Infinity.ExpFibre` proved the first exact instance of the exponential functional
equation, at `(logOmega, logOmega)`. This file turns that instance into a **ladder**:
the canonical-sum exponential is evaluated exactly on the entire lattice
`ℕ⁺ · logOmega`, and the functional equation holds exactly between any two lattice
points.

* `expInf_ladder` : **`expInf ((n+1)·logOmega) = (1+ω⁻¹)^(n+1)`** for every `n : ℕ` —
  the first exact evaluation of the surreal exponential on an infinite family of
  arguments.
* `birthday_expInf_ladder` : `birthday (expInf ((n+1)·logOmega)) = ω·(n+1)` **exactly**
  — the exponential prices the `n`-fold argument at the `n`-th block, uniformly.
  (Rung 1 recovers `ExpLog`'s day-`ω` value.)
* `expInf_lattice_add_eq_mul` : **THE LATTICE FUNCTIONAL EQUATION** —
  `expInf (a + b) = expInf a · expInf b` for all `a = (n+1)·logOmega`,
  `b = (m+1)·logOmega`: infinitely many exact FE instances at once.

The engine is the rung-coupled induction discovered in the ExpFibre session:

1. **Rung `n`'s value feeds rung `n+1`'s Hahn-sum half.** By the inductive hypothesis
   `expInf (n·logOmega) = (1+ω⁻¹)ⁿ` and the Cauchy product (`isHahnSum_expInf_mul`),
   the product `(1+ω⁻¹)ⁿ·(1+ω⁻¹) = (1+ω⁻¹)^(n+1)` is a Hahn sum of the exponential
   series at `(n+1)·logOmega` — no polynomial identities, no composition estimates.
2. **The binomial padded series prices the rung.** `(1+ω⁻¹)^N = Σ_{k≤N} C(N,k)·ω⁻ᵏ`
   is the level-`N` grid point of the padded series
   `ladderCoeff N = (C(N,0), …, C(N,N), 1, 1, …)` (all coefficients nonzero dyadics),
   so `birthday ((1+ω⁻¹)^N) ≤ ω·N` (`birthday_pow_le`).
3. **The tube theorem polices the rung's halo.** Every Hahn sum of the series at any
   `σ` of class `ω⁻¹` for which `(1+ω⁻¹)^(N+2)` is a Hahn sum sits at distance-class
   exactly `ω^{-(N+3)}` from the padded canonical sum; the block-`N` monomial tube
   theorem forces anything born before day `ω·(N+2)` to be the penultimate partial sum
   `(1+ω⁻¹)^(N+2) − ω^{-(N+2)}` — contradicting halo strictness
   (`ladder_lower`). So every Hahn sum of the rung's series is born ≥ `ω·(N+2)`.

Identification closes rung by rung through `hahnSum_eq_iff`. The census side
(`ladder_strict`, `ladder_lower`, `birthday_pow_le`) is fully parametric — it never
mentions `logOmega` — so the same rungs will price other exact-value ladders (mixed
dyadic-monomial log anchors, the half-log fibre once exact square roots land).
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

private theorem one_cast : ((1 : Dyadic) : Surreal) = 1 := by
  show (((1 : Dyadic) : ℚ) : Surreal) = 1
  norm_num

private theorem zero_cast : ((0 : Dyadic) : Surreal) = 0 := by
  show (((0 : Dyadic) : ℚ) : Surreal) = 0
  norm_num

private theorem mk_pow_congr' {a b : Surreal}
    (h : ArchimedeanClass.mk a = ArchimedeanClass.mk b) (n : ℕ) :
    ArchimedeanClass.mk (a ^ n) = ArchimedeanClass.mk (b ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, ih, h]

/-! ### The binomial padded series -/

/-- The binomial padded census coefficients for rung `N`: the binomial expansion of
`(1+ω⁻¹)^N` padded with a tail of ones, so that every coefficient is a nonzero dyadic
and the monomial tube census applies. -/
def ladderCoeff (N k : ℕ) : Dyadic :=
  if k ≤ N then (N.choose k : Dyadic) else 1

theorem ladderCoeff_ne_zero (N k : ℕ) : ladderCoeff N k ≠ 0 := by
  unfold ladderCoeff
  split
  · rename_i hk
    intro h
    have h2 : ((N.choose k : Dyadic) : Surreal.{0}) = ((0 : Dyadic) : Surreal) := by rw [h]
    rw [dyadic_cast_natCast, zero_cast] at h2
    exact (Nat.cast_ne_zero (R := Surreal.{0})).2 (Nat.choose_pos hk).ne' h2
  · intro h
    have h2 : ((1 : Dyadic) : Surreal.{0}) = ((0 : Dyadic) : Surreal) := by rw [h]
    rw [one_cast, zero_cast] at h2
    exact one_ne_zero h2

/-- **The binomial theorem on the grid**: the first `N+1` terms of the padded series
sum to `(1+ω⁻¹)^N`. -/
theorem monoS_ladder_full (N : ℕ) : monoS (ladderCoeff N) (N + 1) = (1 + ε₀) ^ N := by
  show partialSum (monoTerm (ladderCoeff N)) (N + 1) = _
  rw [partialSum, add_comm (1 : Surreal.{0}) ε₀, add_pow]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkN : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  simp only [monoTerm, ladderCoeff]
  rw [if_pos hkN, dyadic_cast_natCast, one_pow, mul_one]
  ring

/-- Peeling the top binomial term: `T_{N+1} = T_N + ω^{-N}` (since `C(N,N) = 1`). -/
theorem monoS_ladder_succ (N : ℕ) :
    monoS (ladderCoeff N) (N + 1) = monoS (ladderCoeff N) N + ε₀ ^ N := by
  have h : monoS (ladderCoeff N) (N + 1)
      = monoS (ladderCoeff N) N + monoTerm (ladderCoeff N) N :=
    partialSum_succ (monoTerm (ladderCoeff N)) N
  have hlast : monoTerm (ladderCoeff N) N = ε₀ ^ N := by
    simp only [monoTerm, ladderCoeff]
    rw [if_pos le_rfl, Nat.choose_self, dyadic_cast_natCast, Nat.cast_one, one_mul]
  rw [h, hlast]

/-! ### The upper bound: every binomial power is a grid point -/

/-- **The grid price of the binomial powers**: `birthday ((1+ω⁻¹)^(N+1)) ≤ ω·(N+1)` —
the power is the level-`(N+1)` grid point `T_{N+1} + 1·ω^{-(N+1)}` of its own padded
series. -/
theorem birthday_pow_le (N : ℕ) :
    (((1 : Surreal.{0}) + ε₀) ^ (N + 1)).birthday ≤ Ω * (((N + 1) : ℕ) : NatOrdinal) := by
  have h : (monoS (ladderCoeff (N + 1)) (N + 1) + ((1 : Dyadic) : Surreal) * ε₀ ^ (N + 1)).birthday
      ≤ Ω * (((N + 1) : ℕ) : NatOrdinal) + ((Dyadic.hgt (1 : Dyadic) - 1 : ℕ) : NatOrdinal) :=
    birthday_monoS_add_dyadic_mul_le (ladderCoeff_ne_zero (N + 1)) N (t := 1) one_ne_zero
  have hfull : monoS (ladderCoeff (N + 1)) (N + 2) = (1 + ε₀) ^ (N + 1) :=
    monoS_ladder_full (N + 1)
  have hsucc : monoS (ladderCoeff (N + 1)) (N + 2)
      = monoS (ladderCoeff (N + 1)) (N + 1) + ε₀ ^ (N + 1) :=
    monoS_ladder_succ (N + 1)
  have hval : monoS (ladderCoeff (N + 1)) (N + 1) + ((1 : Dyadic) : Surreal) * ε₀ ^ (N + 1)
      = (1 + ε₀) ^ (N + 1) := by
    rw [one_cast, one_mul]
    linear_combination hfull - hsucc
  have hhgt : ((Dyadic.hgt (1 : Dyadic) - 1 : ℕ) : NatOrdinal) = 0 := by
    rw [Dyadic.hgt_one]
    norm_num
  rw [hval, hhgt, add_zero] at h
  exact h

/-! ### Halo strictness and the lower bound, parametric in the argument -/

/-- **Halo strictness**, parametric: for any `σ` of class `ω⁻¹`, any two Hahn sums of
the exponential series at `σ` differ by less than every `ω`-power scale. -/
theorem ladder_strict {σ v z : Surreal.{0}}
    (hσ : ArchimedeanClass.mk σ = ArchimedeanClass.mk ε₀)
    (hv : IsHahnSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) v)
    (hz : IsHahnSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) z) (m : ℕ) :
    ArchimedeanClass.mk (ε₀ ^ m) < ArchimedeanClass.mk (z - v) := by
  have h : ArchimedeanClass.mk (σ ^ (m + 1) / (((m + 1).factorial : ℕ) : Surreal)) ≤
      ArchimedeanClass.mk (z - v) :=
    IsHahnSum.mk_sub_le hz hv (m + 1)
  have hterm : ArchimedeanClass.mk (σ ^ (m + 1) / (((m + 1).factorial : ℕ) : Surreal))
      = ArchimedeanClass.mk (ε₀ ^ (m + 1)) := by
    rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero]
    exact mk_pow_congr' hσ (m + 1)
  rw [hterm] at h
  exact (mk_pow_lt_mk_pow_succ eps0_inf eps0_pos' m).trans_le h

/-- **The census rung**: for any `σ` of class `ω⁻¹` such that `(1+ω⁻¹)^(N+2)` is a Hahn
sum of the exponential series at `σ`, *every* Hahn sum of that series is born at or
after day `ω·(N+2)` — by the block-`N` monomial tube theorem through the binomial
padded series. -/
theorem ladder_lower (N : ℕ) {σ z : Surreal.{0}}
    (hσ : ArchimedeanClass.mk σ = ArchimedeanClass.mk ε₀)
    (hv : IsHahnSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) ((1 + ε₀) ^ (N + 2)))
    (hz : IsHahnSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) z) :
    Ω * (((N + 2) : ℕ) : NatOrdinal) ≤ z.birthday := by
  by_contra hcon
  rw [not_le] at hcon
  set w := hahnSum (monoTerm_strict_dominating (ladderCoeff_ne_zero (N + 2))) with hwdef
  have hw : IsHahnSum (monoTerm (ladderCoeff (N + 2))) w := isHahnSum_hahnSum _
  -- `z` is at distance-class exactly `ω^{-(N+3)}` from the padded canonical sum `w`
  have hfull : monoS (ladderCoeff (N + 2)) (N + 3) = (1 + ε₀) ^ (N + 2) :=
    monoS_ladder_full (N + 2)
  have hdv : ArchimedeanClass.mk (monoS (ladderCoeff (N + 2)) (N + 3) - w)
      = ArchimedeanClass.mk (ε₀ ^ (N + 3)) :=
    mk_monoS_sub (ladderCoeff_ne_zero (N + 2)) hw (N + 3)
  have hv3 : ArchimedeanClass.mk (ε₀ ^ (N + 3)) <
      ArchimedeanClass.mk (z - (1 + ε₀) ^ (N + 2)) := ladder_strict hσ hv hz (N + 3)
  have hsplit : z - w
      = (monoS (ladderCoeff (N + 2)) (N + 3) - w) + (z - (1 + ε₀) ^ (N + 2)) := by
    rw [hfull]
    ring
  have hlt : ArchimedeanClass.mk (monoS (ladderCoeff (N + 2)) (N + 3) - w) <
      ArchimedeanClass.mk (z - (1 + ε₀) ^ (N + 2)) := by
    rw [hdv]
    exact hv3
  have hzw : ArchimedeanClass.mk (z - w) = ArchimedeanClass.mk (ε₀ ^ (N + 3)) := by
    rw [hsplit, ArchimedeanClass.mk_add_eq_mk_left hlt, hdv]
  -- the tube theorem at block `B = N` forces `z` to be the penultimate partial sum
  have hstep1 : ArchimedeanClass.mk (ε₀ ^ (N + 1)) < ArchimedeanClass.mk (ε₀ ^ (N + 2)) :=
    mk_pow_lt_mk_pow_succ eps0_inf eps0_pos' (N + 1)
  have hstep2 : ArchimedeanClass.mk (ε₀ ^ (N + 2)) < ArchimedeanClass.mk (ε₀ ^ (N + 3)) :=
    mk_pow_lt_mk_pow_succ eps0_inf eps0_pos' (N + 2)
  have hdist : ArchimedeanClass.mk (ε₀ ^ (N + 1)) < ArchimedeanClass.mk (z - w) := by
    rw [hzw]
    exact hstep1.trans hstep2
  have heq : z = monoS (ladderCoeff (N + 2)) (N + 2) :=
    mono_eq_monoS_of_birthday_lt_of_mk_lt (ladderCoeff_ne_zero (N + 2)) hw N hdist hcon
  -- contradiction with halo strictness at scale `N+2`
  have hsucc : monoS (ladderCoeff (N + 2)) (N + 3)
      = monoS (ladderCoeff (N + 2)) (N + 2) + ε₀ ^ (N + 2) :=
    monoS_ladder_succ (N + 2)
  have h2 := ladder_strict hσ hv hz (N + 2)
  rw [heq] at h2
  have hval : monoS (ladderCoeff (N + 2)) (N + 2) - (1 + ε₀) ^ (N + 2) = -ε₀ ^ (N + 2) := by
    linear_combination hfull - hsucc
  rw [hval, ArchimedeanClass.mk_neg] at h2
  exact lt_irrefl _ h2

/-! ### The lattice arguments `(n+1)·logOmega` -/

/-- The exponential's argument respects propositional equality (proof irrelevance). -/
theorem expInf_congr {ε ε' : Surreal} (h : ε = ε') (hε : Infinitesimal ε) (hε0 : ε ≠ 0)
    (hε' : Infinitesimal ε') (hε0' : ε' ≠ 0) : expInf ε hε hε0 = expInf ε' hε' hε0' := by
  subst h
  rfl

theorem mk_ladder_arg (n : ℕ) :
    ArchimedeanClass.mk ((((n + 1) : ℕ) : Surreal.{0}) * logOmega)
      = ArchimedeanClass.mk ε₀ := by
  have hcast : (((n + 1 : ℕ) : ℕ) : Surreal.{0}) = (((n + 1 : ℕ) : ℝ) : Surreal) := by
    rw [Real.toSurreal_natCast]
  rw [ArchimedeanClass.mk_mul, hcast, mk_realCast (by positivity), zero_add, mk_logOmega,
    eps0_def]

theorem ladder_arg_infinitesimal (n : ℕ) :
    Infinitesimal ((((n + 1) : ℕ) : Surreal.{0}) * logOmega) := by
  rw [infinitesimal_def, mk_ladder_arg]
  exact infinitesimal_def.1 eps0_inf

theorem ladder_arg_pos (n : ℕ) : (0 : Surreal.{0}) < (((n + 1) : ℕ) : Surreal) * logOmega :=
  mul_pos (by exact_mod_cast Nat.succ_pos n) logOmega_pos

/-! ### The rung step and the ladder -/

/-- **The rung step**: for any argument `σ` of class `ω⁻¹` for which `(1+ω⁻¹)^(n+2)` is
a Hahn sum of the exponential series, the canonical value *is* that power — it is born
by day `ω·(n+2)` while every Hahn sum of the series is born at or after day `ω·(n+2)`. -/
theorem ladder_step (n : ℕ) {σ : Surreal.{0}} (hσinf : Infinitesimal σ) (hσ0 : σ ≠ 0)
    (hσmk : ArchimedeanClass.mk σ = ArchimedeanClass.mk ε₀)
    (hv : IsHahnSum (fun k ↦ σ ^ k / ((k.factorial : ℕ) : Surreal)) ((1 + ε₀) ^ (n + 2))) :
    expInf σ hσinf hσ0 = (1 + ε₀) ^ (n + 2) := by
  unfold expInf
  rw [hahnSum_eq_iff]
  refine ⟨hv, fun w hw ↦ ?_⟩
  have hup : (((1 : Surreal.{0}) + ε₀) ^ (n + 2)).birthday
      ≤ Ω * (((n + 2) : ℕ) : NatOrdinal) := birthday_pow_le (n + 1)
  exact hup.trans (ladder_lower n hσmk hv hw)

/-- **THE FE LADDER**: `expInf ((n+1)·logOmega) = (1+ω⁻¹)^(n+1)` for every `n` — the
canonical-sum exponential evaluated exactly on the entire lattice `ℕ⁺·logOmega`, by
rung-coupled induction: each rung's exact value feeds the next rung's Hahn-sum half
through the Cauchy product, and the binomial padded census prices each rung. -/
theorem expInf_ladder (n : ℕ) :
    expInf ((((n + 1) : ℕ) : Surreal.{0}) * logOmega)
        (ladder_arg_infinitesimal n) (ladder_arg_pos n).ne' = (1 + ε₀) ^ (n + 1) := by
  induction n with
  | zero =>
    have harg : (((0 + 1 : ℕ) : ℕ) : Surreal.{0}) * logOmega = logOmega := by
      push_cast
      ring
    rw [expInf_congr harg (ladder_arg_infinitesimal 0) (ladder_arg_pos 0).ne'
      logOmega_infinitesimal logOmega_pos.ne', expInf_logOmega_eq]
    have hpow : ((1 : Surreal.{0}) + ε₀) ^ (0 + 1) = 1 + ε₀ := pow_one (1 + ε₀)
    rw [hpow, eps0_def]
  | succ n ih =>
    -- rung `n+1`'s value + the Cauchy product = rung `n+2`'s Hahn-sum half
    have hmul := isHahnSum_expInf_mul (ladder_arg_infinitesimal n) logOmega_infinitesimal
      (ladder_arg_pos n) logOmega_pos
    rw [ih, expInf_logOmega_eq] at hmul
    have hval : ((1 : Surreal.{0}) + ε₀) ^ (n + 1) * (1 + (ω^ (1 : Surreal))⁻¹)
        = (1 + ε₀) ^ (n + 1 + 1) := by
      rw [← eps0_def]
      exact (pow_succ (1 + ε₀) (n + 1)).symm
    have harg : (((n + 1 : ℕ) : ℕ) : Surreal.{0}) * logOmega + logOmega
        = (((n + 1 + 1 : ℕ) : ℕ) : Surreal.{0}) * logOmega := by
      push_cast
      ring
    rw [hval, harg] at hmul
    -- identification at rung `n+2`
    have hstep : expInf ((((n + 1 + 1 : ℕ) : ℕ) : Surreal.{0}) * logOmega)
        (ladder_arg_infinitesimal (n + 1)) (ladder_arg_pos (n + 1)).ne'
        = (1 + ε₀) ^ (n + 2) :=
      ladder_step n (ladder_arg_infinitesimal (n + 1)) (ladder_arg_pos (n + 1)).ne'
        (mk_ladder_arg (n + 1)) hmul
    exact hstep

/-! ### The exact values, birthdays, and the lattice functional equation -/

/-- The ladder in `ω`-power form: `exp ((n+1)·log(1+ω⁻¹)) = (1+ω⁻¹)^(n+1)` on **No**. -/
theorem expInf_ladder' (n : ℕ) :
    expInf ((((n + 1) : ℕ) : Surreal.{0}) * logOmega)
        (ladder_arg_infinitesimal n) (ladder_arg_pos n).ne'
      = (1 + (ω^ (1 : Surreal))⁻¹) ^ (n + 1) := by
  rw [expInf_ladder, eps0_def]

/-- **Every rung is priced exactly**: `birthday (expInf ((n+1)·logOmega)) = ω·(n+1)` —
the exponential of the `(n+1)`-fold argument is born on day `ω·(n+1)`, uniformly in
`n`. Rung 1 recovers the day-`ω` value of `ExpLog`. -/
theorem birthday_expInf_ladder (n : ℕ) :
    (expInf ((((n + 1) : ℕ) : Surreal.{0}) * logOmega)
        (ladder_arg_infinitesimal n) (ladder_arg_pos n).ne').birthday
      = Ω * (((n + 1) : ℕ) : NatOrdinal) := by
  cases n with
  | zero =>
    have harg : (((0 + 1 : ℕ) : ℕ) : Surreal.{0}) * logOmega = logOmega := by
      push_cast
      ring
    rw [expInf_congr harg (ladder_arg_infinitesimal 0) (ladder_arg_pos 0).ne'
      logOmega_infinitesimal logOmega_pos.ne', birthday_expInf_logOmega]
    have h1 : (((0 + 1 : ℕ) : ℕ) : NatOrdinal) = 1 := by norm_num
    rw [h1, mul_one]
  | succ n =>
    refine le_antisymm ?_ ?_
    · rw [expInf_ladder (n + 1)]
      exact birthday_pow_le (n + 1)
    · have hself := isHahnSum_expInf (ladder_arg_infinitesimal (n + 1))
        (ladder_arg_pos (n + 1)).ne'
      have hv := hself
      rw [expInf_ladder (n + 1)] at hv
      have hlow : Ω * (((n + 2) : ℕ) : NatOrdinal) ≤
          (expInf ((((n + 1 + 1 : ℕ) : ℕ) : Surreal.{0}) * logOmega)
            (ladder_arg_infinitesimal (n + 1)) (ladder_arg_pos (n + 1)).ne').birthday :=
        ladder_lower n (mk_ladder_arg (n + 1)) hv hself
      exact hlow

/-- **THE LATTICE FUNCTIONAL EQUATION**: the exponential functional equation holds
*exactly* between any two points of the lattice `ℕ⁺·logOmega` —
`expInf ((n+1)·logOmega + (m+1)·logOmega) = expInf ((n+1)·logOmega) · expInf ((m+1)·logOmega)`,
both sides being `(1+ω⁻¹)^(n+m+2)`. Infinitely many exact instances of the open
multiplicativity question, settled affirmatively at once. -/
theorem expInf_lattice_add_eq_mul (n m : ℕ) :
    expInf ((((n + 1) : ℕ) : Surreal.{0}) * logOmega + (((m + 1) : ℕ) : Surreal) * logOmega)
        ((ladder_arg_infinitesimal n).add (ladder_arg_infinitesimal m))
        (add_pos (ladder_arg_pos n) (ladder_arg_pos m)).ne' =
      expInf ((((n + 1) : ℕ) : Surreal.{0}) * logOmega)
          (ladder_arg_infinitesimal n) (ladder_arg_pos n).ne' *
        expInf ((((m + 1) : ℕ) : Surreal.{0}) * logOmega)
          (ladder_arg_infinitesimal m) (ladder_arg_pos m).ne' := by
  have harg : (((n + 1) : ℕ) : Surreal.{0}) * logOmega + (((m + 1) : ℕ) : Surreal) * logOmega
      = (((n + m + 1 + 1 : ℕ) : ℕ) : Surreal.{0}) * logOmega := by
    push_cast
    ring
  rw [expInf_congr harg
    ((ladder_arg_infinitesimal n).add (ladder_arg_infinitesimal m))
    (add_pos (ladder_arg_pos n) (ladder_arg_pos m)).ne'
    (ladder_arg_infinitesimal (n + m + 1)) (ladder_arg_pos (n + m + 1)).ne',
    expInf_ladder (n + m + 1), expInf_ladder n, expInf_ladder m]
  rw [← pow_add]
  congr 1
  omega

end Surreal

end
