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
# The first exact functional equation instance: `exp(σ + σ) = exp σ · exp σ`

Whether the canonical-sum exponential is multiplicative — `expInf (ε + δ) =
expInf ε · expInf δ` — is the repo's sharpest open question about `expInf` as a
function (`Infinity.ExpMul` proved the law *modulo domination*;
`Infinity.BirthdayHahn` reduced exactness to a birthday inequality). This file proves
the **first exact instance**, at `ε = δ = logOmega` (the canonical logarithm of
`1 + ω⁻¹` from `Infinity.ExpLog`):

* `expInf_add_logOmega_eq_mul` :
  **`expInf (logOmega + logOmega) = expInf logOmega · expInf logOmega`** — both sides
  exactly `(1 + ω⁻¹)² = 1 + 2ω⁻¹ + ω⁻²`.

The route is the discovery that makes this cheap: **go up by squaring, not down by
roots**. The phase-log plan for the fibre instance went through exact square roots
(`√(1+ω⁻¹)`, needing real-closedness); instead, squaring the one banked exact value
`expInf logOmega = 1 + ω⁻¹` is exact *field algebra*, and the whole burden moves to a
birthday census around the product — which is precisely what `Infinity.MonomialCensus`
just made available. Three banked results snap together:

1. **The candidate is a Hahn sum for free**: `isHahnSum_expInf_mul` (`ExpMul`) says
   `expInf logOmega · expInf logOmega` is a Hahn sum of the exponential series at
   `logOmega + logOmega`; rewriting by `expInf_logOmega_eq` (`ExpLog`) identifies it as
   `(1 + ω⁻¹)²`. No new polynomial identities, no composition estimates.
2. **The upper bound is a grid price**: `(1+ω⁻¹)² = 1 + 2ω⁻¹ + ω⁻²` is a level-`2`
   grid point of the *padded census series* `1 + 2ω⁻¹ + ω⁻² + ω⁻³ + ω⁻⁴ + ⋯`
   (`fibreCoeff = (1,2,1,1,1,…)`, all coefficients nonzero dyadics), so
   `birthday ((1+ω⁻¹)²) ≤ ω·2` by the general level pack
   (`birthday_monoS_add_dyadic_mul_le`).
3. **The lower bound is the monomial tube theorem**: every Hahn sum `z` of the
   exponential series at `logOmega + logOmega` lies strictly inside every scale of the
   halo of `(1+ω⁻¹)²`, hence sits at distance-class exactly `ω⁻³` from the padded
   series' canonical sum `w`; if `z` were born before day `ω·2`, the tube theorem
   (`mono_eq_monoS_of_birthday_lt_of_mk_lt`, block `B = 0`) would force
   `z = 1 + 2ω⁻¹` — a point at distance-class `ω⁻²` from `(1+ω⁻¹)²`, contradicting
   halo strictness. So **every** Hahn sum of the series is born at or after day `ω·2`
   (`omega_mul_two_le_birthday_of_isHahnSum_expSq`).

The identification closes through `expInf_add_eq_mul_iff` (`BirthdayHahn`). The padded
series is a genuinely new census instrument: the tube machinery demands nonzero
coefficients, and a finite dyadic polynomial is *not* a Hahn sum of any such series —
but it **is** a grid point at every level of a padded one, which lets the tube around
the padded sum police the polynomial's halo.

Corollaries:

* `expInf_add_logOmega_eq` / `expInf_add_logOmega_eq'` : **the second exact exponential
  value** — `expInf (logOmega + logOmega) = (1+ω⁻¹)² = 1 + 2ω⁻¹ + ω⁻²`. The first was
  born on day `ω`; this one on day `ω·2`.
* `birthday_expInf_add_logOmega` : `birthday (expInf (logOmega + logOmega)) = ω·2`
  **exactly** — doubling the argument of the exponential doubles the birthday block.
  The first exact `expInf` birthday beyond day `ω`.
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

private theorem two_cast : ((2 : Dyadic) : Surreal) = 2 := by
  have h : ((2 : Dyadic) : Surreal) = (((2 : ℕ) : Dyadic) : Surreal) := by norm_num
  rw [h, dyadic_cast_natCast]
  norm_num

private theorem mk_pow_congr' {a b : Surreal}
    (h : ArchimedeanClass.mk a = ArchimedeanClass.mk b) (n : ℕ) :
    ArchimedeanClass.mk (a ^ n) = ArchimedeanClass.mk (b ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, ih, h]

/-! ### The doubled logarithm and its series scales -/

/-- The doubled argument has the class of `ω⁻¹`: adding a surreal to itself preserves
its Archimedean class. -/
private theorem mk_sigma :
    ArchimedeanClass.mk (logOmega + logOmega : Surreal.{0}) = ArchimedeanClass.mk ε₀ := by
  have hmm : ArchimedeanClass.mk (logOmega + logOmega : Surreal.{0}) =
      ArchimedeanClass.mk (logOmega : Surreal.{0}) := by
    refine le_antisymm ?_ ?_
    · rw [ArchimedeanClass.mk_le_mk]
      refine ⟨1, ?_⟩
      rw [one_nsmul, ← two_mul, abs_mul, abs_two]
      nlinarith [abs_nonneg (logOmega : Surreal.{0})]
    · rw [ArchimedeanClass.mk_le_mk]
      refine ⟨2, ?_⟩
      rw [two_nsmul]
      exact abs_add_le _ _
  rw [hmm, mk_logOmega, eps0_def]

/-- The `n`-th term of the exponential series at `logOmega + logOmega` has exactly the
scale `ω⁻ⁿ`. -/
private theorem mk_sigma_term (n : ℕ) :
    ArchimedeanClass.mk ((logOmega + logOmega : Surreal.{0}) ^ n /
        ((n.factorial : ℕ) : Surreal)) = ArchimedeanClass.mk (ε₀ ^ n) := by
  rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero]
  exact mk_pow_congr' mk_sigma n

/-! ### The candidate value is a Hahn sum — for free, by the Cauchy product -/

/-- **The product of the exact values is a Hahn sum of the doubled series**: by the
Cauchy product (`Infinity.ExpMul`) and the exact evaluation `expInf logOmega = 1 + ω⁻¹`
(`Infinity.ExpLog`), the square `(1 + ω⁻¹)·(1 + ω⁻¹)` satisfies every domination
equation of the exponential series at `logOmega + logOmega`. -/
theorem isHahnSum_expSq_v :
    IsHahnSum
      (fun k ↦ (logOmega + logOmega : Surreal.{0}) ^ k / ((k.factorial : ℕ) : Surreal))
      ((1 + ε₀) * (1 + ε₀)) := by
  have h := isHahnSum_expInf_mul logOmega_infinitesimal logOmega_infinitesimal
    logOmega_pos logOmega_pos
  rwa [expInf_logOmega_eq] at h

/-- **Halo strictness**: every Hahn sum of the exponential series at
`logOmega + logOmega` lies strictly inside every `ω`-power scale of the halo of
`(1 + ω⁻¹)²`. -/
theorem mk_pow_lt_mk_sub_of_isHahnSum_expSq {z : Surreal.{0}}
    (hz : IsHahnSum
      (fun k ↦ (logOmega + logOmega) ^ k / ((k.factorial : ℕ) : Surreal)) z)
    (n : ℕ) :
    ArchimedeanClass.mk (ε₀ ^ n) < ArchimedeanClass.mk (z - (1 + ε₀) * (1 + ε₀)) := by
  have h : ArchimedeanClass.mk ((logOmega + logOmega : Surreal.{0}) ^ (n + 1) /
      (((n + 1).factorial : ℕ) : Surreal)) ≤
        ArchimedeanClass.mk (z - (1 + ε₀) * (1 + ε₀)) :=
    IsHahnSum.mk_sub_le hz isHahnSum_expSq_v (n + 1)
  rw [mk_sigma_term (n + 1)] at h
  exact (mk_pow_lt_mk_pow_succ eps0_inf eps0_pos' n).trans_le h

/-! ### The padded census series `1 + 2ω⁻¹ + ω⁻² + ω⁻³ + ⋯` -/

/-- The padded census coefficients `(1, 2, 1, 1, 1, …)`: the expansion of `(1+ω⁻¹)²`
padded with a tail of ones, so that every coefficient is a nonzero dyadic and the
monomial tube census applies. -/
def fibreCoeff : ℕ → Dyadic := fun k ↦ if k = 1 then 2 else 1

theorem fibreCoeff_ne_zero (k : ℕ) : fibreCoeff k ≠ 0 := by
  unfold fibreCoeff
  split
  · exact two_ne_zero
  · exact one_ne_zero

private theorem monoTerm_fibre_zero : monoTerm fibreCoeff 0 = 1 := by
  show ((fibreCoeff 0 : Dyadic) : Surreal) * ε₀ ^ 0 = 1
  rw [show fibreCoeff 0 = 1 from rfl, one_cast, pow_zero, mul_one]

private theorem monoTerm_fibre_one : monoTerm fibreCoeff 1 = 2 * ε₀ := by
  show ((fibreCoeff 1 : Dyadic) : Surreal) * ε₀ ^ 1 = 2 * ε₀
  rw [show fibreCoeff 1 = 2 from rfl, two_cast, pow_one]

private theorem monoTerm_fibre_two : monoTerm fibreCoeff 2 = ε₀ ^ 2 := by
  show ((fibreCoeff 2 : Dyadic) : Surreal) * ε₀ ^ 2 = ε₀ ^ 2
  rw [show fibreCoeff 2 = 1 from rfl, one_cast, one_mul]

private theorem monoS_fibre_two : monoS fibreCoeff 2 = 1 + 2 * ε₀ := by
  have h : monoS fibreCoeff 2 = monoS fibreCoeff 1 + monoTerm fibreCoeff 1 :=
    partialSum_succ (monoTerm fibreCoeff) 1
  have h1 : monoS fibreCoeff 1 = 1 := by
    rw [monoS_one, show fibreCoeff 0 = 1 from rfl, one_cast]
  rw [h, h1, monoTerm_fibre_one]

private theorem monoS_fibre_three : monoS fibreCoeff 3 = 1 + 2 * ε₀ + ε₀ ^ 2 := by
  have h : monoS fibreCoeff 3 = monoS fibreCoeff 2 + monoTerm fibreCoeff 2 :=
    partialSum_succ (monoTerm fibreCoeff) 2
  rw [h, monoS_fibre_two, monoTerm_fibre_two]

/-! ### The upper bound: the square is a grid point priced at `ω·2` -/

/-- **The grid price of the square**: `(1+ω⁻¹)² = 1 + 2ω⁻¹ + ω⁻²` is the level-`2`
grid point `T₂ + 1·ω⁻²` of the padded series, so it is born by day `ω·2`. -/
theorem birthday_expSq_le :
    (((1 : Surreal.{0}) + ε₀) * (1 + ε₀)).birthday ≤ Ω * ((2 : ℕ) : NatOrdinal) := by
  have h : (monoS fibreCoeff 2 + ((1 : Dyadic) : Surreal) * ε₀ ^ 2).birthday
      ≤ Ω * ((2 : ℕ) : NatOrdinal) + ((Dyadic.hgt (1 : Dyadic) - 1 : ℕ) : NatOrdinal) :=
    birthday_monoS_add_dyadic_mul_le fibreCoeff_ne_zero 1 (t := 1) one_ne_zero
  have hval : monoS fibreCoeff 2 + ((1 : Dyadic) : Surreal) * ε₀ ^ 2 =
      (1 + ε₀) * (1 + ε₀) := by
    rw [monoS_fibre_two, one_cast, one_mul]
    ring
  have hhgt : ((Dyadic.hgt (1 : Dyadic) - 1 : ℕ) : NatOrdinal) = 0 := by
    rw [Dyadic.hgt_one]
    norm_num
  rw [hval, hhgt, add_zero] at h
  exact h

/-! ### The lower bound: the tube theorem polices the halo -/

/-- The block-`0` tube theorem along the padded series, with the numerals normalized:
a surreal born before day `ω·2` at distance strictly finer than class `ω⁻¹` from a Hahn
sum of the padded series is the partial sum `T₂`. -/
private theorem tube_force {w z : Surreal.{0}} (hw : IsHahnSum (monoTerm fibreCoeff) w)
    (hdist : ArchimedeanClass.mk (ε₀ ^ 1) < ArchimedeanClass.mk (z - w))
    (hb : z.birthday < Ω * ((2 : ℕ) : NatOrdinal)) : z = monoS fibreCoeff 2 :=
  mono_eq_monoS_of_birthday_lt_of_mk_lt fibreCoeff_ne_zero hw 0 hdist hb

private theorem mk_pow_one_lt_three :
    ArchimedeanClass.mk (ε₀ ^ 1) < ArchimedeanClass.mk (ε₀ ^ 3) := by
  have ha : ArchimedeanClass.mk (ε₀ ^ 1) < ArchimedeanClass.mk (ε₀ ^ 2) :=
    mk_pow_lt_mk_pow_succ eps0_inf eps0_pos' 1
  have hb : ArchimedeanClass.mk (ε₀ ^ 2) < ArchimedeanClass.mk (ε₀ ^ 3) :=
    mk_pow_lt_mk_pow_succ eps0_inf eps0_pos' 2
  exact ha.trans hb

/-- **Every Hahn sum of the doubled exponential series is born at or after day `ω·2`.**
Such a sum `z` sits at distance-class exactly `ω⁻³` from the canonical sum `w` of the
padded census series (the halo of `(1+ω⁻¹)²` is strictly finer than every scale, and
`(1+ω⁻¹)² = T₃` misses `w` by the class of the first padding term). If `z` were born
before day `ω·2`, the monomial tube theorem at block `0` would force `z = T₂ = 1+2ω⁻¹`,
which sits at distance-class `ω⁻²` from `(1+ω⁻¹)²` — contradicting halo strictness. -/
theorem omega_mul_two_le_birthday_of_isHahnSum_expSq {z : Surreal.{0}}
    (hz : IsHahnSum
      (fun k ↦ (logOmega + logOmega) ^ k / ((k.factorial : ℕ) : Surreal)) z) :
    Ω * ((2 : ℕ) : NatOrdinal) ≤ z.birthday := by
  by_contra hcon
  rw [not_le] at hcon
  set w := hahnSum (monoTerm_strict_dominating fibreCoeff_ne_zero) with hwdef
  have hw : IsHahnSum (monoTerm fibreCoeff) w := isHahnSum_hahnSum _
  -- `z` is at distance-class exactly `ω⁻³` from the padded canonical sum `w`
  have h3 : ArchimedeanClass.mk (monoS fibreCoeff 3 - w) = ArchimedeanClass.mk (ε₀ ^ 3) :=
    mk_monoS_sub fibreCoeff_ne_zero hw 3
  have hv3 : ArchimedeanClass.mk (ε₀ ^ 3) <
      ArchimedeanClass.mk (z - (1 + ε₀) * (1 + ε₀)) :=
    mk_pow_lt_mk_sub_of_isHahnSum_expSq hz 3
  have hsplit : z - w = (monoS fibreCoeff 3 - w) + (z - (1 + ε₀) * (1 + ε₀)) := by
    rw [monoS_fibre_three]
    ring
  have hlt : ArchimedeanClass.mk (monoS fibreCoeff 3 - w) <
      ArchimedeanClass.mk (z - (1 + ε₀) * (1 + ε₀)) := by
    rw [h3]
    exact hv3
  have hzw : ArchimedeanClass.mk (z - w) = ArchimedeanClass.mk (ε₀ ^ 3) := by
    rw [hsplit, ArchimedeanClass.mk_add_eq_mk_left hlt, h3]
  -- the tube theorem at block `B = 0` forces `z` to be the partial sum `1 + 2ω⁻¹`
  have hdist : ArchimedeanClass.mk (ε₀ ^ 1) < ArchimedeanClass.mk (z - w) := by
    rw [hzw]
    exact mk_pow_one_lt_three
  have heq : z = monoS fibreCoeff 2 := tube_force hw hdist hcon
  -- contradiction with halo strictness at scale `2`
  have h2 := mk_pow_lt_mk_sub_of_isHahnSum_expSq hz 2
  rw [heq, monoS_fibre_two] at h2
  have hval : (1 : Surreal.{0}) + 2 * ε₀ - (1 + ε₀) * (1 + ε₀) = -ε₀ ^ 2 := by ring
  rw [hval, ArchimedeanClass.mk_neg] at h2
  exact lt_irrefl _ h2

/-! ### The first exact functional equation instance -/

/-- **THE FIRST EXACT FUNCTIONAL EQUATION INSTANCE**:
`expInf (logOmega + logOmega) = expInf logOmega · expInf logOmega` — the canonical-sum
exponential is multiplicative at `(logOmega, logOmega)`, *exactly*. The product is
`(1+ω⁻¹)²`, born by day `ω·2` (the grid price), while every Hahn sum of the exponential
series at the doubled argument is born at or after day `ω·2` (the tube theorem through
the padded census series); so the product is the birthday-minimal Hahn sum — the
canonical value. -/
theorem expInf_add_logOmega_eq_mul :
    expInf (logOmega + logOmega : Surreal.{0})
        (logOmega_infinitesimal.add logOmega_infinitesimal)
        (add_pos logOmega_pos logOmega_pos).ne' =
      expInf logOmega logOmega_infinitesimal logOmega_pos.ne' *
        expInf logOmega logOmega_infinitesimal logOmega_pos.ne' := by
  refine (expInf_add_eq_mul_iff logOmega_infinitesimal logOmega_infinitesimal
    logOmega_pos logOmega_pos).2 ?_
  intro z hz
  have hb : (expInf logOmega logOmega_infinitesimal logOmega_pos.ne' *
      expInf logOmega logOmega_infinitesimal logOmega_pos.ne').birthday ≤
        Ω * ((2 : ℕ) : NatOrdinal) := by
    rw [expInf_logOmega_eq]
    exact birthday_expSq_le
  exact hb.trans (omega_mul_two_le_birthday_of_isHahnSum_expSq hz)

/-- **The second exact exponential value**: `expInf (logOmega + logOmega) = (1+ω⁻¹)²`. -/
theorem expInf_add_logOmega_eq :
    expInf (logOmega + logOmega : Surreal.{0})
        (logOmega_infinitesimal.add logOmega_infinitesimal)
        (add_pos logOmega_pos logOmega_pos).ne' =
      (1 + (ω^ (1 : Surreal))⁻¹) * (1 + (ω^ (1 : Surreal))⁻¹) := by
  rw [expInf_add_logOmega_eq_mul, expInf_logOmega_eq]

/-- The second exact exponential value, expanded: `exp (2·log(1+ω⁻¹)) = 1 + 2ω⁻¹ + ω⁻²`
on **No**. -/
theorem expInf_add_logOmega_eq' :
    expInf (logOmega + logOmega : Surreal.{0})
        (logOmega_infinitesimal.add logOmega_infinitesimal)
        (add_pos logOmega_pos logOmega_pos).ne' =
      1 + 2 * (ω^ (1 : Surreal))⁻¹ + ((ω^ (1 : Surreal))⁻¹) ^ 2 := by
  rw [expInf_add_logOmega_eq]
  ring

/-- **Doubling the argument doubles the block**:
`birthday (expInf (logOmega + logOmega)) = ω·2` exactly — the first exact `expInf`
birthday beyond day `ω`. Upper bound: the value is the grid point `1 + 2ω⁻¹ + ω⁻²`.
Lower bound: it is itself a Hahn sum of the doubled series, so the tube theorem
applies to it. -/
theorem birthday_expInf_add_logOmega :
    (expInf (logOmega + logOmega : Surreal.{0})
        (logOmega_infinitesimal.add logOmega_infinitesimal)
        (add_pos logOmega_pos logOmega_pos).ne').birthday = Ω * ((2 : ℕ) : NatOrdinal) := by
  refine le_antisymm ?_ ?_
  · rw [expInf_add_logOmega_eq]
    exact birthday_expSq_le
  · exact omega_mul_two_le_birthday_of_isHahnSum_expSq
      (isHahnSum_expInf (logOmega_infinitesimal.add logOmega_infinitesimal)
        (add_pos logOmega_pos logOmega_pos).ne')

end Surreal

end
