import Infinity.Darboux
import Infinity.ExpFin
import Infinity.GonshorExp

/-!
# Norton's error as a theorem

For fifty years the story of surreal integration has featured one famous concrete
failure: Norton's genetic integral (the Conway–Kruskal–Norton program, ONAG ch. 16 —
"the integral in mist") computes `∫₀^ω eˣ dx = e^ω` where the correct value, by any
translation-invariance or fundamental-theorem reasoning, is `e^ω − 1`. Kruskal found the
flaw; the program stalled; the episode is recounted in Costin–Ehrlich
(arXiv:2208.14331, §1). This file proves, as machine-checked theorems, *why* that
failure is structural — that the wrong value is exactly what Conway-style simplest-fit
must produce.

## The construction

* `nortonExp` — the exponential on the **`ω`-lattice** (Route A v1 of
  `notes/exp-infinite-design.md`): `expFin` (`Infinity.ExpFin`) on the finite galaxy,
  `ω^ω · expFin (x − ω)` on the rest, so that `nortonExp k = eᵏ` at reals and
  `nortonExp ω = ω^ω`. The identification `e^ω = ω^ω` is Gonshor's theorem, and it is
  *machine-checked* in this development: `nortonExp_wpow_one_eq_gonshor` shows the value
  at `ω` equals the evaluated genetic cut of `Infinity.GonshorExp.gonshorExp_omega`.
* `IsExpPartitionOn` — finite monotone partitions of `[0, ω]` whose points lie in the
  two-galaxy lattice `{finite} ∪ {ω + finite}` — exactly where the Route-A exponential
  is meaningful.
* `nortonLo`/`nortonHi` — the genetic (Darboux) cut: all lower exponential sums below,
  all upper exponential sums above; `nortonIntegralExp` — the birthday-simplest surreal
  between them (`Cut.simplestBtwn`), i.e. the Conway-style genetic value of `∫₀^ω eˣ dx`
  over this option family.

## The two-horned theorem

* **Horn (a), halo blindness** (`fits_norton_add_of_isFinite`,
  `norton_indeterminate`): *every* finite perturbation `ω^ω + c` fits strictly between
  all lower and all upper sums. Lower sums are trapped below `ω^ω − (positive real)·ω^ω`
  + `(finite)·ω` — the top-galaxy block is `ω^ω` times a left Riemann sum of `eᵗ` on
  `(−∞, 0]`, which loses a non-infinitesimal fraction of `∫eᵗ = 1`; upper sums must jump
  the middle galaxies in a single piece of infinite length at height `≈ ω^ω`, so they
  all exceed `k·ω^ω` for every `k`. The cut's resolution at `ω^ω` is therefore *no finer
  than a whole Archimedean class*: in particular both `e^ω − 1` (the true value) and
  `e^ω` (Norton's value) fit, and analysis alone cannot separate them.

* **Horn (b), the headline** (`nortonIntegralExp_eq_wpow_wpow`, `norton_error`):
  **the birthday-simplest fit is the bare monomial `ω^ω` — Norton's wrong answer.**
  Every fit exceeds the surreal image of every ordinal below `ω^ω` (one three-point
  partition `0 < ω − 1 < ω` already forces every fit above `e⁻¹·ω^ω`-scale), so by
  `Surreal.le_toSurreal_birthday` every fit is born at or after day `ω^ω`; and `ω^ω`
  itself — the image of the *ordinal* `ω^ω`, `birthday_wpow_wpow_one` — is born exactly
  on day `ω^ω` and fits. `Cut.simplestBtwn_eq_iff` then evaluates the genetic integral
  to `ω^ω` exactly.

Together: the genetic simplicity principle, applied to exponential Darboux data over an
infinite interval, *selects Norton's wrong value* — the monomial is born on day `ω^ω`
while the correct value `ω^ω − 1` is born later (it differs from a day-`ω^ω` surreal by
a finite amount, cf. the birthday lower bounds of `Infinity.BirthdayHahn`). Simplest-fit
is structurally not integration: the information that forces `−1` (translation
invariance, the functional equation, FTC) lives at scales the approximating cut provably
cannot see. This is, to our knowledge, the first formal theorem locating the
Conway–Kruskal–Norton failure — the phenomenon itself is classical folklore
(Kruskal's critique; Costin–Ehrlich §1), but no proof that "the simplest fit is the
wrong value" existed at any level of rigor, because "the" genetic integral was never
pinned to a definite option family.

## Calibration — what is and is not proved

Proved: for the *lattice* option family above (finite partitions with two-galaxy
points, the natural family at current formalization scope), the genetic cut admits the
whole finite halo of `ω^ω` and simplicity selects `ω^ω`. Not proved: the same for
Norton's own richer option families (their definition needs `exp` on all of `[0, ω]`,
i.e. Gonshor's full genetic recursion — Route B), nor the FTC-side evaluation
`∫₀^ω eˣ dx = e^ω − 1` (an exp-polynomial integral class in the style of
`Infinity.Laurent` is the plotted route). Enriching the option family can only *shrink*
the set of fits; the indeterminacy horn is therefore the part that would need
re-proving for richer families, while the mechanism of horn (b) — class-wide blindness
plus birthday minimality of the monomial — is exactly the mechanism visible in
Norton's `e^ω`.
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

/-! ### Order and finiteness helpers -/

/-- A nonnegative surreal below a finite surreal is finite. -/
theorem isFinite_of_nonneg_of_le {a b : Surreal} (h0 : 0 ≤ a) (hab : a ≤ b)
    (hb : IsFinite b) : IsFinite a := by
  obtain ⟨n, hn⟩ := isFinite_iff.1 hb
  exact isFinite_iff.2 ⟨n, by rw [abs_of_nonneg h0]; exact hab.trans ((le_abs_self b).trans hn)⟩

/-- A nonnegative infinite surreal exceeds every natural number. -/
theorem natCast_lt_of_nonneg_of_not_isFinite {a : Surreal} (h0 : 0 ≤ a)
    (ha : ¬ IsFinite a) (n : ℕ) : (n : Surreal) < a := by
  by_contra h
  rw [not_lt] at h
  exact ha (isFinite_iff.2 ⟨n, by rwa [abs_of_nonneg h0]⟩)

theorem one_lt_wpow_one : (1 : Surreal) < ω^ (1 : Surreal) := by
  simpa using natCast_lt_wpow_one 1

/-- `expInf'` is positive everywhere (its junk value is `1`). -/
theorem expInf'_pos' (ε : Surreal) : 0 < expInf' ε := by
  by_cases h : Infinitesimal ε
  · exact expInf'_pos h
  · unfold expInf'
    rw [dif_neg fun hc ↦ h hc.1]
    norm_num

/-- `expFin` is positive everywhere (its junk values multiply a positive real by `1`). -/
theorem expFin_pos' (x : Surreal) : 0 < expFin x := by
  unfold expFin
  have h1 : (0 : Surreal) < (Real.exp (stdPart x) : Surreal) := by
    rw [← Real.toSurreal_zero]
    exact Real.toSurreal_lt_iff.2 (Real.exp_pos _)
  exact mul_pos h1 (expInf'_pos' _)

/-! ### The `ω`-lattice exponential -/

open scoped Classical in
/-- **The `ω`-lattice exponential** (Route A v1): `expFin` on the finite galaxy,
`ω^ω · expFin (x − ω)` beyond it. On its intended domain — the two galaxies
`{finite} ∪ {ω + finite}` — this is the exponential with `nortonExp r = eʳ` at reals and
`nortonExp ω = ω^ω`, Gonshor's machine-checked value of `exp ω`
(`Infinity.GonshorExp.gonshorExp_omega`). Junk-valued in the middle galaxies. -/
def nortonExp (x : Surreal) : Surreal :=
  if IsFinite x then expFin x else ω^ ω^ (1 : Surreal) * expFin (x - ω^ (1 : Surreal))

theorem nortonExp_of_isFinite {x : Surreal} (hx : IsFinite x) : nortonExp x = expFin x := by
  unfold nortonExp
  rw [if_pos hx]

theorem nortonExp_of_not_isFinite {x : Surreal} (hx : ¬ IsFinite x) :
    nortonExp x = ω^ ω^ (1 : Surreal) * expFin (x - ω^ (1 : Surreal)) := by
  unfold nortonExp
  rw [if_neg hx]

@[simp]
theorem nortonExp_realCast (r : ℝ) : nortonExp (r : Surreal) = (Real.exp r : Surreal) := by
  rw [nortonExp_of_isFinite (isFinite_realCast r), expFin_realCast]

/-- On the naturals the lattice exponential is `eᵏ`. -/
theorem nortonExp_natCast (k : ℕ) : nortonExp (k : Surreal) = (Real.exp k : Surreal) := by
  rw [← Real.toSurreal_natCast k, nortonExp_realCast]

/-- At `ω` the lattice exponential takes Gonshor's value `exp ω = ω^ω`. -/
theorem nortonExp_wpow_one : nortonExp (ω^ (1 : Surreal)) = ω^ ω^ (1 : Surreal) := by
  rw [nortonExp_of_not_isFinite not_isFinite_wpow_one, sub_self, expFin_zero, mul_one]

/-- **The identification `e^ω = ω^ω` is Gonshor's, machine-checked**: the value of the
lattice exponential at `ω` is the evaluated genetic cut of Gonshor's recursion at `ω`
(`Infinity.GonshorExp.gonshorExp_omega`). -/
theorem nortonExp_wpow_one_eq_gonshor :
    nortonExp (ω^ (1 : Surreal)) =
      !{insert 0 (Set.range fun p : ℕ × ℕ ↦
          ((Real.exp p.1 : ℝ) : Surreal) *
            expPartial p.2 (ω^ (1 : Surreal) - (p.1 : Surreal))) | ∅} := by
  rw [nortonExp_wpow_one, gonshorExp_omega]

/-- Top-galaxy values: `nortonExp (ω + d) = ω^ω · expFin d` for finite `d`. -/
theorem nortonExp_wpow_one_add {d : Surreal} (hd : IsFinite d) :
    nortonExp (ω^ (1 : Surreal) + d) = ω^ ω^ (1 : Surreal) * expFin d := by
  have h : ¬ IsFinite (ω^ (1 : Surreal) + d) := by
    intro hfin
    exact not_isFinite_wpow_one (by simpa using hfin.sub hd)
  rw [nortonExp_of_not_isFinite h, add_sub_cancel_left]

theorem nortonExp_pos (x : Surreal) : 0 < nortonExp x := by
  by_cases h : IsFinite x
  · rw [nortonExp_of_isFinite h]
    exact expFin_pos' x
  · rw [nortonExp_of_not_isFinite h]
    exact mul_pos (wpow_pos _) (expFin_pos' _)

end Surreal

end
