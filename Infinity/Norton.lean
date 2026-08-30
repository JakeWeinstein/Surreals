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

/-! ### Partition helpers -/

/-- The points of a partition are monotone in the index. -/
theorem IsPartitionOn.mono {x : ℕ → Surreal} {n : ℕ} {a b : Surreal}
    (hp : IsPartitionOn x n a b) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) : x i ≤ x j := by
  obtain ⟨-, -, hmono⟩ := hp
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => simp
  | succ d ih =>
    have h2 : x (i + d) ≤ x (i + d + 1) := hmono (i + d) (by omega)
    have h1 : x i ≤ x (i + d) := ih (by omega)
    have h3 : i + (d + 1) = (i + d) + 1 := by omega
    rw [h3]
    exact h1.trans h2

/-- Partition points lie above the left endpoint. -/
theorem IsPartitionOn.left_le {x : ℕ → Surreal} {n : ℕ} {a b : Surreal}
    (hp : IsPartitionOn x n a b) {i : ℕ} (hi : i ≤ n) : a ≤ x i := by
  rw [← hp.1]
  exact hp.mono (Nat.zero_le i) hi

/-- Partition points lie below the right endpoint. -/
theorem IsPartitionOn.le_right {x : ℕ → Surreal} {n : ℕ} {a b : Surreal}
    (hp : IsPartitionOn x n a b) {i : ℕ} (hi : i ≤ n) : x i ≤ b := by
  rw [← hp.2.1]
  exact hp.mono hi le_rfl

/-! ### Lattice partitions and exponential Darboux sums -/

/-- The two-galaxy `ω`-lattice: the points at which the Route-A exponential is
meaningful. -/
def IsExpLatticePt (x : Surreal) : Prop :=
  IsFinite x ∨ IsFinite (x - ω^ (1 : Surreal))

/-- A monotone partition of `[a, b]` through lattice points. -/
def IsExpPartitionOn (x : ℕ → Surreal) (n : ℕ) (a b : Surreal) : Prop :=
  IsPartitionOn x n a b ∧ ∀ i ≤ n, IsExpLatticePt (x i)

/-- The lower exponential Darboux sum: left tags. -/
def lowerSumExp (x : ℕ → Surreal) (n : ℕ) : Surreal :=
  ∑ i ∈ Finset.range n, nortonExp (x i) * (x (i + 1) - x i)

/-- The upper exponential Darboux sum: right tags. -/
def upperSumExp (x : ℕ → Surreal) (n : ℕ) : Surreal :=
  ∑ i ∈ Finset.range n, nortonExp (x (i + 1)) * (x (i + 1) - x i)

/-- The cut just above all lower exponential Darboux sums on `[0, ω]`. -/
def nortonLo : Cut :=
  ⨆ p : {q : (ℕ → Surreal) × ℕ // IsExpPartitionOn q.1 q.2 0 (ω^ (1 : Surreal))},
    Cut.rightSurreal (lowerSumExp p.1.1 p.1.2)

/-- The cut just below all upper exponential Darboux sums on `[0, ω]`. -/
def nortonHi : Cut :=
  ⨅ p : {q : (ℕ → Surreal) × ℕ // IsExpPartitionOn q.1 q.2 0 (ω^ (1 : Surreal))},
    Cut.leftSurreal (upperSumExp p.1.1 p.1.2)

/-- A surreal fits between the exponential Darboux cuts iff it lies strictly between
every lower and every upper exponential sum. -/
theorem fits_norton_iff {z : Surreal} :
    Cut.Fits z nortonLo nortonHi ↔
      ∀ x n, IsExpPartitionOn x n 0 (ω^ (1 : Surreal)) →
        lowerSumExp x n < z ∧ z < upperSumExp x n := by
  rw [Cut.Fits, Set.mem_inter_iff, ← Cut.notMem_left_iff]
  unfold nortonLo nortonHi
  simp only [Cut.left_iSup, Cut.left_iInf, Cut.left_rightSurreal, Cut.left_leftSurreal,
    Set.mem_iUnion, Set.mem_iInter, Set.mem_Iic, Set.mem_Iio, not_exists, not_le]
  constructor
  · rintro ⟨h1, h2⟩ x n hp
    exact ⟨h1 ⟨(x, n), hp⟩, h2 ⟨(x, n), hp⟩⟩
  · intro h
    exact ⟨fun p ↦ (h p.1.1 p.1.2 p.2).1, fun p ↦ (h p.1.1 p.1.2 p.2).2⟩

/-! ### The splitting index of a lattice partition -/

/-- Every lattice partition of `[0, ω]` splits at a last finite point: everything at or
below index `m` is finite, everything above lies in the top galaxy `ω + finite`. -/
theorem exists_split {x : ℕ → Surreal} {n : ℕ}
    (hp : IsExpPartitionOn x n 0 (ω^ (1 : Surreal))) :
    ∃ m < n, (∀ i ≤ m, IsFinite (x i)) ∧
      ∀ i, m < i → i ≤ n → IsFinite (x i - ω^ (1 : Surreal)) ∧ ¬ IsFinite (x i) := by
  classical
  obtain ⟨hpart, hlat⟩ := hp
  have h0fin : IsFinite (x 0) := by rw [hpart.1]; exact isFinite_zero
  have hmfin : IsFinite (x (Nat.findGreatest (fun i ↦ IsFinite (x i)) n)) :=
    Nat.findGreatest_spec (P := fun i ↦ IsFinite (x i)) (Nat.zero_le n) h0fin
  have hnfin : ¬ IsFinite (x n) := by rw [hpart.2.1]; exact not_isFinite_wpow_one
  have hmn : Nat.findGreatest (fun i ↦ IsFinite (x i)) n < n :=
    (Nat.findGreatest_le n).lt_of_ne fun h ↦ hnfin (h ▸ hmfin)
  refine ⟨_, hmn, fun i hi ↦ ?_, fun i hmi hin ↦ ?_⟩
  · exact isFinite_of_nonneg_of_le (hpart.left_le (by omega))
      (hpart.mono hi (by omega)) hmfin
  · have hnot : ¬ IsFinite (x i) := Nat.findGreatest_is_greatest hmi hin
    rcases hlat i hin with h | h
    · exact absurd h hnot
    · exact ⟨h, hnot⟩

/-! ### Upper sums exceed every natural multiple of `ω^ω` -/

/-- **Upper sums are class-wide overshoots**: every upper exponential Darboux sum over
the lattice exceeds `k·ω^ω` for every natural `k`. Any lattice partition must jump the
middle galaxies in a single piece — from its last finite point to a point `ω + finite` —
and that piece contributes (top-galaxy value `≈ ω^ω`) × (infinite length). -/
theorem natCast_mul_lt_upperSumExp {x : ℕ → Surreal} {n : ℕ}
    (hp : IsExpPartitionOn x n 0 (ω^ (1 : Surreal))) (k : ℕ) :
    (k : Surreal) * ω^ ω^ (1 : Surreal) < upperSumExp x n := by
  obtain ⟨m, hmn, hfin, htop⟩ := exists_split hp
  obtain ⟨hD, hnotfin⟩ := htop (m + 1) (by omega) (by omega)
  -- the gap piece has positive infinite length
  have hlen_nonneg : 0 ≤ x (m + 1) - x m := sub_nonneg.2 (hp.1.2.2 m hmn)
  have hlen_inf : ¬ IsFinite (x (m + 1) - x m) := by
    intro hfin'
    have h1 : IsFinite (x (m + 1)) := by
      have h := hfin'.add (hfin m le_rfl)
      simpa using h
    exact hnotfin h1
  -- a rational below the (positive) standard part of the tag factor, and a big natural
  obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (Real.exp_pos (stdPart (x (m + 1) - ω^ (1 : Surreal))))
  have hqR : (0 : ℝ) < (q : ℝ) := hq0
  obtain ⟨N, hN⟩ := exists_nat_gt ((k : ℝ) / (q : ℝ))
  have hkqN : (k : ℝ) < (q : ℝ) * N := by
    rw [div_lt_iff₀ hqR] at hN
    linarith
  -- k < (cast q) · N in the surreals
  have h1 : (k : Surreal) < ((q : ℝ) : Surreal) * (N : Surreal) := by
    have hcast : ((k : ℝ) : Surreal) < (((q : ℝ) * N : ℝ) : Surreal) :=
      Real.toSurreal_lt_iff.2 hkqN
    rwa [Real.toSurreal_mul, Real.toSurreal_natCast, Real.toSurreal_natCast] at hcast
  -- cast q < expFin (x (m+1) − ω)
  have h2 : ((q : ℝ) : Surreal) < expFin (x (m + 1) - ω^ (1 : Surreal)) := by
    refine lt_of_stdPart_lt (isFinite_realCast _) (isFinite_expFin hD) ?_
    rw [stdPart_realCast, stdPart_expFin hD]
    exact hq
  -- N < the gap length
  have h3 : (N : Surreal) < x (m + 1) - x m :=
    natCast_lt_of_nonneg_of_not_isFinite hlen_nonneg hlen_inf N
  -- k < expFin (x (m+1) − ω) · (gap length)
  have h4 : (k : Surreal) < expFin (x (m + 1) - ω^ (1 : Surreal)) * (x (m + 1) - x m) := by
    have ha : ((q : ℝ) : Surreal) * (N : Surreal) ≤
        expFin (x (m + 1) - ω^ (1 : Surreal)) * (N : Surreal) :=
      mul_le_mul_of_nonneg_right h2.le (Nat.cast_nonneg N)
    have hb : expFin (x (m + 1) - ω^ (1 : Surreal)) * (N : Surreal) <
        expFin (x (m + 1) - ω^ (1 : Surreal)) * (x (m + 1) - x m) :=
      mul_lt_mul_of_pos_left h3 (expFin_pos' _)
    linarith
  -- multiply through by ω^ω and pass to the gap term of the upper sum
  have h5 : (k : Surreal) * ω^ ω^ (1 : Surreal) <
      nortonExp (x (m + 1)) * (x (m + 1) - x m) := by
    rw [nortonExp_of_not_isFinite hnotfin]
    calc (k : Surreal) * ω^ ω^ (1 : Surreal)
        < (expFin (x (m + 1) - ω^ (1 : Surreal)) * (x (m + 1) - x m)) *
            ω^ ω^ (1 : Surreal) := mul_lt_mul_of_pos_right h4 (wpow_pos _)
      _ = ω^ ω^ (1 : Surreal) * expFin (x (m + 1) - ω^ (1 : Surreal)) *
            (x (m + 1) - x m) := by ring
  have h6 : nortonExp (x (m + 1)) * (x (m + 1) - x m) ≤ upperSumExp x n := by
    refine Finset.single_le_sum (f := fun i ↦ nortonExp (x (i + 1)) * (x (i + 1) - x i))
      (fun i hi ↦ ?_) (Finset.mem_range.2 hmn)
    exact mul_nonneg (nortonExp_pos _).le
      (sub_nonneg.2 (hp.1.2.2 i (Finset.mem_range.1 hi)))
  exact h5.trans_le h6

/-! ### Lower sums are trapped below the finite halo of `ω^ω` -/

/-- The exponential left-Riemann telescoping bound over the reals: for any real nodes
`d`, the tagged sum `Σ e^{dᵢ}(dᵢ₊₁ − dᵢ)` over `[a, b)` is at most `e^{d_b} − e^{d_a}`.
(No monotonicity is needed: `1 + t ≤ eᵗ` holds for all real `t`.) -/
private theorem real_exp_riemann_le (d : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, Real.exp (d i) * (d (i + 1) - d i) ≤
      Real.exp (d b) - Real.exp (d a) := by
  have hstep : ∀ i, Real.exp (d i) * (d (i + 1) - d i) ≤
      Real.exp (d (i + 1)) - Real.exp (d i) := by
    intro i
    have h := Real.add_one_le_exp (d (i + 1) - d i)
    have hpos := Real.exp_pos (d i)
    have h2 : Real.exp (d i) * (d (i + 1) - d i + 1) ≤
        Real.exp (d i) * Real.exp (d (i + 1) - d i) :=
      mul_le_mul_of_nonneg_left h hpos.le
    rw [← Real.exp_add] at h2
    have h3 : d i + (d (i + 1) - d i) = d (i + 1) := by ring
    rw [h3] at h2
    nlinarith
  calc ∑ i ∈ Finset.Ico a b, Real.exp (d i) * (d (i + 1) - d i)
      ≤ ∑ i ∈ Finset.Ico a b, (Real.exp (d (i + 1)) - Real.exp (d i)) :=
        Finset.sum_le_sum fun i _ ↦ hstep i
    _ = Real.exp (d b) - Real.exp (d a) := by
        have h1 := Finset.sum_Ico_consecutive
          (fun i ↦ Real.exp (d (i + 1)) - Real.exp (d i)) (Nat.zero_le a) hab
        have h2 := Finset.sum_range_sub (fun i ↦ Real.exp (d i)) a
        have h3 := Finset.sum_range_sub (fun i ↦ Real.exp (d i)) b
        rw [Finset.range_eq_Ico] at h2 h3
        linarith

/-- **Lower sums are trapped**: every lower exponential Darboux sum over the lattice
lies strictly below `ω^ω + c` for *every* finite `c`. The finite-galaxy block
contributes at most `(finite)·ω`; the top-galaxy block is `ω^ω` times a surreal whose
standard part is a left Riemann sum of `eᵗ` over `(−∞, 0]`, hence loses at least the
non-infinitesimal fraction `e^{st(x₍ₘ₊₁₎ − ω)}` of `1`. -/
theorem lowerSumExp_lt_wpow_add {x : ℕ → Surreal} {n : ℕ}
    (hp : IsExpPartitionOn x n 0 (ω^ (1 : Surreal))) {c : Surreal} (hc : IsFinite c) :
    lowerSumExp x n < ω^ ω^ (1 : Surreal) + c := by
  obtain ⟨m, hmn, hfin, htop⟩ := exists_split hp
  have hxle : ∀ i ≤ n, x i ≤ ω^ (1 : Surreal) := fun i hi ↦ hp.1.le_right hi
  have hx0 : ∀ i ≤ n, 0 ≤ x i := fun i hi ↦ hp.1.left_le hi
  have hDfin : ∀ i, m < i → i ≤ n → IsFinite (x i - ω^ (1 : Surreal)) :=
    fun i h1 h2 ↦ (htop i h1 h2).1
  -- Block A: the finite-galaxy block is at most K·ω with K finite
  have hA : ∑ i ∈ Finset.range (m + 1), nortonExp (x i) * (x (i + 1) - x i) ≤
      (∑ i ∈ Finset.range (m + 1), expFin (x i)) * ω^ (1 : Surreal) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [nortonExp_of_isFinite (hfin i him)]
    refine mul_le_mul_of_nonneg_left ?_ (expFin_pos' _).le
    have h1 : x (i + 1) ≤ ω^ (1 : Surreal) := hxle (i + 1) (by omega)
    have h2 : 0 ≤ x i := hx0 i (by omega)
    linarith
  have hKfin : IsFinite (∑ i ∈ Finset.range (m + 1), expFin (x i)) :=
    isFinite_sum fun i hi ↦ isFinite_expFin (hfin i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
  obtain ⟨k₀, hk₀⟩ := isFinite_iff.1 hKfin
  have hA' : ∑ i ∈ Finset.range (m + 1), nortonExp (x i) * (x (i + 1) - x i) ≤
      (k₀ : Surreal) * ω^ (1 : Surreal) :=
    hA.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hk₀) (wpow_nonneg _))
  -- Block B: the top-galaxy block is ω^ω times the tagged sum S
  have hB : ∑ i ∈ Finset.Ico (m + 1) n, nortonExp (x i) * (x (i + 1) - x i) =
      ω^ ω^ (1 : Surreal) * ∑ i ∈ Finset.Ico (m + 1) n,
        expFin (x i - ω^ (1 : Surreal)) *
          ((x (i + 1) - ω^ (1 : Surreal)) - (x i - ω^ (1 : Surreal))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
    rw [nortonExp_of_not_isFinite (htop i (by omega) (by omega)).2]
    ring
  -- S and its standard part
  have hSfin : IsFinite (∑ i ∈ Finset.Ico (m + 1) n,
      expFin (x i - ω^ (1 : Surreal)) *
        ((x (i + 1) - ω^ (1 : Surreal)) - (x i - ω^ (1 : Surreal)))) := by
    refine isFinite_sum fun i hi ↦ ?_
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
    exact (isFinite_expFin (hDfin i (by omega) (by omega))).mul
      ((hDfin (i + 1) (by omega) (by omega)).sub (hDfin i (by omega) (by omega)))
  have hstS : stdPart (∑ i ∈ Finset.Ico (m + 1) n,
      expFin (x i - ω^ (1 : Surreal)) *
        ((x (i + 1) - ω^ (1 : Surreal)) - (x i - ω^ (1 : Surreal)))) =
      ∑ i ∈ Finset.Ico (m + 1) n, Real.exp (stdPart (x i - ω^ (1 : Surreal))) *
        (stdPart (x (i + 1) - ω^ (1 : Surreal)) - stdPart (x i - ω^ (1 : Surreal))) := by
    rw [stdPart_sum (fun i hi ↦ ?_)]
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
      rw [stdPart_mul (isFinite_expFin (hDfin i (by omega) (by omega)))
          ((hDfin (i + 1) (by omega) (by omega)).sub (hDfin i (by omega) (by omega))),
        stdPart_expFin (hDfin i (by omega) (by omega)),
        stdPart_sub (hDfin (i + 1) (by omega) (by omega)) (hDfin i (by omega) (by omega))]
    · obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
      exact (isFinite_expFin (hDfin i (by omega) (by omega))).mul
        ((hDfin (i + 1) (by omega) (by omega)).sub (hDfin i (by omega) (by omega)))
  -- the real Riemann bound: st S ≤ 1 − exp (st (x (m+1) − ω))
  have hd0 : stdPart (x n - ω^ (1 : Surreal)) = 0 := by
    rw [hp.1.2.1, sub_self, ArchimedeanClass.stdPart_zero]
  have hst_le : stdPart (∑ i ∈ Finset.Ico (m + 1) n,
      expFin (x i - ω^ (1 : Surreal)) *
        ((x (i + 1) - ω^ (1 : Surreal)) - (x i - ω^ (1 : Surreal)))) ≤
      1 - Real.exp (stdPart (x (m + 1) - ω^ (1 : Surreal))) := by
    rw [hstS]
    have h := real_exp_riemann_le (fun i ↦ stdPart (x i - ω^ (1 : Surreal)))
      (show m + 1 ≤ n by omega)
    rw [hd0, Real.exp_zero] at h
    exact h
  -- rationals wedged under the retained fraction
  obtain ⟨q, hq0, hqρ⟩ :=
    exists_rat_btwn (Real.exp_pos (stdPart (x (m + 1) - ω^ (1 : Surreal))))
  obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn hqρ
  -- S ≤ 1 − cast q, hence V·S ≤ V − (cast q)·V
  have hι := infinitesimal_sub_stdPart hSfin
  have habs : |(∑ i ∈ Finset.Ico (m + 1) n,
      expFin (x i - ω^ (1 : Surreal)) *
        ((x (i + 1) - ω^ (1 : Surreal)) - (x i - ω^ (1 : Surreal)))) -
      ((stdPart (∑ i ∈ Finset.Ico (m + 1) n,
        expFin (x i - ω^ (1 : Surreal)) *
          ((x (i + 1) - ω^ (1 : Surreal)) - (x i - ω^ (1 : Surreal)))) : ℝ) : Surreal)| <
      ((q' - q : ℚ) : Surreal) :=
    hι.abs_lt_ratCast (by exact_mod_cast sub_pos.2 (show (q : ℝ) < (q' : ℝ) from hq'1))
  have hcast1 : ((stdPart (∑ i ∈ Finset.Ico (m + 1) n,
      expFin (x i - ω^ (1 : Surreal)) *
        ((x (i + 1) - ω^ (1 : Surreal)) - (x i - ω^ (1 : Surreal)))) : ℝ) : Surreal) ≤
      ((1 - Real.exp (stdPart (x (m + 1) - ω^ (1 : Surreal))) : ℝ) : Surreal) :=
    Real.toSurreal_le_iff.2 hst_le
  have hSle : (∑ i ∈ Finset.Ico (m + 1) n,
      expFin (x i - ω^ (1 : Surreal)) *
        ((x (i + 1) - ω^ (1 : Surreal)) - (x i - ω^ (1 : Surreal)))) ≤
      1 - ((q : ℝ) : Surreal) := by
    have h1 := (le_abs_self _).trans_lt habs
    have h2 : ((1 - Real.exp (stdPart (x (m + 1) - ω^ (1 : Surreal))) : ℝ) : Surreal) +
        ((q' - q : ℚ) : Surreal) ≤ 1 - ((q : ℝ) : Surreal) := by
      rw [← Real.toSurreal_ratCast, ← Real.toSurreal_add, ← Real.toSurreal_one,
        ← Real.toSurreal_sub]
      refine Real.toSurreal_le_iff.2 ?_
      push_cast
      linarith
    linarith
  have hVS : ω^ ω^ (1 : Surreal) * (∑ i ∈ Finset.Ico (m + 1) n,
      expFin (x i - ω^ (1 : Surreal)) *
        ((x (i + 1) - ω^ (1 : Surreal)) - (x i - ω^ (1 : Surreal)))) ≤
      ω^ ω^ (1 : Surreal) - ((q : ℝ) : Surreal) * ω^ ω^ (1 : Surreal) := by
    have h := mul_le_mul_of_nonneg_left hSle (wpow_nonneg (ω^ (1 : Surreal)))
    have hexp : ω^ ω^ (1 : Surreal) * (1 - ((q : ℝ) : Surreal)) =
        ω^ ω^ (1 : Surreal) - ((q : ℝ) : Surreal) * ω^ ω^ (1 : Surreal) := by ring
    linarith [hexp ▸ h]
  -- the wpow class comparison: (k₀ + j)·ω < (cast q)·ω^ω
  obtain ⟨j, hj⟩ := isFinite_iff.1 hc
  have hcj : -(j : Surreal) ≤ c := by
    have := (abs_le.1 hj).1
    linarith
  have hmain : ((k₀ + j : ℕ) : Surreal) * ω^ (1 : Surreal) <
      ((q : ℝ) : Surreal) * ω^ ω^ (1 : Surreal) := by
    have h := mul_wpow_lt_mul_wpow ((k₀ + j : ℕ) : ℝ)
      (show (0 : ℝ) < (q : ℝ) from hq0) one_lt_wpow_one
    rwa [Real.toSurreal_natCast] at h
  have hΩ1 : (1 : Surreal) ≤ ω^ (1 : Surreal) := one_lt_wpow_one.le
  have hfinal : (k₀ : Surreal) * ω^ (1 : Surreal) - c ≤
      ((k₀ + j : ℕ) : Surreal) * ω^ (1 : Surreal) := by
    have hjΩ : (j : Surreal) ≤ (j : Surreal) * ω^ (1 : Surreal) :=
      le_mul_of_one_le_right (Nat.cast_nonneg j) hΩ1
    have hpc : ((k₀ + j : ℕ) : Surreal) * ω^ (1 : Surreal) =
        (k₀ : Surreal) * ω^ (1 : Surreal) + (j : Surreal) * ω^ (1 : Surreal) := by
      push_cast
      ring
    rw [hpc]
    linarith
  -- assemble
  have hsplit : lowerSumExp x n =
      (∑ i ∈ Finset.range (m + 1), nortonExp (x i) * (x (i + 1) - x i)) +
      ∑ i ∈ Finset.Ico (m + 1) n, nortonExp (x i) * (x (i + 1) - x i) := by
    rw [lowerSumExp, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (m + 1)) (show m + 1 ≤ n by omega),
      Finset.range_eq_Ico]
  rw [hsplit, hB]
  linarith

/-! ### Horn (a): the finite halo of `ω^ω` fits — the cut cannot see the `−1` -/

/-- **Halo blindness**: every finite perturbation of `ω^ω` fits strictly between all
lower and all upper exponential Darboux sums. The genetic cut for `∫₀^ω eˣ dx` has no
resolution below the Archimedean class of `e^ω` itself. -/
theorem fits_norton_add_of_isFinite {c : Surreal} (hc : IsFinite c) :
    Cut.Fits (ω^ ω^ (1 : Surreal) + c) nortonLo nortonHi := by
  rw [fits_norton_iff]
  intro x n hp
  refine ⟨lowerSumExp_lt_wpow_add hp hc, ?_⟩
  have h2 := natCast_mul_lt_upperSumExp hp 2
  obtain ⟨j, hj⟩ := isFinite_iff.1 hc
  have hcj : c ≤ (j : Surreal) := (le_abs_self c).trans hj
  have hjV : (j : Surreal) < ω^ ω^ (1 : Surreal) :=
    (natCast_lt_wpow_one j).trans (wpow_lt_wpow.2 one_lt_wpow_one)
  push_cast at h2
  linarith

/-- Norton's value `e^ω = ω^ω` fits the genetic cut. -/
theorem fits_norton_wpow : Cut.Fits (ω^ ω^ (1 : Surreal)) nortonLo nortonHi := by
  simpa using fits_norton_add_of_isFinite isFinite_zero

/-- The **true** value `e^ω − 1` also fits the genetic cut. -/
theorem fits_norton_wpow_sub_one :
    Cut.Fits (ω^ ω^ (1 : Surreal) - 1) nortonLo nortonHi := by
  have h := fits_norton_add_of_isFinite isFinite_one.neg
  rwa [← sub_eq_add_neg] at h

/-- **The indeterminacy horn**: both Norton's value `e^ω = ω^ω` and the correct value
`e^ω − 1` fit strictly between all lower and all upper exponential Darboux sums over
`[0, ω]`. Approximation alone cannot decide the genetic exponential integral — the
choice falls entirely to the simplicity principle. (Compare `darboux_indeterminate`,
the same phenomenon for `∫₀^ω x dx` at scale `ω`; here the blindness is a full
Archimedean class at scale `ω^ω`.) -/
theorem norton_indeterminate :
    Cut.Fits (ω^ ω^ (1 : Surreal) - 1) nortonLo nortonHi ∧
      Cut.Fits (ω^ ω^ (1 : Surreal)) nortonLo nortonHi :=
  ⟨fits_norton_wpow_sub_one, fits_norton_wpow⟩

theorem nortonLo_lt_nortonHi : nortonLo < nortonHi :=
  fits_norton_wpow.lt

/-- **The genetic exponential integral over `[0, ω]`**: the birthday-simplest surreal
lying strictly between all lower and all upper exponential Darboux sums — the
Conway-style simplest-fit principle applied to the exponential over an infinite
interval, i.e. the genetic value of `∫₀^ω eˣ dx` for this option family. -/
def nortonIntegralExp : Surreal :=
  Cut.simplestBtwn nortonLo_lt_nortonHi

end Surreal

end
