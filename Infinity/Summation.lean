import Infinity.Series

/-!
# The Transfinite Summation Theorem (ℕ-length)

`Infinity.Series` defined Hahn-sum semantics and verified one instance. This file proves the
general theorem: **every strictly dominating series of surreals has a Hahn sum** — where
*strictly dominating* means each term lies in a strictly larger Archimedean class (strictly
smaller magnitude scale) than the one before.

The construction is a single Conway cut, elementary and explicit:

`x := !{ sₙ - 2|tₙ| | sₙ + 2|tₙ| }`

— sandwich every partial sum within twice its current term. The separation of the two sides
is pure domination calculus: between stages `m < n`, the partial sums differ by
`tₘ + (strictly smaller stuff)`, and anything of strictly larger class is smaller in absolute
value than `|tₘ|`, so the sandwich intervals overlap coherently. No simplicity or birthday
machinery is required.

Combined with `IsHahnSum.mk_sub_le` (uniqueness modulo every term's class) and
`not_tendstoSurreal_partialSum` (no topological convergence, ever), this completes an
existence-uniqueness-nonconvergence trilogy: on `No`, ℕ-length summation is total on
strictly dominating series and has nothing to do with limits.

* `Surreal.exists_isHahnSum` — the summation theorem.
* `Surreal.summable_not_convergent` — the trilogy in one statement.
* `Surreal.exists_isHahnSum_omegaPowerSeries` — every ω-power series `Σ rₖ ω⁻ᵏ` with
  nonzero real coefficients has a transfinite sum: the ℕ-length shadow of the existence of
  Conway normal forms.
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

/-! ### Domination calculus helpers -/

private theorem lt_mk_add {c : ArchimedeanClass Surreal} {a b : Surreal}
    (ha : c < ArchimedeanClass.mk a) (hb : c < ArchimedeanClass.mk b) :
    c < ArchimedeanClass.mk (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (ArchimedeanClass.min_le_mk_add ..)

private theorem lt_mk_sum {c : ArchimedeanClass Surreal} (hc : c < ⊤) {s : Finset ℕ}
    {u : ℕ → Surreal} (h : ∀ i ∈ s, c < ArchimedeanClass.mk (u i)) :
    c < ArchimedeanClass.mk (∑ i ∈ s, u i) := by
  induction s using Finset.cons_induction with
  | empty =>
    have h0 : ArchimedeanClass.mk (0 : Surreal) = ⊤ := ArchimedeanClass.mk_eq_top_iff.2 rfl
    rw [Finset.sum_empty, h0]
    exact hc
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact lt_mk_add (h a (Finset.mem_cons_self ..))
      (ih fun i hi ↦ h i (Finset.mem_cons_of_mem hi))

/-- Strict domination in Archimedean class gives strict comparison of absolute values. -/
theorem abs_lt_abs_of_mk_lt {a b : Surreal}
    (h : ArchimedeanClass.mk a < ArchimedeanClass.mk b) : |b| < |a| := by
  have h1 := ArchimedeanClass.mk_lt_mk.1 h 1
  simpa using h1

private theorem mk_two : ArchimedeanClass.mk (2 : Surreal) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [show (2 : Surreal) = ((2 : ℕ) : Surreal) by norm_cast]
  rw [ArchimedeanClass.stdPart_natCast]
  norm_num

private theorem mk_two_mul_abs (a : Surreal) :
    ArchimedeanClass.mk (2 * |a|) = ArchimedeanClass.mk a := by
  rw [ArchimedeanClass.mk_mul, mk_two, zero_add, ArchimedeanClass.mk_abs]

private theorem partialSum_sub (t : ℕ → Surreal) {m n : ℕ} (h : m ≤ n) :
    partialSum t n - partialSum t m = ∑ k ∈ Ico m n, t k := by
  rw [partialSum, partialSum]
  exact (sum_Ico_eq_sub _ h).symm

/-- Terms of a strictly dominating series are nonzero. -/
theorem ne_zero_of_strict_dominating {t : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) (n : ℕ) :
    t n ≠ 0 := by
  intro h0
  have h1 : ArchimedeanClass.mk (t n) = ⊤ := ArchimedeanClass.mk_eq_top_iff.2 h0
  exact absurd (h1 ▸ ht n) not_top_lt

/-! ### The summation theorem -/

/-- **The Transfinite Summation Theorem** (ℕ-length): every strictly dominating series of
surreals has a Hahn sum, namely the Conway cut sandwiching each partial sum within twice
its current term. -/
theorem exists_isHahnSum {t : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    ∃ x, IsHahnSum t x := by
  have hmono : StrictMono fun n ↦ ArchimedeanClass.mk (t n) := strictMono_nat_of_lt_succ ht
  have ht0 := ne_zero_of_strict_dominating ht
  have htop : ∀ n, ArchimedeanClass.mk (t n) < ⊤ := fun n ↦ (ht n).trans_le le_top
  -- Separation of the two sides of the cut.
  have H : ∀ a ∈ Set.range (fun n ↦ partialSum t n - 2 * |t n|),
      ∀ b ∈ Set.range (fun n ↦ partialSum t n + 2 * |t n|), a < b := by
    rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
    dsimp only
    rcases lt_trichotomy m n with hmn | rfl | hnm
    -- `m < n`: the gap `sₙ - sₘ` is `tₘ` plus strictly dominated junk.
    · have hsub := partialSum_sub t hmn.le
      have hpeel : ∑ k ∈ Ico m n, t k = t m + ∑ k ∈ Ico (m + 1) n, t k :=
        sum_eq_sum_Ico_succ_bot hmn _
      have hD : ArchimedeanClass.mk (t m) <
          ArchimedeanClass.mk ((∑ k ∈ Ico (m + 1) n, t k) + 2 * |t n|) := by
        apply lt_mk_add
        · exact lt_mk_sum (htop m) fun i hi ↦
            hmono (Nat.lt_of_succ_le (Finset.mem_Ico.1 hi).1)
        · rw [mk_two_mul_abs]
          exact hmono hmn
      have habs := abs_lt.1 (abs_lt_abs_of_mk_lt hD)
      have h1 : -|t m| ≤ t m := neg_abs_le _
      have hs : partialSum t n =
          partialSum t m + (t m + ∑ k ∈ Ico (m + 1) n, t k) := by
        rw [← hpeel, ← hsub]; ring
      rw [hs]
      linarith [habs.1]
    -- `m = n`: trivial, the interval has positive width.
    · have := abs_pos.2 (ht0 m)
      linarith
    -- `n < m`: symmetric, with the `-2|tₘ|` absorbed into the dominated junk.
    · have hsub := partialSum_sub t hnm.le
      have hpeel : ∑ k ∈ Ico n m, t k = t n + ∑ k ∈ Ico (n + 1) m, t k :=
        sum_eq_sum_Ico_succ_bot hnm _
      have hD : ArchimedeanClass.mk (t n) <
          ArchimedeanClass.mk ((∑ k ∈ Ico (n + 1) m, t k) + -(2 * |t m|)) := by
        apply lt_mk_add
        · exact lt_mk_sum (htop n) fun i hi ↦
            hmono (Nat.lt_of_succ_le (Finset.mem_Ico.1 hi).1)
        · rw [ArchimedeanClass.mk_neg, mk_two_mul_abs]
          exact hmono hnm
      have habs := abs_lt.1 (abs_lt_abs_of_mk_lt hD)
      have h1 : t n ≤ |t n| := le_abs_self _
      have hs : partialSum t m =
          partialSum t n + (t n + ∑ k ∈ Ico (n + 1) m, t k) := by
        rw [← hpeel, ← hsub]; ring
      rw [hs]
      linarith [habs.2]
  -- The cut is the sum.
  refine ⟨!{Set.range (fun n ↦ partialSum t n - 2 * |t n|) |
      Set.range (fun n ↦ partialSum t n + 2 * |t n|)}'H, ?_⟩
  intro n
  have hl := lt_ofSets_of_mem_left (H := H) ⟨n, rfl⟩
  have hr := ofSets_lt_of_mem_right (H := H) ⟨n, rfl⟩
  dsimp only at hl hr
  rw [ArchimedeanClass.mk_le_mk]
  refine ⟨2, ?_⟩
  have habs : |(!{_ | _}'H) - partialSum t n| ≤ 2 * |t n| :=
    abs_le.2 ⟨by linarith, by linarith⟩
  calc |(!{_ | _}'H) - partialSum t n| ≤ 2 * |t n| := habs
    _ = 2 • |t n| := by rw [two_nsmul, two_mul]

/-- **Summable but never convergent**: the existence–uniqueness–nonconvergence trilogy for
strictly dominating series, in one statement. Such a series always has a Hahn sum (unique
modulo every term's class, by `IsHahnSum.mk_sub_le`), and its partial sums converge to no
surreal whatsoever. -/
theorem summable_not_convergent {t : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    (∃ x, IsHahnSum t x) ∧ ∀ y : Surreal, ¬ TendstoSurreal (partialSum t) atTop y :=
  ⟨exists_isHahnSum ht,
    fun y ↦ not_tendstoSurreal_partialSum (ne_zero_of_strict_dominating ht) y⟩

/-! ### Application: all ω-power series sum -/

/-- Powers of a positive infinitesimal are strictly dominating. -/
theorem mk_pow_lt_mk_pow_succ {e : Surreal} (he : Infinitesimal e) (he0 : 0 < e) (k : ℕ) :
    ArchimedeanClass.mk (e ^ k) < ArchimedeanClass.mk (e ^ (k + 1)) := by
  rw [ArchimedeanClass.mk_lt_mk]
  intro j
  have h1 : (j : Surreal) * e < 1 := by
    have h := infinitesimal_iff.1 he j
    rwa [nsmul_eq_mul, abs_of_pos he0] at h
  have h2 : (0 : Surreal) < e ^ k := pow_pos he0 k
  calc j • |e ^ (k + 1)| = e ^ k * ((j : Surreal) * e) := by
        rw [abs_of_pos (pow_pos he0 _), nsmul_eq_mul, pow_succ]; ring
    _ < e ^ k * 1 := mul_lt_mul_of_pos_left h1 h2
    _ = |e ^ k| := by rw [mul_one, abs_of_pos h2]

/-- **Every ω-power series sums**: for any sequence of nonzero real coefficients `rₖ`, the
series `Σ_{k<ω} rₖ ω⁻ᵏ` has a transfinite sum in `No`. This is the ℕ-length shadow of the
existence of Conway normal forms: arbitrary "decimal expansions in base ω" all denote
surreal numbers. -/
theorem exists_isHahnSum_omegaPowerSeries (r : ℕ → ℝ) (hr : ∀ n, r n ≠ 0) :
    ∃ x, IsHahnSum (fun k ↦ (r k : Surreal) * ((ω^ (1 : Surreal))⁻¹) ^ k) x := by
  apply exists_isHahnSum
  intro n
  have he : Infinitesimal ((ω^ (1 : Surreal))⁻¹ : Surreal) := infinitesimal_inv_wpow one_pos
  have he0 : (0 : Surreal) < (ω^ (1 : Surreal))⁻¹ := inv_pos.2 (wpow_pos _)
  rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, mk_realCast (hr n),
    mk_realCast (hr (n + 1)), zero_add, zero_add]
  exact mk_pow_lt_mk_pow_succ he he0 n

end Surreal
