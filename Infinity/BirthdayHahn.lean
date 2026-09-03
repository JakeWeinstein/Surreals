/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.ExpMul
import Infinity.MicroKernel
import CombinatorialGames.Surreal.Birthday.Cut
import CombinatorialGames.Surreal.Birthday.Dyadic

/-!
# The birthday theory of canonical transfinite sums

`Infinity.CanonicalSum` defined the canonical transfinite sum `hahnSum` of a strictly
dominating series as the birthday-simplest surreal fitting between the cuts `sumLo`/`sumHi`
that bound all Hahn sums. This file develops the birthday theory of that construction, and
in particular settles the *uniqueness* question underneath it.

## Level 1: uniqueness of the simplest fit

The central theorem is **`Cut.eq_of_fits_of_birthday_le`**: a birthday-minimal surreal
fitting between two cuts is *unique* — any fit of minimal birthday is *the* simplest fit.
The proof is a new cut-level rendition of Conway's simplicity theorem needing no sign
expansions: given two distinct fits `z < w` of equal minimal birthday, take birthday-minimal
numeric games `g, k` representing them; either some left option of `k` lands in `[z, w)`
(a strictly simpler fit — contradiction), or some right option of `g` lands in `(z, w]`
(same), or else `le_iff_forall_lf` forces `k ≤ g`, contradicting `g < k`.

Consequences:

* `Cut.birthday_lt_of_fits_of_ne` : every *other* fit is **strictly** more complex;
* `Cut.simplestBtwn_eq_iff` : a complete characterization of `Cut.simplestBtwn`;
* `hahnSum_eq_iff` : `hahnSum ht = z ↔ z` is a Hahn sum of minimal birthday;
* `birthday_hahnSum_lt_of_ne` : every non-canonical Hahn sum is strictly more complex;
* `hahnSum_neg` : **the canonical sum is odd** — the first unconditional instance of
  canonicity commuting with arithmetic.

## Level 2: birthday bounds

* `birthday_hahnSum_le_iSup` / `birthday_hahnSum_le_sup` : the canonical sum's birthday is
  at most `⨆ n k, (birthday of the n-th partial sum) + (k+1)·(birthday of the n-th term) + 1`,
  read off the explicit structure of the cuts `sumLo`/`sumHi`.
* Lower bounds via dyadic theory: `omega0_le_birthday_of_infinitesimal_sub` (a surreal
  infinitesimally close to, but distinct from, a dyadic is born at or after day `ω`),
  specializing to `omega0_le_birthday_of_infinitesimal` and, for series,
  `omega0_le_birthday_sub_of_isHahnSum` — **the cost of non-uniqueness**: distinct Hahn
  sums of one series differ by an element of birthday `≥ ω`.

## Level 3: the geometric series, and exact evaluations

* `isHahnSum_geometric_iff` : the Hahn sums of `Σ ω⁻ᵏ` are **exactly the micro-halo** of
  `ω/(ω−1)` — the surreals within distance smaller than every scale `ω⁻ⁿ`.
* `hahnSum_geometric_dichotomy` : either the canonical sum *is* `ω/(ω−1)`, or it is
  **strictly simpler** — `birthday_hahnSum_geometric_le` unconditionally.
* `hahnSum_geometric_eq_of_halo_minimal` : the exact equality
  `hahnSum (Σ ω⁻ᵏ) = ω/(ω−1)` follows from one isolated conjecture (`ω/(ω−1)` is
  birthday-minimal in its own micro-halo — a truncation-simplicity statement that
  classically follows from sign-expansion/normal-form theory not yet formalized).
* **The birthday sandwich**: unconditionally, `ω ≤ birthday (hahnSum (Σ ω⁻ᵏ)) ≤
  birthday (ω/(ω−1))` (`omega0_le_birthday_hahnSum_geometric`), and
  `stdPart_hahnSum_geometric : st (hahnSum (Σ ω⁻ᵏ)) = 1`.
* **Exact evaluations** — the canonical-sum operator provably computes closed forms:
  `hahnSum_telescoping_eq_one` : `hahnSum (Σ (ω⁻ᵏ − ω⁻⁽ᵏ⁺¹⁾)) = 1`, and
  `hahnSum_omega_telescoping_eq` : `hahnSum (Σ ω·(ω⁻ᵏ − ω⁻⁽ᵏ⁺¹⁾)) = ω` — the latter via
  `birthday_wpow_one : birthday ω = ω`, the first computed birthday of an infinite
  surreal in this development.

## Level 4: the additivity and multiplicativity frontier

* `IsHahnSum.add` : Hahn sums add, given termwise non-cancellation
  (`mk (t n + u n) ≤ min (mk (t n)) (mk (u n))`); `strict_dominating_add` shows the
  hypothesis also preserves strict domination.
* `hahnSum_add_eq_iff` : additivity of the *canonical* sum is **equivalent** to a birthday
  inequality — `hahnSum t + hahnSum u` being minimal-birthday among sums of `t + u`.
* `expInf_add_eq_mul_iff` : likewise, the exponential functional equation
  `expInf (ε+δ) = expInf ε * expInf δ` (for positive infinitesimals) is **equivalent** to
  minimality of `expInf ε * expInf δ`; and if it fails, `birthday_expInf_add_lt_of_mul_ne`
  says the canonical value is strictly simpler than the product.

The multiplicativity/additivity questions thus reduce, exactly, to whether the arithmetic
operations preserve birthday-minimality within the relevant halos. The truncation-simplicity
heuristic (normal forms of the canonical sums extend termwise, and truncations are simpler)
predicts *yes* in the non-cancelling regime, but proving it needs the sign-expansion or
Conway-normal-form birthday theory. These theorems pin the open questions to single, sharp
inequalities.
-/

open ArchimedeanClass Filter Finset IGame

noncomputable section

namespace Surreal

/-! ### Level 1: uniqueness of the simplest fit -/

/-- The set of surreals fitting between two cuts is order-convex. -/
theorem Cut.fits_of_le_of_le {x y : Cut} {z w v : Surreal} (hz : Cut.Fits z x y)
    (hw : Cut.Fits w x y) (h1 : z ≤ v) (h2 : v ≤ w) : Cut.Fits v x y :=
  ⟨Cut.isUpperSet_right x h1 hz.1, Cut.isLowerSet_left y h2 hw.2⟩

/-- The engine of the uniqueness theorem: two fits `z < w` with `z` of minimal birthday and
`w` no more complex are contradictory. Choose birthday-minimal numeric games `g, k` for
`z, w`; either an option of one of them gives a strictly simpler fit, or `k ≤ g` outright. -/
private theorem fits_aux {x y : Cut} {z w : Surreal}
    (hz : Cut.Fits z x y) (hw : Cut.Fits w x y) (hzw : z < w)
    (hmin : ∀ v, Cut.Fits v x y → z.birthday ≤ v.birthday)
    (hwb : w.birthday ≤ z.birthday) : False := by
  obtain ⟨g, hgn, hgz, hgb⟩ := birthday_eq_iGameBirthday z
  obtain ⟨k, hkn, hkw, hkb⟩ := birthday_eq_iGameBirthday w
  have hgk : g < k := by
    rw [← hgz, ← hkw] at hzw
    exact mk_lt_mk.1 hzw
  -- Case A: some left option of `k` is at least `z`: it is a strictly simpler fit.
  by_cases hA : ∃ i ∈ kᴸ, g ≤ i
  · obtain ⟨i, hik, hgi⟩ := hA
    haveI : IGame.Numeric i := IGame.Numeric.of_mem_moves hik
    have hzi : z ≤ Surreal.mk i := by
      rw [← hgz]; exact mk_le_mk.2 hgi
    have hiw : Surreal.mk i ≤ w := by
      rw [← hkw]; exact (mk_lt_mk.2 (IGame.Numeric.left_lt hik)).le
    have hbi : (Surreal.mk i).birthday < z.birthday :=
      lt_of_le_of_lt (birthday_mk_le i) <|
        (IGame.birthday_lt_of_mem_moves hik).trans_le (hkb.le.trans hwb)
    exact hbi.not_ge (hmin _ (Cut.fits_of_le_of_le hz hw hzi hiw))
  -- Case B: some right option of `g` is at most `w`: it is a strictly simpler fit.
  by_cases hB : ∃ j ∈ gᴿ, j ≤ k
  · obtain ⟨j, hjg, hjk⟩ := hB
    haveI : IGame.Numeric j := IGame.Numeric.of_mem_moves hjg
    have hzj : z ≤ Surreal.mk j := by
      rw [← hgz]; exact (mk_lt_mk.2 (IGame.Numeric.lt_right hjg)).le
    have hjw : Surreal.mk j ≤ w := by
      rw [← hkw]; exact mk_le_mk.2 hjk
    have hbj : (Surreal.mk j).birthday < z.birthday :=
      lt_of_le_of_lt (birthday_mk_le j) <|
        (IGame.birthday_lt_of_mem_moves hjg).trans_le hgb.le
    exact hbj.not_ge (hmin _ (Cut.fits_of_le_of_le hz hw hzj hjw))
  -- Case C: no left option of `k` reaches `g` and no right option of `g` reaches down to
  -- `k`; then `k ≤ g` by the fundamental characterization of `≤`, contradicting `g < k`.
  simp only [not_exists, not_and] at hA hB
  exact hgk.not_ge (le_iff_forall_lf.2 ⟨hA, hB⟩)

/-- **Uniqueness of the simplest fit**: if `z` fits between the cuts `x` and `y` with
minimal birthday, then any fit `w` of birthday at most `z.birthday` *is* `z`. Conway's
simplicity phenomenon, at the level of arbitrary cut intervals. -/
theorem Cut.eq_of_fits_of_birthday_le {x y : Cut} {z w : Surreal}
    (hz : Cut.Fits z x y) (hw : Cut.Fits w x y)
    (hmin : ∀ v, Cut.Fits v x y → z.birthday ≤ v.birthday)
    (hwb : w.birthday ≤ z.birthday) : w = z := by
  by_contra hne
  have hb : w.birthday = z.birthday := hwb.antisymm (hmin w hw)
  obtain h | h := Ne.lt_or_gt hne
  · exact fits_aux hw hz h (fun v hv ↦ hb ▸ hmin v hv) hb.ge
  · exact fits_aux hz hw h hmin hwb

/-- Two birthday-minimal fits between the same cuts are equal. -/
theorem Cut.fits_unique {x y : Cut} {z w : Surreal}
    (hz : Cut.Fits z x y) (hw : Cut.Fits w x y)
    (hminz : ∀ v, Cut.Fits v x y → z.birthday ≤ v.birthday)
    (hminw : ∀ v, Cut.Fits v x y → w.birthday ≤ v.birthday) : z = w :=
  (Cut.eq_of_fits_of_birthday_le hz hw hminz (hminw z hz)).symm

/-- **Strict complexity of every other fit**: if `z` is a birthday-minimal fit, any fit
`w ≠ z` has strictly larger birthday. -/
theorem Cut.birthday_lt_of_fits_of_ne {x y : Cut} {z w : Surreal}
    (hz : Cut.Fits z x y) (hmin : ∀ v, Cut.Fits v x y → z.birthday ≤ v.birthday)
    (hw : Cut.Fits w x y) (hne : w ≠ z) : z.birthday < w.birthday := by
  rcases le_or_gt w.birthday z.birthday with h | h
  · exact absurd (Cut.eq_of_fits_of_birthday_le hz hw hmin h) hne
  · exact h

/-- **The complete characterization of `simplestBtwn`**: it is the unique fit of minimal
birthday. -/
theorem Cut.simplestBtwn_eq_iff {x y : Cut} (h : x < y) {z : Surreal} :
    Cut.simplestBtwn h = z ↔
      Cut.Fits z x y ∧ ∀ w, Cut.Fits w x y → z.birthday ≤ w.birthday := by
  constructor
  · rintro rfl
    exact ⟨Cut.fits_simplestBtwn h, fun w hw ↦ Cut.birthday_simplestBtwn_le_of_fits hw⟩
  · rintro ⟨hz, hmin⟩
    exact Cut.eq_of_fits_of_birthday_le hz (Cut.fits_simplestBtwn h) hmin
      (Cut.birthday_simplestBtwn_le_of_fits hz)

/-- Any fit other than `simplestBtwn` is strictly more complex. -/
theorem Cut.birthday_simplestBtwn_lt_of_fits_of_ne {x y : Cut} {w : Surreal} (h : x < y)
    (hw : Cut.Fits w x y) (hne : w ≠ Cut.simplestBtwn h) :
    (Cut.simplestBtwn h).birthday < w.birthday :=
  Cut.birthday_lt_of_fits_of_ne (Cut.fits_simplestBtwn h)
    (fun _ hv ↦ Cut.birthday_simplestBtwn_le_of_fits hv) hw hne

/-! ### Level 1 payoff: the characterization of canonical sums -/

variable {t u : ℕ → Surreal}

/-- **The characterization of the canonical transfinite sum**: `hahnSum ht` is the unique
Hahn sum of minimal birthday. -/
theorem hahnSum_eq_iff
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) {z : Surreal} :
    hahnSum ht = z ↔
      IsHahnSum t z ∧ ∀ w, IsHahnSum t w → z.birthday ≤ w.birthday := by
  have h0 := ne_zero_of_strict_dominating ht
  unfold hahnSum
  rw [Cut.simplestBtwn_eq_iff]
  constructor
  · rintro ⟨hz, hmin⟩
    exact ⟨(fits_iff_isHahnSum h0).1 hz, fun w hw ↦ hmin w ((fits_iff_isHahnSum h0).2 hw)⟩
  · rintro ⟨hz, hmin⟩
    exact ⟨(fits_iff_isHahnSum h0).2 hz, fun w hw ↦ hmin w ((fits_iff_isHahnSum h0).1 hw)⟩

/-- A Hahn sum at least as simple as the canonical one *is* the canonical one. -/
theorem hahnSum_eq_of_isHahnSum_of_birthday_le
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) {z : Surreal}
    (hz : IsHahnSum t z) (hb : z.birthday ≤ (hahnSum ht).birthday) : hahnSum ht = z := by
  have h0 := ne_zero_of_strict_dominating ht
  exact (Cut.eq_of_fits_of_birthday_le ((fits_iff_isHahnSum h0).2 (isHahnSum_hahnSum ht))
    ((fits_iff_isHahnSum h0).2 hz)
    (fun v hv ↦ birthday_hahnSum_le ht ((fits_iff_isHahnSum h0).1 hv)) hb).symm

/-- **Every non-canonical Hahn sum is strictly more complex** than the canonical one. -/
theorem birthday_hahnSum_lt_of_ne
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) {z : Surreal}
    (hz : IsHahnSum t z) (hne : z ≠ hahnSum ht) :
    (hahnSum ht).birthday < z.birthday := by
  have h0 := ne_zero_of_strict_dominating ht
  exact Cut.birthday_lt_of_fits_of_ne
    ((fits_iff_isHahnSum h0).2 (isHahnSum_hahnSum ht))
    (fun v hv ↦ birthday_hahnSum_le ht ((fits_iff_isHahnSum h0).1 hv))
    ((fits_iff_isHahnSum h0).2 hz) hne

/-! ### Negation: the first unconditional arithmetic law for canonical sums -/

theorem partialSum_neg (t : ℕ → Surreal) (n : ℕ) :
    partialSum (fun k ↦ -t k) n = -partialSum t n := by
  simp [partialSum]

theorem IsHahnSum.neg {x : Surreal} (hx : IsHahnSum t x) :
    IsHahnSum (fun n ↦ -t n) (-x) := by
  intro n
  show ArchimedeanClass.mk (-t n) ≤ _
  have h1 : -x - partialSum (fun k ↦ -t k) n = -(x - partialSum t n) := by
    rw [partialSum_neg]; ring
  rw [h1, ArchimedeanClass.mk_neg, ArchimedeanClass.mk_neg]
  exact hx n

theorem strict_dominating_neg
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) (n : ℕ) :
    ArchimedeanClass.mk (-t n) < ArchimedeanClass.mk (-t (n + 1)) := by
  simpa [ArchimedeanClass.mk_neg] using ht n

/-- **The canonical transfinite sum is odd**: `hahnSum (-t) = -hahnSum t`. The first
unconditional instance of canonicity respecting arithmetic: birthday-minimality transports
along negation because birthdays are negation-invariant. -/
theorem hahnSum_neg
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    hahnSum (strict_dominating_neg ht) = -hahnSum ht := by
  rw [hahnSum_eq_iff]
  refine ⟨(isHahnSum_hahnSum ht).neg, fun w hw ↦ ?_⟩
  have h1 : IsHahnSum t (-w) := by simpa using hw.neg
  calc (-hahnSum ht).birthday = (hahnSum ht).birthday := birthday_neg _
    _ ≤ (-w).birthday := birthday_hahnSum_le ht h1
    _ = w.birthday := birthday_neg w

/-! ### Level 2: birthday bounds for canonical sums -/

@[simp]
theorem birthday_abs (x : Surreal) : |x|.birthday = x.birthday := by
  rcases abs_choice x with h | h <;> simp [h]

theorem birthday_nsmul_le (n : ℕ) (x : Surreal) : (n • x).birthday ≤ n • x.birthday := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [succ_nsmul, succ_nsmul]
    exact (birthday_add_le _ _).trans (add_le_add ih le_rfl)

private theorem birthday_bandLo_le (t : ℕ → Surreal) (n : ℕ) :
    (bandLo t n).birthday ≤
      ⨆ k : ℕ, (((partialSum t n).birthday + (k + 1) • (t n).birthday + 1 : NatOrdinal) :
        WithTop NatOrdinal) := by
  refine (Cut.birthday_iInf_le _).trans (iSup_mono fun k ↦ ?_)
  rw [Cut.birthday_rightSurreal, ← WithTop.coe_add_one, WithTop.coe_le_coe]
  refine add_le_add ?_ le_rfl
  refine (birthday_sub_le _ _).trans (add_le_add le_rfl ?_)
  exact (birthday_nsmul_le _ _).trans_eq (by rw [birthday_abs])

private theorem birthday_bandHi_le (t : ℕ → Surreal) (n : ℕ) :
    (bandHi t n).birthday ≤
      ⨆ k : ℕ, (((partialSum t n).birthday + (k + 1) • (t n).birthday + 1 : NatOrdinal) :
        WithTop NatOrdinal) := by
  refine (Cut.birthday_iSup_le _).trans (iSup_mono fun k ↦ ?_)
  rw [Cut.birthday_leftSurreal, ← WithTop.coe_add_one, WithTop.coe_le_coe]
  refine add_le_add ?_ le_rfl
  refine (birthday_add_le _ _).trans (add_le_add le_rfl ?_)
  exact (birthday_nsmul_le _ _).trans_eq (by rw [birthday_abs])

theorem birthday_sumLo_le (t : ℕ → Surreal) :
    (sumLo t).birthday ≤
      ⨆ n : ℕ, ⨆ k : ℕ, (((partialSum t n).birthday + (k + 1) • (t n).birthday + 1 :
        NatOrdinal) : WithTop NatOrdinal) :=
  (Cut.birthday_iSup_le _).trans (iSup_mono fun n ↦ birthday_bandLo_le t n)

theorem birthday_sumHi_le (t : ℕ → Surreal) :
    (sumHi t).birthday ≤
      ⨆ n : ℕ, ⨆ k : ℕ, (((partialSum t n).birthday + (k + 1) • (t n).birthday + 1 :
        NatOrdinal) : WithTop NatOrdinal) :=
  (Cut.birthday_iInf_le _).trans (iSup_mono fun n ↦ birthday_bandHi_le t n)

/-- **The birthday bound for canonical sums** (`WithTop` form): the birthday of `hahnSum` is
at most the supremum over `n, k` of
`(birthday of the n-th partial sum) + (k+1) · (birthday of the n-th term) + 1`. -/
theorem birthday_hahnSum_le_iSup
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    ((hahnSum ht).birthday : WithTop NatOrdinal) ≤
      ⨆ n : ℕ, ⨆ k : ℕ, (((partialSum t n).birthday + (k + 1) • (t n).birthday + 1 :
        NatOrdinal) : WithTop NatOrdinal) :=
  (Cut.birthday_simplestBtwn_le (sumLo_lt_sumHi ht)).trans
    (max_le (birthday_sumLo_le t) (birthday_sumHi_le t))

/-- **The birthday bound for canonical sums**: an explicit `NatOrdinal`-valued bound from
the birthdays of the partial sums and terms of the series. -/
theorem birthday_hahnSum_le_sup
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    (hahnSum ht).birthday ≤
      ⨆ p : ℕ × ℕ, ((partialSum t p.1).birthday + (p.2 + 1) • (t p.1).birthday + 1) := by
  rw [← WithTop.coe_le_coe, WithTop.coe_iSup _ (NatOrdinal.bddAbove_of_small _)]
  refine (birthday_hahnSum_le_iSup ht).trans ?_
  refine iSup_le fun n ↦ iSup_le fun k ↦ ?_
  exact le_iSup_of_le (n, k) le_rfl

/-! ### Level 3: the geometric series -/

private theorem eps0_infinitesimal : Infinitesimal eps0 :=
  show Infinitesimal (ω^ (1 : Surreal))⁻¹ from infinitesimal_inv_wpow one_pos

private theorem eps0_pos : (0 : Surreal.{0}) < eps0 :=
  show (0 : Surreal) < (ω^ (1 : Surreal))⁻¹ from inv_pos.2 (wpow_pos _)

/-- The geometric series `Σ ω⁻ᵏ` is strictly dominating. -/
theorem geometric_strict_dominating (n : ℕ) :
    ArchimedeanClass.mk (eps0 ^ n) < ArchimedeanClass.mk (eps0 ^ (n + 1)) :=
  mk_pow_lt_mk_pow_succ eps0_infinitesimal eps0_pos n

/-- **The Hahn sums of the geometric series are exactly the micro-halo of `ω/(ω−1)`**: the
surreals whose distance to `ω/(ω−1)` is smaller than every scale `ω⁻ⁿ`. -/
theorem isHahnSum_geometric_iff {y : Surreal} :
    IsHahnSum (fun k ↦ eps0 ^ k) y ↔
      ∀ n, ArchimedeanClass.mk (eps0 ^ n) < ArchimedeanClass.mk (y - (1 - eps0)⁻¹) := by
  constructor
  · intro hy n
    exact (geometric_strict_dominating n).trans_le
      (IsHahnSum.mk_sub_le hy isHahnSum_geometric (n + 1))
  · intro h n
    have h1 : y - partialSum (fun k ↦ eps0 ^ k) n =
        (y - (1 - eps0)⁻¹) + ((1 - eps0)⁻¹ - partialSum (fun k ↦ eps0 ^ k) n) := by
      ring
    show ArchimedeanClass.mk (eps0 ^ n) ≤ _
    rw [h1]
    exact le_trans (le_min (h n).le (mk_sub_partialSum_geometric n).ge)
      (ArchimedeanClass.min_le_mk_add ..)

/-- Unconditionally: the canonical sum of the geometric series is at least as simple as
`ω/(ω−1)`. -/
theorem birthday_hahnSum_geometric_le :
    (hahnSum geometric_strict_dominating).birthday ≤ ((1 - eps0)⁻¹).birthday :=
  birthday_hahnSum_le _ isHahnSum_geometric

/-- **The geometric dichotomy**: the canonical sum of `Σ ω⁻ᵏ` either *is* `ω/(ω−1)`, or it
is strictly simpler. (Classical normal-form theory predicts the first alternative; deciding
it is exactly the halo-minimality conjecture below.) -/
theorem hahnSum_geometric_dichotomy :
    hahnSum geometric_strict_dominating = (1 - eps0)⁻¹ ∨
      (hahnSum geometric_strict_dominating).birthday < ((1 - eps0)⁻¹).birthday := by
  rcases eq_or_ne ((1 - eps0)⁻¹) (hahnSum geometric_strict_dominating) with h | h
  · exact .inl h.symm
  · exact .inr (birthday_hahnSum_lt_of_ne _ isHahnSum_geometric h)

/-- **Conditional identification of the geometric canonical sum**: if `ω/(ω−1)` is
birthday-minimal within its own micro-halo (a truncation-simplicity statement: adding a
perturbation below every scale `ω⁻ⁿ` cannot decrease the birthday), then the canonical
transfinite sum of `Σ ω⁻ᵏ` is exactly `ω/(ω−1)`. This isolates precisely what remains
open. -/
theorem hahnSum_geometric_eq_of_halo_minimal
    (H : ∀ w : Surreal, (∀ n, ArchimedeanClass.mk (eps0 ^ n) < ArchimedeanClass.mk w) →
      ((1 - eps0)⁻¹).birthday ≤ ((1 - eps0)⁻¹ + w).birthday) :
    hahnSum geometric_strict_dominating = (1 - eps0)⁻¹ := by
  rw [hahnSum_eq_iff]
  refine ⟨isHahnSum_geometric, fun w hw ↦ ?_⟩
  have h := isHahnSum_geometric_iff.1 hw
  have hw' : (1 - eps0)⁻¹ + (w - (1 - eps0)⁻¹) = w := by ring
  calc ((1 - eps0)⁻¹).birthday
      ≤ ((1 - eps0)⁻¹ + (w - (1 - eps0)⁻¹)).birthday := H _ h
    _ = w.birthday := by rw [hw']

/-! #### An exact canonical-sum evaluation: the telescoping series -/

private theorem mk_one_sub_eps0 : ArchimedeanClass.mk (1 - eps0) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [stdPart_sub isFinite_one eps0_infinitesimal.isFinite,
    eps0_infinitesimal.stdPart_eq_zero, ArchimedeanClass.stdPart_one]
  norm_num

private theorem mk_telescoping_term (k : ℕ) :
    ArchimedeanClass.mk (eps0 ^ k - eps0 ^ (k + 1)) = ArchimedeanClass.mk (eps0 ^ k) := by
  have h : eps0 ^ k - eps0 ^ (k + 1) = eps0 ^ k * (1 - eps0) := by ring
  rw [h, ArchimedeanClass.mk_mul, mk_one_sub_eps0, add_zero]

/-- The telescoping series `Σ (ω⁻ᵏ − ω⁻⁽ᵏ⁺¹⁾)` is strictly dominating. -/
theorem telescoping_strict_dominating (n : ℕ) :
    ArchimedeanClass.mk (eps0 ^ n - eps0 ^ (n + 1)) <
      ArchimedeanClass.mk (eps0 ^ (n + 1) - eps0 ^ (n + 1 + 1)) := by
  rw [mk_telescoping_term, mk_telescoping_term]
  exact geometric_strict_dominating n

private theorem partialSum_telescoping (n : ℕ) :
    partialSum (fun k ↦ eps0 ^ k - eps0 ^ (k + 1)) n = 1 - eps0 ^ n := by
  rw [partialSum, Finset.sum_range_sub' (fun k ↦ eps0 ^ k) n, pow_zero]

/-- `1` is a Hahn sum of the telescoping series `Σ (ω⁻ᵏ − ω⁻⁽ᵏ⁺¹⁾)`. -/
theorem isHahnSum_telescoping :
    IsHahnSum (fun k ↦ eps0 ^ k - eps0 ^ (k + 1)) 1 := by
  intro n
  show ArchimedeanClass.mk (eps0 ^ n - eps0 ^ (n + 1)) ≤ _
  rw [partialSum_telescoping, mk_telescoping_term]
  have h : (1 : Surreal) - (1 - eps0 ^ n) = eps0 ^ n := by ring
  rw [h]

/-- **An exact canonical transfinite sum**: the canonical sum of the telescoping series
`Σ (ω⁻ᵏ − ω⁻⁽ᵏ⁺¹⁾)` is exactly `1`. Every other Hahn sum of this series is `1` plus a
nonzero perturbation below all scales `ω⁻ⁿ`, hence is nonzero and has birthday
`≥ 1 = birthday 1`; the characterization theorem then evaluates the canonical sum on the
nose. The first closed-form evaluation of a canonical transfinite sum. -/
theorem hahnSum_telescoping_eq_one :
    hahnSum telescoping_strict_dominating = 1 := by
  rw [hahnSum_eq_iff]
  refine ⟨isHahnSum_telescoping, fun w hw ↦ ?_⟩
  have h1 := IsHahnSum.mk_sub_le hw isHahnSum_telescoping 1
  have h2 : (0 : ArchimedeanClass Surreal) < ArchimedeanClass.mk (w - 1) := by
    refine lt_of_lt_of_le ?_ h1
    show (0 : ArchimedeanClass Surreal) <
      ArchimedeanClass.mk (eps0 ^ 1 - eps0 ^ (1 + 1))
    rw [mk_telescoping_term, pow_one]
    exact eps0_infinitesimal
  have hne : w ≠ 0 := by
    rintro rfl
    rw [zero_sub, ArchimedeanClass.mk_neg, ArchimedeanClass.mk_one] at h2
    exact lt_irrefl _ h2
  have h0 : w.birthday ≠ 0 := fun h ↦ hne (birthday_eq_zero.1 h)
  have h3 : (0 : NatOrdinal) < w.birthday := by
    have hb : w.birthday ≠ ⊥ := by simpa using h0
    simpa using hb.bot_lt
  rw [birthday_one]
  calc (1 : NatOrdinal) = 0 + 1 := (zero_add 1).symm
    _ ≤ w.birthday := Order.add_one_le_of_lt h3

/-! #### A birthday lower bound: nonzero infinitesimals are born at or after day `ω` -/

/-- **A birthday lower bound**: a surreal infinitesimally close to, but distinct from, a
surreal of finite birthday (i.e. a dyadic rational) has birthday at least `ω`. -/
theorem omega0_le_birthday_of_infinitesimal_sub {x c : Surreal}
    (hc : c.birthday < NatOrdinal.of Ordinal.omega0)
    (hx : Infinitesimal (x - c)) (hne : x ≠ c) :
    NatOrdinal.of Ordinal.omega0 ≤ x.birthday := by
  by_contra h
  rw [not_le] at h
  obtain ⟨q, hq⟩ := Surreal.birthday_lt_omega0_iff.1 h
  obtain ⟨r, hr⟩ := Surreal.birthday_lt_omega0_iff.1 hc
  have hq' : ((q : ℚ) : Surreal) = x := hq
  have hr' : ((r : ℚ) : Surreal) = c := hr
  have hqr : ((q : ℚ) - (r : ℚ) : ℚ) ≠ 0 := by
    intro h0
    apply hne
    rw [← hq', ← hr', sub_eq_zero.1 h0]
  have hcast : x - c = (((q : ℚ) - (r : ℚ) : ℚ) : Surreal) := by
    rw [← hq', ← hr', Rat.cast_sub]
  have hmk : ArchimedeanClass.mk (x - c) = 0 := by
    rw [hcast, ← Real.toSurreal_ratCast]
    exact mk_realCast (Rat.cast_ne_zero.2 hqr)
  rw [Infinitesimal, hmk] at hx
  exact lt_irrefl _ hx

/-- **Nonzero infinitesimals have birthday at least `ω`**: below day `ω`, every surreal is
a dyadic rational, and nonzero rationals are not infinitesimal. The first nontrivial
birthday *lower* bound in this development. -/
theorem omega0_le_birthday_of_infinitesimal {x : Surreal} (hx : Infinitesimal x)
    (hx0 : x ≠ 0) : NatOrdinal.of Ordinal.omega0 ≤ x.birthday := by
  refine omega0_le_birthday_of_infinitesimal_sub (c := 0) ?_ (by rwa [sub_zero]) hx0
  rw [birthday_zero, ← NatOrdinal.of_zero, NatOrdinal.of_lt_iff, NatOrdinal.val_of]
  exact Ordinal.omega0_pos

/-- **The cost of non-uniqueness**: two distinct Hahn sums of a strictly dominating series
whose terms reach infinitesimal scale differ by a nonzero infinitesimal, so their difference
has birthday at least `ω`. -/
theorem omega0_le_birthday_sub_of_isHahnSum {x y : Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hx : IsHahnSum t x) (hy : IsHahnSum t y) (hne : x ≠ y)
    (h0 : ∃ n, 0 ≤ ArchimedeanClass.mk (t n)) :
    NatOrdinal.of Ordinal.omega0 ≤ (x - y).birthday := by
  obtain ⟨n, hn⟩ := h0
  refine omega0_le_birthday_of_infinitesimal ?_ (sub_ne_zero.2 hne)
  exact lt_of_le_of_lt hn ((ht n).trans_le (IsHahnSum.mk_sub_le hx hy (n + 1)))

/-! #### The birthday sandwich for the canonical geometric sum -/

private theorem one_not_isHahnSum_geometric : ¬ IsHahnSum (fun k ↦ eps0 ^ k) 1 := by
  intro h
  have h2 : ArchimedeanClass.mk (eps0 ^ 2) ≤
      ArchimedeanClass.mk (1 - partialSum (fun k ↦ eps0 ^ k) 2) := h 2
  have hs : partialSum (fun k ↦ eps0 ^ k) 2 = 1 + eps0 := by
    rw [partialSum, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
  have h3 : (1 : Surreal) - (1 + eps0) = -eps0 := by ring
  rw [hs, h3, ArchimedeanClass.mk_neg] at h2
  have h4 : ArchimedeanClass.mk (eps0 ^ 1) < ArchimedeanClass.mk (eps0 ^ 2) :=
    geometric_strict_dominating 1
  rw [pow_one] at h4
  exact absurd h2 (not_le.2 h4)

private theorem infinitesimal_sub_one_of_isHahnSum_geometric {w : Surreal}
    (hw : IsHahnSum (fun k ↦ eps0 ^ k) w) : Infinitesimal (w - 1) := by
  have h1 : ArchimedeanClass.mk (eps0 ^ 1) ≤
      ArchimedeanClass.mk (w - partialSum (fun k ↦ eps0 ^ k) 1) := hw 1
  have hs1 : partialSum (fun k ↦ eps0 ^ k) 1 = 1 := by
    rw [partialSum, Finset.sum_range_one, pow_zero]
  rw [hs1, pow_one] at h1
  exact lt_of_lt_of_le eps0_infinitesimal h1

/-- Every Hahn sum of the geometric series has birthday at least `ω`: it is
infinitesimally close to `1` but — since `1` itself is *not* a Hahn sum — distinct from
it. -/
theorem omega0_le_birthday_of_isHahnSum_geometric {w : Surreal}
    (hw : IsHahnSum (fun k ↦ eps0 ^ k) w) :
    NatOrdinal.of Ordinal.omega0 ≤ w.birthday := by
  refine omega0_le_birthday_of_infinitesimal_sub ?_
    (infinitesimal_sub_one_of_isHahnSum_geometric hw) ?_
  · rw [birthday_one, ← NatOrdinal.of_one, NatOrdinal.of_lt_iff, NatOrdinal.val_of]
    exact Ordinal.one_lt_omega0
  · intro h0
    exact one_not_isHahnSum_geometric (h0 ▸ hw)

/-- **The birthday sandwich**: the canonical sum of the geometric series is born at or
after day `ω`, and no later than `ω/(ω−1)`. (Contrast with the telescoping series, whose
canonical sum has birthday `1`: canonical sums genuinely inhabit the transfinite range.) -/
theorem omega0_le_birthday_hahnSum_geometric :
    NatOrdinal.of Ordinal.omega0 ≤ (hahnSum geometric_strict_dominating).birthday :=
  omega0_le_birthday_of_isHahnSum_geometric (isHahnSum_hahnSum _)

/-- The canonical geometric sum is infinitesimally close to `1`, so its standard part is
`1` — as it must be, since `Σ 1/ωᵏ` "evaluates" to `1 + 1/(ω−1)`. -/
theorem stdPart_hahnSum_geometric :
    stdPart (hahnSum geometric_strict_dominating) = 1 := by
  have hinf := infinitesimal_sub_one_of_isHahnSum_geometric
    (isHahnSum_hahnSum geometric_strict_dominating)
  have hsplit : hahnSum geometric_strict_dominating =
      1 + (hahnSum geometric_strict_dominating - 1) := by ring
  rw [hsplit, stdPart_add_eq_left hinf, ArchimedeanClass.stdPart_one]

/-! #### A transfinite exact evaluation: `hahnSum (Σ ω·(ω⁻ᵏ − ω⁻⁽ᵏ⁺¹⁾)) = ω` -/

/-- **The birthday of `ω` is `ω`**: the surreal `ω^ 1` is the image of the ordinal `ω`
under the ordinal embedding, whose birthday is itself. -/
theorem birthday_wpow_one :
    (ω^ (1 : Surreal)).birthday = NatOrdinal.of Ordinal.omega0 := by
  have h : (ω^ (1 : Surreal)) = (ω^ (1 : NatOrdinal)).toSurreal := by
    rw [toSurreal_wpow, NatOrdinal.toSurreal_one]
  rw [h, birthday_toSurreal, NatOrdinal.wpow_def, NatOrdinal.val_one, Ordinal.opow_one]

private theorem mk_mul_lt_mk_mul {c a b : Surreal} (hc : 0 < c)
    (h : ArchimedeanClass.mk a < ArchimedeanClass.mk b) :
    ArchimedeanClass.mk (c * a) < ArchimedeanClass.mk (c * b) := by
  rw [ArchimedeanClass.mk_lt_mk] at h ⊢
  intro j
  calc j • |c * b| = c * (j • |b|) := by
        rw [abs_mul, abs_of_pos hc, nsmul_eq_mul, nsmul_eq_mul]; ring
    _ < c * |a| := mul_lt_mul_of_pos_left (h j) hc
    _ = |c * a| := by rw [abs_mul, abs_of_pos hc]

/-- The `ω`-scaled telescoping series `Σ ω·(ω⁻ᵏ − ω⁻⁽ᵏ⁺¹⁾)` is strictly dominating. -/
theorem omega_telescoping_strict_dominating (n : ℕ) :
    ArchimedeanClass.mk (ω^ (1 : Surreal) * (eps0 ^ n - eps0 ^ (n + 1))) <
      ArchimedeanClass.mk (ω^ (1 : Surreal) * (eps0 ^ (n + 1) - eps0 ^ (n + 1 + 1))) :=
  mk_mul_lt_mk_mul (wpow_pos _) (telescoping_strict_dominating n)

private theorem partialSum_omega_telescoping (n : ℕ) :
    partialSum (fun k ↦ ω^ (1 : Surreal) * (eps0 ^ k - eps0 ^ (k + 1))) n =
      ω^ (1 : Surreal) * (1 - eps0 ^ n) := by
  rw [partialSum, ← Finset.mul_sum, ← partialSum, partialSum_telescoping]

/-- `ω` is a Hahn sum of the `ω`-scaled telescoping series. -/
theorem isHahnSum_omega_telescoping :
    IsHahnSum (fun k ↦ ω^ (1 : Surreal) * (eps0 ^ k - eps0 ^ (k + 1)))
      (ω^ (1 : Surreal)) := by
  intro n
  show ArchimedeanClass.mk (ω^ (1 : Surreal) * (eps0 ^ n - eps0 ^ (n + 1))) ≤ _
  rw [partialSum_omega_telescoping]
  have hres : ω^ (1 : Surreal) - ω^ (1 : Surreal) * (1 - eps0 ^ n) =
      ω^ (1 : Surreal) * eps0 ^ n := by ring
  rw [hres, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, mk_telescoping_term]

private theorem infinitesimal_sub_omega_of_isHahnSum {w : Surreal}
    (hw : IsHahnSum (fun k ↦ ω^ (1 : Surreal) * (eps0 ^ k - eps0 ^ (k + 1))) w) :
    Infinitesimal (w - ω^ (1 : Surreal)) := by
  have h2 := IsHahnSum.mk_sub_le hw isHahnSum_omega_telescoping 2
  refine lt_of_lt_of_le ?_ h2
  show (0 : ArchimedeanClass Surreal) <
    ArchimedeanClass.mk (ω^ (1 : Surreal) * (eps0 ^ 2 - eps0 ^ (2 + 1)))
  have h0 : (ω^ (1 : Surreal)) ≠ 0 := (wpow_pos _).ne'
  have hcalc : ω^ (1 : Surreal) * eps0 ^ 2 = eps0 := by
    rw [eps0_def, pow_two, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
  rw [ArchimedeanClass.mk_mul, mk_telescoping_term, ← ArchimedeanClass.mk_mul, hcalc]
  exact eps0_infinitesimal

/-- Every Hahn sum of the `ω`-scaled telescoping series has birthday at least `ω`: it is
infinitesimally close to `ω`, hence infinite, hence not a dyadic rational. -/
theorem omega0_le_birthday_of_isHahnSum_omega_telescoping {w : Surreal}
    (hw : IsHahnSum (fun k ↦ ω^ (1 : Surreal) * (eps0 ^ k - eps0 ^ (k + 1))) w) :
    NatOrdinal.of Ordinal.omega0 ≤ w.birthday := by
  have hinf := infinitesimal_sub_omega_of_isHahnSum hw
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨q, hq⟩ := Surreal.birthday_lt_omega0_iff.1 hlt
  have hq' : ((q : ℚ) : Surreal) = w := hq
  set m : ℕ := ⌈|(q : ℚ)|⌉₊ with hm
  have hwm : w ≤ (m : Surreal) := by
    rw [← hq']
    have h1 : (q : ℚ) ≤ (m : ℚ) := (le_abs_self _).trans (Nat.le_ceil _)
    have h2 := Rat.cast_le (K := Surreal).2 h1
    push_cast at h2 ⊢
    exact h2
  have habs : |w - ω^ (1 : Surreal)| < 1 := by
    simpa using infinitesimal_iff.1 hinf 1
  have h3 : ω^ (1 : Surreal) < ((m + 1 : ℕ) : Surreal) := by
    have h4 := (abs_lt.1 habs).1
    push_cast
    linarith
  exact absurd h3 (natCast_lt_wpow_one (m + 1)).asymm

/-- **A transfinite exact evaluation**: the canonical transfinite sum of the `ω`-scaled
telescoping series `Σ ω·(ω⁻ᵏ − ω⁻⁽ᵏ⁺¹⁾)` is exactly `ω`. Minimality is unconditional:
`birthday ω = ω`, while every other Hahn sum is infinitesimally close to `ω` and hence
also born no earlier than day `ω`. Together with `hahnSum_telescoping_eq_one`, the
canonical-sum operator provably computes exact values at finite and transfinite birthdays
alike. -/
theorem hahnSum_omega_telescoping_eq :
    hahnSum omega_telescoping_strict_dominating = ω^ (1 : Surreal) := by
  rw [hahnSum_eq_iff]
  refine ⟨isHahnSum_omega_telescoping, fun w hw ↦ ?_⟩
  rw [birthday_wpow_one]
  exact omega0_le_birthday_of_isHahnSum_omega_telescoping hw

/-! ### Level 4: the additivity and multiplicativity frontier -/

theorem partialSum_add (t u : ℕ → Surreal) (n : ℕ) :
    partialSum (fun k ↦ t k + u k) n = partialSum t n + partialSum u n := by
  simp [partialSum, Finset.sum_add_distrib]

/-- **Hahn sums add**, given termwise non-cancellation: if no term of `t + u` drops to a
finer scale than both of its summands, then the sum of Hahn sums is a Hahn sum of the
termwise sum. -/
theorem IsHahnSum.add {x y : Surreal}
    (hx : IsHahnSum t x) (hy : IsHahnSum u y)
    (h : ∀ n, ArchimedeanClass.mk (t n + u n) ≤
      min (ArchimedeanClass.mk (t n)) (ArchimedeanClass.mk (u n))) :
    IsHahnSum (fun n ↦ t n + u n) (x + y) := by
  intro n
  have hsplit : x + y - partialSum (fun k ↦ t k + u k) n =
      (x - partialSum t n) + (y - partialSum u n) := by
    rw [partialSum_add]; ring
  show ArchimedeanClass.mk (t n + u n) ≤ _
  rw [hsplit]
  exact le_trans (h n) (le_trans (min_le_min (hx n) (hy n))
    (ArchimedeanClass.min_le_mk_add ..))

/-- Termwise non-cancellation preserves strict domination. -/
theorem strict_dominating_add
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (h : ∀ n, ArchimedeanClass.mk (t n + u n) ≤
      min (ArchimedeanClass.mk (t n)) (ArchimedeanClass.mk (u n))) (n : ℕ) :
    ArchimedeanClass.mk (t n + u n) < ArchimedeanClass.mk (t (n + 1) + u (n + 1)) := by
  have h1 : ArchimedeanClass.mk (t n + u n) =
      min (ArchimedeanClass.mk (t n)) (ArchimedeanClass.mk (u n)) :=
    le_antisymm (h n) (ArchimedeanClass.min_le_mk_add ..)
  rw [h1]
  exact (min_lt_min (ht n) (hu n)).trans_le
    (le_trans (le_of_eq (le_antisymm (h (n + 1)) (ArchimedeanClass.min_le_mk_add ..)).symm)
      le_rfl)

/-- **Additivity of the canonical sum, reduced to a birthday inequality**: for
non-cancelling strictly dominating series, `hahnSum (t + u) = hahnSum t + hahnSum u` holds
**iff** the sum of the canonical sums is birthday-minimal among the Hahn sums of `t + u`.
The truncation-simplicity heuristic predicts this holds; deciding it requires normal-form
birthday theory. -/
theorem hahnSum_add_eq_iff
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (h : ∀ n, ArchimedeanClass.mk (t n + u n) ≤
      min (ArchimedeanClass.mk (t n)) (ArchimedeanClass.mk (u n))) :
    hahnSum (strict_dominating_add ht hu h) = hahnSum ht + hahnSum hu ↔
      ∀ z, IsHahnSum (fun n ↦ t n + u n) z →
        (hahnSum ht + hahnSum hu).birthday ≤ z.birthday := by
  constructor
  · intro heq z hz
    rw [← heq]
    exact birthday_hahnSum_le _ hz
  · intro hmin
    exact (hahnSum_eq_iff _).2
      ⟨(isHahnSum_hahnSum ht).add (isHahnSum_hahnSum hu) h, hmin⟩

/-- If additivity of the canonical sum *fails* at `(t, u)`, then the canonical sum of
`t + u` is **strictly simpler** than `hahnSum t + hahnSum u`. -/
theorem birthday_hahnSum_add_lt_of_ne
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (h : ∀ n, ArchimedeanClass.mk (t n + u n) ≤
      min (ArchimedeanClass.mk (t n)) (ArchimedeanClass.mk (u n)))
    (hne : hahnSum ht + hahnSum hu ≠ hahnSum (strict_dominating_add ht hu h)) :
    (hahnSum (strict_dominating_add ht hu h)).birthday <
      (hahnSum ht + hahnSum hu).birthday :=
  birthday_hahnSum_lt_of_ne _ ((isHahnSum_hahnSum ht).add (isHahnSum_hahnSum hu) h) hne

/-- **The exponential functional equation, reduced to a birthday inequality**: for positive
infinitesimals, `expInf (ε + δ) = expInf ε * expInf δ` holds **iff** the product
`expInf ε * expInf δ` is birthday-minimal among the Hahn sums of the exponential series at
`ε + δ`. This is the sharpest currently-provable form of the multiplicativity question
surfaced by `Infinity.ExpMul`. -/
theorem expInf_add_eq_mul_iff {ε δ : Surreal} (hε : Infinitesimal ε) (hδ : Infinitesimal δ)
    (hε0 : 0 < ε) (hδ0 : 0 < δ) :
    expInf (ε + δ) (hε.add hδ) (by positivity) = expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne' ↔
      ∀ z, IsHahnSum (fun k ↦ (ε + δ) ^ k / ((k.factorial : ℕ) : Surreal)) z →
        (expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne').birthday ≤ z.birthday := by
  constructor
  · intro heq z hz
    rw [← heq]
    exact birthday_expInf_le _ _ hz
  · intro hmin
    exact (hahnSum_eq_iff _).2 ⟨isHahnSum_expInf_mul hε hδ hε0 hδ0, hmin⟩

/-- If the exponential functional equation *fails* at `(ε, δ)`, then the canonical value
`expInf (ε + δ)` is **strictly simpler** than the product `expInf ε * expInf δ`. -/
theorem birthday_expInf_add_lt_of_mul_ne {ε δ : Surreal} (hε : Infinitesimal ε)
    (hδ : Infinitesimal δ) (hε0 : 0 < ε) (hδ0 : 0 < δ)
    (hne : expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne' ≠
      expInf (ε + δ) (hε.add hδ) (by positivity)) :
    (expInf (ε + δ) (hε.add hδ) (by positivity)).birthday <
      (expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne').birthday :=
  birthday_hahnSum_lt_of_ne _ (isHahnSum_expInf_mul hε hδ hε0 hδ0) hne

end Surreal

end
