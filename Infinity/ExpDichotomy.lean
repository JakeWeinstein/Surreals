import Infinity.GameCofinality
import Infinity.ExpLadder

/-!
# The multiplicativity dichotomy: `exp(σ+τ) = exp σ · exp τ` iff the classes are comparable

`Infinity.GameCofinality` proved the exponential functional equation
`expInf (σ + τ) = expInf σ * expInf τ` for all positive infinitesimals `σ, τ` with
*comparable* Archimedean classes (`mk σ ≤ K • mk τ` and `mk τ ≤ K • mk σ` for some `K`).
This file proves that comparability is also *necessary*, so the functional equation becomes
an if-and-only-if — and on the way it proves that the canonical-sum exponential is *blind*
to any perturbation infinitely finer than every power of its argument.

* **The congruence lemma** `Surreal.isHahnSum_congr` / `Surreal.hahnSum_congr`: if two
  series have termwise equal classes and their partial sums differ by something strictly
  finer than the current term, they have exactly the same Hahn sums, hence the same
  canonical sum (both directions of `hahnSum_eq_iff`).
* **The blindness theorem** `Surreal.expInf_add_eq_of_forall_nsmul_lt`: if
  `k • mk σ < mk τ` for every `k : ℕ` (`τ` is strictly finer than every power of `σ`), then
  `expInf (σ + τ) = expInf σ`. Proof: the exponential series at `σ + τ` and at `σ` satisfy
  the congruence lemma, because `mk (σ + τ) = mk σ` and
  `(σ+τ)^k − σ^k = τ · Σ_{j<k} (σ+τ)^j σ^{k−1−j}` has class at least `mk τ`.
* **The failure** `Surreal.expInf_add_ne_mul_of_forall_nsmul_lt`: under the same
  hypothesis `expInf (σ + τ) ≠ expInf σ * expInf τ`, because `expInf τ > 1`.
* **The trichotomy** `Surreal.classComparable_or_forall_nsmul_lt`: two infinitesimals
  either have comparable classes (`Surreal.ClassComparable`), or one is strictly finer than
  every power of the other.
* **THE DICHOTOMY** `Surreal.expInf_add_eq_mul_iff_classComparable`: for positive
  infinitesimals,
  `expInf (σ + τ) = expInf σ * expInf τ ↔ ClassComparable σ τ`.
* **Consequences**: the iterate law `Surreal.expInf_succ_nsmul`
  (`expInf ((n+1) • σ) = expInf σ ^ (n+1)`), the root law `Surreal.expInf_eq_pow_expInf_div`
  (`expInf σ = expInf (σ/(n+1)) ^ (n+1)`) with its half case
  `Surreal.expInf_eq_sq_expInf_half`, and non-injectivity
  `Surreal.expInf_not_injective_of_forall_nsmul_lt` (`σ + τ ≠ σ` yet the values agree);
  the concrete witness `Surreal.expInf_wpow_neg_one_add_wpow_neg_omega`
  (`expInf (ω⁻¹ + ω^(−ω)) = expInf ω⁻¹`) and its failed functional equation
  `Surreal.expInf_wpow_neg_one_add_wpow_neg_omega_ne_mul`.

The moral: the canonical exponential is multiplicative exactly when it can see both of its
arguments.
-/

open ArchimedeanClass Finset

universe u

noncomputable section

namespace Surreal

/-! ### Class bounds on finite sums -/

/-- A class bound shared by all summands passes to the sum (`mk 0 = ⊤`). -/
theorem le_mk_sum {ι : Type*} {c : ArchimedeanClass Surreal.{u}} {s : Finset ι}
    {f : ι → Surreal.{u}} (h : ∀ i ∈ s, c ≤ ArchimedeanClass.mk (f i)) :
    c ≤ ArchimedeanClass.mk (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (fun x ↦ c ≤ ArchimedeanClass.mk x) ?_ ?_ h
  · intro a b ha hb
    exact le_trans (le_min ha hb) (ArchimedeanClass.min_le_mk_add a b)
  · rw [ArchimedeanClass.mk_zero]
    exact le_top

/-! ### The congruence lemma -/

/-- **The congruence lemma for Hahn sums.** If two series have termwise equal classes
(`mk (t N) = mk (t' N)`) and their partial sums differ by something strictly finer than the
current term (`mk (t N) < mk (s'_N − s_N)`), then they have exactly the same Hahn sums:
`z − s'_N = (z − s_N) − (s'_N − s_N)` and `mk (a − b) ≥ min (mk a) (mk b)`. -/
theorem isHahnSum_congr {t t' : ℕ → Surreal.{u}} {z : Surreal.{u}}
    (hmk : ∀ N, ArchimedeanClass.mk (t N) = ArchimedeanClass.mk (t' N))
    (hps : ∀ N, ArchimedeanClass.mk (t N) <
      ArchimedeanClass.mk (partialSum t' N - partialSum t N)) :
    IsHahnSum t z ↔ IsHahnSum t' z := by
  constructor
  · intro hz N
    have h1 : z - partialSum t' N =
        (z - partialSum t N) - (partialSum t' N - partialSum t N) := by ring
    rw [h1, ← hmk N]
    exact le_trans (le_min (hz N) (hps N).le) (ArchimedeanClass.min_le_mk_sub _ _)
  · intro hz N
    have h1 : z - partialSum t N =
        (z - partialSum t' N) + (partialSum t' N - partialSum t N) := by ring
    rw [h1]
    exact le_trans (le_min ((hmk N).trans_le (hz N)) (hps N).le)
      (ArchimedeanClass.min_le_mk_add _ _)

/-- Termwise equal classes transport strict domination. -/
theorem strictDominating_of_mk_eq {t t' : ℕ → Surreal.{u}}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hmk : ∀ N, ArchimedeanClass.mk (t N) = ArchimedeanClass.mk (t' N)) (n : ℕ) :
    ArchimedeanClass.mk (t' n) < ArchimedeanClass.mk (t' (n + 1)) := by
  rw [← hmk n, ← hmk (n + 1)]
  exact ht n

/-- **The congruence lemma for canonical sums**: under the hypotheses of `isHahnSum_congr`,
the canonical sums coincide (the two series have the same Hahn sums, hence the same
birthday-minimal Hahn sum). -/
theorem hahnSum_congr {t t' : ℕ → Surreal.{u}}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (ht' : ∀ n, ArchimedeanClass.mk (t' n) < ArchimedeanClass.mk (t' (n + 1)))
    (hmk : ∀ N, ArchimedeanClass.mk (t N) = ArchimedeanClass.mk (t' N))
    (hps : ∀ N, ArchimedeanClass.mk (t N) <
      ArchimedeanClass.mk (partialSum t' N - partialSum t N)) :
    hahnSum ht = hahnSum ht' := by
  rw [hahnSum_eq_iff ht]
  refine ⟨(isHahnSum_congr hmk hps).2 (isHahnSum_hahnSum ht'), fun w hw ↦ ?_⟩
  exact birthday_hahnSum_le ht' ((isHahnSum_congr hmk hps).1 hw)

/-! ### The blindness theorem -/

/-- The class of an exponential-series term. -/
private theorem mk_expTerm {ε : Surreal.{u}} (k : ℕ) :
    ArchimedeanClass.mk (ε ^ k / ((k.factorial : ℕ) : Surreal)) =
      k • ArchimedeanClass.mk ε := by
  rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero, ArchimedeanClass.mk_pow]

/-- `(σ+τ)^k − σ^k = τ · Σ_{j<k} (σ+τ)^j σ^{k−1−j}` is `τ` times a finite quantity, so its
class is at least `mk τ`. -/
theorem mk_le_mk_add_pow_sub_pow {σ τ : Surreal.{u}} (hσ : Infinitesimal σ)
    (hτ : Infinitesimal τ) (k : ℕ) :
    ArchimedeanClass.mk τ ≤ ArchimedeanClass.mk ((σ + τ) ^ k - σ ^ k) := by
  have h := geom_sum₂_mul (σ + τ) σ k
  rw [add_sub_cancel_left] at h
  rw [← h, ArchimedeanClass.mk_mul]
  refine le_add_of_nonneg_left (le_mk_sum fun i _ ↦ ?_)
  exact ((hσ.add hτ).isFinite.pow i).mul (hσ.isFinite.pow _)

/-- If `τ` is strictly finer than every power of `σ`, then `mk (σ + τ) = mk σ`. -/
theorem mk_add_eq_of_forall_nsmul_lt {σ τ : Surreal.{u}}
    (hfine : ∀ k : ℕ, k • ArchimedeanClass.mk σ < ArchimedeanClass.mk τ) :
    ArchimedeanClass.mk (σ + τ) = ArchimedeanClass.mk σ := by
  apply ArchimedeanClass.mk_add_eq_mk_left
  simpa using hfine 1

theorem add_ne_zero_of_forall_nsmul_lt {σ τ : Surreal.{u}} (hσ0 : σ ≠ 0)
    (hfine : ∀ k : ℕ, k • ArchimedeanClass.mk σ < ArchimedeanClass.mk τ) :
    σ + τ ≠ 0 := by
  intro h
  have hμ := mk_add_eq_of_forall_nsmul_lt hfine
  rw [h, ArchimedeanClass.mk_zero] at hμ
  exact hσ0 (ArchimedeanClass.mk_eq_top_iff.1 hμ.symm)

/-- **THE BLINDNESS THEOREM**: the canonical-sum exponential cannot see a perturbation that
is infinitely finer than every power of its argument. If `k • mk σ < mk τ` for every
`k : ℕ`, then `expInf (σ + τ) = expInf σ`.

Proof: the exponential series at `σ + τ` and at `σ` satisfy the congruence lemma
`hahnSum_congr` — their terms have equal classes `N • mk σ` (since `mk (σ + τ) = mk σ`),
and their partial sums differ by `Σ_{k<N} ((σ+τ)^k − σ^k)/k!`, each summand of which is
`τ` times a finite quantity, so the difference has class `≥ mk τ > N • mk σ`. -/
theorem expInf_add_eq_of_forall_nsmul_lt {σ τ : Surreal.{u}}
    (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) (hσ0 : σ ≠ 0) (hστ0 : σ + τ ≠ 0)
    (hfine : ∀ k : ℕ, k • ArchimedeanClass.mk σ < ArchimedeanClass.mk τ) :
    expInf (σ + τ) (hσ.add hτ) hστ0 = expInf σ hσ hσ0 := by
  have hμ : ArchimedeanClass.mk (σ + τ) = ArchimedeanClass.mk σ :=
    mk_add_eq_of_forall_nsmul_lt hfine
  unfold expInf
  refine hahnSum_congr _ _ (fun N ↦ ?_) (fun N ↦ ?_)
  · rw [mk_expTerm, mk_expTerm, hμ]
  · rw [mk_expTerm, hμ]
    refine (hfine N).trans_le ?_
    rw [partialSum, partialSum, ← Finset.sum_sub_distrib]
    refine le_mk_sum fun k _ ↦ ?_
    rw [← sub_div, ArchimedeanClass.mk_div, mk_factorial, sub_zero,
      ArchimedeanClass.mk_sub_comm]
    exact mk_le_mk_add_pow_sub_pow hσ hτ k

/-- The blindness theorem for positive infinitesimals (no nonvanishing side conditions). -/
theorem expInf_add_eq_of_forall_nsmul_lt_of_pos {σ τ : Surreal.{u}}
    (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) (hσ0 : 0 < σ) (hτ0 : 0 < τ)
    (hfine : ∀ k : ℕ, k • ArchimedeanClass.mk σ < ArchimedeanClass.mk τ) :
    expInf (σ + τ) (hσ.add hτ) (by positivity) = expInf σ hσ hσ0.ne' :=
  expInf_add_eq_of_forall_nsmul_lt hσ hτ hσ0.ne' _ hfine

/-! ### The failure of the functional equation below every power -/

/-- **The failure**: when `τ` is strictly finer than every power of `σ`, the functional
equation fails — `expInf (σ + τ) = expInf σ` by blindness, while
`expInf σ * expInf τ > expInf σ` because `expInf τ > 1`. -/
theorem expInf_add_ne_mul_of_forall_nsmul_lt {σ τ : Surreal.{u}}
    (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) (hσ0 : 0 < σ) (hτ0 : 0 < τ)
    (hfine : ∀ k : ℕ, k • ArchimedeanClass.mk σ < ArchimedeanClass.mk τ) :
    expInf (σ + τ) (hσ.add hτ) (by positivity) ≠
      expInf σ hσ hσ0.ne' * expInf τ hτ hτ0.ne' := by
  rw [expInf_add_eq_of_forall_nsmul_lt hσ hτ hσ0.ne' _ hfine]
  intro h
  have h1 := one_lt_expInf hσ hσ0
  have h2 := one_lt_expInf hτ hτ0
  have h3 : expInf σ hσ hσ0.ne' < expInf σ hσ hσ0.ne' * expInf τ hτ hτ0.ne' :=
    lt_mul_of_one_lt_right (zero_lt_one.trans h1) h2
  exact absurd h h3.ne

/-! ### Comparable classes and the trichotomy -/

/-- Two surreals have **comparable Archimedean classes** when each class is bounded by a
natural multiple of the other: `mk σ ≤ K • mk τ` and `mk τ ≤ K • mk σ` for some `K : ℕ`.
For infinitesimals: each is at least as coarse as some power of the other. -/
def ClassComparable (σ τ : Surreal.{u}) : Prop :=
  ∃ K : ℕ, ArchimedeanClass.mk σ ≤ K • ArchimedeanClass.mk τ ∧
    ArchimedeanClass.mk τ ≤ K • ArchimedeanClass.mk σ

theorem ClassComparable.symm {σ τ : Surreal.{u}} (h : ClassComparable σ τ) :
    ClassComparable τ σ :=
  let ⟨K, h1, h2⟩ := h
  ⟨K, h2, h1⟩

theorem ClassComparable.refl (σ : Surreal.{u}) : ClassComparable σ σ :=
  ⟨1, by simp, by simp⟩

theorem ClassComparable.of_mk_eq {σ τ : Surreal.{u}}
    (h : ArchimedeanClass.mk σ = ArchimedeanClass.mk τ) : ClassComparable σ τ :=
  ⟨1, by rw [one_nsmul, h], by rw [one_nsmul, h]⟩

/-- Comparability is transitive (`mk σ ≤ K • mk τ ≤ (K L) • mk ρ`). -/
theorem ClassComparable.trans {σ τ ρ : Surreal.{u}}
    (h1 : ClassComparable σ τ) (h2 : ClassComparable τ ρ) : ClassComparable σ ρ := by
  obtain ⟨K, hστ, hτσ⟩ := h1
  obtain ⟨L, hτρ, hρτ⟩ := h2
  refine ⟨K * L, ?_, ?_⟩
  · calc ArchimedeanClass.mk σ ≤ K • ArchimedeanClass.mk τ := hστ
      _ ≤ K • (L • ArchimedeanClass.mk ρ) := nsmul_le_nsmul_right hτρ K
      _ = (K * L) • ArchimedeanClass.mk ρ := (mul_nsmul' _ _ _).symm
  · calc ArchimedeanClass.mk ρ ≤ L • ArchimedeanClass.mk τ := hρτ
      _ ≤ L • (K • ArchimedeanClass.mk σ) := nsmul_le_nsmul_right hτσ L
      _ = (K * L) • ArchimedeanClass.mk σ := by rw [← mul_nsmul', mul_comm]

/-- **The class trichotomy**: two infinitesimals either have comparable classes, or one of
them is strictly finer than every power of the other. -/
theorem classComparable_or_forall_nsmul_lt {σ τ : Surreal.{u}}
    (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) :
    ClassComparable σ τ ∨
      (∀ k : ℕ, k • ArchimedeanClass.mk σ < ArchimedeanClass.mk τ) ∨
      (∀ k : ℕ, k • ArchimedeanClass.mk τ < ArchimedeanClass.mk σ) := by
  by_cases h1 : ∃ k : ℕ, ArchimedeanClass.mk τ ≤ k • ArchimedeanClass.mk σ
  · by_cases h2 : ∃ k : ℕ, ArchimedeanClass.mk σ ≤ k • ArchimedeanClass.mk τ
    · obtain ⟨k₀, hk₀⟩ := h1
      obtain ⟨k₁, hk₁⟩ := h2
      exact Or.inl ⟨max k₀ k₁, hk₁.trans (nsmul_le_nsmul_left hτ.le (le_max_right _ _)),
        hk₀.trans (nsmul_le_nsmul_left hσ.le (le_max_left _ _))⟩
    · push Not at h2
      exact Or.inr (Or.inr h2)
  · push Not at h1
    exact Or.inr (Or.inl h1)

/-- The comparable-class functional equation, restated with `ClassComparable`. -/
theorem expInf_add_eq_mul_of_classComparable {σ τ : Surreal.{u}}
    (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) (hσ0 : 0 < σ) (hτ0 : 0 < τ)
    (h : ClassComparable σ τ) :
    expInf (σ + τ) (hσ.add hτ) (by positivity) =
      expInf σ hσ hσ0.ne' * expInf τ hτ hτ0.ne' :=
  let ⟨K, h1, h2⟩ := h
  expInf_add_eq_mul_of_comparable hσ hτ hσ0 hτ0 K h1 h2

/-! ### The dichotomy -/

/-- **THE MULTIPLICATIVITY DICHOTOMY**: for positive infinitesimals `σ, τ`, the canonical
exponential satisfies `expInf (σ + τ) = expInf σ * expInf τ` **if and only if** the
Archimedean classes of `σ` and `τ` are comparable. The functional equation holds exactly
when the canonical sum can see both of its arguments.

`⟸` is `expInf_add_eq_mul_of_comparable` (`Infinity.GameCofinality`). `⟹`: by the class
trichotomy, if the classes are not comparable then one argument is strictly finer than every
power of the other, and the failure theorem (applied with the roles swapped if necessary)
contradicts the functional equation. -/
theorem expInf_add_eq_mul_iff_classComparable {σ τ : Surreal.{u}}
    (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) (hσ0 : 0 < σ) (hτ0 : 0 < τ) :
    expInf (σ + τ) (hσ.add hτ) (by positivity) =
        expInf σ hσ hσ0.ne' * expInf τ hτ hτ0.ne' ↔
      ClassComparable σ τ := by
  constructor
  · intro h
    rcases classComparable_or_forall_nsmul_lt hσ hτ with hc | hf | hf
    · exact hc
    · exact absurd h (expInf_add_ne_mul_of_forall_nsmul_lt hσ hτ hσ0 hτ0 hf)
    · have h' := (expInf_congr (add_comm τ σ) (hτ.add hσ) (by positivity) (hσ.add hτ)
        (by positivity)).trans (h.trans (mul_comm _ _))
      exact absurd h' (expInf_add_ne_mul_of_forall_nsmul_lt hτ hσ hτ0 hσ0 hf)
  · exact expInf_add_eq_mul_of_classComparable hσ hτ hσ0 hτ0

/-! ### Consequences: iterates, roots, non-injectivity -/

theorem Infinitesimal.nsmul {σ : Surreal.{u}} (hσ : Infinitesimal σ) (n : ℕ) :
    Infinitesimal (n • σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul]
    exact ih.add hσ

private theorem mk_natCast_succ (n : ℕ) :
    ArchimedeanClass.mk (((n + 1 : ℕ)) : Surreal.{u}) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [ArchimedeanClass.stdPart_natCast]
  exact_mod_cast n.succ_ne_zero

/-- A positive natural multiple does not change the Archimedean class. -/
theorem mk_succ_nsmul (σ : Surreal.{u}) (n : ℕ) :
    ArchimedeanClass.mk ((n + 1) • σ) = ArchimedeanClass.mk σ := by
  rw [nsmul_eq_mul, ArchimedeanClass.mk_mul, mk_natCast_succ, zero_add]

/-- **The iterate law**: `expInf ((n+1) • σ) = expInf σ ^ (n+1)`, by induction from the
equal-class functional equation (`mk ((n+1) • σ) = mk σ`). -/
theorem expInf_succ_nsmul {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : 0 < σ) (n : ℕ) :
    expInf ((n + 1) • σ) (hσ.nsmul (n + 1)) (by positivity) =
      expInf σ hσ hσ0.ne' ^ (n + 1) := by
  induction n with
  | zero =>
    rw [pow_one]
    exact expInf_congr (by simp) _ _ _ _
  | succ n ih =>
    rw [pow_succ, ← ih]
    have hσ' : Infinitesimal ((n + 1) • σ) := hσ.nsmul (n + 1)
    have hσ0' : 0 < (n + 1) • σ := by positivity
    refine (expInf_congr (succ_nsmul σ (n + 1)) _ _ (hσ'.add hσ) (by positivity)).trans ?_
    exact expInf_add_eq_mul_of_mk_eq hσ' hσ hσ0' hσ0 (mk_succ_nsmul σ n)

theorem Infinitesimal.div_natCast_succ {σ : Surreal.{u}} (hσ : Infinitesimal σ) (n : ℕ) :
    Infinitesimal (σ / ((n + 1 : ℕ) : Surreal)) := by
  rw [div_eq_mul_inv]
  refine hσ.mul_isFinite ?_
  rw [IsFinite, ArchimedeanClass.mk_inv, mk_natCast_succ, neg_zero]

/-- **The root law**: `expInf σ = expInf (σ / (n+1)) ^ (n+1)` — every canonical exponential
value has canonical `(n+1)`-st roots. -/
theorem expInf_eq_pow_expInf_div {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : 0 < σ)
    (n : ℕ) :
    expInf σ hσ hσ0.ne' =
      expInf (σ / ((n + 1 : ℕ) : Surreal)) (hσ.div_natCast_succ n) (by positivity) ^
        (n + 1) := by
  have hd : Infinitesimal (σ / ((n + 1 : ℕ) : Surreal)) := hσ.div_natCast_succ n
  have hd0 : 0 < σ / ((n + 1 : ℕ) : Surreal) := by positivity
  rw [← expInf_succ_nsmul hd hd0 n]
  refine expInf_congr ?_ _ _ _ _
  rw [nsmul_eq_mul, mul_div_cancel₀]
  positivity

theorem Infinitesimal.half {σ : Surreal.{u}} (hσ : Infinitesimal σ) :
    Infinitesimal (σ / 2) := by
  have h := hσ.div_natCast_succ 1
  rwa [show ((1 + 1 : ℕ) : Surreal) = 2 by norm_num] at h

/-- **The half-log fibre, settled**: `expInf σ = expInf (σ / 2) ^ 2`. -/
theorem expInf_eq_sq_expInf_half {σ : Surreal.{u}} (hσ : Infinitesimal σ) (hσ0 : 0 < σ) :
    expInf σ hσ hσ0.ne' = expInf (σ / 2) hσ.half (by positivity) ^ 2 := by
  rw [expInf_eq_pow_expInf_div hσ hσ0 1]
  have h : σ / ((1 + 1 : ℕ) : Surreal) = σ / 2 := by norm_num
  rw [expInf_congr h _ _ hσ.half (by positivity)]

/-- **Non-injectivity**: when `τ ≠ 0` is strictly finer than every power of `σ`, the
arguments `σ + τ` and `σ` differ but their canonical exponentials agree. -/
theorem expInf_not_injective_of_forall_nsmul_lt {σ τ : Surreal.{u}}
    (hσ : Infinitesimal σ) (hτ : Infinitesimal τ) (hσ0 : σ ≠ 0) (hτ0 : τ ≠ 0)
    (hfine : ∀ k : ℕ, k • ArchimedeanClass.mk σ < ArchimedeanClass.mk τ) :
    σ + τ ≠ σ ∧
      expInf (σ + τ) (hσ.add hτ) (add_ne_zero_of_forall_nsmul_lt hσ0 hfine) =
        expInf σ hσ hσ0 :=
  ⟨fun h ↦ hτ0 (add_eq_left.1 h), expInf_add_eq_of_forall_nsmul_lt hσ hτ hσ0 _ hfine⟩

/-! ### A concrete witness: `ω⁻¹` and `ω^(−ω)` -/

/-- `ω^(−k) = (ω⁻¹)^k`. -/
theorem wpow_neg_natCast_eq_pow (k : ℕ) :
    ω^ (-(k : Surreal.{u})) = (ω^ (-1 : Surreal)) ^ k := by
  induction k with
  | zero => simp [wpow_zero]
  | succ k ih => rw [Nat.cast_succ, neg_add, wpow_add, ih, pow_succ]

theorem infinitesimal_wpow_neg_omega : Infinitesimal (ω^ (-(ω^ (1 : Surreal.{u})))) := by
  rw [Infinitesimal, ← ArchimedeanClass.mk_one, ← wpow_zero]
  apply archimedeanClassMk_wpow_strictAnti
  simp [wpow_pos]

/-- `ω^(−ω)` is strictly finer than every power of `ω⁻¹`: `k • mk ω⁻¹ = mk (ω^(−k))` and
`k < ω`. -/
theorem forall_nsmul_mk_wpow_neg_one_lt (k : ℕ) :
    k • ArchimedeanClass.mk (ω^ (-1 : Surreal.{u})) <
      ArchimedeanClass.mk (ω^ (-(ω^ (1 : Surreal)))) := by
  rw [← ArchimedeanClass.mk_pow, ← wpow_neg_natCast_eq_pow]
  apply archimedeanClassMk_wpow_strictAnti
  rw [neg_lt_neg_iff]
  exact natCast_lt_wpow_one k

/-- **Blindness, concretely**: `expInf (ω⁻¹ + ω^(−ω)) = expInf ω⁻¹`. -/
theorem expInf_wpow_neg_one_add_wpow_neg_omega :
    expInf (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal))))
        (infinitesimal_wpow_neg_one.add infinitesimal_wpow_neg_omega)
        (add_pos (wpow_pos _) (wpow_pos _)).ne' =
      expInf (ω^ (-1 : Surreal)) infinitesimal_wpow_neg_one (wpow_pos _).ne' :=
  expInf_add_eq_of_forall_nsmul_lt_of_pos infinitesimal_wpow_neg_one
    infinitesimal_wpow_neg_omega (wpow_pos _) (wpow_pos _) forall_nsmul_mk_wpow_neg_one_lt

/-- **The functional equation fails, concretely**:
`expInf (ω⁻¹ + ω^(−ω)) ≠ expInf ω⁻¹ * expInf ω^(−ω)`. -/
theorem expInf_wpow_neg_one_add_wpow_neg_omega_ne_mul :
    expInf (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal))))
        (infinitesimal_wpow_neg_one.add infinitesimal_wpow_neg_omega)
        (add_pos (wpow_pos _) (wpow_pos _)).ne' ≠
      expInf (ω^ (-1 : Surreal)) infinitesimal_wpow_neg_one (wpow_pos _).ne' *
        expInf (ω^ (-(ω^ (1 : Surreal)))) infinitesimal_wpow_neg_omega (wpow_pos _).ne' :=
  expInf_add_ne_mul_of_forall_nsmul_lt infinitesimal_wpow_neg_one
    infinitesimal_wpow_neg_omega (wpow_pos _) (wpow_pos _) forall_nsmul_mk_wpow_neg_one_lt

end Surreal
