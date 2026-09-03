import Infinity.FaithfulExp
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Log

/-!
# The jet calculus: every power series is a differentiable function on the halo of every point

`FaithfulExp.lean` built the faithful evaluation `fevalHS ε f` of a power series at an
infinitesimal through Conway's isomorphism `No ≅ ℝ((ω^No))` and proved `exp′ = exp` — at the
*base point* of each jet (`hasDerivS_fevalHS_zero`) and, for the exponential only, at every
infinitesimal via the functional equation. This file is the general calculus behind that one
function: **every power series `T` defines a differentiable function on the halo of every point,
with the formal derivative as its derivative**, together with the Taylor shift law that drives it,
higher derivatives, the composition law for `heval` and the chain rule, and the faithful logarithm
as the inverse of the faithful exponential.

Write `K := HahnSeries Γ ℝ` (mathlib's Hahn series; the repo's `toHahn` lands in
`HahnSeries Surrealᵒᵈ ℝ`) and `ev_a f := heval a f` for `a` of positive order.

## The summable-family engine

* `SummableFamily.compInj` — precomposition with an injective reindexing;
* `SummableFamily.sumFst` / **`hsum_sumFst`** — fibrewise summation of a family indexed by
  `α × β` (Fubini for Hahn sums, from `finsum_curry`);
* **`hsum_eq_add_hsum_compInj_succ`** — the peel-off lemma `Σ_n s n = s 0 + Σ_n s (n+1)`;
* `zero_le_orderTop_hsum`, `small_support_hsum`, `small_support_mul`.

## THE TAYLOR SHIFT LAW (`heval_add_eq_hsum_taylor`)

`taylorCoeff f j := D^j f / j!` (`coeff_taylorCoeff : coeff i (D^j f/j!) = C(i+j,j) f_{i+j}`),
`taylorDouble a b f k` is the double family `(j, i) ↦ coeff i (T_{j+k} f) · bʲ aⁱ`
(`smulFamily` of `mul (powers b) (powers a)` — summable for free), and
**`taylorFamily a b f k := sumFst (taylorDouble a b f k)`** is the summable family
`j ↦ bʲ · ev_a (D^{j+k} f/(j+k)!)` (`taylorFamily_apply`). Then for `a, b` of positive order
* **`heval_add_eq_hsum_taylor : heval (a + b) f = (taylorFamily a b f 0).hsum`** — the binomial
  expansion of `Σ_n f_n (a+b)^n` regrouped along the antidiagonals
  (`hsum_eq_hsum_of_antidiagonal`) and summed fibrewise;
* `hsum_taylorFamily_succ` (the recursion in `k`) and
  **`heval_add_eq_two_term : heval (a+b) f = heval a f + b · heval a f′ + b² · R`** with
  `R = (taylorFamily a b f 2).hsum`, `0 ≤ R.orderTop` and **`coeff_zero_hsum_taylorFamily_two :
  R.coeff 0 = f₂`**.

## THE JET CALCULUS ON SURREALS

* `taylorRemS ε δ T` (the remainder as a surreal Hahn series),
  **`fevalHS_add_eq : fevalHS (ε + δ) T = fevalHS ε T + fevalHS ε T′ · δ + δ² · evalHahn (taylorRemS ε δ T)`**
  and the uniform bound **`abs_evalHahn_taylorRemS_le : |evalHahn (taylorRemS ε δ T)| ≤ |T₂| + 1`**
  (a Hahn series of nonnegative order with coefficient `c` at `0` evaluates to within an
  infinitesimal of `c`: `infinitesimal_evalHahn_of_support_neg`, `infinitesimal_evalHahn_ofHahn_sub`);
  `toHahn_hevalS_add` is the full Taylor expansion on surreals.
* **The jet function** `jet T c x := fevalHS (x − c) T` and
  **`hasDerivS_jet : HasDerivS (jet T c) (c + ε) (fevalHS ε T′)`** at every infinitesimal `ε`,
  with constant `|T₂| + 1`; **`hasDerivS_jet' : HasDerivS (jet T c) x (jet T′ c x)`** at every
  `x` in the halo of `c`; **`hasDerivS_jet_iterate`** for all higher derivatives;
  `hasDerivS_jet_zero` (the base point, recovering `hasDerivS_fevalHS_zero`),
  `jet_exp_zero`/`hasDerivS_jet_exp` (`hasDerivS_expH` as the instance `T = exp`),
  `jet_coe` (polynomials).

## COMPOSITION AND THE CHAIN RULE

* **`heval_subst : heval a (f.subst g) = heval (heval a g) f`** for `g` without constant term
  (`orderTop_heval_pos`): coefficientwise both sides are the finite double sum
  `Σ_{d,n} f_d · coeff n (g^d) · coeff γ (aⁿ)` (`coeff_heval_eq`, `coeff_subst'`, `finsum_curry`);
* **`fevalHS_subst : fevalHS ε (f.subst g) = fevalHS (fevalHS ε g) f`**, `jet_subst`,
  **`hasDerivS_jet_subst`** (`(f ∘ g)′ = (f′ ∘ g) · g′` via mathlib's `derivative_subst`) and
  the classical form **`hasDerivS_jet_comp`** for `x ↦ J f 0 (J g c x)` (`HasDerivS.congr_of_halo`).

## THE FAITHFUL LOGARITHM

* The power-series identities **`exp_subst_log : exp.subst log = 1 + X`** (from
  `F′ = F · log′`, `(F · log′)′ = 0`, `derivative.ext`) and
  **`log_subst_exp_sub_one : log.subst (exp − 1) = X`** (uniqueness of substitution inverses,
  `substInvOfIsUnit`); `one_add_X_mul_derivative_log : (1 + X) · log′ = 1`.
* **`logH1p ε := fevalHS ε (log ℝ)`** (`log (1 + ε)`), infinitesimal at infinitesimals;
  **`expH_logH1p : expH (logH1p ε) = 1 + ε`**, **`logH1p_expH_sub_one : logH1p (expH ε − 1) = ε`**,
  `logH1p_inj`, **`logH1p_mul : logH1p ((1+ε)(1+δ) − 1) = logH1p ε + logH1p δ`**, monotonicity,
  `fevalHS_derivative_log : fevalHS ε log′ = (1 + ε)⁻¹`, and
  **`hasDerivS_logH1p : HasDerivS (fun x ↦ logH1p (x − 1)) (1 + ε) ((1 + ε)⁻¹)`**
  (`hasDerivS_logH1p'` at every point of the halo of `1`).
* **The contrast** `expH_logH1p_and_not_expInf_log`: at `x = ω⁻¹ + ω^(−ω)` the faithful pair is
  an honest inverse pair while the canonical `expInf` of every canonical log value misses `1 + x`.
-/

open ArchimedeanClass Finset

universe u

noncomputable section

/-! ### Summable families: reindexing, fibrewise summation, and the peel-off lemma -/

namespace HahnSeries.SummableFamily

variable {Γ R α β : Type*} [PartialOrder Γ] [AddCommMonoid R]

/-- Precomposition of a summable family with an injective reindexing. -/
def compInj (s : SummableFamily Γ R β) (φ : α → β) (hφ : Function.Injective φ) :
    SummableFamily Γ R α where
  toFun a := s (φ a)
  isPWO_iUnion_support' := s.isPWO_iUnion_support.mono
    (Set.iUnion_subset fun a ↦ Set.subset_iUnion (fun b ↦ (s b).support) (φ a))
  finite_co_support' g := (s.finite_co_support' g).preimage hφ.injOn

@[simp]
theorem compInj_apply (s : SummableFamily Γ R β) (φ : α → β) (hφ : Function.Injective φ)
    (a : α) : s.compInj φ hφ a = s (φ a) :=
  rfl

/-- **Fibrewise summation**: summing a family indexed by `α × β` over the second coordinate gives
a summable family indexed by `α`. -/
def sumFst (u : SummableFamily Γ R (α × β)) : SummableFamily Γ R α where
  toFun a := (u.compInj (fun b ↦ (a, b)) fun _ _ h ↦ (Prod.mk.inj h).2).hsum
  isPWO_iUnion_support' := u.isPWO_iUnion_support.mono (Set.iUnion_subset fun a ↦
    support_hsum_subset.trans
      (Set.iUnion_subset fun b ↦ Set.subset_iUnion (fun p ↦ (u p).support) (a, b)))
  finite_co_support' g := by
    refine ((u.finite_co_support' g).image Prod.fst).subset fun a ha ↦ ?_
    have ha' : ∑ᶠ b, (u (a, b)).coeff g ≠ 0 := ha
    obtain ⟨b, hb⟩ : ∃ b, (u (a, b)).coeff g ≠ 0 := by
      by_contra h
      exact ha' (finsum_eq_zero_of_forall_eq_zero fun b ↦ not_not.1 fun h' ↦ h ⟨b, h'⟩)
    exact ⟨(a, b), hb, rfl⟩

theorem sumFst_apply (u : SummableFamily Γ R (α × β)) (a : α) :
    sumFst u a = (u.compInj (fun b ↦ (a, b)) fun _ _ h ↦ (Prod.mk.inj h).2).hsum :=
  rfl

/-- **Fubini for Hahn sums**: summing fibrewise gives the same Hahn sum. -/
theorem hsum_sumFst (u : SummableFamily Γ R (α × β)) : (sumFst u).hsum = u.hsum := by
  ext g
  rw [coeff_hsum, coeff_hsum, finsum_curry (fun p ↦ (u p).coeff g) (u.finite_co_support g)]
  rfl

/-- A finitely supported sum over `ℕ` peels off its first term. -/
theorem _root_.finsum_nat_eq_zero_add (F : ℕ → R) (hF : (Function.support F).Finite) :
    ∑ᶠ n, F n = F 0 + ∑ᶠ n, F (n + 1) := by
  obtain ⟨N, hN⟩ := hF.bddAbove
  rw [finsum_eq_sum_of_support_subset F (s := Finset.range (N + 1)) (fun n hn ↦
      Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le (hN hn)))),
    finsum_eq_sum_of_support_subset (fun n ↦ F (n + 1)) (s := Finset.range N) (fun n hn ↦
      Finset.mem_coe.2 (Finset.mem_range.2
        (Nat.lt_of_succ_le (hN (show n + 1 ∈ Function.support F from hn))))),
    Finset.sum_range_succ', add_comm]

/-- **The peel-off lemma**: a Hahn sum over `ℕ` is its first term plus the Hahn sum of the
shifted family. -/
theorem hsum_eq_add_hsum_compInj_succ (s : SummableFamily Γ R ℕ) :
    s.hsum = s 0 + (s.compInj Nat.succ Nat.succ_injective).hsum := by
  ext g
  rw [coeff_add, coeff_hsum, coeff_hsum, finsum_nat_eq_zero_add _ (s.finite_co_support g)]
  rfl

/-- A Hahn sum of series of nonnegative order has nonnegative order. -/
theorem zero_le_orderTop_hsum {Γ : Type*} [Zero Γ] [LinearOrder Γ] {s : SummableFamily Γ R α}
    (h : ∀ i, 0 ≤ (s i).orderTop) : 0 ≤ s.hsum.orderTop := by
  rw [le_orderTop_iff_forall]
  intro j hj
  rw [coeff_hsum]
  exact finsum_eq_zero_of_forall_eq_zero fun i ↦
    coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le hj (h i))

end HahnSeries.SummableFamily

/-! ### Smallness of supports -/

namespace SurrealHahnSeries

open HahnSeries

theorem small_support_mul {a b : HahnSeries Surreal.{u}ᵒᵈ ℝ} (ha : Small.{u} a.support)
    (hb : Small.{u} b.support) : Small.{u} (a * b).support := by
  haveI := ha
  haveI := hb
  have h2 : Small.{u} ↥(Set.image2 (· + ·) a.support b.support) := inferInstance
  rw [Set.image2_add] at h2
  exact small_subset support_mul_subset

theorem small_support_smul (r : ℝ) {a : HahnSeries Surreal.{u}ᵒᵈ ℝ} (ha : Small.{u} a.support) :
    Small.{u} (r • a).support := by
  haveI := ha
  exact small_subset (support_smul_subset r a)

theorem small_support_hsum {α : Type*} [Small.{u} α] {s : SummableFamily Surreal.{u}ᵒᵈ ℝ α}
    (h : ∀ i, Small.{u} (s i).support) : Small.{u} s.hsum.support := by
  haveI := h
  exact small_subset SummableFamily.support_hsum_subset

theorem toHahn_pow (x : SurrealHahnSeries.{u}) (n : ℕ) : toHahn (x ^ n) = toHahn x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, toHahn_one]
  | succ n ih => rw [pow_succ, pow_succ, toHahn_mul, ih]

end SurrealHahnSeries

/-! ### The Taylor coefficient series `D^j f / j!` -/

namespace Surreal

open SurrealHahnSeries OrderDual HahnSeries

/-- The `j`-th Taylor coefficient series `D^j f / j!` of a power series. -/
def taylorCoeff (f : PowerSeries ℝ) (j : ℕ) : PowerSeries ℝ :=
  ((j.factorial : ℝ)⁻¹) • (PowerSeries.derivative ℝ)^[j] f

/-- `coeff i (D^j f / j!) = C(i+j, j) · f_{i+j}`. -/
theorem coeff_taylorCoeff (f : PowerSeries ℝ) (i j : ℕ) :
    PowerSeries.coeff i (taylorCoeff f j) =
      ((i + j).choose j : ℝ) * PowerSeries.coeff (i + j) f := by
  rw [taylorCoeff, PowerSeries.coeff_smul, PowerSeries.coeff_iterate_derivative,
    Nat.ascFactorial_eq_factorial_mul_choose, smul_eq_mul, Nat.cast_mul, ← mul_assoc,
    ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 j.factorial_ne_zero), one_mul]

theorem taylorCoeff_zero (f : PowerSeries ℝ) : taylorCoeff f 0 = f := by
  rw [taylorCoeff, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    Function.iterate_zero_apply]

theorem taylorCoeff_one (f : PowerSeries ℝ) : taylorCoeff f 1 = PowerSeries.derivative ℝ f := by
  rw [taylorCoeff, Nat.factorial_one, Nat.cast_one, inv_one, one_smul, Function.iterate_one]

theorem constantCoeff_taylorCoeff (f : PowerSeries ℝ) (j : ℕ) :
    PowerSeries.constantCoeff (taylorCoeff f j) = PowerSeries.coeff j f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_taylorCoeff, zero_add,
    Nat.choose_self, Nat.cast_one, one_mul]

/-! ### The Taylor family and the Taylor shift law -/

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- The double family `(j, i) ↦ coeff i (D^{j+k} f / (j+k)!) · bʲ aⁱ`. -/
def taylorDouble (a b : HahnSeries Γ ℝ) (f : PowerSeries ℝ) (k : ℕ) :
    SummableFamily Γ ℝ (ℕ × ℕ) :=
  SummableFamily.smulFamily (fun p ↦ PowerSeries.coeff p.2 (taylorCoeff f (p.1 + k)))
    (SummableFamily.mul (SummableFamily.powers b) (SummableFamily.powers a))

theorem taylorDouble_apply {a b : HahnSeries Γ ℝ} (ha : 0 < a.orderTop) (hb : 0 < b.orderTop)
    (f : PowerSeries ℝ) (k : ℕ) (p : ℕ × ℕ) :
    taylorDouble a b f k p =
      PowerSeries.coeff p.2 (taylorCoeff f (p.1 + k)) • (b ^ p.1 * a ^ p.2) := by
  rw [taylorDouble, SummableFamily.smulFamily_toFun, SummableFamily.mul_toFun,
    SummableFamily.powers_of_orderTop_pos hb, SummableFamily.powers_of_orderTop_pos ha]

/-- **The Taylor family** `j ↦ bʲ · ev_a (D^{j+k} f / (j+k)!)`, as a summable family (the
fibrewise sum of the double family). -/
def taylorFamily (a b : HahnSeries Γ ℝ) (f : PowerSeries ℝ) (k : ℕ) : SummableFamily Γ ℝ ℕ :=
  SummableFamily.sumFst (taylorDouble a b f k)

theorem taylorFamily_apply {a b : HahnSeries Γ ℝ} (ha : 0 < a.orderTop) (hb : 0 < b.orderTop)
    (f : PowerSeries ℝ) (k j : ℕ) :
    taylorFamily a b f k j = b ^ j * PowerSeries.heval a (taylorCoeff f (j + k)) := by
  rw [taylorFamily, SummableFamily.sumFst_apply, PowerSeries.heval_apply,
    ← SummableFamily.hsum_smul]
  congr 1
  refine SummableFamily.ext fun i ↦ ?_
  show taylorDouble a b f k (j, i) =
    b ^ j * SummableFamily.powerSeriesFamily a (taylorCoeff f (j + k)) i
  rw [taylorDouble_apply ha hb, SummableFamily.powerSeriesFamily_of_orderTop_pos ha]
  exact (Algebra.mul_smul_comm _ _ _).symm

/-- The recursion `Σ_j bʲ T_{j+k} = T_k + b · Σ_j bʲ T_{j+k+1}`. -/
theorem hsum_taylorFamily_succ {a b : HahnSeries Γ ℝ} (ha : 0 < a.orderTop)
    (hb : 0 < b.orderTop) (f : PowerSeries ℝ) (k : ℕ) :
    (taylorFamily a b f k).hsum =
      PowerSeries.heval a (taylorCoeff f k) + b * (taylorFamily a b f (k + 1)).hsum := by
  rw [SummableFamily.hsum_eq_add_hsum_compInj_succ (taylorFamily a b f k),
    taylorFamily_apply ha hb, pow_zero, one_mul, zero_add, ← SummableFamily.hsum_smul]
  congr 2
  refine SummableFamily.ext fun j ↦ ?_
  show taylorFamily a b f k (j + 1) = b * taylorFamily a b f (k + 1) j
  rw [taylorFamily_apply ha hb, taylorFamily_apply ha hb, show j + 1 + k = j + (k + 1) by omega]
  ring

/-- **THE TAYLOR SHIFT LAW IN THE HAHN-SERIES FIELD**: for Hahn series `a, b` of positive order,
`heval (a + b) f = Σ_j heval a (D^j f / j!) · bʲ` — the binomial expansion of `Σ_n f_n (a+b)^n`
regrouped along the antidiagonals and summed fibrewise. -/
theorem heval_add_eq_hsum_taylor {a b : HahnSeries Γ ℝ} (ha : 0 < a.orderTop)
    (hb : 0 < b.orderTop) (f : PowerSeries ℝ) :
    PowerSeries.heval (a + b) f = (taylorFamily a b f 0).hsum := by
  have hab : 0 < (a + b).orderTop :=
    lt_of_lt_of_le (lt_min ha hb) HahnSeries.min_orderTop_le_orderTop_add
  rw [PowerSeries.heval_apply, taylorFamily, SummableFamily.hsum_sumFst]
  apply SummableFamily.hsum_eq_hsum_of_antidiagonal
  intro n
  rw [SummableFamily.powerSeriesFamily_of_orderTop_pos hab, add_comm a b, add_pow,
    Finset.smul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [taylorDouble_apply ha hb, add_zero, coeff_taylorCoeff, Nat.sub_add_cancel hk',
    ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_comm (PowerSeries.coeff n f)]

/-- **The two-term Taylor law**: `heval (a + b) f = heval a f + b · heval a f′ + b² · R` with
`R = Σ_j bʲ · heval a (D^{j+2} f / (j+2)!)`. -/
theorem heval_add_eq_two_term {a b : HahnSeries Γ ℝ} (ha : 0 < a.orderTop)
    (hb : 0 < b.orderTop) (f : PowerSeries ℝ) :
    PowerSeries.heval (a + b) f =
      PowerSeries.heval a f + b * PowerSeries.heval a (PowerSeries.derivative ℝ f) +
        b ^ 2 * (taylorFamily a b f 2).hsum := by
  rw [heval_add_eq_hsum_taylor ha hb, hsum_taylorFamily_succ ha hb, zero_add,
    hsum_taylorFamily_succ ha hb, taylorCoeff_zero, taylorCoeff_one,
    show (1 + 1 : ℕ) = 2 from rfl]
  ring

/-! ### Order and coefficient facts about the Taylor remainder -/

theorem zero_le_orderTop_pow {a : HahnSeries Γ ℝ} (ha : 0 < a.orderTop) (n : ℕ) :
    0 ≤ (a ^ n).orderTop :=
  le_trans (nsmul_nonneg ha.le n) HahnSeries.orderTop_nsmul_le_orderTop_pow

theorem zero_lt_orderTop_pow {a : HahnSeries Γ ℝ} (ha : 0 < a.orderTop) {n : ℕ} (hn : n ≠ 0) :
    0 < (a ^ n).orderTop :=
  lt_of_lt_of_le ((nsmul_pos_iff hn).2 ha) HahnSeries.orderTop_nsmul_le_orderTop_pow

omit [IsOrderedCancelAddMonoid Γ] in
theorem zero_le_orderTop_smul (r : ℝ) {x : HahnSeries Γ ℝ} (hx : 0 ≤ x.orderTop) :
    0 ≤ (r • x).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall] at hx ⊢
  intro j hj
  rw [HahnSeries.coeff_smul, hx j hj, smul_zero]

/-- Every exponent of `heval a f` is nonnegative. -/
theorem zero_le_orderTop_heval {a : HahnSeries Γ ℝ} (ha : 0 < a.orderTop) (f : PowerSeries ℝ) :
    0 ≤ (PowerSeries.heval a f).orderTop := by
  rw [PowerSeries.heval_apply]
  refine SummableFamily.zero_le_orderTop_hsum fun n ↦ ?_
  rw [SummableFamily.powerSeriesFamily_of_orderTop_pos ha]
  exact zero_le_orderTop_smul _ (zero_le_orderTop_pow ha n)

theorem zero_le_orderTop_taylorFamily {a b : HahnSeries Γ ℝ} (ha : 0 < a.orderTop)
    (hb : 0 < b.orderTop) (f : PowerSeries ℝ) (k j : ℕ) :
    0 ≤ (taylorFamily a b f k j).orderTop := by
  rw [taylorFamily_apply ha hb, HahnSeries.orderTop_mul]
  exact add_nonneg (zero_le_orderTop_pow hb j) (zero_le_orderTop_heval ha _)

theorem zero_le_orderTop_hsum_taylorFamily {a b : HahnSeries Γ ℝ} (ha : 0 < a.orderTop)
    (hb : 0 < b.orderTop) (f : PowerSeries ℝ) (k : ℕ) :
    0 ≤ (taylorFamily a b f k).hsum.orderTop :=
  SummableFamily.zero_le_orderTop_hsum fun j ↦ zero_le_orderTop_taylorFamily ha hb f k j

/-- **The coefficient at exponent `0` of the Taylor remainder** `Σ_j bʲ heval a (D^{j+2}f/(j+2)!)`
is `f₂`: only `j = 0` contributes, and its constant term is `constantCoeff (D²f/2) = f₂`. -/
theorem coeff_zero_hsum_taylorFamily_two {a b : HahnSeries Γ ℝ} (ha : 0 < a.orderTop)
    (hb : 0 < b.orderTop) (f : PowerSeries ℝ) :
    (taylorFamily a b f 2).hsum.coeff 0 = PowerSeries.coeff 2 f := by
  rw [SummableFamily.coeff_hsum, finsum_eq_single _ 0]
  · rw [taylorFamily_apply ha hb, pow_zero, one_mul, PowerSeries.coeff_heval_zero, zero_add,
      constantCoeff_taylorCoeff]
  · intro j hj
    rw [taylorFamily_apply ha hb]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [HahnSeries.orderTop_mul, WithTop.coe_zero]
    exact add_pos_of_pos_of_nonneg (zero_lt_orderTop_pow hb hj) (zero_le_orderTop_heval ha _)

/-! ### Smallness of the Taylor family -/

theorem small_support_taylorDouble {a b : HahnSeries Surreal.{u}ᵒᵈ ℝ} (ha : Small.{u} a.support)
    (hb : Small.{u} b.support) (f : PowerSeries ℝ) (k : ℕ) (p : ℕ × ℕ) :
    Small.{u} (taylorDouble a b f k p).support := by
  rw [taylorDouble, SummableFamily.smulFamily_toFun, SummableFamily.mul_toFun]
  exact small_support_smul _
    (small_support_mul (small_support_powers hb _) (small_support_powers ha _))

theorem small_support_taylorFamily {a b : HahnSeries Surreal.{u}ᵒᵈ ℝ} (ha : Small.{u} a.support)
    (hb : Small.{u} b.support) (f : PowerSeries ℝ) (k j : ℕ) :
    Small.{u} (taylorFamily a b f k j).support := by
  rw [taylorFamily, SummableFamily.sumFst_apply]
  exact small_support_hsum fun i ↦ small_support_taylorDouble ha hb f k _

theorem small_support_hsum_taylorFamily {a b : HahnSeries Surreal.{u}ᵒᵈ ℝ}
    (ha : Small.{u} a.support) (hb : Small.{u} b.support) (f : PowerSeries ℝ) (k : ℕ) :
    Small.{u} (taylorFamily a b f k).hsum.support :=
  small_support_hsum fun j ↦ small_support_taylorFamily ha hb f k j

/-- **The Taylor remainder** at `(ε, δ)`: the surreal Hahn series of
`Σ_j δʲ · ev_ε (D^{j+2} T / (j+2)!)`. -/
def taylorRemS (ε δ : Surreal.{u}) (T : PowerSeries ℝ) : SurrealHahnSeries.{u} :=
  ofHahn (taylorFamily (toHahn (toHahnSeries ε)) (toHahn (toHahnSeries δ)) T 2).hsum
    (small_support_hsum_taylorFamily inferInstance inferInstance T 2)

theorem toHahn_taylorRemS (ε δ : Surreal.{u}) (T : PowerSeries ℝ) :
    toHahn (taylorRemS ε δ T) =
      (taylorFamily (toHahn (toHahnSeries ε)) (toHahn (toHahnSeries δ)) T 2).hsum :=
  toHahn_ofHahn _ _

/-! ### Transport to surreals: the remainder is bounded by `|T₂| + 1` -/

/-- A surreal Hahn series all of whose exponents are negative evaluates to an infinitesimal (its
leading exponent `e < 0` gives `mk (ω^e) ≤ mk (evalHahn x)`). -/
theorem infinitesimal_evalHahn_of_support_neg {x : SurrealHahnSeries.{u}}
    (hx : ∀ s ∈ x.support, s < 0) : Infinitesimal (evalHahn x) := by
  rcases eq_or_ne x 0 with rfl | hne
  · rw [evalHahn_zero]
    exact infinitesimal_zero
  · have h0 : 0 < x.length := pos_iff_ne_zero.2 fun h ↦ hne (length_eq_zero.1 h)
    have he : (x.exp ⟨0, h0⟩).1 ∈ x.support := (x.exp ⟨0, h0⟩).2
    have hub : ∀ s ∈ x.support, s ≤ (x.exp ⟨0, h0⟩).1 := by
      intro s hs
      obtain ⟨j, hj⟩ := eq_exp_of_mem_support hs
      rw [← hj]
      exact Subtype.coe_le_coe.2 (exp_le_exp_iff.2 (Subtype.coe_le_coe.1 _root_.zero_le))
    rw [infinitesimal_def]
    exact lt_of_lt_of_le (infinitesimal_def.1 (infinitesimal_wpow_of_neg (hx _ he)))
      (mk_wpow_le_mk_evalHahn_of_support_le hub)

/-- A mathlib Hahn series of nonnegative order evaluates to within an infinitesimal of its
coefficient at exponent `0`. -/
theorem infinitesimal_evalHahn_ofHahn_sub {h : HahnSeries Surreal.{u}ᵒᵈ ℝ}
    (hs : Small.{u} h.support) (h0 : 0 ≤ h.orderTop) :
    Infinitesimal (evalHahn (ofHahn h hs) - ((h.coeff 0 : ℝ) : Surreal)) := by
  have hsingle : ((h.coeff 0 : ℝ) : Surreal.{u}) =
      evalHahn (SurrealHahnSeries.single 0 (h.coeff 0)) := by
    rw [evalHahn_single, wpow_zero, mul_one]
  rw [hsingle, ← evalHahn_sub]
  refine infinitesimal_evalHahn_of_support_neg fun s hs' ↦ ?_
  rw [mem_support_iff, coeff_sub_apply, coeff_ofHahn] at hs'
  rcases eq_or_ne s 0 with rfl | hne
  · exact absurd (by rw [coeff_single_self]; exact sub_self _) hs'
  · rw [coeff_single_of_ne hne.symm, sub_zero] at hs'
    have hle : (0 : WithTop Surreal.{u}ᵒᵈ) ≤ toDual s :=
      le_trans h0 (HahnSeries.orderTop_le_of_coeff_ne_zero hs')
    rw [← WithTop.coe_zero, WithTop.coe_le_coe] at hle
    exact lt_of_le_of_ne (OrderDual.ofDual_le_ofDual.2 hle) hne

theorem abs_evalHahn_ofHahn_le {h : HahnSeries Surreal.{u}ᵒᵈ ℝ} (hs : Small.{u} h.support)
    (h0 : 0 ≤ h.orderTop) :
    |evalHahn (ofHahn h hs)| ≤ |((h.coeff 0 : ℝ) : Surreal)| + 1 := by
  have h1 := infinitesimal_iff.1 (infinitesimal_evalHahn_ofHahn_sub hs h0) 1
  rw [one_nsmul] at h1
  have h2 := abs_sub_abs_le_abs_sub (evalHahn (ofHahn h hs)) ((h.coeff 0 : ℝ) : Surreal)
  linarith

/-- **The uniform remainder bound**: `|R| ≤ |T₂| + 1` for all infinitesimals `ε, δ`. -/
theorem abs_evalHahn_taylorRemS_le {ε δ : Surreal.{u}} (hε : Infinitesimal ε)
    (hδ : Infinitesimal δ) (T : PowerSeries ℝ) :
    |evalHahn (taylorRemS ε δ T)| ≤ |((PowerSeries.coeff 2 T : ℝ) : Surreal)| + 1 := by
  have ha := orderTop_pos_of_infinitesimal hε
  have hb := orderTop_pos_of_infinitesimal hδ
  have h := abs_evalHahn_ofHahn_le (small_support_hsum_taylorFamily inferInstance inferInstance T 2)
    (zero_le_orderTop_hsum_taylorFamily ha hb T 2)
  rw [coeff_zero_hsum_taylorFamily_two ha hb] at h
  exact h

/-- **THE TWO-TERM TAYLOR LAW ON SURREALS**: for infinitesimals `ε, δ` and every power series `T`,
`fevalHS (ε + δ) T = fevalHS ε T + fevalHS ε T′ · δ + δ² · evalHahn (taylorRemS ε δ T)`. -/
theorem fevalHS_add_eq {ε δ : Surreal.{u}} (hε : Infinitesimal ε) (hδ : Infinitesimal δ)
    (T : PowerSeries ℝ) :
    fevalHS (ε + δ) T = fevalHS ε T + fevalHS ε (PowerSeries.derivative ℝ T) * δ +
      δ ^ 2 * evalHahn (taylorRemS ε δ T) := by
  have ha := orderTop_pos_of_infinitesimal hε
  have hb := orderTop_pos_of_infinitesimal hδ
  have key : hevalS (ε + δ) T = hevalS ε T + hevalS ε (PowerSeries.derivative ℝ T) * toHahnSeries δ +
      toHahnSeries δ ^ 2 * taylorRemS ε δ T := by
    apply toHahn_injective
    rw [toHahn_add, toHahn_add, toHahn_mul, toHahn_mul, toHahn_pow, toHahn_hevalS, toHahn_hevalS,
      toHahn_hevalS, toHahn_taylorRemS, toHahnSeries_add, toHahn_add, heval_add_eq_two_term ha hb]
    ring
  rw [fevalHS, key, evalHahn_add', evalHahn_add', evalHahn_mul, evalHahn_mul, evalHahn_pow,
    evalHahn_toHahnSeries]
  rfl

/-- **The Taylor shift law on surreals** (the full expansion, in Hahn-series form):
`toHahn (hevalS (ε + δ) T) = Σ_j δʲ · heval ε (D^j T / j!)`. -/
theorem toHahn_hevalS_add {ε δ : Surreal.{u}} (hε : Infinitesimal ε) (hδ : Infinitesimal δ)
    (T : PowerSeries ℝ) :
    toHahn (hevalS (ε + δ) T) =
      (taylorFamily (toHahn (toHahnSeries ε)) (toHahn (toHahnSeries δ)) T 0).hsum := by
  rw [toHahn_hevalS, toHahnSeries_add, toHahn_add,
    heval_add_eq_hsum_taylor (orderTop_pos_of_infinitesimal hε) (orderTop_pos_of_infinitesimal hδ)]

/-! ### THE JET CALCULUS: every power series is differentiable on the halo of every point -/

/-- **The jet function** of `T` centred at `c`: `x ↦ fevalHS (x − c) T` (honest on the halo of
`c`; junk elsewhere). For real `c = r` this is the "power series `T` at `r`". -/
def jet (T : PowerSeries ℝ) (c x : Surreal.{u}) : Surreal.{u} :=
  fevalHS (x - c) T

theorem jet_apply (T : PowerSeries ℝ) (c x : Surreal.{u}) : jet T c x = fevalHS (x - c) T := rfl

/-- **DIFFERENTIABILITY EVERYWHERE ON THE HALO**: at every point `c + ε` of the halo of `c`, the
jet function `J T c` has surreal-point derivative `fevalHS ε T′`, with the uniform constant
`|T₂| + 1` (the same constant as at the base point). -/
theorem hasDerivS_jet (T : PowerSeries ℝ) (c : Surreal.{u}) {ε : Surreal.{u}}
    (hε : Infinitesimal ε) :
    HasDerivS (jet T c) (c + ε) (fevalHS ε (PowerSeries.derivative ℝ T)) := by
  refine ⟨|((PowerSeries.coeff 2 T : ℝ) : Surreal)| + 1, fun δ hδ ↦ ?_⟩
  have h := fevalHS_add_eq hε hδ T
  calc |jet T c (c + ε + δ) - jet T c (c + ε) - fevalHS ε (PowerSeries.derivative ℝ T) * δ|
      = |δ ^ 2 * evalHahn (taylorRemS ε δ T)| := by
        rw [jet_apply, jet_apply, show c + ε + δ - c = ε + δ by ring, add_sub_cancel_left, h]
        congr 1
        ring
    _ = δ ^ 2 * |evalHahn (taylorRemS ε δ T)| := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg δ)]
    _ ≤ δ ^ 2 * (|((PowerSeries.coeff 2 T : ℝ) : Surreal)| + 1) :=
        mul_le_mul_of_nonneg_left (abs_evalHahn_taylorRemS_le hε hδ T) (sq_nonneg δ)
    _ = (|((PowerSeries.coeff 2 T : ℝ) : Surreal)| + 1) * δ ^ 2 := mul_comm _ _

/-- **At every point `x` of the halo of `c`**: `J T c` has derivative `J T′ c x` at `x`. -/
theorem hasDerivS_jet' (T : PowerSeries ℝ) (c : Surreal.{u}) {x : Surreal.{u}}
    (hx : Infinitesimal (x - c)) :
    HasDerivS (jet T c) x (jet (PowerSeries.derivative ℝ T) c x) := by
  have h := hasDerivS_jet T c hx
  rwa [add_sub_cancel] at h

/-- **Higher derivatives**: the `j`-th derivative jet is differentiable on the halo with derivative
the `(j+1)`-st derivative jet. -/
theorem hasDerivS_jet_iterate (T : PowerSeries ℝ) (c : Surreal.{u}) (j : ℕ) {x : Surreal.{u}}
    (hx : Infinitesimal (x - c)) :
    HasDerivS (jet ((PowerSeries.derivative ℝ)^[j] T) c) x
      (jet ((PowerSeries.derivative ℝ)^[j + 1] T) c x) := by
  rw [Function.iterate_succ_apply']
  exact hasDerivS_jet' _ c hx

/-- The jet at a real point `r`, in the form `HasDerivS (J T r) (r + ε) (J T′ r (r + ε))`. -/
theorem hasDerivS_jet_realCast (T : PowerSeries ℝ) (r : ℝ) {ε : Surreal.{u}}
    (hε : Infinitesimal ε) :
    HasDerivS (jet T (r : Surreal)) ((r : Surreal) + ε)
      (jet (PowerSeries.derivative ℝ T) (r : Surreal) ((r : Surreal) + ε)) := by
  have h := hasDerivS_jet T (r : Surreal.{u}) hε
  rwa [jet_apply, add_sub_cancel_left]

/-- The base-point case `ε = 0` recovers `hasDerivS_fevalHS_zero` (`T₁` as the derivative). -/
theorem hasDerivS_jet_zero (T : PowerSeries ℝ) (c : Surreal.{u}) :
    HasDerivS (jet T c) c ((PowerSeries.coeff 1 T : ℝ) : Surreal) := by
  have h := hasDerivS_jet T c infinitesimal_zero
  rwa [add_zero, fevalHS_zero_left, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_derivative, zero_add, Nat.cast_zero, zero_add, mul_one] at h

/-- The jet of `exp` at `0` is the faithful exponential. -/
theorem jet_exp_zero : jet (PowerSeries.exp ℝ) 0 = expH.{u} :=
  funext fun x ↦ by rw [jet_apply, sub_zero, expH_def]

/-- `hasDerivS_expH` is the instance `T = exp`, `c = 0` of `hasDerivS_jet'` (not re-proved). -/
theorem hasDerivS_jet_exp {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    HasDerivS (jet (PowerSeries.exp ℝ) 0) ε (jet (PowerSeries.exp ℝ) 0 ε) := by
  have h := hasDerivS_jet' (PowerSeries.exp ℝ) 0 (by rwa [sub_zero])
  rwa [PowerSeries.derivative_exp] at h

/-- Polynomials: the jet is the polynomial evaluated at `x − c`. -/
theorem jet_coe (p : Polynomial ℝ) (c : Surreal.{u}) {x : Surreal.{u}}
    (hx : Infinitesimal (x - c)) : jet (p : PowerSeries ℝ) c x = p.eval₂ realHom (x - c) :=
  fevalHS_coe hx p

/-! ### Composition: `heval x (f.subst g) = heval (heval x g) f` and the chain rule -/

theorem coeff_heval_eq {a : HahnSeries Γ ℝ} (ha : 0 < a.orderTop) (f : PowerSeries ℝ) (g : Γ) :
    (PowerSeries.heval a f).coeff g = ∑ᶠ n, PowerSeries.coeff n f * (a ^ n).coeff g := by
  rw [PowerSeries.coeff_heval]
  refine finsum_congr fun n ↦ ?_
  rw [SummableFamily.coeff_def, SummableFamily.powerSeriesFamily_of_orderTop_pos ha,
    HahnSeries.coeff_smul, smul_eq_mul]

/-- The evaluation of a series without constant term has positive order. -/
theorem orderTop_heval_pos {a : HahnSeries Γ ℝ} (ha : 0 < a.orderTop) {g : PowerSeries ℝ}
    (hg : PowerSeries.constantCoeff g = 0) : 0 < (PowerSeries.heval a g).orderTop := by
  obtain ⟨g', hg'⟩ := PowerSeries.X_dvd_iff.2 hg
  rw [hg', PowerSeries.heval_mul, PowerSeries.heval_X a ha, HahnSeries.orderTop_mul]
  exact add_pos_of_pos_of_nonneg ha (zero_le_orderTop_heval ha g')

/-- **THE COMPOSITION LAW**: for `g` without constant term and `a` of positive order,
`heval a (f.subst g) = heval (heval a g) f`. Coefficientwise both sides are the finite double sum
`Σ_{d, n} f_d · coeff n (g^d) · coeff γ (aⁿ)`, in the two orders. -/
theorem heval_subst {a : HahnSeries Γ ℝ} (ha : 0 < a.orderTop) {g : PowerSeries ℝ}
    (hg : PowerSeries.constantCoeff g = 0) (f : PowerSeries ℝ) :
    PowerSeries.heval a (f.subst g) = PowerSeries.heval (PowerSeries.heval a g) f := by
  have hg' : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have hag : 0 < (PowerSeries.heval a g).orderTop := orderTop_heval_pos ha hg
  ext γ
  rw [coeff_heval_eq ha, coeff_heval_eq hag]
  set F : ℕ × ℕ → ℝ := fun p ↦
    (PowerSeries.coeff p.1 f • PowerSeries.coeff p.2 (g ^ p.1)) * (a ^ p.2).coeff γ with hF_def
  have hF : (Function.support F).Finite := by
    have hS : {n : ℕ | (a ^ n).coeff γ ≠ 0}.Finite := SummableFamily.pow_finite_co_support ha γ
    refine (hS.biUnion fun n _ ↦
      Set.Finite.image (fun d ↦ (d, n)) (PowerSeries.coeff_subst_finite' hg' f n)).subset ?_
    intro p hp
    rw [Function.mem_support, hF_def] at hp
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hp
    exact Set.mem_iUnion₂.2 ⟨p.2, h2, p.1, h1, rfl⟩
  have hF' : (Function.support fun q : ℕ × ℕ ↦ F q.swap).Finite :=
    hF.preimage Prod.swap_injective.injOn
  calc ∑ᶠ n, PowerSeries.coeff n (f.subst g) * (a ^ n).coeff γ
      = ∑ᶠ n, ∑ᶠ d, F (d, n) := by
        refine finsum_congr fun n ↦ ?_
        rw [PowerSeries.coeff_subst' hg', finsum_mul]
    _ = ∑ᶠ q : ℕ × ℕ, F q.swap := (finsum_curry (fun q : ℕ × ℕ ↦ F q.swap) hF').symm
    _ = ∑ᶠ p, F p := finsum_comp_equiv (Equiv.prodComm ℕ ℕ)
    _ = ∑ᶠ d, ∑ᶠ n, F (d, n) := finsum_curry F hF
    _ = ∑ᶠ d, PowerSeries.coeff d f * ((PowerSeries.heval a g) ^ d).coeff γ := by
        refine finsum_congr fun d ↦ ?_
        rw [← map_pow, coeff_heval_eq ha, mul_finsum]
        refine finsum_congr fun n ↦ ?_
        show (PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)) * (a ^ n).coeff γ = _
        ring

/-- The composition law on surreals, in Hahn-series form. -/
theorem hevalS_subst {ε : Surreal.{u}} (hε : Infinitesimal ε) {g : PowerSeries ℝ}
    (hg : PowerSeries.constantCoeff g = 0) (f : PowerSeries ℝ) :
    hevalS ε (f.subst g) = hevalS (fevalHS ε g) f := by
  apply toHahn_injective
  rw [toHahn_hevalS, toHahn_hevalS, fevalHS, toHahnSeries_evalHahn, toHahn_hevalS,
    heval_subst (orderTop_pos_of_infinitesimal hε) hg]

/-- **THE COMPOSITION LAW ON SURREALS**: `fevalHS ε (f ∘ g) = fevalHS (fevalHS ε g) f` for every
infinitesimal `ε` and every `g` without constant term. -/
theorem fevalHS_subst {ε : Surreal.{u}} (hε : Infinitesimal ε) {g : PowerSeries ℝ}
    (hg : PowerSeries.constantCoeff g = 0) (f : PowerSeries ℝ) :
    fevalHS ε (f.subst g) = fevalHS (fevalHS ε g) f := by
  rw [fevalHS, hevalS_subst hε hg]
  rfl

/-- A series without constant term evaluates to an infinitesimal. -/
theorem infinitesimal_fevalHS_of_constantCoeff_eq_zero {ε : Surreal.{u}} (hε : Infinitesimal ε)
    {g : PowerSeries ℝ} (hg : PowerSeries.constantCoeff g = 0) : Infinitesimal (fevalHS ε g) := by
  obtain ⟨g', hg'⟩ := PowerSeries.X_dvd_iff.2 hg
  rw [hg', fevalHS_mul, fevalHS_X hε]
  exact hε.mul_isFinite (isFinite_fevalHS hε g')

/-- The jet of a composite is the composite of the jets: `J (f ∘ g) c x = J f 0 (J g c x)`. -/
theorem jet_subst {g : PowerSeries ℝ} (hg : PowerSeries.constantCoeff g = 0) (f : PowerSeries ℝ)
    (c : Surreal.{u}) {x : Surreal.{u}} (hx : Infinitesimal (x - c)) :
    jet (f.subst g) c x = jet f 0 (jet g c x) := by
  rw [jet_apply, jet_apply, jet_apply, sub_zero, fevalHS_subst hx hg]

/-- **THE CHAIN RULE FOR JET FUNCTIONS**: `(f ∘ g)′ = (f′ ∘ g) · g′` at every point of the halo. -/
theorem hasDerivS_jet_subst {g : PowerSeries ℝ} (hg : PowerSeries.constantCoeff g = 0)
    (f : PowerSeries ℝ) (c : Surreal.{u}) {x : Surreal.{u}} (hx : Infinitesimal (x - c)) :
    HasDerivS (jet (f.subst g) c) x
      (jet (PowerSeries.derivative ℝ f) 0 (jet g c x) * jet (PowerSeries.derivative ℝ g) c x) := by
  have hg' : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have h := hasDerivS_jet' (f.subst g) c hx
  rw [PowerSeries.derivative_subst hg', jet_apply, fevalHS_mul, fevalHS_subst hx hg] at h
  rw [jet_apply (PowerSeries.derivative ℝ f), sub_zero]
  exact h

/-- A surreal-point derivative only depends on the function on the halo of the point. -/
theorem _root_.HasDerivS.congr_of_halo {f f' : Surreal → Surreal} {x d : Surreal}
    (h : HasDerivS f x d) (hf : ∀ δ, Infinitesimal δ → f (x + δ) = f' (x + δ)) (hx : f x = f' x) :
    HasDerivS f' x d := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun δ hδ ↦ ?_⟩
  rw [← hf δ hδ, ← hx]
  exact hC δ hδ

/-- **THE CHAIN RULE, classical form**: on the halo of `c`, `x ↦ J f 0 (J g c x)` has derivative
`J f′ 0 (J g c x) · J g′ c x`. -/
theorem hasDerivS_jet_comp {g : PowerSeries ℝ} (hg : PowerSeries.constantCoeff g = 0)
    (f : PowerSeries ℝ) (c : Surreal.{u}) {x : Surreal.{u}} (hx : Infinitesimal (x - c)) :
    HasDerivS (fun y ↦ jet f 0 (jet g c y)) x
      (jet (PowerSeries.derivative ℝ f) 0 (jet g c x) * jet (PowerSeries.derivative ℝ g) c x) :=
  HasDerivS.congr_of_halo (hasDerivS_jet_subst hg f c hx)
    (fun δ hδ ↦ jet_subst hg f c (by rw [add_sub_right_comm]; exact hx.add hδ))
    (jet_subst hg f c hx)

/-! ### THE FAITHFUL LOGARITHM -/

/-- `(1 + X) · log′(1 + X) = 1`: the derivative of `log (1 + X)` is the geometric series
`Σ (−1)ⁿ Xⁿ = 1/(1 + X)`. -/
theorem one_add_X_mul_derivative_log :
    (1 + PowerSeries.X) * PowerSeries.derivative ℝ (PowerSeries.log ℝ) = 1 := by
  rw [PowerSeries.deriv_log]
  ext n
  rcases n with _ | n
  · rw [add_mul, one_mul, map_add, PowerSeries.coeff_zero_X_mul, add_zero, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, if_pos rfl, pow_zero, map_one]
  · rw [add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), map_pow, map_pow,
      map_neg, map_one, pow_succ]
    ring

theorem constantCoeff_derivative_log :
    PowerSeries.constantCoeff (PowerSeries.derivative ℝ (PowerSeries.log ℝ)) = 1 := by
  have h := congrArg PowerSeries.constantCoeff one_add_X_mul_derivative_log
  rwa [map_mul, map_add, map_one, PowerSeries.constantCoeff_X, add_zero, one_mul] at h

/-- `log″(1 + X) = −(log′(1 + X))²`. -/
theorem derivative_derivative_log :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (PowerSeries.log ℝ)) =
      -(PowerSeries.derivative ℝ (PowerSeries.log ℝ)) ^ 2 := by
  set G := PowerSeries.derivative ℝ (PowerSeries.log ℝ) with hG
  have hG1 : (1 + PowerSeries.X) * G = 1 := one_add_X_mul_derivative_log
  have h := congrArg (PowerSeries.derivative ℝ) hG1
  rw [Derivation.leibniz, PowerSeries.derivative_one, map_add, PowerSeries.derivative_one,
    PowerSeries.derivative_X, zero_add, smul_eq_mul, smul_eq_mul, mul_one] at h
  calc PowerSeries.derivative ℝ G = PowerSeries.derivative ℝ G * ((1 + PowerSeries.X) * G) := by
        rw [hG1, mul_one]
    _ = G * ((1 + PowerSeries.X) * PowerSeries.derivative ℝ G + G) - G * G := by ring
    _ = -G ^ 2 := by rw [h, mul_zero, zero_sub, sq]

/-- Substituting a series without constant term preserves the constant coefficient. -/
theorem constantCoeff_subst_of_constantCoeff_eq_zero {g : PowerSeries ℝ}
    (hg : PowerSeries.constantCoeff g = 0) (f : PowerSeries ℝ) :
    PowerSeries.constantCoeff (f.subst g) = PowerSeries.constantCoeff f := by
  have hg' := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_subst' hg', finsum_eq_single _ 0]
  · rw [pow_zero, PowerSeries.coeff_one, if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hg, zero_pow hd, smul_zero]

/-- **`exp ∘ log = 1 + X`** as a power-series identity: `F := exp.subst log` satisfies
`F′ = F · log′` and `(F · log′)′ = 0`, so `F · log′ = 1` and `F = 1 + X`. -/
theorem exp_subst_log : (PowerSeries.exp ℝ).subst (PowerSeries.log ℝ) = 1 + PowerSeries.X := by
  set F := (PowerSeries.exp ℝ).subst (PowerSeries.log ℝ) with hF
  set G := PowerSeries.derivative ℝ (PowerSeries.log ℝ) with hG
  have hDF : PowerSeries.derivative ℝ F = F * G := by
    rw [hF, PowerSeries.derivative_subst PowerSeries.HasSubst.log, PowerSeries.derivative_exp]
  have hDG : PowerSeries.derivative ℝ G = -G ^ 2 := derivative_derivative_log
  have hFG : F * G = 1 := by
    apply PowerSeries.derivative.ext
    · rw [Derivation.leibniz, hDF, hDG, PowerSeries.derivative_one, smul_eq_mul, smul_eq_mul]
      ring
    · rw [map_mul, map_one, hF, constantCoeff_subst_of_constantCoeff_eq_zero PowerSeries.constantCoeff_log,
        PowerSeries.constantCoeff_exp, hG, constantCoeff_derivative_log, mul_one]
  calc F = F * (G * (1 + PowerSeries.X)) := by
        rw [mul_comm G, one_add_X_mul_derivative_log, mul_one]
    _ = 1 + PowerSeries.X := by rw [← mul_assoc, hFG, one_mul]

theorem constantCoeff_exp_sub_one : PowerSeries.constantCoeff (PowerSeries.exp ℝ - 1) = 0 := by
  rw [map_sub, PowerSeries.constantCoeff_exp, map_one, sub_self]

/-- The associativity of substitution, stated for abstract series (used to keep the concrete
instances below from unfolding). -/
theorem subst_subst_of_hasSubst {P Q L : PowerSeries ℝ} (hP : PowerSeries.HasSubst P)
    (hL : PowerSeries.HasSubst L) :
    PowerSeries.subst L (PowerSeries.subst P Q) = PowerSeries.subst (PowerSeries.subst L P) Q :=
  PowerSeries.subst_comp_subst_apply hP hL Q

/-- **`log ∘ (exp − 1) = X`** as a power-series identity: `log` is the substitution inverse of
`exp − 1` (from `exp_subst_log` and the uniqueness of substitution inverses). -/
theorem log_subst_exp_sub_one :
    (PowerSeries.log ℝ).subst (PowerSeries.exp ℝ - 1) = PowerSeries.X := by
  have hP0 : PowerSeries.constantCoeff (PowerSeries.exp ℝ - 1) = 0 := constantCoeff_exp_sub_one
  have hP1' : PowerSeries.coeff 1 (PowerSeries.exp ℝ - 1) = 1 := by
    rw [map_sub, PowerSeries.coeff_exp, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero,
      Nat.factorial_one, Nat.cast_one, div_one, map_one]
  have hP1 : IsUnit (PowerSeries.coeff 1 (PowerSeries.exp ℝ - 1)) := by
    rw [hP1']
    exact isUnit_one
  have hPsubst : PowerSeries.HasSubst (PowerSeries.exp ℝ - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hP0
  have hPL : (PowerSeries.exp ℝ - 1).subst (PowerSeries.log ℝ) = PowerSeries.X := by
    rw [PowerSeries.subst_sub PowerSeries.HasSubst.log, exp_subst_log,
      ← PowerSeries.coe_substAlgHom PowerSeries.HasSubst.log, map_one, add_sub_cancel_left]
  obtain ⟨Q, hQP⟩ : ∃ Q : PowerSeries ℝ,
      PowerSeries.subst (PowerSeries.exp ℝ - 1) Q = PowerSeries.X :=
    ⟨_, PowerSeries.subst_substInvOfIsUnit_left _ hP0 hP1⟩
  have hLQ : PowerSeries.log ℝ = Q := by
    calc PowerSeries.log ℝ = PowerSeries.subst (PowerSeries.log ℝ) PowerSeries.X :=
          (PowerSeries.subst_X PowerSeries.HasSubst.log).symm
      _ = PowerSeries.subst (PowerSeries.log ℝ) (PowerSeries.subst (PowerSeries.exp ℝ - 1) Q) := by
          rw [hQP]
      _ = PowerSeries.subst (PowerSeries.subst (PowerSeries.log ℝ) (PowerSeries.exp ℝ - 1)) Q :=
          subst_subst_of_hasSubst hPsubst PowerSeries.HasSubst.log
      _ = Q := by rw [hPL, PowerSeries.X_subst]
  rw [hLQ]
  exact hQP

/-- **THE FAITHFUL LOGARITHM** `logH1p ε := fevalHS ε (log ℝ)`, i.e. `log (1 + ε)`, the log series
evaluated through Conway's isomorphism. A total function; honest on infinitesimals. -/
def logH1p (ε : Surreal.{u}) : Surreal.{u} :=
  fevalHS ε (PowerSeries.log ℝ)

theorem logH1p_def (ε : Surreal.{u}) : logH1p ε = fevalHS ε (PowerSeries.log ℝ) := rfl

theorem infinitesimal_logH1p {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    Infinitesimal (logH1p ε) :=
  infinitesimal_fevalHS_of_constantCoeff_eq_zero hε PowerSeries.constantCoeff_log

@[simp]
theorem logH1p_zero : logH1p (0 : Surreal.{u}) = 0 := by
  rw [logH1p, fevalHS_zero_left, PowerSeries.constantCoeff_log, Real.toSurreal_zero]

/-- **`exp ∘ log = id`**: `expH (logH1p ε) = 1 + ε` at every infinitesimal `ε` — an honest
inverse (contrast `expInf_ne_one_add_of_isHahnSum_log_wpow`). -/
theorem expH_logH1p {ε : Surreal.{u}} (hε : Infinitesimal ε) : expH (logH1p ε) = 1 + ε := by
  rw [expH, logH1p, ← fevalHS_subst hε PowerSeries.constantCoeff_log, exp_subst_log, fevalHS_add,
    fevalHS_one, fevalHS_X hε]

/-- **`log ∘ exp = id`**: `logH1p (expH ε − 1) = ε` at every infinitesimal `ε`. -/
theorem logH1p_expH_sub_one {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    logH1p (expH ε - 1) = ε := by
  rw [logH1p, expH, ← fevalHS_one ε, ← fevalHS_sub,
    ← fevalHS_subst hε constantCoeff_exp_sub_one, log_subst_exp_sub_one, fevalHS_X hε]

/-- The faithful logarithm is injective on infinitesimals. -/
theorem logH1p_inj {ε δ : Surreal.{u}} (hε : Infinitesimal ε) (hδ : Infinitesimal δ) :
    logH1p ε = logH1p δ ↔ ε = δ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have h' := congrArg expH h
  rwa [expH_logH1p hε, expH_logH1p hδ, add_right_inj] at h'

/-- **The logarithm of a product**: `log ((1+ε)(1+δ)) = log (1+ε) + log (1+δ)`. -/
theorem logH1p_mul {ε δ : Surreal.{u}} (hε : Infinitesimal ε) (hδ : Infinitesimal δ) :
    logH1p ((1 + ε) * (1 + δ) - 1) = logH1p ε + logH1p δ := by
  have h1 : Infinitesimal ((1 + ε) * (1 + δ) - 1) := by
    rw [show (1 + ε) * (1 + δ) - 1 = ε + δ + ε * δ by ring]
    exact (hε.add hδ).add (hε.mul_isFinite hδ.isFinite)
  rw [← expH_inj (infinitesimal_logH1p h1)
    ((infinitesimal_logH1p hε).add (infinitesimal_logH1p hδ)),
    expH_add (infinitesimal_logH1p hε) (infinitesimal_logH1p hδ), expH_logH1p h1, expH_logH1p hε,
    expH_logH1p hδ, add_sub_cancel]

theorem logH1p_pos_of_pos {ε : Surreal.{u}} (hε : Infinitesimal ε) (h : 0 < ε) : 0 < logH1p ε := by
  by_contra hle
  have h1 := expH_logH1p hε
  rcases (not_lt.1 hle).lt_or_eq with hlt | heq
  · have := expH_lt_one_of_neg (infinitesimal_logH1p hε) hlt
    linarith
  · rw [heq, expH_zero] at h1
    linarith

theorem logH1p_lt_logH1p_of_lt {ε δ : Surreal.{u}} (hε : Infinitesimal ε) (hδ : Infinitesimal δ)
    (h : ε < δ) : logH1p ε < logH1p δ := by
  by_contra hle
  have := expH_lt_expH_of_lt (infinitesimal_logH1p hε) (infinitesimal_logH1p hδ)
  rw [not_lt] at hle
  rcases hle.lt_or_eq with hlt | heq
  · have h2 := expH_lt_expH_of_lt (infinitesimal_logH1p hδ) (infinitesimal_logH1p hε) hlt
    rw [expH_logH1p hε, expH_logH1p hδ] at h2
    linarith
  · rw [(logH1p_inj hδ hε).1 heq] at h
    exact lt_irrefl _ h

/-- The value of `log′(1 + X)` at `ε` is `(1 + ε)⁻¹`. -/
theorem fevalHS_derivative_log {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    fevalHS ε (PowerSeries.derivative ℝ (PowerSeries.log ℝ)) = (1 + ε)⁻¹ := by
  have h := congrArg (fevalHS ε) one_add_X_mul_derivative_log
  rw [fevalHS_mul, fevalHS_add, fevalHS_one, fevalHS_X hε] at h
  exact eq_inv_of_mul_eq_one_right h

/-- **`log′ = 1/x`**: `x ↦ logH1p (x − 1)` has surreal-point derivative `(1 + ε)⁻¹` at `1 + ε`,
for every infinitesimal `ε`. -/
theorem hasDerivS_logH1p {ε : Surreal.{u}} (hε : Infinitesimal ε) :
    HasDerivS (fun x ↦ logH1p (x - 1)) (1 + ε) ((1 + ε)⁻¹) := by
  have h := hasDerivS_jet (PowerSeries.log ℝ) 1 hε
  rw [fevalHS_derivative_log hε] at h
  exact h

/-- `log′ = 1/x` at every point `x` of the halo of `1`. -/
theorem hasDerivS_logH1p' {x : Surreal.{u}} (hx : Infinitesimal (x - 1)) :
    HasDerivS (fun x ↦ logH1p (x - 1)) x x⁻¹ := by
  have h := hasDerivS_logH1p hx
  rwa [add_sub_cancel] at h

/-- **THE CONTRAST**: at `x = ω⁻¹ + ω^(−ω)` the faithful pair is an honest inverse pair,
`expH (logH1p x) = 1 + x`, while no canonical Hahn sum `σ` of the log series at `x` satisfies
`expInf σ = 1 + x` (`HaloGame.expInf_ne_one_add_of_isHahnSum_log_wpow`). -/
theorem expH_logH1p_and_not_expInf_log :
    expH (logH1p (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal))))) =
        1 + (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal)))) ∧
      ∀ (σ : Surreal.{u})
        (hσ : IsHahnSum (logSeriesAt (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal))))) σ),
        expInf σ (infinitesimal_of_isHahnSum_log infinitesimal_wpow_neg_one_add_wpow_neg_omega
            wpow_neg_one_add_wpow_neg_omega_ne_zero hσ)
          (ne_zero_of_isHahnSum_log infinitesimal_wpow_neg_one_add_wpow_neg_omega
            wpow_neg_one_add_wpow_neg_omega_ne_zero hσ) ≠
          1 + (ω^ (-1 : Surreal.{u}) + ω^ (-(ω^ (1 : Surreal)))) :=
  ⟨expH_logH1p infinitesimal_wpow_neg_one_add_wpow_neg_omega,
    fun _ hσ ↦ expInf_ne_one_add_of_isHahnSum_log_wpow hσ⟩

end Surreal

end
