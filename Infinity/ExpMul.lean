import Infinity.CanonicalSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# The exponential functional equation, modulo domination

The multiplicative law of the exponential, on the surreals: for **positive** infinitesimals
`ε, δ`, the product `expInf ε * expInf δ` is a Hahn sum of the exponential series at `ε + δ`
(`isHahnSum_expInf_mul`) — hence the canonical values satisfy

`expInf (ε + δ) ≈ expInf ε * expInf δ`  modulo domination by every term `(ε+δ)ⁿ/n!`
(`mk_expInf_add_sub_mul`).

Positivity is the honest scope: under cancellation (`δ ≈ -ε`) the sum `ε + δ` lives at a
finer scale than the factors control, and the product genuinely cannot be pinned against
the finer series.

The proof is the partial-sum Cauchy product: with `s, r` the `n`-th partial sums at `ε, δ`
and `P` the one at `ε + δ`,

`x·y − P = [x·y − s·r] + [s·r − P]`,

where the first bracket is `s·(y−r) + (x−s)·r + (x−s)·(y−r)` (each factor's Hahn residual
enters once, at class ≥ `n • mk (ε+δ)`), and the second bracket is — by the binomial theorem
organized along antidiagonals — exactly the sum of the terms `εⁱδʲ/(i!j!)` with
`i, j < n ≤ i + j`, all of class ≥ `n • mk (ε+δ)`.

Whether the **exact** equation `expInf (ε+δ) = expInf ε * expInf δ` holds is a genuinely
open question this development surfaces: it asks whether birthday-minimality of Hahn sums
is multiplicative.
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

/-! ### Domination-calculus helpers (`≤` versions) -/

private theorem le_mk_add {c : ArchimedeanClass Surreal} {a b : Surreal}
    (ha : c ≤ ArchimedeanClass.mk a) (hb : c ≤ ArchimedeanClass.mk b) :
    c ≤ ArchimedeanClass.mk (a + b) :=
  le_trans (le_min ha hb) (ArchimedeanClass.min_le_mk_add ..)

private theorem le_mk_sum {ι : Type*} {c : ArchimedeanClass Surreal} {s : Finset ι}
    {u : ι → Surreal} (h : ∀ i ∈ s, c ≤ ArchimedeanClass.mk (u i)) :
    c ≤ ArchimedeanClass.mk (∑ i ∈ s, u i) := by
  induction s using Finset.cons_induction with
  | empty =>
    have h0 : ArchimedeanClass.mk (0 : Surreal) = ⊤ := ArchimedeanClass.mk_eq_top_iff.2 rfl
    rw [Finset.sum_empty, h0]
    exact le_top
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact le_mk_add (h a (Finset.mem_cons_self ..))
      (ih fun i hi ↦ h i (Finset.mem_cons_of_mem hi))

/-! ### Class computations for the exponential series -/

/-- The class of an exponential-series term. -/
private theorem mk_expTerm {ε : Surreal} (k : ℕ) :
    ArchimedeanClass.mk (ε ^ k / ((k.factorial : ℕ) : Surreal)) =
      k • ArchimedeanClass.mk ε := by
  rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero, ArchimedeanClass.mk_pow]

/-- A partial sum of the exponential series at an infinitesimal lies in the class of `1`. -/
private theorem mk_partialSum_expSeries {ε : Surreal} (hε : Infinitesimal ε) {n : ℕ}
    (hn : 1 ≤ n) :
    ArchimedeanClass.mk
      (partialSum (fun k ↦ ε ^ k / ((k.factorial : ℕ) : Surreal)) n) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  have hfin : ∀ k ∈ range n,
      IsFinite (ε ^ k / ((k.factorial : ℕ) : Surreal)) := by
    intro k _
    rw [IsFinite, mk_expTerm]
    exact nsmul_nonneg hε.le k
  rw [partialSum, stdPart_sum hfin]
  rw [Finset.sum_eq_single_of_mem 0 (mem_range.2 (by omega)) ?_]
  · rw [show ε ^ 0 / (((0 : ℕ).factorial : ℕ) : Surreal) = 1 by norm_num,
      ArchimedeanClass.stdPart_one]
    norm_num
  · intro k _ hk
    apply Infinitesimal.stdPart_eq_zero
    rw [Infinitesimal, mk_expTerm]
    have h1 : (0 : ArchimedeanClass Surreal) < 1 • ArchimedeanClass.mk ε := by
      rwa [one_nsmul]
    exact h1.trans_le (nsmul_le_nsmul_left hε.le (by omega))

/-- `expInf` lies in the class of `1`. -/
private theorem mk_expInf {ε : Surreal} (hε : Infinitesimal ε) (hε0 : ε ≠ 0) :
    ArchimedeanClass.mk (expInf ε hε hε0) = 0 :=
  mk_eq_zero_of_stdPart_ne_zero (by rw [stdPart_expInf]; norm_num)

/-! ### The binomial identity along antidiagonals -/

/-- One binomial layer: `(ε+δ)ᵏ/k!` is the antidiagonal sum of `εⁱδʲ/(i!j!)`. -/
private theorem expTerm_add (ε δ : Surreal) (k : ℕ) :
    (ε + δ) ^ k / ((k.factorial : ℕ) : Surreal) =
      ∑ p ∈ Finset.antidiagonal k,
        ε ^ p.1 * δ ^ p.2 / (((p.1.factorial : ℕ) : Surreal) * ((p.2.factorial : ℕ) : Surreal)) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, (Commute.all ε δ).add_pow k,
    div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hik : i ≤ k := by
    have := mem_range.1 hi
    omega
  have h1 : ((k.choose i : ℕ) : Surreal) =
      ((k.factorial : ℕ) : Surreal) /
        (((i.factorial : ℕ) : Surreal) * (((k - i).factorial : ℕ) : Surreal)) := by
    exact_mod_cast Nat.cast_choose (K := Surreal) hik
  have hK : ((k.factorial : ℕ) : Surreal) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have hI : ((i.factorial : ℕ) : Surreal) ≠ 0 := Nat.cast_ne_zero.2 i.factorial_ne_zero
  have hJ : (((k - i).factorial : ℕ) : Surreal) ≠ 0 :=
    Nat.cast_ne_zero.2 (k - i).factorial_ne_zero
  rw [h1]
  field_simp

/-- The triangle `{(i,j) : i+j < n}` is the union of the antidiagonals below `n`. -/
private theorem triangle_eq_biUnion (n : ℕ) :
    ((range n ×ˢ range n).filter fun p ↦ p.1 + p.2 < n) =
      (range n).biUnion Finset.antidiagonal := by
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_biUnion,
    Finset.mem_antidiagonal]
  constructor
  · rintro ⟨⟨_, _⟩, h⟩
    exact ⟨i + j, h, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    omega

/-- The partial-sum Cauchy identity: the product of partial sums minus the partial sum of
the binomial series is exactly the high-degree part of the square. -/
private theorem partialSum_mul_sub (ε δ : Surreal) (n : ℕ) :
    partialSum (fun k ↦ ε ^ k / ((k.factorial : ℕ) : Surreal)) n *
      partialSum (fun k ↦ δ ^ k / ((k.factorial : ℕ) : Surreal)) n -
    partialSum (fun k ↦ (ε + δ) ^ k / ((k.factorial : ℕ) : Surreal)) n =
      ∑ p ∈ (range n ×ˢ range n).filter fun p ↦ ¬ p.1 + p.2 < n,
        ε ^ p.1 * δ ^ p.2 /
          (((p.1.factorial : ℕ) : Surreal) * ((p.2.factorial : ℕ) : Surreal)) := by
  have hsq : partialSum (fun k ↦ ε ^ k / ((k.factorial : ℕ) : Surreal)) n *
      partialSum (fun k ↦ δ ^ k / ((k.factorial : ℕ) : Surreal)) n =
      ∑ p ∈ range n ×ˢ range n,
        ε ^ p.1 * δ ^ p.2 /
          (((p.1.factorial : ℕ) : Surreal) * ((p.2.factorial : ℕ) : Surreal)) := by
    rw [partialSum, partialSum, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [div_mul_div_comm]
  have hP : partialSum (fun k ↦ (ε + δ) ^ k / ((k.factorial : ℕ) : Surreal)) n =
      ∑ p ∈ (range n ×ˢ range n).filter fun p ↦ p.1 + p.2 < n,
        ε ^ p.1 * δ ^ p.2 /
          (((p.1.factorial : ℕ) : Surreal) * ((p.2.factorial : ℕ) : Surreal)) := by
    rw [triangle_eq_biUnion, Finset.sum_biUnion, partialSum]
    · exact Finset.sum_congr rfl fun k _ ↦ expTerm_add ε δ k
    · intro a _ b _ hab
      simp only [Finset.disjoint_left, Finset.mem_antidiagonal]
      rintro ⟨i, j⟩ h1 h2
      exact hab (h1 ▸ h2)
  rw [hsq, hP, ← Finset.sum_filter_add_sum_filter_not (range n ×ˢ range n)
    (fun p ↦ p.1 + p.2 < n)]
  ring

/-! ### The main theorem -/

/-- **The exponential multiplies** (Cauchy product): for positive infinitesimals `ε, δ`,
the product of the canonical exponentials is a Hahn sum of the exponential series at
`ε + δ`. -/
theorem isHahnSum_expInf_mul {ε δ : Surreal} (hε : Infinitesimal ε) (hδ : Infinitesimal δ)
    (hε0 : 0 < ε) (hδ0 : 0 < δ) :
    IsHahnSum (fun k ↦ (ε + δ) ^ k / ((k.factorial : ℕ) : Surreal))
      (expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne') := by
  intro n
  set x := expInf ε hε hε0.ne' with hx
  set y := expInf δ hδ hδ0.ne' with hy
  set m := ArchimedeanClass.mk (ε + δ) with hm
  -- the target class
  rw [mk_expTerm]
  -- scale comparisons: `mk (ε+δ) ≤ mk ε, mk δ` (no cancellation for positives), `0 < m`
  have hmε : m ≤ ArchimedeanClass.mk ε :=
    ArchimedeanClass.mk_antitoneOn (Set.mem_Ici.2 hε0.le)
      (Set.mem_Ici.2 (by positivity)) (by linarith)
  have hmδ : m ≤ ArchimedeanClass.mk δ :=
    ArchimedeanClass.mk_antitoneOn (Set.mem_Ici.2 hδ0.le)
      (Set.mem_Ici.2 (by positivity)) (by linarith)
  have hm0 : (0 : ArchimedeanClass Surreal) ≤ m := (hε.add hδ).le
  obtain rfl | hn := Nat.eq_zero_or_pos n
  -- stage 0: the residual is `x*y`, of class 0
  · rw [partialSum_zero, sub_zero, ArchimedeanClass.mk_mul, mk_expInf hε hε0.ne',
      mk_expInf hδ hδ0.ne', add_zero, zero_nsmul]
  -- main stage: split the residual
  · set s := partialSum (fun k ↦ ε ^ k / ((k.factorial : ℕ) : Surreal)) n with hs
    set r := partialSum (fun k ↦ δ ^ k / ((k.factorial : ℕ) : Surreal)) n with hr
    have hsplit : x * y - partialSum (fun k ↦ (ε + δ) ^ k / ((k.factorial : ℕ) : Surreal)) n =
        (s * (y - r) + ((x - s) * r + (x - s) * (y - r))) +
          (s * r - partialSum (fun k ↦ (ε + δ) ^ k / ((k.factorial : ℕ) : Surreal)) n) := by
      ring
    rw [hsplit]
    -- residual classes of the factors
    have hb : (n : ℕ) • m ≤ ArchimedeanClass.mk (y - r) := by
      refine le_trans ?_ (isHahnSum_expInf hδ hδ0.ne' n)
      rw [mk_expTerm]
      exact nsmul_le_nsmul_right hmδ n
    have ha : (n : ℕ) • m ≤ ArchimedeanClass.mk (x - s) := by
      refine le_trans ?_ (isHahnSum_expInf hε hε0.ne' n)
      rw [mk_expTerm]
      exact nsmul_le_nsmul_right hmε n
    refine le_mk_add (le_mk_add ?_ (le_mk_add ?_ ?_)) ?_
    -- `s * (y - r)`
    · rw [ArchimedeanClass.mk_mul, mk_partialSum_expSeries hε hn, zero_add]
      exact hb
    -- `(x - s) * r`
    · rw [ArchimedeanClass.mk_mul, mk_partialSum_expSeries hδ hn, add_zero]
      exact ha
    -- `(x - s) * (y - r)`
    · rw [ArchimedeanClass.mk_mul]
      have h0b : (0 : ArchimedeanClass Surreal) ≤ ArchimedeanClass.mk (y - r) :=
        le_trans (nsmul_nonneg hm0 n) hb
      exact le_trans ha (le_add_of_nonneg_right h0b)
    -- the high triangle: all remaining terms have total degree ≥ n
    · rw [hs, hr, partialSum_mul_sub]
      refine le_mk_sum fun p hp ↦ ?_
      obtain ⟨_, hsum⟩ := Finset.mem_filter.1 hp
      rw [not_lt] at hsum
      rw [ArchimedeanClass.mk_div, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
        mk_factorial, mk_factorial, add_zero, sub_zero, ArchimedeanClass.mk_pow,
        ArchimedeanClass.mk_pow]
      calc (n : ℕ) • m ≤ (p.1 + p.2) • m := nsmul_le_nsmul_left hm0 hsum
        _ = p.1 • m + p.2 • m := add_nsmul ..
        _ ≤ p.1 • ArchimedeanClass.mk ε + p.2 • ArchimedeanClass.mk δ :=
            add_le_add (nsmul_le_nsmul_right hmε _) (nsmul_le_nsmul_right hmδ _)

/-- **The exponential functional equation, modulo domination**: for positive infinitesimals,
the canonical value `expInf (ε + δ)` and the product `expInf ε * expInf δ` agree up to
domination by every term `(ε+δ)ⁿ/n!` of the series. (Whether they are *exactly* equal —
i.e. whether birthday-minimality of Hahn sums is multiplicative — is an open question this
development surfaces.) -/
theorem mk_expInf_add_sub_mul {ε δ : Surreal} (hε : Infinitesimal ε) (hδ : Infinitesimal δ)
    (hε0 : 0 < ε) (hδ0 : 0 < δ) (n : ℕ) :
    ArchimedeanClass.mk ((ε + δ) ^ n / ((n.factorial : ℕ) : Surreal)) ≤
      ArchimedeanClass.mk
        (expInf (ε + δ) (hε.add hδ) (by positivity) -
          expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne') :=
  IsHahnSum.mk_sub_le (isHahnSum_expInf (hε.add hδ) (by positivity))
    (isHahnSum_expInf_mul hε hδ hε0 hδ0) n

end Surreal
