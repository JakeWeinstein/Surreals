import Infinity.CanonicalSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# The general Cauchy product theorem for transfinite sums

`Infinity.ExpMul` proved that the exponential series multiplies — by running the partial-sum
Cauchy product concretely through the binomial theorem. This file proves that theorem at its
natural generality: **Hahn-sum semantics is multiplicative**, under a single no-cancellation
hypothesis, with no binomial content at all.

For series `t, u : ℕ → Surreal` the **Cauchy product** is
`cauchyMul t u n := Σ_{i+j=n} tᵢ·uⱼ` (a sum over the `n`-th antidiagonal), and the theorem is:

* `Surreal.IsHahnSum.mul` : if `x` is a Hahn sum of `t` and `y` of `u`, and the series
  satisfies the **no-cancellation floor**
  `∀ n i j, n ≤ i + j → mk (cauchyMul t u n) ≤ mk (t i * u j)`
  — every raw product of total degree at least `n` is dominated by the `n`-th product term —
  then `x * y` is a Hahn sum of `cauchyMul t u`.

**Hypothesis design.** The floor must be assumed on the *raw products* `tᵢ·uⱼ`, not derived
from scale data on `cauchyMul` itself: cancellation inside an antidiagonal can push
`cauchyMul t u n` into a strictly larger class (smaller magnitude) than its constituents, and
then the product `x·y` genuinely cannot be pinned against the finer series — this is the same
honest boundary that restricts the exponential law to *positive* infinitesimals. More
surprisingly, the floor is the *only* hypothesis needed. The two auxiliary families one
expects from the `ExpMul` template — partial sums of class `0`, and
`mk (cauchyMul t u n) ≤ mk (t n), mk (u n)` — are subsumed: in the residual split

`x·y − Pₙ = sₙ·(y − rₙ) + (x − sₙ)·rₙ + (x − sₙ)·(y − rₙ) + (sₙ·rₙ − Pₙ)`,

the factor pieces are estimated by expanding `sₙ·uₙ = Σ_{i<n} tᵢ·uₙ` — a sum of raw products
of total degree `≥ n`, each covered by the floor — and then trading `mk (uₙ)` for the Hahn
residual `mk (y − rₙ)` by monotonicity of class addition. Every piece reduces to the floor.

The combinatorial half is pure `Finset` bookkeeping, stated independently:

* `Surreal.partialSum_mul_sub_cauchyMul` : the partial-sum square identity — the product of
  `n`-th partial sums minus the `n`-th partial sum of the Cauchy product is exactly the
  high-degree corner `Σ_{i,j<n, i+j≥n} tᵢ·uⱼ` of the square. (In `ExpMul` this carried the
  binomial theorem; here the antidiagonal *is* the definition, and the binomial theorem
  vanishes from the story.)

Corollaries:

* `Surreal.IsHahnSum.sq` : the Cauchy square — `x²` sums `cauchyMul t t`.
* `Surreal.IsHahnSum.eq_partialSum_of_apply_eq_zero` : **exactness at ⊤**: a Hahn sum of a
  series with a vanishing term *equals* the partial sum at that index — domination semantics
  collapses to equality exactly when the controlling class is `⊤`.
* `Surreal.IsHahnSum.sq_eq_partialSum` : hence if the Cauchy square of a series terminates
  (`cauchyMul t t N = 0` under the floor), then `x²` is *exactly* the partial square sum.
  This is the mechanism the square-root program needs: to certify `x = √s` on the nose, one
  wants a candidate series for `x` whose Cauchy square reproduces the (finitely supported)
  series of `s` — beyond finite support, exactness would additionally require canonicity
  transport (is birthday-minimality multiplicative? — the open question `ExpMul` surfaces).
* `Surreal.isHahnSum_expInf_mul'` : the exponential functional equation re-derived from the
  general theorem — for positive infinitesimals, `expInf ε * expInf δ` is a Hahn sum of the
  exponential series at `ε + δ`; the only series-specific inputs are the binomial collapse
  of `cauchyMul` and the class floor `n • mk (ε+δ) ≤ i • mk ε + j • mk δ`.
* `Surreal.isHahnSum_geometric_sq` : a new instance for free — the Cauchy square of the
  geometric series: `Σ_{n<ω} (n+1)·ω⁻ⁿ` has Hahn sum `(ω/(ω−1))²`.
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

/-- The **Cauchy product** of two series: `cauchyMul t u n = Σ_{i+j=n} tᵢ·uⱼ`. -/
def cauchyMul (t u : ℕ → Surreal) (n : ℕ) : Surreal :=
  ∑ p ∈ Finset.antidiagonal n, t p.1 * u p.2

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

/-! ### The partial-sum square identity -/

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

/-- **The partial-sum square identity**: the product of `n`-th partial sums minus the `n`-th
partial sum of the Cauchy product is exactly the high-degree corner of the square — the sum
of the raw products `tᵢ·uⱼ` with `i, j < n ≤ i + j`. Pure `Finset` combinatorics: the
triangle below the `n`-th antidiagonal is the union of the antidiagonals below `n`. -/
theorem partialSum_mul_sub_cauchyMul (t u : ℕ → Surreal) (n : ℕ) :
    partialSum t n * partialSum u n - partialSum (cauchyMul t u) n =
      ∑ p ∈ (range n ×ˢ range n).filter fun p ↦ ¬ p.1 + p.2 < n, t p.1 * u p.2 := by
  have hsq : partialSum t n * partialSum u n =
      ∑ p ∈ range n ×ˢ range n, t p.1 * u p.2 := by
    rw [partialSum, partialSum, Finset.sum_mul_sum, Finset.sum_product]
  have hP : partialSum (cauchyMul t u) n =
      ∑ p ∈ (range n ×ˢ range n).filter fun p ↦ p.1 + p.2 < n, t p.1 * u p.2 := by
    rw [triangle_eq_biUnion, Finset.sum_biUnion, partialSum]
    · exact Finset.sum_congr rfl fun k _ ↦ rfl
    · intro a _ b _ hab
      simp only [Finset.disjoint_left, Finset.mem_antidiagonal]
      rintro ⟨i, j⟩ h1 h2
      exact hab (h1 ▸ h2)
  rw [hsq, hP, ← Finset.sum_filter_add_sum_filter_not (range n ×ˢ range n)
    (fun p ↦ p.1 + p.2 < n)]
  ring

/-! ### The general Cauchy product theorem -/

/-- **The general Cauchy product theorem**: Hahn-sum semantics is multiplicative. If `x` is
a Hahn sum of `t` and `y` of `u`, and the series satisfy the **no-cancellation floor** —
every raw product `tᵢ·uⱼ` of total degree `i + j ≥ n` is dominated by the `n`-th
Cauchy-product term — then `x * y` is a Hahn sum of the Cauchy product `cauchyMul t u`.

The floor is the only hypothesis: the residual splits as

`x·y − Pₙ = sₙ·(y − rₙ) + (x − sₙ)·rₙ + (x − sₙ)·(y − rₙ) + (sₙ·rₙ − Pₙ)`,

the last bracket is the high-degree corner of the square (`partialSum_mul_sub_cauchyMul`,
covered by the floor term by term), and each factor piece is estimated by expanding
`sₙ·uₙ = Σ_{i<n} tᵢ·uₙ` — again raw products of total degree `≥ n` — then trading
`mk (uₙ)` for the Hahn residual class `mk (y − rₙ)`. -/
theorem IsHahnSum.mul {t u : ℕ → Surreal} {x y : Surreal}
    (hx : IsHahnSum t x) (hy : IsHahnSum u y)
    (H : ∀ n i j : ℕ, n ≤ i + j →
      ArchimedeanClass.mk (cauchyMul t u n) ≤ ArchimedeanClass.mk (t i * u j)) :
    IsHahnSum (cauchyMul t u) (x * y) := by
  intro n
  have hsplit : x * y - partialSum (cauchyMul t u) n =
      (partialSum t n * (y - partialSum u n) +
        ((x - partialSum t n) * partialSum u n +
          (x - partialSum t n) * (y - partialSum u n))) +
        (partialSum t n * partialSum u n - partialSum (cauchyMul t u) n) := by
    ring
  rw [hsplit]
  refine le_mk_add (le_mk_add ?_ (le_mk_add ?_ ?_)) ?_
  -- `sₙ·(y − rₙ)`: expand `sₙ·uₙ` into raw products, then trade `uₙ` for the residual.
  · have h1 : ArchimedeanClass.mk (cauchyMul t u n) ≤
        ArchimedeanClass.mk (partialSum t n * u n) := by
      rw [partialSum, Finset.sum_mul]
      exact le_mk_sum fun i _ ↦ H n i n (Nat.le_add_left n i)
    calc ArchimedeanClass.mk (cauchyMul t u n)
        ≤ ArchimedeanClass.mk (partialSum t n * u n) := h1
      _ = ArchimedeanClass.mk (partialSum t n) + ArchimedeanClass.mk (u n) := by
          rw [ArchimedeanClass.mk_mul]
      _ ≤ ArchimedeanClass.mk (partialSum t n) +
            ArchimedeanClass.mk (y - partialSum u n) := add_le_add_right (hy n) _
      _ = ArchimedeanClass.mk (partialSum t n * (y - partialSum u n)) := by
          rw [ArchimedeanClass.mk_mul]
  -- `(x − sₙ)·rₙ`: symmetric.
  · have h1 : ArchimedeanClass.mk (cauchyMul t u n) ≤
        ArchimedeanClass.mk (t n * partialSum u n) := by
      rw [partialSum, Finset.mul_sum]
      exact le_mk_sum fun j _ ↦ H n n j (Nat.le_add_right n j)
    calc ArchimedeanClass.mk (cauchyMul t u n)
        ≤ ArchimedeanClass.mk (t n * partialSum u n) := h1
      _ = ArchimedeanClass.mk (t n) + ArchimedeanClass.mk (partialSum u n) := by
          rw [ArchimedeanClass.mk_mul]
      _ ≤ ArchimedeanClass.mk (x - partialSum t n) +
            ArchimedeanClass.mk (partialSum u n) := add_le_add_left (hx n) _
      _ = ArchimedeanClass.mk ((x - partialSum t n) * partialSum u n) := by
          rw [ArchimedeanClass.mk_mul]
  -- `(x − sₙ)·(y − rₙ)`: both residuals enter; the floor at `(n, n)` covers it.
  · calc ArchimedeanClass.mk (cauchyMul t u n)
        ≤ ArchimedeanClass.mk (t n * u n) := H n n n (Nat.le_add_right n n)
      _ = ArchimedeanClass.mk (t n) + ArchimedeanClass.mk (u n) := by
          rw [ArchimedeanClass.mk_mul]
      _ ≤ ArchimedeanClass.mk (x - partialSum t n) +
            ArchimedeanClass.mk (y - partialSum u n) := add_le_add (hx n) (hy n)
      _ = ArchimedeanClass.mk ((x - partialSum t n) * (y - partialSum u n)) := by
          rw [ArchimedeanClass.mk_mul]
  -- the high-degree corner: every term has total degree `≥ n`.
  · rw [partialSum_mul_sub_cauchyMul]
    refine le_mk_sum fun p hp ↦ ?_
    obtain ⟨-, hsum⟩ := Finset.mem_filter.1 hp
    rw [not_lt] at hsum
    exact H n p.1 p.2 hsum

/-- **The Cauchy square**: if `x` is a Hahn sum of `t` and the square satisfies the
no-cancellation floor, then `x²` is a Hahn sum of `cauchyMul t t`. -/
theorem IsHahnSum.sq {t : ℕ → Surreal} {x : Surreal} (hx : IsHahnSum t x)
    (H : ∀ n i j : ℕ, n ≤ i + j →
      ArchimedeanClass.mk (cauchyMul t t n) ≤ ArchimedeanClass.mk (t i * t j)) :
    IsHahnSum (cauchyMul t t) (x ^ 2) := by
  rw [pow_two]
  exact hx.mul hx H

/-! ### Exactness at `⊤`: vanishing terms pin the sum -/

/-- **Exactness**: a Hahn sum of a series with a vanishing term *equals* the partial sum at
that index. Domination by class `⊤` is equality — the one place where Hahn-sum semantics
pins a value on the nose rather than modulo finer classes. -/
theorem IsHahnSum.eq_partialSum_of_apply_eq_zero {t : ℕ → Surreal} {x : Surreal} {N : ℕ}
    (hx : IsHahnSum t x) (h0 : t N = 0) : x = partialSum t N := by
  have h := hx N
  rw [h0, show ArchimedeanClass.mk (0 : Surreal) = ⊤ from ArchimedeanClass.mk_eq_top_iff.2 rfl,
    top_le_iff] at h
  exact sub_eq_zero.1 (ArchimedeanClass.mk_eq_top_iff.1 h)

/-- **Exact squares from terminating Cauchy squares**: if `x` sums `t`, the square satisfies
the no-cancellation floor, and some Cauchy-square term vanishes, then `x²` is *exactly* the
partial sum of the square series — not merely modulo domination.

This is the exactness mechanism the square-root program rests on: to certify `x = √s`
exactly, exhibit a series for `x` whose Cauchy square reproduces a finitely supported series
of `s`. (Note the floor at a vanishing term forces the whole high-degree tail of raw products
to vanish, so this is genuinely the terminating case; for non-terminating squares, exactness
would further require canonicity transport — whether birthday-minimality of Hahn sums is
multiplicative, the open question surfaced by `Infinity.ExpMul`.) -/
theorem IsHahnSum.sq_eq_partialSum {t : ℕ → Surreal} {x : Surreal} {N : ℕ}
    (hx : IsHahnSum t x)
    (H : ∀ n i j : ℕ, n ≤ i + j →
      ArchimedeanClass.mk (cauchyMul t t n) ≤ ArchimedeanClass.mk (t i * t j))
    (h0 : cauchyMul t t N = 0) :
    x ^ 2 = partialSum (cauchyMul t t) N :=
  (hx.sq H).eq_partialSum_of_apply_eq_zero h0

/-! ### Instance I: the exponential functional equation, re-derived -/

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

/-- The Cauchy product of two exponential series is the exponential series of the sum:
the binomial theorem, packaged once. -/
private theorem cauchyMul_expSeries (ε δ : Surreal) (k : ℕ) :
    cauchyMul (fun i ↦ ε ^ i / ((i.factorial : ℕ) : Surreal))
      (fun j ↦ δ ^ j / ((j.factorial : ℕ) : Surreal)) k =
      (ε + δ) ^ k / ((k.factorial : ℕ) : Surreal) := by
  rw [expTerm_add, cauchyMul]
  exact Finset.sum_congr rfl fun p _ ↦ div_mul_div_comm ..

/-- The class of an exponential-series term. -/
private theorem mk_expTerm {ε : Surreal} (k : ℕ) :
    ArchimedeanClass.mk (ε ^ k / ((k.factorial : ℕ) : Surreal)) =
      k • ArchimedeanClass.mk ε := by
  rw [ArchimedeanClass.mk_div, mk_factorial, sub_zero, ArchimedeanClass.mk_pow]

/-- **The exponential multiplies, from the general theorem**: for positive infinitesimals
`ε, δ`, the product `expInf ε * expInf δ` is a Hahn sum of the exponential series at `ε + δ`.
This re-derives the content of `Infinity.ExpMul`'s `isHahnSum_expInf_mul` as an instance of
`IsHahnSum.mul`: the only series-specific inputs are the binomial collapse
`cauchyMul_expSeries` and the no-cancellation floor
`n • mk (ε+δ) ≤ i • mk ε + j • mk δ` (valid since positivity gives
`0 ≤ mk (ε+δ) ≤ mk ε, mk δ`). -/
theorem isHahnSum_expInf_mul' {ε δ : Surreal} (hε : Infinitesimal ε) (hδ : Infinitesimal δ)
    (hε0 : 0 < ε) (hδ0 : 0 < δ) :
    IsHahnSum (fun k ↦ (ε + δ) ^ k / ((k.factorial : ℕ) : Surreal))
      (expInf ε hε hε0.ne' * expInf δ hδ hδ0.ne') := by
  have hfun : (fun k ↦ (ε + δ) ^ k / ((k.factorial : ℕ) : Surreal)) =
      cauchyMul (fun i ↦ ε ^ i / ((i.factorial : ℕ) : Surreal))
        (fun j ↦ δ ^ j / ((j.factorial : ℕ) : Surreal)) :=
    funext fun k ↦ (cauchyMul_expSeries ε δ k).symm
  rw [hfun]
  have hmε : ArchimedeanClass.mk (ε + δ) ≤ ArchimedeanClass.mk ε :=
    ArchimedeanClass.mk_antitoneOn (Set.mem_Ici.2 hε0.le)
      (Set.mem_Ici.2 (by positivity)) (by linarith)
  have hmδ : ArchimedeanClass.mk (ε + δ) ≤ ArchimedeanClass.mk δ :=
    ArchimedeanClass.mk_antitoneOn (Set.mem_Ici.2 hδ0.le)
      (Set.mem_Ici.2 (by positivity)) (by linarith)
  have hm0 : (0 : ArchimedeanClass Surreal) ≤ ArchimedeanClass.mk (ε + δ) := (hε.add hδ).le
  refine (isHahnSum_expInf hε hε0.ne').mul (isHahnSum_expInf hδ hδ0.ne') ?_
  intro n i j hn
  rw [cauchyMul_expSeries, mk_expTerm]
  rw [ArchimedeanClass.mk_mul, mk_expTerm, mk_expTerm]
  calc n • ArchimedeanClass.mk (ε + δ)
      ≤ (i + j) • ArchimedeanClass.mk (ε + δ) := nsmul_le_nsmul_left hm0 hn
    _ = i • ArchimedeanClass.mk (ε + δ) + j • ArchimedeanClass.mk (ε + δ) := add_nsmul ..
    _ ≤ i • ArchimedeanClass.mk ε + j • ArchimedeanClass.mk δ :=
        add_le_add (nsmul_le_nsmul_right hmε _) (nsmul_le_nsmul_right hmδ _)

/-! ### Instance II: the Cauchy square of the geometric series -/

/-- The Cauchy square of a geometric series collapses layer by layer:
`Σ_{i+j=n} eⁱ·eʲ = (n+1)·eⁿ`. -/
theorem cauchyMul_geometric_self (e : Surreal) (n : ℕ) :
    cauchyMul (fun k ↦ e ^ k) (fun k ↦ e ^ k) n = ((n : Surreal) + 1) * e ^ n := by
  have h : ∀ p ∈ Finset.antidiagonal n,
      (fun k ↦ e ^ k) p.1 * (fun k ↦ e ^ k) p.2 = e ^ n := by
    rintro ⟨i, j⟩ hp
    dsimp only
    rw [← pow_add, Finset.mem_antidiagonal.1 hp]
  rw [cauchyMul, Finset.sum_congr rfl h, Finset.sum_const, Finset.Nat.card_antidiagonal,
    nsmul_eq_mul]
  push_cast
  ring

private theorem mk_natCast_add_one (n : ℕ) :
    ArchimedeanClass.mk ((n : Surreal) + 1) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [show ((n : Surreal) + 1) = (((n + 1 : ℕ)) : Surreal) by push_cast; ring,
    ArchimedeanClass.stdPart_natCast]
  exact_mod_cast n.succ_ne_zero

/-- **The geometric square sums**: the Cauchy square of the geometric series `Σ ω⁻ᵏ` is
`Σ_{n<ω} (n+1)·ω⁻ⁿ`, and it has Hahn sum `((1 − ω⁻¹)⁻¹)² = (ω/(ω−1))²` — a genuinely new
instance produced by the general theorem with zero additional analytic work. -/
theorem isHahnSum_geometric_sq :
    IsHahnSum (fun n : ℕ ↦ ((n : Surreal) + 1) * eps0 ^ n) ((1 - eps0)⁻¹ ^ 2) := by
  have he : Infinitesimal eps0 := by
    rw [eps0_def]
    exact infinitesimal_inv_wpow one_pos
  have hfun : (fun n : ℕ ↦ ((n : Surreal) + 1) * eps0 ^ n) =
      cauchyMul (fun k ↦ eps0 ^ k) (fun k ↦ eps0 ^ k) :=
    funext fun n ↦ (cauchyMul_geometric_self eps0 n).symm
  rw [hfun]
  refine isHahnSum_geometric.sq ?_
  intro n i j hn
  rw [cauchyMul_geometric_self]
  rw [ArchimedeanClass.mk_mul, mk_natCast_add_one, zero_add, ArchimedeanClass.mk_mul,
    ArchimedeanClass.mk_pow, ArchimedeanClass.mk_pow, ArchimedeanClass.mk_pow, ← add_nsmul]
  exact nsmul_le_nsmul_left he.le hn

end Surreal
