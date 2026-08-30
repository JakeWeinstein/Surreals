import Infinity.BirthdayHahn
import Infinity.CauchyProduct
import Mathlib.Data.Nat.Pairing

/-!
# Surreal expected utility: impossibility, underdetermination, and the canonical expectation

This file begins a machine-checked foundation for **surreal-valued probability and expected
utility**, the framework proposed in the philosophy literature by Chen–Rubio (*Surreal
Decisions*, PPR 2020) and Gallow (*Surreal Probabilities*) as the mathematics of transfinite
decision theory. Chen–Rubio prove a surreal von Neumann–Morgenstern theorem for **finite**
state spaces and explicitly defer infinite state spaces to "ongoing research in surreal
analysis" — the missing ingredient being a theory of surreal infinite summation. That theory
is exactly what this repository provides (`IsHahnSum`, `exists_isHahnSum`, `hahnSum`), and
this file connects it to expected utility.

A countable **lottery** is a pair of sequences: probability weights `p : ℕ → Surreal` and
outcome utilities `u : ℕ → Surreal`. Its `expectationSeries` is `n ↦ p n * u n`, and a
surreal `x` is a *domination-consistent expected utility* of the lottery when
`IsHahnSum (expectationSeries p u) x` — every residual `x - (partial expected utility)` is
dominated by the first omitted term. Three pillars are proved here, each answering a claim
in the philosophical literature:

## Pillar I — no limit-based expectation exists

* `not_tendstoSurreal_partialSum_expectation` : for any lottery with infinitely many
  relevant outcomes (all `p n ≠ 0`, `u n ≠ 0`), the partial expected utilities converge to
  **no** surreal whatsoever. Expected utility over infinitely many outcomes cannot be a
  limit on `No`; approximation semantics is impossible, not merely inconvenient. (This is
  the eventual-constancy obstruction of `Infinity.Limits` applied to decision theory.)

## Pillar II — underdetermination, made precise (Pruss's objection as a theorem)

Pruss (*Underdetermination of infinitesimal probabilities*, Synthese 2021) argues that
infinitesimal-valued expectations are objectionably arbitrary: any assignment can be
replaced by another with "all the same intuitive features". On the surreals, with domination
semantics, that phenomenon is a theorem — and it is *exactly measurable*:

* `isHahnSum_iff_forall_mk_le` : **the halo characterization** — given one consistent value
  `x`, the consistent values are exactly `x + w` for perturbations `w` dominated by every
  term of the series. The solution set is a coset of the tail-halo subgroup.
* `IsHahnSum.add_halo` : the replacement construction itself (Pruss's move, verified).
* `exists_pos_forall_mk_lt` : the tail-halo is nontrivial — by countable coinitiality there
  is a positive surreal below every scale the series can name.
* `exists_isHahnSum_ne` : hence **every** strictly dominating expectation series has at
  least two (in fact a proper class of) domination-consistent values. Underdetermination is
  universal, not pathological.
* `exists_isHahnSum_ne_hahnSum` : the sharpened form — a non-canonical consistent value
  always exists, and it is **strictly more complex** (strictly larger birthday) than the
  canonical value `hahnSum`. Together with `hahnSum_eq_iff` and
  `omega0_le_birthday_sub_of_isHahnSum` (in `Infinity.BirthdayHahn`), this is the formal
  answer to the underdetermination objection: the constraints do underdetermine the value,
  but the solution set carries a canonical, definable, birthday-minimal representative, and
  every rival differs from it by an element born no earlier than day `ω`.

## Pillar III — properties of consistent expectations

* `stdPart_eq_of_isHahnSum` : **agreement with classical expectation** — once the series
  reaches infinitesimal scale at index `k`, the standard part of every consistent expected
  utility equals the standard part of the `k`-th partial expected utility. The real-valued
  shadow of surreal expected utility is classical finite expected utility.
* `pos_of_isHahnSum` : **the dominance principle at the leading scale** — if the dominant
  term of the expectation series is positive, every consistent expected utility is
  positive. (The sign of an expectation is decided by its most significant stake.)
* `lt_of_isHahnSum_of_head_lt` : **a comparison/dominance theorem** — improving the
  dominant term by more than either tail's scale strictly improves every consistent
  expectation. This is the pattern of Chen–Rubio's dominance verdicts (`G₂ > G₁`), proved
  at infinite-state scope.
* `IsHahnSum.const_mul`, `strict_dominating_const_mul` : rescaling laws (stakes and
  probabilities scale linearly at the level of consistent values).

## The honest boundary — the flat (St. Petersburg) collapse

Domination semantics requires genuinely dominating terms. When the expectation series is
Archimedean-flat, the constraints degenerate:

* `isHahnSum_one_iff` : for the constant series `1, 1, 1, …` — the expectation series of
  the St. Petersburg game, where `(1/2ⁿ)·2ⁿ = 1` — the domination-consistent values are
  **exactly the finite surreals**: an entire Archimedean galaxy. The constraint set is not
  a halo but a galaxy, and simplicity-selection over it would return `0`, ignoring the
  series entirely. This is why the canonical expectation is defined only for strictly
  dominating series: the restriction marks a real semantic boundary, not a convenience.
  (See `Infinity.PascalWager` for a fully surreal St. Petersburg instance with infinitesimal
  probabilities and transfinite payoffs that still collapses.)
-/

open ArchimedeanClass Filter Finset

noncomputable section

namespace Surreal

variable {t u : ℕ → Surreal} {x y w : Surreal}

/-! ### Lotteries and expectation series -/

/-- The **expectation series** of a countable lottery with probability weights `p` and
outcome utilities `u`: the `n`-th term is the probability-weighted utility `p n * u n`, so
the `n`-th partial sum is the expected utility of the first `n` outcomes. -/
def expectationSeries (p u : ℕ → Surreal) : ℕ → Surreal :=
  fun n ↦ p n * u n

@[simp]
theorem expectationSeries_apply (p u : ℕ → Surreal) (n : ℕ) :
    expectationSeries p u n = p n * u n :=
  rfl

/-! ### Pillar I: no limit-based expected utility -/

/-- **No limit-based expectation exists.** For a lottery with infinitely many relevant
outcomes — every probability weight and every utility nonzero — the sequence of partial
expected utilities converges to no surreal number at all. Expected utility over a countable
state space cannot be defined by approximation on `No`. -/
theorem not_tendstoSurreal_partialSum_expectation {p u : ℕ → Surreal}
    (hp : ∀ n, p n ≠ 0) (hu : ∀ n, u n ≠ 0) (y : Surreal) :
    ¬ TendstoSurreal (partialSum (expectationSeries p u)) atTop y :=
  not_tendstoSurreal_partialSum (fun n ↦ mul_ne_zero (hp n) (hu n)) y

/-! ### Pillar II: underdetermination, made precise -/

/-- **The halo characterization of consistent values**: given one Hahn sum `x` of a series,
a surreal `y` is a Hahn sum iff the difference `y - x` is dominated by every term. The set
of domination-consistent values is exactly the coset `x + {w | ∀ n, mk (t n) ≤ mk w}` of
the series' tail-halo. -/
theorem isHahnSum_iff_forall_mk_le (hx : IsHahnSum t x) :
    IsHahnSum t y ↔ ∀ n, ArchimedeanClass.mk (t n) ≤ ArchimedeanClass.mk (y - x) := by
  constructor
  · intro hy n
    exact IsHahnSum.mk_sub_le hy hx n
  · intro h n
    have hsplit : y - partialSum t n = (y - x) + (x - partialSum t n) := by ring
    show ArchimedeanClass.mk (t n) ≤ ArchimedeanClass.mk (y - partialSum t n)
    rw [hsplit]
    exact le_trans (le_min (h n) (hx n)) (ArchimedeanClass.min_le_mk_add ..)

/-- **The resolution of domination semantics is the finest attained scale**: if every term
of the series has magnitude at least scale `c` (class at most `c`) and some term sits
exactly at scale `c`, then the consistent values are exactly `x + {w | c ≤ mk w}` — the
full ball of magnitudes at most scale `c`. In the Archimedean-flat regime the
underdetermination is thus galaxy-sized, not halo-sized: the special case `c = 0` is the
St. Petersburg collapse `isHahnSum_one_iff` below. -/
theorem isHahnSum_iff_of_le_of_attained {c : ArchimedeanClass Surreal}
    (hle : ∀ n, ArchimedeanClass.mk (t n) ≤ c) (hex : ∃ n, ArchimedeanClass.mk (t n) = c)
    (hx : IsHahnSum t x) :
    IsHahnSum t y ↔ c ≤ ArchimedeanClass.mk (y - x) := by
  rw [isHahnSum_iff_forall_mk_le hx]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := hex
    exact hn ▸ h n
  · intro h n
    exact (hle n).trans h

/-- **Finite lotteries are fully determined**: if some outcome has probability zero — in
particular, if only finitely many outcomes are live — then any two domination-consistent
expected utilities coincide (both equal the partial expected utility at that outcome, by
`IsHahnSum.eq_partialSum_of_apply_eq_zero`). Surreal expected utility is a conservative
extension of classical finite expected utility, and underdetermination is strictly an
infinite-lottery phenomenon. -/
theorem eq_of_isHahnSum_expectation_of_prob_zero {p u : ℕ → Surreal} {N : ℕ}
    (h0 : p N = 0) {x y : Surreal} (hx : IsHahnSum (expectationSeries p u) x)
    (hy : IsHahnSum (expectationSeries p u) y) : x = y := by
  have hz : expectationSeries p u N = 0 := by rw [expectationSeries_apply, h0, zero_mul]
  rw [hx.eq_partialSum_of_apply_eq_zero hz, hy.eq_partialSum_of_apply_eq_zero hz]

/-- **The replacement construction** (Pruss's underdetermination move, verified): perturbing
a consistent value by anything dominated by every term of the series yields another
consistent value with all the same domination features. -/
theorem IsHahnSum.add_halo (hx : IsHahnSum t x)
    (hw : ∀ n, ArchimedeanClass.mk (t n) ≤ ArchimedeanClass.mk w) :
    IsHahnSum t (x + w) := by
  refine (isHahnSum_iff_forall_mk_le hx).2 fun n ↦ ?_
  rw [add_sub_cancel_left]
  exact hw n

/-- **The tail-halo is never trivial**: below the scales of any series of nonzero terms sits
a positive surreal dominated by every one of them — by countable coinitiality
(`exists_pos_forall_lt`), applied to the doubly-indexed family `|t n| / (k + 1)`. -/
theorem exists_pos_forall_mk_lt (ht : ∀ n, t n ≠ 0) :
    ∃ w : Surreal, 0 < w ∧
      ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk w := by
  obtain ⟨w, hw0, hw⟩ := exists_pos_forall_lt
    (z := fun m ↦ |t m.unpair.1| / ((m.unpair.2 + 1 : ℕ) : Surreal))
    (fun m ↦ div_pos (abs_pos.2 (ht _)) (by exact_mod_cast Nat.succ_pos _))
  refine ⟨w, hw0, fun n ↦ ?_⟩
  rw [ArchimedeanClass.mk_lt_mk]
  intro j
  rw [abs_of_pos hw0]
  obtain rfl | hj := Nat.eq_zero_or_pos j
  · simpa using abs_pos.2 (ht n)
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, (Nat.succ_pred_eq_of_pos hj).symm⟩
    have h := hw (Nat.pair n k)
    rw [Nat.unpair_pair] at h
    dsimp only at h
    have hpos : (0 : Surreal) < ((k + 1 : ℕ) : Surreal) := by
      exact_mod_cast Nat.succ_pos k
    rw [lt_div_iff₀ hpos] at h
    calc (k + 1) • w = w * ((k + 1 : ℕ) : Surreal) := by
          rw [nsmul_eq_mul]; ring
      _ < |t n| := h

/-- **Underdetermination is universal**: every strictly dominating expectation series has at
least two distinct domination-consistent values. The constraints never single out the
expected utility on their own. -/
theorem exists_isHahnSum_ne
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    ∃ x y, IsHahnSum t x ∧ IsHahnSum t y ∧ x ≠ y := by
  obtain ⟨x, hx⟩ := exists_isHahnSum ht
  obtain ⟨w, hw0, hw⟩ := exists_pos_forall_mk_lt (ne_zero_of_strict_dominating ht)
  refine ⟨x, x + w, hx, hx.add_halo fun n ↦ (hw n).le, fun h ↦ ?_⟩
  exact hw0.ne' (by linarith [h.le, h.ge])

/-- **Underdetermination answered**: a rival to the canonical expected utility always
exists — and every rival is strictly more complex than the canonical value. The
constraints underdetermine the value (Pruss's objection), but birthday-minimality is a
principled selection: the canonical value is simplest, uniquely so
(`hahnSum_eq_iff`), and each alternative pays a strict complexity price. -/
theorem exists_isHahnSum_ne_hahnSum
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) :
    ∃ y, IsHahnSum t y ∧ y ≠ hahnSum ht ∧
      (hahnSum ht).birthday < y.birthday := by
  obtain ⟨w, hw0, hw⟩ := exists_pos_forall_mk_lt (ne_zero_of_strict_dominating ht)
  have hy : IsHahnSum t (hahnSum ht + w) :=
    (isHahnSum_hahnSum ht).add_halo fun n ↦ (hw n).le
  have hne : hahnSum ht + w ≠ hahnSum ht := fun h ↦ hw0.ne' (by linarith [h.le, h.ge])
  exact ⟨hahnSum ht + w, hy, hne, birthday_hahnSum_lt_of_ne ht hy hne⟩

/-! ### Pillar III: properties of consistent expected utilities -/

/-- **Agreement with classical expectation**: once the expectation series reaches
infinitesimal scale at index `k`, the standard part of every consistent expected utility is
the standard part of the `k`-th partial expected utility. Classical finite expected utility
is the real shadow of surreal expected utility. -/
theorem stdPart_eq_of_isHahnSum (hx : IsHahnSum t x) {k : ℕ}
    (hk : 0 < ArchimedeanClass.mk (t k)) :
    stdPart x = stdPart (partialSum t k) := by
  have hres : Infinitesimal (x - partialSum t k) := lt_of_lt_of_le hk (hx k)
  have hsplit : x = partialSum t k + (x - partialSum t k) := by ring
  rw [hsplit, stdPart_add_eq_left hres]

/-- **The dominance principle at the leading scale**: if the dominant (first) term of the
expectation series is positive and strictly dominates the second, then every consistent
expected utility is positive. The sign of the expectation is the sign of the most
significant stake. -/
theorem pos_of_isHahnSum (hx : IsHahnSum t x)
    (h01 : ArchimedeanClass.mk (t 0) < ArchimedeanClass.mk (t 1)) (h0 : 0 < t 0) :
    0 < x := by
  have h1 : ArchimedeanClass.mk (t 0) < ArchimedeanClass.mk (x - partialSum t 1) :=
    h01.trans_le (hx 1)
  have habs : |x - partialSum t 1| < |t 0| := abs_lt_abs_of_mk_lt h1
  rw [partialSum, Finset.sum_range_one, abs_of_pos h0] at habs
  have h2 := (abs_lt.1 habs).1
  linarith

/-- **A dominance comparison theorem**: if two expectation series have heads `t 0 < u 0`
whose difference strictly dominates both tails, then every consistent value of the first
lottery is strictly below every consistent value of the second. Improving the dominant
outcome by more than the tail scales strictly improves the expectation — Chen–Rubio's
dominance verdicts, at infinite-state scope. -/
theorem lt_of_isHahnSum_of_head_lt (hx : IsHahnSum t x) (hy : IsHahnSum u y)
    (hlt : t 0 < u 0)
    (h1 : ArchimedeanClass.mk (u 0 - t 0) < ArchimedeanClass.mk (t 1))
    (h2 : ArchimedeanClass.mk (u 0 - t 0) < ArchimedeanClass.mk (u 1)) :
    x < y := by
  have hxr := hx 1
  have hyr := hy 1
  rw [partialSum, Finset.sum_range_one] at hxr hyr
  have hr : ArchimedeanClass.mk (u 0 - t 0) <
      ArchimedeanClass.mk ((y - u 0) + -(x - t 0)) := by
    refine lt_of_lt_of_le (lt_min (h2.trans_le hyr) ?_) (ArchimedeanClass.min_le_mk_add ..)
    rw [ArchimedeanClass.mk_neg]
    exact h1.trans_le hxr
  have habs := abs_lt.1 (abs_lt_abs_of_mk_lt hr)
  rw [abs_of_pos (sub_pos.2 hlt)] at habs
  have hyx : y - x = (u 0 - t 0) + ((y - u 0) + -(x - t 0)) := by ring
  have h3 := habs.1
  linarith

/-! #### Rescaling laws -/

private theorem partialSum_const_mul (c : Surreal) (t : ℕ → Surreal) (n : ℕ) :
    partialSum (fun k ↦ c * t k) n = c * partialSum t n := by
  simp [partialSum, Finset.mul_sum]

/-- Consistent expected utilities rescale: if `x` sums the series `t`, then `c * x` sums
the rescaled series `c * t`. (Rescaling all stakes, or a common factor of all probability
weights, rescales the expectation.) -/
private theorem IsHahnSum.const_mul (hx : IsHahnSum t x) (c : Surreal) :
    IsHahnSum (fun n ↦ c * t n) (c * x) := by
  intro n
  show ArchimedeanClass.mk (c * t n) ≤ _
  rw [partialSum_const_mul, ← mul_sub, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul]
  exact add_le_add le_rfl (hx n)

/-- Multiplication by a nonzero constant preserves strict domination of Archimedean
classes. -/
theorem mk_mul_lt_mk_mul_left {c a b : Surreal} (hc : c ≠ 0)
    (h : ArchimedeanClass.mk a < ArchimedeanClass.mk b) :
    ArchimedeanClass.mk (c * a) < ArchimedeanClass.mk (c * b) := by
  rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul]
  refine lt_of_le_of_ne (add_le_add le_rfl h.le) fun heq ↦ h.ne ?_
  exact ArchimedeanClass.add_left_cancel_of_ne_top
    (by simpa [ArchimedeanClass.mk_eq_top_iff] using hc) heq

/-- Rescaling by a nonzero constant preserves strict domination of a series. -/
theorem strict_dominating_const_mul {c : Surreal} (hc : c ≠ 0)
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))) (n : ℕ) :
    ArchimedeanClass.mk (c * t n) < ArchimedeanClass.mk (c * t (n + 1)) :=
  mk_mul_lt_mk_mul_left hc (ht n)

/-! ### The honest boundary: the flat (St. Petersburg) collapse -/

theorem partialSum_one (n : ℕ) : partialSum (fun _ ↦ (1 : Surreal)) n = n := by
  simp [partialSum]

/-- **The St. Petersburg collapse**: for the constant expectation series `1, 1, 1, …` —
the classical St. Petersburg game, whose `n`-th probability-weighted payoff is
`(1/2ⁿ)·2ⁿ = 1` — the domination-consistent values are exactly the finite surreals. The
constraint set is an entire Archimedean galaxy rather than a halo: domination semantics
degenerates on Archimedean-flat series, and no principled canonical expectation exists at
this scope. This theorem marks the honest boundary of the theory. -/
theorem isHahnSum_one_iff :
    IsHahnSum (fun _ ↦ (1 : Surreal)) x ↔ IsFinite x := by
  constructor
  · intro h
    have h0 := h 0
    rw [partialSum_zero, sub_zero] at h0
    rw [isFinite_def]
    simpa [ArchimedeanClass.mk_one] using h0
  · intro hx n
    show ArchimedeanClass.mk (1 : Surreal) ≤ _
    rw [partialSum_one, ArchimedeanClass.mk_one]
    exact hx.sub (ArchimedeanClass.mk_natCast_nonneg n)

end Surreal

end
