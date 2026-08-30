import Infinity.TransfiniteSum
import Infinity.OrdinalSum
import Infinity.BirthdayHahn
import CombinatorialGames.Surreal.HahnSeries.Basic

/-!
# Toward Conway normal form: `ω + ω` compatibility, ω-power series, and Hahn-series evaluation

`Infinity.TransfiniteSum` proved the Transfinite Summation Theorem: every strictly
dominating series of any ordinal length has a canonical Hahn sum `hahnSumO`. This file
harvests it in three directions.

**1. Length `ω + ω`: agreement with `Infinity.OrdinalSum`, and canonicity settled.**
`isHahnSumO_omega0_add_omega0_iff` shows that at length `ω + ω` the transfinite predicate
`IsHahnSumO` coincides exactly with the hand-built `IsHahnSum₂` (under strict domination,
which supplies the separation hypothesis). Consequently:

* `hahnSumO t (ω + ω)` *is* an `ω + ω` sum (`isHahnSum₂_hahnSumO`), and it is the
  **birthday-minimal** one (`birthday_hahnSumO_le_of_isHahnSum₂`) — settling in the
  reframed sense the canonicity question `Infinity.OrdinalSum` left open: a canonical
  (birthday-minimal) `ω + ω` sum *exists* and the recursion computes it.
* Whether the compositional `hahnSum₂ = hahnSum + hahnSum` equals it is *exactly* the
  translation-invariance question: `hahnSumO_eq_hahnSum₂_iff` reduces the identity to
  birthday-minimality of `hahnSum₂`, the sharpest currently-provable form.

**2. The ω-power payoff** (`exists_isHahnSumO_omegaPowSeries`): every series
`Σ_{β<α} r_β · ω^(y_β)` with strictly decreasing surreal exponents and nonzero real
coefficients — an arbitrary "base-`ω` expansion" of any ordinal length — is strictly
dominating and hence denotes a surreal number, canonically. This is the existence half of
Conway normal form at the level of *values*: every normal-form expression names a surreal,
kernel-checked.

**3. Evaluation of the library's Hahn series** (`Surreal.evalHahn`): the maintainer's
`SurrealHahnSeries` (ordinal-indexed exponent/coefficient data with no evaluation map yet)
evaluates: its term sequence is strictly dominating (`SurrealHahnSeries.isStrictDom_term`),
so `evalHahn x := hahnSumO x.term x.length` is a genuine evaluation map
`SurrealHahnSeries → Surreal` satisfying the domination-residual semantics at every stage
(`isHahnSumO_evalHahn`), birthday-minimal at limit lengths (`birthday_evalHahn_le`).

**The future bridge** (for when upstream evaluation lands in
`CombinatorialGames.Surreal.HahnSeries`): to identify vihdzp's evaluation map with
`evalHahn`, it suffices to show their map is an `IsHahnSumO` of the term sequence — its
residuals against truncations should be dominated by the first omitted term, which is how
Hahn-series arithmetic behaves by construction — and then either (a) birthday-minimality
of their map at limit lengths, or (b) an exactness argument at successor stages, pins the
two maps equal via `IsHahnSumO.mk_sub_le` + `hahnSumO_eq_iff`. A second bridge point:
`(x.truncIdx i).term` agrees with `x.term` below `i`, so by `hahnSumO_congr` evaluation of
truncations should compute the canonical partial sums `hahnSumO x.term i` — "truncation =
partial sum".

**What remains for full Conway normal form** (the honest map): (i) *termination of
leading-term extraction* — iterating `x ↦ x - x.leadingTerm` (strictly finer at each step
by the library's `mk_lt_mk_sub_leadingTerm`, and through limits by the residual calculus
here) must reach `0` at some set-sized ordinal; classically this uses the smallness of the
support, which is exactly the Hahn-series representation theorem being built upstream.
(ii) *Uniqueness of representation* — distinct series have distinct sums (injectivity of
`evalHahn`), for which the leading-scale calculus (`Surreal/Leading`) is the tool.
Both are mapped, neither is attempted here. The informal mathematics is Conway
(ONAG ch. 3) and Gonshor (ch. 5); Mizar has a formalization of Conway normal form by a
different (sign-expansion) route; the theorems here are, to our knowledge, the first
formalization of transfinite Hahn-sum evaluation semantics in any prover.
-/

open ArchimedeanClass Order

universe u

noncomputable section

namespace Surreal

/-! ### The general characterization of canonical sums at limit lengths -/

/-- **The characterization of the canonical transfinite sum at limit lengths**: provided
some Hahn sum exists, `hahnSumO t γ = z` iff `z` is a Hahn sum of minimal birthday. The
transfinite generalization of `hahnSum_eq_iff`. -/
theorem hahnSumO_eq_iff {t : Ordinal.{u} → Surreal.{u}} {γ : Ordinal.{u}}
    (hγ : IsSuccLimit γ) (ht0 : ∀ β < γ, t β ≠ 0) (hex : ∃ w, IsHahnSumO t γ w)
    {z : Surreal.{u}} :
    hahnSumO t γ = z ↔
      IsHahnSumO t γ z ∧ ∀ w, IsHahnSumO t γ w → z.birthday ≤ w.birthday := by
  obtain ⟨w₀, hw₀⟩ := hex
  have hlt := ((fits_sumO_iff ht0).2 hw₀).lt
  rw [hahnSumO_of_isSuccLimit t hγ, simplestBtwnD_of_lt hlt, Cut.simplestBtwn_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(fits_sumO_iff ht0).1 h1, fun w hw ↦ h2 w ((fits_sumO_iff ht0).2 hw)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(fits_sumO_iff ht0).2 h1, fun w hw ↦ h2 w ((fits_sumO_iff ht0).1 hw)⟩

/-! ### Length `ω + ω`: agreement with `Infinity.OrdinalSum` -/

section OmegaPlusOmega

variable {t : Ordinal.{u} → Surreal.{u}}

/-- `ω + ω` is a limit ordinal. -/
private theorem isSuccLimit_omega0_add_omega0 :
    IsSuccLimit (Ordinal.omega0 + Ordinal.omega0) :=
  Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0

/-- Strict domination below `ω + ω` restricts to the strictly dominating fine block
`k ↦ t (ω + k)`. -/
theorem IsStrictDom.fine_natCast_succ
    (ht : IsStrictDom t (Ordinal.omega0 + Ordinal.omega0)) (n : ℕ) :
    ArchimedeanClass.mk ((fun k : ℕ ↦ t (Ordinal.omega0 + k)) n) <
      ArchimedeanClass.mk ((fun k : ℕ ↦ t (Ordinal.omega0 + k)) (n + 1)) := by
  refine ht (add_lt_add_right ?_ _) (add_lt_add_right (Ordinal.natCast_lt_omega0 _) _)
  rw [Nat.cast_add_one]
  exact lt_add_one_iff.2 le_rfl

/-- **Separation**: below `ω + ω`, every fine term is strictly finer than every coarse
term — the `hsep` hypothesis of `Infinity.OrdinalSum`, for free from strict domination. -/
theorem IsStrictDom.coarse_fine_sep
    (ht : IsStrictDom t (Ordinal.omega0 + Ordinal.omega0)) (m n : ℕ) :
    ArchimedeanClass.mk ((fun k : ℕ ↦ t k) m) <
      ArchimedeanClass.mk ((fun k : ℕ ↦ t (Ordinal.omega0 + k)) n) :=
  ht ((Ordinal.natCast_lt_omega0 m).trans_le (le_self_add))
    (add_lt_add_right (Ordinal.natCast_lt_omega0 n) _)

/-- The canonical partial sums at stages `ω + n`: the canonical coarse sum plus the finite
partial sums of the fine block — the transfinite recursion recovers the two-block
structure of `Infinity.OrdinalSum` exactly. -/
theorem hahnSumO_omega0_add_natCast
    (ht : IsStrictDom t (Ordinal.omega0 + Ordinal.omega0)) (n : ℕ) :
    hahnSumO t (Ordinal.omega0 + n) =
      hahnSum (ht.natCast_succ (le_self_add)) +
        partialSum (fun k ↦ t (Ordinal.omega0 + k)) n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, add_zero, partialSum_zero, add_zero,
      hahnSumO_omega0 (ht.mono (le_self_add))]
  | succ n ih =>
    rw [Nat.cast_add_one, ← add_assoc, hahnSumO_add_one, ih, partialSum_succ]
    ring

/-- **`IsHahnSumO` at `ω + ω` is `IsHahnSum₂`**: under strict domination, the transfinite
summation predicate coincides with the hand-built two-block predicate of
`Infinity.OrdinalSum`. Forward: project the fine-stage conditions. Backward: the fine
conditions are definitional, and the coarse conditions follow from the compatibility
theorem `IsHahnSum₂.isHahnSum_coarse` via separation. -/
theorem isHahnSumO_omega0_add_omega0_iff
    (ht : IsStrictDom t (Ordinal.omega0 + Ordinal.omega0)) {x : Surreal.{u}} :
    IsHahnSumO t (Ordinal.omega0 + Ordinal.omega0) x ↔
      IsHahnSum₂ (ht.natCast_succ (le_self_add))
        (fun k ↦ t (Ordinal.omega0 + k)) x := by
  constructor
  · intro h n
    have h1 := h (Ordinal.omega0 + n)
      (add_lt_add_right (Ordinal.natCast_lt_omega0 n) _)
    rw [hahnSumO_omega0_add_natCast ht n] at h1
    have heq : x - (hahnSum (ht.natCast_succ (le_self_add)) +
        partialSum (fun k ↦ t (Ordinal.omega0 + k)) n) =
        (x - hahnSum (ht.natCast_succ (le_self_add))) -
          partialSum (fun k ↦ t (Ordinal.omega0 + k)) n := by
      ring
    rw [heq] at h1
    exact h1
  · intro h β hβ
    rcases lt_or_ge β Ordinal.omega0 with hβω | hωβ
    · have hcoarse : IsHahnSum (fun n : ℕ ↦ t n) x :=
        IsHahnSum₂.isHahnSum_coarse ht.coarse_fine_sep h
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hβω
      rw [hahnSumO_natCast]
      exact hcoarse n
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, β = Ordinal.omega0 + n := by
        obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1
          (Ordinal.sub_lt_of_lt_add hβ Ordinal.omega0_pos)
        exact ⟨n, by rw [← hn, Ordinal.add_sub_cancel_of_le hωβ]⟩
      rw [hahnSumO_omega0_add_natCast ht n]
      have h1 := h.isHahnSum_fine n
      have heq : x - hahnSum (ht.natCast_succ (le_self_add)) -
          partialSum (fun k ↦ t (Ordinal.omega0 + k)) n =
          x - (hahnSum (ht.natCast_succ (le_self_add)) +
            partialSum (fun k ↦ t (Ordinal.omega0 + k)) n) := by
        ring
      rw [heq] at h1
      exact h1

/-- The canonical arbitrary-length sum at `ω + ω` is an `ω + ω` sum in the sense of
`Infinity.OrdinalSum`. -/
theorem isHahnSum₂_hahnSumO (ht : IsStrictDom t (Ordinal.omega0 + Ordinal.omega0)) :
    IsHahnSum₂ (ht.natCast_succ (le_self_add))
      (fun k ↦ t (Ordinal.omega0 + k)) (hahnSumO t (Ordinal.omega0 + Ordinal.omega0)) :=
  (isHahnSumO_omega0_add_omega0_iff ht).1 (isHahnSumO_hahnSumO ht)

/-- **Canonicity at `ω + ω`, settled**: the canonical arbitrary-length sum is
birthday-minimal among *all* `ω + ω` sums. `Infinity.OrdinalSum` left open whether a
birthday-minimal `ω + ω` sum can be canonically chosen; the transfinite recursion chooses
it. -/
theorem birthday_hahnSumO_le_of_isHahnSum₂
    (ht : IsStrictDom t (Ordinal.omega0 + Ordinal.omega0)) {z : Surreal.{u}}
    (hz : IsHahnSum₂ (ht.natCast_succ (le_self_add))
      (fun k ↦ t (Ordinal.omega0 + k)) z) :
    (hahnSumO t (Ordinal.omega0 + Ordinal.omega0)).birthday ≤ z.birthday :=
  birthday_hahnSumO_le isSuccLimit_omega0_add_omega0
    (ht.ne_zero_of_isSuccLimit isSuccLimit_omega0_add_omega0)
    ((isHahnSumO_omega0_add_omega0_iff ht).2 hz)

/-- The canonical arbitrary-length sum is at least as simple as the compositional
`hahnSum₂`. -/
theorem birthday_hahnSumO_le_hahnSum₂
    (ht : IsStrictDom t (Ordinal.omega0 + Ordinal.omega0)) :
    (hahnSumO t (Ordinal.omega0 + Ordinal.omega0)).birthday ≤
      (hahnSum₂ (ht.natCast_succ (le_self_add))
        ht.fine_natCast_succ).birthday :=
  birthday_hahnSumO_le_of_isHahnSum₂ ht
    (isHahnSum₂_hahnSum₂ (ht.natCast_succ (le_self_add))
      ht.fine_natCast_succ)

/-- **The translation question, isolated**: the canonical arbitrary-length sum at `ω + ω`
equals the compositional `hahnSum₂ = hahnSum + hahnSum` **iff** `hahnSum₂` is
birthday-minimal among `ω + ω` sums — precisely the (open) translation-equivariance
question discussed in `Infinity.OrdinalSum`. Either way the minimal sum now exists; what
is open is only whether the compositional formula computes it. -/
theorem hahnSumO_eq_hahnSum₂_iff
    (ht : IsStrictDom t (Ordinal.omega0 + Ordinal.omega0)) :
    hahnSumO t (Ordinal.omega0 + Ordinal.omega0) =
        hahnSum₂ (ht.natCast_succ (le_self_add)) ht.fine_natCast_succ ↔
      ∀ z, IsHahnSum₂ (ht.natCast_succ (le_self_add))
          (fun k ↦ t (Ordinal.omega0 + k)) z →
        (hahnSum₂ (ht.natCast_succ (le_self_add))
          ht.fine_natCast_succ).birthday ≤ z.birthday := by
  rw [hahnSumO_eq_iff isSuccLimit_omega0_add_omega0
    (ht.ne_zero_of_isSuccLimit isSuccLimit_omega0_add_omega0)
    ⟨_, isHahnSumO_hahnSumO ht⟩]
  constructor
  · rintro ⟨-, hmin⟩ z hz
    exact hmin z ((isHahnSumO_omega0_add_omega0_iff ht).2 hz)
  · intro hmin
    exact ⟨(isHahnSumO_omega0_add_omega0_iff ht).2
        (isHahnSum₂_hahnSum₂ _ ht.fine_natCast_succ),
      fun w hw ↦ hmin w ((isHahnSumO_omega0_add_omega0_iff ht).1 hw)⟩

end OmegaPlusOmega

/-! ### The ω-power payoff: arbitrary-length base-`ω` expansions denote surreals -/

/-- A series `β ↦ r_β · ω^(y_β)` with strictly decreasing surreal exponents and nonzero
real coefficients is strictly dominating: the scale of a term is the class of its
`ω`-power, and `mk ∘ (ω^ ·)` is strictly antitone. -/
theorem isStrictDom_omegaPow {α : Ordinal.{u}} {y : Ordinal.{u} → Surreal.{u}}
    {r : Ordinal.{u} → ℝ} (hy : ∀ ⦃β γ⦄, β < γ → γ < α → y γ < y β)
    (hr : ∀ β < α, r β ≠ 0) :
    IsStrictDom (fun β ↦ (r β : Surreal.{u}) * ω^ (y β)) α := by
  intro β γ hβγ hγα
  dsimp only
  rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, mk_realCast (hr β (hβγ.trans hγα)),
    mk_realCast (hr γ hγα), zero_add, zero_add]
  exact archimedeanClassMk_wpow_strictAnti (hy hβγ hγα)

/-- **Arbitrary base-`ω` expansions denote surreal numbers**: for every ordinal `α`, every
sequence of strictly decreasing surreal exponents `y_β` and nonzero real coefficients
`r_β` (`β < α`), the series `Σ_{β<α} r_β · ω^(y_β)` has a Hahn sum — canonically, the
value `hahnSumO`. This is the existence of Conway-normal-form *values* at every ordinal
length: every normal-form expression names a surreal number. -/
theorem exists_isHahnSumO_omegaPowSeries {α : Ordinal.{u}} {y : Ordinal.{u} → Surreal.{u}}
    {r : Ordinal.{u} → ℝ} (hy : ∀ ⦃β γ⦄, β < γ → γ < α → y γ < y β)
    (hr : ∀ β < α, r β ≠ 0) :
    ∃ x, IsHahnSumO (fun β ↦ (r β : Surreal.{u}) * ω^ (y β)) α x :=
  exists_isHahnSumO (isStrictDom_omegaPow hy hr)

/-! ### A concrete series of every length: the transfinite geometric series -/

/-- The transfinite geometric series `Σ_{β<α} ω^(−β)` (exponents descending through *all*
the ordinals below `α`, embedded in the surreals) is strictly dominating below every
ordinal. -/
theorem isStrictDom_wpow_neg (α : Ordinal.{u}) :
    IsStrictDom (fun β ↦ ω^ (-(NatOrdinal.of β).toSurreal)) α := by
  intro β γ hβγ _
  exact archimedeanClassMk_wpow_strictAnti
    (neg_lt_neg (NatOrdinal.toSurreal.lt_iff_lt.2 (by simpa using hβγ)))

/-- **A concrete canonical sum of every ordinal length**: for *every* ordinal `α`, the
transfinite geometric series `Σ_{β<α} ω^(−β)` has a canonical Hahn sum. At `α = ω` this
is the flagship geometric series of `Infinity.Series`; beyond it, no instance of any
length existed before. -/
theorem isHahnSumO_wpow_neg (α : Ordinal.{u}) :
    IsHahnSumO (fun β ↦ ω^ (-(NatOrdinal.of β).toSurreal)) α
      (hahnSumO (fun β ↦ ω^ (-(NatOrdinal.of β).toSurreal)) α) :=
  isHahnSumO_hahnSumO (isStrictDom_wpow_neg α)

/-! ### Evaluation of the library's surreal Hahn series -/

/-- The term sequence of a `SurrealHahnSeries` is strictly dominating: exponents strictly
decrease along the enumeration of the support, and coefficients are nonzero below the
length. -/
theorem _root_.SurrealHahnSeries.isStrictDom_term (x : SurrealHahnSeries.{u}) :
    IsStrictDom x.term x.length := by
  intro β γ hβγ hγ
  have hβ : β < x.length := hβγ.trans hγ
  have hrβ : x.coeffIdx β ≠ 0 := fun h ↦
    absurd (SurrealHahnSeries.coeffIdx_eq_zero_iff.1 h) hβ.not_ge
  have hrγ : x.coeffIdx γ ≠ 0 := fun h ↦
    absurd (SurrealHahnSeries.coeffIdx_eq_zero_iff.1 h) hγ.not_ge
  rw [SurrealHahnSeries.term_of_lt hβ, SurrealHahnSeries.term_of_lt hγ,
    ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, mk_realCast hrβ, mk_realCast hrγ,
    zero_add, zero_add]
  refine archimedeanClassMk_wpow_strictAnti ?_
  exact Subtype.coe_lt_coe.2 (SurrealHahnSeries.exp_lt_exp_iff.2 hβγ)

/-- **The evaluation of a surreal Hahn series**: the canonical transfinite sum of its term
sequence. The library (`CombinatorialGames.Surreal.HahnSeries.Basic`) provides the
representation data — `term`, `trunc`, `length` — with no evaluation map yet; the
Transfinite Summation Theorem provides the map. See the module docstring for the bridge to
the upstream evaluation once it lands. -/
def evalHahn (x : SurrealHahnSeries.{u}) : Surreal.{u} :=
  hahnSumO x.term x.length

/-- The evaluation satisfies the domination-residual semantics at every ordinal stage:
`evalHahn x` differs from the canonical stage-`β` partial sum by a quantity dominated by
the first omitted term, for every `β < x.length`. -/
theorem isHahnSumO_evalHahn (x : SurrealHahnSeries.{u}) :
    IsHahnSumO x.term x.length (evalHahn x) :=
  isHahnSumO_hahnSumO x.isStrictDom_term

@[simp]
theorem evalHahn_zero : evalHahn (0 : SurrealHahnSeries.{u}) = 0 := by
  rw [evalHahn, SurrealHahnSeries.length_zero, hahnSumO_zero]

/-- At limit lengths, the evaluation is the birthday-minimal Hahn sum of the series. -/
theorem birthday_evalHahn_le {x : SurrealHahnSeries.{u}} (hlen : IsSuccLimit x.length)
    {z : Surreal.{u}} (hz : IsHahnSumO x.term x.length z) :
    (evalHahn x).birthday ≤ z.birthday :=
  birthday_hahnSumO_le hlen (x.isStrictDom_term.ne_zero_of_isSuccLimit hlen) hz

/-- Any two Hahn sums of a surreal Hahn series agree modulo every term's class — the
uniqueness backing the future bridge theorem to the upstream evaluation map. -/
theorem mk_term_le_mk_sub_evalHahn {x : SurrealHahnSeries.{u}} {z : Surreal.{u}}
    (hz : IsHahnSumO x.term x.length z) {β : Ordinal.{u}} (hβ : β < x.length) :
    ArchimedeanClass.mk (x.term β) ≤ ArchimedeanClass.mk (z - evalHahn x) :=
  IsHahnSumO.mk_sub_le hz (isHahnSumO_evalHahn x) hβ

end Surreal
