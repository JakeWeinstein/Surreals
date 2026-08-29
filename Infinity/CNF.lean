import Infinity.TransfiniteSum
import CombinatorialGames.Surreal.Leading

/-!
# Conway-normal-form extraction: every surreal is a Hahn sum of its leading terms

The missing half of Conway normal form is the *representation* direction: every surreal
should *equal* the canonical sum of some (unique) series `Σ r_β·ω^(y_β)`. The classical
construction (Conway ONAG ch. 3, Gonshor ch. 5) extracts leading terms transfinitely:
subtract the leading term, land at a strictly finer scale, repeat through limits. This
file formalizes the extraction on top of the Transfinite Summation Theorem and proves
everything except termination — which it isolates as a single, precisely stated open
statement.

**Definitions.** By transfinite recursion:

* `cnfRes x β` — the residual of `x` after extracting `β` leading terms: `x` at stage `0`;
  `cnfRes x δ - (cnfRes x δ).leadingTerm` at `δ + 1`; and at a limit stage, `x` minus the
  canonical transfinite sum of the terms extracted so far.
* `cnfTerm x β := (cnfRes x β).leadingTerm` — the `β`-th normal-form term of `x`, a real
  multiple of an `ω`-power by construction (`leadingTerm = leadingCoeff · ω^ wlog`).

**Main theorems.**

* `cnfRes_eq_sub` : `cnfRes x α = x - hahnSumO (cnfTerm x) α` at *every* ordinal — the
  extraction is exact bookkeeping against the canonical partial sums, unconditionally.
* `isHahnSumO_cnfTerm` : **every surreal is a Hahn sum of its leading-term series, of
  every ordinal length, unconditionally** — with the residual's class *exactly* the class
  of the first omitted term (`mk_sub_hahnSumO_cnfTerm`).
* `mk_cnfRes_lt` : while the residuals are nonzero they climb strictly in scale — through
  limit stages as well, by the residual calculus of the summation theorem. Hence
  `cnfTerm_isStrictDom` : the extracted series is strictly dominating while alive.
* `IsCNFLength x α` (the residual dies exactly at `α`) and its harvest:
  `IsCNFLength.eq_hahnSumO` — **if the extraction terminates, `x` *is* the canonical
  transfinite sum of its normal form**, a strictly dominating series of leading terms of
  length exactly `α`; at limit `α` it is moreover the birthday-minimal such sum
  (`IsCNFLength.birthday_le`).
* `isCNFLength_monomial` : monomials `r·ω^y` have normal form of length `1` — the base
  case of the finite theory.

**What remains open — the CNF termination problem.** Full Conway normal form is exactly
the statement `∀ x, ∃ α, cnfRes x α = 0` (every extraction dies at some set-sized stage).
Classically this follows from the smallness of the Hahn-support of a surreal, i.e. from
the full `Surreal ≃ SurrealHahnSeries` representation theorem the library maintainer is
building; the Mizar formalization of Conway normal form reached it through sign-expansion
machinery. Termination is *not* attempted here; every other ingredient of the
representation direction is above, kernel-checked, so termination is now the single
missing statement between this development and full CNF.
-/

open ArchimedeanClass Order

universe u

noncomputable section

namespace Surreal

/-! ### The extraction recursion -/

/-- **The normal-form residual**: what is left of `x` after extracting `β` leading terms.
At a limit stage the extracted terms have no last partial sum, so the residual is taken
against the canonical transfinite sum of the terms extracted so far — the Transfinite
Summation Theorem is what makes the recursion well-posed through limits. -/
def cnfRes (x : Surreal.{u}) (α : Ordinal.{u}) : Surreal.{u} :=
  Ordinal.limitRecOn (motive := fun _ ↦ Surreal.{u}) α x
    (fun _ R ↦ R - R.leadingTerm)
    fun γ _ ih ↦
      x - hahnSumO (fun δ ↦ if h : δ < γ then (ih δ h).leadingTerm else 0) γ

/-- **The `β`-th normal-form term** of `x`: the leading term of the `β`-th residual — by
construction a real multiple of an `ω`-power, `leadingCoeff · ω^ wlog`. -/
def cnfTerm (x : Surreal.{u}) (β : Ordinal.{u}) : Surreal.{u} :=
  (cnfRes x β).leadingTerm

@[simp]
theorem cnfRes_zero (x : Surreal.{u}) : cnfRes x 0 = x :=
  Ordinal.limitRecOn_zero ..

@[simp]
theorem cnfRes_add_one (x : Surreal.{u}) (β : Ordinal.{u}) :
    cnfRes x (β + 1) = cnfRes x β - (cnfRes x β).leadingTerm :=
  Ordinal.limitRecOn_add_one ..

theorem cnfRes_of_isSuccLimit (x : Surreal.{u}) {γ : Ordinal.{u}} (hγ : IsSuccLimit γ) :
    cnfRes x γ =
      x - hahnSumO (fun δ ↦ if _h : δ < γ then (cnfRes x δ).leadingTerm else 0) γ := by
  unfold cnfRes
  rw [Ordinal.limitRecOn_limit _ _ _ _ hγ]

/-- The `β`-th term has exactly the scale of the `β`-th residual. -/
@[simp]
theorem mk_cnfTerm (x : Surreal.{u}) (β : Ordinal.{u}) :
    ArchimedeanClass.mk (cnfTerm x β) = ArchimedeanClass.mk (cnfRes x β) :=
  mk_leadingTerm _

/-! ### The exact bookkeeping identity -/

/-- **The extraction is exact**: at every ordinal stage — zero, successor, or limit — the
residual is `x` minus the canonical transfinite sum of the extracted terms. This is the
identity that turns termination of the extraction into the normal-form representation. -/
theorem cnfRes_eq_sub (x : Surreal.{u}) (α : Ordinal.{u}) :
    cnfRes x α = x - hahnSumO (cnfTerm x) α := by
  induction α using Ordinal.limitRecOn with
  | zero => rw [cnfRes_zero, hahnSumO_zero, sub_zero]
  | add_one δ ih =>
    rw [cnfRes_add_one, hahnSumO_add_one]
    have hterm : (cnfRes x δ).leadingTerm = cnfTerm x δ := rfl
    rw [hterm, ih]
    ring
  | limit γ hγ _ih =>
    rw [cnfRes_of_isSuccLimit x hγ]
    have hcong : hahnSumO (fun δ ↦ if _h : δ < γ then (cnfRes x δ).leadingTerm else 0) γ =
        hahnSumO (cnfTerm x) γ :=
      hahnSumO_congr fun δ hδ ↦ dif_pos hδ
    rw [hcong]

/-! ### Every surreal is a Hahn sum of its leading terms -/

/-- The residual against the canonical stage-`β` partial sum has **exactly** the class of
the first omitted term — the sharp form of the summation conditions, at every ordinal
stage of every surreal, unconditionally. -/
theorem mk_sub_hahnSumO_cnfTerm (x : Surreal.{u}) (β : Ordinal.{u}) :
    ArchimedeanClass.mk (x - hahnSumO (cnfTerm x) β) = ArchimedeanClass.mk (cnfTerm x β) := by
  rw [← cnfRes_eq_sub, mk_cnfTerm]

/-- **Every surreal is a Hahn sum of its leading-term series, at every ordinal length,
unconditionally.** The extraction never leaves the domination bands: this is the
representation direction of Conway normal form, short of termination alone. -/
theorem isHahnSumO_cnfTerm (x : Surreal.{u}) (α : Ordinal.{u}) :
    IsHahnSumO (cnfTerm x) α x := fun β _ ↦
  (mk_sub_hahnSumO_cnfTerm x β).ge

/-! ### The residual scales climb strictly while alive -/

private theorem lt_mk_add' {c : ArchimedeanClass Surreal} {a b : Surreal}
    (ha : c < ArchimedeanClass.mk a) (hb : c < ArchimedeanClass.mk b) :
    c < ArchimedeanClass.mk (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (ArchimedeanClass.min_le_mk_add ..)

private theorem mk_cnfRes_lt_aux (x : Surreal.{u}) (α : Ordinal.{u}) :
    (∀ δ < α, cnfRes x δ ≠ 0) → ∀ β < α,
      ArchimedeanClass.mk (cnfRes x β) < ArchimedeanClass.mk (cnfRes x α) := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro _ β hβ
    exact absurd hβ not_lt_bot
  | add_one δ ih =>
    intro halive β hβ
    have hstep : ArchimedeanClass.mk (cnfRes x δ) <
        ArchimedeanClass.mk (cnfRes x (δ + 1)) := by
      rw [cnfRes_add_one]
      exact mk_lt_mk_sub_leadingTerm (halive δ (lt_add_one_iff.2 le_rfl))
    rcases (le_of_lt_add_one hβ).eq_or_lt with rfl | hlt
    · exact hstep
    · exact (ih (fun ρ hρ ↦ halive ρ (hρ.trans (lt_add_one_iff.2 le_rfl))) β hlt).trans
        hstep
  | limit γ hγ ih =>
    intro halive β hβ
    -- While alive, the extracted terms are strictly dominating below `γ` …
    have hdom : IsStrictDom (cnfTerm x) γ := by
      intro β' δ' hβδ hδγ
      rw [mk_cnfTerm, mk_cnfTerm]
      exact ih δ' hδγ (fun ρ hρ ↦ halive ρ (hρ.trans hδγ)) β' hβδ
    -- … so the canonical partial sums satisfy the summation theorem's residual bounds.
    have hsum := isHahnSumO_hahnSumO hdom
    have hβ1 : β + 1 < γ := by
      rw [← succ_eq_add_one]
      exact hγ.succ_lt hβ
    have hres : cnfRes x γ = cnfRes x (β + 1) +
        -(hahnSumO (cnfTerm x) γ - hahnSumO (cnfTerm x) (β + 1)) := by
      rw [cnfRes_eq_sub, cnfRes_eq_sub]
      ring
    have h1 : ArchimedeanClass.mk (cnfRes x β) <
        ArchimedeanClass.mk (cnfRes x (β + 1)) := by
      rw [cnfRes_add_one]
      exact mk_lt_mk_sub_leadingTerm (halive β hβ)
    have h2 : ArchimedeanClass.mk (cnfRes x β) <
        ArchimedeanClass.mk
          (-(hahnSumO (cnfTerm x) γ - hahnSumO (cnfTerm x) (β + 1))) := by
      rw [ArchimedeanClass.mk_neg]
      refine h1.trans_le ?_
      rw [← mk_cnfTerm]
      exact hsum (β + 1) hβ1
    rw [hres]
    exact lt_mk_add' h1 h2

/-- **The residual scales climb strictly** while the residuals are nonzero — through limit
stages as well: at a limit, the residual splits along any earlier stage into a
strictly-finer successor residual plus a summation-theorem remainder, and the pincer
closes. This is what keeps the extraction strictly dominating forever (or until it
dies). -/
theorem mk_cnfRes_lt {x : Surreal.{u}} {α β : Ordinal.{u}}
    (halive : ∀ δ < α, cnfRes x δ ≠ 0) (hβ : β < α) :
    ArchimedeanClass.mk (cnfRes x β) < ArchimedeanClass.mk (cnfRes x α) :=
  mk_cnfRes_lt_aux x α halive β hβ

/-- While the extraction is alive below `α`, the extracted series is strictly
dominating. -/
theorem cnfTerm_isStrictDom {x : Surreal.{u}} {α : Ordinal.{u}}
    (halive : ∀ δ < α, cnfRes x δ ≠ 0) : IsStrictDom (cnfTerm x) α := by
  intro β γ hβγ hγα
  rw [mk_cnfTerm, mk_cnfTerm]
  exact mk_cnfRes_lt (fun ρ hρ ↦ halive ρ (hρ.trans hγα)) hβγ

/-! ### Termination, and what it buys -/

/-- `α` is **the normal-form length of `x`**: the extraction dies exactly at stage `α` —
alive at every earlier stage, zero residual at `α`. Full Conway normal form is precisely
the (open here) statement that every surreal has a normal-form length. -/
def IsCNFLength (x : Surreal.{u}) (α : Ordinal.{u}) : Prop :=
  cnfRes x α = 0 ∧ ∀ β < α, cnfRes x β ≠ 0

/-- **Terminating extractions represent**: if the extraction of `x` dies at `α`, then `x`
*is* the canonical transfinite sum of its normal form — a strictly dominating series of
leading terms (real multiples of `ω`-powers) of length exactly `α`. -/
theorem IsCNFLength.eq_hahnSumO {x : Surreal.{u}} {α : Ordinal.{u}}
    (h : IsCNFLength x α) : x = hahnSumO (cnfTerm x) α := by
  have h1 := cnfRes_eq_sub x α
  rw [h.1] at h1
  exact sub_eq_zero.1 h1.symm

theorem IsCNFLength.isStrictDom {x : Surreal.{u}} {α : Ordinal.{u}}
    (h : IsCNFLength x α) : IsStrictDom (cnfTerm x) α :=
  cnfTerm_isStrictDom h.2

/-- At a limit normal-form length, `x` is moreover the **birthday-minimal** Hahn sum of
its own normal form: a surreal is the simplest number with its residual structure. -/
theorem IsCNFLength.birthday_le {x : Surreal.{u}} {α : Ordinal.{u}}
    (h : IsCNFLength x α) (hα : IsSuccLimit α) {z : Surreal.{u}}
    (hz : IsHahnSumO (cnfTerm x) α z) : x.birthday ≤ z.birthday := by
  rw [h.eq_hahnSumO]
  exact birthday_hahnSumO_le hα (h.isStrictDom.ne_zero_of_isSuccLimit hα) hz

/-! ### The base case: monomials have normal form of length one -/

/-- Monomials are their own leading terms. -/
theorem leadingTerm_monomial {r : ℝ} (y : Surreal.{u}) :
    ((r : Surreal.{u}) * ω^ y).leadingTerm = (r : Surreal.{u}) * ω^ y := by
  rw [leadingTerm_mul, leadingTerm_realCast, leadingTerm_wpow]

/-- **Monomials have normal form of length `1`**: the extraction of `r·ω^y` (with `r ≠ 0`)
dies exactly at stage `1`. The base case of the finite-support normal-form theory. -/
theorem isCNFLength_monomial {r : ℝ} (hr : r ≠ 0) (y : Surreal.{u}) :
    IsCNFLength ((r : Surreal.{u}) * ω^ y) 1 := by
  have hne : (r : Surreal.{u}) * ω^ y ≠ 0 :=
    mul_ne_zero (by simpa using hr) (wpow_pos y).ne'
  constructor
  · rw [show (1 : Ordinal.{u}) = 0 + 1 from (zero_add 1).symm, cnfRes_add_one,
      cnfRes_zero, leadingTerm_monomial, sub_self]
  · intro β hβ
    obtain rfl : β = 0 := lt_one_iff.1 hβ
    rw [cnfRes_zero]
    exact hne

end Surreal
