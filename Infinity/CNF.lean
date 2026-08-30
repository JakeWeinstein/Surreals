import Infinity.NormalForm
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

/-! ### Finite base-`ω` expansions are their own normal forms -/

section FiniteCNF

open Finset

variable {n : ℕ} {r : ℕ → ℝ} {y : ℕ → Surreal.{u}}

private theorem lt_mk_sum' {c : ArchimedeanClass Surreal} (hc : c < ⊤) {s : Finset ℕ}
    {u : ℕ → Surreal} (h : ∀ i ∈ s, c < ArchimedeanClass.mk (u i)) :
    c < ArchimedeanClass.mk (∑ i ∈ s, u i) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, show ArchimedeanClass.mk (0 : Surreal) = ⊤ from
      ArchimedeanClass.mk_eq_top_iff.2 rfl]
    exact hc
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact lt_mk_add' (h a (Finset.mem_cons_self ..))
      (ih fun i hi ↦ h i (Finset.mem_cons_of_mem hi))

/-- In a finite expansion with strictly decreasing exponents, each term strictly dominates
the tail after it. -/
private theorem mk_head_lt_tail (hy : ∀ i j, i < j → j < n → y j < y i)
    (hr : ∀ i < n, r i ≠ 0) {k : ℕ} (hk : k < n) :
    ArchimedeanClass.mk ((r k : Surreal.{u}) * ω^ (y k)) <
      ArchimedeanClass.mk (∑ i ∈ Ico (k + 1) n, (r i : Surreal.{u}) * ω^ (y i)) := by
  have hne : (r k : Surreal.{u}) * ω^ (y k) ≠ 0 :=
    mul_ne_zero (by simpa using hr k hk) (wpow_pos _).ne'
  refine lt_mk_sum' (lt_top_iff_ne_top.2 fun h ↦ hne (ArchimedeanClass.mk_eq_top_iff.1 h))
    fun i hi ↦ ?_
  obtain ⟨hik, hin⟩ := mem_Ico.1 hi
  rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, mk_realCast (hr k hk),
    mk_realCast (hr i hin), zero_add, zero_add]
  exact archimedeanClassMk_wpow_strictAnti (hy k i (Nat.lt_of_succ_le hik) hin)

/-- The residuals of a finite expansion are its tails: extracting `k` terms leaves
`Σ_{k≤i<n} r_i·ω^(y_i)`. -/
theorem cnfRes_finsum (hy : ∀ i j, i < j → j < n → y j < y i) (hr : ∀ i < n, r i ≠ 0)
    (k : ℕ) (hkn : k ≤ n) :
    cnfRes (∑ i ∈ range n, (r i : Surreal.{u}) * ω^ (y i)) k =
      ∑ i ∈ Ico k n, (r i : Surreal.{u}) * ω^ (y i) := by
  induction k with
  | zero => rw [Nat.cast_zero, cnfRes_zero, range_eq_Ico]
  | succ k ih =>
    have hk : k < n := Nat.lt_of_succ_le hkn
    rw [Nat.cast_add_one, cnfRes_add_one, ih hk.le,
      sum_eq_sum_Ico_succ_bot hk (fun i ↦ (r i : Surreal.{u}) * ω^ (y i)),
      leadingTerm_add_eq_left (vlt_def.2 (mk_head_lt_tail hy hr hk)),
      leadingTerm_monomial]
    ring

/-- The extracted terms of a finite expansion are its own terms. -/
theorem cnfTerm_finsum (hy : ∀ i j, i < j → j < n → y j < y i) (hr : ∀ i < n, r i ≠ 0)
    {k : ℕ} (hk : k < n) :
    cnfTerm (∑ i ∈ range n, (r i : Surreal.{u}) * ω^ (y i)) k =
      (r k : Surreal.{u}) * ω^ (y k) := by
  rw [cnfTerm, cnfRes_finsum hy hr k hk.le,
    sum_eq_sum_Ico_succ_bot hk (fun i ↦ (r i : Surreal.{u}) * ω^ (y i)),
    leadingTerm_add_eq_left (vlt_def.2 (mk_head_lt_tail hy hr hk)),
    leadingTerm_monomial]

/-- **Finite base-`ω` expansions have normal form of length exactly `n`**: the extraction
of `Σ_{i<n} r_i·ω^(y_i)` (strictly decreasing exponents, nonzero coefficients) recovers
the expansion term by term and dies at stage `n`. -/
theorem isCNFLength_finsum (hy : ∀ i j, i < j → j < n → y j < y i)
    (hr : ∀ i < n, r i ≠ 0) :
    IsCNFLength (∑ i ∈ range n, (r i : Surreal.{u}) * ω^ (y i)) n := by
  constructor
  · rw [cnfRes_finsum hy hr n le_rfl, Ico_self, sum_empty]
  · intro β hβ
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.1 (hβ.trans (Ordinal.natCast_lt_omega0 n))
    have hk : k < n := by exact_mod_cast hβ
    rw [cnfRes_finsum hy hr k hk.le,
      sum_eq_sum_Ico_succ_bot hk (fun i ↦ (r i : Surreal.{u}) * ω^ (y i))]
    intro h0
    have hneg := eq_neg_of_add_eq_zero_right h0
    have hlt := mk_head_lt_tail hy hr hk
    rw [hneg, ArchimedeanClass.mk_neg] at hlt
    exact lt_irrefl _ hlt

/-- **The finite normal-form representation theorem**: every finite base-`ω` expansion
*is* the canonical transfinite sum of its own extracted terms — the finite-support case of
Conway normal form, complete. -/
theorem finsum_eq_hahnSumO (hy : ∀ i j, i < j → j < n → y j < y i)
    (hr : ∀ i < n, r i ≠ 0) :
    (∑ i ∈ range n, (r i : Surreal.{u}) * ω^ (y i)) =
      hahnSumO (cnfTerm (∑ i ∈ range n, (r i : Surreal.{u}) * ω^ (y i))) n :=
  (isCNFLength_finsum hy hr).eq_hahnSumO

end FiniteCNF

/-! ### Uniqueness: the extraction reads the series off any of its sums -/

private theorem add_one_lt_of_isSuccLimit {β γ : Ordinal.{u}} (hγ : IsSuccLimit γ)
    (h : β < γ) : β + 1 < γ := by
  rw [← succ_eq_add_one]
  exact hγ.succ_lt h

/-- **Term recovery — the uniqueness direction of Conway normal form**: if `x` is *any*
Hahn sum of a strictly dominating series of monomial terms (each term its own leading
term: an ω-power series, the terms of a surreal Hahn series, …), then the normal-form
extraction of `x` recovers the series — `cnfTerm x β = t β` at every stage with
`β + 1 < α`. (At a final successor stage nothing can be recovered: the Hahn-sum
conditions never constrain a last term.) -/
theorem cnfTerm_eq_of_isHahnSumO {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    {x : Surreal.{u}} (ht : IsStrictDom t α)
    (hmon : ∀ β, β + 1 < α → (t β).leadingTerm = t β)
    (hx : IsHahnSumO t α x) :
    ∀ β, β + 1 < α → cnfTerm x β = t β := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β ih =>
    intro hβ1
    have hβα : β < α := (lt_add_one_iff.2 le_rfl).trans hβ1
    -- previously recovered terms give agreement of the canonical partial sums
    have hcong : hahnSumO (cnfTerm x) β = hahnSumO t β :=
      hahnSumO_congr fun δ hδ ↦ ih δ hδ ((add_one_le_iff.2 hδ).trans_lt hβα)
    -- the stage-`β` residual is the `β`-th term plus strictly finer junk
    have hres : cnfRes x β = t β + (x - hahnSumO t (β + 1)) := by
      rw [cnfRes_eq_sub, hcong, hahnSumO_add_one]
      ring
    have hdom : (x - hahnSumO t (β + 1)) <ᵥ t β := by
      rw [vlt_def]
      exact lt_of_lt_of_le (ht (lt_add_one_iff.2 le_rfl) hβ1) (hx (β + 1) hβ1)
    rw [cnfTerm, hres, leadingTerm_add_eq_left hdom, hmon β hβ1]

/-- At limit lengths, *every* term of a monomial series is recovered from any of its Hahn
sums. -/
theorem cnfTerm_eq_of_isHahnSumO_of_isSuccLimit {t : Ordinal.{u} → Surreal.{u}}
    {α : Ordinal.{u}} {x : Surreal.{u}} (hα : IsSuccLimit α) (ht : IsStrictDom t α)
    (hmon : ∀ β < α, (t β).leadingTerm = t β) (hx : IsHahnSumO t α x) :
    ∀ β < α, cnfTerm x β = t β := fun β hβ ↦
  cnfTerm_eq_of_isHahnSumO ht
    (fun δ hδ1 ↦ hmon δ ((lt_add_one_iff.2 le_rfl).trans hδ1)) hx β
    (add_one_lt_of_isSuccLimit hα hβ)

/-- **Uniqueness of representation at limit lengths**: two strictly dominating monomial
series of the same limit length sharing even a single common Hahn sum are equal (below the
length). Combined with `exists_isHahnSumO`, monomial series of limit length are determined
by their sums — the injectivity half of Conway normal form at the level of term
sequences. -/
theorem eq_of_isHahnSumO_of_isHahnSumO {t u : Ordinal.{u} → Surreal.{u}}
    {α : Ordinal.{u}} {x : Surreal.{u}} (hα : IsSuccLimit α)
    (ht : IsStrictDom t α) (hu : IsStrictDom u α)
    (hmont : ∀ β < α, (t β).leadingTerm = t β)
    (hmonu : ∀ β < α, (u β).leadingTerm = u β)
    (hxt : IsHahnSumO t α x) (hxu : IsHahnSumO u α x) :
    ∀ β < α, t β = u β := fun β hβ ↦ by
  rw [← cnfTerm_eq_of_isHahnSumO_of_isSuccLimit hα ht hmont hxt β hβ,
    cnfTerm_eq_of_isHahnSumO_of_isSuccLimit hα hu hmonu hxu β hβ]

/-! ### The evaluation of a surreal Hahn series is faithful -/

/-- The terms of a surreal Hahn series are monomials (their own leading terms). -/
theorem _root_.SurrealHahnSeries.leadingTerm_term (x : SurrealHahnSeries.{u})
    {β : Ordinal.{u}} (hβ : β < x.length) : (x.term β).leadingTerm = x.term β := by
  rw [SurrealHahnSeries.term_of_lt hβ]
  exact leadingTerm_monomial _

/-- **The evaluation is faithful**: the normal-form extraction reads the Hahn series back
off its evaluation — `cnfTerm (evalHahn x) β = x.term β` whenever `β + 1 < x.length`. -/
theorem cnfTerm_evalHahn (x : SurrealHahnSeries.{u}) {β : Ordinal.{u}}
    (hβ : β + 1 < x.length) : cnfTerm (evalHahn x) β = x.term β :=
  cnfTerm_eq_of_isHahnSumO x.isStrictDom_term
    (fun _δ hδ1 ↦ x.leadingTerm_term ((lt_add_one_iff.2 le_rfl).trans hδ1))
    (isHahnSumO_evalHahn x) β hβ

/-- **At limit lengths the extraction of an evaluation terminates**, at exactly the
series' length: `evalHahn x` has normal-form length `x.length` — the value's canonical
normal form *is* the series it came from. -/
theorem isCNFLength_evalHahn {x : SurrealHahnSeries.{u}} (hx : IsSuccLimit x.length) :
    IsCNFLength (evalHahn x) x.length := by
  have hrec : ∀ δ < x.length, cnfTerm (evalHahn x) δ = x.term δ := fun δ hδ ↦
    cnfTerm_evalHahn x (add_one_lt_of_isSuccLimit hx hδ)
  constructor
  · rw [cnfRes_eq_sub, hahnSumO_congr hrec]
    exact sub_eq_zero.2 rfl
  · intro β hβ h0
    have h1 := mk_sub_hahnSumO_cnfTerm (evalHahn x) β
    rw [← cnfRes_eq_sub, h0, hrec β hβ,
      show ArchimedeanClass.mk (0 : Surreal) = ⊤ from
        ArchimedeanClass.mk_eq_top_iff.2 rfl] at h1
    exact absurd (SurrealHahnSeries.term_eq_zero.1
      (ArchimedeanClass.mk_eq_top_iff.1 h1.symm)) hβ.not_ge

private theorem length_le_of_evalHahn_eq {x y : SurrealHahnSeries.{u}}
    (hx : IsSuccLimit x.length) (hy : IsSuccLimit y.length)
    (h : evalHahn x = evalHahn y) : y.length ≤ x.length := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : cnfTerm (evalHahn y) x.length = y.term x.length :=
    cnfTerm_evalHahn y (add_one_lt_of_isSuccLimit hy hlt)
  rw [← h, cnfTerm, (isCNFLength_evalHahn hx).1, leadingTerm_zero] at h1
  exact absurd (SurrealHahnSeries.term_eq_zero.1 h1.symm) hlt.not_ge

/-- Two limit-length series with the same evaluation have the same length. -/
theorem length_eq_of_evalHahn_eq {x y : SurrealHahnSeries.{u}}
    (hx : IsSuccLimit x.length) (hy : IsSuccLimit y.length)
    (h : evalHahn x = evalHahn y) : x.length = y.length :=
  (length_le_of_evalHahn_eq hy hx h.symm).antisymm (length_le_of_evalHahn_eq hx hy h)

/-- **Term-level injectivity of the evaluation**: two surreal Hahn series of limit length
with the same evaluation have the same length and the same terms — uniqueness of the
normal-form data, read off the value by the extraction. -/
theorem term_congr_of_evalHahn_eq {x y : SurrealHahnSeries.{u}}
    (hx : IsSuccLimit x.length) (hy : IsSuccLimit y.length)
    (h : evalHahn x = evalHahn y) : ∀ β, x.term β = y.term β := by
  have hlen := length_eq_of_evalHahn_eq hx hy h
  intro β
  rcases lt_or_ge β x.length with hβ | hβ
  · rw [← cnfTerm_evalHahn x (add_one_lt_of_isSuccLimit hx hβ), h,
      cnfTerm_evalHahn y (add_one_lt_of_isSuccLimit hy (hlen ▸ hβ))]
  · rw [SurrealHahnSeries.term_of_le hβ, SurrealHahnSeries.term_of_le (hlen ▸ hβ)]

/-! ### Full injectivity: a series is determined by its evaluation -/

/-- Two monomials with a nonzero coefficient are equal only componentwise: comparing
Archimedean classes forces the exponents equal, then cancellation forces the
coefficients. -/
private theorem monomial_eq_iff {r s : ℝ} {a b : Surreal.{u}} (hr : r ≠ 0)
    (h : (r : Surreal.{u}) * ω^ a = (s : Surreal.{u}) * ω^ b) : a = b ∧ r = s := by
  have hs : s ≠ 0 := by
    rintro rfl
    apply hr
    have h0 : (r : Surreal.{u}) * ω^ a = 0 := by
      rw [h]
      simp
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 (wpow_pos a).ne'
  have hab : a = b := by
    have hmk := congrArg ArchimedeanClass.mk h
    rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, mk_realCast hr, mk_realCast hs,
      zero_add, zero_add] at hmk
    exact archimedeanClassMk_wpow_strictAnti.injective hmk
  subst hab
  refine ⟨rfl, ?_⟩
  have h2 := mul_right_cancel₀ (wpow_pos a).ne' h
  exact_mod_cast h2

/-- Series with equal lengths and equal terms have equal coefficients on the support of
the first. -/
private theorem coeff_eq_of_term_congr {x y : SurrealHahnSeries.{u}}
    (hlen : x.length = y.length) (hterm : ∀ β, x.term β = y.term β)
    {e : Surreal.{u}} (he : e ∈ x.support) : x.coeff e = y.coeff e := by
  obtain ⟨j, hj⟩ := SurrealHahnSeries.eq_exp_of_mem_support he
  have hjx : j.1 < x.length := j.2
  have hjy : j.1 < y.length := hlen ▸ hjx
  have hcx : x.coeffIdx j.1 ≠ 0 := fun h0 ↦
    absurd (SurrealHahnSeries.coeffIdx_eq_zero_iff.1 h0) hjx.not_ge
  have ht := hterm j.1
  rw [SurrealHahnSeries.term_of_lt hjx, SurrealHahnSeries.term_of_lt hjy] at ht
  obtain ⟨hexp, hcoeff⟩ := monomial_eq_iff hcx ht
  have hx1 : x.coeff e = x.coeffIdx j.1 := by
    rw [← hj]
    exact x.coeff_exp j
  have he2 : ((y.exp ⟨j.1, hjy⟩ : y.support) : Surreal) = e := by
    rw [← hexp]
    exact hj
  have hy1 : y.coeff e = y.coeffIdx j.1 := by
    rw [← he2]
    exact y.coeff_exp _
  rw [hx1, hy1]
  exact hcoeff

/-- **The evaluation is injective on limit-length series**: a surreal Hahn series of limit
length is determined by its value. Together with `isHahnSumO_evalHahn` and
`isCNFLength_evalHahn`, this is uniqueness of the Conway-normal-form *representation* for
every value in the range of the evaluation. -/
theorem evalHahn_inj {x y : SurrealHahnSeries.{u}} (hx : IsSuccLimit x.length)
    (hy : IsSuccLimit y.length) (h : evalHahn x = evalHahn y) : x = y := by
  have hlen := length_eq_of_evalHahn_eq hx hy h
  have hterm := term_congr_of_evalHahn_eq hx hy h
  ext e
  by_cases hex : e ∈ x.support
  · exact coeff_eq_of_term_congr hlen hterm hex
  · by_cases hey : e ∈ y.support
    · exact (coeff_eq_of_term_congr hlen.symm (fun β ↦ (hterm β).symm) hey).symm
    · rw [SurrealHahnSeries.mem_support_iff, not_ne_iff] at hex hey
      rw [hex, hey]

end Surreal
