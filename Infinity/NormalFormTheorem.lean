/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import Infinity.HahnMerge

/-!
# Conway's Normal Form Theorem: every surreal is the canonical sum of its normal form

`Infinity/CNF.lean` formalized the leading-term extraction of Conway normal form — the
residuals `cnfRes x β`, the terms `cnfTerm x β = (cnfRes x β).leadingTerm`, the exact
bookkeeping `cnfRes x α = x − hahnSumO (cnfTerm x) α`, strict domination while alive, and
the harvest of termination (`IsCNFLength.eq_hahnSumO`) — and isolated **termination** of the
extraction as the sole remaining gap. This file closes it.

**The argument.** The canonical partial sums `S β := hahnSumO (cnfTerm x) β` of the
extraction are born no later than `x` itself, as long as the extraction is alive below `β`:

* at a limit stage, `x` is a Hahn sum of the prefix (`isHahnSumO_cnfTerm`), so a
  representative of `x` fits the transfinite option game whose value is `S β`
  (`fits_optionGameO_iff`, `mk_optionGameO_eq_hahnSumO`), and the simplicity theorem gives
  `birthday (S β) ≤ birthday x`;
* at a successor stage `δ + 1`, `S (δ+1)` is a canonical sum of monomials, hence coarsely
  representable at the class of its last term (`coarseRep_hahnSumO`, `coarseRep_monomial`),
  while `x − S (δ+1)` is strictly finer than that class; the new lemma
  `birthday_le_of_coarseRep_of_mk_lt` — **coarse representability forces simplicity in the
  fine halo** — again gives `birthday (S (δ+1)) ≤ birthday x`.

While alive, distinct stages have distinct partial sums (`mk_cnfRes_lt`). So if the
extraction never died, `β ↦ S β` would inject `Ordinal.{u}` into the `Small.{u}` set of
surreals born by `birthday x` (`small_setOf_birthday_le`), contradicting `not_small_ordinal`
(Burali-Forti). Hence the extraction dies at some set-sized stage.

**Main theorems.**

* `birthday_le_of_coarseRep_of_mk_lt` : `CoarseRep X c → c < mk (z − X) → X.birthday ≤ z.birthday`;
  `haloSimple_of_coarseRep` : every coarsely representable point is halo-simple at every
  scale finer than its representability class — the conjecture (φ) of the roadmap for all
  coarsely representable points, in particular (`haloSimple_hahnSumO_cnfTerm`) for every
  successor-length normal-form prefix sum at every scale finer than its last term.
* `birthday_hahnSumO_cnfTerm_le` : `(∀ δ < β, cnfRes x δ ≠ 0) → (hahnSumO (cnfTerm x) β).birthday ≤ x.birthday`.
* `exists_cnfRes_eq_zero` : **the extraction terminates**: `∀ x, ∃ α, cnfRes x α = 0`.
* `cnfLength x` (the least such `α`), `isCNFLength_cnfLength`, `exists_isCNFLength`,
  `IsCNFLength.unique`, `IsCNFLength.eq_cnfLength`.
* **`eq_hahnSumO_cnfTerm`** — *Conway's Normal Form Theorem, existence*: every surreal is
  the canonical transfinite sum of its normal form, `x = hahnSumO (cnfTerm x) (cnfLength x)`,
  a strictly dominating series of monomials `leadingCoeff · ω^ wlog` of length exactly
  `cnfLength x` (`isStrictDom_cnfTerm`, `cnfTerm_eq_monomial`); at limit lengths it is the
  birthday-minimal such sum (`IsCNFLength.birthday_le` in `CNF.lean`).
* `toHahnSeries x : SurrealHahnSeries` — the normal form packaged as a surreal Hahn series
  (coefficient `leadingCoeff (cnfRes x β)` at exponent `wlog (cnfRes x β)`), with
  `length_toHahnSeries`, `term_toHahnSeries`, **`evalHahn_toHahnSeries : evalHahn (toHahnSeries x) = x`**,
  hence **`evalHahn_surjective`**: every surreal is the evaluation of a surreal Hahn series.
* **Uniqueness at every length**: `cnfTerm_eq_of_eq_hahnSumO` / `isCNFLength_of_eq_hahnSumO` —
  if `x` *is* the canonical sum of a strictly dominating series of nonzero monomials of length
  `α`, that series is the normal form of `x` and `α = cnfLength x` (a final successor term,
  invisible to `cnfTerm_eq_of_isHahnSumO`, is pinned by the exact value). Hence
  `cnfLength_evalHahn`, `cnfTerm_evalHahn_of_lt`, `cnfCoeff_evalHahn`, and
  **`toHahnSeries_evalHahn : toHahnSeries (evalHahn y) = y`**, so `evalHahn` is injective at
  every length (`evalHahn_injective`; `evalHahn_inj` of `CNF.lean` was the limit-length case)
  and **`hahnEquiv : SurrealHahnSeries ≃ Surreal`** — the normal-form correspondence — is an
  honest `Equiv` with inverse `toHahnSeries`.

**A remark on the residual past the length.** `cnfRes x β = 0` for `β = cnfLength x`, but the
residual is *not* identically zero afterwards: at the next limit stage the band cuts of the
recursion no longer separate (all terms from the length on are `0`, so the lower cut sits at
`rightSurreal x` and the upper at `leftSurreal x`), `simplestBtwnD` returns its junk value
`0`, and the extraction restarts from `x`. Nothing here depends on the behaviour past the
length; all statements are made for stages at which the extraction is alive below.
-/

open ArchimedeanClass IGame Order

universe u

noncomputable section

namespace Surreal

/-! ### Coarse representability forces simplicity in the fine halo -/

/-- **Coarse ⟹ simplest in the fine halo.** If `X` has a numeric representative all of whose
options sit at distance of class `≤ c` from `X`, then every point `z` whose distance from `X`
is strictly finer than `c` fits that representative, so `X` is born no later than `z`. -/
theorem birthday_le_of_coarseRep_of_mk_lt {X : Surreal.{u}} {c : ArchimedeanClass Surreal.{u}}
    (hX : CoarseRep X c) {z : Surreal.{u}} (hz : c < ArchimedeanClass.mk (z - X)) :
    X.birthday ≤ z.birthday := by
  obtain ⟨G, hG, hGX, hl, hr⟩ := hX
  rw [← hGX]
  refine birthday_mk_le_of_fits ?_
  constructor
  · intro a ha
    haveI := IGame.Numeric.of_mem_moves ha
    refine IGame.Numeric.not_le.2 ?_
    rw [← Surreal.mk_lt_mk, out_eq]
    have h1 : |z - X| < |X - Surreal.mk a| := by
      have := ArchimedeanClass.mk_lt_mk.1 ((hl a ha).trans_lt hz) 1
      simpa using this
    have h2 : Surreal.mk a < X := by
      rw [← hGX]
      exact Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt ha)
    rw [abs_of_pos (sub_pos.2 h2)] at h1
    have h3 := le_abs_self (X - z)
    rw [abs_sub_comm] at h3
    linarith
  · intro b hb
    haveI := IGame.Numeric.of_mem_moves hb
    refine IGame.Numeric.not_le.2 ?_
    rw [← Surreal.mk_lt_mk, out_eq]
    have h1 : |z - X| < |Surreal.mk b - X| := by
      have := ArchimedeanClass.mk_lt_mk.1 ((hr b hb).trans_lt hz) 1
      simpa using this
    have h2 : X < Surreal.mk b := by
      rw [← hGX]
      exact Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right hb)
    rw [abs_of_pos (sub_pos.2 h2)] at h1
    have h3 := le_abs_self (z - X)
    linarith

/-- **Coarsely representable points are halo-simple** at every scale `ε` some power of which
is at least as fine as the representability class: the deep halo of `X` at scale `ε` consists
of points strictly finer than `c` away from `X`, all of which are at least as complex as `X`. -/
theorem haloSimple_of_coarseRep {X : Surreal.{u}} {c : ArchimedeanClass Surreal.{u}}
    (hX : CoarseRep X c) {ε : Surreal.{u}}
    (hc : ∃ N : ℕ, c ≤ ArchimedeanClass.mk (ε ^ N)) : HaloSimple ε X := by
  obtain ⟨N, hN⟩ := hc
  intro z hz
  exact birthday_le_of_coarseRep_of_mk_lt hX (hN.trans_lt (hz N))

/-! ### The terms of the extraction are coarsely representable monomials -/

/-- The `β`-th normal-form term is the monomial `leadingCoeff · ω^ wlog` of the `β`-th
residual (definitionally). -/
theorem cnfTerm_eq_monomial (x : Surreal.{u}) (β : Ordinal.{u}) :
    cnfTerm x β = ((cnfRes x β).leadingCoeff : Surreal.{u}) * ω^ (cnfRes x β).wlog :=
  rfl

/-- Every normal-form term is its own leading term. -/
theorem leadingTerm_cnfTerm (x : Surreal.{u}) (β : Ordinal.{u}) :
    (cnfTerm x β).leadingTerm = cnfTerm x β :=
  leadingTerm_leadingTerm _

/-- While alive, the class of `ω^ wlog` of the residual is the class of the term. -/
theorem mk_wpow_wlog_cnfRes {x : Surreal.{u}} {β : Ordinal.{u}} (h : cnfRes x β ≠ 0) :
    ArchimedeanClass.mk (ω^ (cnfRes x β).wlog) = ArchimedeanClass.mk (cnfTerm x β) := by
  rw [mk_cnfTerm]
  exact archimedeanClassMk_wpow_wlog h

/-- Every normal-form term is coarsely representable at the class of its `ω`-power. -/
theorem coarseRep_cnfTerm (x : Surreal.{u}) (β : Ordinal.{u}) :
    CoarseRep (cnfTerm x β) (ArchimedeanClass.mk (ω^ (cnfRes x β).wlog)) :=
  coarseRep_monomial _ _

/-- **Coarse representability of the successor-stage prefix sums**: while the extraction is
alive below `δ + 1`, the prefix sum `hahnSumO (cnfTerm x) (δ + 1)` is coarsely representable
at the class of its last term `cnfTerm x δ`. -/
theorem coarseRep_hahnSumO_cnfTerm {x : Surreal.{u}} {δ : Ordinal.{u}}
    (halive : ∀ ρ < δ + 1, cnfRes x ρ ≠ 0) :
    CoarseRep (hahnSumO (cnfTerm x) (δ + 1)) (ArchimedeanClass.mk (cnfTerm x δ)) := by
  have hδ : δ < δ + 1 := lt_add_one_iff.2 le_rfl
  have ht : IsStrictDom (cnfTerm x) (δ + 1) := cnfTerm_isStrictDom halive
  have hle : ∀ ζ < δ + 1, ArchimedeanClass.mk (cnfTerm x ζ) ≤ ArchimedeanClass.mk (cnfTerm x δ) := by
    intro ζ hζ
    rcases (le_of_lt_add_one hζ).eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact (ht hlt hδ).le
  refine coarseRep_hahnSumO ht hle fun ζ hζ ↦ ?_
  refine (coarseRep_cnfTerm x ζ).mono ?_
  rw [mk_wpow_wlog_cnfRes (halive ζ hζ)]
  exact hle ζ hζ

/-- **Halo-simplicity of the successor-stage prefix sums**: at every scale `ε` some power of
which is at least as fine as the last term, `hahnSumO (cnfTerm x) (δ + 1)` is the
birthday-simplest point of its own deep halo. -/
theorem haloSimple_hahnSumO_cnfTerm {x : Surreal.{u}} {δ : Ordinal.{u}}
    (halive : ∀ ρ < δ + 1, cnfRes x ρ ≠ 0) {ε : Surreal.{u}}
    (hε : ∃ N : ℕ, ArchimedeanClass.mk (cnfTerm x δ) ≤ ArchimedeanClass.mk (ε ^ N)) :
    HaloSimple ε (hahnSumO (cnfTerm x) (δ + 1)) :=
  haloSimple_of_coarseRep (coarseRep_hahnSumO_cnfTerm halive) hε

/-! ### The birthday bound along the extraction -/

/-- **The canonical prefix sums are born no later than `x`**, at every stage below which the
extraction is alive. Limit stages: `x` fits the transfinite option game whose value is the
prefix sum. Successor stages: the prefix sum is coarsely representable at the class of its
last term, and `x` lies strictly finer than that class from it. -/
theorem birthday_hahnSumO_cnfTerm_le {x : Surreal.{u}} {β : Ordinal.{u}}
    (halive : ∀ δ < β, cnfRes x δ ≠ 0) :
    (hahnSumO (cnfTerm x) β).birthday ≤ x.birthday := by
  induction β using Ordinal.limitRecOn with
  | zero =>
    rw [hahnSumO_zero, birthday_zero]
    exact bot_le
  | add_one δ _ =>
    have hδ : δ < δ + 1 := lt_add_one_iff.2 le_rfl
    refine birthday_le_of_coarseRep_of_mk_lt (coarseRep_hahnSumO_cnfTerm halive) ?_
    rw [← cnfRes_eq_sub, mk_cnfTerm]
    exact mk_cnfRes_lt halive hδ
  | limit γ hγ _ =>
    have ht : IsStrictDom (cnfTerm x) γ := cnfTerm_isStrictDom halive
    haveI := numeric_optionGameO hγ ht
    rw [← mk_optionGameO_eq_hahnSumO hγ ht]
    refine birthday_mk_le_of_fits ?_
    rw [fits_optionGameO_iff hγ ht, out_eq]
    exact isHahnSumO_cnfTerm x γ

/-! ### Injectivity of the prefix sums while alive -/

/-- While the extraction is alive, distinct stages have distinct canonical prefix sums: the
residuals at the two stages lie at distinct scales. -/
theorem hahnSumO_cnfTerm_ne {x : Surreal.{u}} {β γ : Ordinal.{u}}
    (halive : ∀ δ < γ, cnfRes x δ ≠ 0) (hβγ : β < γ) :
    hahnSumO (cnfTerm x) β ≠ hahnSumO (cnfTerm x) γ := by
  intro h
  have hlt := mk_cnfRes_lt halive hβγ
  rw [cnfRes_eq_sub, cnfRes_eq_sub x γ, h] at hlt
  exact lt_irrefl _ hlt

/-! ### Termination -/

/-- **The extraction terminates.** If the residual never vanished, `β ↦ hahnSumO (cnfTerm x) β`
would be an injection of `Ordinal.{u}` into the `Small.{u}` set of surreals born by
`x.birthday` — the type-theoretic Burali-Forti paradox (`not_small_ordinal`). -/
theorem exists_cnfRes_eq_zero (x : Surreal.{u}) : ∃ α : Ordinal.{u}, cnfRes x α = 0 := by
  by_contra hcon
  have halive : ∀ α, cnfRes x α ≠ 0 := fun α h ↦ hcon ⟨α, h⟩
  let f : Ordinal.{u} → {y : Surreal.{u} | y.birthday ≤ x.birthday} := fun β ↦
    ⟨hahnSumO (cnfTerm x) β, birthday_hahnSumO_cnfTerm_le fun δ _ ↦ halive δ⟩
  have hf : Function.Injective f := by
    intro β γ h
    have h' : hahnSumO (cnfTerm x) β = hahnSumO (cnfTerm x) γ := congrArg Subtype.val h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hahnSumO_cnfTerm_ne (fun δ _ ↦ halive δ) hlt h'
    · exact hahnSumO_cnfTerm_ne (fun δ _ ↦ halive δ) hlt h'.symm
  exact not_small_ordinal.{u, u} (small_of_injective hf)

/-! ### The normal-form length -/

/-- **The normal-form length** of `x`: the least stage at which the extraction dies. -/
def cnfLength (x : Surreal.{u}) : Ordinal.{u} :=
  sInf {α : Ordinal.{u} | cnfRes x α = 0}

/-- The extraction of `x` dies exactly at `cnfLength x`: alive before, zero residual there. -/
theorem isCNFLength_cnfLength (x : Surreal.{u}) : IsCNFLength x (cnfLength x) := by
  have hne : {α : Ordinal.{u} | cnfRes x α = 0}.Nonempty := exists_cnfRes_eq_zero x
  refine ⟨csInf_mem hne, fun β hβ h0 ↦ ?_⟩
  exact absurd hβ (not_lt.2 (csInf_le' (show β ∈ {α : Ordinal.{u} | cnfRes x α = 0} from h0)))

/-- **Every surreal has a normal-form length** — the statement `CNF.lean` left open. -/
theorem exists_isCNFLength (x : Surreal.{u}) : ∃ α : Ordinal.{u}, IsCNFLength x α :=
  ⟨cnfLength x, isCNFLength_cnfLength x⟩

/-- The normal-form length is unique. -/
theorem IsCNFLength.unique {x : Surreal.{u}} {α α' : Ordinal.{u}} (h : IsCNFLength x α)
    (h' : IsCNFLength x α') : α = α' := by
  rcases lt_trichotomy α α' with hlt | heq | hgt
  · exact absurd h.1 (h'.2 α hlt)
  · exact heq
  · exact absurd h'.1 (h.2 α' hgt)

theorem IsCNFLength.eq_cnfLength {x : Surreal.{u}} {α : Ordinal.{u}} (h : IsCNFLength x α) :
    α = cnfLength x :=
  h.unique (isCNFLength_cnfLength x)

theorem isCNFLength_iff {x : Surreal.{u}} {α : Ordinal.{u}} :
    IsCNFLength x α ↔ α = cnfLength x :=
  ⟨IsCNFLength.eq_cnfLength, fun h ↦ h ▸ isCNFLength_cnfLength x⟩

@[simp]
theorem cnfRes_cnfLength (x : Surreal.{u}) : cnfRes x (cnfLength x) = 0 :=
  (isCNFLength_cnfLength x).1

theorem cnfRes_ne_zero_of_lt_cnfLength {x : Surreal.{u}} {β : Ordinal.{u}}
    (hβ : β < cnfLength x) : cnfRes x β ≠ 0 :=
  (isCNFLength_cnfLength x).2 β hβ

theorem cnfTerm_ne_zero_of_lt_cnfLength {x : Surreal.{u}} {β : Ordinal.{u}}
    (hβ : β < cnfLength x) : cnfTerm x β ≠ 0 := fun h ↦
  cnfRes_ne_zero_of_lt_cnfLength hβ (leadingTerm_eq_zero.1 h)

/-- The prefix sums up to the length are born no later than `x`. -/
theorem birthday_hahnSumO_cnfTerm_le_of_le {x : Surreal.{u}} {β : Ordinal.{u}}
    (hβ : β ≤ cnfLength x) : (hahnSumO (cnfTerm x) β).birthday ≤ x.birthday :=
  birthday_hahnSumO_cnfTerm_le fun _ hδ ↦ cnfRes_ne_zero_of_lt_cnfLength (hδ.trans_le hβ)

/-- Monomials have normal-form length `1`. -/
theorem cnfLength_monomial {r : ℝ} (hr : r ≠ 0) (y : Surreal.{u}) :
    cnfLength ((r : Surreal.{u}) * ω^ y) = 1 :=
  (isCNFLength_monomial hr y).eq_cnfLength.symm

/-- Finite base-`ω` expansions with `n` terms have normal-form length `n`. -/
theorem cnfLength_finsum {n : ℕ} {r : ℕ → ℝ} {y : ℕ → Surreal.{u}}
    (hy : ∀ i j, i < j → j < n → y j < y i) (hr : ∀ i < n, r i ≠ 0) :
    cnfLength (∑ i ∈ Finset.range n, (r i : Surreal.{u}) * ω^ (y i)) = n :=
  (isCNFLength_finsum hy hr).eq_cnfLength.symm

/-! ### Conway's Normal Form Theorem -/

/-- **CONWAY'S NORMAL FORM THEOREM (existence).** Every surreal is the canonical transfinite
sum of its normal form: `x = hahnSumO (cnfTerm x) (cnfLength x)`, the canonical sum of the
strictly dominating series of monomials `leadingCoeff (cnfRes x β) · ω^ wlog (cnfRes x β)`
extracted from it, of length exactly `cnfLength x`. -/
theorem eq_hahnSumO_cnfTerm (x : Surreal.{u}) : x = hahnSumO (cnfTerm x) (cnfLength x) :=
  (isCNFLength_cnfLength x).eq_hahnSumO

/-- Existential form of the Normal Form Theorem. -/
theorem exists_eq_hahnSumO_cnfTerm (x : Surreal.{u}) :
    ∃ α : Ordinal.{u}, x = hahnSumO (cnfTerm x) α :=
  ⟨_, eq_hahnSumO_cnfTerm x⟩

/-- The normal-form series of `x` is strictly dominating below its length. -/
theorem isStrictDom_cnfTerm (x : Surreal.{u}) : IsStrictDom (cnfTerm x) (cnfLength x) :=
  (isCNFLength_cnfLength x).isStrictDom

/-- At a limit normal-form length, `x` is the birthday-minimal Hahn sum of its own normal
form. -/
theorem birthday_le_of_isHahnSumO_cnfTerm (x : Surreal.{u}) (hα : IsSuccLimit (cnfLength x))
    {z : Surreal.{u}} (hz : IsHahnSumO (cnfTerm x) (cnfLength x) z) :
    x.birthday ≤ z.birthday :=
  (isCNFLength_cnfLength x).birthday_le hα hz

/-- **The Normal Form Theorem, packaged**: every surreal is the canonical transfinite sum of a
strictly dominating series of nonzero monomials (each its own leading term), of some ordinal
length at which the extraction dies. -/
theorem conway_normal_form (x : Surreal.{u}) :
    ∃ α : Ordinal.{u}, x = hahnSumO (cnfTerm x) α ∧ IsStrictDom (cnfTerm x) α ∧
      (∀ β < α, cnfTerm x β ≠ 0) ∧ (∀ β, (cnfTerm x β).leadingTerm = cnfTerm x β) ∧
      IsCNFLength x α :=
  ⟨cnfLength x, eq_hahnSumO_cnfTerm x, isStrictDom_cnfTerm x,
    fun _ hβ ↦ cnfTerm_ne_zero_of_lt_cnfLength hβ, leadingTerm_cnfTerm x,
    isCNFLength_cnfLength x⟩

/-! ### The normal form as a surreal Hahn series -/

/-- **The `β`-th normal-form exponent**: the `ω`-logarithm of the `β`-th residual. -/
def cnfExp (x : Surreal.{u}) (β : Ordinal.{u}) : Surreal.{u} :=
  (cnfRes x β).wlog

theorem cnfTerm_eq_cnfExp (x : Surreal.{u}) (β : Ordinal.{u}) :
    cnfTerm x β = ((cnfRes x β).leadingCoeff : Surreal.{u}) * ω^ (cnfExp x β) :=
  rfl

/-- Below the length, the normal-form exponents strictly decrease. -/
theorem cnfExp_lt_cnfExp {x : Surreal.{u}} {β γ : Ordinal.{u}} (hβγ : β < γ)
    (hγ : γ < cnfLength x) : cnfExp x γ < cnfExp x β := by
  have h := mk_cnfRes_lt (fun δ hδ ↦ cnfRes_ne_zero_of_lt_cnfLength (hδ.trans hγ)) hβγ
  rw [← archimedeanClassMk_wpow_wlog (cnfRes_ne_zero_of_lt_cnfLength (hβγ.trans hγ)),
    ← archimedeanClassMk_wpow_wlog (cnfRes_ne_zero_of_lt_cnfLength hγ)] at h
  exact archimedeanClassMk_wpow_strictAnti.lt_iff_gt.1 h

/-- Below the length, the normal-form exponents are injective. -/
theorem cnfExp_injOn {x : Surreal.{u}} {β γ : Ordinal.{u}} (hβ : β < cnfLength x)
    (hγ : γ < cnfLength x) (h : cnfExp x β = cnfExp x γ) : β = γ := by
  rcases lt_trichotomy β γ with hlt | heq | hgt
  · exact absurd h (cnfExp_lt_cnfExp hlt hγ).ne'
  · exact heq
  · exact absurd h (cnfExp_lt_cnfExp hgt hβ).ne

open Classical in
/-- **The normal-form coefficient function**: at an exponent `e = cnfExp x β` with
`β < cnfLength x`, the leading coefficient of the `β`-th residual; `0` elsewhere. -/
def cnfCoeff (x : Surreal.{u}) (e : Surreal.{u}) : ℝ :=
  if h : ∃ β < cnfLength x, cnfExp x β = e then (cnfRes x h.choose).leadingCoeff else 0

theorem cnfCoeff_cnfExp {x : Surreal.{u}} {β : Ordinal.{u}} (hβ : β < cnfLength x) :
    cnfCoeff x (cnfExp x β) = (cnfRes x β).leadingCoeff := by
  have h : ∃ β' < cnfLength x, cnfExp x β' = cnfExp x β := ⟨β, hβ, rfl⟩
  rw [cnfCoeff, dif_pos h]
  have := cnfExp_injOn h.choose_spec.1 hβ h.choose_spec.2
  rw [this]

theorem cnfCoeff_of_not_exists {x : Surreal.{u}} {e : Surreal.{u}}
    (he : ¬ ∃ β < cnfLength x, cnfExp x β = e) : cnfCoeff x e = 0 := by
  rw [cnfCoeff, dif_neg he]

/-- The support of the normal-form coefficient function is the set of exponents below the
length. -/
theorem support_cnfCoeff (x : Surreal.{u}) :
    Function.support (cnfCoeff x) =
      Set.range (fun β : Set.Iio (cnfLength x) ↦ cnfExp x β.1) := by
  ext e
  simp only [Function.mem_support, Set.mem_range]
  constructor
  · intro he
    by_contra hcon
    exact he (cnfCoeff_of_not_exists fun ⟨β, hβ, hβe⟩ ↦ hcon ⟨⟨β, hβ⟩, hβe⟩)
  · rintro ⟨⟨β, hβ⟩, rfl⟩
    rw [cnfCoeff_cnfExp hβ]
    exact leadingCoeff_eq_zero.not.2 (cnfRes_ne_zero_of_lt_cnfLength hβ)

/-- The support is small: it is the image of the small set `Iio (cnfLength x)`. -/
theorem small_support_cnfCoeff (x : Surreal.{u}) :
    Small.{u} (Function.support (cnfCoeff x)) := by
  rw [support_cnfCoeff]
  infer_instance

/-- The support is well-founded for `>`: the exponents decrease along the ordinals. -/
theorem wellFoundedOn_support_cnfCoeff (x : Surreal.{u}) :
    (Function.support (cnfCoeff x)).WellFoundedOn (· > ·) := by
  rw [support_cnfCoeff, Set.wellFoundedOn_range]
  refine Subrelation.wf (fun {a b} h ↦ ?_) wellFounded_lt
  refine lt_of_not_ge fun hab ↦ ?_
  rcases hab.lt_or_eq with hlt | rfl
  · exact lt_asymm h (cnfExp_lt_cnfExp hlt a.2)
  · exact lt_irrefl _ h

/-- **The normal form of `x` as a surreal Hahn series**: coefficient
`leadingCoeff (cnfRes x β)` at the exponent `wlog (cnfRes x β)`, for `β < cnfLength x`. -/
def toHahnSeries (x : Surreal.{u}) : SurrealHahnSeries.{u} :=
  SurrealHahnSeries.mk (cnfCoeff x) (small_support_cnfCoeff x)
    (wellFoundedOn_support_cnfCoeff x)

@[simp]
theorem coeff_toHahnSeries (x : Surreal.{u}) : (toHahnSeries x).coeff = cnfCoeff x :=
  SurrealHahnSeries.coeff_mk _ _ _

theorem support_toHahnSeries (x : Surreal.{u}) :
    (toHahnSeries x).support =
      Set.range (fun β : Set.Iio (cnfLength x) ↦ cnfExp x β.1) := by
  rw [toHahnSeries, SurrealHahnSeries.support_mk]
  exact support_cnfCoeff x

theorem cnfExp_mem_support_toHahnSeries {x : Surreal.{u}} {β : Ordinal.{u}}
    (hβ : β < cnfLength x) : cnfExp x β ∈ (toHahnSeries x).support := by
  rw [support_toHahnSeries]
  exact ⟨⟨β, hβ⟩, rfl⟩

/-- The exponent map `β ↦ cnfExp x β` from `Iio (cnfLength x)` into the support of the
normal-form series. -/
def cnfExpMap (x : Surreal.{u}) (β : Set.Iio (cnfLength x)) : (toHahnSeries x).support :=
  ⟨cnfExp x β.1, cnfExp_mem_support_toHahnSeries β.2⟩

theorem cnfExpMap_bijective (x : Surreal.{u}) : Function.Bijective (cnfExpMap x) := by
  constructor
  · intro a b h
    exact Subtype.ext (cnfExp_injOn a.2 b.2 (congrArg Subtype.val h))
  · rintro ⟨e, he⟩
    obtain ⟨β, hβ⟩ := (Set.ext_iff.1 (support_toHahnSeries x) e).1 he
    exact ⟨β, Subtype.ext hβ⟩

/-- The exponent map is an order isomorphism from `Iio (cnfLength x)` (with `<`) onto the
support of the normal-form series (with `>`). -/
def cnfExpIso (x : Surreal.{u}) :
    (· < · : Set.Iio (cnfLength x) → Set.Iio (cnfLength x) → Prop) ≃r
      (· > · : (toHahnSeries x).support → (toHahnSeries x).support → Prop) :=
  ⟨Equiv.ofBijective (cnfExpMap x) (cnfExpMap_bijective x), fun {a b} ↦ by
    show cnfExp x b.1 < cnfExp x a.1 ↔ a < b
    constructor
    · intro h
      refine lt_of_not_ge fun hab ↦ ?_
      rcases hab.lt_or_eq with hlt | rfl
      · exact lt_asymm h (cnfExp_lt_cnfExp hlt a.2)
      · exact lt_irrefl _ h
    · intro h
      exact cnfExp_lt_cnfExp h b.2⟩

/-- **The length of the normal-form series is the normal-form length.** -/
theorem length_toHahnSeries (x : Surreal.{u}) : (toHahnSeries x).length = cnfLength x := by
  have h1 := (cnfExpIso x).ordinalType_congr
  have h2 : Ordinal.type (· < · : Set.Iio (cnfLength x) → Set.Iio (cnfLength x) → Prop) =
      Ordinal.lift.{u + 1} (cnfLength x) := Ordinal.type_lt_Iio _
  rw [SurrealHahnSeries.type_support, h2] at h1
  exact (Ordinal.lift_inj.1 h1).symm

/-- The inclusion of `Iio α` into the ordinals, as an initial segment. -/
private def iioInitialSeg (α : Ordinal.{u}) :
    @InitialSeg (Set.Iio α) Ordinal.{u} (· < ·) (· < ·) :=
  ⟨⟨⟨Subtype.val, Subtype.val_injective⟩, Iff.rfl⟩, fun a b hb ↦ ⟨⟨b, hb.trans a.2⟩, rfl⟩⟩

/-- The position of `a` in `Iio α` is `a` itself (lifted). -/
private theorem typein_Iio (α : Ordinal.{u}) (a : Set.Iio α) :
    Ordinal.typein (· < · : Set.Iio α → Set.Iio α → Prop) a = Ordinal.lift.{u + 1} a.1 := by
  have h := Ordinal.typein_apply (iioInitialSeg α) a
  rw [← h]
  exact Ordinal.typein_ordinal a.1

/-- The index of the `β`-th normal-form exponent in the normal-form series is `β`. -/
theorem symm_exp_toHahnSeries (x : Surreal.{u}) (a : Set.Iio (cnfLength x)) :
    ((toHahnSeries x).exp.symm (cnfExpMap x a)).1 = a.1 := by
  have h := Ordinal.typein_apply (cnfExpIso x).toInitialSeg a
  rw [SurrealHahnSeries.typein_support, typein_Iio, Ordinal.lift_inj] at h
  exact h

/-- **The exponents of the normal-form series are the normal-form exponents.** -/
theorem exp_toHahnSeries {x : Surreal.{u}} {β : Ordinal.{u}}
    (hβ : β < (toHahnSeries x).length) :
    ((toHahnSeries x).exp ⟨β, hβ⟩).1 = cnfExp x β := by
  have hβ' : β < cnfLength x := length_toHahnSeries x ▸ hβ
  have h1 := symm_exp_toHahnSeries x ⟨β, hβ'⟩
  have h2 : (toHahnSeries x).exp.symm (cnfExpMap x ⟨β, hβ'⟩) = ⟨β, hβ⟩ := Subtype.ext h1
  have h3 := congrArg (toHahnSeries x).exp h2
  rw [RelIso.apply_symm_apply] at h3
  rw [← h3]
  rfl

/-- **The terms of the normal-form series are the normal-form terms**, below the length. -/
theorem term_toHahnSeries {x : Surreal.{u}} {β : Ordinal.{u}} (hβ : β < cnfLength x) :
    (toHahnSeries x).term β = cnfTerm x β := by
  have hβ' : β < (toHahnSeries x).length := (length_toHahnSeries x).symm ▸ hβ
  rw [SurrealHahnSeries.term_of_lt hβ', SurrealHahnSeries.coeffIdx_of_lt hβ',
    coeff_toHahnSeries, exp_toHahnSeries hβ', cnfCoeff_cnfExp hβ]
  rfl

/-- **The evaluation of the normal-form series of `x` is `x`.** -/
theorem evalHahn_toHahnSeries (x : Surreal.{u}) : evalHahn (toHahnSeries x) = x := by
  rw [evalHahn, length_toHahnSeries, hahnSumO_congr fun _ hβ ↦ term_toHahnSeries hβ]
  exact (eq_hahnSumO_cnfTerm x).symm

/-- **`evalHahn` is surjective**: every surreal is the evaluation of a surreal Hahn series —
the Normal Form Theorem in the language of Hahn series. -/
theorem evalHahn_surjective :
    Function.Surjective (evalHahn : SurrealHahnSeries.{u} → Surreal.{u}) :=
  fun x ↦ ⟨toHahnSeries x, evalHahn_toHahnSeries x⟩

/-! ### Uniqueness: every exact canonical-sum representation is the extraction -/

/-- **Term recovery from an exact representation, at every stage.** If `x` *is* the canonical
sum of a strictly dominating monomial series of length `α`, the extraction recovers every term
below `α` — including a final successor term, which `cnfTerm_eq_of_isHahnSumO` (mere Hahn
sums) cannot see. -/
theorem cnfTerm_eq_of_eq_hahnSumO {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    {x : Surreal.{u}} (ht : IsStrictDom t α) (hmon : ∀ β < α, (t β).leadingTerm = t β)
    (hx : x = hahnSumO t α) : ∀ β < α, cnfTerm x β = t β := by
  intro β hβ
  have hx' : IsHahnSumO t α x := hx ▸ isHahnSumO_hahnSumO ht
  have hmon' : ∀ δ, δ + 1 < α → (t δ).leadingTerm = t δ := fun δ hδ ↦
    hmon δ ((lt_add_one_iff.2 le_rfl).trans hδ)
  rcases (add_one_le_iff.2 hβ).lt_or_eq with hβ1 | hβ1
  · exact cnfTerm_eq_of_isHahnSumO ht hmon' hx' β hβ1
  · have hcong : hahnSumO (cnfTerm x) β = hahnSumO t β :=
      hahnSumO_congr fun δ hδ ↦ cnfTerm_eq_of_isHahnSumO ht hmon' hx' δ
        (hβ1 ▸ (add_one_le_iff.2 hδ).trans_lt (lt_add_one_iff.2 le_rfl))
    have hres : cnfRes x β = t β := by
      rw [cnfRes_eq_sub, hcong, hx, ← hβ1, hahnSumO_add_one]
      ring
    rw [cnfTerm, hres, hmon β hβ]

/-- **Uniqueness of the normal form.** If `x` is the canonical sum of a strictly dominating
series of nonzero monomials of length `α`, then `α` is the normal-form length of `x` (and,
by `cnfTerm_eq_of_eq_hahnSumO`, the series is the normal form of `x`). -/
theorem isCNFLength_of_eq_hahnSumO {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    {x : Surreal.{u}} (ht : IsStrictDom t α) (hmon : ∀ β < α, (t β).leadingTerm = t β)
    (h0 : ∀ β < α, t β ≠ 0) (hx : x = hahnSumO t α) : IsCNFLength x α := by
  have hterm := cnfTerm_eq_of_eq_hahnSumO ht hmon hx
  constructor
  · rw [cnfRes_eq_sub, hahnSumO_congr hterm, ← hx, sub_self]
  · intro β hβ hres
    have h := hterm β hβ
    rw [cnfTerm, hres, leadingTerm_zero] at h
    exact h0 β hβ h.symm

theorem cnfLength_eq_of_eq_hahnSumO {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    {x : Surreal.{u}} (ht : IsStrictDom t α) (hmon : ∀ β < α, (t β).leadingTerm = t β)
    (h0 : ∀ β < α, t β ≠ 0) (hx : x = hahnSumO t α) : cnfLength x = α :=
  (isCNFLength_of_eq_hahnSumO ht hmon h0 hx).eq_cnfLength.symm

/-- The value of *every* surreal Hahn series has normal-form length the series' length
(the limit-length case is `isCNFLength_evalHahn` of `CNF.lean`). -/
theorem isCNFLength_evalHahn' (y : SurrealHahnSeries.{u}) :
    IsCNFLength (evalHahn y) y.length :=
  isCNFLength_of_eq_hahnSumO y.isStrictDom_term (fun _ hβ ↦ y.leadingTerm_term hβ)
    (fun _ hβ h ↦ absurd hβ (not_lt.2 (SurrealHahnSeries.term_eq_zero.1 h))) rfl

theorem cnfLength_evalHahn (y : SurrealHahnSeries.{u}) : cnfLength (evalHahn y) = y.length :=
  (isCNFLength_evalHahn' y).eq_cnfLength.symm

/-- The extraction recovers every term of a surreal Hahn series from its value. -/
theorem cnfTerm_evalHahn_of_lt (y : SurrealHahnSeries.{u}) {β : Ordinal.{u}}
    (hβ : β < y.length) : cnfTerm (evalHahn y) β = y.term β :=
  cnfTerm_eq_of_eq_hahnSumO y.isStrictDom_term (fun _ hβ ↦ y.leadingTerm_term hβ) rfl β hβ

/-- The normal-form exponents of a value are the series' exponents. -/
theorem cnfExp_evalHahn (y : SurrealHahnSeries.{u}) {β : Ordinal.{u}} (hβ : β < y.length) :
    cnfExp (evalHahn y) β = (y.exp ⟨β, hβ⟩).1 := by
  have h := cnfTerm_evalHahn_of_lt y hβ
  rw [SurrealHahnSeries.term_of_lt hβ] at h
  have hc : y.coeffIdx β ≠ 0 := fun h0 ↦
    absurd (SurrealHahnSeries.coeffIdx_eq_zero_iff.1 h0) hβ.not_ge
  have h' := congrArg wlog h
  rw [cnfTerm, wlog_leadingTerm, wlog_mul (by simpa using hc) (wpow_pos _).ne', wlog_realCast,
    wlog_wpow, zero_add] at h'
  exact h'

/-- The normal-form coefficients of a value are the series' coefficients (indexed). -/
theorem leadingCoeff_cnfRes_evalHahn (y : SurrealHahnSeries.{u}) {β : Ordinal.{u}}
    (hβ : β < y.length) : (cnfRes (evalHahn y) β).leadingCoeff = y.coeffIdx β := by
  have h := cnfTerm_evalHahn_of_lt y hβ
  rw [SurrealHahnSeries.term_of_lt hβ] at h
  have h' := congrArg leadingCoeff h
  rw [cnfTerm, leadingCoeff_leadingTerm, leadingCoeff_mul, leadingCoeff_realCast,
    leadingCoeff_wpow, mul_one] at h'
  exact h'

/-- **The normal-form coefficient function of a value is the series' coefficient function.** -/
theorem cnfCoeff_evalHahn (y : SurrealHahnSeries.{u}) : cnfCoeff (evalHahn y) = y.coeff := by
  funext e
  by_cases he : e ∈ y.support
  · obtain ⟨j, hj⟩ := SurrealHahnSeries.eq_exp_of_mem_support he
    have hj' : j.1 < y.length := j.2
    have hjl : j.1 < cnfLength (evalHahn y) := (cnfLength_evalHahn y).symm ▸ hj'
    have he' : cnfExp (evalHahn y) j.1 = e := by
      rw [cnfExp_evalHahn y hj']
      exact hj
    calc cnfCoeff (evalHahn y) e
        = cnfCoeff (evalHahn y) (cnfExp (evalHahn y) j.1) := by rw [he']
      _ = (cnfRes (evalHahn y) j.1).leadingCoeff := cnfCoeff_cnfExp hjl
      _ = y.coeffIdx j.1 := leadingCoeff_cnfRes_evalHahn y hj'
      _ = y.coeff (y.exp j) := (y.coeff_exp j).symm
      _ = y.coeff e := by rw [hj]
  · rw [SurrealHahnSeries.mem_support_iff, not_ne_iff] at he
    rw [he]
    refine cnfCoeff_of_not_exists fun ⟨β, hβ, hβe⟩ ↦ ?_
    have hβ' : β < y.length := cnfLength_evalHahn y ▸ hβ
    rw [cnfExp_evalHahn y hβ'] at hβe
    have hmem : e ∈ y.support := hβe ▸ (y.exp ⟨β, hβ'⟩).2
    rw [SurrealHahnSeries.mem_support_iff] at hmem
    exact hmem he

/-- **The normal-form series of a value is the series**: `toHahnSeries` is a left inverse of
`evalHahn`. -/
theorem toHahnSeries_evalHahn (y : SurrealHahnSeries.{u}) : toHahnSeries (evalHahn y) = y :=
  SurrealHahnSeries.ext (by rw [coeff_toHahnSeries, cnfCoeff_evalHahn])

/-- **`evalHahn` is injective** — at every length (the limit-length case is `evalHahn_inj` of
`CNF.lean`). -/
theorem evalHahn_injective :
    Function.Injective (evalHahn : SurrealHahnSeries.{u} → Surreal.{u}) :=
  Function.LeftInverse.injective toHahnSeries_evalHahn

/-- **`evalHahn` is a bijection.** -/
theorem evalHahn_bijective :
    Function.Bijective (evalHahn : SurrealHahnSeries.{u} → Surreal.{u}) :=
  ⟨evalHahn_injective, evalHahn_surjective⟩

/-- **THE NORMAL-FORM CORRESPONDENCE**: surreal Hahn series and surreals are in bijection,
by evaluation (the canonical transfinite sum of the term sequence) and normal-form
extraction. -/
def hahnEquiv : SurrealHahnSeries.{u} ≃ Surreal.{u} where
  toFun := evalHahn
  invFun := toHahnSeries
  left_inv := toHahnSeries_evalHahn
  right_inv := evalHahn_toHahnSeries

@[simp]
theorem hahnEquiv_apply (y : SurrealHahnSeries.{u}) : hahnEquiv y = evalHahn y :=
  rfl

@[simp]
theorem hahnEquiv_symm_apply (x : Surreal.{u}) : hahnEquiv.symm x = toHahnSeries x :=
  rfl

theorem toHahnSeries_injective :
    Function.Injective (toHahnSeries : Surreal.{u} → SurrealHahnSeries.{u}) :=
  Function.LeftInverse.injective evalHahn_toHahnSeries

@[simp]
theorem toHahnSeries_zero : toHahnSeries (0 : Surreal.{u}) = 0 := by
  have h := toHahnSeries_evalHahn (0 : SurrealHahnSeries.{u})
  rwa [evalHahn_zero] at h

/-- The evaluation of the normal-form series is characterized by: `y = toHahnSeries x` iff
`evalHahn y = x`. -/
theorem toHahnSeries_eq_iff {x : Surreal.{u}} {y : SurrealHahnSeries.{u}} :
    toHahnSeries x = y ↔ evalHahn y = x :=
  ⟨fun h ↦ h ▸ evalHahn_toHahnSeries x, fun h ↦ h ▸ toHahnSeries_evalHahn y⟩

end Surreal
