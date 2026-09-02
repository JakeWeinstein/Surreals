import Infinity.Concatenation
import Infinity.CNF

/-!
# Scaling and merging: two more laws of normal-form evaluation

`Infinity.TransfiniteGame` proved that the canonical transfinite sum `hahnSumO` is additive on a
common index set, and `Infinity.Concatenation` proved the concatenation law under coarse
representability. This file adds the two laws Conway's normal-form evaluation needs next on its
way to becoming a ring homomorphism: **scaling** a series by a coarsely representable factor, and
the **merge** — additivity of the Hahn-series evaluation `evalHahn` for arbitrary supports.

* **THE SCALING THEOREM** `Surreal.hahnSumO_const_mul`: for `t` strictly dominating below `α` and
  `m ≠ 0` coarsely representable at its own class (`CoarseRep m (mk m)`),
  `hahnSumO (fun β ↦ m * t β) α = m * hahnSumO t α`. Proof: transfinite induction on `α`; at a
  limit stage the identification engine is applied to the Conway *product* of a coarse
  representative `G_m` of `m` and the transfinite option game of `t`. Each option of the product
  is `m·S ∓ (m − a)(S − b)` with `a` an option of `G_m` and `b` an option of the option game, and
  the displacement has class `mk (m − a) + mk (S − b) ≤ mk m + mk (t β) = mk (m · t β)`, so it is
  beaten at stage `β + 1`. Corollaries: `hahnSumO_monomial_mul` (every monomial `c · ω^ z`),
  `hahnSumO_wpow_mul`, `hahnSumO_realCast_mul`, `hahnSumO_neg`.
* **Truncation is the canonical partial sum** `Surreal.evalHahn_trunc_eq_hahnSumO` /
  `Surreal.evalHahn_truncIdx`: `evalHahn (x.trunc e) = hahnSumO x.term (x.trunc e).length` and
  `evalHahn (x.truncIdx i) = hahnSumO x.term (min i x.length)` — the "truncation = partial sum"
  bridge anticipated in `Infinity.NormalForm`. The bookkeeping is the initial-segment lemma
  `SurrealHahnSeries.exp_trunc_eq` (the exponent enumeration of a truncation is a prefix of the
  original's, via `typein_apply` on the inclusion `InitialSeg`), `term_trunc_eq`, and
  `exp_length_trunc_le` (the first omitted exponent is `≤ e`).
* **The residual at a truncation** `Surreal.mk_wpow_le_mk_evalHahn_sub_trunc`:
  `mk (ω^ e) ≤ mk (evalHahn x − evalHahn (x.trunc e))`, and **the append law**
  `Surreal.evalHahn_eq_trunc_add_of_lowerBound`: if every exponent of `x` is `≥ e`, then
  `evalHahn x = evalHahn (x.trunc e) + x.coeff e · ω^ e`; hence `Surreal.evalHahn_single`
  (`evalHahn (single e c) = c · ω^ e`).
* **Termwise coarse representability** `Surreal.TermRep X T`: `X` is the value of a numeric game
  each of whose options sits at a distance of class `≤ c` for some `c ∈ T`. Closure under sums
  and the induction `termRep_hahnSumO` (canonical sums of every length, at the set of their
  terms' classes), and `termRep_evalHahn` for Hahn series.
* **THE MERGE THEOREM** `Surreal.evalHahn_add`: for surreal Hahn series `x, y` with no
  coefficient cancellation (`x.coeff i + y.coeff i = 0 → x.coeff i = 0 ∧ y.coeff i = 0`),
  `evalHahn (x + y) = evalHahn x + evalHahn y`, for *arbitrary* supports. Proof: transfinite
  induction over the stages `γ ≤ (x + y).length` of the merged series, proving
  `hahnSumO (x + y).term γ = evalHahn (x ⇂ γ) + evalHahn (y ⇂ γ)` where `x ⇂ γ` is `x` truncated
  along the `γ`-th merged exponent. Successor stages are the append law; at a limit stage the
  identification engine is applied to the Conway sum of termwise-coarse representatives of the
  two truncated evaluations, each option being beaten at the merged stage following the term it
  is coarse against. The stage-by-stage statement is
  `Surreal.hahnSumO_term_eq_evalHahn_truncAlong_add`; corollary
  `Surreal.evalHahn_add_of_disjoint_support`.
* **THE SPLIT LAW** `Surreal.evalHahn_eq_trunc_add_sub_trunc`:
  `evalHahn x = evalHahn (x.trunc e) + evalHahn (x − x.trunc e)` for every exponent `e` — the
  restatement of the concatenation theorem for the library's Hahn series, obtained from the merge
  (the two pieces have disjoint supports); `Surreal.evalHahn_sub_trunc` reads it as the value of
  the tail.

Everything is the game-cofinality method of `Infinity.GameCofinality`, `Infinity.TransfiniteGame`
and `Infinity.Concatenation`; no birthday census is used.
-/

open ArchimedeanClass IGame Order

universe u

noncomputable section

namespace Surreal

/-! ### Scaling a strictly dominating series by a constant -/

/-- The class of a nonzero surreal is not `⊤`. -/
theorem mk_ne_top_of_ne_zero {m : Surreal.{u}} (hm : m ≠ 0) : ArchimedeanClass.mk m ≠ ⊤ :=
  fun h ↦ hm (ArchimedeanClass.mk_eq_top_iff.1 h)

/-- Multiplying a strictly dominating series by a nonzero constant keeps it strictly
dominating (the class of every term shifts by `mk m`). -/
theorem IsStrictDom.const_mul {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    (ht : IsStrictDom t α) {m : Surreal.{u}} (hm : m ≠ 0) :
    IsStrictDom (fun β ↦ m * t β) α := by
  intro β γ hβγ hγ
  dsimp only
  rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul]
  exact (add_lt_add_iff_right_of_ne_top (mk_ne_top_of_ne_zero hm)).2 (ht hβγ hγ)

private theorem hahnSumO_const_mul_aux (t : Ordinal.{u} → Surreal.{u}) (m : Surreal.{u})
    (hm : m ≠ 0) (hrep : CoarseRep m (ArchimedeanClass.mk m)) (α : Ordinal.{u}) :
    IsStrictDom t α → hahnSumO (fun β ↦ m * t β) α = m * hahnSumO t α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro _
    rw [hahnSumO_zero, hahnSumO_zero, mul_zero]
  | add_one δ ih =>
    intro ht
    have hδ : δ < δ + 1 := lt_add_one_iff.2 le_rfl
    rw [hahnSumO_add_one, hahnSumO_add_one, ih (ht.mono hδ.le), mul_add]
  | limit γ hγ ih =>
    intro ht
    have hmtop : ArchimedeanClass.mk m ≠ ⊤ := mk_ne_top_of_ne_zero hm
    have hV : ∀ β < γ, hahnSumO (fun β ↦ m * t β) β = m * hahnSumO t β :=
      fun β hβ ↦ ih β hβ (ht.mono hβ.le)
    have hmt : IsStrictDom (fun β ↦ m * t β) γ := ht.const_mul hm
    have hS : IsHahnSumO t γ (hahnSumO t γ) := isHahnSumO_hahnSumO ht
    obtain ⟨Gm, hGmn, hGm, hGml, hGmr⟩ := hrep
    haveI := hGmn
    haveI := numeric_optionGameO hγ ht
    -- The value `m · S` is a Hahn sum of the scaled series: by the induction hypothesis the
    -- scaled partial sums are `m · S_β`, so the residual is `m · (S − S_β)`.
    have hP : IsHahnSumO (fun β ↦ m * t β) γ (m * hahnSumO t γ) := by
      intro β hβ
      rw [hV β hβ, ← mul_sub]
      show ArchimedeanClass.mk (m * t β) ≤
        ArchimedeanClass.mk (m * (hahnSumO t γ - hahnSumO t β))
      rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul]
      exact add_le_add le_rfl (hS β hβ)
    have hG : Surreal.mk (Gm * optionGameO t γ) = m * hahnSumO t γ := by
      rw [Surreal.mk_mul, hGm, mk_optionGameO_eq_hahnSumO hγ ht]
    rw [← hG]
    refine hahnSumO_eq_of_isHahnSumO_of_moves_le hγ hmt (by rwa [hG]) ?_ ?_
    · -- left options of the product: both-left or both-right pairs
      rw [forall_moves_mul]
      intro p a ha b hb
      cases p with
      | left =>
        rw [Player.left_mul] at hb
        rw [leftMoves_optionGameO] at hb
        obtain ⟨⟨β, hβ⟩, rfl⟩ := hb
        haveI := IGame.Numeric.of_mem_moves ha
        have hβ1 : β + 1 < γ := hγ.add_one_lt_of_ordinal hβ
        refine ⟨β + 1, hβ1, ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, mk_mulOption, out_eq, mk_optionGameO_eq_hahnSumO hγ ht,
          hGm]
        have hapos : 0 < m - Surreal.mk a := by
          rw [sub_pos, ← hGm]
          exact Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt ha)
        obtain ⟨hbpos, hbmk⟩ := sub_optLoO_pos_mk_eq ht hS hβ1
        have hDpos : 0 < (m - Surreal.mk a) * (hahnSumO t γ - optLoO t β) := mul_pos hapos hbpos
        have hDmk : ArchimedeanClass.mk ((m - Surreal.mk a) * (hahnSumO t γ - optLoO t β)) <
            ArchimedeanClass.mk (m * t (β + 1)) := by
          rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, hbmk]
          exact (add_le_add (hGml a ha) le_rfl).trans_lt
            ((add_lt_add_iff_right_of_ne_top hmtop).2 (ht (lt_add_one_iff.2 le_rfl) hβ1))
        have key := sub_le_optLoO_of_mk_lt hmt hP hDpos (hγ.add_one_lt_of_ordinal hβ1) hDmk
        rw [show Surreal.mk a * hahnSumO t γ + m * optLoO t β - Surreal.mk a * optLoO t β =
          m * hahnSumO t γ - (m - Surreal.mk a) * (hahnSumO t γ - optLoO t β) by ring]
        exact key
      | right =>
        rw [Player.right_mul, Player.neg_left] at hb
        rw [rightMoves_optionGameO] at hb
        obtain ⟨⟨β, hβ⟩, rfl⟩ := hb
        haveI := IGame.Numeric.of_mem_moves ha
        have hβ1 : β + 1 < γ := hγ.add_one_lt_of_ordinal hβ
        refine ⟨β + 1, hβ1, ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, mk_mulOption, out_eq, mk_optionGameO_eq_hahnSumO hγ ht,
          hGm]
        have hapos : 0 < Surreal.mk a - m := by
          rw [sub_pos, ← hGm]
          exact Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right ha)
        obtain ⟨hbpos, hbmk⟩ := optHiO_sub_pos_mk_eq ht hS hβ1
        have hDpos : 0 < (Surreal.mk a - m) * (optHiO t β - hahnSumO t γ) := mul_pos hapos hbpos
        have hDmk : ArchimedeanClass.mk ((Surreal.mk a - m) * (optHiO t β - hahnSumO t γ)) <
            ArchimedeanClass.mk (m * t (β + 1)) := by
          rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, hbmk]
          exact (add_le_add (hGmr a ha) le_rfl).trans_lt
            ((add_lt_add_iff_right_of_ne_top hmtop).2 (ht (lt_add_one_iff.2 le_rfl) hβ1))
        have key := sub_le_optLoO_of_mk_lt hmt hP hDpos (hγ.add_one_lt_of_ordinal hβ1) hDmk
        rw [show Surreal.mk a * hahnSumO t γ + m * optHiO t β - Surreal.mk a * optHiO t β =
          m * hahnSumO t γ - (Surreal.mk a - m) * (optHiO t β - hahnSumO t γ) by ring]
        exact key
    · -- right options of the product: mixed pairs
      rw [forall_moves_mul]
      intro p a ha b hb
      cases p with
      | left =>
        rw [Player.left_mul] at hb
        rw [rightMoves_optionGameO] at hb
        obtain ⟨⟨β, hβ⟩, rfl⟩ := hb
        haveI := IGame.Numeric.of_mem_moves ha
        have hβ1 : β + 1 < γ := hγ.add_one_lt_of_ordinal hβ
        refine ⟨β + 1, hβ1, ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, mk_mulOption, out_eq, mk_optionGameO_eq_hahnSumO hγ ht,
          hGm]
        have hapos : 0 < m - Surreal.mk a := by
          rw [sub_pos, ← hGm]
          exact Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt ha)
        obtain ⟨hbpos, hbmk⟩ := optHiO_sub_pos_mk_eq ht hS hβ1
        have hDpos : 0 < (m - Surreal.mk a) * (optHiO t β - hahnSumO t γ) := mul_pos hapos hbpos
        have hDmk : ArchimedeanClass.mk ((m - Surreal.mk a) * (optHiO t β - hahnSumO t γ)) <
            ArchimedeanClass.mk (m * t (β + 1)) := by
          rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, hbmk]
          exact (add_le_add (hGml a ha) le_rfl).trans_lt
            ((add_lt_add_iff_right_of_ne_top hmtop).2 (ht (lt_add_one_iff.2 le_rfl) hβ1))
        have key := optHiO_le_add_of_mk_lt hmt hP hDpos (hγ.add_one_lt_of_ordinal hβ1) hDmk
        rw [show Surreal.mk a * hahnSumO t γ + m * optHiO t β - Surreal.mk a * optHiO t β =
          m * hahnSumO t γ + (m - Surreal.mk a) * (optHiO t β - hahnSumO t γ) by ring]
        exact key
      | right =>
        rw [Player.right_mul, Player.neg_right] at hb
        rw [leftMoves_optionGameO] at hb
        obtain ⟨⟨β, hβ⟩, rfl⟩ := hb
        haveI := IGame.Numeric.of_mem_moves ha
        have hβ1 : β + 1 < γ := hγ.add_one_lt_of_ordinal hβ
        refine ⟨β + 1, hβ1, ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, mk_mulOption, out_eq, mk_optionGameO_eq_hahnSumO hγ ht,
          hGm]
        have hapos : 0 < Surreal.mk a - m := by
          rw [sub_pos, ← hGm]
          exact Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right ha)
        obtain ⟨hbpos, hbmk⟩ := sub_optLoO_pos_mk_eq ht hS hβ1
        have hDpos : 0 < (Surreal.mk a - m) * (hahnSumO t γ - optLoO t β) := mul_pos hapos hbpos
        have hDmk : ArchimedeanClass.mk ((Surreal.mk a - m) * (hahnSumO t γ - optLoO t β)) <
            ArchimedeanClass.mk (m * t (β + 1)) := by
          rw [ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul, hbmk]
          exact (add_le_add (hGmr a ha) le_rfl).trans_lt
            ((add_lt_add_iff_right_of_ne_top hmtop).2 (ht (lt_add_one_iff.2 le_rfl) hβ1))
        have key := optHiO_le_add_of_mk_lt hmt hP hDpos (hγ.add_one_lt_of_ordinal hβ1) hDmk
        rw [show Surreal.mk a * hahnSumO t γ + m * optLoO t β - Surreal.mk a * optLoO t β =
          m * hahnSumO t γ + (Surreal.mk a - m) * (hahnSumO t γ - optLoO t β) by ring]
        exact key

/-- **THE SCALING THEOREM**: for a series `t` strictly dominating below `α` and a nonzero factor
`m` coarsely representable at its own class, the canonical transfinite sum of the scaled series
`β ↦ m · t β` is `m` times the canonical sum:
`hahnSumO (fun β ↦ m * t β) α = m * hahnSumO t α`.

Proof: transfinite induction on `α`. Zero and successor stages are algebra. At a limit stage
`γ` the identification engine is applied to the Conway product `G_m * optionGameO t γ` of a
coarse representative of `m` and the transfinite option game: its value `m · S_γ` is a Hahn sum
of the scaled series (the residual at stage `β` is `m · (S_γ − S_β)`), and every option is
`m · S_γ ∓ (m − a)(S_γ − b)` with `mk (m − a) ≤ mk m` and `mk (S_γ − b) = mk (t β)`, so the
displacement is coarser than the scaled term `m · t (β + 1)` and the option is beaten at stage
`β + 1`. -/
theorem hahnSumO_const_mul {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    (ht : IsStrictDom t α) {m : Surreal.{u}} (hm : m ≠ 0)
    (hrep : CoarseRep m (ArchimedeanClass.mk m)) :
    hahnSumO (fun β ↦ m * t β) α = m * hahnSumO t α :=
  hahnSumO_const_mul_aux t m hm hrep α ht

/-- **Scaling by a monomial**: for every nonzero real `c` and every surreal `z`,
`hahnSumO (fun β ↦ c · ω^ z · t β) α = c · ω^ z · hahnSumO t α`. -/
theorem hahnSumO_monomial_mul {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    (ht : IsStrictDom t α) {c : ℝ} (hc : c ≠ 0) (z : Surreal.{u}) :
    hahnSumO (fun β ↦ (c : Surreal.{u}) * ω^ z * t β) α =
      (c : Surreal.{u}) * ω^ z * hahnSumO t α := by
  have hne : (c : Surreal.{u}) * ω^ z ≠ 0 :=
    mul_ne_zero (by simpa using hc) (wpow_pos z).ne'
  refine hahnSumO_const_mul ht hne ?_
  have hmk : ArchimedeanClass.mk ((c : Surreal.{u}) * ω^ z) = ArchimedeanClass.mk (ω^ z) := by
    rw [ArchimedeanClass.mk_mul, mk_realCast hc, zero_add]
  rw [hmk]
  exact coarseRep_monomial c z

/-- **Scaling by an `ω`-power**. -/
theorem hahnSumO_wpow_mul {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    (ht : IsStrictDom t α) (z : Surreal.{u}) :
    hahnSumO (fun β ↦ ω^ z * t β) α = ω^ z * hahnSumO t α :=
  hahnSumO_const_mul ht (wpow_pos z).ne' (CoarseRep.wpow z)

/-- **Scaling by a nonzero real**. -/
theorem hahnSumO_realCast_mul {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    (ht : IsStrictDom t α) {c : ℝ} (hc : c ≠ 0) :
    hahnSumO (fun β ↦ (c : Surreal.{u}) * t β) α = (c : Surreal.{u}) * hahnSumO t α := by
  have hne : (c : Surreal.{u}) ≠ 0 := by simpa using hc
  refine hahnSumO_const_mul ht hne ?_
  rw [mk_realCast hc]
  exact coarseRep_realCast c

/-- **Negation**: the canonical sum of the negated series is the negated canonical sum. -/
theorem hahnSumO_neg {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    (ht : IsStrictDom t α) :
    hahnSumO (fun β ↦ -t β) α = -hahnSumO t α := by
  have h := hahnSumO_realCast_mul ht (c := -1) (by norm_num)
  have e : ∀ s : Surreal.{u}, ((-1 : ℝ) : Surreal.{u}) * s = -s := by
    intro s
    rw [Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul]
  simp only [e] at h
  exact h

end Surreal

/-! ### Truncations of surreal Hahn series: the prefix bookkeeping

The support of a truncation `x.trunc e` (exponents `> e`) is an *initial segment* of the support of
`x` in the decreasing order, so its exponent enumeration is a prefix of the original's. The
bookkeeping below turns this into "truncation = canonical partial sum". -/

namespace SurrealHahnSeries

open Ordinal

variable {x : SurrealHahnSeries.{u}}

/-- The inclusion of the support of a truncation into the support, as a relation embedding for
the decreasing order. -/
private def truncEmb (x : SurrealHahnSeries.{u}) (e : Surreal.{u}) :
    @RelEmbedding (x.trunc e).support x.support (· > ·) (· > ·) :=
  ⟨⟨fun a ↦ ⟨a.1, support_trunc_subset x e a.2⟩,
    fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h)⟩, Iff.rfl⟩

/-- The inclusion of the support of a truncation is an *initial segment* for the decreasing
order: anything larger than an exponent `> e` is itself `> e`. -/
private def truncInitialSeg (x : SurrealHahnSeries.{u}) (e : Surreal.{u}) :
    @InitialSeg (x.trunc e).support x.support (· > ·) (· > ·) :=
  ⟨truncEmb x e, fun a b hb ↦ by
    have hab : a.1 < b.1 := hb
    have ha : e < a.1 := ((Set.ext_iff.1 (support_trunc x e) a.1).1 a.2).2
    refine ⟨⟨b.1, ?_⟩, rfl⟩
    rw [support_trunc]
    exact ⟨b.2, ha.trans hab⟩⟩

/-- **The position of an exponent of a truncation is its position in the original series.** -/
theorem typein_trunc_eq (x : SurrealHahnSeries.{u}) (e : Surreal.{u}) (a : (x.trunc e).support) :
    typein (· > · : x.support → x.support → Prop) ⟨a.1, support_trunc_subset x e a.2⟩ =
      typein (· > · : (x.trunc e).support → (x.trunc e).support → Prop) a :=
  typein_apply (truncInitialSeg x e) a

/-- The index of an exponent of a truncation, in the truncation and in the original. -/
theorem symm_exp_trunc_eq (x : SurrealHahnSeries.{u}) (e : Surreal.{u}) (a : (x.trunc e).support) :
    (x.exp.symm ⟨a.1, support_trunc_subset x e a.2⟩).1 = ((x.trunc e).exp.symm a).1 := by
  have h := typein_trunc_eq x e a
  rwa [typein_support, typein_support, lift_inj] at h

theorem length_trunc_le (x : SurrealHahnSeries.{u}) (e : Surreal.{u}) :
    (x.trunc e).length ≤ x.length :=
  length_mono (support_trunc_subset x e)

/-- **The exponent enumeration of a truncation is a prefix of the original's.** -/
theorem exp_trunc_eq (x : SurrealHahnSeries.{u}) (e : Surreal.{u}) {j : Ordinal.{u}}
    (hj : j < (x.trunc e).length) :
    ((x.trunc e).exp ⟨j, hj⟩).1 =
      (x.exp ⟨j, hj.trans_le (length_trunc_le x e)⟩).1 := by
  have h1 := symm_exp_trunc_eq x e ((x.trunc e).exp ⟨j, hj⟩)
  rw [RelIso.symm_apply_apply] at h1
  have h3 : x.exp.symm ⟨((x.trunc e).exp ⟨j, hj⟩).1,
      support_trunc_subset x e ((x.trunc e).exp ⟨j, hj⟩).2⟩ =
      ⟨j, hj.trans_le (length_trunc_le x e)⟩ := Subtype.ext h1
  have h4 := congrArg x.exp h3
  rw [RelIso.apply_symm_apply] at h4
  rw [← h4]

/-- Every exponent of `x.trunc e` is `> e`. -/
theorem lt_exp_trunc (x : SurrealHahnSeries.{u}) (e : Surreal.{u}) {j : Ordinal.{u}}
    (hj : j < (x.trunc e).length) : e < ((x.trunc e).exp ⟨j, hj⟩).1 :=
  ((Set.ext_iff.1 (support_trunc x e) _).1 ((x.trunc e).exp ⟨j, hj⟩).2).2

/-- **The terms of a truncation are the terms of the original**, below the truncation's
length. -/
theorem term_trunc_eq (x : SurrealHahnSeries.{u}) (e : Surreal.{u}) {j : Ordinal.{u}}
    (hj : j < (x.trunc e).length) : (x.trunc e).term j = x.term j := by
  have hj' : j < x.length := hj.trans_le (length_trunc_le x e)
  have he : e < (x.exp ⟨j, hj'⟩).1 := by
    have h := lt_exp_trunc x e hj
    rwa [exp_trunc_eq x e hj] at h
  rw [term_of_lt hj, term_of_lt hj', coeffIdx_of_lt hj, coeffIdx_of_lt hj', exp_trunc_eq x e hj,
    coeff_trunc_of_lt he]

/-- **The first omitted exponent of a truncation is `≤ e`**: if the truncation is shorter than
the series, the exponent at its length is not `> e`. -/
theorem exp_length_trunc_le (x : SurrealHahnSeries.{u}) (e : Surreal.{u})
    (h : (x.trunc e).length < x.length) : (x.exp ⟨(x.trunc e).length, h⟩).1 ≤ e := by
  by_contra hlt
  rw [not_le] at hlt
  have hmem : (x.exp ⟨(x.trunc e).length, h⟩).1 ∈ (x.trunc e).support := by
    rw [support_trunc]
    exact ⟨(x.exp ⟨(x.trunc e).length, h⟩).2, hlt⟩
  have h1 := symm_exp_trunc_eq x e ⟨_, hmem⟩
  have h2 : (⟨(x.exp ⟨(x.trunc e).length, h⟩).1, support_trunc_subset x e hmem⟩ : x.support) =
      x.exp ⟨(x.trunc e).length, h⟩ := rfl
  rw [h2, RelIso.symm_apply_apply] at h1
  have h3 := symm_exp_lt (x := x.trunc e) ⟨_, hmem⟩
  rw [← h1] at h3
  exact lt_irrefl _ h3

/-- The support of a Hahn series with a lower bound `e` in the support: the length is one more
than the length of the truncation at `e`. -/
theorem length_eq_length_trunc_add_one (x : SurrealHahnSeries.{u}) {e : Surreal.{u}}
    (he : e ∈ x.support) (hlb : ∀ s ∈ x.support, e ≤ s) :
    x.length = (x.trunc e).length + 1 := by
  have hlt := length_trunc_lt he
  have hexp : (x.exp ⟨_, hlt⟩).1 = e :=
    le_antisymm (exp_length_trunc_le x e hlt) (hlb _ (x.exp _).2)
  apply le_antisymm
  · refine le_of_forall_lt fun j hj ↦ ?_
    rw [lt_add_one_iff]
    have h1 : x.exp ⟨(x.trunc e).length, hlt⟩ ≤ x.exp ⟨j, hj⟩ := by
      refine Subtype.coe_le_coe.1 ?_
      rw [hexp]
      exact hlb _ (x.exp ⟨j, hj⟩).2
    exact Subtype.coe_le_coe.2 (exp_le_exp_iff.1 h1)
  · exact add_one_le_iff.2 hlt

/-- The last term of a series whose support has minimum `e` is `x.coeff e · ω^ e`, at index
`(x.trunc e).length`. -/
theorem term_length_trunc_eq (x : SurrealHahnSeries.{u}) {e : Surreal.{u}}
    (he : e ∈ x.support) (hlb : ∀ s ∈ x.support, e ≤ s) :
    x.term (x.trunc e).length = (x.coeff e : Surreal.{u}) * ω^ e := by
  have hlt := length_trunc_lt he
  have hexp : (x.exp ⟨_, hlt⟩).1 = e :=
    le_antisymm (exp_length_trunc_le x e hlt) (hlb _ (x.exp _).2)
  rw [term_of_lt hlt, coeffIdx_of_lt hlt, hexp]

end SurrealHahnSeries

namespace Surreal

open SurrealHahnSeries in
/-- **Truncation is the canonical partial sum**: the evaluation of `x.trunc e` is the canonical
partial sum of `x`'s term sequence at the truncation's length. -/
theorem evalHahn_trunc_eq_hahnSumO (x : SurrealHahnSeries.{u}) (e : Surreal.{u}) :
    evalHahn (x.trunc e) = hahnSumO x.term (x.trunc e).length := by
  unfold evalHahn
  exact hahnSumO_congr fun j hj ↦ term_trunc_eq x e hj

open SurrealHahnSeries in
/-- **Index truncation is the canonical partial sum**:
`evalHahn (x.truncIdx i) = hahnSumO x.term (min i x.length)` — the "truncation = partial sum"
bridge anticipated in `Infinity.NormalForm`. -/
theorem evalHahn_truncIdx (x : SurrealHahnSeries.{u}) (i : Ordinal.{u}) :
    evalHahn (x.truncIdx i) = hahnSumO x.term (min i x.length) := by
  rcases lt_or_ge i x.length with h | h
  · rw [truncIdx_of_lt h, evalHahn_trunc_eq_hahnSumO, trunc_exp, length_truncIdx]
  · rw [truncIdx_of_le h, min_eq_right h]
    rfl

open SurrealHahnSeries in
/-- **The residual at a truncation**: the evaluation of `x` differs from the evaluation of its
truncation at `e` by a quantity dominated by `ω^ e` (the first omitted exponent is `≤ e`). -/
theorem mk_wpow_le_mk_evalHahn_sub_trunc (x : SurrealHahnSeries.{u}) (e : Surreal.{u}) :
    ArchimedeanClass.mk (ω^ e) ≤ ArchimedeanClass.mk (evalHahn x - evalHahn (x.trunc e)) := by
  rw [evalHahn_trunc_eq_hahnSumO]
  rcases (length_trunc_le x e).eq_or_lt with heq | hlt
  · rw [heq, show evalHahn x = hahnSumO x.term x.length from rfl, sub_self,
      show ArchimedeanClass.mk (0 : Surreal.{u}) = ⊤ from ArchimedeanClass.mk_eq_top_iff.2 rfl]
    exact le_top
  · refine le_trans ?_ (isHahnSumO_evalHahn x _ hlt)
    rw [term_of_lt hlt, ArchimedeanClass.mk_mul, mk_realCast (coeffIdx_ne_zero hlt), zero_add]
    exact archimedeanClassMk_wpow_strictAnti.antitone (exp_length_trunc_le x e hlt)

open SurrealHahnSeries in
/-- **The append law**: if every exponent of `x` is `≥ e`, then
`evalHahn x = evalHahn (x.trunc e) + x.coeff e · ω^ e` (with `x.coeff e = 0` allowed). -/
theorem evalHahn_eq_trunc_add_of_lowerBound (x : SurrealHahnSeries.{u}) {e : Surreal.{u}}
    (hlb : ∀ s ∈ x.support, e ≤ s) :
    evalHahn x = evalHahn (x.trunc e) + (x.coeff e : Surreal.{u}) * ω^ e := by
  by_cases he : e ∈ x.support
  · rw [evalHahn_trunc_eq_hahnSumO, ← term_length_trunc_eq x he hlb, ← hahnSumO_add_one,
      ← length_eq_length_trunc_add_one x he hlb]
    rfl
  · rw [mem_support_iff, not_ne_iff] at he
    rw [he, Real.toSurreal_zero, zero_mul, add_zero,
      trunc_eq_self fun s hs ↦ lt_of_le_of_ne (hlb s hs) fun h ↦ mem_support_iff.1 hs (h ▸ he)]

open SurrealHahnSeries in
/-- **Monomials evaluate to monomials**: `evalHahn (single e c) = c · ω^ e`. -/
theorem evalHahn_single (e : Surreal.{u}) (c : ℝ) :
    evalHahn (single e c) = (c : Surreal.{u}) * ω^ e := by
  have hlb : ∀ s ∈ (single e c).support, e ≤ s := fun s hs ↦
    (Set.mem_singleton_iff.1 (support_single_subset hs)).ge
  rw [evalHahn_eq_trunc_add_of_lowerBound _ hlb, trunc_single_of_le le_rfl, evalHahn_zero,
    zero_add, coeff_single_self]

/-! ### Termwise coarse representability

`CoarseRep X c` asks every option of a representative to sit at distance not finer than one fixed
class `c`. For the merge we need the sharper form where each option is only required to be not
finer than *some* term of a series — the classes may accumulate. -/

/-- **Termwise coarse representability**: `X` is the value of a numeric game each of whose
options differs from `X` by an amount whose class is `≤ c` for some `c ∈ T` (not finer than some
class in `T`). -/
def TermRep (X : Surreal.{u}) (T : Set (ArchimedeanClass Surreal.{u})) : Prop :=
  ∃ G : IGame.{u}, ∃ _ : G.Numeric, Surreal.mk G = X ∧
    (∀ a ∈ Gᴸ, ∀ [a.Numeric], ∃ c ∈ T, ArchimedeanClass.mk (X - Surreal.mk a) ≤ c) ∧
    (∀ b ∈ Gᴿ, ∀ [b.Numeric], ∃ c ∈ T, ArchimedeanClass.mk (Surreal.mk b - X) ≤ c)

/-- A coarse representative at `c ∈ T` is a termwise coarse representative at `T`. -/
theorem CoarseRep.termRep {X : Surreal.{u}} {c : ArchimedeanClass Surreal.{u}}
    (h : CoarseRep X c) {T : Set (ArchimedeanClass Surreal.{u})} (hc : c ∈ T) : TermRep X T := by
  obtain ⟨G, hG, hGX, hl, hr⟩ := h
  exact ⟨G, hG, hGX, fun a ha _ ↦ ⟨c, hc, hl a ha⟩, fun b hb _ ↦ ⟨c, hc, hr b hb⟩⟩

theorem TermRep.mono {X : Surreal.{u}} {T T' : Set (ArchimedeanClass Surreal.{u})}
    (h : TermRep X T) (hT : T ⊆ T') : TermRep X T' := by
  obtain ⟨G, hG, hGX, hl, hr⟩ := h
  refine ⟨G, hG, hGX, fun a ha _ ↦ ?_, fun b hb _ ↦ ?_⟩
  · obtain ⟨c, hc, h⟩ := hl a ha
    exact ⟨c, hT hc, h⟩
  · obtain ⟨c, hc, h⟩ := hr b hb
    exact ⟨c, hT hc, h⟩

theorem termRep_zero (T : Set (ArchimedeanClass Surreal.{u})) : TermRep (0 : Surreal.{u}) T := by
  refine ⟨0, inferInstance, rfl, ?_, ?_⟩
  · intro a ha
    simp at ha
  · intro b hb
    simp at hb

/-- **Sums**: termwise coarse representatives add (the Conway sum game). -/
theorem TermRep.add {X Y : Surreal.{u}} {T : Set (ArchimedeanClass Surreal.{u})}
    (hX : TermRep X T) (hY : TermRep Y T) : TermRep (X + Y) T := by
  obtain ⟨G, hG, hGX, hGl, hGr⟩ := hX
  obtain ⟨H, hH, hHY, hHl, hHr⟩ := hY
  refine ⟨G + H, inferInstance, by rw [Surreal.mk_add, hGX, hHY], ?_, ?_⟩
  · rw [forall_moves_add]
    constructor
    · intro a ha _
      haveI := IGame.Numeric.of_mem_moves ha
      rw [Surreal.mk_add, hHY, show X + Y - (Surreal.mk a + Y) = X - Surreal.mk a by ring]
      exact hGl a ha
    · intro b hb _
      haveI := IGame.Numeric.of_mem_moves hb
      rw [Surreal.mk_add, hGX, show X + Y - (X + Surreal.mk b) = Y - Surreal.mk b by ring]
      exact hHl b hb
  · rw [forall_moves_add]
    constructor
    · intro a ha _
      haveI := IGame.Numeric.of_mem_moves ha
      rw [Surreal.mk_add, hHY, show Surreal.mk a + Y - (X + Y) = Surreal.mk a - X by ring]
      exact hGr a ha
    · intro b hb _
      haveI := IGame.Numeric.of_mem_moves hb
      rw [Surreal.mk_add, hGX, show X + Surreal.mk b - (X + Y) = Surreal.mk b - Y by ring]
      exact hHr b hb

/-- **Limit-stage canonical sums are termwise coarsely representable** at any set containing
the classes of all the terms: the transfinite option game's option at stage `β` sits at distance
of class exactly `mk (t β)`. -/
theorem termRep_hahnSumO_of_isSuccLimit {t : Ordinal.{u} → Surreal.{u}} {γ : Ordinal.{u}}
    (hγ : IsSuccLimit γ) (ht : IsStrictDom t γ) {T : Set (ArchimedeanClass Surreal.{u})}
    (hT : ∀ β < γ, ArchimedeanClass.mk (t β) ∈ T) : TermRep (hahnSumO t γ) T := by
  haveI := numeric_optionGameO hγ ht
  have hS : IsHahnSumO t γ (hahnSumO t γ) := isHahnSumO_hahnSumO ht
  refine ⟨optionGameO t γ, inferInstance, mk_optionGameO_eq_hahnSumO hγ ht, ?_, ?_⟩
  · intro a ha _
    rw [leftMoves_optionGameO] at ha
    obtain ⟨⟨β, hβ⟩, rfl⟩ := ha
    refine ⟨_, hT β hβ, le_of_eq ?_⟩
    rw [out_eq, (sub_optLoO_pos_mk_eq ht hS (hγ.add_one_lt_of_ordinal hβ)).2]
  · intro b hb _
    rw [rightMoves_optionGameO] at hb
    obtain ⟨⟨β, hβ⟩, rfl⟩ := hb
    refine ⟨_, hT β hβ, le_of_eq ?_⟩
    rw [out_eq, (optHiO_sub_pos_mk_eq ht hS (hγ.add_one_lt_of_ordinal hβ)).2]

private theorem termRep_hahnSumO_aux (t : Ordinal.{u} → Surreal.{u})
    (T : Set (ArchimedeanClass Surreal.{u})) (α : Ordinal.{u}) :
    IsStrictDom t α → (∀ β < α, ArchimedeanClass.mk (t β) ∈ T) →
    (∀ β < α, TermRep (t β) T) → TermRep (hahnSumO t α) T := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro _ _ _
    rw [hahnSumO_zero]
    exact termRep_zero T
  | add_one δ ih =>
    intro ht hT hrep
    have hδ : δ < δ + 1 := lt_add_one_iff.2 le_rfl
    rw [hahnSumO_add_one]
    exact (ih (ht.mono hδ.le) (fun β hβ ↦ hT β (hβ.trans hδ))
      (fun β hβ ↦ hrep β (hβ.trans hδ))).add (hrep δ hδ)
  | limit γ hγ _ =>
    intro ht hT _
    exact termRep_hahnSumO_of_isSuccLimit hγ ht hT

/-- **Canonical sums of every length are termwise coarsely representable**: if every term of a
strictly dominating series below `α` is termwise coarsely representable at `T` and has its class
in `T`, then so is `hahnSumO t α`. -/
theorem termRep_hahnSumO {t : Ordinal.{u} → Surreal.{u}} {α : Ordinal.{u}}
    (ht : IsStrictDom t α) {T : Set (ArchimedeanClass Surreal.{u})}
    (hT : ∀ β < α, ArchimedeanClass.mk (t β) ∈ T) (hrep : ∀ β < α, TermRep (t β) T) :
    TermRep (hahnSumO t α) T :=
  termRep_hahnSumO_aux t T α ht hT hrep

open SurrealHahnSeries in
/-- Every term of a surreal Hahn series is a monomial, coarsely representable at its own
class. -/
theorem coarseRep_term (x : SurrealHahnSeries.{u}) {j : Ordinal.{u}} (hj : j < x.length) :
    CoarseRep (x.term j) (ArchimedeanClass.mk (x.term j)) := by
  rw [term_of_lt hj, ArchimedeanClass.mk_mul, mk_realCast (coeffIdx_ne_zero hj), zero_add]
  exact coarseRep_monomial _ _

/-- **The evaluation of a Hahn series is termwise coarsely representable** at the set of the
classes of its terms. -/
theorem termRep_evalHahn (x : SurrealHahnSeries.{u}) :
    TermRep (evalHahn x) {c | ∃ j < x.length, c = ArchimedeanClass.mk (x.term j)} :=
  termRep_hahnSumO x.isStrictDom_term (fun j hj ↦ ⟨j, hj, rfl⟩)
    fun j hj ↦ (coarseRep_term x hj).termRep ⟨j, hj, rfl⟩

end Surreal

/-! ### Truncation along another series -/

namespace SurrealHahnSeries

/-- **Truncation of `x` along `z`**: `x` truncated at the `γ`-th exponent of `z` (keeping the
exponents `> z.exp γ`), or `x` itself when `γ ≥ z.length`. When `x`'s support is contained in
`z`'s, this is `x` restricted to the first `γ` exponents of `z`. -/
def truncAlong (x z : SurrealHahnSeries.{u}) (γ : Ordinal.{u}) : SurrealHahnSeries.{u} :=
  if h : γ < z.length then x.trunc (z.exp ⟨γ, h⟩) else x

variable {x z : SurrealHahnSeries.{u}}

theorem truncAlong_of_lt {γ : Ordinal.{u}} (h : γ < z.length) :
    x.truncAlong z γ = x.trunc (z.exp ⟨γ, h⟩) :=
  dif_pos h

theorem truncAlong_of_le {γ : Ordinal.{u}} (h : z.length ≤ γ) : x.truncAlong z γ = x :=
  dif_neg h.not_gt

/-- An exponent of `x.truncAlong z γ` is an exponent of `x`, and lies above `z.exp γ` when the
latter exists. -/
theorem mem_support_truncAlong {γ : Ordinal.{u}} {s : Surreal.{u}}
    (hs : s ∈ (x.truncAlong z γ).support) :
    s ∈ x.support ∧ ∀ h : γ < z.length, (z.exp ⟨γ, h⟩).1 < s := by
  by_cases h : γ < z.length
  · rw [truncAlong_of_lt h, support_trunc] at hs
    exact ⟨hs.1, fun _ ↦ hs.2⟩
  · rw [truncAlong_of_le (not_lt.1 h)] at hs
    exact ⟨hs, fun h' ↦ absurd h' h⟩

theorem support_truncAlong_subset (x z : SurrealHahnSeries.{u}) (γ : Ordinal.{u}) :
    (x.truncAlong z γ).support ⊆ x.support :=
  fun _ hs ↦ (mem_support_truncAlong hs).1

/-- At stage `0` nothing of `x` survives (every exponent of `z` is `≤ z.exp 0`). -/
theorem truncAlong_zero (hxz : x.support ⊆ z.support) : x.truncAlong z 0 = 0 := by
  rw [← support_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro s hs
  obtain ⟨hsx, hlt⟩ := mem_support_truncAlong hs
  obtain ⟨k, hk⟩ := eq_exp_of_mem_support (hxz hsx)
  have h0 : 0 < z.length := bot_le.trans_lt k.2
  have h := hlt h0
  rw [← hk] at h
  have h' := exp_lt_exp_iff.1 (Subtype.coe_lt_coe.1 h)
  have h'' : (k : Ordinal.{u}) < 0 := Subtype.coe_lt_coe.2 h'
  exact absurd h'' not_lt_bot

/-- Truncating `x.truncAlong z γ` at an earlier exponent `z.exp β` (`β < γ`) gives
`x.truncAlong z β`. -/
theorem truncAlong_trunc_exp {β γ : Ordinal.{u}} (hβγ : β < γ) (hγ : γ ≤ z.length) :
    (x.truncAlong z γ).trunc (z.exp ⟨β, hβγ.trans_le hγ⟩) = x.truncAlong z β := by
  rw [truncAlong_of_lt (hβγ.trans_le hγ)]
  rcases hγ.lt_or_eq with hlt | heq
  · rw [truncAlong_of_lt hlt, trunc_trunc, max_eq_right]
    exact Subtype.coe_le_coe.2 (exp_le_exp_iff.2 (Subtype.mk_le_mk.2 hβγ.le))
  · rw [truncAlong_of_le heq.ge]

/-- The coefficient of `x.truncAlong z (γ + 1)` at the exponent `z.exp γ` is that of `x`. -/
theorem coeff_truncAlong_add_one {γ : Ordinal.{u}} (hγ : γ < z.length) :
    (x.truncAlong z (γ + 1)).coeff (z.exp ⟨γ, hγ⟩) = x.coeff (z.exp ⟨γ, hγ⟩) := by
  rcases lt_or_ge (γ + 1) z.length with h1 | h1
  · rw [truncAlong_of_lt h1, coeff_trunc_of_lt]
    exact Subtype.coe_lt_coe.2 (exp_lt_exp_iff.2 (Subtype.mk_lt_mk.2 (lt_add_one_iff.2 le_rfl)))
  · rw [truncAlong_of_le h1]

/-- Every exponent of `x.truncAlong z (γ + 1)` is `≥ z.exp γ`. -/
theorem exp_le_of_mem_support_truncAlong_add_one (hxz : x.support ⊆ z.support)
    {γ : Ordinal.{u}} (hγ : γ < z.length) {s : Surreal.{u}}
    (hs : s ∈ (x.truncAlong z (γ + 1)).support) : (z.exp ⟨γ, hγ⟩).1 ≤ s := by
  obtain ⟨hsx, hlt⟩ := mem_support_truncAlong hs
  obtain ⟨k, hk⟩ := eq_exp_of_mem_support (hxz hsx)
  rw [← hk]
  refine Subtype.coe_le_coe.2 (exp_le_exp_iff.2 (Subtype.coe_le_coe.1 ?_))
  rcases lt_or_ge (γ + 1) z.length with h1 | h1
  · have h := hlt h1
    rw [← hk] at h
    have h' := exp_lt_exp_iff.1 (Subtype.coe_lt_coe.1 h)
    exact lt_add_one_iff.1 (Subtype.coe_lt_coe.2 h')
  · exact lt_add_one_iff.1 (k.2.trans_le h1)

/-- **The exponents of a truncation along `z` are exponents of `z` at earlier stages.** -/
theorem exists_exp_truncAlong_eq (hxz : x.support ⊆ z.support) {γ : Ordinal.{u}}
    (hγ : γ ≤ z.length) {j : Ordinal.{u}} (hj : j < (x.truncAlong z γ).length) :
    ∃ β, ∃ hβ : β < z.length, β < γ ∧
      ((x.truncAlong z γ).exp ⟨j, hj⟩).1 = (z.exp ⟨β, hβ⟩).1 := by
  obtain ⟨hsx, hlt⟩ := mem_support_truncAlong ((x.truncAlong z γ).exp ⟨j, hj⟩).2
  obtain ⟨k, hk⟩ := eq_exp_of_mem_support (hxz hsx)
  refine ⟨k.1, k.2, ?_, hk.symm⟩
  rcases hγ.lt_or_eq with h | h
  · have h1 := hlt h
    rw [← hk] at h1
    exact exp_lt_exp_iff.1 (Subtype.coe_lt_coe.1 h1)
  · exact h ▸ k.2

end SurrealHahnSeries

namespace Surreal

open SurrealHahnSeries

/-- **The successor step of the merge**: passing from stage `γ` to stage `γ + 1` along `z` appends
the single term `x.coeff (z.exp γ) · ω^ (z.exp γ)` (possibly zero). -/
theorem evalHahn_truncAlong_add_one {x z : SurrealHahnSeries.{u}} (hxz : x.support ⊆ z.support)
    {γ : Ordinal.{u}} (hγ : γ < z.length) :
    evalHahn (x.truncAlong z (γ + 1)) = evalHahn (x.truncAlong z γ) +
      (x.coeff (z.exp ⟨γ, hγ⟩) : Surreal.{u}) * ω^ (z.exp ⟨γ, hγ⟩).1 := by
  rw [evalHahn_eq_trunc_add_of_lowerBound _
    (fun s hs ↦ exp_le_of_mem_support_truncAlong_add_one hxz hγ hs),
    truncAlong_trunc_exp (lt_add_one_iff.2 le_rfl) (add_one_le_iff.2 hγ),
    coeff_truncAlong_add_one hγ]

/-- The evaluation of a truncation along `z` is termwise coarsely representable at the classes
of the terms of `z` at earlier stages. -/
theorem termRep_evalHahn_truncAlong {x z : SurrealHahnSeries.{u}} (hxz : x.support ⊆ z.support)
    {γ : Ordinal.{u}} (hγ : γ ≤ z.length) :
    TermRep (evalHahn (x.truncAlong z γ))
      {c | ∃ β < γ, c = ArchimedeanClass.mk (z.term β)} := by
  refine (termRep_evalHahn _).mono ?_
  rintro c ⟨j, hj, rfl⟩
  obtain ⟨β, hβN, hβγ, hexp⟩ := exists_exp_truncAlong_eq hxz hγ hj
  refine ⟨β, hβγ, ?_⟩
  rw [term_of_lt hj, term_of_lt hβN, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
    mk_realCast (coeffIdx_ne_zero hj), mk_realCast (coeffIdx_ne_zero hβN), hexp]

/-! ### THE MERGE THEOREM -/

private theorem hahnSumO_term_eq_aux (x y z : SurrealHahnSeries.{u})
    (hxz : x.support ⊆ z.support) (hyz : y.support ⊆ z.support)
    (hzc : ∀ e, z.coeff e = x.coeff e + y.coeff e) (γ : Ordinal.{u}) :
    γ ≤ z.length →
      hahnSumO z.term γ = evalHahn (x.truncAlong z γ) + evalHahn (y.truncAlong z γ) := by
  induction γ using Ordinal.limitRecOn with
  | zero =>
    intro _
    rw [hahnSumO_zero, truncAlong_zero hxz, truncAlong_zero hyz, evalHahn_zero, add_zero]
  | add_one δ ih =>
    intro h
    have hδ : δ < z.length := add_one_le_iff.1 h
    rw [hahnSumO_add_one, ih hδ.le, evalHahn_truncAlong_add_one hxz hδ,
      evalHahn_truncAlong_add_one hyz hδ, term_of_lt hδ, coeffIdx_of_lt hδ, hzc,
      Real.toSurreal_add]
    ring
  | limit γ hγ ih =>
    intro hγN
    have hV : ∀ β < γ, hahnSumO z.term β =
        evalHahn (x.truncAlong z β) + evalHahn (y.truncAlong z β) :=
      fun β hβ ↦ ih β hβ (hβ.le.trans hγN)
    have hzt : IsStrictDom z.term γ := z.isStrictDom_term.mono hγN
    -- The value is a Hahn sum of the merged series: the residual at stage `β` is the sum of the
    -- two residuals at the truncations at `z.exp β`, each dominated by `ω^ (z.exp β)`.
    have hP : IsHahnSumO z.term γ
        (evalHahn (x.truncAlong z γ) + evalHahn (y.truncAlong z γ)) := by
      intro β hβ
      have hβN : β < z.length := hβ.trans_le hγN
      rw [hV β hβ, ← truncAlong_trunc_exp hβ hγN (x := x), ← truncAlong_trunc_exp hβ hγN (x := y),
        add_sub_add_comm]
      have hmk : ArchimedeanClass.mk (z.term β) =
          ArchimedeanClass.mk (ω^ (z.exp ⟨β, hβN⟩).1) := by
        rw [term_of_lt hβN, ArchimedeanClass.mk_mul, mk_realCast (coeffIdx_ne_zero hβN), zero_add]
      rw [hmk]
      exact le_trans (le_min (mk_wpow_le_mk_evalHahn_sub_trunc _ _)
        (mk_wpow_le_mk_evalHahn_sub_trunc _ _)) (ArchimedeanClass.min_le_mk_add ..)
    -- The game: the Conway sum of termwise-coarse representatives of the two truncated values.
    obtain ⟨GX, hGXn, hGX, hGXl, hGXr⟩ := termRep_evalHahn_truncAlong hxz hγN
    obtain ⟨GY, hGYn, hGY, hGYl, hGYr⟩ := termRep_evalHahn_truncAlong hyz hγN
    haveI := hGXn
    haveI := hGYn
    have hG : Surreal.mk (GX + GY) = evalHahn (x.truncAlong z γ) + evalHahn (y.truncAlong z γ) := by
      rw [Surreal.mk_add, hGX, hGY]
    rw [← hG]
    refine hahnSumO_eq_of_isHahnSumO_of_moves_le hγ hzt (by rwa [hG]) ?_ ?_
    · rw [forall_moves_add]
      constructor
      · intro a ha
        haveI := IGame.Numeric.of_mem_moves ha
        obtain ⟨c, ⟨β, hβ, rfl⟩, hc⟩ := hGXl a ha
        have hβ1 : β + 1 < γ := hγ.add_one_lt_of_ordinal hβ
        refine ⟨β + 1, hβ1, ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, hGY]
        have hpos : 0 < evalHahn (x.truncAlong z γ) - Surreal.mk a := by
          rw [sub_pos, ← hGX]
          exact Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt ha)
        have hmk : ArchimedeanClass.mk (evalHahn (x.truncAlong z γ) - Surreal.mk a) <
            ArchimedeanClass.mk (z.term (β + 1)) :=
          hc.trans_lt (hzt (lt_add_one_iff.2 le_rfl) hβ1)
        have key := sub_le_optLoO_of_mk_lt hzt hP hpos (hγ.add_one_lt_of_ordinal hβ1) hmk
        rw [show Surreal.mk a + evalHahn (y.truncAlong z γ) =
          evalHahn (x.truncAlong z γ) + evalHahn (y.truncAlong z γ) -
            (evalHahn (x.truncAlong z γ) - Surreal.mk a) by ring]
        exact key
      · intro b hb
        haveI := IGame.Numeric.of_mem_moves hb
        obtain ⟨c, ⟨β, hβ, rfl⟩, hc⟩ := hGYl b hb
        have hβ1 : β + 1 < γ := hγ.add_one_lt_of_ordinal hβ
        refine ⟨β + 1, hβ1, ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, hGX]
        have hpos : 0 < evalHahn (y.truncAlong z γ) - Surreal.mk b := by
          rw [sub_pos, ← hGY]
          exact Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt hb)
        have hmk : ArchimedeanClass.mk (evalHahn (y.truncAlong z γ) - Surreal.mk b) <
            ArchimedeanClass.mk (z.term (β + 1)) :=
          hc.trans_lt (hzt (lt_add_one_iff.2 le_rfl) hβ1)
        have key := sub_le_optLoO_of_mk_lt hzt hP hpos (hγ.add_one_lt_of_ordinal hβ1) hmk
        rw [show evalHahn (x.truncAlong z γ) + Surreal.mk b =
          evalHahn (x.truncAlong z γ) + evalHahn (y.truncAlong z γ) -
            (evalHahn (y.truncAlong z γ) - Surreal.mk b) by ring]
        exact key
    · rw [forall_moves_add]
      constructor
      · intro a ha
        haveI := IGame.Numeric.of_mem_moves ha
        obtain ⟨c, ⟨β, hβ, rfl⟩, hc⟩ := hGXr a ha
        have hβ1 : β + 1 < γ := hγ.add_one_lt_of_ordinal hβ
        refine ⟨β + 1, hβ1, ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, hGY]
        have hpos : 0 < Surreal.mk a - evalHahn (x.truncAlong z γ) := by
          rw [sub_pos, ← hGX]
          exact Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right ha)
        have hmk : ArchimedeanClass.mk (Surreal.mk a - evalHahn (x.truncAlong z γ)) <
            ArchimedeanClass.mk (z.term (β + 1)) :=
          hc.trans_lt (hzt (lt_add_one_iff.2 le_rfl) hβ1)
        have key := optHiO_le_add_of_mk_lt hzt hP hpos (hγ.add_one_lt_of_ordinal hβ1) hmk
        rw [show Surreal.mk a + evalHahn (y.truncAlong z γ) =
          evalHahn (x.truncAlong z γ) + evalHahn (y.truncAlong z γ) +
            (Surreal.mk a - evalHahn (x.truncAlong z γ)) by ring]
        exact key
      · intro b hb
        haveI := IGame.Numeric.of_mem_moves hb
        obtain ⟨c, ⟨β, hβ, rfl⟩, hc⟩ := hGYr b hb
        have hβ1 : β + 1 < γ := hγ.add_one_lt_of_ordinal hβ
        refine ⟨β + 1, hβ1, ?_⟩
        rw [← Surreal.mk_le_mk, out_eq, Surreal.mk_add, hGX]
        have hpos : 0 < Surreal.mk b - evalHahn (y.truncAlong z γ) := by
          rw [sub_pos, ← hGY]
          exact Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right hb)
        have hmk : ArchimedeanClass.mk (Surreal.mk b - evalHahn (y.truncAlong z γ)) <
            ArchimedeanClass.mk (z.term (β + 1)) :=
          hc.trans_lt (hzt (lt_add_one_iff.2 le_rfl) hβ1)
        have key := optHiO_le_add_of_mk_lt hzt hP hpos (hγ.add_one_lt_of_ordinal hβ1) hmk
        rw [show evalHahn (x.truncAlong z γ) + Surreal.mk b =
          evalHahn (x.truncAlong z γ) + evalHahn (y.truncAlong z γ) +
            (Surreal.mk b - evalHahn (y.truncAlong z γ)) by ring]
        exact key

/-- **The merge, stage by stage**: if `z` has coefficients `z.coeff = x.coeff + y.coeff` and
contains both supports, then at every stage `γ ≤ z.length` the canonical partial sum of `z`'s
term sequence is the sum of the evaluations of `x` and `y` truncated along `z`. -/
theorem hahnSumO_term_eq_evalHahn_truncAlong_add {x y z : SurrealHahnSeries.{u}}
    (hxz : x.support ⊆ z.support) (hyz : y.support ⊆ z.support)
    (hzc : ∀ e, z.coeff e = x.coeff e + y.coeff e) {γ : Ordinal.{u}} (hγ : γ ≤ z.length) :
    hahnSumO z.term γ = evalHahn (x.truncAlong z γ) + evalHahn (y.truncAlong z γ) :=
  hahnSumO_term_eq_aux x y z hxz hyz hzc γ hγ

/-- **THE MERGE THEOREM — additivity of Hahn-series evaluation on arbitrary supports**: for
surreal Hahn series `x, y` with no coefficient cancellation
(`x.coeff i + y.coeff i = 0 → x.coeff i = 0 ∧ y.coeff i = 0`),
`evalHahn (x + y) = evalHahn x + evalHahn y`.

Proof: transfinite induction over the stages `γ ≤ (x + y).length` of the merged series, proving
`hahnSumO (x + y).term γ = evalHahn (x ⇂ γ) + evalHahn (y ⇂ γ)` with `x ⇂ γ` the truncation of
`x` along the `γ`-th merged exponent. Successor stages are the append law (the merged term is
`(x_e + y_e) ω^ e`, and each truncation grows by exactly its own part). At a limit stage the
identification engine is applied to the Conway sum of termwise-coarse representatives of the two
truncated evaluations: the value is a Hahn sum of the merged series (each residual splits into the
two residuals at the truncations at `z.exp β`, both dominated by `ω^ (z.exp β)`), and each option
is at distance of class `≤ mk ((x + y).term β)` for some `β < γ`, hence beaten at stage `β + 1`. -/
theorem evalHahn_add {x y : SurrealHahnSeries.{u}}
    (hnc : ∀ i, x.coeff i + y.coeff i = 0 → x.coeff i = 0 ∧ y.coeff i = 0) :
    evalHahn (x + y) = evalHahn x + evalHahn y := by
  have hxz : x.support ⊆ (x + y).support := fun i hi ↦ by
    rw [mem_support_iff, coeff_add_apply]
    exact fun h ↦ mem_support_iff.1 hi (hnc i h).1
  have hyz : y.support ⊆ (x + y).support := fun i hi ↦ by
    rw [mem_support_iff, coeff_add_apply]
    exact fun h ↦ mem_support_iff.1 hi (hnc i h).2
  have h := hahnSumO_term_eq_evalHahn_truncAlong_add hxz hyz (coeff_add_apply x y) le_rfl
  rw [truncAlong_of_le le_rfl, truncAlong_of_le le_rfl] at h
  exact h

/-- **The merge for disjoint supports** (no cancellation is automatic). -/
theorem evalHahn_add_of_disjoint_support {x y : SurrealHahnSeries.{u}}
    (h : Disjoint x.support y.support) : evalHahn (x + y) = evalHahn x + evalHahn y := by
  refine evalHahn_add fun i hi ↦ ?_
  by_cases hx : x.coeff i = 0
  · exact ⟨hx, by rwa [hx, zero_add] at hi⟩
  · have hy : y.coeff i = 0 := by
      by_contra hy
      exact Set.disjoint_left.1 h (mem_support_iff.2 hx) (mem_support_iff.2 hy)
    exact absurd (by rwa [hy, add_zero] at hi) hx

/-- **THE SPLIT LAW**: the evaluation of a Hahn series splits at any exponent `e` into the
evaluation of the truncation (exponents `> e`) plus the evaluation of the tail (exponents `≤ e`)
— the concatenation theorem, restated for the library's Hahn series. -/
theorem evalHahn_eq_trunc_add_sub_trunc (x : SurrealHahnSeries.{u}) (e : Surreal.{u}) :
    evalHahn x = evalHahn (x.trunc e) + evalHahn (x - x.trunc e) := by
  have h := evalHahn_add_of_disjoint_support (x := x.trunc e) (y := x - x.trunc e) ?_
  · rwa [add_sub_cancel] at h
  · rw [Set.disjoint_left]
    intro i hi hi'
    rw [support_trunc] at hi
    rw [mem_support_iff, coeff_sub_apply, coeff_trunc_of_lt hi.2, sub_self] at hi'
    exact hi' rfl

/-- The evaluation of the tail below `e` is the residual of the evaluation at the truncation. -/
theorem evalHahn_sub_trunc (x : SurrealHahnSeries.{u}) (e : Surreal.{u}) :
    evalHahn (x - x.trunc e) = evalHahn x - evalHahn (x.trunc e) :=
  (eq_sub_of_add_eq' (evalHahn_eq_trunc_add_sub_trunc x e).symm)

end Surreal

end
