import Infinity.GeometricBirthday

/-!
# The day-`ω+1` census

`Infinity.DayOmega` proved Conway's day-`ω` census as an iff;
`Infinity.GeometricBirthday` proved the uniform grid census for the *finite* surreals of
every day `ω + n`. This file completes the day-`ω+1` census as a single iff, adding the
*infinite* branch:

* `birthday_wpow_one_sub_one` : **`birthday (ω − 1) = ω + 1`** — realization by a
  two-sided cut `!{dyadics | ω}` mutually cofinal with the Conway sum `ω + (−1)`
  (pure order, no simplicity), lower bound from the day-`ω` classification.
* `birthday_wpow_one_add_one` : `birthday (ω + 1) = ω + 1`.
* `eq_of_pos_of_not_isFinite_of_birthday_le_omega0_add_one` — **the infinite branch**:
  a positive infinite surreal born by day `ω+1` is `ω`, `ω+1` or `ω−1`. Census method:
  the options of a birthday-minimal game are day-`ω` surreals, so the infinite ones
  among them are `±ω`; four cases on which side sees `ω`, each pinned by simplest-fit
  uniqueness.
* `birthday_le_omega0_add_one_iff` — **the day-`ω+1` census, machine-checked**: a
  surreal is born by day `ω+1` iff it is a grid point `a + r·ω⁻¹` with `hgt r ≤ 1`
  over any real, or `hgt r ≤ 2` over a dyadic anchor, or one of `±ω`, `±(ω+1)`,
  `±(ω−1)`. (ONAG ch. 2's day-`ω+1` description; the dyadic coefficients of height
  `≤ 2` are `0, ±1, ±2, ±½`, so the finite newcomers are exactly `a ± ω⁻¹` for
  non-dyadic real `a` and `d ± 2·ω⁻¹`, `d ± ω⁻¹/2` for dyadic `d`.)
-/

open ArchimedeanClass IGame Set

universe u

noncomputable section

namespace Surreal

/-! ### `ω ± 1`: infiniteness and exact birthdays -/

private theorem one_lt_wpow_one : (1 : Surreal.{u}) < ω^ (1 : Surreal) := by
  have h : ((1 : ℕ) : Surreal.{u}) < ω^ (1 : Surreal) := natCast_lt_wpow_one 1
  have h1 : ((1 : ℕ) : Surreal.{u}) = 1 := by push_cast; rfl
  rwa [h1] at h

theorem not_isFinite_wpow_one_add_one : ¬ IsFinite (ω^ (1 : Surreal.{u}) + 1) := by
  intro h
  obtain ⟨n, hn⟩ := isFinite_iff.1 h
  have hpos : (0 : Surreal) < ω^ (1 : Surreal) + 1 := by
    have := wpow_pos (1 : Surreal.{u})
    linarith
  rw [abs_of_pos hpos] at hn
  have h2 : ((n : ℕ) : Surreal.{u}) < ω^ (1 : Surreal) := natCast_lt_wpow_one n
  linarith

theorem not_isFinite_wpow_one_sub_one : ¬ IsFinite (ω^ (1 : Surreal.{u}) - 1) := by
  intro h
  obtain ⟨n, hn⟩ := isFinite_iff.1 h
  have h1 : (1 : Surreal.{u}) < ω^ (1 : Surreal) := one_lt_wpow_one
  have hpos : (0 : Surreal) < ω^ (1 : Surreal) - 1 := by linarith
  rw [abs_of_pos hpos] at hn
  have h2 : ((n + 1 : ℕ) : Surreal.{u}) < ω^ (1 : Surreal) := natCast_lt_wpow_one (n + 1)
  have h3 : ((n + 1 : ℕ) : Surreal.{u}) = (n : Surreal) + 1 := by push_cast; ring
  rw [h3] at h2
  linarith

/-- `birthday (ω + 1) = ω + 1`. -/
theorem birthday_wpow_one_add_one :
    (ω^ (1 : Surreal.{u}) + 1).birthday = NatOrdinal.of Ordinal.omega0 + 1 := by
  rw [add_comm]
  exact birthday_one_add_wpow

/-- The left moves of the game `ω^ 1`. -/
private theorem leftMoves_wpow_one : (ω^ (1 : IGame.{u}))ᴸ =
    insert 0 ((fun r : Dyadic ↦ (r : IGame) * ω^ (0 : IGame)) '' Set.Ioi 0) := by
  have h1 : (1 : IGame.{u})ᴸ = {0} := by simp
  rw [leftMoves_wpow, h1, Set.image2_singleton_right]

private theorem rightMoves_wpow_one : (ω^ (1 : IGame.{u}))ᴿ = ∅ := by
  have h1 : (1 : IGame.{u})ᴿ = ∅ := by simp
  rw [rightMoves_wpow, h1]
  simp

private theorem mk_wpow_one' : mk (ω^ (1 : IGame.{u})) = ω^ (1 : Surreal) := by
  rw [Surreal.mk_wpow]
  norm_num

private theorem mk_dyadic_mul_wpow_zero' (q : Dyadic) :
    Surreal.mk ((q : IGame.{u}) * ω^ (0 : IGame)) = (q : Surreal) := by
  rw [Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow, Surreal.mk_zero, wpow_zero, mul_one]

private theorem neg_one_leftMoves : (-1 : IGame.{u})ᴸ = ∅ := by
  rw [show (-1 : IGame.{u}) = -(1 : IGame) from rfl]
  simp

private theorem neg_one_rightMoves : (-1 : IGame.{u})ᴿ = {0} := by
  rw [show (-1 : IGame.{u}) = -(1 : IGame) from rfl]
  simp

private theorem mk_neg_one : Surreal.mk (-1 : IGame.{u}) = -1 := by
  show Surreal.mk (-(1 : IGame.{u})) = -1
  rw [Surreal.mk_neg, Surreal.mk_one]

/-- **`ω − 1` is born by day `ω + 1`**: the Conway sum `ω + (−1)` is mutually cofinal
with the two-sided cut on the dyadics and a birthday-minimal game for `ω`. -/
theorem birthday_wpow_one_sub_one_le :
    (ω^ (1 : Surreal.{u}) - 1).birthday ≤ NatOrdinal.of Ordinal.omega0 + 1 := by
  obtain ⟨gω, hgωn, hgωv, hgωb⟩ := birthday_eq_iGameBirthday (ω^ (1 : Surreal.{u}))
  haveI := hgωn
  set C : IGame.{u} := !{Set.range (fun q : Dyadic ↦ (q : IGame.{u})) | {gω}} with hC
  have hCL : Cᴸ = Set.range (fun q : Dyadic ↦ (q : IGame.{u})) := leftMoves_ofSets ..
  have hCR : Cᴿ = {gω} := rightMoves_ofSets ..
  have hequiv : ω^ (1 : IGame.{u}) + (-1 : IGame) ≈ C := by
    apply equiv_of_exists_le
    · rw [forall_moves_add]
      constructor
      · intro i hi
        rw [show (ω^ (1 : IGame.{u})).moves Player.left = (ω^ (1 : IGame.{u}))ᴸ from rfl,
          leftMoves_wpow_one, Set.mem_insert_iff] at hi
        rcases hi with rfl | ⟨q, hq, rfl⟩
        · refine ⟨((0 : Dyadic) : IGame), by rw [hCL]; exact Set.mem_range_self 0, ?_⟩
          rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_zero, Surreal.mk_dyadic,
            mk_neg_one, dyadic_cast_zero]
          linarith
        · refine ⟨(q : IGame), by rw [hCL]; exact Set.mem_range_self q, ?_⟩
          rw [← Surreal.mk_le_mk, Surreal.mk_add, mk_dyadic_mul_wpow_zero', Surreal.mk_dyadic,
            mk_neg_one]
          linarith
      · intro b hb
        rw [show (-1 : IGame.{u}).moves Player.left = (-1 : IGame.{u})ᴸ from rfl,
          neg_one_leftMoves] at hb
        exact absurd hb (Set.notMem_empty b)
    · rw [forall_moves_add]
      constructor
      · intro j hj
        rw [show (ω^ (1 : IGame.{u})).moves Player.right = (ω^ (1 : IGame.{u}))ᴿ from rfl,
          rightMoves_wpow_one] at hj
        exact absurd hj (Set.notMem_empty j)
      · intro b hb
        rw [show (-1 : IGame.{u}).moves Player.right = (-1 : IGame.{u})ᴿ from rfl,
          neg_one_rightMoves, Set.mem_singleton_iff] at hb
        subst hb
        refine ⟨gω, by rw [hCR]; exact Set.mem_singleton _, ?_⟩
        rw [← Surreal.mk_le_mk, Surreal.mk_add, mk_wpow_one', Surreal.mk_zero, add_zero, hgωv]
    · rw [hCL]
      rintro b ⟨q, rfl⟩
      -- the dyadic option `q` sits below the left move `q'·ω⁰ + (−1)` for a suitable `q' > 0`
      have hqle : ∃ q' : Dyadic, 0 < q' ∧ (q : Surreal) ≤ (q' : Surreal) + -1 := by
        rcases lt_or_ge 0 (q + 1) with hq1 | hq1
        · refine ⟨q + 1, hq1, ?_⟩
          rw [dyadic_cast_add', dyadic_cast_one]
          linarith
        · refine ⟨1, by norm_num, ?_⟩
          have h1 : q ≤ -1 + 1 := by linarith
          have h2 : q ≤ (0 : Dyadic) := by linarith
          have h3 := dyadic_cast_lt (show q < 1 from by linarith [h2])
          have h4 : (q : Surreal) ≤ (0 : Surreal) := by
            have := dyadic_cast_lt (show q < 1 from by linarith [h2])
            rcases eq_or_lt_of_le h2 with he | hl
            · rw [he, dyadic_cast_zero]
            · have := dyadic_cast_lt hl
              rw [dyadic_cast_zero] at this
              linarith
          rw [dyadic_cast_one]
          linarith
      obtain ⟨q', hq', hle⟩ := hqle
      refine ⟨(q' : IGame) * ω^ (0 : IGame) + (-1 : IGame),
        add_right_mem_moves_add ?_ _, ?_⟩
      · rw [show (ω^ (1 : IGame.{u})).moves Player.left = (ω^ (1 : IGame.{u}))ᴸ from rfl,
          leftMoves_wpow_one]
        exact Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ hq')
      · rw [← Surreal.mk_le_mk, Surreal.mk_add, mk_dyadic_mul_wpow_zero', Surreal.mk_dyadic,
          mk_neg_one]
        exact hle
    · rw [hCR]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      refine ⟨ω^ (1 : IGame.{u}) + (0 : IGame),
        add_left_mem_moves_add (by
          rw [show (-1 : IGame.{u}).moves Player.right = (-1 : IGame.{u})ᴿ from rfl,
            neg_one_rightMoves]
          exact Set.mem_singleton _) _, ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.mk_add, mk_wpow_one', Surreal.mk_zero, add_zero, hgωv]
  -- the cut is numeric
  have hCn : IGame.Numeric C := by
    refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
    · rw [hC, leftMoves_ofSets] at hy
      rw [hC, rightMoves_ofSets, Set.mem_singleton_iff] at hz
      obtain ⟨q, rfl⟩ := hy
      subst hz
      rw [← Surreal.mk_lt_mk, Surreal.mk_dyadic, hgωv]
      exact finite_lt_of_not_isFinite_of_lt not_isFinite_wpow_one (wpow_pos _)
        isFinite_zero (isFinite_dyadic_cast q)
    · cases p with
      | left =>
        rw [hC, moves_ofSets] at hy
        obtain ⟨q, rfl⟩ := hy
        infer_instance
      | right =>
        rw [hC, moves_ofSets, Set.mem_singleton_iff] at hy
        subst hy
        infer_instance
  -- value and birthday
  have hval : ω^ (1 : Surreal.{u}) - 1 = @Surreal.mk C hCn := by
    have h1 : Surreal.mk (ω^ (1 : IGame.{u}) + (-1 : IGame))
        = ω^ (1 : Surreal.{u}) - 1 := by
      rw [Surreal.mk_add, mk_wpow_one', mk_neg_one]
      ring
    rw [← h1]
    exact Surreal.mk_eq hequiv
  refine le_of_eq_of_le (congrArg birthday hval) ?_
  refine (birthday_mk_le _).trans ?_
  rw [hC, IGame.birthday_ofSets]
  refine max_le ?_ ?_
  · refine csSup_le' ?_
    rintro o ⟨g, ⟨q, rfl⟩, rfl⟩
    rw [Function.comp_apply, Order.succ_eq_add_one]
    have h := IGame.short_iff_birthday_finite.1 (IGame.Short.dyadic q)
    have h1 : (q : IGame.{u}).birthday + 1 ≤ NatOrdinal.of Ordinal.omega0 := by
      rw [← Order.succ_eq_add_one]
      exact Order.succ_le_of_lt h
    exact h1.trans (le_add_of_nonneg_right zero_le_one)
  · refine csSup_le' ?_
    rintro o ⟨g, hg, rfl⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rw [Function.comp_apply, Order.succ_eq_add_one, hgωb, birthday_wpow_one]

/-- **An exact transfinite birthday**: `birthday (ω − 1) = ω + 1`. -/
theorem birthday_wpow_one_sub_one :
    (ω^ (1 : Surreal.{u}) - 1).birthday = NatOrdinal.of Ordinal.omega0 + 1 := by
  refine le_antisymm birthday_wpow_one_sub_one_le ?_
  refine omega0_add_one_le_birthday_of_not_isFinite_of_ne not_isFinite_wpow_one_sub_one ?_ ?_
  · intro h
    exact one_ne_zero (by linarith : (1 : Surreal.{u}) = 0)
  · intro h
    have h1 : (1 : Surreal.{u}) < ω^ (1 : Surreal) := one_lt_wpow_one
    linarith

/-! ### The infinite branch of the day-`ω+1` census -/

/-- **The day-`ω+1` classification of positive infinite surreals**: `ω`, `ω+1`, or
`ω−1`. -/
theorem eq_of_pos_of_not_isFinite_of_birthday_le_omega0_add_one {y : Surreal.{u}}
    (hy0 : 0 < y) (hy : ¬ IsFinite y)
    (hb : y.birthday ≤ NatOrdinal.of Ordinal.omega0 + 1) :
    y = ω^ (1 : Surreal) ∨ y = ω^ (1 : Surreal) + 1 ∨ y = ω^ (1 : Surreal) - 1 := by
  have h1ω : (1 : Surreal.{u}) < ω^ (1 : Surreal) := one_lt_wpow_one
  have hωpos := wpow_pos (1 : Surreal.{u})
  rcases lt_or_eq_of_le hb with hlt | heq
  · exact .inl (eq_wpow_one_of_pos_of_not_isFinite_of_birthday_le hy0 hy
      (Order.lt_add_one_iff.1 hlt))
  · -- `y` exceeds every natural
    have hyn : ∀ n : ℕ, (n : Surreal) < y := by
      intro n
      by_contra hn
      rw [not_lt] at hn
      exact hy (isFinite_iff.2 ⟨n, by rwa [abs_of_pos hy0]⟩)
    obtain ⟨g, hgn, hgy, hgb⟩ := birthday_eq_iGameBirthday y
    haveI := hgn
    have hslt := Cut.supLeft_lt_infRight_of_numeric g
    have hopt : ∀ (p : Player) (i : IGame), i ∈ g.moves p →
        i.birthday ≤ NatOrdinal.of Ordinal.omega0 := by
      intro p i hi
      have h1 := IGame.birthday_lt_of_mem_moves hi
      rw [hgb, heq] at h1
      exact Order.lt_add_one_iff.1 h1
    -- every right option has value `ω`
    have hR : ∀ j (hj : j ∈ gᴿ),
        @Surreal.mk j (IGame.Numeric.of_mem_moves hj) = ω^ (1 : Surreal) := by
      intro j hj
      haveI := IGame.Numeric.of_mem_moves hj
      have hyj : y < Surreal.mk j := by
        rw [← hgy]
        exact mk_lt_mk.2 (IGame.Numeric.lt_right hj)
      have hjinf : ¬ IsFinite (Surreal.mk j) := by
        intro h
        obtain ⟨n, hn⟩ := isFinite_iff.1 h
        have h2 : Surreal.mk j ≤ n := (le_abs_self _).trans hn
        exact absurd (hyj.trans_le h2) (not_lt.2 (hyn n).le)
      exact eq_wpow_one_of_pos_of_not_isFinite_of_birthday_le (hy0.trans hyj) hjinf
        ((birthday_mk_le j).trans (hopt _ j hj))
    -- left options: finite, `−ω`, or `ω`
    have hL : ∀ i (hi : i ∈ gᴸ),
        IsFinite (@Surreal.mk i (IGame.Numeric.of_mem_moves hi)) ∨
        @Surreal.mk i (IGame.Numeric.of_mem_moves hi) = -ω^ (1 : Surreal) ∨
        @Surreal.mk i (IGame.Numeric.of_mem_moves hi) = ω^ (1 : Surreal) := by
      intro i hi
      haveI := IGame.Numeric.of_mem_moves hi
      by_cases hf : IsFinite (Surreal.mk i)
      · exact .inl hf
      · rcases eq_wpow_one_or_eq_neg_of_not_isFinite_of_birthday_le hf
          ((birthday_mk_le i).trans (hopt _ i hi)) with h | h
        · exact .inr (.inr h)
        · exact .inr (.inl h)
    -- the closing pattern
    have hclose : ∀ c : Surreal.{u}, Cut.Fits c (Cut.supLeft g) (Cut.infRight g) →
        c.birthday ≤ y.birthday → y = c := by
      intro c hfitc hcb
      have hy' : Cut.simplestBtwn hslt = y := by
        rw [← toGame_inj, Cut.simplestBtwn_supLeft_infRight hslt, ← hgy, toGame_mk]
      have hfity : Cut.Fits y (Cut.supLeft g) (Cut.infRight g) :=
        hy' ▸ Cut.fits_simplestBtwn hslt
      have hmin : ∀ v, Cut.Fits v (Cut.supLeft g) (Cut.infRight g) →
          y.birthday ≤ v.birthday := by
        intro v hv
        have h := Cut.birthday_simplestBtwn_le_of_fits hv
        rwa [hy'] at h
      exact (Cut.eq_of_fits_of_birthday_le hfity hfitc hmin hcb).symm
    by_cases hRne : ∃ j, j ∈ gᴿ
    · obtain ⟨j0, hj0⟩ := hRne
      haveI := IGame.Numeric.of_mem_moves hj0
      have hyltω : y < ω^ (1 : Surreal) := by
        have hyj : y < Surreal.mk j0 := by
          rw [← hgy]
          exact mk_lt_mk.2 (IGame.Numeric.lt_right hj0)
        rwa [hR j0 hj0] at hyj
      -- no left option can be `ω`
      have hLω : ∀ i (hi : i ∈ gᴸ),
          @Surreal.mk i (IGame.Numeric.of_mem_moves hi) ≠ ω^ (1 : Surreal) := by
        intro i hi hiv
        haveI := IGame.Numeric.of_mem_moves hi
        have hiy : Surreal.mk i < y := by
          rw [← hgy]
          exact mk_lt_mk.2 (IGame.Numeric.left_lt hi)
        rw [hiv] at hiy
        exact absurd (hiy.trans hyltω) (lt_irrefl _)
      -- candidate: `ω − 1`
      have hfitc : Cut.Fits (ω^ (1 : Surreal.{u}) - 1) (Cut.supLeft g) (Cut.infRight g) := by
        rw [Cut.Fits, Set.mem_inter_iff]
        constructor
        · rw [Cut.right_supLeft]
          simp only [Set.mem_iInter, Set.mem_ofPred_eq]
          intro i hi
          haveI := IGame.Numeric.of_mem_moves hi
          have hlt : Surreal.mk i < ω^ (1 : Surreal) - 1 := by
            rcases hL i hi with hf | hneg | hω
            · exact finite_lt_of_not_isFinite_of_lt not_isFinite_wpow_one_sub_one
                (by linarith) isFinite_zero hf
            · rw [hneg]
              linarith
            · exact absurd hω (hLω i hi)
          rw [← toGame_mk, toGame_le_iff]
          exact not_le.2 hlt
        · rw [Cut.left_infRight]
          simp only [Set.mem_iInter, Set.mem_ofPred_eq]
          intro j hj
          haveI := IGame.Numeric.of_mem_moves hj
          have hlt : ω^ (1 : Surreal.{u}) - 1 < Surreal.mk j := by
            rw [hR j hj]
            linarith
          rw [← toGame_mk, toGame_le_iff]
          exact not_le.2 hlt
      refine .inr (.inr (hclose _ hfitc ?_))
      rw [birthday_wpow_one_sub_one, heq]
    · push Not at hRne
      by_cases hLω : ∃ i, ∃ hi : i ∈ gᴸ,
          @Surreal.mk i (IGame.Numeric.of_mem_moves hi) = ω^ (1 : Surreal)
      · -- candidate: `ω + 1`
        have hfitc : Cut.Fits (ω^ (1 : Surreal.{u}) + 1) (Cut.supLeft g) (Cut.infRight g) := by
          rw [Cut.Fits, Set.mem_inter_iff]
          constructor
          · rw [Cut.right_supLeft]
            simp only [Set.mem_iInter, Set.mem_ofPred_eq]
            intro i hi
            haveI := IGame.Numeric.of_mem_moves hi
            have hlt : Surreal.mk i < ω^ (1 : Surreal) + 1 := by
              rcases hL i hi with hf | hneg | hω
              · exact finite_lt_of_not_isFinite_of_lt not_isFinite_wpow_one_add_one
                  (by linarith) isFinite_zero hf
              · rw [hneg]
                linarith
              · rw [hω]
                linarith
            rw [← toGame_mk, toGame_le_iff]
            exact not_le.2 hlt
          · rw [Cut.left_infRight]
            simp only [Set.mem_iInter, Set.mem_ofPred_eq]
            intro j hj
            exact absurd hj (hRne j)
        refine .inr (.inl (hclose _ hfitc ?_))
        rw [birthday_wpow_one_add_one, heq]
      · -- candidate: `ω`
        push Not at hLω
        have hfitc : Cut.Fits (ω^ (1 : Surreal.{u})) (Cut.supLeft g) (Cut.infRight g) := by
          rw [Cut.Fits, Set.mem_inter_iff]
          constructor
          · rw [Cut.right_supLeft]
            simp only [Set.mem_iInter, Set.mem_ofPred_eq]
            intro i hi
            haveI := IGame.Numeric.of_mem_moves hi
            have hlt : Surreal.mk i < ω^ (1 : Surreal) := by
              rcases hL i hi with hf | hneg | hω
              · exact finite_lt_of_not_isFinite_of_lt not_isFinite_wpow_one
                  (by linarith) isFinite_zero hf
              · rw [hneg]
                linarith
              · exact absurd hω (hLω i hi)
            rw [← toGame_mk, toGame_le_iff]
            exact not_le.2 hlt
          · rw [Cut.left_infRight]
            simp only [Set.mem_iInter, Set.mem_ofPred_eq]
            intro j hj
            exact absurd hj (hRne j)
        refine .inl (hclose _ hfitc ?_)
        rw [birthday_wpow_one, heq]
        exact le_add_of_nonneg_right zero_le_one

/-! ### The day-`ω+1` census as a single iff -/

/-- **Conway's day-`ω+1` census, machine-checked**: a surreal is born by day `ω+1` iff
it is a grid point `a + r·ω⁻¹` with `hgt r ≤ 1` over some real `a`, a grid point
`e + r·ω⁻¹` with `hgt r ≤ 2` over some dyadic `e`, or one of the six infinite values
`±ω`, `±(ω+1)`, `±(ω−1)`. -/
theorem birthday_le_omega0_add_one_iff {y : Surreal.{u}} :
    y.birthday ≤ NatOrdinal.of Ordinal.omega0 + 1 ↔
      (∃ (a : ℝ) (r : Dyadic), Dyadic.hgt r ≤ 1 ∧
        y = (a : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)) ∨
      (∃ (e : Dyadic) (r : Dyadic), Dyadic.hgt r ≤ 2 ∧
        y = (e : Surreal) + (r : Surreal) * ω^ (-1 : Surreal)) ∨
      y = ω^ (1 : Surreal) ∨ y = -ω^ (1 : Surreal) ∨
      y = ω^ (1 : Surreal) + 1 ∨ y = -(ω^ (1 : Surreal) + 1) ∨
      y = ω^ (1 : Surreal) - 1 ∨ y = -(ω^ (1 : Surreal) - 1) := by
  constructor
  · intro hb
    by_cases hy : IsFinite y
    · have hb1 : y.birthday ≤ NatOrdinal.of Ordinal.omega0 + ((1 : ℕ) : NatOrdinal) := by
        have h1 : ((1 : ℕ) : NatOrdinal) = 1 := by exact_mod_cast rfl
        rwa [h1]
      obtain ⟨r, hval, h1, h2⟩ := eq_grid_of_isFinite_of_birthday_le 1 hy hb1
      by_cases hdy : ∃ e : Dyadic, stdPart y = ((e : ℚ) : ℝ)
      · obtain ⟨e, he⟩ := hdy
        refine .inr (.inl ⟨e, r, h1, ?_⟩)
        rw [hval, he, Real.toSurreal_ratCast]
      · push Not at hdy
        exact .inl ⟨stdPart y, r, h2 hdy, hval⟩
    · rcases lt_trichotomy y 0 with h0 | h0 | h0
      · have hneg := eq_of_pos_of_not_isFinite_of_birthday_le_omega0_add_one
          (y := -y) (neg_pos.2 h0) (fun h ↦ hy (by simpa using h.neg)) (by rwa [birthday_neg])
        rcases hneg with h | h | h
        · refine .inr (.inr (.inr (.inl ?_)))
          linarith
        · refine .inr (.inr (.inr (.inr (.inr (.inl ?_)))))
          linarith
        · refine .inr (.inr (.inr (.inr (.inr (.inr (.inr ?_))))))
          linarith
      · exact absurd (h0 ▸ isFinite_zero) hy
      · rcases eq_of_pos_of_not_isFinite_of_birthday_le_omega0_add_one h0 hy hb
          with h | h | h
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr (.inr (.inl h))))
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
  · rintro (⟨a, r, hr, rfl⟩ | ⟨e, r, hr, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl)
    · refine (birthday_realCast_add_dyadic_mul_wpow_le a r).trans ?_
      rw [show (1 : NatOrdinal) = ((1 : ℕ) : NatOrdinal) from by exact_mod_cast rfl]
      exact add_le_add le_rfl (by exact_mod_cast hr)
    · rcases eq_or_ne r 0 with rfl | hr0
      · rw [dyadic_cast_zero, zero_mul, add_zero]
        refine (birthday_dyadic_lt_omega0 e).le.trans ?_
        exact le_add_of_nonneg_right zero_le_one
      · refine (birthday_dyadic_add_dyadic_mul_wpow_le e hr0).trans ?_
        rw [show (1 : NatOrdinal) = ((1 : ℕ) : NatOrdinal) from by exact_mod_cast rfl]
        exact add_le_add le_rfl (by exact_mod_cast (by omega : Dyadic.hgt r - 1 ≤ 1))
    · rw [birthday_wpow_one]
      exact le_add_of_nonneg_right zero_le_one
    · rw [birthday_neg, birthday_wpow_one]
      exact le_add_of_nonneg_right zero_le_one
    · exact birthday_wpow_one_add_one.le
    · rw [birthday_neg]
      exact birthday_wpow_one_add_one.le
    · exact birthday_wpow_one_sub_one.le
    · rw [birthday_neg]
      exact birthday_wpow_one_sub_one.le

end Surreal

end
