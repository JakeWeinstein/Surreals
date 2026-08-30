import Infinity.GeometricBirthday

/-!
# Birthdays of `ω`-power scales, and the `ω²` upper bound for the geometric sum

The lower half of the geometric ladder (`Infinity.GeometricBirthday`) showed every Hahn
sum of `Σ ω⁻ᵏ` is born at or after day `ω·2`. This file supplies the **upper half of the
squeeze**: the canonical sum is born by day `ω·ω`.

The engine is a *halving-chain* recursion that realizes every value `ω⁻⁽ᵏ⁺¹⁾·2⁻ʲ` by an
explicit game of birthday at most `ω·(k+1) + j`, with no multiplication birthdays in
sight (the surreal multiplicative birthday bound is an open problem upstream):

* `mul_half_equiv` — **the halving lemma**: if a numeric game `G` has left moves `{0}`
  and every right-option value at least twice its own value, then `G · ½` is mutually
  cofinal with `!{0 | G}`. Halving is order-pinned; no simplicity needed.
* `exists_chain_package` — the double recursion: the scale step realizes `ω⁻⁽ᵏ⁺²⁾` as
  `!{0 | (chain games at scale k+1)}` (mutually cofinal with the `ω`-power game, whose
  right options the chain values undercut cofinally), and the halving lemma then walks
  down `2⁻ʲ` one day at a time.
* `birthday_wpow_neg_mul_half_pow_le` / `birthday_eps0_pow_le` :
  **`birthday (ω⁻⁽ᵏ⁺¹⁾·2⁻ʲ) ≤ ω·(k+1) + j`**; in particular
  `birthday (ω⁻ᵏ) ≤ ω·k`.
* `birthday_partialSum_geometric_le` : the partial sums of `Σ ω⁻ᵏ` have birthday below
  `ω·ω`.
* `birthday_hahnSum_geometric_le_omega_mul_omega` : **the canonical geometric sum is
  born by day `ω·ω`** (natural product; equals the ordinal `ω²`). With the lower bound,
  the canonical sum is squeezed into `[ω·2, ω²]`; the halo-minimality conjecture
  predicts its birthday is exactly `ω²` and its value `ω/(ω−1)`.
-/

open ArchimedeanClass IGame Set

universe u

noncomputable section

namespace Surreal

local notation "Ω" => NatOrdinal.of Ordinal.omega0

/-! ### Half: casts and the game `½` -/

private theorem half_pos'' : (0 : Dyadic) < Dyadic.half := by
  rw [← Dyadic.coe_lt_coe, Dyadic.coe_half]
  norm_num

private theorem half_cast_pos : (0 : Surreal) < ((Dyadic.half : Dyadic) : Surreal) :=
  dyadic_cast_pos half_pos''

private theorem two_mul_half_cast :
    (2 : Surreal) * ((Dyadic.half : Dyadic) : Surreal) = 1 := by
  have hd : (Dyadic.half + Dyadic.half : Dyadic) = 1 := by
    ext
    push_cast [Dyadic.coe_half]
    norm_num
  have h := dyadic_cast_add' Dyadic.half Dyadic.half
  rw [hd, dyadic_cast_one] at h
  linarith

private theorem mk_half_game : Surreal.mk (½ : IGame.{u}) = ((Dyadic.half : Dyadic) : Surreal) := by
  have h : ((Dyadic.half : Dyadic) : IGame.{u}) = (½ : IGame) := Dyadic.toIGame_half
  have h2 : Surreal.mk ((Dyadic.half : Dyadic) : IGame.{u}) = ((Dyadic.half : Dyadic) : Surreal) :=
    Surreal.mk_dyadic _
  rw [← h2]
  exact (Surreal.mk_eq (by rw [h])).symm

private theorem mulOption_def' (x y a b : IGame) :
    mulOption x y a b = a * y + x * b - a * b :=
  rfl

private theorem mk_mulOption'' (y w a b : IGame.{u}) [IGame.Numeric y] [IGame.Numeric w]
    [IGame.Numeric a] [IGame.Numeric b] :
    Surreal.mk (mulOption y w a b)
      = Surreal.mk a * Surreal.mk w + Surreal.mk y * Surreal.mk b
        - Surreal.mk a * Surreal.mk b := by
  show Surreal.mk (a * w + y * b - a * b) = _
  rw [Surreal.mk_sub, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_mul, Surreal.mk_mul]

private theorem mk_dyadic_mul_wpow_zero (q : Dyadic) :
    Surreal.mk ((q : IGame.{u}) * ω^ (0 : IGame)) = (q : Surreal) := by
  rw [Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow, Surreal.mk_zero, wpow_zero, mul_one]

/-! ### The halving lemma -/

/-- **The halving lemma**: a numeric game `G` with left moves `{0}` whose right-option
values all weigh at least twice its own value satisfies `G · ½ ≈ !{0 | G}` — halving is
order-pinned by mutual cofinality, with no simplicity theory. -/
theorem mul_half_equiv {G : IGame.{u}} [IGame.Numeric G]
    (hL : Gᴸ = {(0 : IGame)})
    (hR : ∀ r (hr : r ∈ Gᴿ),
      2 * Surreal.mk G ≤ @Surreal.mk r (IGame.Numeric.of_mem_moves hr)) :
    G * (½ : IGame) ≈ !{{(0 : IGame)} | {G}} := by
  have hCL : (!{{(0 : IGame)} | {G}} : IGame.{u})ᴸ = {(0 : IGame)} := leftMoves_ofSets ..
  have hCR : (!{{(0 : IGame)} | {G}} : IGame.{u})ᴿ = {G} := rightMoves_ofSets ..
  have hhalf := two_mul_half_cast
  have hhpos := half_cast_pos
  apply equiv_of_exists_le
  · rw [forall_moves_mul]
    intro p' a ha b hb
    cases p' with
    | left =>
      rw [hL, Set.mem_singleton_iff] at ha
      subst ha
      rw [show Player.left * Player.left = Player.left from rfl] at hb
      rw [show (½ : IGame.{u}).moves Player.left = (½ : IGame.{u})ᴸ from rfl,
        leftMoves_half, Set.mem_singleton_iff] at hb
      subst hb
      refine ⟨0, by rw [hCL]; exact Set.mem_singleton _, ?_⟩
      rw [← Surreal.mk_le_mk, mk_mulOption'', Surreal.mk_zero]
      ring_nf
      exact le_rfl
    | right =>
      rw [show Player.right * Player.left = Player.right from rfl] at hb
      rw [show (½ : IGame.{u}).moves Player.right = (½ : IGame.{u})ᴿ from rfl,
        rightMoves_half, Set.mem_singleton_iff] at hb
      subst hb
      haveI := IGame.Numeric.of_mem_moves ha
      refine ⟨0, by rw [hCL]; exact Set.mem_singleton _, ?_⟩
      rw [← Surreal.mk_le_mk, mk_mulOption'', mk_half_game, Surreal.mk_one, Surreal.mk_zero]
      have h1 := mul_le_mul_of_nonneg_right (hR a ha) hhpos.le
      have h2 : 2 * Surreal.mk G * ((Dyadic.half : Dyadic) : Surreal) = Surreal.mk G := by
        calc 2 * Surreal.mk G * ((Dyadic.half : Dyadic) : Surreal)
            = Surreal.mk G * (2 * ((Dyadic.half : Dyadic) : Surreal)) := by ring
          _ = Surreal.mk G * 1 := by rw [hhalf]
          _ = Surreal.mk G := mul_one _
      -- value: mk a · h + mk G · 1 − mk a · 1 ≤ 0
      nlinarith [h1, h2]
  · rw [forall_moves_mul]
    intro p' a ha b hb
    cases p' with
    | left =>
      rw [hL, Set.mem_singleton_iff] at ha
      subst ha
      rw [show Player.left * Player.right = Player.right from rfl] at hb
      rw [show (½ : IGame.{u}).moves Player.right = (½ : IGame.{u})ᴿ from rfl,
        rightMoves_half, Set.mem_singleton_iff] at hb
      subst hb
      refine ⟨G, by rw [hCR]; exact Set.mem_singleton _, ?_⟩
      rw [← Surreal.mk_le_mk, mk_mulOption'', Surreal.mk_zero, Surreal.mk_one]
      ring_nf
      exact le_rfl
    | right =>
      rw [show Player.right * Player.right = Player.left from rfl] at hb
      rw [show (½ : IGame.{u}).moves Player.left = (½ : IGame.{u})ᴸ from rfl,
        leftMoves_half, Set.mem_singleton_iff] at hb
      subst hb
      haveI := IGame.Numeric.of_mem_moves ha
      refine ⟨G, by rw [hCR]; exact Set.mem_singleton _, ?_⟩
      rw [← Surreal.mk_le_mk, mk_mulOption'', mk_half_game, Surreal.mk_zero]
      have h1 := mul_le_mul_of_nonneg_right (hR a ha) hhpos.le
      have h2 : 2 * Surreal.mk G * ((Dyadic.half : Dyadic) : Surreal) = Surreal.mk G := by
        calc 2 * Surreal.mk G * ((Dyadic.half : Dyadic) : Surreal)
            = Surreal.mk G * (2 * ((Dyadic.half : Dyadic) : Surreal)) := by ring
          _ = Surreal.mk G * 1 := by rw [hhalf]
          _ = Surreal.mk G := mul_one _
      -- value: mk G ≤ mk a · h + 0 − 0
      nlinarith [h1, h2]
  · rw [hCL]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine ⟨mulOption G (½ : IGame) 0 0,
      mulOption_mem_moves_mul (px := Player.left) (py := Player.left)
        (by rw [hL]; exact Set.mem_singleton _)
        (by rw [show (½ : IGame.{u}).moves Player.left = (½ : IGame.{u})ᴸ from rfl,
          leftMoves_half]; exact Set.mem_singleton _), ?_⟩
    rw [← Surreal.mk_le_mk, mk_mulOption'', Surreal.mk_zero]
    ring_nf
    exact le_rfl
  · rw [hCR]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    refine ⟨mulOption G (½ : IGame) 0 1,
      mulOption_mem_moves_mul (px := Player.left) (py := Player.right)
        (by rw [hL]; exact Set.mem_singleton _)
        (by rw [show (½ : IGame.{u}).moves Player.right = (½ : IGame.{u})ᴿ from rfl,
          rightMoves_half]; exact Set.mem_singleton _), ?_⟩
    rw [← Surreal.mk_le_mk, mk_mulOption'', Surreal.mk_zero, Surreal.mk_one]
    ring_nf
    exact le_rfl

/-! ### The chain step -/

/-- Given a chain game for a positive value `x`, `!{0 | G}` is a chain game for `x/2`,
one day later. -/
private theorem chain_step {G : IGame.{u}} (hGn : IGame.Numeric G) {x : Surreal}
    (hval : @Surreal.mk G hGn = x) (hx : 0 < x)
    (hL : Gᴸ = {(0 : IGame)})
    (hR : ∀ r (hr : r ∈ Gᴿ),
      2 * x ≤ @Surreal.mk r (@IGame.Numeric.of_mem_moves _ _ _ hGn hr)) :
    ∃ (G' : IGame.{u}) (hG'n : IGame.Numeric G'),
      @Surreal.mk G' hG'n = x * ((Dyadic.half : Dyadic) : Surreal) ∧
      G'ᴸ = {(0 : IGame)} ∧
      (∀ r (hr : r ∈ G'ᴿ),
        2 * (x * ((Dyadic.half : Dyadic) : Surreal))
          ≤ @Surreal.mk r (@IGame.Numeric.of_mem_moves _ _ _ hG'n hr)) ∧
      G'.birthday ≤ G.birthday + 1 := by
  haveI := hGn
  have hR' : ∀ r (hr : r ∈ Gᴿ),
      2 * Surreal.mk G ≤ @Surreal.mk r (IGame.Numeric.of_mem_moves hr) := by
    intro r hr
    rw [hval]
    exact hR r hr
  have hequiv := mul_half_equiv hL hR'
  have hG'n : IGame.Numeric (!{{(0 : IGame.{u})} | {G}}) := by
    refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
    · rw [leftMoves_ofSets, Set.mem_singleton_iff] at hy
      rw [rightMoves_ofSets, Set.mem_singleton_iff] at hz
      subst hy
      subst hz
      rw [← Surreal.mk_lt_mk, Surreal.mk_zero, hval]
      exact hx
    · cases p with
      | left =>
        rw [moves_ofSets, Set.mem_singleton_iff] at hy
        subst hy
        infer_instance
      | right =>
        rw [moves_ofSets, Set.mem_singleton_iff] at hy
        subst hy
        exact hGn
  refine ⟨!{{(0 : IGame.{u})} | {G}}, hG'n, ?_, leftMoves_ofSets .., ?_, ?_⟩
  · have h1 : Surreal.mk (G * (½ : IGame.{u})) = x * ((Dyadic.half : Dyadic) : Surreal) := by
      rw [Surreal.mk_mul, mk_half_game, hval]
    rw [← h1]
    exact (Surreal.mk_eq hequiv).symm
  · intro r hr
    rw [show (!{{(0 : IGame.{u})} | {G}})ᴿ = {G} from rightMoves_ofSets ..,
      Set.mem_singleton_iff] at hr
    subst hr
    have h2 : 2 * (x * ((Dyadic.half : Dyadic) : Surreal)) = x := by
      calc 2 * (x * ((Dyadic.half : Dyadic) : Surreal))
          = x * (2 * ((Dyadic.half : Dyadic) : Surreal)) := by ring
        _ = x * 1 := by rw [two_mul_half_cast]
        _ = x := mul_one x
    rw [h2]
    exact le_of_eq hval.symm
  · rw [IGame.birthday_ofSets]
    refine max_le ?_ ?_
    · refine csSup_le' ?_
      rintro o ⟨g, hg, rfl⟩
      rw [Set.mem_singleton_iff] at hg
      subst hg
      rw [Function.comp_apply, Order.succ_eq_add_one, IGame.birthday_zero, zero_add]
      exact NatOrdinal.le_add_left
    · refine csSup_le' ?_
      rintro o ⟨g, hg, rfl⟩
      rw [Set.mem_singleton_iff] at hg
      subst hg
      rw [Function.comp_apply, Order.succ_eq_add_one]

/-! ### The scale step -/

private theorem coe_half_pow (j : ℕ) : ((Dyadic.half ^ j : Dyadic) : ℚ) = (2 : ℚ)⁻¹ ^ j := by
  push_cast [Dyadic.coe_half]
  rfl

private theorem half_pow_pos (j : ℕ) : (0 : Dyadic) < Dyadic.half ^ j :=
  pow_pos half_pos'' j

/-- Every positive dyadic is undercut by a power of `½`. -/
private theorem exists_half_pow_le {q : Dyadic} (hq : 0 < q) :
    ∃ j : ℕ, Dyadic.half ^ j ≤ q := by
  obtain ⟨e, he⟩ := q.den_mem_powers
  refine ⟨e, ?_⟩
  rw [← Dyadic.coe_le_coe, coe_half_pow]
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hnum : 1 ≤ q.num := Rat.num_pos.2 hq'
  have hden : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.den_pos
  have hqval : (q : ℚ) = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den _).symm
  have hpow : ((2 : ℚ)⁻¹) ^ e = 1 / (q.den : ℚ) := by
    rw [← he]
    push_cast
    rw [inv_pow]
    rw [one_div]
  rw [hpow, hqval]
  rw [div_le_div_iff_of_pos_right hden]
  exact_mod_cast hnum

private theorem leftMoves_wpow_neg_natCast (m : ℕ) :
    (ω^ (-((m : ℕ) : IGame.{u})))ᴸ = {0} := by
  have h : (-((m : ℕ) : IGame.{u}))ᴸ = ∅ := by
    rw [show (-((m : ℕ) : IGame.{u}))ᴸ = ((-((m : ℕ) : IGame.{u}))).moves Player.left from rfl,
      moves_neg, show -Player.left = Player.right from rfl,
      show (((m : ℕ) : IGame.{u})).moves Player.right = (((m : ℕ) : IGame.{u}))ᴿ from rfl,
      rightMoves_natCast]
    exact Set.neg_empty
  rw [leftMoves_wpow, h]
  simp

private theorem rightMoves_wpow_neg_natCast_succ (m : ℕ) :
    (ω^ (-(((m + 1) : ℕ) : IGame.{u})))ᴿ =
      (fun q : Dyadic ↦ (q : IGame) * ω^ (-((m : ℕ) : IGame))) '' Set.Ioi 0 := by
  have h : (-(((m + 1) : ℕ) : IGame.{u}))ᴿ = {-((m : ℕ) : IGame)} := by
    rw [show (-(((m + 1) : ℕ) : IGame.{u}))ᴿ
        = ((-(((m + 1) : ℕ) : IGame.{u}))).moves Player.right from rfl, moves_neg,
      show -Player.right = Player.left from rfl,
      show ((((m + 1) : ℕ) : IGame.{u})).moves Player.left
        = ((((m + 1) : ℕ) : IGame.{u}))ᴸ from rfl, leftMoves_natCast_succ' m]
    exact Set.neg_singleton _
  rw [rightMoves_wpow, h, Set.image2_singleton_right]

private theorem mk_wpow_neg_natCast (m : ℕ) :
    Surreal.mk (ω^ (-((m : ℕ) : IGame.{u}))) = ω^ (-((m : ℕ) : Surreal)) := by
  rw [Surreal.mk_wpow]
  have h : Surreal.mk (-((m : ℕ) : IGame.{u})) = -((m : ℕ) : Surreal) := by
    show Surreal.mk (-((m : ℕ) : IGame.{u})) = _
    rw [Surreal.mk_neg, Surreal.mk_natCast]
  rw [h]

private theorem two_cast_eq : ((2 : Dyadic) : Surreal) = 2 := by
  have h : ((2 : Dyadic) : Surreal) = (((2 : ℕ) : Dyadic) : Surreal) := by norm_num
  rw [h, dyadic_cast_natCast]
  norm_num

/-- The key domination: twice the next scale sits below every halving of the current
scale. -/
private theorem two_mul_wpow_le (k : ℕ) (j : ℕ) :
    2 * ω^ (-(((k + 2) : ℕ) : Surreal))
      ≤ ω^ (-(((k + 1) : ℕ) : Surreal)) * ((Dyadic.half ^ j : Dyadic) : Surreal) := by
  have hsplit : (-(((k + 2) : ℕ) : Surreal)) = (-1 : Surreal) + (-(((k + 1) : ℕ) : Surreal)) := by
    push_cast
    ring
  rw [hsplit, wpow_add]
  have hcore : (2 : Surreal) * ω^ (-1 : Surreal) ≤ ((Dyadic.half ^ j : Dyadic) : Surreal) := by
    have h := dyadic_mul_wpow_lt (s := (2 : Dyadic)) (half_pow_pos j)
    rw [two_cast_eq] at h
    exact h.le
  calc 2 * (ω^ (-1 : Surreal) * ω^ (-(((k + 1) : ℕ) : Surreal)))
      = (2 * ω^ (-1 : Surreal)) * ω^ (-(((k + 1) : ℕ) : Surreal)) := by ring
    _ ≤ ((Dyadic.half ^ j : Dyadic) : Surreal) * ω^ (-(((k + 1) : ℕ) : Surreal)) :=
        mul_le_mul_of_nonneg_right hcore (wpow_pos _).le
    _ = ω^ (-(((k + 1) : ℕ) : Surreal)) * ((Dyadic.half ^ j : Dyadic) : Surreal) := by ring

/-- **The scale step**: from a chain family realizing `ω⁻⁽ᵏ⁺¹⁾·2⁻ʲ` for every `j`, the
cut `!{0 | family}` realizes `ω⁻⁽ᵏ⁺²⁾`, one `ω`-block of days later. -/
private theorem scale_start (k : ℕ)
    (g : ℕ → IGame.{u}) (hgn : ∀ j, (g j).Numeric)
    (hgv : ∀ j, @Surreal.mk (g j) (hgn j)
      = ω^ (-(((k + 1) : ℕ) : Surreal)) * ((Dyadic.half ^ j : Dyadic) : Surreal))
    (hgb : ∀ j, (g j).birthday
      ≤ NatOrdinal.of Ordinal.omega0 * (((k + 1) : ℕ) : NatOrdinal) + (j : NatOrdinal)) :
    ∃ (G : IGame.{u}) (hGn : IGame.Numeric G),
      @Surreal.mk G hGn = ω^ (-(((k + 2) : ℕ) : Surreal)) ∧
      Gᴸ = {(0 : IGame)} ∧
      (∀ r (hr : r ∈ Gᴿ),
        2 * ω^ (-(((k + 2) : ℕ) : Surreal))
          ≤ @Surreal.mk r (@IGame.Numeric.of_mem_moves _ _ _ hGn hr)) ∧
      G.birthday ≤ NatOrdinal.of Ordinal.omega0 * (((k + 2) : ℕ) : NatOrdinal) := by
  haveI : ∀ j, (g j).Numeric := hgn
  set C : IGame.{u} := !{{(0 : IGame)} | Set.range g} with hC
  have hCL : Cᴸ = {(0 : IGame)} := leftMoves_ofSets ..
  have hCR : Cᴿ = Set.range g := rightMoves_ofSets ..
  have hWL := leftMoves_wpow_neg_natCast.{u} (k + 2)
  have hWR := rightMoves_wpow_neg_natCast_succ.{u} (k + 1)
  -- mutual cofinality of the `ω`-power game with the cut
  have hequiv : ω^ (-(((k + 2) : ℕ) : IGame.{u})) ≈ C := by
    apply equiv_of_exists_le
    · intro a ha
      rw [show (ω^ (-(((k + 2) : ℕ) : IGame.{u}))).moves Player.left
          = (ω^ (-(((k + 2) : ℕ) : IGame.{u})))ᴸ from rfl, hWL, Set.mem_singleton_iff] at ha
      subst ha
      exact ⟨0, by rw [hCL]; exact Set.mem_singleton _, le_rfl⟩
    · intro a ha
      rw [show (ω^ (-(((k + 2) : ℕ) : IGame.{u}))).moves Player.right
          = (ω^ (-(((k + 2) : ℕ) : IGame.{u})))ᴿ from rfl,
        show ((k + 2 : ℕ) : IGame.{u}) = (((k + 1) + 1 : ℕ) : IGame) from rfl, hWR] at ha
      obtain ⟨q, hq, rfl⟩ := ha
      obtain ⟨j, hj⟩ := exists_half_pow_le hq
      refine ⟨g j, by rw [hCR]; exact Set.mem_range_self j, ?_⟩
      rw [← Surreal.mk_le_mk, hgv j, Surreal.mk_mul, Surreal.mk_dyadic, mk_wpow_neg_natCast]
      have hle : ((Dyadic.half ^ j : Dyadic) : Surreal) ≤ (q : Surreal) := by
        rcases eq_or_lt_of_le hj with he | hl
        · rw [he]
        · exact (dyadic_cast_lt hl).le
      calc ω^ (-(((k + 1) : ℕ) : Surreal)) * ((Dyadic.half ^ j : Dyadic) : Surreal)
          ≤ ω^ (-(((k + 1) : ℕ) : Surreal)) * (q : Surreal) :=
            mul_le_mul_of_nonneg_left hle (wpow_pos _).le
        _ = (q : Surreal) * ω^ (-(((k + 1) : ℕ) : Surreal)) := by ring
    · rw [hCL]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      refine ⟨0, ?_, le_rfl⟩
      rw [show (ω^ (-(((k + 2) : ℕ) : IGame.{u}))).moves Player.left
          = (ω^ (-(((k + 2) : ℕ) : IGame.{u})))ᴸ from rfl, hWL]
      exact Set.mem_singleton _
    · rw [hCR]
      rintro b ⟨j, rfl⟩
      refine ⟨((Dyadic.half ^ j : Dyadic) : IGame) * ω^ (-(((k + 1) : ℕ) : IGame)), ?_, ?_⟩
      · rw [show (ω^ (-(((k + 2) : ℕ) : IGame.{u}))).moves Player.right
            = (ω^ (-(((k + 2) : ℕ) : IGame.{u})))ᴿ from rfl,
          show ((k + 2 : ℕ) : IGame.{u}) = (((k + 1) + 1 : ℕ) : IGame) from rfl, hWR]
        exact Set.mem_image_of_mem _ (half_pow_pos j)
      · rw [← Surreal.mk_le_mk, hgv j, Surreal.mk_mul, Surreal.mk_dyadic, mk_wpow_neg_natCast]
        calc ((Dyadic.half ^ j : Dyadic) : Surreal) * ω^ (-(((k + 1) : ℕ) : Surreal))
            = ω^ (-(((k + 1) : ℕ) : Surreal)) * ((Dyadic.half ^ j : Dyadic) : Surreal) := by
              ring
          _ ≤ _ := le_rfl
  -- numericity
  have hCn : IGame.Numeric C := by
    refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
    · rw [hC, leftMoves_ofSets, Set.mem_singleton_iff] at hy
      rw [hC, rightMoves_ofSets] at hz
      obtain ⟨j, rfl⟩ := hz
      subst hy
      rw [← Surreal.mk_lt_mk, Surreal.mk_zero, hgv j]
      have h1 := wpow_pos (-(((k + 1) : ℕ) : Surreal))
      have h2 := dyadic_cast_pos (half_pow_pos j)
      exact mul_pos h1 h2
    · cases p with
      | left =>
        rw [hC, moves_ofSets, Set.mem_singleton_iff] at hy
        subst hy
        infer_instance
      | right =>
        rw [hC, moves_ofSets] at hy
        obtain ⟨j, rfl⟩ := hy
        exact hgn j
  refine ⟨C, hCn, ?_, hCL, ?_, ?_⟩
  · have h1 : Surreal.mk (ω^ (-(((k + 2) : ℕ) : IGame.{u})))
        = ω^ (-(((k + 2) : ℕ) : Surreal)) := mk_wpow_neg_natCast (k + 2)
    rw [← h1]
    exact (Surreal.mk_eq hequiv).symm
  · intro r hr
    rw [hCR] at hr
    obtain ⟨j, rfl⟩ := hr
    rw [show @Surreal.mk (g j) _ = ω^ (-(((k + 1) : ℕ) : Surreal))
        * ((Dyadic.half ^ j : Dyadic) : Surreal) from hgv j]
    exact two_mul_wpow_le k j
  · rw [hC, IGame.birthday_ofSets]
    refine max_le ?_ ?_
    · refine csSup_le' ?_
      rintro o ⟨x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [Function.comp_apply, Order.succ_eq_add_one, IGame.birthday_zero, zero_add]
      have h1 : ((1 : ℕ) : NatOrdinal) < Ω := NatOrdinal.natCast_lt_omega0 1
      rw [Nat.cast_one] at h1
      calc (1 : NatOrdinal) ≤ Ω := h1.le
        _ ≤ Ω * (((k + 2) : ℕ) : NatOrdinal) := by
            refine le_mul_of_one_le_right ?_ ?_
            · exact le_trans zero_le_one h1.le
            · exact_mod_cast (by omega : 1 ≤ k + 2)
    · refine csSup_le' ?_
      rintro o ⟨x, ⟨j, rfl⟩, rfl⟩
      rw [Function.comp_apply, Order.succ_eq_add_one]
      refine (add_le_add (hgb j) (le_refl 1)).trans ?_
      have hj1 : ((j : ℕ) : NatOrdinal) + 1 ≤ Ω := by
        have h := NatOrdinal.natCast_lt_omega0 (j + 1)
        have h2 : (((j + 1) : ℕ) : NatOrdinal) = ((j : ℕ) : NatOrdinal) + 1 := by push_cast; ring
        rw [h2] at h
        exact h.le
      calc Ω * (((k + 1) : ℕ) : NatOrdinal) + ((j : ℕ) : NatOrdinal) + 1
          = Ω * (((k + 1) : ℕ) : NatOrdinal) + (((j : ℕ) : NatOrdinal) + 1) := by
            rw [add_assoc]
        _ ≤ Ω * (((k + 1) : ℕ) : NatOrdinal) + Ω := add_le_add le_rfl hj1
        _ = Ω * ((((k + 1) : ℕ) : NatOrdinal) + 1) := by rw [mul_add, mul_one]
        _ = Ω * (((k + 2) : ℕ) : NatOrdinal) := by
            congr 1
            push_cast
            ring

/-! ### The chain package: every `ω⁻⁽ᵏ⁺¹⁾·2⁻ʲ`, realized -/

/-- Iterating the chain step down the halving chain. -/
private theorem chain_iterate {x : Surreal.{u}} (hx : 0 < x) {β : NatOrdinal.{u}}
    (base : ∃ (G : IGame.{u}) (hGn : IGame.Numeric G),
      @Surreal.mk G hGn = x ∧ Gᴸ = {(0 : IGame)} ∧
      (∀ r (hr : r ∈ Gᴿ),
        2 * x ≤ @Surreal.mk r (@IGame.Numeric.of_mem_moves _ _ _ hGn hr)) ∧
      G.birthday ≤ β) :
    ∀ j : ℕ, ∃ (G : IGame.{u}) (hGn : IGame.Numeric G),
      @Surreal.mk G hGn = x * ((Dyadic.half ^ j : Dyadic) : Surreal) ∧
      Gᴸ = {(0 : IGame)} ∧
      (∀ r (hr : r ∈ Gᴿ),
        2 * (x * ((Dyadic.half ^ j : Dyadic) : Surreal))
          ≤ @Surreal.mk r (@IGame.Numeric.of_mem_moves _ _ _ hGn hr)) ∧
      G.birthday ≤ β + (j : NatOrdinal) := by
  intro j
  induction j with
  | zero =>
    obtain ⟨G, hGn, hval, hL, hR, hb⟩ := base
    have h1 : ((Dyadic.half ^ 0 : Dyadic) : Surreal) = 1 := by
      rw [pow_zero]
      exact dyadic_cast_one
    refine ⟨G, hGn, ?_, hL, ?_, ?_⟩
    · rw [h1, mul_one]
      exact hval
    · intro r hr
      rw [h1, mul_one]
      exact hR r hr
    · refine hb.trans ?_
      have h0 : ((0 : ℕ) : NatOrdinal) = 0 := by exact_mod_cast rfl
      rw [h0, add_zero]
  | succ j ihj =>
    obtain ⟨G, hGn, hval, hL, hR, hb⟩ := ihj
    have hxj : (0 : Surreal) < x * ((Dyadic.half ^ j : Dyadic) : Surreal) :=
      mul_pos hx (dyadic_cast_pos (half_pow_pos j))
    obtain ⟨G', hG'n, hval', hL', hR', hb'⟩ := chain_step hGn hval hxj hL hR
    have hpow : x * ((Dyadic.half ^ j : Dyadic) : Surreal) * ((Dyadic.half : Dyadic) : Surreal)
        = x * ((Dyadic.half ^ (j + 1) : Dyadic) : Surreal) := by
      rw [mul_assoc, ← dyadic_cast_mul', ← pow_succ]
    refine ⟨G', hG'n, ?_, hL', ?_, ?_⟩
    · rw [hval', hpow]
    · intro r hr
      rw [← hpow]
      exact hR' r hr
    · refine (hb'.trans (add_le_add hb (le_refl 1))).trans ?_
      rw [add_assoc]
      refine add_le_add le_rfl ?_
      have h1 : ((j : ℕ) : NatOrdinal) + 1 = (((j + 1) : ℕ) : NatOrdinal) := by
        push_cast
        ring
      rw [h1]

/-- The double recursion: for every `k` and `j` there is a chain game realizing
`ω⁻⁽ᵏ⁺¹⁾·2⁻ʲ` with birthday at most `ω·(k+1) + j`. -/
private theorem exists_chain_package :
    ∀ k : ℕ, ∀ j : ℕ, ∃ (G : IGame.{u}) (hGn : IGame.Numeric G),
      @Surreal.mk G hGn
        = ω^ (-(((k + 1) : ℕ) : Surreal)) * ((Dyadic.half ^ j : Dyadic) : Surreal) ∧
      Gᴸ = {(0 : IGame)} ∧
      (∀ r (hr : r ∈ Gᴿ),
        2 * (ω^ (-(((k + 1) : ℕ) : Surreal)) * ((Dyadic.half ^ j : Dyadic) : Surreal))
          ≤ @Surreal.mk r (@IGame.Numeric.of_mem_moves _ _ _ hGn hr)) ∧
      G.birthday ≤ NatOrdinal.of Ordinal.omega0 * (((k + 1) : ℕ) : NatOrdinal)
        + (j : NatOrdinal) := by
  intro k
  induction k with
  | zero =>
    -- scale 1: the base is the cut on positive dyadics, pinned to `ω^(−1)`
    have hcast1 : ω^ (-((1 : ℕ) : Surreal.{u})) = ω^ (-1 : Surreal) := by
      congr 1
      push_cast
      ring
    have hbase : ∃ (G : IGame.{u}) (hGn : IGame.Numeric G),
        @Surreal.mk G hGn = ω^ (-((1 : ℕ) : Surreal)) ∧
        Gᴸ = {(0 : IGame)} ∧
        (∀ r (hr : r ∈ Gᴿ),
          2 * ω^ (-((1 : ℕ) : Surreal))
            ≤ @Surreal.mk r (@IGame.Numeric.of_mem_moves _ _ _ ‹_› hr)) ∧
        G.birthday ≤ NatOrdinal.of Ordinal.omega0 := by
      set C : IGame.{u} := !{{(0 : IGame)} | (fun q : Dyadic ↦ (q : IGame)) '' Set.Ioi 0}
        with hC
      have hCL : Cᴸ = {(0 : IGame)} := leftMoves_ofSets ..
      have hCR : Cᴿ = (fun q : Dyadic ↦ (q : IGame)) '' Set.Ioi 0 := rightMoves_ofSets ..
      have hequiv : ω^ (-1 : IGame.{u}) ≈ C := by
        apply equiv_of_exists_le
        · intro a ha
          rw [show (ω^ (-1 : IGame.{u})).moves Player.left = (ω^ (-1 : IGame.{u}))ᴸ from rfl,
            leftMoves_wpow_neg_one', Set.mem_singleton_iff] at ha
          subst ha
          exact ⟨0, by rw [hCL]; exact Set.mem_singleton _, le_rfl⟩
        · intro a ha
          rw [show (ω^ (-1 : IGame.{u})).moves Player.right = (ω^ (-1 : IGame.{u}))ᴿ from rfl,
            rightMoves_wpow_neg_one'] at ha
          obtain ⟨q, hq, rfl⟩ := ha
          refine ⟨(q : IGame), by rw [hCR]; exact Set.mem_image_of_mem _ hq, ?_⟩
          rw [← Surreal.mk_le_mk, mk_dyadic_mul_wpow_zero, Surreal.mk_dyadic]
        · rw [hCL]
          intro b hb
          rw [Set.mem_singleton_iff] at hb
          rw [hb]
          refine ⟨0, ?_, le_rfl⟩
          rw [show (ω^ (-1 : IGame.{u})).moves Player.left = (ω^ (-1 : IGame.{u}))ᴸ from rfl,
            leftMoves_wpow_neg_one']
          exact Set.mem_singleton _
        · rw [hCR]
          rintro b ⟨q, hq, rfl⟩
          refine ⟨(q : IGame) * ω^ (0 : IGame), ?_, ?_⟩
          · rw [show (ω^ (-1 : IGame.{u})).moves Player.right = (ω^ (-1 : IGame.{u}))ᴿ from rfl,
              rightMoves_wpow_neg_one']
            exact Set.mem_image_of_mem _ hq
          · rw [← Surreal.mk_le_mk, mk_dyadic_mul_wpow_zero, Surreal.mk_dyadic]
      have hCn : IGame.Numeric C := by
        refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
        · rw [hC, leftMoves_ofSets, Set.mem_singleton_iff] at hy
          rw [hC, rightMoves_ofSets] at hz
          obtain ⟨q, hq, rfl⟩ := hz
          subst hy
          rw [← Surreal.mk_lt_mk, Surreal.mk_zero, Surreal.mk_dyadic]
          exact dyadic_cast_pos hq
        · cases p with
          | left =>
            rw [hC, moves_ofSets, Set.mem_singleton_iff] at hy
            subst hy
            infer_instance
          | right =>
            rw [hC, moves_ofSets] at hy
            obtain ⟨q, hq, rfl⟩ := hy
            infer_instance
      refine ⟨C, hCn, ?_, hCL, ?_, ?_⟩
      · rw [hcast1, ← mk_wpow_neg_one']
        exact (Surreal.mk_eq hequiv).symm
      · intro r hr
        rw [hCR] at hr
        obtain ⟨q, hq, rfl⟩ := hr
        rw [show @Surreal.mk ((q : IGame.{u})) _ = (q : Surreal) from Surreal.mk_dyadic q,
          hcast1]
        have h := dyadic_mul_wpow_lt (s := (2 : Dyadic)) hq
        rw [two_cast_eq] at h
        exact h.le
      · rw [hC, IGame.birthday_ofSets]
        refine max_le ?_ ?_
        · refine csSup_le' ?_
          rintro o ⟨g, hg, rfl⟩
          rw [Set.mem_singleton_iff] at hg
          subst hg
          rw [Function.comp_apply, Order.succ_eq_add_one, IGame.birthday_zero, zero_add]
          have h1 : ((1 : ℕ) : NatOrdinal) < NatOrdinal.of Ordinal.omega0 :=
            NatOrdinal.natCast_lt_omega0 1
          rw [Nat.cast_one] at h1
          exact h1.le
        · refine csSup_le' ?_
          rintro o ⟨g, ⟨q, hq, rfl⟩, rfl⟩
          rw [Function.comp_apply, Order.succ_eq_add_one, ← Order.succ_eq_add_one]
          exact Order.succ_le_of_lt
            (IGame.short_iff_birthday_finite.1 (IGame.Short.dyadic q))
    intro j
    have hpos : (0 : Surreal.{u}) < ω^ (-((1 : ℕ) : Surreal)) := wpow_pos _
    have h := chain_iterate hpos hbase j
    obtain ⟨G, hGn, hval, hL, hR, hb⟩ := h
    refine ⟨G, hGn, hval, hL, hR, hb.trans ?_⟩
    refine add_le_add ?_ le_rfl
    rw [show (((0 + 1) : ℕ) : NatOrdinal) = 1 from by push_cast; ring, mul_one]
  | succ k ih =>
    choose g hgn hgv hgL hgR hgb using ih
    obtain ⟨G, hGn, hval, hL, hR, hb⟩ := scale_start k g hgn hgv hgb
    intro j
    have hpos : (0 : Surreal.{u}) < ω^ (-(((k + 2) : ℕ) : Surreal)) := wpow_pos _
    have h := chain_iterate hpos ⟨G, hGn, hval, hL, hR, hb⟩ j
    obtain ⟨G', hG'n, hval', hL', hR', hb'⟩ := h
    exact ⟨G', hG'n, hval', hL', hR', hb'⟩

/-- **The birthday of every halved `ω`-power scale**:
`birthday (ω⁻⁽ᵏ⁺¹⁾ · 2⁻ʲ) ≤ ω·(k+1) + j`. -/
theorem birthday_wpow_neg_mul_half_pow_le (k j : ℕ) :
    (ω^ (-(((k + 1) : ℕ) : Surreal.{u})) * ((Dyadic.half ^ j : Dyadic) : Surreal)).birthday
      ≤ NatOrdinal.of Ordinal.omega0 * (((k + 1) : ℕ) : NatOrdinal) + (j : NatOrdinal) := by
  obtain ⟨G, hGn, hval, -, -, hb⟩ := exists_chain_package k j
  haveI := hGn
  refine le_of_eq_of_le (congrArg birthday hval.symm) ?_
  exact (birthday_mk_le G).trans hb

/-- `birthday (ω⁻⁽ᵏ⁺¹⁾) ≤ ω·(k+1)`. -/
theorem birthday_wpow_neg_natCast_le (k : ℕ) :
    (ω^ (-(((k + 1) : ℕ) : Surreal.{u}))).birthday
      ≤ NatOrdinal.of Ordinal.omega0 * (((k + 1) : ℕ) : NatOrdinal) := by
  have h := birthday_wpow_neg_mul_half_pow_le.{u} k 0
  have h1 : ((Dyadic.half ^ 0 : Dyadic) : Surreal.{u}) = 1 := by
    rw [pow_zero]
    exact dyadic_cast_one
  rw [h1, mul_one] at h
  have h0 : ((0 : ℕ) : NatOrdinal) = 0 := by exact_mod_cast rfl
  rwa [h0, add_zero] at h

/-! ### The `ω²` upper bound for the canonical geometric sum -/

/-- Birthdays of the geometric terms: `birthday (ω⁻ᵏ) ≤ ω·(k+1) + (k+1)`. -/
theorem birthday_eps0_pow_le (k : ℕ) :
    ((eps0 : Surreal.{0}) ^ k).birthday
      ≤ NatOrdinal.of Ordinal.omega0 * (((k + 1) : ℕ) : NatOrdinal)
        + (((k + 1) : ℕ) : NatOrdinal) := by
  cases k with
  | zero =>
    rw [pow_zero, birthday_one]
    have h1 : (1 : NatOrdinal) ≤ (((0 + 1) : ℕ) : NatOrdinal) := by
      exact_mod_cast Nat.le_refl 1
    exact h1.trans NatOrdinal.le_add_left
  | succ k =>
    have hval : (eps0 : Surreal.{0}) ^ (k + 1) = ω^ (-(((k + 1) : ℕ) : Surreal.{0})) := by
      rw [eps0_def, wpow_neg, wpow_natCast, inv_pow]
    rw [hval]
    refine (birthday_wpow_neg_natCast_le k).trans ?_
    refine le_trans ?_ NatOrdinal.le_add_right
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    exact_mod_cast Nat.le_succ (k + 1)

/-- The bounding shape `ω·m + m` sits below `ω·ω`. -/
private theorem omega_shape_le_omega_mul_omega (m : ℕ) {x : NatOrdinal}
    (h : x ≤ NatOrdinal.of Ordinal.omega0 * (m : NatOrdinal) + (m : NatOrdinal)) :
    x ≤ NatOrdinal.of Ordinal.omega0 * NatOrdinal.of Ordinal.omega0 := by
  refine h.trans ?_
  have hm : ((m : ℕ) : NatOrdinal) < NatOrdinal.of Ordinal.omega0 :=
    NatOrdinal.natCast_lt_omega0 m
  calc NatOrdinal.of Ordinal.omega0 * (m : NatOrdinal) + (m : NatOrdinal)
      ≤ NatOrdinal.of Ordinal.omega0 * (m : NatOrdinal) + NatOrdinal.of Ordinal.omega0 :=
        add_le_add le_rfl hm.le
    _ = NatOrdinal.of Ordinal.omega0 * ((m : NatOrdinal) + 1) := by rw [mul_add, mul_one]
    _ ≤ NatOrdinal.of Ordinal.omega0 * NatOrdinal.of Ordinal.omega0 := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        have h1 : (((m + 1) : ℕ) : NatOrdinal) = ((m : ℕ) : NatOrdinal) + 1 := by
          push_cast
          ring
        rw [← h1]
        exact (NatOrdinal.natCast_lt_omega0 (m + 1)).le

/-- The partial sums of the geometric series are all of the shape `ω·m + m`. -/
theorem birthday_partialSum_geometric_le (n : ℕ) :
    ∃ m : ℕ, (partialSum (fun k ↦ (eps0 : Surreal.{0}) ^ k) n).birthday
      ≤ NatOrdinal.of Ordinal.omega0 * (m : NatOrdinal) + (m : NatOrdinal) := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    rw [partialSum_zero, birthday_zero]
    exact bot_le
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + (n + 1), ?_⟩
    rw [partialSum_succ]
    refine (birthday_add_le _ _).trans ?_
    refine (add_le_add hm (birthday_eps0_pow_le n)).trans (le_of_eq ?_)
    push_cast
    ring

/-- **The canonical geometric sum is born by day `ω·ω`** (the natural product `Ω·Ω`,
which coincides with the ordinal `ω²`). With
`omega0_mul_two_le_birthday_hahnSum_geometric` this squeezes the canonical sum of
`Σ ω⁻ᵏ` into the window `[ω·2, ω²]`; halo minimality predicts exactly `ω²`, with value
`ω/(ω−1)`. -/
theorem birthday_hahnSum_geometric_le_omega_mul_omega :
    (hahnSum geometric_strict_dominating).birthday
      ≤ NatOrdinal.of Ordinal.omega0 * NatOrdinal.of Ordinal.omega0 := by
  refine (birthday_hahnSum_le_sup geometric_strict_dominating).trans ?_
  refine ciSup_le fun p ↦ ?_
  obtain ⟨m₁, hm₁⟩ := birthday_partialSum_geometric_le p.1
  have hm₂ := birthday_eps0_pow_le p.1
  -- assemble the shape bound
  have hsmul : (p.2 + 1) • ((eps0 : Surreal.{0}) ^ p.1).birthday
      ≤ NatOrdinal.of Ordinal.omega0 * (((p.2 + 1) * (p.1 + 1) : ℕ) : NatOrdinal)
        + (((p.2 + 1) * (p.1 + 1) : ℕ) : NatOrdinal) := by
    refine (nsmul_le_nsmul_right hm₂ (p.2 + 1)).trans ?_
    have h1 : (p.2 + 1) • (NatOrdinal.of Ordinal.omega0 * ((((p.1 + 1)) : ℕ) : NatOrdinal)
        + ((((p.1 + 1)) : ℕ) : NatOrdinal))
        = NatOrdinal.of Ordinal.omega0 * ((((p.2 + 1) * (p.1 + 1) : ℕ)) : NatOrdinal)
          + ((((p.2 + 1) * (p.1 + 1) : ℕ)) : NatOrdinal) := by
      rw [nsmul_eq_mul]
      push_cast
      ring
    rw [h1]
  set M : ℕ := m₁ + (p.2 + 1) * (p.1 + 1) + 1 with hM
  refine omega_shape_le_omega_mul_omega M ?_
  have hcast : ((M : ℕ) : NatOrdinal)
      = ((m₁ : ℕ) : NatOrdinal) + (((p.2 + 1) * (p.1 + 1) : ℕ) : NatOrdinal)
        + ((1 : ℕ) : NatOrdinal) := by
    rw [hM]
    push_cast
    ring
  have hone : ((1 : ℕ) : NatOrdinal) = 1 := by exact_mod_cast rfl
  calc (partialSum (fun k ↦ (eps0 : Surreal.{0}) ^ k) p.1).birthday
        + (p.2 + 1) • ((eps0 : Surreal.{0}) ^ p.1).birthday + 1
      ≤ (NatOrdinal.of Ordinal.omega0 * ↑m₁ + ↑m₁)
        + (NatOrdinal.of Ordinal.omega0 * (((p.2 + 1) * (p.1 + 1) : ℕ) : NatOrdinal)
          + (((p.2 + 1) * (p.1 + 1) : ℕ) : NatOrdinal)) + 1 := by
        exact add_le_add (add_le_add hm₁ hsmul) le_rfl
    _ = NatOrdinal.of Ordinal.omega0 * (((m₁ : ℕ) : NatOrdinal)
          + (((p.2 + 1) * (p.1 + 1) : ℕ) : NatOrdinal))
        + (((m₁ : ℕ) : NatOrdinal) + ((((p.2 + 1) * (p.1 + 1) : ℕ)) : NatOrdinal) + 1) := by
        ring
    _ ≤ NatOrdinal.of Ordinal.omega0 * ((M : ℕ) : NatOrdinal) + ((M : ℕ) : NatOrdinal) := by
        rw [hcast, hone]
        refine add_le_add (mul_le_mul_of_nonneg_left NatOrdinal.le_add_right bot_le)
          (le_of_eq ?_)
        ring

end Surreal

end
