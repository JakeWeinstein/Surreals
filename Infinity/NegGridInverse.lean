import Infinity.AltInverse
import Infinity.NegGrid

/-!
# `(1 + a·ω⁻¹)⁻¹` is born by day `ω²`, for every positive dyadic `a`

The negative-grid census (`Infinity.NegGrid`) placed `v_a := (1 + a·ω⁻¹)⁻¹` at
birthday `≥ ω²` for every nonzero dyadic `a`; this file supplies the matching upper
bound for positive `a`, generalizing `Infinity.AltInverse` from the anchor `a = 1`
to the whole positive dyadic family.

The game inverted is `X_a := !{ {1} ∪ (1 + a·ω^(−1))ᴸ | (1 + a·ω^(−1))ᴿ }`: the
product game `1 + a·ω^(−1)` (whose value is `1 + a·ω⁻¹` by `mk_mul`) with the game
`1` adjoined as an extra left option — the *gift horse*, which leaves the value
unchanged (`equiv_of_forall_lf`) but guarantees a left move of value exactly `1`
even when `a > 1` (the product game's own value-near-`1` left options are
`1 + lower(a)·ω⁻¹` with `lower(a)` possibly nonzero). Every move of `X_a` has value
`d + e·ω⁻¹` with `d, e` dyadic, so the Conway-inverse word-class invariant holds in
a uniform three-case form (`d = 1` refines the class by one `ω`-power, `d = 0`
coarsens by one, other `d` keep it), and the value-`1` word-chain generates exactly
the partial sums of `Σ (−a·ω⁻¹)ᵏ` via `1 − (a·ω⁻¹)·Sₙ = Sₙ₊₁`
(`NegGrid.one_add_mul_monoS_neg`), which straddle `v_a` (evens below, odds above,
by the exact residual `sub_monoS_neg`). Mutual cofinality with the two-sided cut
`!{S_even | S_odd}` and the pricing `birthday_monoS_add_one_le` close the bound.

* `birthday_inv_one_add_dyadic_le` — **`birthday ((1 + a·ω⁻¹)⁻¹) ≤ ω·ω`** for every
  positive dyadic `a`.

With `NegGrid.omega_sq_le_birthday_inv_one_add_dyadic` this pins
`birthday ((1 + a·ω⁻¹)⁻¹) = ω²` exactly for every positive dyadic `a`.
-/

open ArchimedeanClass IGame Set

noncomputable section

namespace Surreal

local notation "Ω" => NatOrdinal.of Ordinal.omega0
local notation "ε₀" => eps0

/-! ### The moves and value of `ω^(−1)` (copied from `Infinity.AltInverse`) -/

private theorem mk_neg_one₀ : Surreal.mk (-1 : IGame.{0}) = -1 := by
  show Surreal.mk (-(1 : IGame.{0})) = -1
  rw [Surreal.mk_neg, Surreal.mk_one]

private theorem mk_wpow_neg_one₀ : Surreal.mk (ω^ (-1 : IGame.{0})) = ε₀ := by
  rw [Surreal.mk_wpow, mk_neg_one₀,
    show (-1 : Surreal.{0}) = -(1 : Surreal) from rfl, wpow_neg, eps0_def]

private theorem neg_one_leftMoves₀ : (-1 : IGame.{0})ᴸ = ∅ := by
  rw [show (-1 : IGame.{0}) = -(1 : IGame) from rfl]
  simp

private theorem neg_one_rightMoves₀ : (-1 : IGame.{0})ᴿ = {0} := by
  rw [show (-1 : IGame.{0}) = -(1 : IGame) from rfl]
  simp

private theorem leftMoves_wpow_neg_one₀ : (ω^ (-1 : IGame.{0}))ᴸ = {0} := by
  rw [leftMoves_wpow, neg_one_leftMoves₀]
  simp

private theorem rightMoves_wpow_neg_one₀ : (ω^ (-1 : IGame.{0}))ᴿ =
    (fun r : Dyadic ↦ (r : IGame) * ω^ (0 : IGame)) '' Set.Ioi 0 := by
  rw [rightMoves_wpow, neg_one_rightMoves₀, Set.image2_singleton_right]

private theorem mk_dyadic_mul_wpow_zero₀ (q : Dyadic) :
    Surreal.mk ((q : IGame.{0}) * ω^ (0 : IGame)) = (q : Surreal) := by
  rw [Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow, Surreal.mk_zero, wpow_zero, mul_one]

/-! ### Class toolkit (copied from `Infinity.AltInverse`) -/

/-- Coarser class dominates: positives of strictly coarser class are strictly larger. -/
private theorem lt_of_mk_lt_mk' {a b : Surreal.{0}} (hb : 0 < b)
    (hmk : ArchimedeanClass.mk b < ArchimedeanClass.mk a) : a < b := by
  have h := (ArchimedeanClass.mk_lt_mk).1 hmk 1
  rw [one_smul] at h
  calc a ≤ |a| := le_abs_self a
    _ < |b| := h
    _ = b := abs_of_pos hb

private theorem mk_wpow_int_anti {k l : ℤ} (h : k < l) :
    ArchimedeanClass.mk (ω^ ((l : ℤ) : Surreal.{0}))
      < ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0})) := by
  refine archimedeanClassMk_wpow_strictAnti ?_
  exact_mod_cast h

private theorem mk_eps0_pow_int (n : ℕ) :
    ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ (n + 1))
      = ArchimedeanClass.mk (ω^ (((-(n + 1) : ℤ) : ℤ) : Surreal.{0})) := by
  have hval : (ε₀ : Surreal.{0}) ^ (n + 1) = ω^ (-(((n + 1) : ℕ) : Surreal.{0})) := by
    rw [eps0_def, wpow_neg, wpow_natCast, inv_pow]
  rw [hval]
  have h1 : (-(((n + 1) : ℕ) : Surreal.{0})) = (((-(n + 1) : ℤ) : ℤ) : Surreal.{0}) := by
    push_cast
    ring
  rw [h1]

private theorem mk_eps0_pow_all (n : ℕ) :
    ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ n)
      = ArchimedeanClass.mk (ω^ (((-(n : ℤ) : ℤ)) : Surreal.{0})) := by
  cases n with
  | zero =>
    rw [pow_zero]
    have h : (((-((0 : ℕ) : ℤ) : ℤ)) : Surreal.{0}) = 0 := by push_cast; ring
    rw [h, wpow_zero]
  | succ n =>
    have h := mk_eps0_pow_int n
    have hc : (((-(n + 1) : ℤ) : ℤ) : Surreal.{0})
        = (((-((n + 1 : ℕ) : ℤ) : ℤ)) : Surreal.{0}) := by
      push_cast
      ring
    rwa [hc] at h

private theorem mk_wpow_int_add (k l : ℤ) :
    ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0}))
        + ArchimedeanClass.mk (ω^ ((l : ℤ) : Surreal.{0}))
      = ArchimedeanClass.mk (ω^ (((k + l : ℤ) : ℤ) : Surreal.{0})) := by
  rw [← ArchimedeanClass.mk_mul, ← wpow_add]
  congr 2
  push_cast
  ring

private theorem mk_wpow_one_int : ArchimedeanClass.mk (ω^ (1 : Surreal.{0}))
    = ArchimedeanClass.mk (ω^ (((1 : ℤ) : ℤ) : Surreal.{0})) := by
  congr 2
  push_cast
  ring

private theorem mk_wpow_one_inv_int : ArchimedeanClass.mk ((ω^ (1 : Surreal.{0}))⁻¹)
    = ArchimedeanClass.mk (ω^ (((-1 : ℤ) : ℤ) : Surreal.{0})) := by
  rw [show (((-1 : ℤ) : ℤ) : Surreal.{0}) = -(1 : Surreal) from by push_cast; ring, wpow_neg]

/-- `d + e·ω⁻¹` has class `0` whenever the dyadic `d` is nonzero. -/
private theorem mk_dyadic_pair {d : Dyadic} (hd : d ≠ 0) (e : Dyadic) :
    ArchimedeanClass.mk ((d : Surreal.{0}) + (e : Surreal) * ε₀) = 0 := by
  rcases eq_or_ne e 0 with rfl | he
  · rw [dyadic_cast_zero, zero_mul, add_zero]
    exact mk_dyadic_cast_ne_zero hd
  · have h : ArchimedeanClass.mk ((d : Surreal.{0}))
        < ArchimedeanClass.mk ((e : Surreal) * ε₀) := by
      rw [mk_dyadic_cast_ne_zero hd]
      exact dyadic_mul_eps0_infinitesimal' e
    rw [ArchimedeanClass.mk_add_eq_mk_left h, mk_dyadic_cast_ne_zero hd]

/-- `(a·ω⁻¹)ʲ` has the class of `ω⁻ʲ` for nonzero dyadic `a`. -/
private theorem mk_aeps_pow {a : Dyadic} (ha : a ≠ 0) (j : ℕ) :
    ArchimedeanClass.mk (((a : Surreal.{0}) * ε₀) ^ j)
      = ArchimedeanClass.mk ((ε₀ : Surreal.{0}) ^ j) := by
  rw [mul_pow, ArchimedeanClass.mk_mul,
    show ((a : Surreal.{0}) ^ j) = (((a ^ j : Dyadic)) : Surreal) from by
      induction j with
      | zero => rw [pow_zero, pow_zero, dyadic_cast_one]
      | succ m ih => rw [pow_succ, pow_succ, dyadic_cast_mul', ih],
    mk_dyadic_cast_ne_zero (pow_ne_zero _ ha), zero_add]

/-! ### The anchor games: the product `1 + a·ω^(−1)` and its gift-horse extension -/

/-- The product game `1 + a·ω^(−1)`, of value `1 + a·ω⁻¹`. -/
private def Xprod (a : Dyadic) : IGame.{0} := 1 + (a : IGame) * ω^ (-1 : IGame)

instance (a : Dyadic) : IGame.Numeric (Xprod a) := by
  unfold Xprod
  infer_instance

private theorem mk_Xprod (a : Dyadic) :
    Surreal.mk (Xprod a) = (1 : Surreal.{0}) + (a : Surreal) * ε₀ := by
  show Surreal.mk ((1 : IGame.{0}) + (a : IGame) * ω^ (-1 : IGame)) = _
  rw [Surreal.mk_add, Surreal.mk_one, Surreal.mk_mul, Surreal.mk_dyadic, mk_wpow_neg_one₀]

/-- **The anchor game `X_a`**: the product game with the gift-horse left option `1`
adjoined, so that the value-`1` chain move exists for every positive dyadic `a`. -/
private def Xg (a : Dyadic) : IGame.{0} :=
  !{insert 1 ((Xprod a)ᴸ) | (Xprod a)ᴿ}

private theorem Xg_moves_left (a : Dyadic) :
    (Xg a).moves Player.left = insert 1 ((Xprod a)ᴸ) := by
  rw [show Xg a = !{insert 1 ((Xprod a)ᴸ) | (Xprod a)ᴿ} from rfl]
  exact leftMoves_ofSets ..

private theorem Xg_moves_right (a : Dyadic) :
    (Xg a).moves Player.right = (Xprod a)ᴿ := by
  rw [show Xg a = !{insert 1 ((Xprod a)ᴸ) | (Xprod a)ᴿ} from rfl]
  exact rightMoves_ofSets ..

private theorem one_lt_Xprod {a : Dyadic} (ha : 0 < a) : (1 : IGame.{0}) < Xprod a := by
  rw [← @Surreal.mk_lt_mk 1 (Xprod a) _ _, Surreal.mk_one, mk_Xprod]
  have h := mul_pos (dyadic_cast_pos ha) eps0_pos
  linarith

private theorem Xg_numeric {a : Dyadic} (ha : 0 < a) : IGame.Numeric (Xg a) := by
  refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
  · rw [show (Xg a)ᴸ = (Xg a).moves Player.left from rfl, Xg_moves_left] at hy
    rw [show (Xg a)ᴿ = (Xg a).moves Player.right from rfl, Xg_moves_right] at hz
    rcases Set.mem_insert_iff.1 hy with rfl | hy'
    · exact (one_lt_Xprod ha).trans (IGame.Numeric.lt_right hz)
    · exact IGame.Numeric.left_lt_right hy' hz
  · cases p with
    | left =>
      rw [Xg_moves_left] at hy
      rcases Set.mem_insert_iff.1 hy with rfl | hy'
      · infer_instance
      · exact IGame.Numeric.of_mem_moves hy'
    | right =>
      rw [Xg_moves_right] at hy
      exact IGame.Numeric.of_mem_moves hy

/-- The gift-horse principle: adjoining the left option `1 < X` leaves the game
equivalent to the product game. -/
private theorem Xg_equiv {a : Dyadic} (ha : 0 < a) : Xg a ≈ Xprod a := by
  refine equiv_of_forall_lf ?_ ?_ ?_ ?_
  · intro z hz
    rw [show (Xg a)ᴸ = (Xg a).moves Player.left from rfl, Xg_moves_left] at hz
    rcases Set.mem_insert_iff.1 hz with rfl | hz'
    · exact (one_lt_Xprod ha).not_ge
    · exact left_lf hz'
  · intro z hz
    rw [show (Xg a)ᴿ = (Xg a).moves Player.right from rfl, Xg_moves_right] at hz
    exact lf_right hz
  · intro z hz
    refine left_lf ?_
    rw [show (Xg a)ᴸ = (Xg a).moves Player.left from rfl, Xg_moves_left]
    exact Set.mem_insert_of_mem _ hz
  · intro z hz
    refine lf_right ?_
    rw [show (Xg a)ᴿ = (Xg a).moves Player.right from rfl, Xg_moves_right]
    exact hz

private theorem mk_Xg {a : Dyadic} (ha : 0 < a) [IGame.Numeric (Xg a)] :
    Surreal.mk (Xg a) = (1 : Surreal.{0}) + (a : Surreal) * ε₀ := by
  rw [← mk_Xprod a]
  exact Surreal.mk_eq (Xg_equiv ha)

private theorem Xg_pos {a : Dyadic} (ha : 0 < a) [IGame.Numeric (Xg a)] :
    (0 : IGame.{0}) < Xg a := by
  rw [← @Surreal.mk_lt_mk 0 (Xg a) _ _, Surreal.mk_zero, mk_Xg ha]
  exact one_add_dyadic_mul_eps0_pos a

private theorem mk_inv_Xg {a : Dyadic} (ha : 0 < a) [IGame.Numeric (Xg a)] :
    Surreal.mk ((Xg a)⁻¹) = ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ := by
  rw [Surreal.mk_inv, mk_Xg ha]

/-! ### The moves of `X_a`: every move has value `d + e·ω⁻¹` with `d`, `e` dyadic -/

private theorem mk_mulOption_zero₀ (a s : Dyadic) :
    Surreal.mk (mulOption (a : IGame.{0}) (ω^ (-1 : IGame)) (s : IGame) 0)
      = (s : Surreal) * ε₀ := by
  show Surreal.mk ((s : IGame.{0}) * ω^ (-1 : IGame) + (a : IGame) * 0
      - (s : IGame) * 0) = _
  rw [Surreal.mk_sub, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_mul, Surreal.mk_mul,
    Surreal.mk_dyadic, Surreal.mk_dyadic, Surreal.mk_zero, mk_wpow_neg_one₀]
  ring

private theorem mk_mulOption_q₀ (a s r : Dyadic) :
    Surreal.mk (mulOption (a : IGame.{0}) (ω^ (-1 : IGame)) (s : IGame)
        ((r : IGame) * ω^ (0 : IGame)))
      = (((a - s) * r : Dyadic) : Surreal) + (s : Surreal) * ε₀ := by
  show Surreal.mk ((s : IGame.{0}) * ω^ (-1 : IGame)
      + (a : IGame) * ((r : IGame) * ω^ (0 : IGame))
      - (s : IGame) * ((r : IGame) * ω^ (0 : IGame))) = _
  simp only [Surreal.mk_sub, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_dyadic]
  rw [mk_wpow_neg_one₀,
    show Surreal.mk (ω^ (0 : IGame.{0})) = 1 from by
      rw [Surreal.mk_wpow, Surreal.mk_zero, wpow_zero],
    dyadic_cast_mul', dyadic_cast_sub']
  ring

/-- Every product move of `a·ω^(−1)` has value `d + e·ω⁻¹` with `d`, `e` dyadic. -/
private theorem Xprod_mulOption_value {a : Dyadic} (pb pc : Player) {b c : IGame.{0}}
    (hb : b ∈ ((a : IGame.{0})).moves pb) (hc : c ∈ (ω^ (-1 : IGame.{0})).moves pc)
    [IGame.Numeric (mulOption (a : IGame.{0}) (ω^ (-1 : IGame)) b c)] :
    ∃ d e : Dyadic, Surreal.mk (mulOption (a : IGame.{0}) (ω^ (-1 : IGame)) b c)
      = (d : Surreal) + (e : Surreal) * ε₀ := by
  have hbd : ∃ s : Dyadic, b = ((s : Dyadic) : IGame) := by
    cases pb with
    | left => exact ⟨_, Dyadic.eq_lower_of_mem_leftMoves_toIGame hb⟩
    | right => exact ⟨_, Dyadic.eq_upper_of_mem_rightMoves_toIGame hb⟩
  obtain ⟨s, rfl⟩ := hbd
  cases pc with
  | left =>
    rw [show (ω^ (-1 : IGame.{0})).moves Player.left = (ω^ (-1 : IGame.{0}))ᴸ from rfl,
      leftMoves_wpow_neg_one₀, Set.mem_singleton_iff] at hc
    subst hc
    refine ⟨0, s, ?_⟩
    rw [mk_mulOption_zero₀, dyadic_cast_zero, zero_add]
  | right =>
    rw [show (ω^ (-1 : IGame.{0})).moves Player.right = (ω^ (-1 : IGame.{0}))ᴿ from rfl,
      rightMoves_wpow_neg_one₀] at hc
    obtain ⟨r, hr, rfl⟩ := hc
    exact ⟨(a - s) * r, s, mk_mulOption_q₀ a s r⟩

/-- Every move of the product game `1 + a·ω^(−1)` has value `d + e·ω⁻¹` with `d`, `e`
dyadic. -/
private theorem Xprod_move_value {a : Dyadic} (p : Player) (y : IGame.{0})
    (hy : y ∈ (Xprod a).moves p) [IGame.Numeric y] :
    ∃ d e : Dyadic, Surreal.mk y = (d : Surreal) + (e : Surreal) * ε₀ := by
  have hy' : y ∈ ((1 : IGame.{0}) + (a : IGame) * ω^ (-1 : IGame)).moves p := hy
  rw [moves_add] at hy'
  rcases hy' with ⟨i, hi, rfl⟩ | ⟨z, hz, rfl⟩
  · -- a move of the `1` side, plus `a·ω^(−1)`
    cases p with
    | left =>
      rw [show (1 : IGame.{0}).moves Player.left = (1 : IGame.{0})ᴸ from rfl,
        show (1 : IGame.{0})ᴸ = {0} from by simp, Set.mem_singleton_iff] at hi
      subst hi
      refine ⟨0, a, ?_⟩
      rw [show Surreal.mk ((0 : IGame.{0}) + (a : IGame) * ω^ (-1 : IGame))
          = Surreal.mk (0 : IGame.{0}) + Surreal.mk ((a : IGame.{0}) * ω^ (-1 : IGame))
          from Surreal.mk_add .., Surreal.mk_zero, Surreal.mk_mul, Surreal.mk_dyadic,
        mk_wpow_neg_one₀, dyadic_cast_zero, zero_add]
    | right =>
      rw [show (1 : IGame.{0}).moves Player.right = (1 : IGame.{0})ᴿ from rfl,
        show (1 : IGame.{0})ᴿ = ∅ from by simp] at hi
      exact absurd hi (Set.notMem_empty i)
  · -- the `1`, plus a product move
    rw [moves_mul] at hz
    obtain ⟨⟨b, c⟩, hbc, rfl⟩ := hz
    haveI : IGame.Numeric (mulOption (a : IGame.{0}) (ω^ (-1 : IGame)) b c) := by
      rcases hbc with ⟨hb, hc⟩ | ⟨hb, hc⟩
      · exact IGame.Numeric.of_mem_moves (mulOption_mem_moves_mul hb hc)
      · exact IGame.Numeric.of_mem_moves (mulOption_mem_moves_mul hb hc)
    have hval : ∃ d e : Dyadic,
        Surreal.mk (mulOption (a : IGame.{0}) (ω^ (-1 : IGame)) b c)
          = (d : Surreal) + (e : Surreal) * ε₀ := by
      rcases hbc with ⟨hb, hc⟩ | ⟨hb, hc⟩
      · exact Xprod_mulOption_value Player.left p hb hc
      · exact Xprod_mulOption_value Player.right (-p) hb hc
    obtain ⟨d, e, hde⟩ := hval
    refine ⟨1 + d, e, ?_⟩
    rw [show Surreal.mk
        ((1 : IGame.{0}) + mulOption (a : IGame.{0}) (ω^ (-1 : IGame)) b c)
        = Surreal.mk (1 : IGame.{0})
          + Surreal.mk (mulOption (a : IGame.{0}) (ω^ (-1 : IGame)) b c)
        from Surreal.mk_add .., Surreal.mk_one, hde, dyadic_cast_add', dyadic_cast_one]
    ring

/-- Every move of `X_a` has value `d + e·ω⁻¹` with `d`, `e` dyadic. -/
private theorem Xg_move_value {a : Dyadic} [IGame.Numeric (Xg a)]
    (p : Player) (y : IGame.{0}) (hy : y ∈ (Xg a).moves p) :
    ∃ d e : Dyadic,
      @Surreal.mk y (IGame.Numeric.of_mem_moves hy)
        = (d : Surreal) + (e : Surreal) * ε₀ := by
  haveI := IGame.Numeric.of_mem_moves hy
  have hy' := hy
  cases p with
  | left =>
    rw [Xg_moves_left] at hy'
    rcases Set.mem_insert_iff.1 hy' with rfl | hy''
    · refine ⟨1, 0, ?_⟩
      rw [Surreal.mk_one, dyadic_cast_one, dyadic_cast_zero, zero_mul, add_zero]
    · exact Xprod_move_value Player.left y hy''
  | right =>
    rw [Xg_moves_right] at hy'
    exact Xprod_move_value Player.right y hy'

/-! ### The word-class invariant -/

/-- **Every option of `X_a⁻¹` sits at distance exactly `ω^k` from `(1 + a·ω⁻¹)⁻¹`**
for some integer `k`: the Conway-inverse words never enter the micro-halo. Moves of
value `e·ω⁻¹` coarsen the class by one `ω`-power, moves of value `1 + e·ω⁻¹` refine
it by one, and moves with a dyadic part `d ∉ {0, 1}` keep it. -/
private theorem inv_move_class {a : Dyadic} (ha : 0 < a) [IGame.Numeric (Xg a)] :
    ∀ (p : Player) (y : IGame.{0}) (hy : y ∈ ((Xg a)⁻¹).moves p),
      ∃ k : ℤ, ArchimedeanClass.mk
          (@Surreal.mk y (IGame.Numeric.of_mem_moves hy)
            - ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹)
        = ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0})) := by
  refine invRec (Xg_pos ha) ?_ ?_
  · -- the zero option: distance `v_a`, class `ω^0`
    refine ⟨0, ?_⟩
    rw [show @Surreal.mk (0 : IGame.{0}) (IGame.Numeric.of_mem_moves
        (zero_mem_leftMoves_inv (Xg_pos ha))) = 0 from Surreal.mk_zero,
      zero_sub, ArchimedeanClass.mk_neg, mk_inv_one_add_dyadic_mul_eps0,
      show (((0 : ℤ) : ℤ) : Surreal.{0}) = 0 from by push_cast; ring, wpow_zero,
      ArchimedeanClass.mk_one]
  · -- the inductive step
    intro p₁ p₂ y hy0 hyx t ht IH
    obtain ⟨k, hk⟩ := IH
    haveI hyn : y.Numeric := IGame.Numeric.of_mem_moves hyx
    haveI htn : t.Numeric := IGame.Numeric.of_mem_moves ht
    have hyv0 : (0 : Surreal) < Surreal.mk y := by
      rw [← Surreal.mk_zero]
      exact Surreal.mk_lt_mk.2 hy0
    -- the value of the new word
    have hval : @Surreal.mk (invOption (Xg a) y t)
        (IGame.Numeric.of_mem_moves (invOption_mem_moves_inv (Xg_pos ha) hy0 hyx ht))
        = (1 + (Surreal.mk y - ((1 : Surreal) + (a : Surreal) * ε₀)) * Surreal.mk t)
          / Surreal.mk y := by
      show Surreal.mk ((1 + (y - Xg a) * t) / y) = _
      rw [Surreal.mk_div, Surreal.mk_add, Surreal.mk_one, Surreal.mk_mul, Surreal.mk_sub,
        mk_Xg ha]
    -- the exact error recursion
    have herr : (1 + (Surreal.mk y - ((1 : Surreal) + (a : Surreal) * ε₀)) * Surreal.mk t)
            / Surreal.mk y
          - ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹
        = (((1 : Surreal) + (a : Surreal) * ε₀) - Surreal.mk y)
            * (((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ - Surreal.mk t)
            / Surreal.mk y := by
      have hy' : Surreal.mk y ≠ 0 := hyv0.ne'
      have hx' : ((1 : Surreal.{0}) + (a : Surreal) * ε₀) ≠ 0 :=
        one_add_dyadic_mul_eps0_ne_zero a
      have hx'' : ((a : Surreal) * ε₀ + (1 : Surreal.{0})) ≠ 0 := by
        intro h0
        apply hx'
        linarith
      field_simp
      ring
    have hmk_va : ArchimedeanClass.mk
          (((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ - Surreal.mk t)
        = ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0})) := by
      rw [show ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ - Surreal.mk t
          = -(Surreal.mk t - ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹) from by ring,
        ArchimedeanClass.mk_neg]
      exact hk
    -- the move value never equals the anchor value
    have hyne : Surreal.mk y ≠ (1 : Surreal.{0}) + (a : Surreal) * ε₀ := by
      have hyx' := hyx
      rw [← mk_Xg ha]
      cases hpp : -(p₁ * p₂) with
      | left =>
        rw [hpp] at hyx'
        exact (Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt hyx')).ne
      | right =>
        rw [hpp] at hyx'
        exact (Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right hyx')).ne'
    obtain ⟨d, e, hqv⟩ := Xg_move_value _ y hyx
    rcases eq_or_ne d 1 with rfl | hd1
    · -- `d = 1`: the error refines by one `ω`-power
      have hea : (a - e : Dyadic) ≠ 0 := by
        intro h0
        have hae : a = e := sub_eq_zero.1 h0
        apply hyne
        rw [hqv, dyadic_cast_one, ← hae]
      refine ⟨k - 1, ?_⟩
      rw [hval, herr]
      have hxy : ((1 : Surreal.{0}) + (a : Surreal) * ε₀) - Surreal.mk y
          = (((a - e : Dyadic)) : Surreal) * ε₀ := by
        rw [hqv, dyadic_cast_one, dyadic_cast_sub']
        ring
      rw [div_eq_mul_inv, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
        ArchimedeanClass.mk_inv, hxy, mk_dyadic_mul_eps0 hea, hmk_va, hqv,
        mk_dyadic_pair one_ne_zero, neg_zero, add_zero]
      rw [show ArchimedeanClass.mk (ε₀ : Surreal.{0})
          = ArchimedeanClass.mk (ω^ (((-1 : ℤ) : ℤ) : Surreal.{0})) from by
            rw [eps0_def]; exact mk_wpow_one_inv_int,
        mk_wpow_int_add]
      congr 2
      push_cast
      ring
    rcases eq_or_ne d 0 with rfl | hd0
    · -- `d = 0`: the error coarsens by one `ω`-power
      rw [dyadic_cast_zero, zero_add] at hqv
      have he0 : e ≠ 0 := by
        intro h0
        rw [h0, dyadic_cast_zero, zero_mul] at hqv
        exact absurd hqv hyv0.ne'
      refine ⟨k + 1, ?_⟩
      rw [hval, herr]
      have hxy : ((1 : Surreal.{0}) + (a : Surreal) * ε₀) - Surreal.mk y
          = (((1 : Dyadic)) : Surreal) + (((a - e : Dyadic)) : Surreal) * ε₀ := by
        rw [hqv, dyadic_cast_one, dyadic_cast_sub']
        ring
      rw [div_eq_mul_inv, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
        ArchimedeanClass.mk_inv, hxy, mk_dyadic_pair one_ne_zero, zero_add, hmk_va,
        hqv, mk_dyadic_mul_eps0 he0]
      rw [show -ArchimedeanClass.mk (ε₀ : Surreal.{0})
          = ArchimedeanClass.mk ((ε₀ : Surreal.{0})⁻¹) from
          (ArchimedeanClass.mk_inv _).symm,
        show (ε₀ : Surreal.{0})⁻¹ = ω^ (1 : Surreal) from by rw [eps0_def, inv_inv],
        mk_wpow_one_int, mk_wpow_int_add]
    · -- `d ∉ {0, 1}`: the error class is unchanged
      have hd1' : (1 - d : Dyadic) ≠ 0 := sub_ne_zero.2 (Ne.symm hd1)
      refine ⟨k, ?_⟩
      rw [hval, herr]
      have hxy : ((1 : Surreal.{0}) + (a : Surreal) * ε₀) - Surreal.mk y
          = (((1 - d : Dyadic)) : Surreal) + (((a - e : Dyadic)) : Surreal) * ε₀ := by
        rw [hqv, dyadic_cast_sub', dyadic_cast_sub', dyadic_cast_one]
        ring
      rw [div_eq_mul_inv, ArchimedeanClass.mk_mul, ArchimedeanClass.mk_mul,
        ArchimedeanClass.mk_inv, hxy, mk_dyadic_pair hd1', hmk_va, hqv,
        mk_dyadic_pair hd0, neg_zero, add_zero, zero_add]

/-! ### The negative-grid partial-sum ladder and the chain words -/

/-- The step identity of the negative grid: `1 − (a·ω⁻¹)·Sₙ = Sₙ₊₁`. -/
private theorem neg_step (a : Dyadic) (n : ℕ) :
    (1 : Surreal.{0}) - (a : Surreal) * ε₀ * monoS (negCoeff a) n
      = monoS (negCoeff a) (n + 1) := by
  have h := one_add_mul_monoS_neg a n
  have hp : (-((a : Surreal.{0}) * ε₀)) ^ n = (-(a : Surreal)) ^ n * ε₀ ^ n := by
    rw [show -((a : Surreal.{0}) * ε₀) = (-(a : Surreal)) * ε₀ from by ring, mul_pow]
  rw [monoS_succ n, negCoeff_cast]
  linear_combination -h + hp

/-- Even partial sums sit exactly `(a·ω⁻¹)^(2n)·v_a` below `v_a`. -/
private theorem monoS_neg_even (a : Dyadic) (n : ℕ) :
    monoS (negCoeff a) (2 * n)
      = ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹
        - ((a : Surreal) * ε₀) ^ (2 * n) * (1 + (a : Surreal) * ε₀)⁻¹ := by
  have h := sub_monoS_neg a (2 * n)
  rw [Even.neg_pow (even_two_mul n)] at h
  linarith

/-- Odd partial sums sit exactly `(a·ω⁻¹)^(2n+1)·v_a` above `v_a`. -/
private theorem monoS_neg_odd (a : Dyadic) (n : ℕ) :
    monoS (negCoeff a) (2 * n + 1)
      = ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹
        + ((a : Surreal) * ε₀) ^ (2 * n + 1) * (1 + (a : Surreal) * ε₀)⁻¹ := by
  have h := sub_monoS_neg a (2 * n + 1)
  rw [Odd.neg_pow (odd_two_mul_add_one n), neg_mul] at h
  linarith

private theorem aeps_pos {a : Dyadic} (ha : 0 < a) :
    (0 : Surreal.{0}) < (a : Surreal) * ε₀ :=
  mul_pos (dyadic_cast_pos ha) eps0_pos

private theorem inv_va_pos (a : Dyadic) :
    (0 : Surreal.{0}) < ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ :=
  inv_pos.2 (one_add_dyadic_mul_eps0_pos a)

private theorem monoS_neg_even_lt {a : Dyadic} (ha : 0 < a) (n : ℕ) :
    monoS (negCoeff a) (2 * n) < ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ := by
  rw [monoS_neg_even]
  have h := mul_pos (pow_pos (aeps_pos ha) (2 * n)) (inv_va_pos a)
  linarith

private theorem lt_monoS_neg_odd {a : Dyadic} (ha : 0 < a) (n : ℕ) :
    ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ < monoS (negCoeff a) (2 * n + 1) := by
  rw [monoS_neg_odd]
  have h := mul_pos (pow_pos (aeps_pos ha) (2 * n + 1)) (inv_va_pos a)
  linarith

/-- The gift-horse value-`1` left move of `X_a`. -/
private theorem hy1_mem {a : Dyadic} : (1 : IGame.{0}) ∈ (Xg a).moves Player.left := by
  rw [Xg_moves_left]
  exact Set.mem_insert _ _

/-- One chain step: the value-`1` move sends a word of value `s` on one side to a word
of value `1 − (a·ω⁻¹)·s` on the other. -/
private theorem chain_step {a : Dyadic} (ha : 0 < a) [IGame.Numeric (Xg a)]
    (p₁ p₂ : Player) (hp : (1 : IGame.{0}) ∈ (Xg a).moves (-(p₁ * p₂)))
    (w : IGame.{0}) (hw : w ∈ ((Xg a)⁻¹).moves p₁) :
    ∃ w', ∃ hw' : w' ∈ ((Xg a)⁻¹).moves p₂,
      @Surreal.mk w' (IGame.Numeric.of_mem_moves hw')
        = 1 - (a : Surreal) * ε₀ * @Surreal.mk w (IGame.Numeric.of_mem_moves hw) := by
  haveI := IGame.Numeric.of_mem_moves hw
  refine ⟨invOption (Xg a) 1 w,
    invOption_mem_moves_inv (Xg_pos ha) IGame.zero_lt_one hp hw, ?_⟩
  have hval : @Surreal.mk (invOption (Xg a) 1 w)
      (IGame.Numeric.of_mem_moves
        (invOption_mem_moves_inv (Xg_pos ha) IGame.zero_lt_one hp hw))
      = (1 + ((1 : Surreal) - ((1 : Surreal) + (a : Surreal) * ε₀)) * Surreal.mk w)
        / 1 := by
    show Surreal.mk ((1 + ((1 : IGame.{0}) - Xg a) * w) / (1 : IGame.{0})) = _
    rw [Surreal.mk_div, Surreal.mk_add, Surreal.mk_one, Surreal.mk_mul, Surreal.mk_sub,
      mk_Xg ha, Surreal.mk_one]
  rw [hval, div_one]
  ring

/-- **The chain words**: every negative-grid partial sum is realized by a word of
`X_a⁻¹` — even-index sums as left options, odd-index sums as right options. -/
private theorem exists_chain_words {a : Dyadic} (ha : 0 < a) [IGame.Numeric (Xg a)]
    (m : ℕ) :
    (∃ w, ∃ hw : w ∈ ((Xg a)⁻¹).moves Player.left,
      @Surreal.mk w (IGame.Numeric.of_mem_moves hw) = monoS (negCoeff a) (2 * m)) ∧
    (∃ w, ∃ hw : w ∈ ((Xg a)⁻¹).moves Player.right,
      @Surreal.mk w (IGame.Numeric.of_mem_moves hw) = monoS (negCoeff a) (2 * m + 1)) := by
  induction m with
  | zero =>
    have hL : ∃ w, ∃ hw : w ∈ ((Xg a)⁻¹).moves Player.left,
        @Surreal.mk w (IGame.Numeric.of_mem_moves hw) = monoS (negCoeff a) (2 * 0) := by
      refine ⟨0, zero_mem_leftMoves_inv (Xg_pos ha), ?_⟩
      rw [show @Surreal.mk (0 : IGame.{0}) (IGame.Numeric.of_mem_moves
          (zero_mem_leftMoves_inv (Xg_pos ha))) = 0 from Surreal.mk_zero,
        show (2 * 0 : ℕ) = 0 from rfl, monoS_zero]
    refine ⟨hL, ?_⟩
    obtain ⟨w, hw, hwv⟩ := hL
    obtain ⟨w', hw', hwv'⟩ := chain_step ha Player.left Player.right hy1_mem w hw
    refine ⟨w', hw', ?_⟩
    rw [hwv', hwv, show (2 * 0 + 1 : ℕ) = (2 * 0) + 1 from rfl]
    exact neg_step a (2 * 0)
  | succ m ih =>
    obtain ⟨-, ⟨wR, hwR, hvR⟩⟩ := ih
    have hL : ∃ w, ∃ hw : w ∈ ((Xg a)⁻¹).moves Player.left,
        @Surreal.mk w (IGame.Numeric.of_mem_moves hw)
          = monoS (negCoeff a) (2 * (m + 1)) := by
      obtain ⟨w', hw', hwv'⟩ := chain_step ha Player.right Player.left hy1_mem wR hwR
      refine ⟨w', hw', ?_⟩
      rw [hwv', hvR, show (2 * (m + 1) : ℕ) = (2 * m + 1) + 1 from by ring]
      exact neg_step a (2 * m + 1)
    refine ⟨hL, ?_⟩
    obtain ⟨w, hw, hwv⟩ := hL
    obtain ⟨w', hw', hwv'⟩ := chain_step ha Player.left Player.right hy1_mem w hw
    refine ⟨w', hw', ?_⟩
    rw [hwv', hwv]
    exact neg_step a (2 * (m + 1))

/-! ### Pricing the cut options -/

/-- Every negative-grid partial sum is born strictly inside `ω·ω`. -/
private theorem birthday_negS_succ_le {a : Dyadic} (ha : a ≠ 0) (n : ℕ) :
    (monoS (negCoeff a) n).birthday + 1 ≤ Ω * Ω := by
  cases n with
  | zero =>
    rw [monoS_zero, birthday_zero, zero_add]
    refine omega_shape_le_omega_mul_omega 1 ?_
    rw [Nat.cast_one, mul_one]
    exact NatOrdinal.le_add_left
  | succ B =>
    refine (birthday_monoS_add_one_le (negCoeff_ne_zero ha) B).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    exact (NatOrdinal.natCast_lt_omega0 (B + 1)).le

/-! ### The cofinality and the `ω²` bound -/

/-- **`(1 + a·ω⁻¹)⁻¹` is born by day `ω·ω` for every positive dyadic `a`**: the
Conway inverse `X_a⁻¹` of the gift-horse anchor `X_a` (value `1 + a·ω⁻¹`) is
mutually cofinal with the two-sided cut on the negative-grid partial sums (evens on
the left, odds on the right) — the word-class invariant keeps every inverse option
outside the micro-halo, and the value-`1` word-chain supplies approximants at every
scale on both sides. Each partial sum costs `< ω·(n+1)`, so the cut is born by
`ω·ω`. -/
theorem birthday_inv_one_add_dyadic_le {a : Dyadic} (ha : 0 < a) :
    (((1 : Surreal.{0}) + (a : Surreal) * eps0)⁻¹).birthday
      ≤ NatOrdinal.of Ordinal.omega0 * NatOrdinal.of Ordinal.omega0 := by
  classical
  haveI := Xg_numeric ha
  -- realizations of the partial sums
  have hLg : ∀ m : ℕ, ∃ (g : IGame.{0}) (_ : g.Numeric),
      Surreal.mk g = monoS (negCoeff a) (2 * m) ∧ g.birthday + 1 ≤ Ω * Ω := by
    intro m
    obtain ⟨g, gn, gv, gb⟩ := birthday_eq_iGameBirthday (monoS (negCoeff a) (2 * m))
    refine ⟨g, gn, gv, ?_⟩
    rw [gb]
    exact birthday_negS_succ_le ha.ne' (2 * m)
  have hRg : ∀ m : ℕ, ∃ (g : IGame.{0}) (_ : g.Numeric),
      Surreal.mk g = monoS (negCoeff a) (2 * m + 1) ∧ g.birthday + 1 ≤ Ω * Ω := by
    intro m
    obtain ⟨g, gn, gv, gb⟩ := birthday_eq_iGameBirthday (monoS (negCoeff a) (2 * m + 1))
    refine ⟨g, gn, gv, ?_⟩
    rw [gb]
    exact birthday_negS_succ_le ha.ne' (2 * m + 1)
  choose gL hgLn hgLv hgLb using hLg
  choose gR hgRn hgRv hgRb using hRg
  haveI : ∀ n, (gL n).Numeric := hgLn
  haveI : ∀ n, (gR n).Numeric := hgRn
  set C : IGame.{0} := !{Set.range gL | Set.range gR} with hC
  have hCL : Cᴸ = Set.range gL := leftMoves_ofSets ..
  have hCR : Cᴿ = Set.range gR := rightMoves_ofSets ..
  -- the mutual cofinality
  have hequiv : (Xg a)⁻¹ ≈ C := by
    apply equiv_of_exists_le
    · -- left moves of `X_a⁻¹` fit under even partial sums
      intro w hw
      haveI := IGame.Numeric.of_mem_moves hw
      obtain ⟨k, hk⟩ := inv_move_class ha Player.left w hw
      have hwlt : Surreal.mk w < ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ := by
        rw [← mk_inv_Xg ha]
        exact Surreal.mk_lt_mk.2 (IGame.Numeric.left_lt hw)
      have he_pos : (0 : Surreal.{0})
          < ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ - Surreal.mk w := by
        linarith
      have hmke : ArchimedeanClass.mk
            (((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ - Surreal.mk w)
          = ArchimedeanClass.mk (ω^ ((k : ℤ) : Surreal.{0})) := by
        rw [show ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ - Surreal.mk w
            = -(Surreal.mk w - ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹) from by ring,
          ArchimedeanClass.mk_neg]
        exact hk
      refine ⟨gL ((-k).toNat + 1), by rw [hCL]; exact Set.mem_range_self _, ?_⟩
      rw [← Surreal.mk_le_mk, hgLv, monoS_neg_even]
      have hlt : ((a : Surreal) * ε₀) ^ (2 * ((-k).toNat + 1))
            * ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹
          < ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ - Surreal.mk w := by
        refine lt_of_mk_lt_mk' he_pos ?_
        rw [hmke, ArchimedeanClass.mk_mul, mk_aeps_pow ha.ne',
          mk_inv_one_add_dyadic_mul_eps0, add_zero, mk_eps0_pow_all]
        exact mk_wpow_int_anti (by omega)
      linarith
    · -- right moves of `X_a⁻¹` dominate odd partial sums
      intro w hw
      haveI := IGame.Numeric.of_mem_moves hw
      obtain ⟨k, hk⟩ := inv_move_class ha Player.right w hw
      have hwgt : ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ < Surreal.mk w := by
        rw [← mk_inv_Xg ha]
        exact Surreal.mk_lt_mk.2 (IGame.Numeric.lt_right hw)
      have he_pos : (0 : Surreal.{0})
          < Surreal.mk w - ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ := by
        linarith
      refine ⟨gR ((-k).toNat), by rw [hCR]; exact Set.mem_range_self _, ?_⟩
      rw [← Surreal.mk_le_mk, hgRv, monoS_neg_odd]
      have hlt : ((a : Surreal) * ε₀) ^ (2 * (-k).toNat + 1)
            * ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹
          < Surreal.mk w - ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ := by
        refine lt_of_mk_lt_mk' he_pos ?_
        rw [hk, ArchimedeanClass.mk_mul, mk_aeps_pow ha.ne',
          mk_inv_one_add_dyadic_mul_eps0, add_zero, mk_eps0_pow_all]
        exact mk_wpow_int_anti (by omega)
      linarith
    · -- cut lefts are matched by even chain words, exactly
      rw [hCL]
      rintro b ⟨m, rfl⟩
      obtain ⟨⟨w, hw, hwv⟩, -⟩ := exists_chain_words ha m
      refine ⟨w, hw, ?_⟩
      haveI := IGame.Numeric.of_mem_moves hw
      rw [← Surreal.mk_le_mk, hgLv, hwv]
    · -- cut rights are matched by odd chain words, exactly
      rw [hCR]
      rintro b ⟨m, rfl⟩
      obtain ⟨-, ⟨w, hw, hwv⟩⟩ := exists_chain_words ha m
      refine ⟨w, hw, ?_⟩
      haveI := IGame.Numeric.of_mem_moves hw
      rw [← Surreal.mk_le_mk, hgRv, hwv]
  -- the cut is numeric
  have hCn : IGame.Numeric C := by
    refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
    · rw [hC, leftMoves_ofSets] at hy
      rw [hC, rightMoves_ofSets] at hz
      obtain ⟨n, rfl⟩ := hy
      obtain ⟨m, rfl⟩ := hz
      rw [← Surreal.mk_lt_mk, hgLv, hgRv]
      exact (monoS_neg_even_lt ha n).trans (lt_monoS_neg_odd ha m)
    · cases p with
      | left =>
        rw [hC, moves_ofSets] at hy
        obtain ⟨n, rfl⟩ := hy
        exact hgLn n
      | right =>
        rw [hC, moves_ofSets] at hy
        obtain ⟨n, rfl⟩ := hy
        exact hgRn n
  -- value and birthday
  have hval : ((1 : Surreal.{0}) + (a : Surreal) * ε₀)⁻¹ = @Surreal.mk C hCn := by
    rw [← mk_inv_Xg ha]
    exact Surreal.mk_eq hequiv
  refine le_of_eq_of_le (congrArg birthday hval) ?_
  refine (birthday_mk_le _).trans ?_
  rw [hC, IGame.birthday_ofSets]
  refine max_le ?_ ?_
  · refine csSup_le' ?_
    rintro o ⟨g, ⟨n, rfl⟩, rfl⟩
    rw [Function.comp_apply, Order.succ_eq_add_one]
    exact hgLb n
  · refine csSup_le' ?_
    rintro o ⟨g, ⟨n, rfl⟩, rfl⟩
    rw [Function.comp_apply, Order.succ_eq_add_one]
    exact hgRb n

end Surreal

end
