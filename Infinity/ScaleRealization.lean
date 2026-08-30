import Infinity.GeometricUpper

/-!
# The scale-parametric halo grid: realizing `x + r·W` over separated anchors

`Infinity.HaloRealization` realized the dyadic `ω⁻¹`-grid over rational-separated anchors
by order-pinning (mutual cofinality, no simplicity). This file makes that engine
**parametric in the scale**: for a scale pair `(W, V)` of games — `W` the fine scale with
left moves `{0}` and right moves the positive dyadic multiples of the coarse scale `V` —
and an anchor `x` whose options are separated from its value by dyadic multiples of
`mk V`, the Conway sum `x + r·W` is pinned by two-sided cuts walking the dyadic birth
tree, each step costing one day over a base ordinal.

* `LeftSepV`/`RightSepV` — anchor separation at scale `v = mk V`, with negation
  transport (`RightSepV.neg`, `LeftSepV.neg`).
* `add_dyadic_mul_scale_equiv_of_den_ne_one` / `add_natCast_succ_mul_scale_equiv` — the
  core cofinality computations, generalized from `Infinity.HaloRealization` by replacing
  `(ω⁰, ω⁻¹)` with `(V, W)`; the scale hypothesis is the single inequality
  `s·w < q·v` (every dyadic multiple of the fine scale is below every positive dyadic
  multiple of the coarse scale).
* `scale_grid_aux` — the parametric grid bound: given realizations of the coarse
  translates `mk x + q·v` below `base + c₀`, each grid point `mk x + r·w` is born by
  `base + (hgt r − 1 + c₀)`.

`Infinity.TubeCensus` instantiates this at `(V, W) = (ω^{-(B-1)}, ω^{-B})` with the
geometric partial sums as anchors, producing the birthday bounds
`birthday (S_B + t·ω^{-B}) ≤ ω·B + (hgt t − 1)` that price the tube census.
-/

open ArchimedeanClass IGame Set

noncomputable section

namespace Surreal

/-! ### Separation of an anchor at a coarse scale -/

/-- Left separation of an anchor game at the scale `v`: every left option sits below the
anchor's value by at least a positive dyadic multiple of `v`. -/
def LeftSepV (x : IGame.{0}) [IGame.Numeric x] (v : Surreal.{0}) : Prop :=
  ∀ i (hi : i ∈ xᴸ), ∃ q : Dyadic, 0 < q ∧
    @Surreal.mk i (IGame.Numeric.of_mem_moves hi) + (q : Surreal) * v ≤ Surreal.mk x

/-- Right separation of an anchor game at the scale `v`. -/
def RightSepV (x : IGame.{0}) [IGame.Numeric x] (v : Surreal.{0}) : Prop :=
  ∀ j (hj : j ∈ xᴿ), ∃ q : Dyadic, 0 < q ∧
    Surreal.mk x + (q : Surreal) * v ≤ @Surreal.mk j (IGame.Numeric.of_mem_moves hj)

/-- Negation transports right separation to left separation of the negated anchor. -/
theorem RightSepV.neg {x : IGame.{0}} [IGame.Numeric x] {v : Surreal.{0}}
    (h : RightSepV x v) : LeftSepV (-x) v := by
  intro i hi
  have hi2 := hi
  rw [show (-x)ᴸ = (-x).moves Player.left from rfl, moves_neg,
    show -Player.left = Player.right from rfl, Set.mem_neg] at hi2
  obtain ⟨q, hq, hle⟩ := h (-i) hi2
  refine ⟨q, hq, ?_⟩
  haveI : IGame.Numeric i := IGame.Numeric.of_mem_moves hi
  have hle' : Surreal.mk x + (q : Surreal) * v ≤ -(Surreal.mk i) := by
    rw [← Surreal.mk_neg]
    exact hle
  have hgoal : Surreal.mk i + (q : Surreal) * v ≤ -(Surreal.mk x) := by linarith
  rw [show Surreal.mk (-x) = -(Surreal.mk x) from Surreal.mk_neg x]
  exact hgoal

/-- Negation transports left separation to right separation of the negated anchor. -/
theorem LeftSepV.neg {x : IGame.{0}} [IGame.Numeric x] {v : Surreal.{0}}
    (h : LeftSepV x v) : RightSepV (-x) v := by
  intro j hj
  have hj2 := hj
  rw [show (-x)ᴿ = (-x).moves Player.right from rfl, moves_neg,
    show -Player.right = Player.left from rfl, Set.mem_neg] at hj2
  obtain ⟨q, hq, hle⟩ := h (-j) hj2
  refine ⟨q, hq, ?_⟩
  haveI : IGame.Numeric j := IGame.Numeric.of_mem_moves hj
  have hle' : -(Surreal.mk j) + (q : Surreal) * v ≤ Surreal.mk x := by
    rw [← Surreal.mk_neg]
    exact hle
  have hgoal : -(Surreal.mk x) + (q : Surreal) * v ≤ Surreal.mk j := by linarith
  rw [show Surreal.mk (-x) = -(Surreal.mk x) from Surreal.mk_neg x]
  exact hgoal

/-! ### The scale hypotheses -/

section Core

variable {W V : IGame.{0}} [IGame.Numeric W] [IGame.Numeric V] {w v : Surreal.{0}}

variable (hWL : Wᴸ = {0})
variable (hWR : Wᴿ = (fun q : Dyadic ↦ (q : IGame) * V) '' Set.Ioi 0)
variable (hWv : Surreal.mk W = w) (hVv : Surreal.mk V = v) (hw0 : 0 < w)
variable (hsep : ∀ (s : Dyadic) {q : Dyadic}, 0 < q →
  (s : Surreal) * w < (q : Surreal) * v)

include hsep in
/-- The fine scale is below every positive dyadic multiple of the coarse scale. -/
theorem scale_lt_dyadic_mul {q : Dyadic} (hq : 0 < q) : w < (q : Surreal) * v := by
  have h := hsep 1 hq
  rwa [dyadic_cast_one, one_mul] at h

include hsep in
/-- Negated positive dyadic multiples of the coarse scale sit below every dyadic
multiple of the fine scale. -/
theorem neg_dyadic_mul_scale_lt (s : Dyadic) {q : Dyadic} (hq : 0 < q) :
    -((q : Surreal) * v) < (s : Surreal) * w := by
  have h := hsep (-s) hq
  rw [dyadic_cast_neg', neg_mul] at h
  linarith

/-! ### Values of product moves against the scale pair -/

private theorem mk_mulOption_scale (y u a b : IGame.{0}) [IGame.Numeric y]
    [IGame.Numeric u] [IGame.Numeric a] [IGame.Numeric b] :
    Surreal.mk (mulOption y u a b)
      = Surreal.mk a * Surreal.mk u + Surreal.mk y * Surreal.mk b
        - Surreal.mk a * Surreal.mk b := by
  show Surreal.mk (a * u + y * b - a * b) = _
  rw [Surreal.mk_sub, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_mul, Surreal.mk_mul]

include hVv in
private theorem mk_dyadic_mul_V (q : Dyadic) :
    Surreal.mk ((q : IGame.{0}) * V) = (q : Surreal) * v := by
  rw [Surreal.mk_mul, Surreal.mk_dyadic, hVv]

variable {x : IGame.{0}} [IGame.Numeric x]

include hWv in
private theorem mk_add_mulOption_zero_scale (r s : Dyadic) :
    Surreal.mk (x + mulOption (r : IGame) W (s : IGame) 0)
      = Surreal.mk x + (s : Surreal) * w := by
  rw [Surreal.mk_add, mk_mulOption_scale, Surreal.mk_dyadic, Surreal.mk_dyadic,
    hWv, Surreal.mk_zero]
  ring

include hWv hVv in
private theorem mk_add_mulOption_q_scale (r s q : Dyadic) :
    Surreal.mk (x + mulOption (r : IGame) W (s : IGame) ((q : IGame) * V))
      = Surreal.mk x + (s : Surreal) * w
        + ((r : Surreal) - (s : Surreal)) * ((q : Surreal) * v) := by
  rw [Surreal.mk_add, mk_mulOption_scale, mk_dyadic_mul_V hVv, Surreal.mk_dyadic,
    Surreal.mk_dyadic, hWv]
  ring

/-! ### The core cofinality computation, non-integer case -/

include hWL hWR hWv hVv hsep in
/-- **The core cofinality computation** (non-integer case), scale-parametric: the Conway
sum `x + r·W` is mutually cofinal with the two-sided cut whose options realize the values
`mk x + lower(r)·w` and `mk x + upper(r)·w`. All comparisons happen at the level of
surreal values; no simplicity theory enters. -/
theorem add_dyadic_mul_scale_equiv_of_den_ne_one {r : Dyadic} (hden : r.den ≠ 1)
    {gL gU : IGame.{0}} [IGame.Numeric gL] [IGame.Numeric gU]
    (hgL : Surreal.mk gL = Surreal.mk x + (r.lower : Surreal) * w)
    (hgU : Surreal.mk gU = Surreal.mk x + (r.upper : Surreal) * w)
    (hxL : LeftSepV x v) (hxR : RightSepV x v) :
    x + (r : IGame) * W ≈ !{{gL} | {gU}} := by
  have hCL : (!{{gL} | {gU}} : IGame.{0})ᴸ = {gL} := leftMoves_ofSets ..
  have hCR : (!{{gL} | {gU}} : IGame.{0})ᴿ = {gU} := rightMoves_ofSets ..
  have hrl : (r : IGame.{0})ᴸ = {((r.lower : Dyadic) : IGame)} := by
    rw [Dyadic.toIGame_of_den_ne_one hden, leftMoves_ofSets]
  have hrr : (r : IGame.{0})ᴿ = {((r.upper : Dyadic) : IGame)} := by
    rw [Dyadic.toIGame_of_den_ne_one hden, rightMoves_ofSets]
  -- the key fine-versus-coarse comparisons
  have hlow : ∀ q : Dyadic, 0 < q →
      (r : Surreal) * w - (r.lower : Surreal) * w < (q : Surreal) * v := by
    intro q hq
    have h := hsep (r - r.lower) hq
    rwa [dyadic_cast_sub', sub_mul] at h
  have hupp : ∀ q : Dyadic, 0 < q →
      (r.upper : Surreal) * w - (r : Surreal) * w < (q : Surreal) * v := by
    intro q hq
    have h := hsep (r.upper - r) hq
    rwa [dyadic_cast_sub', sub_mul] at h
  have hgap : ∀ q : Dyadic, 0 < q →
      (r.upper : Surreal) * w - (r.lower : Surreal) * w
        < ((r : Surreal) - (r.lower : Surreal)) * ((q : Surreal) * v) := by
    intro q hq
    have hql : (0 : Dyadic) < q * (r - r.lower) := by
      have h1 : (0 : Dyadic) < r - r.lower := sub_pos.2 (Dyadic.lower_lt r)
      positivity
    have h2 := hsep (r.upper - r.lower) hql
    rw [dyadic_cast_sub', sub_mul, dyadic_cast_mul', dyadic_cast_sub'] at h2
    calc (r.upper : Surreal) * w - (r.lower : Surreal) * w
        < (q : Surreal) * ((r : Surreal) - (r.lower : Surreal)) * v := h2
      _ = ((r : Surreal) - (r.lower : Surreal)) * ((q : Surreal) * v) := by ring
  have hgapU : ∀ q : Dyadic, 0 < q →
      (r.upper : Surreal) * w - (r.lower : Surreal) * w
        < ((r.upper : Surreal) - (r : Surreal)) * ((q : Surreal) * v) := by
    intro q hq
    have hql : (0 : Dyadic) < q * (r.upper - r) := by
      have h1 : (0 : Dyadic) < r.upper - r := sub_pos.2 (Dyadic.lt_upper r)
      positivity
    have h2 := hsep (r.upper - r.lower) hql
    rw [dyadic_cast_sub', sub_mul, dyadic_cast_mul', dyadic_cast_sub'] at h2
    calc (r.upper : Surreal) * w - (r.lower : Surreal) * w
        < (q : Surreal) * ((r.upper : Surreal) - (r : Surreal)) * v := h2
      _ = ((r.upper : Surreal) - (r : Surreal)) * ((q : Surreal) * v) := by ring
  apply equiv_of_exists_le
  · -- every left move of the sum is ≤ the left option gL
    rw [forall_moves_add]
    constructor
    · intro i hi
      refine ⟨gL, by rw [hCL]; exact Set.mem_singleton _, ?_⟩
      haveI := IGame.Numeric.of_mem_moves hi
      obtain ⟨q, hq, hle⟩ := hxL i hi
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_dyadic, hWv, hgL]
      have h1 := hlow q hq
      linarith
    · rw [forall_moves_mul]
      intro p' a ha b hb
      cases p' with
      | left =>
        rw [hrl, Set.mem_singleton_iff] at ha
        subst ha
        rw [show Player.left * Player.left = Player.left from rfl] at hb
        rw [show W.moves Player.left = Wᴸ from rfl, hWL, Set.mem_singleton_iff] at hb
        subst hb
        refine ⟨gL, by rw [hCL]; exact Set.mem_singleton _, ?_⟩
        rw [← Surreal.mk_le_mk, mk_add_mulOption_zero_scale hWv, hgL]
      | right =>
        rw [hrr, Set.mem_singleton_iff] at ha
        subst ha
        rw [show Player.right * Player.left = Player.right from rfl] at hb
        rw [show W.moves Player.right = Wᴿ from rfl, hWR] at hb
        obtain ⟨q, hq, rfl⟩ := hb
        haveI : IGame.Numeric ((q : IGame.{0}) * V) := inferInstance
        refine ⟨gL, by rw [hCL]; exact Set.mem_singleton _, ?_⟩
        rw [← Surreal.mk_le_mk, mk_add_mulOption_q_scale hWv hVv, hgL]
        -- A + upper·w + (r − upper)·(q·v) ≤ A + lower·w
        have h2 := hgapU q hq
        have h3 : ((r : Surreal) - (r.upper : Surreal)) * ((q : Surreal) * v)
            = -(((r.upper : Surreal) - (r : Surreal)) * ((q : Surreal) * v)) := by ring
        linarith
  · -- every right move of the sum is ≥ the right option gU
    rw [forall_moves_add]
    constructor
    · intro j hj
      refine ⟨gU, by rw [hCR]; exact Set.mem_singleton _, ?_⟩
      haveI := IGame.Numeric.of_mem_moves hj
      obtain ⟨q, hq, hle⟩ := hxR j hj
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_dyadic, hWv, hgU]
      have h1 := hupp q hq
      linarith
    · rw [forall_moves_mul]
      intro p' a ha b hb
      cases p' with
      | left =>
        rw [hrl, Set.mem_singleton_iff] at ha
        subst ha
        rw [show Player.left * Player.right = Player.right from rfl] at hb
        rw [show W.moves Player.right = Wᴿ from rfl, hWR] at hb
        obtain ⟨q, hq, rfl⟩ := hb
        refine ⟨gU, by rw [hCR]; exact Set.mem_singleton _, ?_⟩
        rw [← Surreal.mk_le_mk, mk_add_mulOption_q_scale hWv hVv, hgU]
        -- A + upper·w ≤ A + lower·w + (r − lower)·(q·v)
        have h2 := hgap q hq
        linarith
      | right =>
        rw [hrr, Set.mem_singleton_iff] at ha
        subst ha
        rw [show Player.right * Player.right = Player.left from rfl] at hb
        rw [show W.moves Player.left = Wᴸ from rfl, hWL, Set.mem_singleton_iff] at hb
        subst hb
        refine ⟨gU, by rw [hCR]; exact Set.mem_singleton _, ?_⟩
        rw [← Surreal.mk_le_mk, mk_add_mulOption_zero_scale hWv, hgU]
  · -- the left option gL is ≤ some left move of the sum
    rw [hCL]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine ⟨x + mulOption (r : IGame) W ((r.lower : Dyadic) : IGame) 0,
      add_left_mem_moves_add (mulOption_mem_moves_mul (px := Player.left) (py := Player.left)
        (by rw [hrl]; exact Set.mem_singleton _)
        (by rw [show W.moves Player.left = Wᴸ from rfl, hWL]; exact Set.mem_singleton _)) _,
      ?_⟩
    rw [← Surreal.mk_le_mk, mk_add_mulOption_zero_scale hWv, hgL]
  · -- the right option gU is ≥ some right move of the sum
    rw [hCR]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine ⟨x + mulOption (r : IGame) W ((r.upper : Dyadic) : IGame) 0,
      add_left_mem_moves_add (mulOption_mem_moves_mul (px := Player.right) (py := Player.left)
        (by rw [hrr]; exact Set.mem_singleton _)
        (by rw [show W.moves Player.left = Wᴸ from rfl, hWL]; exact Set.mem_singleton _)) _,
      ?_⟩
    rw [← Surreal.mk_le_mk, mk_add_mulOption_zero_scale hWv, hgU]

/-! ### The core cofinality computation, positive-integer case -/

private theorem half_pos_sr : (0 : Dyadic) < Dyadic.half := by
  rw [← Dyadic.coe_lt_coe, Dyadic.coe_half]
  norm_num

private theorem half_add_half_sr (q : Dyadic) : q * Dyadic.half + q * Dyadic.half = q := by
  ext
  push_cast [Dyadic.coe_half]
  ring

include hWv in
private theorem mk_add_mulOption_nat_zero_scale (k : ℕ) :
    Surreal.mk (x + mulOption (((k + 1 : ℕ) : IGame)) W ((k : ℕ) : IGame) 0)
      = Surreal.mk x + (k : Surreal) * w := by
  rw [Surreal.mk_add, mk_mulOption_scale, Surreal.mk_natCast, Surreal.mk_natCast,
    hWv, Surreal.mk_zero]
  ring

include hWv hVv in
private theorem mk_add_mulOption_nat_q_scale (k : ℕ) (q : Dyadic) :
    Surreal.mk (x + mulOption (((k + 1 : ℕ) : IGame)) W ((k : ℕ) : IGame)
        ((q : IGame) * V))
      = Surreal.mk x + (k : Surreal) * w + (q : Surreal) * v := by
  rw [Surreal.mk_add, mk_mulOption_scale, mk_dyadic_mul_V hVv, Surreal.mk_natCast,
    Surreal.mk_natCast, hWv]
  have h : ((k + 1 : ℕ) : Surreal) = (k : Surreal) + 1 := by push_cast; ring
  rw [h]
  ring

include hWL hWR hWv hVv hw0 hsep in
/-- **The core cofinality computation** (positive-integer case), scale-parametric: the
Conway sum `x + (k+1)·W` is mutually cofinal with the cut whose left option realizes
`mk x + k·w` and whose right options realize the coarse translates `mk x + q·v`. -/
theorem add_natCast_succ_mul_scale_equiv (k : ℕ)
    {gL : IGame.{0}} [IGame.Numeric gL]
    (gR : Dyadic → IGame.{0})
    (hgRn : ∀ q : Dyadic, 0 < q → (gR q).Numeric)
    (hgL : Surreal.mk gL = Surreal.mk x + (k : Surreal) * w)
    (hgR : ∀ q (hq : 0 < q), @Surreal.mk (gR q) (hgRn q hq) = Surreal.mk x + (q : Surreal) * v)
    (hxL : LeftSepV x v) (hxR : RightSepV x v) :
    x + ((k + 1 : ℕ) : IGame) * W ≈ !{{gL} | gR '' Set.Ioi 0} := by
  have hCL : (!{{gL} | gR '' Set.Ioi 0} : IGame.{0})ᴸ = {gL} := leftMoves_ofSets ..
  have hCR : (!{{gL} | gR '' Set.Ioi 0} : IGame.{0})ᴿ = gR '' Set.Ioi 0 := rightMoves_ofSets ..
  have hnl : (((k + 1 : ℕ) : IGame.{0}))ᴸ = {((k : ℕ) : IGame)} := leftMoves_natCast_succ k
  have hnr : (((k + 1 : ℕ) : IGame.{0}))ᴿ = ∅ := rightMoves_natCast _
  have hknn : (0 : Surreal) ≤ (k : Surreal) * w := by
    have h1 : (0 : Surreal) ≤ (k : Surreal) := by exact_mod_cast Nat.zero_le k
    exact mul_nonneg h1 hw0.le
  have hkq : ∀ q : Dyadic, 0 < q →
      (k : Surreal) * w < (q : Surreal) * v := by
    intro q hq
    have h := hsep ((k : ℕ) : Dyadic) hq
    rwa [dyadic_cast_natCast] at h
  apply equiv_of_exists_le
  · rw [forall_moves_add]
    constructor
    · intro i hi
      refine ⟨gL, by rw [hCL]; exact Set.mem_singleton _, ?_⟩
      haveI := IGame.Numeric.of_mem_moves hi
      obtain ⟨q, hq, hle⟩ := hxL i hi
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_natCast, hWv, hgL]
      have h1 := scale_lt_dyadic_mul hsep hq
      have h2 : ((k + 1 : ℕ) : Surreal) = (k : Surreal) + 1 := by push_cast; ring
      rw [h2]
      nlinarith [hw0]
    · rw [forall_moves_mul]
      intro p' a ha b hb
      cases p' with
      | left =>
        rw [hnl, Set.mem_singleton_iff] at ha
        subst ha
        rw [show Player.left * Player.left = Player.left from rfl] at hb
        rw [show W.moves Player.left = Wᴸ from rfl, hWL, Set.mem_singleton_iff] at hb
        subst hb
        refine ⟨gL, by rw [hCL]; exact Set.mem_singleton _, ?_⟩
        rw [← Surreal.mk_le_mk, mk_add_mulOption_nat_zero_scale hWv, hgL]
      | right =>
        rw [hnr] at ha
        exact absurd ha (Set.notMem_empty a)
  · rw [forall_moves_add]
    constructor
    · intro j hj
      haveI := IGame.Numeric.of_mem_moves hj
      obtain ⟨q, hq, hle⟩ := hxR j hj
      haveI := hgRn q hq
      refine ⟨gR q, by rw [hCR]; exact Set.mem_image_of_mem _ hq, ?_⟩
      rw [← Surreal.mk_le_mk, Surreal.mk_add, Surreal.mk_mul, Surreal.mk_natCast, hWv,
        hgR q hq]
      have h2 : ((k + 1 : ℕ) : Surreal) = (k : Surreal) + 1 := by push_cast; ring
      rw [h2]
      nlinarith [hw0, hknn]
    · rw [forall_moves_mul]
      intro p' a ha b hb
      cases p' with
      | left =>
        rw [hnl, Set.mem_singleton_iff] at ha
        subst ha
        rw [show Player.left * Player.right = Player.right from rfl] at hb
        rw [show W.moves Player.right = Wᴿ from rfl, hWR] at hb
        obtain ⟨q, hq, rfl⟩ := hb
        haveI := hgRn q hq
        refine ⟨gR q, by rw [hCR]; exact Set.mem_image_of_mem _ hq, ?_⟩
        rw [← Surreal.mk_le_mk, mk_add_mulOption_nat_q_scale hWv hVv, hgR q hq]
        linarith [hknn]
      | right =>
        rw [hnr] at ha
        exact absurd ha (Set.notMem_empty a)
  · rw [hCL]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine ⟨x + mulOption (((k + 1 : ℕ) : IGame)) W ((k : ℕ) : IGame) 0,
      add_left_mem_moves_add (mulOption_mem_moves_mul (px := Player.left) (py := Player.left)
        (by rw [hnl]; exact Set.mem_singleton _)
        (by rw [show W.moves Player.left = Wᴸ from rfl, hWL]; exact Set.mem_singleton _)) _,
      ?_⟩
    rw [← Surreal.mk_le_mk, mk_add_mulOption_nat_zero_scale hWv, hgL]
  · rw [hCR]
    intro b hb
    obtain ⟨q, hq, rfl⟩ := hb
    haveI := hgRn q hq
    have hqh : (0 : Dyadic) < q * Dyadic.half := mul_pos hq half_pos_sr
    refine ⟨x + mulOption (((k + 1 : ℕ) : IGame)) W ((k : ℕ) : IGame)
        (((q * Dyadic.half : Dyadic) : IGame) * V),
      add_left_mem_moves_add (mulOption_mem_moves_mul (px := Player.left) (py := Player.right)
        (by rw [hnl]; exact Set.mem_singleton _)
        (by rw [show W.moves Player.right = Wᴿ from rfl, hWR]
            exact Set.mem_image_of_mem _ hqh)) _, ?_⟩
    rw [← Surreal.mk_le_mk, mk_add_mulOption_nat_q_scale hWv hVv, hgR q hq]
    -- A + k·w + (q/2)·v ≤ A + q·v
    have h1 := hkq (q * Dyadic.half) hqh
    have h2 : ((q * Dyadic.half : Dyadic) : Surreal) + ((q * Dyadic.half : Dyadic) : Surreal)
        = (q : Surreal) := by
      rw [← dyadic_cast_add', half_add_half_sr]
    have h3 : ((q * Dyadic.half : Dyadic) : Surreal) * v
          + ((q * Dyadic.half : Dyadic) : Surreal) * v = (q : Surreal) * v := by
      rw [← add_mul, h2]
    linarith

/-! ### The birthday induction along the dyadic grid, scale-parametric -/

private theorem lower_nonneg_of_pos_sr {r : Dyadic} (hr : 0 < r) : 0 ≤ r.lower := by
  have hnum : 0 < r.num := by
    have h : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr
    exact Rat.num_pos.2 h
  have hd : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.den_pos
  rw [← Dyadic.coe_le_coe]
  show (0 : ℚ) ≤ ((r.lower : Dyadic) : ℚ)
  rw [Dyadic.coe_lower]
  have hr' : (r : ℚ) = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den _).symm
  have key : (r : ℚ) - ((r.den : ℚ))⁻¹ = ((r.num : ℚ) - 1) / (r.den : ℚ) := by
    rw [hr']
    field_simp
  rw [key]
  refine div_nonneg ?_ hd.le
  have h1 : (1 : ℚ) ≤ (r.num : ℚ) := by exact_mod_cast hnum
  linarith

private theorem base_add_nat_succ (base : NatOrdinal) (i : ℕ) :
    (base + (i : NatOrdinal)) + 1 = base + ((i + 1 : ℕ) : NatOrdinal) := by
  rw [add_assoc]
  congr 1
  exact_mod_cast rfl

include hWL hWR hWv hVv hw0 hsep in
/-- **The parametric grid bound.** Given an anchor game `x` whose coarse translates
`mk x + q·v` are all realizable with birthday bound `base + c₀` (exclusive), each
positive grid point `mk x + r·w` is born by day `base + (hgt r − 1) + c₀`. The
induction unwinds the dyadic birth tree: integers step down by one, non-integers step to
their parents, each step costing one day via a two-sided cut pinned by the core
cofinality computations. -/
theorem scale_grid_aux (hxL : LeftSepV x v) (hxR : RightSepV x v)
    (base : NatOrdinal) (c₀ : ℕ)
    (hgames : ∀ q : Dyadic, 0 ≤ q → ∃ (g : IGame.{0}) (_ : g.Numeric),
      Surreal.mk g = Surreal.mk x + (q : Surreal) * v ∧
        g.birthday + 1 ≤ base + (c₀ : NatOrdinal)) :
    ∀ n : ℕ, ∀ r : Dyadic, 0 < r → Dyadic.hgt r ≤ n →
      (Surreal.mk x + (r : Surreal) * w).birthday
        ≤ base + ((Dyadic.hgt r - 1 + c₀ : ℕ) : NatOrdinal) := by
  intro n
  induction n with
  | zero =>
    intro r hr hrn
    have := Dyadic.hgt_pos_of_ne_zero hr.ne'
    omega
  | succ n ih =>
    intro r hr hrn
    -- a realization of `mk x + s·w` for any nonnegative `s` simpler than `r`
    have hrealize : ∀ s : Dyadic, 0 ≤ s → Dyadic.hgt s + 1 ≤ Dyadic.hgt r →
        ∃ (g : IGame.{0}) (_ : g.Numeric),
          Surreal.mk g = Surreal.mk x + (s : Surreal) * w ∧
            g.birthday + 1
              ≤ base + ((Dyadic.hgt r - 1 + c₀ : ℕ) : NatOrdinal) := by
      intro s hs hsr
      rcases eq_or_lt_of_le hs with h0 | hpos
      · obtain ⟨g, hgn, hgv, hgb⟩ := hgames 0 le_rfl
        refine ⟨g, hgn, ?_, ?_⟩
        · rw [hgv, ← h0, dyadic_cast_zero, zero_mul, zero_mul, add_zero]
        · refine hgb.trans (add_le_add le_rfl (nat_cast_mono ?_))
          omega
      · have hb := ih s hpos (by omega)
        obtain ⟨g, hgn, hgv, hgb⟩ := birthday_eq_iGameBirthday
          (Surreal.mk x + (s : Surreal) * w)
        refine ⟨g, hgn, hgv, ?_⟩
        rw [hgb]
        have h1 : (Surreal.mk x + (s : Surreal) * w).birthday + 1
            ≤ (base + ((Dyadic.hgt s - 1 + c₀ : ℕ) : NatOrdinal)) + 1 :=
          add_le_add hb (le_refl 1)
        refine h1.trans ?_
        rw [base_add_nat_succ]
        refine add_le_add le_rfl (nat_cast_mono ?_)
        have := Dyadic.hgt_pos_of_ne_zero hpos.ne'
        omega
    by_cases hden : r.den = 1
    · -- the integer case: `r = k + 1`
      have hnum : 0 < r.num := by
        have h : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr
        exact Rat.num_pos.2 h
      obtain ⟨k, hk⟩ : ∃ k : ℕ, r.num = ((k + 1 : ℕ) : ℤ) :=
        ⟨r.num.toNat - 1, by omega⟩
      have hreq : r = ((k + 1 : ℕ) : Dyadic) := by
        rw [Dyadic.eq_intCast_of_den_eq_one hden, hk]
        push_cast
        rfl
      subst hreq
      -- realizations for the cut options
      obtain ⟨gL, hgLn, hgLv, hgLb⟩ := hrealize ((k : ℕ) : Dyadic)
        (by exact_mod_cast Nat.zero_le k)
        (by rw [Dyadic.hgt_natCast, Dyadic.hgt_natCast])
      choose gR hgRn hgRv hgRb using fun q : Dyadic ↦ hgames q
      let gR' : Dyadic → IGame.{0} := fun q ↦ if h : 0 ≤ q then gR q h else 0
      have hgR'n : ∀ q : Dyadic, 0 < q → (gR' q).Numeric := by
        intro q hq
        show (if h : 0 ≤ q then gR q h else 0).Numeric
        rw [dif_pos hq.le]
        exact hgRn q hq.le
      have hgR'v : ∀ q (hq : 0 < q), @Surreal.mk (gR' q) (hgR'n q hq)
          = Surreal.mk x + (q : Surreal) * v := by
        intro q hq
        have h : gR' q = gR q hq.le := dif_pos hq.le
        rw [show @Surreal.mk (gR' q) (hgR'n q hq)
          = @Surreal.mk (gR q hq.le) (hgRn q hq.le) from by congr 1]
        exact hgRv q hq.le
      haveI := hgLn
      have hgLv' : Surreal.mk gL = Surreal.mk x + ((k : ℕ) : Surreal) * w := by
        rw [hgLv, dyadic_cast_natCast]
      have hequiv := add_natCast_succ_mul_scale_equiv hWL hWR hWv hVv hw0 hsep
        (x := x) k (gR := gR') hgR'n hgLv' hgR'v hxL hxR
      -- the cut is numeric
      have hCn : IGame.Numeric (!{{gL} | gR' '' Set.Ioi 0} : IGame.{0}) := by
        refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
        · rw [leftMoves_ofSets, Set.mem_singleton_iff] at hy
          rw [rightMoves_ofSets] at hz
          obtain ⟨q, hq, rfl⟩ := hz
          subst hy
          haveI := hgR'n q hq
          rw [← Surreal.mk_lt_mk, hgLv', hgR'v q hq]
          have h1 : ((k : ℕ) : Surreal) * w < (q : Surreal) * v := by
            have h := hsep ((k : ℕ) : Dyadic) hq
            rwa [dyadic_cast_natCast] at h
          linarith
        · cases p with
          | left =>
            rw [moves_ofSets, Set.mem_singleton_iff] at hy
            subst hy
            infer_instance
          | right =>
            rw [moves_ofSets] at hy
            obtain ⟨q, hq, rfl⟩ := hy
            exact hgR'n q hq
      -- value and birthday
      have hmkgame : Surreal.mk (x + (((k + 1 : ℕ) : IGame.{0})) * W)
          = Surreal.mk x + (((k + 1 : ℕ) : Dyadic) : Surreal) * w := by
        rw [Surreal.mk_add, Surreal.mk_mul, Surreal.mk_natCast, hWv, dyadic_cast_natCast]
      have hval : Surreal.mk x + (((k + 1 : ℕ) : Dyadic) : Surreal) * w
          = @Surreal.mk _ hCn := by
        haveI := hCn
        rw [← hmkgame]
        exact Surreal.mk_eq hequiv
      refine le_of_eq_of_le (congrArg birthday hval) ?_
      refine (birthday_mk_le _).trans ?_
      rw [IGame.birthday_ofSets]
      refine max_le ?_ ?_
      · refine csSup_le' ?_
        rintro o ⟨g, hg, rfl⟩
        rw [Set.mem_singleton_iff] at hg
        subst hg
        rw [Function.comp_apply, Order.succ_eq_add_one]
        refine hgLb.trans (add_le_add le_rfl (nat_cast_mono ?_))
        rw [Dyadic.hgt_natCast]
      · refine csSup_le' ?_
        rintro o ⟨g, ⟨q, hq, rfl⟩, rfl⟩
        rw [Function.comp_apply, Order.succ_eq_add_one]
        have h : gR' q = gR q hq.le := dif_pos hq.le
        rw [show (gR' q).birthday = (gR q hq.le).birthday from by rw [h]]
        refine (hgRb q hq.le).trans (add_le_add le_rfl (nat_cast_mono ?_))
        omega
    · -- the non-integer case: recurse to the parents
      have hlow0 : 0 ≤ r.lower := lower_nonneg_of_pos_sr hr
      have hup0 : 0 ≤ r.upper := (hlow0.trans (Dyadic.lower_lt r).le).trans (Dyadic.lt_upper r).le
      have hgtl := Dyadic.hgt_lower_lt hden
      have hgtu := Dyadic.hgt_upper_lt hden
      obtain ⟨gL, hgLn, hgLv, hgLb⟩ := hrealize r.lower hlow0 (by omega)
      obtain ⟨gU, hgUn, hgUv, hgUb⟩ := hrealize r.upper hup0 (by omega)
      haveI := hgLn
      haveI := hgUn
      have hequiv := add_dyadic_mul_scale_equiv_of_den_ne_one hWL hWR hWv hVv hsep
        (x := x) hden hgLv hgUv hxL hxR
      have hCn : IGame.Numeric (!{{gL} | {gU}} : IGame.{0}) := by
        refine IGame.Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
        · rw [leftMoves_ofSets, Set.mem_singleton_iff] at hy
          rw [rightMoves_ofSets, Set.mem_singleton_iff] at hz
          subst hy
          subst hz
          rw [← Surreal.mk_lt_mk, hgLv, hgUv]
          have h1 : (r.lower : Surreal) * w < (r.upper : Surreal) * w :=
            mul_lt_mul_of_pos_right (dyadic_cast_lt (Dyadic.lower_lt_upper r)) hw0
          linarith
        · cases p with
          | left =>
            rw [moves_ofSets, Set.mem_singleton_iff] at hy
            subst hy
            infer_instance
          | right =>
            rw [moves_ofSets, Set.mem_singleton_iff] at hy
            subst hy
            infer_instance
      have hmkgame : Surreal.mk (x + (r : IGame.{0}) * W)
          = Surreal.mk x + (r : Surreal) * w := by
        rw [Surreal.mk_add, Surreal.mk_mul, Surreal.mk_dyadic, hWv]
      have hval : Surreal.mk x + (r : Surreal) * w = @Surreal.mk _ hCn := by
        haveI := hCn
        rw [← hmkgame]
        exact Surreal.mk_eq hequiv
      refine le_of_eq_of_le (congrArg birthday hval) ?_
      refine (birthday_mk_le _).trans ?_
      rw [IGame.birthday_ofSets]
      refine max_le ?_ ?_
      · refine csSup_le' ?_
        rintro o ⟨g, hg, rfl⟩
        rw [Set.mem_singleton_iff] at hg
        subst hg
        rw [Function.comp_apply, Order.succ_eq_add_one]
        exact hgLb
      · refine csSup_le' ?_
        rintro o ⟨g, hg, rfl⟩
        rw [Set.mem_singleton_iff] at hg
        subst hg
        rw [Function.comp_apply, Order.succ_eq_add_one]
        exact hgUb

end Core

end Surreal

end
