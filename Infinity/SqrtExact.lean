/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import CombinatorialGames.Surreal.Division
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact square roots of surreal numbers

Every nonnegative surreal number has an exact square root. This file constructs it by the
game-theoretic recursion attributed to Clive Bach (mentioned in the *Properties of Division*
section of Conway's ONAG), mirroring the structure of `CombinatorialGames.Surreal.Division`:

For `0 < x`, the options of `y = √x` are generated recursively. The seeds are `0` and the
square roots `√z` of the positive options `z` of `x` (left options seed left, right options
seed right — recursion on the birthday of `x`). New options are produced by the *mediant map*

  `o(a, b) := (x + a·b) / (a + b)`,

whose square-defect factors through the defects of its inputs:

  `o(a, b)² − x = (o(a, b) − a) · (o(a, b) − b)`,   `o(a, b) − a = (x − a²)/(a + b)`.

Hence if `a² < x < b²` (a left and a right option), `o(a, b)` is a *left* option (its square
undershoots), while two options on the *same* side produce a *right* option. The auxiliary
inductive type `SqrtTy` enumerates these generation trees; special constructors `mixed0` and
`pairL0` handle the pairs involving the zero seed via `o(0, b) = x / b`, keeping every
enumerated value strictly positive (which is what makes the generation well-formed:
`o(a, b)` needs `a + b ≠ 0`).

The main theorem `IGame.Numeric.sqrt_mul_self` proves `√x · √x ≈ x` by simultaneous
induction: every left option of `√x` is nonnegative with square `< x`, every right option is
positive with square `> x` (`sqrt'_spec`), so `√x` is numeric and the options of the product
game `√x * √x` interleave with `x` exactly (`Fits.antisymm`).

At the quotient level this yields `Surreal.sqrt` with the defining properties

* `Surreal.sqrt_nonneg : 0 ≤ sqrt x`
* `Surreal.sq_sqrt : 0 ≤ x → sqrt x ^ 2 = x`
* `Surreal.sqrt_eq_of_sq_eq : 0 ≤ z → z ^ 2 = x → sqrt x = z` (uniqueness)

and the algebraic corollaries (`sqrt_mul`, `sqrt_inv`, strict monotonicity, …), culminating in

* `Surreal.isSquare_iff_nonneg : IsSquare x ↔ 0 ≤ x` —

the first of the two defining axioms of a real closed field, verified for the surreals.
-/

universe u

open IGame

noncomputable section

namespace IGame

/-! ### The square root game -/

/-- An auxiliary inductive type enumerating the options of `IGame.sqrt`.

Given types `lr .left`, `lr .right` of "seeds" (in application: the positive left/right
options of `x`), a term of `SqrtTy lr p` describes a recipe for an option of `√x` for
player `p`. Constructors:

* `seedL i` / `seedR i` : the square root of a positive option of `x` (left options of `x`
  give left options of `√x`, right give right);
* `mixed0 j` : `x / d` for `d` a previously generated right option — a left option
  (the mediant `o(0, d)` of the zero seed with `d`);
* `mixed i j` : the mediant `o(c, d)` of a left and a right option — a left option;
* `pairL0 i` : `x / c` for `c` a previously generated left option — a right option
  (the mediant `o(c, 0)`);
* `pairL i j` : the mediant of two generated left options — a right option;
* `pairR i j` : the mediant of two generated right options — a right option.

The zero left option itself is added separately (via `insert`), so that every value
enumerated by `SqrtTy` is strictly positive and the mediants are always well-defined. -/
private inductive SqrtTy (lr : Player → Type u) : Player → Type u
  | seedL : lr .left → SqrtTy lr .left
  | seedR : lr .right → SqrtTy lr .right
  | mixed0 : SqrtTy lr .right → SqrtTy lr .left
  | mixed : SqrtTy lr .left → SqrtTy lr .right → SqrtTy lr .left
  | pairL0 : SqrtTy lr .left → SqrtTy lr .right
  | pairL : SqrtTy lr .left → SqrtTy lr .left → SqrtTy lr .right
  | pairR : SqrtTy lr .right → SqrtTy lr .right → SqrtTy lr .right

private def SqrtTy.val' {x : IGame.{u}}
    (IH : ∀ p, Shrink.{u} {y ∈ x.moves p | 0 < y} → IGame.{u}) :
    ∀ b, SqrtTy (fun p ↦ Shrink.{u} {y ∈ x.moves p | 0 < y}) b → IGame.{u}
  | _, .seedL i => IH .left i
  | _, .seedR i => IH .right i
  | _, .mixed0 j => x / val' IH _ j
  | _, .mixed i j => (x + val' IH _ i * val' IH _ j) / (val' IH _ i + val' IH _ j)
  | _, .pairL0 i => x / val' IH _ i
  | _, .pairL i j => (x + val' IH _ i * val' IH _ j) / (val' IH _ i + val' IH _ j)
  | _, .pairR i j => (x + val' IH _ i * val' IH _ j) / (val' IH _ i + val' IH _ j)

private def sqrt' (x : IGame.{u}) : IGame.{u} :=
  let IH (p) : Shrink.{u} {y ∈ x.moves p | 0 < y} → IGame.{u} :=
    fun y ↦ sqrt' (Subtype.val <| (equivShrink _).symm y)
  !{insert 0 (Set.range (SqrtTy.val' IH .left)) | Set.range (SqrtTy.val' IH .right)}
termination_by x
decreasing_by exact .of_mem_moves ((equivShrink _).symm y).2.1

private abbrev SqrtTy.val (x : IGame.{u}) (b : Player)
    (i : SqrtTy (fun p ↦ Shrink.{u} {y ∈ x.moves p | 0 < y}) b) : IGame.{u} :=
  i.val' (fun _ ↦ sqrt' ∘ Subtype.val ∘ (equivShrink _).symm) b

/-- The square root of a positive surreal number `x`, as a game: options are seeded by the
square roots of the positive options of `x` and generated by the mediant map
`(a, b) ↦ (x + a·b) / (a + b)` (Bach's construction; see the module docstring).

For `x` not positive we take the junk value `0` (which is the correct value at `x = 0`).
If `x` is numeric and `0 ≤ x`, then `sqrt x` is numeric and `sqrt x * sqrt x ≈ x`. -/
def sqrt (x : IGame.{u}) : IGame.{u} := by
  classical exact if 0 < x then sqrt' x else 0

open Classical in
private theorem sqrt_def {x : IGame.{u}} :
    sqrt x = if 0 < x then sqrt' x else 0 :=
  rfl

private theorem sqrt_of_pos {x : IGame.{u}} (hx : 0 < x) : sqrt x = sqrt' x := by
  rw [sqrt_def, if_pos hx]

theorem sqrt_of_not_pos {x : IGame.{u}} (hx : ¬ 0 < x) : sqrt x = 0 := by
  rw [sqrt_def, if_neg hx]

@[simp]
theorem sqrt_zero : sqrt (0 : IGame) = 0 :=
  sqrt_of_not_pos (lt_irrefl 0)

private theorem sqrt_eq {x : IGame.{u}} (hx : 0 < x) :
    sqrt x = !{insert 0 (Set.range (SqrtTy.val x .left)) | Set.range (SqrtTy.val x .right)} := by
  rw [sqrt_of_pos hx, sqrt']
  rfl

private theorem zero_mem_leftMoves_sqrt {x : IGame.{u}} (hx : 0 < x) : 0 ∈ (sqrt x)ᴸ := by
  rw [sqrt_eq hx, leftMoves_ofSets]
  exact Set.mem_insert ..

private theorem val_mem_moves_sqrt {x : IGame.{u}} (hx : 0 < x) (b : Player)
    (i : SqrtTy (fun p ↦ Shrink.{u} {y ∈ x.moves p | 0 < y}) b) :
    SqrtTy.val x b i ∈ (sqrt x).moves b := by
  rw [sqrt_eq hx]
  cases b
  · rw [leftMoves_ofSets]
    exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
  · rw [rightMoves_ofSets]
    exact ⟨i, rfl⟩

private theorem forall_leftMoves_sqrt {x : IGame.{u}} (hx : 0 < x) {P : IGame → Prop} :
    (∀ a ∈ (sqrt x)ᴸ, P a) ↔
      P 0 ∧ ∀ i, P (SqrtTy.val x .left i) := by
  rw [sqrt_eq hx, leftMoves_ofSets]
  constructor
  · exact fun h ↦ ⟨h 0 (Set.mem_insert ..), fun i ↦ h _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩)⟩
  · rintro ⟨h0, h⟩ a (rfl | ⟨i, rfl⟩)
    exacts [h0, h i]

private theorem forall_rightMoves_sqrt {x : IGame.{u}} (hx : 0 < x) {P : IGame → Prop} :
    (∀ a ∈ (sqrt x)ᴿ, P a) ↔ ∀ i, P (SqrtTy.val x .right i) := by
  rw [sqrt_eq hx, rightMoves_ofSets]
  constructor
  · exact fun h i ↦ h _ ⟨i, rfl⟩
  · rintro h a ⟨i, rfl⟩
    exact h i

end IGame

/-! ### Ordered-field arithmetic of the mediant map

Pure `Surreal`-level lemmas: the mediant `o(A, B) = (X + A·B)/(A + B)` has square-defect
`o² − X = (o − A)(o − B)`, with `o − A = (X − A²)/(A + B)`. Options on opposite sides of
`√X` produce values whose square undershoots `X`; same-side options overshoot. -/

namespace Surreal

private theorem lt_of_mul_self_lt_mul_self {a b : Surreal} (_ha : 0 ≤ a)
    (h : a * a < b * b) (hb : 0 < b) : a < b := by
  by_contra hab
  rw [not_lt] at hab
  exact absurd (mul_self_le_mul_self hb.le hab) (not_le.2 h)

private theorem mediant_left {X A B : Surreal} (hA : 0 ≤ A) (hA2 : A * A < X) (hB : 0 < B)
    (hB2 : X < B * B) :
    0 < (X + A * B) / (A + B) ∧ (X + A * B) / (A + B) * ((X + A * B) / (A + B)) < X := by
  have hX : 0 < X := lt_of_le_of_lt (mul_self_nonneg A) hA2
  have hAB : 0 < A + B := add_pos_of_nonneg_of_pos hA hB
  have hne : A + B ≠ 0 := hAB.ne'
  refine ⟨div_pos (add_pos_of_pos_of_nonneg hX (mul_nonneg hA hB.le)) hAB, ?_⟩
  have key : X - (X + A * B) / (A + B) * ((X + A * B) / (A + B)) =
      (X - A * A) * (B * B - X) / ((A + B) * (A + B)) := by
    field_simp
    ring
  have hpos : 0 < (X - A * A) * (B * B - X) / ((A + B) * (A + B)) :=
    div_pos (mul_pos (sub_pos.2 hA2) (sub_pos.2 hB2)) (mul_pos hAB hAB)
  linarith

private theorem mediant_right {X A B : Surreal} (hA : 0 < A) (hA2 : A * A < X) (hB : 0 ≤ B)
    (hB2 : B * B < X) :
    0 < (X + A * B) / (A + B) ∧ X < (X + A * B) / (A + B) * ((X + A * B) / (A + B)) := by
  have hX : 0 < X := lt_of_le_of_lt (mul_self_nonneg A) hA2
  have hAB : 0 < A + B := add_pos_of_pos_of_nonneg hA hB
  have hne : A + B ≠ 0 := hAB.ne'
  refine ⟨div_pos (add_pos_of_pos_of_nonneg hX (mul_nonneg hA.le hB)) hAB, ?_⟩
  have key : (X + A * B) / (A + B) * ((X + A * B) / (A + B)) - X =
      (X - A * A) * (X - B * B) / ((A + B) * (A + B)) := by
    field_simp
    ring
  have hpos : 0 < (X - A * A) * (X - B * B) / ((A + B) * (A + B)) :=
    div_pos (mul_pos (sub_pos.2 hA2) (sub_pos.2 hB2)) (mul_pos hAB hAB)
  linarith

private theorem mediant_rightR {X A B : Surreal} (hX : 0 < X) (hA : 0 < A) (hA2 : X < A * A)
    (hB : 0 < B) (hB2 : X < B * B) :
    0 < (X + A * B) / (A + B) ∧ X < (X + A * B) / (A + B) * ((X + A * B) / (A + B)) := by
  have hAB : 0 < A + B := add_pos hA hB
  have hne : A + B ≠ 0 := hAB.ne'
  refine ⟨div_pos (add_pos hX (mul_pos hA hB)) hAB, ?_⟩
  have key : (X + A * B) / (A + B) * ((X + A * B) / (A + B)) - X =
      (A * A - X) * (B * B - X) / ((A + B) * (A + B)) := by
    field_simp
    ring
  have hpos : 0 < (A * A - X) * (B * B - X) / ((A + B) * (A + B)) :=
    div_pos (mul_pos (sub_pos.2 hA2) (sub_pos.2 hB2)) (mul_pos hAB hAB)
  linarith

private theorem recip_left {X B : Surreal} (hX : 0 < X) (hB : 0 < B) (hB2 : X < B * B) :
    0 < X / B ∧ X / B * (X / B) < X := by
  have hne : B ≠ 0 := hB.ne'
  refine ⟨div_pos hX hB, ?_⟩
  have key : X - X / B * (X / B) = X * (B * B - X) / (B * B) := by
    field_simp
  have hpos : 0 < X * (B * B - X) / (B * B) :=
    div_pos (mul_pos hX (sub_pos.2 hB2)) (mul_pos hB hB)
  linarith

private theorem recip_right {X A : Surreal} (hX : 0 < X) (hA : 0 < A) (hA2 : A * A < X) :
    0 < X / A ∧ X < X / A * (X / A) := by
  have hne : A ≠ 0 := hA.ne'
  refine ⟨div_pos hX hA, ?_⟩
  have key : X / A * (X / A) - X = X * (X - A * A) / (A * A) := by
    field_simp
  have hpos : 0 < X * (X - A * A) / (A * A) :=
    div_pos (mul_pos hX (sub_pos.2 hA2)) (mul_pos hA hA)
  linarith

/-- If the mediant `(X + A·B)/(A + B)` is a *right* option (so `Y` is below it), then the
`mulOption` value `A·Y + Y·B − A·B` is below `X`. -/
private theorem mulOption_lt_of_lt_mediant {X A B Y : Surreal} (hAB : 0 < A + B)
    (h : Y < (X + A * B) / (A + B)) : A * Y + Y * B - A * B < X := by
  rw [lt_div_iff₀ hAB] at h
  have e : Y * (A + B) = A * Y + Y * B := by ring
  linarith

/-- If the mediant `(X + A·B)/(A + B)` is a *left* option (so `Y` is above it), then the
`mulOption` value `A·Y + Y·B − A·B` is above `X`. -/
private theorem lt_mulOption_of_mediant_lt {X A B Y : Surreal} (hAB : 0 < A + B)
    (h : (X + A * B) / (A + B) < Y) : X < A * Y + Y * B - A * B := by
  rw [div_lt_iff₀ hAB] at h
  have e : (A + B) * Y = A * Y + Y * B := by ring
  linarith

end Surreal

namespace IGame

private instance instNumericMulOption (x y a b : IGame) [Numeric x] [Numeric y] [Numeric a]
    [Numeric b] : Numeric (mulOption x y a b) :=
  inferInstanceAs (Numeric (a * y + x * b - a * b))

private theorem mk_mulOption (y a b : IGame) [Numeric y] [Numeric a] [Numeric b] :
    Surreal.mk (mulOption y y a b) =
      Surreal.mk a * Surreal.mk y + Surreal.mk y * Surreal.mk b
        - Surreal.mk a * Surreal.mk b := by
  show Surreal.mk (a * y + y * b - a * b) = _
  simp

/-! ### The inductive specification of the generated options -/

/-- The specification of the options of `√x`: numeric, strictly positive, with the square on
the correct side of `x` — left options undershoot, right options overshoot. -/
private def SqrtSpec (x v : IGame) (b : Player) : Prop :=
  Numeric v ∧ 0 < v ∧ b.cases (v * v < x) (x < v * v)

/-- The inductive hypothesis for the main recursion: the square root construction works for
every positive option of `x`. -/
private def SqrtIH (x : IGame.{u}) : Prop :=
  ∀ p, ∀ z ∈ x.moves p, 0 < z → Numeric (sqrt z) ∧ 0 < sqrt z ∧ sqrt z * sqrt z ≈ z

variable {x : IGame.{u}}

private theorem SqrtSpec.numeric {v : IGame} {b} (h : SqrtSpec x v b) : Numeric v := h.1
private theorem SqrtSpec.pos {v : IGame} {b} (h : SqrtSpec x v b) : 0 < v := h.2.1
private theorem SqrtSpec.sq_lt {v : IGame} (h : SqrtSpec x v .left) : v * v < x := h.2.2
private theorem SqrtSpec.lt_sq {v : IGame} (h : SqrtSpec x v .right) : x < v * v := h.2.2

private theorem SqrtSpec.mk_left {v : IGame} (hn : Numeric v) (hp : 0 < v)
    (hsq : v * v < x) : SqrtSpec x v .left :=
  ⟨hn, hp, hsq⟩

private theorem SqrtSpec.mk_right {v : IGame} (hn : Numeric v) (hp : 0 < v)
    (hsq : x < v * v) : SqrtSpec x v .right :=
  ⟨hn, hp, hsq⟩

/-! Reduction lemmas for the option valuation. -/

private theorem val_seedL (i) :
    SqrtTy.val x .left (.seedL i) = sqrt' ((equivShrink {y ∈ xᴸ | 0 < y}).symm i).1 :=
  rfl

private theorem val_seedR (i) :
    SqrtTy.val x .right (.seedR i) = sqrt' ((equivShrink {y ∈ xᴿ | 0 < y}).symm i).1 :=
  rfl

private theorem val_mixed0 (j) :
    SqrtTy.val x .left (.mixed0 j) = x / SqrtTy.val x .right j :=
  rfl

private theorem val_mixed (i j) :
    SqrtTy.val x .left (.mixed i j) =
      (x + SqrtTy.val x .left i * SqrtTy.val x .right j) /
        (SqrtTy.val x .left i + SqrtTy.val x .right j) :=
  rfl

private theorem val_pairL0 (i) :
    SqrtTy.val x .right (.pairL0 i) = x / SqrtTy.val x .left i :=
  rfl

private theorem val_pairL (i j) :
    SqrtTy.val x .right (.pairL i j) =
      (x + SqrtTy.val x .left i * SqrtTy.val x .left j) /
        (SqrtTy.val x .left i + SqrtTy.val x .left j) :=
  rfl

private theorem val_pairR (i j) :
    SqrtTy.val x .right (.pairR i j) =
      (x + SqrtTy.val x .right i * SqrtTy.val x .right j) /
        (SqrtTy.val x .right i + SqrtTy.val x .right j) :=
  rfl

/-! Transfer lemmas between the game order and the surreal order. -/

private theorem mk_pos_of {a : IGame} [Numeric a] (h : 0 < a) : 0 < Surreal.mk a := by
  simpa using Surreal.mk_lt_mk.2 h

private theorem pos_of_mk {a : IGame} [Numeric a] (h : 0 < Surreal.mk a) : 0 < a := by
  rw [← Surreal.mk_zero] at h
  exact Surreal.mk_lt_mk.1 h

private theorem mk_sq_lt_of {a c : IGame} [Numeric a] [Numeric c] (h : a * a < c) :
    Surreal.mk a * Surreal.mk a < Surreal.mk c := by
  rw [← Surreal.mk_mul]
  exact Surreal.mk_lt_mk.2 h

private theorem lt_mk_sq_of {a c : IGame} [Numeric a] [Numeric c] (h : c < a * a) :
    Surreal.mk c < Surreal.mk a * Surreal.mk a := by
  rw [← Surreal.mk_mul]
  exact Surreal.mk_lt_mk.2 h

variable [Numeric x]

private theorem val_spec (hx : 0 < x) (IH : SqrtIH x) :
    ∀ b i, SqrtSpec x (SqrtTy.val x b i) b := by
  have hX : (0 : Surreal) < Surreal.mk x := mk_pos_of hx
  intro b i
  induction i with
  | seedL i =>
    rw [val_seedL]
    generalize (equivShrink {y ∈ xᴸ | 0 < y}).symm i = w
    obtain ⟨z, hz, hz0⟩ := w
    obtain ⟨hn, hp, hsq⟩ := IH _ z hz hz0
    rw [← sqrt_of_pos hz0]
    haveI := Numeric.of_mem_moves hz
    haveI := hn
    refine SqrtSpec.mk_left hn hp ?_
    have h1 : Surreal.mk (sqrt z * sqrt z) < Surreal.mk x := by
      rw [Surreal.mk_eq_mk.2 hsq]
      exact Surreal.mk_lt_mk.2 (Numeric.left_lt hz)
    exact Surreal.mk_lt_mk.1 h1
  | seedR i =>
    rw [val_seedR]
    generalize (equivShrink {y ∈ xᴿ | 0 < y}).symm i = w
    obtain ⟨z, hz, hz0⟩ := w
    obtain ⟨hn, hp, hsq⟩ := IH _ z hz hz0
    rw [← sqrt_of_pos hz0]
    haveI := Numeric.of_mem_moves hz
    haveI := hn
    refine SqrtSpec.mk_right hn hp ?_
    have h1 : Surreal.mk x < Surreal.mk (sqrt z * sqrt z) := by
      rw [Surreal.mk_eq_mk.2 hsq]
      exact Surreal.mk_lt_mk.2 (Numeric.lt_right hz)
    exact Surreal.mk_lt_mk.1 h1
  | mixed0 j ihj =>
    rw [val_mixed0]
    haveI := ihj.numeric
    obtain ⟨h1, h2⟩ := Surreal.recip_left hX (mk_pos_of ihj.pos) (lt_mk_sq_of ihj.lt_sq)
    simp only [← Surreal.mk_div, ← Surreal.mk_mul] at h1 h2
    exact SqrtSpec.mk_left inferInstance (pos_of_mk h1) (Surreal.mk_lt_mk.1 h2)
  | mixed i j ihi ihj =>
    rw [val_mixed]
    haveI := ihi.numeric
    haveI := ihj.numeric
    obtain ⟨h1, h2⟩ := Surreal.mediant_left (mk_pos_of ihi.pos).le (mk_sq_lt_of ihi.sq_lt)
      (mk_pos_of ihj.pos) (lt_mk_sq_of ihj.lt_sq)
    simp only [← Surreal.mk_mul, ← Surreal.mk_add, ← Surreal.mk_div] at h1 h2
    exact SqrtSpec.mk_left inferInstance (pos_of_mk h1) (Surreal.mk_lt_mk.1 h2)
  | pairL0 i ihi =>
    rw [val_pairL0]
    haveI := ihi.numeric
    obtain ⟨h1, h2⟩ := Surreal.recip_right hX (mk_pos_of ihi.pos) (mk_sq_lt_of ihi.sq_lt)
    simp only [← Surreal.mk_div, ← Surreal.mk_mul] at h1 h2
    exact SqrtSpec.mk_right inferInstance (pos_of_mk h1) (Surreal.mk_lt_mk.1 h2)
  | pairL i j ihi ihj =>
    rw [val_pairL]
    haveI := ihi.numeric
    haveI := ihj.numeric
    obtain ⟨h1, h2⟩ := Surreal.mediant_right (mk_pos_of ihi.pos) (mk_sq_lt_of ihi.sq_lt)
      (mk_pos_of ihj.pos).le (mk_sq_lt_of ihj.sq_lt)
    simp only [← Surreal.mk_mul, ← Surreal.mk_add, ← Surreal.mk_div] at h1 h2
    exact SqrtSpec.mk_right inferInstance (pos_of_mk h1) (Surreal.mk_lt_mk.1 h2)
  | pairR i j ihi ihj =>
    rw [val_pairR]
    haveI := ihi.numeric
    haveI := ihj.numeric
    obtain ⟨h1, h2⟩ := Surreal.mediant_rightR hX (mk_pos_of ihi.pos) (lt_mk_sq_of ihi.lt_sq)
      (mk_pos_of ihj.pos) (lt_mk_sq_of ihj.lt_sq)
    simp only [← Surreal.mk_mul, ← Surreal.mk_add, ← Surreal.mk_div] at h1 h2
    exact SqrtSpec.mk_right inferInstance (pos_of_mk h1) (Surreal.mk_lt_mk.1 h2)

/-! ### `√x` is numeric, positive, and squares to `x` -/

private theorem mem_moves_sqrt_elim (hx : 0 < x) {p : Player} {a : IGame}
    (ha : a ∈ (sqrt x).moves p) :
    (p = .left ∧ a = 0) ∨ ∃ i, a = SqrtTy.val x p i := by
  rw [sqrt_eq hx] at ha
  cases p
  · rw [leftMoves_ofSets] at ha
    obtain rfl | ⟨i, rfl⟩ := ha
    exacts [.inl ⟨rfl, rfl⟩, .inr ⟨i, rfl⟩]
  · rw [rightMoves_ofSets] at ha
    obtain ⟨i, rfl⟩ := ha
    exact .inr ⟨i, rfl⟩

private theorem sqrt_mem_moves_sqrt (hx : 0 < x) {p : Player} {z : IGame}
    (hz : z ∈ x.moves p) (hz0 : 0 < z) : sqrt z ∈ (sqrt x).moves p := by
  cases p
  · have h := val_mem_moves_sqrt hx .left (.seedL (equivShrink {y ∈ xᴸ | 0 < y} ⟨z, hz, hz0⟩))
    have e : SqrtTy.val x .left (.seedL (equivShrink {y ∈ xᴸ | 0 < y} ⟨z, hz, hz0⟩)) =
        sqrt z := by
      rw [val_seedL, Equiv.symm_apply_apply]
      exact (sqrt_of_pos hz0).symm
    exact e ▸ h
  · have h := val_mem_moves_sqrt hx .right (.seedR (equivShrink {y ∈ xᴿ | 0 < y} ⟨z, hz, hz0⟩))
    have e : SqrtTy.val x .right (.seedR (equivShrink {y ∈ xᴿ | 0 < y} ⟨z, hz, hz0⟩)) =
        sqrt z := by
      rw [val_seedR, Equiv.symm_apply_apply]
      exact (sqrt_of_pos hz0).symm
    exact e ▸ h

private theorem numeric_sqrt_aux (hx : 0 < x)
    (hs : ∀ b i, SqrtSpec x (SqrtTy.val x b i) b) : Numeric (sqrt x) := by
  rw [sqrt_eq hx]
  refine Numeric.mk ?_ ?_
  · simp only [leftMoves_ofSets, rightMoves_ofSets]
    rintro a (rfl | ⟨i, rfl⟩) c ⟨j, rfl⟩
    · exact (hs .right j).pos
    · haveI := (hs .left i).numeric
      haveI := (hs .right j).numeric
      have h1 : Surreal.mk (SqrtTy.val x .left i) < Surreal.mk (SqrtTy.val x .right j) :=
        Surreal.lt_of_mul_self_lt_mul_self (mk_pos_of (hs .left i).pos).le
          ((mk_sq_lt_of (hs .left i).sq_lt).trans (lt_mk_sq_of (hs .right j).lt_sq))
          (mk_pos_of (hs .right j).pos)
      exact Surreal.mk_lt_mk.1 h1
  · intro p y hy
    cases p
    · rw [leftMoves_ofSets] at hy
      obtain rfl | ⟨i, rfl⟩ := hy
      · exact Numeric.zero
      · exact (hs .left i).numeric
    · rw [rightMoves_ofSets] at hy
      obtain ⟨i, rfl⟩ := hy
      exact (hs .right i).numeric

private theorem sqrt_pos_aux (hx : 0 < x) (hn : Numeric (sqrt x)) : 0 < sqrt x :=
  have := hn
  Numeric.left_lt (zero_mem_leftMoves_sqrt hx)

private theorem sqrt_mul_self_aux (hx : 0 < x) (IH : SqrtIH x)
    (hs : ∀ b i, SqrtSpec x (SqrtTy.val x b i) b) (hn : Numeric (sqrt x)) :
    sqrt x * sqrt x ≈ x := by
  haveI := hn
  have hy0 : 0 < sqrt x := sqrt_pos_aux hx hn
  have hY : (0 : Surreal) < Surreal.mk (sqrt x) := mk_pos_of hy0
  have hX : (0 : Surreal) < Surreal.mk x := mk_pos_of hx
  refine Fits.antisymm ⟨?_, ?_⟩ ⟨?_, ?_⟩
  -- (C) every left option of `x` is below `√x · √x`
  · intro z hz
    haveI := Numeric.of_mem_moves hz
    rw [Numeric.not_le]
    obtain hz0 | hz0 := Numeric.lt_or_ge 0 z
    · obtain ⟨hnz, hpz, hsqz⟩ := IH _ z hz hz0
      haveI := hnz
      have hmem : sqrt z ∈ (sqrt x)ᴸ := sqrt_mem_moves_sqrt hx hz hz0
      have h1 : Surreal.mk z < Surreal.mk (sqrt x * sqrt x) := by
        rw [← Surreal.mk_eq_mk.2 hsqz, Surreal.mk_mul, Surreal.mk_mul]
        exact mul_self_lt_mul_self (mk_pos_of hpz).le
          (Surreal.mk_lt_mk.2 (Numeric.left_lt hmem))
      exact Surreal.mk_lt_mk.1 h1
    · exact hz0.trans_lt (Numeric.mul_pos hy0 hy0)
  -- (D) every right option of `x` is above `√x · √x`
  · intro z hz
    haveI := Numeric.of_mem_moves hz
    rw [Numeric.not_le]
    have hz0 : 0 < z := hx.trans (Numeric.lt_right hz)
    obtain ⟨hnz, hpz, hsqz⟩ := IH _ z hz hz0
    haveI := hnz
    have hmem : sqrt z ∈ (sqrt x)ᴿ := sqrt_mem_moves_sqrt hx hz hz0
    have h1 : Surreal.mk (sqrt x * sqrt x) < Surreal.mk z := by
      rw [← Surreal.mk_eq_mk.2 hsqz, Surreal.mk_mul, Surreal.mk_mul]
      exact mul_self_lt_mul_self hY.le (Surreal.mk_lt_mk.2 (Numeric.lt_right hmem))
    exact Surreal.mk_lt_mk.1 h1
  -- (A) every left option of `√x · √x` is below `x`
  · rw [forall_moves_mul]
    intro p'
    cases p' <;>
      simp only [Player.left_mul, Player.right_mul, Player.neg_left] <;>
      intro a ha b hb
    -- a, b both left options of `√x`
    · rcases mem_moves_sqrt_elim hx ha with ⟨-, rfl⟩ | ⟨i, rfl⟩ <;>
        rcases mem_moves_sqrt_elim hx hb with ⟨-, rfl⟩ | ⟨j, rfl⟩
      · -- (0, 0)
        rw [Numeric.not_le]
        refine Surreal.mk_lt_mk.1 ?_
        rw [mk_mulOption]
        simpa using hX
      · -- (0, val j)
        haveI := (hs .left j).numeric
        rw [Numeric.not_le]
        have hmem : sqrt x < SqrtTy.val x .right (.pairL0 j) :=
          Numeric.lt_right (val_mem_moves_sqrt hx .right (.pairL0 j))
        rw [val_pairL0] at hmem
        have hmem' := Surreal.mk_lt_mk.2 hmem
        simp only [Surreal.mk_div] at hmem'
        have h2 : Surreal.mk (sqrt x) * Surreal.mk (SqrtTy.val x .left j) < Surreal.mk x :=
          (lt_div_iff₀ (mk_pos_of (hs .left j).pos)).1 hmem'
        refine Surreal.mk_lt_mk.1 ?_
        rw [mk_mulOption]
        simpa using h2
      · -- (val i, 0)
        haveI := (hs .left i).numeric
        rw [Numeric.not_le]
        have hmem : sqrt x < SqrtTy.val x .right (.pairL0 i) :=
          Numeric.lt_right (val_mem_moves_sqrt hx .right (.pairL0 i))
        rw [val_pairL0] at hmem
        have hmem' := Surreal.mk_lt_mk.2 hmem
        simp only [Surreal.mk_div] at hmem'
        have h2 : Surreal.mk (sqrt x) * Surreal.mk (SqrtTy.val x .left i) < Surreal.mk x :=
          (lt_div_iff₀ (mk_pos_of (hs .left i).pos)).1 hmem'
        refine Surreal.mk_lt_mk.1 ?_
        rw [mk_mulOption]
        simpa [mul_comm] using h2
      · -- (val i, val j)
        haveI := (hs .left i).numeric
        haveI := (hs .left j).numeric
        rw [Numeric.not_le]
        have hmem : sqrt x < SqrtTy.val x .right (.pairL i j) :=
          Numeric.lt_right (val_mem_moves_sqrt hx .right (.pairL i j))
        rw [val_pairL] at hmem
        have hmem' := Surreal.mk_lt_mk.2 hmem
        simp only [Surreal.mk_div, Surreal.mk_add, Surreal.mk_mul] at hmem'
        refine Surreal.mk_lt_mk.1 ?_
        rw [mk_mulOption]
        exact Surreal.mulOption_lt_of_lt_mediant
          (add_pos (mk_pos_of (hs .left i).pos) (mk_pos_of (hs .left j).pos)) hmem'
    -- a, b both right options of `√x`
    · rcases mem_moves_sqrt_elim hx ha with ⟨h, -⟩ | ⟨i, rfl⟩
      · exact absurd h (by simp)
      rcases mem_moves_sqrt_elim hx hb with ⟨h, -⟩ | ⟨j, rfl⟩
      · exact absurd h (by simp)
      haveI := (hs .right i).numeric
      haveI := (hs .right j).numeric
      rw [Numeric.not_le]
      have hmem : sqrt x < SqrtTy.val x .right (.pairR i j) :=
        Numeric.lt_right (val_mem_moves_sqrt hx .right (.pairR i j))
      rw [val_pairR] at hmem
      have hmem' := Surreal.mk_lt_mk.2 hmem
      simp only [Surreal.mk_div, Surreal.mk_add, Surreal.mk_mul] at hmem'
      refine Surreal.mk_lt_mk.1 ?_
      rw [mk_mulOption]
      exact Surreal.mulOption_lt_of_lt_mediant
        (add_pos (mk_pos_of (hs .right i).pos) (mk_pos_of (hs .right j).pos)) hmem'
  -- (B) every right option of `√x · √x` is above `x`
  · rw [forall_moves_mul]
    intro p'
    cases p' <;>
      simp only [Player.left_mul, Player.right_mul, Player.neg_left, Player.neg_right,
        Player.mul_right] <;>
      intro a ha b hb
    -- a a left option, b a right option
    · rcases mem_moves_sqrt_elim hx hb with ⟨h, -⟩ | ⟨j, rfl⟩
      · exact absurd h (by simp)
      haveI := (hs .right j).numeric
      rcases mem_moves_sqrt_elim hx ha with ⟨-, rfl⟩ | ⟨i, rfl⟩
      · -- (0, val j)
        rw [Numeric.not_le]
        refine Surreal.mk_lt_mk.1 ?_
        rw [mk_mulOption]
        have hmem := hval_lt (.mixed0 j)
        rw [val_mixed0, Surreal.mk_div] at hmem
        have hB : (0 : Surreal) < Surreal.mk (SqrtTy.val x .right j) :=
          mk_pos_of (hs .right j).pos
        have h2 : Surreal.mk x < Surreal.mk (sqrt x) * Surreal.mk (SqrtTy.val x .right j) :=
          (div_lt_iff₀ hB).1 hmem
        simpa using h2
      · -- (val i, val j)
        haveI := (hs .left i).numeric
        rw [Numeric.not_le]
        refine Surreal.mk_lt_mk.1 ?_
        rw [mk_mulOption]
        have hmem := hval_lt (.mixed i j)
        rw [val_mixed, Surreal.mk_div, Surreal.mk_add, Surreal.mk_add, Surreal.mk_mul] at hmem
        exact Surreal.lt_mulOption_of_mediant_lt
          (add_pos (mk_pos_of (hs .left i).pos) (mk_pos_of (hs .right j).pos)) hmem
    -- a a right option, b a left option
    · rcases mem_moves_sqrt_elim hx ha with ⟨h, -⟩ | ⟨i, rfl⟩
      · exact absurd h (by simp)
      haveI := (hs .right i).numeric
      rcases mem_moves_sqrt_elim hx hb with ⟨-, rfl⟩ | ⟨j, rfl⟩
      · -- (val i, 0)
        rw [Numeric.not_le]
        refine Surreal.mk_lt_mk.1 ?_
        rw [mk_mulOption]
        have hmem := hval_lt (.mixed0 i)
        rw [val_mixed0, Surreal.mk_div] at hmem
        have hA : (0 : Surreal) < Surreal.mk (SqrtTy.val x .right i) :=
          mk_pos_of (hs .right i).pos
        have h2 : Surreal.mk x < Surreal.mk (sqrt x) * Surreal.mk (SqrtTy.val x .right i) :=
          (div_lt_iff₀ hA).1 hmem
        have e : Surreal.mk (sqrt x) * Surreal.mk (SqrtTy.val x .right i) =
            Surreal.mk (SqrtTy.val x .right i) * Surreal.mk (sqrt x) := mul_comm ..
        rw [e] at h2
        simpa using h2
      · -- (val i right, val j left)
        haveI := (hs .left j).numeric
        rw [Numeric.not_le]
        refine Surreal.mk_lt_mk.1 ?_
        rw [mk_mulOption]
        have hmem := hval_lt (.mixed j i)
        rw [val_mixed, Surreal.mk_div, Surreal.mk_add, Surreal.mk_add, Surreal.mk_mul] at hmem
        have h2 := Surreal.lt_mulOption_of_mediant_lt
          (add_pos (mk_pos_of (hs .left j).pos) (mk_pos_of (hs .right i).pos)) hmem
        have e : Surreal.mk (SqrtTy.val x .left j) * Surreal.mk (sqrt x) +
              Surreal.mk (sqrt x) * Surreal.mk (SqrtTy.val x .right i) -
              Surreal.mk (SqrtTy.val x .left j) * Surreal.mk (SqrtTy.val x .right i) =
            Surreal.mk (SqrtTy.val x .right i) * Surreal.mk (sqrt x) +
              Surreal.mk (sqrt x) * Surreal.mk (SqrtTy.val x .left j) -
              Surreal.mk (SqrtTy.val x .right i) * Surreal.mk (SqrtTy.val x .left j) := by
          ring
        rw [e] at h2
        exact h2

omit [Numeric x] in
/-- The complete recursion: for positive numeric `x`, the square root game is numeric,
positive, and squares to `x`. -/
private theorem sqrt_main {x : IGame.{u}} [Numeric x] (hx : 0 < x) :
    Numeric (sqrt x) ∧ 0 < sqrt x ∧ sqrt x * sqrt x ≈ x := by
  have IH : SqrtIH x := by
    intro p z hz hz0
    have := Numeric.of_mem_moves hz
    exact sqrt_main hz0
  have hs := val_spec hx IH
  have hn := numeric_sqrt_aux hx hs
  exact ⟨hn, sqrt_pos_aux hx hn, sqrt_mul_self_aux hx IH hs hn⟩
termination_by x
decreasing_by igame_wf

/-! ### The public interface -/

namespace Numeric

protected instance sqrt (x : IGame) [Numeric x] : Numeric (IGame.sqrt x) := by
  obtain hx | hx := Classical.em (0 < x)
  · exact (sqrt_main hx).1
  · rw [sqrt_of_not_pos hx]
    exact Numeric.zero

/-- The square root of a positive number is positive. -/
theorem sqrt_pos {x : IGame} [Numeric x] (hx : 0 < x) : 0 < IGame.sqrt x :=
  (sqrt_main hx).2.1

theorem sqrt_nonneg (x : IGame) [Numeric x] : 0 ≤ IGame.sqrt x := by
  obtain hx | hx := Classical.em (0 < x)
  · exact (Numeric.sqrt_pos hx).le
  · rw [sqrt_of_not_pos hx]

/-- **Exact square roots on games**: for a nonnegative numeric game,
`√x · √x` is equivalent to `x`. -/
theorem sqrt_mul_self {x : IGame} [Numeric x] (hx : 0 ≤ x) :
    IGame.sqrt x * IGame.sqrt x ≈ x := by
  obtain hx' | hx' := Classical.em (0 < x)
  · exact (sqrt_main hx').2.2
  · have h0 : x ≈ 0 := ⟨Numeric.not_lt.1 hx', hx⟩
    rw [sqrt_of_not_pos hx', mul_zero]
    exact h0.symm

/-- The square root construction respects equivalence of games. -/
theorem sqrt_congr {x y : IGame} [Numeric x] [Numeric y] (he : x ≈ y) :
    IGame.sqrt x ≈ IGame.sqrt y := by
  obtain hx | hx := Classical.em (0 < x)
  · have hy : 0 < y := hx.trans_le he.1
    haveI := (sqrt_main hx).1
    haveI := (sqrt_main hy).1
    rw [← Surreal.mk_eq_mk]
    have h1 := Surreal.mk_eq_mk.2 (sqrt_main hx).2.2
    have h2 := Surreal.mk_eq_mk.2 (sqrt_main hy).2.2
    rw [Surreal.mk_mul] at h1 h2
    have hxy : Surreal.mk x = Surreal.mk y := Surreal.mk_eq_mk.2 he
    have hsq : Surreal.mk (IGame.sqrt x) * Surreal.mk (IGame.sqrt x) =
        Surreal.mk (IGame.sqrt y) * Surreal.mk (IGame.sqrt y) := by
      rw [h1, h2, hxy]
    exact (mul_self_inj (mk_pos_of (sqrt_main hx).2.1).le
      (mk_pos_of (sqrt_main hy).2.1).le).1 hsq
  · have hy : ¬ 0 < y := fun hy ↦ hx (hy.trans_le he.2)
    rw [sqrt_of_not_pos hx, sqrt_of_not_pos hy]

end Numeric

end IGame

/-! ### The square root on surreal numbers -/

namespace Surreal

open IGame

/-- **The square root of a surreal number.** For `0 ≤ x` it is the unique nonnegative
surreal with `sqrt x ^ 2 = x` (see `Surreal.sq_sqrt` and `Surreal.sqrt_eq_of_sq_eq`);
for `x < 0` it takes the junk value `0`.

Constructed via Bach's recursive option-generation on games (`IGame.sqrt`). -/
noncomputable def sqrt : Surreal → Surreal :=
  Quotient.map (fun x ↦ ⟨IGame.sqrt x.1, Numeric.sqrt x.1⟩) fun _ _ ↦ Numeric.sqrt_congr

@[simp]
theorem mk_sqrt (x : IGame) [Numeric x] : mk (IGame.sqrt x) = sqrt (mk x) :=
  rfl

theorem sqrt_nonneg (x : Surreal) : 0 ≤ sqrt x := by
  induction x using Quotient.ind with | _ a
  obtain ⟨a, ha⟩ := a
  change 0 ≤ sqrt (mk a)
  rw [← mk_sqrt]
  have h := Numeric.sqrt_nonneg a
  simpa using Surreal.mk_le_mk.2 h

/-- **Exact square roots of surreal numbers**: `(√x)² = x` for every `0 ≤ x`. -/
theorem sq_sqrt {x : Surreal} (hx : 0 ≤ x) : sqrt x ^ 2 = x := by
  induction x using Quotient.ind with | _ a
  obtain ⟨a, ha⟩ := a
  change sqrt (mk a) ^ 2 = mk a at *
  rw [sq, ← mk_sqrt, ← Surreal.mk_mul]
  refine Surreal.mk_eq_mk.2 (Numeric.sqrt_mul_self ?_)
  have hx' : (0 : Surreal) ≤ mk a := hx
  rw [← Surreal.mk_zero] at hx'
  exact Surreal.mk_le_mk.1 hx'

theorem sqrt_of_nonpos {x : Surreal} (hx : x ≤ 0) : sqrt x = 0 := by
  induction x using Quotient.ind with | _ a
  obtain ⟨a, ha⟩ := a
  have hx' : mk a ≤ mk 0 := by simpa using hx
  change sqrt (mk a) = 0
  rw [← mk_sqrt, IGame.sqrt_of_not_pos, Surreal.mk_zero]
  intro h
  have h' : (0 : Surreal) < mk a := by simpa using Surreal.mk_lt_mk.2 h
  exact absurd (h'.trans_le (by simpa using hx')) (lt_irrefl _)

@[simp]
theorem sqrt_zero : sqrt (0 : Surreal) = 0 :=
  sqrt_of_nonpos le_rfl

/-- Uniqueness: the square root is the *only* nonnegative surreal squaring to `x`. -/
theorem sqrt_eq_of_sq_eq {x z : Surreal} (hz : 0 ≤ z) (h : z ^ 2 = x) : sqrt x = z := by
  have hx : 0 ≤ x := h ▸ sq_nonneg z
  have h1 : sqrt x ^ 2 = z ^ 2 := by rw [sq_sqrt hx, h]
  rw [sq, sq] at h1
  exact (mul_self_inj (sqrt_nonneg x) hz).1 h1

@[simp]
theorem sqrt_one : sqrt (1 : Surreal) = 1 :=
  sqrt_eq_of_sq_eq zero_le_one (one_pow 2)

theorem sqrt_sq {x : Surreal} (hx : 0 ≤ x) : sqrt (x ^ 2) = x :=
  sqrt_eq_of_sq_eq hx rfl

theorem sqrt_pos {x : Surreal} (hx : 0 < x) : 0 < sqrt x := by
  rcases (sqrt_nonneg x).eq_or_gt with h | h
  · exfalso
    have := sq_sqrt hx.le
    rw [← h, ← this] at hx
    simp at hx
  · exact h

theorem sqrt_eq_zero_iff {x : Surreal} (hx : 0 ≤ x) : sqrt x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have := sq_sqrt hx
    rw [h] at this
    simpa using this.symm
  · rintro rfl
    exact sqrt_zero

/-- The square root is multiplicative on nonnegative surreals. -/
theorem sqrt_mul {x y : Surreal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    sqrt (x * y) = sqrt x * sqrt y :=
  sqrt_eq_of_sq_eq (mul_nonneg (sqrt_nonneg x) (sqrt_nonneg y))
    (by rw [mul_pow, sq_sqrt hx, sq_sqrt hy])

theorem sqrt_inv {x : Surreal} (hx : 0 ≤ x) : sqrt x⁻¹ = (sqrt x)⁻¹ :=
  sqrt_eq_of_sq_eq (inv_nonneg.2 (sqrt_nonneg x)) (by rw [← inv_pow, sq_sqrt hx])

theorem sqrt_lt_sqrt {x y : Surreal} (hx : 0 ≤ x) (hxy : x < y) : sqrt x < sqrt y := by
  rw [← mul_self_lt_mul_self_iff (sqrt_nonneg x) (sqrt_nonneg y), ← sq, ← sq,
    sq_sqrt hx, sq_sqrt (hx.trans hxy.le)]
  exact hxy

theorem sqrt_le_sqrt {x y : Surreal} (hx : 0 ≤ x) (hxy : x ≤ y) : sqrt x ≤ sqrt y := by
  rw [← mul_self_le_mul_self_iff (sqrt_nonneg x) (sqrt_nonneg y), ← sq, ← sq,
    sq_sqrt hx, sq_sqrt (hx.trans hxy)]
  exact hxy

theorem sqrt_inj {x y : Surreal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    sqrt x = sqrt y ↔ x = y := by
  constructor
  · intro h
    rw [← sq_sqrt hx, ← sq_sqrt hy, h]
  · rintro rfl
    rfl

/-! ### Every nonnegative surreal is a square -/

/-- **Every nonnegative surreal number is a square** — the first defining axiom of a real
closed field, for `No`. (Conway, ONAG; construction of the root due to Clive Bach.) -/
theorem isSquare_of_nonneg {x : Surreal} (hx : 0 ≤ x) : IsSquare x :=
  ⟨sqrt x, by rw [← sq_sqrt hx, sq]⟩

/-- A surreal number is a square iff it is nonnegative. -/
theorem isSquare_iff_nonneg {x : Surreal} : IsSquare x ↔ 0 ≤ x := by
  constructor
  · rintro ⟨r, rfl⟩
    exact mul_self_nonneg r
  · exact isSquare_of_nonneg

end Surreal

end
