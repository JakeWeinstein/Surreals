import Infinity.CanonicalSum

/-!
# Summation of length ω + ω: the first step beyond ω

The Transfinite Summation Theorem (`Infinity.Summation`) sums every strictly dominating
ℕ-indexed series, and `Infinity.CanonicalSum` picks out the canonical (birthday-simplest)
sum `hahnSum`. But genuine Hahn series have *ordinal*-length supports, and the first
genuinely new length is `ω + ω`: a coarse ω-block `t` followed by a fine ω-block `u` whose
every term lives at a strictly finer scale than everything `t` can reach (the separation
hypothesis `hsep : ∀ m n, mk (t m) < mk (u n)`; recall that in `ArchimedeanClass` larger
means smaller magnitude).

**The crux is the stage-ω partial sum.** At finite stages the partial sums are honest
finite sums; at stage `ω` the "sum so far" must be a sum of the whole coarse block — and
it cannot be a limit (`tendstoSurreal_atTop_iff_eventuallyEq` forbids it), so it must be
*chosen*. Hahn sums of `t` are unique only modulo domination by every `t`-term
(`IsHahnSum.mk_sub_le`), i.e. modulo quantities finer than every `t`-scale — and the fine
block's residual conditions live exactly in that blind spot: two legitimate `t`-sums may
differ by a quantity at the scale of `u 0` (the separation hypothesis bounds `u` above the
`t`-classes and bounds the ambiguity above the `t`-classes, but does *not* compare the
two). So the loose definition `∃ x, IsHahnSum t x ∧ IsHahnSum u (z - x)` leaves the value
of the fine block ill-defined. The principled stage-ω partial sum is the **canonical** sum
`hahnSum ht`: it is a genuine function of the series, exactly parallel to the finite
partial sums being genuine surreals. This gives the definition adopted here:

* `IsHahnSum₂ ht u z` : `z - hahnSum ht` is a Hahn sum of the fine block — the block
  decomposition of `z` is well-defined, with fine block exactly `z - hahnSum ht`.
* `hahnSum₂ ht hu := hahnSum ht + hahnSum hu` : the canonical ω+ω sum, with
  `isHahnSum₂_hahnSum₂` and `exists_isHahnSum₂`.
* **The compatibility theorem** `IsHahnSum₂.isHahnSum_coarse`: under separation, every
  ω+ω sum is *also* an honest length-ω Hahn sum of the coarse block — appending a finer
  block disturbs no coarse residual condition. This is why `IsHahnSum t z` is deliberately
  *not* a conjunct of the definition: it is a theorem, not an axiom, of the design.
* Uniqueness `IsHahnSum₂.mk_sub_le`: two ω+ω sums agree modulo every fine term's class —
  hence (`mk_coarse_sub_le`) modulo every coarse term's class as well.
* `birthday_hahnSum₂_le`: the additive birthday bound; whether `hahnSum₂` is the
  birthday-*minimal* ω+ω sum is discussed there and left open.
* **The design iterates**: `IsHahnSum₃`/`hahnSum₃` (length `ω·3`) are defined by applying
  the two-block shape once more, and *all* their theorems fall out of the two-block API in
  one or two lines — evidence that "subtract the canonical sum of the coarse prefix" is
  the right induction step for full ordinal-length Hahn evaluation.
* **Showcase** `isHahnSum₂_geomOmega`: the concrete ω+ω series
  `Σ_{k<ω} ω⁻ᵏ ⌢ Σ_{k<ω} ω^(-ω-k)` — the geometric series followed by its copy pushed
  below all its own scales — has a canonical sum with well-defined blocks, which is
  simultaneously a genuine length-ω sum of its coarse block.
-/

open ArchimedeanClass

noncomputable section

namespace Surreal

/-! ### Domination calculus helper

Private in `Infinity.Summation`, reproved locally: a class below both summands' classes is
below the sum's class (the `min_le_mk_add` pincer, non-strict form). -/

private theorem le_mk_add {c : ArchimedeanClass Surreal} {a b : Surreal}
    (ha : c ≤ ArchimedeanClass.mk a) (hb : c ≤ ArchimedeanClass.mk b) :
    c ≤ ArchimedeanClass.mk (a + b) :=
  le_trans (le_min ha hb) (ArchimedeanClass.min_le_mk_add ..)

/-! ### The two-block summation predicate -/

/-- `z` is a **Hahn sum of length `ω + ω`** of the series "`t` then `u`": the residual of
`z` against the canonical sum of the coarse block is a Hahn sum of the fine block.

**Design.** The alternative `∃ x, IsHahnSum t x ∧ IsHahnSum u (z - x)` is rejected: by
`IsHahnSum.mk_sub_le`, `t`-sums float freely at every scale finer than all `t`-terms, which
is precisely where `u` lives, so the truth of `IsHahnSum u (z - x)` genuinely depends on
the choice of `x` and the existential would leave the fine block's value ill-defined. The
canonical sum `hahnSum ht` is the principled stage-`ω` partial sum — the unique
birthday-simplest one — and pinning it makes the block decomposition of `z` well-defined.
The coarse conditions `IsHahnSum t z` are deliberately not a conjunct: under the
separation hypothesis they follow (`IsHahnSum₂.isHahnSum_coarse`), so including them would
only burden every construction with a redundant proof obligation. -/
def IsHahnSum₂ {t : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (u : ℕ → Surreal) (z : Surreal) : Prop :=
  IsHahnSum u (z - hahnSum ht)

theorem isHahnSum₂_iff {t u : ℕ → Surreal}
    {ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))} {z : Surreal} :
    IsHahnSum₂ ht u z ↔ IsHahnSum u (z - hahnSum ht) :=
  Iff.rfl

/-- The fine block of an `ω + ω` sum: the residual against the canonical coarse sum is a
Hahn sum of `u`. (Definitional; provided for dot-notation.) -/
theorem IsHahnSum₂.isHahnSum_fine {t u : ℕ → Surreal}
    {ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))} {z : Surreal}
    (hz : IsHahnSum₂ ht u z) : IsHahnSum u (z - hahnSum ht) :=
  hz

/-! ### The canonical `ω + ω` sum and existence -/

/-- **The canonical `ω + ω` sum**: the canonical sum of the coarse block plus the canonical
sum of the fine block. Compositional by construction: its fine block is exactly the
canonical fine sum (`isHahnSum₂_hahnSum₂`). -/
def hahnSum₂ {t u : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1))) : Surreal :=
  hahnSum ht + hahnSum hu

/-- The canonical `ω + ω` sum is an `ω + ω` sum. -/
theorem isHahnSum₂_hahnSum₂ {t u : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1))) :
    IsHahnSum₂ ht u (hahnSum₂ ht hu) := by
  show IsHahnSum u (hahnSum ht + hahnSum hu - hahnSum ht)
  have hcancel : hahnSum ht + hahnSum hu - hahnSum ht = hahnSum hu := by ring
  rw [hcancel]
  exact isHahnSum_hahnSum hu

/-- **Existence of `ω + ω` sums**: any two strictly dominating blocks admit a Hahn sum of
length `ω + ω`. (Separation is not even needed for bare existence — only for the sum to
relate to the coarse block, see `IsHahnSum₂.isHahnSum_coarse`.) -/
theorem exists_isHahnSum₂ {t u : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1))) :
    ∃ z, IsHahnSum₂ ht u z :=
  ⟨hahnSum₂ ht hu, isHahnSum₂_hahnSum₂ ht hu⟩

/-! ### The compatibility theorem -/

/-- **The compatibility theorem**: under separation (every fine term strictly finer than
every coarse term), an `ω + ω` sum is *also* an honest length-`ω` Hahn sum of the coarse
block. Appending a block below all the coarse scales disturbs no coarse residual
condition: the `n`-th coarse residual splits as
`(hahnSum ht - partialSum t n) + (z - hahnSum ht)`, the first piece dominated by `t n`
since the canonical sum sums, the second finer than *every* coarse scale since it is a
Hahn sum of the fine block; the `min_le_mk_add` pincer combines them. -/
theorem IsHahnSum₂.isHahnSum_coarse {t u : ℕ → Surreal}
    {ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))}
    (hsep : ∀ m n, ArchimedeanClass.mk (t m) < ArchimedeanClass.mk (u n))
    {z : Surreal} (hz : IsHahnSum₂ ht u z) : IsHahnSum t z := by
  intro n
  have h0 := hz.isHahnSum_fine 0
  simp only [partialSum_zero, sub_zero] at h0
  have hfine : ArchimedeanClass.mk (t n) ≤ ArchimedeanClass.mk (z - hahnSum ht) :=
    ((hsep n 0).trans_le h0).le
  have hsplit : z - partialSum t n = (hahnSum ht - partialSum t n) + (z - hahnSum ht) := by
    ring
  rw [hsplit]
  exact le_mk_add (isHahnSum_hahnSum ht n) hfine

/-- The canonical `ω + ω` sum is a genuine length-`ω` Hahn sum of its coarse block: the
concrete instance of compatibility promised by the design. -/
theorem isHahnSum_hahnSum₂ {t u : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (hsep : ∀ m n, ArchimedeanClass.mk (t m) < ArchimedeanClass.mk (u n)) :
    IsHahnSum t (hahnSum₂ ht hu) :=
  (isHahnSum₂_hahnSum₂ ht hu).isHahnSum_coarse hsep

/-! ### Uniqueness modulo the finest scales -/

/-- **Uniqueness**: two `ω + ω` sums agree modulo every *fine* term's class — the exact
analogue of `IsHahnSum.mk_sub_le` one length further out. -/
theorem IsHahnSum₂.mk_sub_le {t u : ℕ → Surreal}
    {ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))}
    {z₁ z₂ : Surreal} (h₁ : IsHahnSum₂ ht u z₁) (h₂ : IsHahnSum₂ ht u z₂) (n : ℕ) :
    ArchimedeanClass.mk (u n) ≤ ArchimedeanClass.mk (z₁ - z₂) := by
  have h := IsHahnSum.mk_sub_le h₁.isHahnSum_fine h₂.isHahnSum_fine n
  have hcancel : z₁ - hahnSum ht - (z₂ - hahnSum ht) = z₁ - z₂ := by ring
  rwa [hcancel] at h

/-- Under separation, two `ω + ω` sums agree modulo every *coarse* term's class as well —
strictly sharper than the length-`ω` uniqueness for the coarse block alone. -/
theorem IsHahnSum₂.mk_coarse_sub_le {t u : ℕ → Surreal}
    {ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))}
    (hsep : ∀ m n, ArchimedeanClass.mk (t m) < ArchimedeanClass.mk (u n))
    {z₁ z₂ : Surreal} (h₁ : IsHahnSum₂ ht u z₁) (h₂ : IsHahnSum₂ ht u z₂) (m : ℕ) :
    ArchimedeanClass.mk (t m) ≤ ArchimedeanClass.mk (z₁ - z₂) :=
  ((hsep m 0).trans_le (h₁.mk_sub_le h₂ 0)).le

/-! ### Birthday bound

`hahnSum₂` satisfies the additive birthday bound below. Whether it is the
birthday-*minimal* `ω + ω` sum is open here: the set of `ω + ω` sums is the translate by
`hahnSum ht` of the interval of fine-block sums, and while `hahnSum hu` is the simplest
element of that interval (`birthday_hahnSum_le`), simplicity is not translation-equivariant
— the simplest element of `hahnSum ht + [interval]` need not be `hahnSum ht +` (simplest
element of the interval); e.g. translating `(-1, 1) ∋ 0` by `1/2` gives `(-1/2, 3/2)`,
whose simplest element is still `0`, not `1/2`. Proving or refuting minimality would need
a translation/simplicity interaction lemma for `Cut.simplestBtwn` (or a birthday
computation for a concrete pair of blocks); neither is in the library. We keep the
compositional definition regardless: "the fine block of the canonical sum is the canonical
fine sum" is the property that iterates to longer lengths (see `IsHahnSum₃` below), and a
birthday-minimal variant can always be added later as `simplestBtwn` of the translated
band. -/

theorem birthday_hahnSum₂_le {t u : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1))) :
    (hahnSum₂ ht hu).birthday ≤ (hahnSum ht).birthday + (hahnSum hu).birthday :=
  birthday_add_le _ _

/-! ### Three blocks: the design iterates

Length `ω·3` is obtained by applying the two-block shape once more: subtract the canonical
sum of the coarsest block, and require the remainder to be an `ω + ω` sum of the remaining
two. Every theorem below is one or two lines of the two-block API — the definition
composes, which is the real test of the design. -/

/-- `z` is a **Hahn sum of length `ω·3`** of "`t` then `u` then `v`": the residual against
the canonical sum of the coarsest block is an `ω + ω` sum of the two finer blocks.
Unfolding twice: `z - hahnSum ht - hahnSum hu` is a Hahn sum of `v`. -/
def IsHahnSum₃ {t u : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (v : ℕ → Surreal) (z : Surreal) : Prop :=
  IsHahnSum₂ hu v (z - hahnSum ht)

/-- The canonical `ω·3` sum. -/
def hahnSum₃ {t u v : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (hv : ∀ n, ArchimedeanClass.mk (v n) < ArchimedeanClass.mk (v (n + 1))) : Surreal :=
  hahnSum ht + hahnSum₂ hu hv

/-- The canonical `ω·3` sum is an `ω·3` sum. -/
theorem isHahnSum₃_hahnSum₃ {t u v : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (hv : ∀ n, ArchimedeanClass.mk (v n) < ArchimedeanClass.mk (v (n + 1))) :
    IsHahnSum₃ ht hu v (hahnSum₃ ht hu hv) := by
  show IsHahnSum₂ hu v (hahnSum ht + hahnSum₂ hu hv - hahnSum ht)
  have hcancel : hahnSum ht + hahnSum₂ hu hv - hahnSum ht = hahnSum₂ hu hv := by ring
  rw [hcancel]
  exact isHahnSum₂_hahnSum₂ hu hv

/-- Existence of `ω·3` sums. -/
theorem exists_isHahnSum₃ {t u v : ℕ → Surreal}
    (ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1)))
    (hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1)))
    (hv : ∀ n, ArchimedeanClass.mk (v n) < ArchimedeanClass.mk (v (n + 1))) :
    ∃ z, IsHahnSum₃ ht hu v z :=
  ⟨hahnSum₃ ht hu hv, isHahnSum₃_hahnSum₃ ht hu hv⟩

/-- Middle-block compatibility: under separation of the two finer blocks, the residual of
an `ω·3` sum against the canonical coarsest sum is an honest length-`ω` sum of the middle
block. -/
theorem IsHahnSum₃.isHahnSum_mid {t u v : ℕ → Surreal}
    {ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))}
    {hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1))}
    (hsep_uv : ∀ m n, ArchimedeanClass.mk (u m) < ArchimedeanClass.mk (v n))
    {z : Surreal} (hz : IsHahnSum₃ ht hu v z) : IsHahnSum u (z - hahnSum ht) :=
  IsHahnSum₂.isHahnSum_coarse hsep_uv hz

/-- Coarse compatibility for `ω·3`: an `ω·3` sum is also an honest length-`ω` sum of its
coarsest block — two applications of the two-block compatibility theorem, using that
`IsHahnSum u (z - hahnSum ht)` *is* `IsHahnSum₂ ht u z` definitionally. -/
theorem IsHahnSum₃.isHahnSum_coarse {t u v : ℕ → Surreal}
    {ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))}
    {hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1))}
    (hsep_tu : ∀ m n, ArchimedeanClass.mk (t m) < ArchimedeanClass.mk (u n))
    (hsep_uv : ∀ m n, ArchimedeanClass.mk (u m) < ArchimedeanClass.mk (v n))
    {z : Surreal} (hz : IsHahnSum₃ ht hu v z) : IsHahnSum t z :=
  IsHahnSum₂.isHahnSum_coarse hsep_tu (hz.isHahnSum_mid hsep_uv)

/-- Uniqueness for `ω·3` sums: agreement modulo every finest term's class. -/
theorem IsHahnSum₃.mk_sub_le {t u v : ℕ → Surreal}
    {ht : ∀ n, ArchimedeanClass.mk (t n) < ArchimedeanClass.mk (t (n + 1))}
    {hu : ∀ n, ArchimedeanClass.mk (u n) < ArchimedeanClass.mk (u (n + 1))}
    {z₁ z₂ : Surreal} (h₁ : IsHahnSum₃ ht hu v z₁) (h₂ : IsHahnSum₃ ht hu v z₂) (n : ℕ) :
    ArchimedeanClass.mk (v n) ≤ ArchimedeanClass.mk (z₁ - z₂) := by
  have h := IsHahnSum₂.mk_sub_le h₁ h₂ n
  have hcancel : z₁ - hahnSum ht - (z₂ - hahnSum ht) = z₁ - z₂ := by ring
  rwa [hcancel] at h

/-! ### Showcase: `Σ_{k<ω} ω⁻ᵏ` followed by `Σ_{k<ω} ω^(-ω-k)`

A concrete `ω + ω` series: the geometric series in `ω⁻¹` (the flagship of
`Infinity.Series`), followed by its own copy pushed below every scale it can name —
`ω^(-ω) · ω⁻ᵏ`. Everything is wpow arithmetic via `archimedeanClassMk_wpow_strictAnti`;
the separation boils down to `m < ω`. -/

/-- The coarse block: `k ↦ ω⁻ᵏ`, as `ω`-powers. -/
def geomOmega (k : ℕ) : Surreal :=
  ω^ (-(k : Surreal))

/-- The fine block: `k ↦ ω^(-ω-k)`, the geometric series pushed below all its own
scales. -/
def geomOmegaShifted (k : ℕ) : Surreal :=
  ω^ (-(ω^ (1 : Surreal)) - (k : Surreal))

/-- The fine block really is `ω^(-ω)` times the coarse block. -/
theorem geomOmegaShifted_eq (k : ℕ) :
    geomOmegaShifted k = ω^ (-(ω^ (1 : Surreal))) * geomOmega k := by
  show ω^ (-(ω^ (1 : Surreal)) - (k : Surreal)) =
    ω^ (-(ω^ (1 : Surreal))) * ω^ (-(k : Surreal))
  rw [sub_eq_add_neg, wpow_add]

/-- The coarse block is strictly dominating. -/
theorem geomOmega_strict_dominating (k : ℕ) :
    ArchimedeanClass.mk (geomOmega k) < ArchimedeanClass.mk (geomOmega (k + 1)) :=
  archimedeanClassMk_wpow_strictAnti (neg_lt_neg (Nat.cast_lt.2 (Nat.lt_succ_self k)))

/-- The fine block is strictly dominating. -/
theorem geomOmegaShifted_strict_dominating (k : ℕ) :
    ArchimedeanClass.mk (geomOmegaShifted k) <
      ArchimedeanClass.mk (geomOmegaShifted (k + 1)) :=
  archimedeanClassMk_wpow_strictAnti
    (sub_lt_sub_left (Nat.cast_lt.2 (Nat.lt_succ_self k)) _)

private theorem mk_natCast_of_ne_zero' {m : ℕ} (hm : m ≠ 0) :
    ArchimedeanClass.mk ((m : ℕ) : Surreal) = 0 := by
  apply mk_eq_zero_of_stdPart_ne_zero
  rw [ArchimedeanClass.stdPart_natCast]
  exact_mod_cast hm

private theorem mk_wpow_one_neg' : ArchimedeanClass.mk (ω^ (1 : Surreal)) < 0 := by
  have h := archimedeanClassMk_wpow_strictAnti (one_pos : (0 : Surreal) < 1)
  simpa [wpow_zero, ArchimedeanClass.mk_one] using h

private theorem natCast_lt_wpow_one' (m : ℕ) : ((m : ℕ) : Surreal) < ω^ (1 : Surreal) := by
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · rw [Nat.cast_zero]
    exact wpow_pos _
  · have h1 : ArchimedeanClass.mk (ω^ (1 : Surreal)) <
        ArchimedeanClass.mk ((m : ℕ) : Surreal) := by
      rw [mk_natCast_of_ne_zero' hm.ne']
      exact mk_wpow_one_neg'
    have h2 := abs_lt_abs_of_mk_lt h1
    rwa [abs_of_nonneg (Nat.cast_nonneg m), wpow_abs] at h2

/-- **Separation**: every fine term is strictly finer than every coarse term — because
every natural sits below `ω`. This is what makes "coarse then fine" a legitimate `ω + ω`
series. -/
theorem geomOmega_sep (m n : ℕ) :
    ArchimedeanClass.mk (geomOmega m) < ArchimedeanClass.mk (geomOmegaShifted n) := by
  refine archimedeanClassMk_wpow_strictAnti ?_
  have h1 : ((m : ℕ) : Surreal) < ω^ (1 : Surreal) + ((n : ℕ) : Surreal) :=
    (natCast_lt_wpow_one' m).trans_le (le_add_of_nonneg_right (Nat.cast_nonneg n))
  linarith

/-- **The showcase, part 1**: the concrete `ω + ω` series `Σ ω⁻ᵏ ⌢ Σ ω^(-ω-k)` has an
`ω + ω` sum — the canonical one, with well-defined blocks. -/
theorem isHahnSum₂_geomOmega :
    IsHahnSum₂ geomOmega_strict_dominating geomOmegaShifted
      (hahnSum₂ geomOmega_strict_dominating geomOmegaShifted_strict_dominating) :=
  isHahnSum₂_hahnSum₂ geomOmega_strict_dominating geomOmegaShifted_strict_dominating

/-- **The showcase, part 2**: that same `ω + ω` sum is simultaneously an honest length-`ω`
Hahn sum of the geometric series — the compatibility theorem in the concrete instance. -/
theorem isHahnSum_geomOmega_hahnSum₂ :
    IsHahnSum geomOmega
      (hahnSum₂ geomOmega_strict_dominating geomOmegaShifted_strict_dominating) :=
  (isHahnSum₂_hahnSum₂ geomOmega_strict_dominating
    geomOmegaShifted_strict_dominating).isHahnSum_coarse geomOmega_sep

end Surreal
