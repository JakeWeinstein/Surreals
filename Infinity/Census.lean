import CombinatorialGames.Surreal.Dyadic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# The dyadic tree: heights, children, and interleaving

The finite skeleton of Conway's day-by-day census (ONAG, ch. 2): the dyadic rationals are
generated day by day, each day's newcomers sitting strictly between (or beyond) the numbers
already born. This file formalizes that skeleton as pure `Dyadic` combinatorics, with no
surreal numbers in sight:

* `Dyadic.hgt` — the *height* of a dyadic in the birth tree: `|n|` for an integer `n`, and
  `max (hgt lower) (hgt upper) + 1` otherwise (mirroring the `Dyadic.toIGame` recursion).
* `Dyadic.upChild` / `Dyadic.downChild` — the two children of a node: `x ± 1/(2 den x)`,
  with `lower (upChild x) = x` and `upper (upChild x) = upper x`.
* `Dyadic.exists_hgt_btwn` — **the interleaving theorem**: strictly between any two dyadics
  there is one of height at most `max (hgt a) (hgt b) + 1`. This is the engine that lets a
  census argument choose a *simple* candidate between the options of a game.
* `Dyadic.exists_hgt_above` / `exists_hgt_below` — the one-sided versions.
* `Dyadic.finite_setOf_hgt_le` — each height-ball is finite (each day's census is finite).

These feed the day-`ω + n` censuses: the surreals born by day `ω + n` in an infinitesimal
halo are exactly the translates by `r·ω⁻¹` with `r` of bounded height, and the candidate
selection in the census induction is precisely `exists_hgt_btwn`.
-/

namespace Dyadic

/-! ### The height of a dyadic in the birth tree -/

/-- The height of a dyadic rational in the birth tree: `|n|` for an integer `n`, one more
than the maximal height of the two parents `lower x`, `upper x` otherwise. This mirrors the
recursion defining `Dyadic.toIGame`, and is an upper-bound analogue of the classical
birthday of a dyadic surreal. -/
def hgt (x : Dyadic) : ℕ :=
  if _ : x.den = 1 then x.num.natAbs else max (hgt (lower x)) (hgt (upper x)) + 1
termination_by x.den
decreasing_by dyadic_wf

theorem hgt_of_den_eq_one {x : Dyadic} (h : x.den = 1) : hgt x = x.num.natAbs := by
  rw [hgt, dif_pos h]

theorem hgt_of_den_ne_one {x : Dyadic} (h : x.den ≠ 1) :
    hgt x = max (hgt (lower x)) (hgt (upper x)) + 1 := by
  rw [hgt, dif_neg h]

@[simp]
theorem hgt_intCast (n : ℤ) : hgt (n : Dyadic) = n.natAbs := by
  rw [hgt_of_den_eq_one (den_intCast n)]
  simp

@[simp]
theorem hgt_natCast (n : ℕ) : hgt (n : Dyadic) = n := by
  have h : ((n : ℤ) : Dyadic) = (n : Dyadic) := by push_cast; rfl
  rw [← h, hgt_intCast]
  simp

@[simp]
theorem hgt_zero : hgt (0 : Dyadic) = 0 := by
  simpa using hgt_natCast 0

@[simp]
theorem hgt_one : hgt (1 : Dyadic) = 1 := by
  simpa using hgt_natCast 1

@[simp]
theorem hgt_neg (x : Dyadic) : hgt (-x) = hgt x := by
  by_cases h : x.den = 1
  · rw [hgt_of_den_eq_one h, hgt_of_den_eq_one (by rw [den_neg]; exact h), num_neg,
      Int.natAbs_neg]
  · have hn : (-x).den ≠ 1 := by rw [den_neg]; exact h
    rw [hgt_of_den_ne_one h, hgt_of_den_ne_one hn, lower_neg, upper_neg, hgt_neg, hgt_neg,
      max_comm]
termination_by x.den
decreasing_by all_goals first
  | exact den_upper_lt h
  | exact den_lower_lt h

theorem hgt_lower_lt {x : Dyadic} (h : x.den ≠ 1) : hgt (lower x) < hgt x := by
  rw [hgt_of_den_ne_one h]
  exact Nat.lt_succ_of_le (le_max_left _ _)

theorem hgt_upper_lt {x : Dyadic} (h : x.den ≠ 1) : hgt (upper x) < hgt x := by
  rw [hgt_of_den_ne_one h]
  exact Nat.lt_succ_of_le (le_max_right _ _)

theorem hgt_pos_of_ne_zero {x : Dyadic} (h : x ≠ 0) : 0 < hgt x := by
  by_cases hd : x.den = 1
  · rw [hgt_of_den_eq_one hd]
    rw [Int.natAbs_pos]
    intro h0
    apply h
    ext
    have : x.toRat.num = 0 := h0
    rw [Rat.zero_iff_num_zero.2 this]
    simp
  · rw [hgt_of_den_ne_one hd]
    exact Nat.succ_pos _

/-! ### The two children of a dyadic -/

private theorem two_mul_den_mem_powers (x : Dyadic) : 2 * x.den ∈ Submonoid.powers 2 :=
  mul_mem (Submonoid.mem_powers 2) x.den_mem_powers

/-- The upper child of `x` in the birth tree: `x + 1/(2 den x)`, the simplest new dyadic
strictly between `x` and `upper x`. -/
def upChild (x : Dyadic) : Dyadic :=
  Dyadic.mkRat (2 * x.num + 1) (two_mul_den_mem_powers x)

/-- The lower child of `x` in the birth tree: `x - 1/(2 den x)`. -/
def downChild (x : Dyadic) : Dyadic :=
  Dyadic.mkRat (2 * x.num - 1) (two_mul_den_mem_powers x)

private theorem coprime_odd_two_mul_den (x : Dyadic) (m : ℤ) (hm : Odd m) :
    Nat.Coprime m.natAbs (2 * x.den) := by
  obtain ⟨e, he⟩ := x.den_mem_powers
  have h2 : 2 * x.den = 2 ^ (e + 1) := by rw [← he]; ring
  rw [h2]
  refine Nat.Coprime.pow_right _ ?_
  have hodd : Odd m.natAbs := Int.natAbs_odd.2 hm
  have hnd : ¬ (2 ∣ m.natAbs) := by
    intro hdvd
    obtain ⟨k, hk⟩ := hodd
    omega
  exact Nat.coprime_comm.1 (Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.2 hnd)

private theorem den_two_pos (x : Dyadic) : (0 : ℕ) < 2 * x.den :=
  Nat.mul_pos two_pos x.den_pos

theorem coe_upChild (x : Dyadic) : (upChild x : ℚ) = (2 * x.num + 1) / (2 * x.den) := by
  show (upChild x).toRat = _
  rw [upChild, coe_mkRat, Rat.mkRat_eq_div]
  norm_num

theorem coe_downChild (x : Dyadic) : (downChild x : ℚ) = (2 * x.num - 1) / (2 * x.den) := by
  show (downChild x).toRat = _
  rw [downChild, coe_mkRat, Rat.mkRat_eq_div]
  norm_num

private theorem coe_eq_num_div_den (x : Dyadic) : (x : ℚ) = (x.num : ℚ) / (x.den : ℚ) :=
  (Rat.num_div_den x.toRat).symm

private theorem den_cast_pos (x : Dyadic) : (0 : ℚ) < (x.den : ℚ) := by
  exact_mod_cast x.den_pos

theorem lt_upChild (x : Dyadic) : x < upChild x := by
  rw [← Dyadic.coe_lt_coe, coe_upChild, coe_eq_num_div_den]
  have hd := den_cast_pos x
  rw [div_lt_div_iff₀ hd (by positivity)]
  nlinarith

theorem upChild_lt_upper (x : Dyadic) : upChild x < upper x := by
  rw [← Dyadic.coe_lt_coe, coe_upChild, coe_upper]
  have hd := den_cast_pos x
  rw [coe_eq_num_div_den, div_lt_iff₀ (by positivity)]
  field_simp
  nlinarith

theorem den_upChild (x : Dyadic) : (upChild x).den = 2 * x.den := by
  have hne : 2 * x.den ≠ 0 := (den_two_pos x).ne'
  have hcop : Nat.gcd (2 * x.num + 1).natAbs (2 * x.den) = 1 :=
    coprime_odd_two_mul_den x _ ⟨x.num, by ring⟩
  show (upChild x).toRat.den = 2 * x.den
  rw [upChild, coe_mkRat, ← Rat.normalize_eq_mkRat hne, Rat.normalize_eq]
  show 2 * x.den / (2 * x.num + 1).natAbs.gcd (2 * x.den) = 2 * x.den
  rw [hcop, Nat.div_one]

theorem den_upChild_ne_one (x : Dyadic) : (upChild x).den ≠ 1 := by
  rw [den_upChild]
  have := x.den_pos
  omega

theorem lower_upChild (x : Dyadic) : lower (upChild x) = x := by
  ext
  rw [show ((lower (upChild x) : Dyadic) : ℚ) = _ from coe_lower _, den_upChild, coe_upChild,
    coe_eq_num_div_den]
  have hd := den_cast_pos x
  field_simp
  push_cast
  ring

theorem upper_upChild (x : Dyadic) : upper (upChild x) = upper x := by
  ext
  rw [show ((upper (upChild x) : Dyadic) : ℚ) = _ from coe_upper _, den_upChild, coe_upper,
    coe_upChild, coe_eq_num_div_den]
  have hd := den_cast_pos x
  field_simp
  push_cast
  ring

theorem hgt_upChild (x : Dyadic) : hgt (upChild x) = max (hgt x) (hgt (upper x)) + 1 := by
  rw [hgt_of_den_ne_one (den_upChild_ne_one x), lower_upChild, upper_upChild]

theorem downChild_eq_neg (x : Dyadic) : downChild x = -upChild (-x) := by
  ext
  rw [coe_neg, coe_downChild, coe_upChild, den_neg, num_neg]
  push_cast
  ring

theorem downChild_lt (x : Dyadic) : downChild x < x := by
  rw [downChild_eq_neg, neg_lt]
  exact lt_upChild (-x)

theorem lower_lt_downChild (x : Dyadic) : lower x < downChild x := by
  rw [downChild_eq_neg, lt_neg]
  have h := upChild_lt_upper (-x)
  rwa [upper_neg] at h

theorem hgt_downChild (x : Dyadic) : hgt (downChild x) = max (hgt (lower x)) (hgt x) + 1 := by
  rw [downChild_eq_neg, hgt_neg, hgt_upChild, upper_neg, hgt_neg, hgt_neg, max_comm]

/-! ### Integer representation at denominator one -/

theorem eq_intCast_of_den_eq_one {x : Dyadic} (h : x.den = 1) : x = (x.num : Dyadic) := by
  ext
  rw [coe_intCast, coe_eq_num_div_den, h]
  norm_num

private theorem coe_eq_num_of_den_eq_one {x : Dyadic} (h : x.den = 1) :
    (x : ℚ) = (x.num : ℚ) := by
  rw [coe_eq_num_div_den, h]
  norm_num

private theorem lt_intCast_of_num_lt {x : Dyadic} {m : ℤ} (h : x.den = 1)
    (hm : x.num < m) : x < (m : Dyadic) := by
  rw [← Dyadic.coe_lt_coe, coe_eq_num_of_den_eq_one h, coe_intCast]
  exact_mod_cast hm

private theorem intCast_lt_of_lt_num {x : Dyadic} {m : ℤ} (h : x.den = 1)
    (hm : m < x.num) : (m : Dyadic) < x := by
  rw [← Dyadic.coe_lt_coe, coe_eq_num_of_den_eq_one h, coe_intCast]
  exact_mod_cast hm

private theorem num_lt_num_of_den_one {a b : Dyadic} (ha : a.den = 1) (hb : b.den = 1)
    (hab : a < b) : a.num < b.num := by
  rw [← Dyadic.coe_lt_coe, coe_eq_num_of_den_eq_one ha, coe_eq_num_of_den_eq_one hb] at hab
  exact_mod_cast hab

/-! ### The interleaving theorem -/

/-- **The interleaving theorem for the dyadic birth tree**: strictly between any two dyadics
`a < b` there is a dyadic of height at most `max (hgt a) (hgt b) + 1`. This is the finite
combinatorial heart of Conway's census: the candidate a census argument inserts between the
options of a game can always be chosen at most one day younger than the options. -/
theorem exists_hgt_btwn (a b : Dyadic) (hab : a < b) :
    ∃ t : Dyadic, a < t ∧ t < b ∧ hgt t ≤ max (hgt a) (hgt b) + 1 := by
  by_cases hb1 : b.den = 1
  · by_cases ha1 : a.den = 1
    · -- both integers
      have hnum := num_lt_num_of_den_one ha1 hb1 hab
      by_cases hadj : a.num + 1 = b.num
      · -- adjacent integers: take the upper child of `a`
        have hub : upper a = b := by
          rw [upper_eq_of_den_eq_one ha1, eq_intCast_of_den_eq_one hb1, ← hadj]
          push_cast
          ring
        refine ⟨upChild a, lt_upChild a, ?_, ?_⟩
        · rw [← hub]
          exact upChild_lt_upper a
        · rw [hgt_upChild, hub]
      · -- non-adjacent integers: an integer fits
        rcases le_or_gt 0 a.num with h0a | h0a
        · refine ⟨((a.num + 1 : ℤ) : Dyadic), lt_intCast_of_num_lt ha1 (by omega),
            intCast_lt_of_lt_num hb1 (by omega), ?_⟩
          rw [hgt_intCast, hgt_of_den_eq_one ha1]
          refine le_trans ?_ (Nat.add_le_add_right (le_max_left _ _) 1)
          omega
        · rcases le_or_gt b.num 0 with hb0 | hb0
          · refine ⟨((b.num - 1 : ℤ) : Dyadic), lt_intCast_of_num_lt ha1 (by omega),
              intCast_lt_of_lt_num hb1 (by omega), ?_⟩
            rw [hgt_intCast, hgt_of_den_eq_one hb1]
            refine le_trans ?_ (Nat.add_le_add_right (le_max_right _ _) 1)
            omega
          · have h0 : (0 : Dyadic) = ((0 : ℤ) : Dyadic) := by push_cast; rfl
            refine ⟨0, ?_, ?_, by simp⟩
            · rw [h0]
              exact lt_intCast_of_num_lt ha1 (by omega)
            · rw [h0]
              exact intCast_lt_of_lt_num hb1 (by omega)
    · -- `a` strictly deeper than `b` is impossible here; this branch has `b` an integer
      -- and `a` not: `a` is deeper, use the upper route
      have hd : b.den ≤ a.den := by
        rw [hb1]
        exact a.one_le_den
      have hup := upper_le_of_lt hd hab
      rcases eq_or_lt_of_le hup with heq | hlt
      · refine ⟨upChild a, lt_upChild a, ?_, ?_⟩
        · rw [← heq]
          exact upChild_lt_upper a
        · rw [hgt_upChild, heq]
      · obtain ⟨t, h1, h2, h3⟩ := exists_hgt_btwn (upper a) b hlt
        refine ⟨t, (lt_upper a).trans h1, h2, ?_⟩
        refine h3.trans (Nat.add_le_add_right (max_le ?_ (le_max_right _ _)) 1)
        exact le_max_of_le_left (hgt_upper_lt ha1).le
  · by_cases hd : b.den ≤ a.den
    · -- `a` at least as deep as `b`, and `a` is not an integer
      have ha1 : a.den ≠ 1 := by
        intro h
        exact hb1 (le_antisymm (h ▸ hd) b.one_le_den)
      have hup := upper_le_of_lt hd hab
      rcases eq_or_lt_of_le hup with heq | hlt
      · refine ⟨upChild a, lt_upChild a, ?_, ?_⟩
        · rw [← heq]
          exact upChild_lt_upper a
        · rw [hgt_upChild, heq]
      · obtain ⟨t, h1, h2, h3⟩ := exists_hgt_btwn (upper a) b hlt
        refine ⟨t, (lt_upper a).trans h1, h2, ?_⟩
        refine h3.trans (Nat.add_le_add_right (max_le ?_ (le_max_right _ _)) 1)
        exact le_max_of_le_left (hgt_upper_lt ha1).le
    · -- `b` strictly deeper than `a`: use the lower route
      have hd' : a.den ≤ b.den := (not_le.1 hd).le
      have hlo := le_lower_of_lt hd' hab
      rcases eq_or_lt_of_le hlo with heq | hlt
      · refine ⟨downChild b, ?_, downChild_lt b, ?_⟩
        · rw [heq]
          exact lower_lt_downChild b
        · rw [hgt_downChild, ← heq]
      · obtain ⟨t, h1, h2, h3⟩ := exists_hgt_btwn a (lower b) hlt
        refine ⟨t, h1, h2.trans (lower_lt b), ?_⟩
        refine h3.trans (Nat.add_le_add_right (max_le (le_max_left _ _) ?_) 1)
        exact le_max_of_le_right (hgt_lower_lt hb1).le
termination_by hgt a + hgt b
decreasing_by
  · have := hgt_upper_lt ha1
    omega
  · have := hgt_upper_lt ha1
    omega
  · have := hgt_lower_lt hb1
    omega

/-- One-sided interleaving, upward: above any dyadic there is one at most one day younger. -/
theorem exists_hgt_above (a : Dyadic) : ∃ t : Dyadic, a < t ∧ hgt t ≤ hgt a + 1 := by
  by_cases h : a.den = 1
  · refine ⟨((a.num + 1 : ℤ) : Dyadic), lt_intCast_of_num_lt h (by omega), ?_⟩
    rw [hgt_intCast, hgt_of_den_eq_one h]
    omega
  · exact ⟨upper a, lt_upper a, (hgt_upper_lt h).le.trans (Nat.le_succ _)⟩

/-- One-sided interleaving, downward. -/
theorem exists_hgt_below (a : Dyadic) : ∃ t : Dyadic, t < a ∧ hgt t ≤ hgt a + 1 := by
  obtain ⟨t, h1, h2⟩ := exists_hgt_above (-a)
  refine ⟨-t, ?_, ?_⟩
  · rw [neg_lt]
    exact h1
  · rw [hgt_neg]
    rwa [hgt_neg] at h2

/-! ### Finiteness of the height balls -/

private theorem hgt_le_zero_subset : {x : Dyadic | hgt x ≤ 0} ⊆ {0} := by
  intro x hx
  rw [Set.mem_ofPred_eq, Nat.le_zero] at hx
  by_cases h : x.den = 1
  · rw [hgt_of_den_eq_one h, Int.natAbs_eq_zero] at hx
    rw [Set.mem_singleton_iff, eq_intCast_of_den_eq_one h, hx]
    push_cast
    rfl
  · rw [hgt_of_den_ne_one h] at hx
    omega

/-- **Each day's census is finite**: the set of dyadics of height at most `n` is finite. -/
theorem finite_setOf_hgt_le (n : ℕ) : {x : Dyadic | hgt x ≤ n}.Finite := by
  induction n with
  | zero => exact (Set.finite_singleton 0).subset hgt_le_zero_subset
  | succ n ih =>
    have hsub : {x : Dyadic | hgt x ≤ n + 1} ⊆
        (fun m : ℤ ↦ (m : Dyadic)) '' {m : ℤ | m.natAbs ≤ n + 1} ∪
          {x : Dyadic | x.den ≠ 1 ∧ hgt (lower x) ≤ n ∧ hgt (upper x) ≤ n} := by
      intro x hx
      rw [Set.mem_ofPred_eq] at hx
      by_cases h : x.den = 1
      · left
        refine ⟨x.num, ?_, (eq_intCast_of_den_eq_one h).symm⟩
        rwa [Set.mem_ofPred_eq, ← hgt_of_den_eq_one h]
      · right
        rw [hgt_of_den_ne_one h] at hx
        have hx' : max (hgt (lower x)) (hgt (upper x)) ≤ n := by omega
        exact ⟨h, le_trans (le_max_left _ _) hx', le_trans (le_max_right _ _) hx'⟩
    refine Set.Finite.subset (Set.Finite.union ?_ ?_) hsub
    · refine Set.Finite.image _ (Set.Finite.subset (Set.finite_Icc (-(n + 1) : ℤ) (n + 1)) ?_)
      intro m hm
      rw [Set.mem_ofPred_eq] at hm
      rw [Set.mem_Icc]
      omega
    · refine Set.Finite.of_finite_image (f := fun x : Dyadic ↦ (lower x, upper x)) ?_ ?_
      · refine Set.Finite.subset (Set.Finite.prod ih ih) ?_
        rintro ⟨u, v⟩ ⟨x, ⟨_, hxl, hxu⟩, hx⟩
        rw [Prod.ext_iff] at hx
        obtain ⟨hu, hv⟩ := hx
        exact ⟨by rw [← hu]; exact hxl, by rw [← hv]; exact hxu⟩
      · rintro x - y - hxy
        have hl : lower x = lower y := congrArg Prod.fst hxy
        have hu : upper x = upper y := congrArg Prod.snd hxy
        have hl' : (x : ℚ) - (x.den : ℚ)⁻¹ = (y : ℚ) - (y.den : ℚ)⁻¹ := by
          rw [← coe_lower, ← coe_lower, hl]
        have hu' : (x : ℚ) + (x.den : ℚ)⁻¹ = (y : ℚ) + (y.den : ℚ)⁻¹ := by
          rw [← coe_upper, ← coe_upper, hu]
        ext
        linarith

end Dyadic
