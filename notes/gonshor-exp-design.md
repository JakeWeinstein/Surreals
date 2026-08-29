# Gonshor's exponential on infinite surreals: design note

*2026-08-29. Written before `Infinity/GonshorExp.lean`; the definitional choices below are
the actual research content. Sources: Gonshor, «An Introduction to the Theory of Surreal
Numbers», ch. 10 (based on Kruskal's unpublished ideas); the precise statements are quoted
from the local survey PDF (Mantova–Matusinski, «Surreal numbers with derivation, Hardy
fields and transseries», §2.3, Theorems 2.15–2.16, which cites Gonshor Thms 10.1–10.17).*

## 1. What Gonshor proves (verified against the survey, §2.3)

Write `E_n(x) := Σ_{k≤n} x^k/k!` for the partial sums of the exponential series.

**The genetic definition** (Gonshor 10.1–10.9; survey Thm 2.15). For every surreal `a`,

```
exp a = !{ 0,  exp(aᴸ)·E_n(a − aᴸ),  exp(aᴿ)·E_{2n+1}(a − aᴿ)
         |  exp(aᴿ)/E_n(aᴿ − a),  exp(aᴸ)/E_{2n+1}(aᴸ − a) }
```

over all `n ∈ ℕ`, where on each side only the `n` with `E_{2n+1}(·) > 0` are admitted.
This is a recursion over the options of (a representative of) `a`; uniformity — that
cofinal representations give the same value — is part of Gonshor's theorem. The resulting
`exp : (No, +, <) → (No^{>0}, ·, <)` is an ordered-group isomorphism, restricting to the
real exponential on ℝ and to the Maclaurin series on infinitesimals.

**The three-part factorization.** Every surreal is uniquely `x = J + r + ε` with `J`
purely infinite (Conway normal form with only positive exponents), `r ∈ ℝ`,
`ε` infinitesimal; then `exp x = exp J · e^r · exp ε`, the last factor being the series.
This repo already owns the third factor (`expInf`, `Infinity/CanonicalSum.lean`) and a
parallel agent owns the middle assembly on finite arguments. **This file's territory is
`exp J`.**

**The purely infinite case** (Gonshor 10.8–10.13; survey Thm 2.16):
`ω^No = exp(J)` (monomials = exponentials of purely infinite numbers), and for
`a = Σ_{i<λ} ω^{a_i}·r_i` purely infinite (all `a_i > 0`),

```
exp a = ω^y   with   y = Σ_{i<λ} ω^{g(a_i)}·r_i ,
```

where `g : No^{>0} → No` is itself genetically defined. Gonshor 10.17: `g(a) = a`
whenever `1 ≤ a ≤ β < ε₀` (or `ε_α + ω ≤ a ≤ β < ε_{α+1}`) for ordinals `β`; `g` deviates
from the identity only near the generalized ε-numbers (fixed points of the ω-map).

**Flagship value** (survey, explicit computation): with `ω = !{n | ∅}`,

```
exp ω = !{ 0, e^n·E_n(ω − n) | ∅ }        (the right options vanish because
      = !{ ω^n | ∅ }   (mutual cofinality)  E_{2n+1}(n − ω) < 0 for every n)
      = ω^ω .
```

Similarly `exp ε₀ = ω^{ω^{ε₀+1}} ≠ ε₀` (so exp has no fixed points, unlike the ω-map).

## 2. The definitional decision

Three candidate routes were considered.

**(A) Full genetic recursion on `IGame`.** Faithful, but the well-definedness proof is the
whole of Gonshor ch. 10 up front: the recursion's value must be shown numeric, which needs
the order-compatibility of all option pairs, which needs exp's homomorphism and growth
laws *inside the induction*. This is the multi-month route (compare: CG's `wpow`, with far
simpler options, is ~400 lines of delicate simultaneous induction). Not for one session.

**(B) Define `exp J := ω^J` on the `g = id` class and prove homomorphism laws.** Cheap —
and worthless: the laws are `wpow_add`/`wpow_lt_wpow`, already in CG, and calling this
"Gonshor's exp" would be exactly the kind of grandiose relabeling this repo has been
criticized for. The identity `exp ω = ω^ω` would be true *by definition* — vacuous.

**(C) Verify the genetic recursion's evaluation, step by step.** The honest content of
`exp ω = ω^ω` is: *Gonshor's option list at `ω`, seeded with the already-known values
`exp n = e^n` on the left options, evaluates to `ω^ω`*. That is a concrete, kernel-checkable
cut computation — the survey's displayed derivation — and it generalizes: at every "limit"
argument `a = !{range s | ∅}` (no right options, `a − s n` infinite), Gonshor's formula
reduces to a left-options-only cut, and its value is a power of `ω` whose exponent is
itself a cut assembled from `wlog` data of the seeds. **Route (C) is chosen.**

## 3. The main theorem (route C, general form)

For `a` any surreal, `s v : ℕ → Surreal` with `v n > 0`, `s n < a`, `a − s n` infinite:

```
!{ {0} ∪ { v n · E_k(a − s n) : n k : ℕ } | ∅ }
    = ω^ !{ { wlog (v n) + k • wlog (a − s n) : n k : ℕ } | ∅ }
```

Interpretation: if `a = !{range s | ∅}` and `v n` is the (already computed) value
`exp (s n)`, the LHS is exactly Gonshor's genetic formula at `a` (the `0` option included;
right options empty because `aᴿ = ∅` and every `E_{2n+1}(s n − a) < 0` — proved
separately), and the RHS exhibits the value as `ω^(cut of exponents)` — the mechanism by
which Gonshor's `g`-function emerges. The theorem itself is representation-free: it never
uses what `a` is, only the domination structure of the options.

Proof skeleton (all at the `Surreal` level):
1. `E_k` asymptotics: for infinite `y`, `mk (E_k y) = k • mk y` (dominant-term calculus,
   `mk_add_eq_mk_left`); positivity for `y > 0`; negativity of odd partial sums for
   negative infinite `y` (kills Gonshor's right options at limit arguments).
2. Classes of options: `mk (v n · E_k(a − s n)) = mk (ω^(c n + k • d n))` where
   `c n := wlog (v n)`, `d n := wlog (a − s n) > 0` (via `archimedeanClassMk_wpow_wlog`).
3. Mutual cofinality: each `v n·E_k` is dominated by `ω^(c n + (k+1)•d n)` (a RHS option,
   `r = 1`), and each dyadic multiple `r·ω^(c n + k•d n)` by `v n·E_{k+1}` — strict class
   inequalities plus `abs_lt_abs_of_mk_lt`.
4. Two bridge lemmas (new, generally useful):
   - **cofinal-equality**: `!{A | ∅} = !{B | ∅}` for mutually ≤-cofinal `A, B`
     (descends `Fits.equiv_of_forall_moves` / `le_iff_forall_lf` through `toGame`);
   - **`wpow` of a cut**: `ω^ !{A | ∅} = !{ {0} ∪ {r·ω^x : r ∈ Dyadic^{>0}, x ∈ A} | ∅ }`
     (pushes CG's `wpow_def` through `Surreal.mk_ofSets`).

## 4. The flagship corollary

With `s n := n`, `v n := (e^n : ℝ) ↪ No`: `c n = 0` (`wlog` of a nonzero real),
`d n = 1` (`wlog (ω − n) = wlog ω = 1`), so the exponent cut is `!{ℕ | ∅} = ω` and

```
theorem gonshorExp_omega :
  !{ {0} ∪ { e^n · E_k(ω − n) : n k } | ∅ } = ω^ω^1   -- i.e. exp ω = ω^ω
```

using a third small bridge, `ω^1 = !{range Nat.cast | ∅}` (from `wpow_def` at `1` plus
cofinal-equality between the positive dyadics and ℕ). Together with the vanishing of the
right options this is precisely the survey's computation of `exp ω`, every step checked.

**Calibration.** What is proved: the evaluation of Gonshor's recursion at `ω` (and at any
limit-type argument), given its values on earlier arguments as inputs. What is *not*
proved: the global well-definedness/uniformity of the recursion, or `exp` as a total
function on No — those remain the genuine long-term target (route A). No claim of a total
`exp` should appear in any commit message.

## 5. Follow-ups this unlocks (in value order)

1. Iterate the step: `exp (ω·2) = ω^{ω·2}` from seeds `exp(ω+n) = ω^ω·e^n`
   (needs `ω·2 = !{ω+n | ∅}`, an `IGame.add` computation) — evidence the step theorem
   composes along Gonshor's induction. Similarly `exp ε₀ = ω^{ω^{ε₀+1}}` — the first
   `g ≠ id` value — if a workable `ε₀` representation is built (ordinal bridge needed).
2. The dual (`log` at limit cuts) via Gonshor's `log(ω^b)` formula — same machinery.
3. Combining with the finite-argument agent's `exp`: a piecewise-total `exp` on
   {finite} ∪ {g=id purely infinite monomial sums}, with the functional equation where
   both sides are defined — the assembly milestone.
4. Route A proper: the genetic recursion as a `Surreal`-valued function with a
   simultaneous-induction well-definedness proof — the multi-session mountain.
