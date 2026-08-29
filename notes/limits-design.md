# Design note: limits on the surreals (the road to integration)

*2026-08-29. Status: design; no Lean yet.*

## Where we are

Formalized so far (StandardPart.lean, Derivative.lean, DerivRules.lean): the
finite/infinitesimal trichotomy, the standard-part decomposition, and a complete
differential calculus at real anchor points (polynomials, product/quotient/chain rules),
all via "quantify over every nonzero infinitesimal increment."

The next layer — sequences, series, continuity on intervals, and ultimately integration —
needs a notion of *limit*. This is where naive analysis on No famously breaks, and the
design decision here determines everything downstream.

## The obstruction: No has gaps that sequences fall into

The ω-indexed sequence `1/n` has **no limit in No**: every positive real is eventually
above it, but every positive infinitesimal is below *all* of its terms. The sequence
converges to the *gap* between the infinitesimals and the positive reals — a location
that is not a surreal number. (Conway calls these gaps; they are the reason No is not
Cauchy complete and why Rubinstein-Salzedo–Swaminathan restrict their analysis to
sequences of transfinite length and special function classes.)

So a limit operator with codomain `Surreal` is inevitably partial. Fighting this is a
mistake; the design should make the partiality structural.

## Proposal: limits live in `Cut`, calculus happens where they are surreal

The CombinatorialGames library already has the right codomain:
`CombinatorialGames/Surreal/Cut.lean` defines `Cut` (as a concept lattice over `<`),
which is a **complete linear order** into which the surreals embed. Cuts are to No what
Dedekind completion is to ℚ — gaps included as first-class citizens.

Plan:

1. `limsup` / `liminf` of any family `f : ι → Surreal` along a filter (or just of an
   ordinal-indexed sequence along tails) as `⨅ tails, ⨆ …` **computed in `Cut`**, where
   the complete-lattice structure makes them total.
2. `CutTendsto f l c : Prop` — liminf = limsup = c. Total, well-behaved, no partiality.
3. `Tendsto f l (L : Surreal)` := `CutTendsto f l (toCut L)` — the *surreal-valued*
   special case. All calculus theorems restrict to this case.
4. The `1/n` example becomes a theorem, not an embarrassment: its cut-limit is the
   infinitesimal gap, which is provably not in the image of `toCut`.

Payoffs:
- Monotone convergence is nearly free (complete lattice).
- The standard-part machinery slots in: for a sequence of reals-cast values, the
  cut-limit is surreal iff the classical limit exists, and they agree — a bridge
  theorem to mathlib's `Filter.Tendsto` over ℝ.
- Integration à la Riemann can be *defined* as a cut (sup of lower sums / inf of upper
  sums in `Cut`), with "integrable" meaning the two cuts coincide at a surreal. This is
  exactly the shape of the Conway–Kruskal–Norton problem, restated in a total codomain —
  and where Costin–Ehrlich–Friedman's obstruction (the genetic integral of `exp` giving
  the wrong value) can be examined formally.

## Open questions before writing Lean

- Which index shape first: `Ordinal`-indexed sequences with tail filters, or general
  `Filter ι`? (Leaning: general filters, restricted lemmas for ordinal tails — reuses
  mathlib's filter library wholesale.)
- Does CG's `Cut` API have `toCut`, `Monotone`/`GaloisConnection` lemmas, and the sup/inf
  characterizations we need, or do we contribute those upstream first? (Audit next
  session; `Cut.lean` is 724 lines and looked rich.)
- Interaction with `SurrealHahnSeries`: transfinite series `Σ rᵢ ω^(aᵢ)` should be the
  flagship convergent sequences once the maintainer's Hahn-series evaluation lands —
  our limit notion should be checked against it for compatibility.

## Non-goals (for now)

- Cauchy completeness (false), metric structure (none), measure theory (premature).
- Racing the CombinatorialGames maintainer on Conway normal form.
