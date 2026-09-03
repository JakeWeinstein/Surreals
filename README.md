# Surreals

## DISCLAIMER

With the exception of these few diaclaimer paragraphs, everything in this repository was written by Claude. This project stemmed from a long-running curiosity I've had about dealing with infinity. I kept asking myself: why can't we do math with infinity? Shouldn't there be a way to formalize algebra and calculus done on infinities and infinitesimals? So I looked into it, and I found the surreal numbers. My goal here is to in some way advance our knowledge of this very natural numerical system and hopefully discover some use for analysis on the surreals. 

Claude seems well equipped to deal with at least the beginning of this problem. Formalizing the existing work in lean was simple, and I think we've made some progress already in terms of developing a kind of surreal analysis. This seems like an ideal field to try to push the boundaries of AI-driven math research. Many of the ideas already exist and formalizing and expanding upon those ideas, drawing connections across math disciplines, seems like an ideal task for us to try to tackle with LLMs.

 If you stumble across this repo, hopefully it will be useful to you in some way. Please don't hesitate to reach out to me if you have questions. My contact information is on my Github profile.

**Machine-checked infinitesimal calculus on Conway's surreal numbers.**

This repository contains, to our knowledge, the first formal (Lean 4) development of
analysis on the surreal number field **No** — including **Conway's Normal Form Theorem and
the ordered-field isomorphism `No ≅ ℝ((ω^No))`** (`Infinity/HahnProduct.lean`) —: the standard-part decomposition, a complete
differential calculus via infinitesimals, a limit theory valued in cuts, the obstruction
theorems that explain why naive analysis fails on No, and a theory of transfinite
summation under which infinite series have sums *without converging*.

Everything is proved from first principles on top of [mathlib] and the
[CombinatorialGames] library and checked by the Lean kernel. There are **no `sorry`s**.

## Headline results

| Result | Statement (informal) | Where |
|---|---|---|
| Standard part decomposition | Every finite surreal is a *unique* real plus an infinitesimal; `stdPart` is a section of `ℝ ↪ No` | [`Infinity/StandardPart.lean`](Infinity/StandardPart.lean) |
| Derivative via infinitesimals | `st((p(x+ε) − p(x))/ε) = p′(x)` for real polynomials, real `x`, *any* nonzero infinitesimal `ε` — e.g. `st(((3 + 1/ω)² − 9)·ω) = 6` | [`Infinity/Derivative.lean`](Infinity/Derivative.lean) |
| Differential calculus toolkit | Sum, product, quotient, and **chain rules**; uniqueness of the derivative (witnessed by `ε = 1/ω`) | [`Infinity/DerivRules.lean`](Infinity/DerivRules.lean) |
| Cut-valued limits | `limsup`/`liminf` of surreal sequences always exist in the complete lattice of cuts; sandwich characterization of convergence | [`Infinity/Limits.lean`](Infinity/Limits.lean) |
| **Gap theorem** | `1/n` converges to *no* surreal — it converges to a gap of No | [`Infinity/Limits.lean`](Infinity/Limits.lean) |
| **Eventual constancy** | An ℕ-indexed sequence of surreals converges **iff it is eventually constant** (via countable coinitiality: `{0 ∣ z₀, z₁, …}`) | [`Infinity/Limits.lean`](Infinity/Limits.lean) |
| **Summation without convergence** | `Σ_{k<ω} ω⁻ᵏ` has the canonical sum `ω/(ω−1)` under domination semantics (`IsHahnSum`), yet its partial sums converge to nothing | [`Infinity/Series.lean`](Infinity/Series.lean) |
| **Transfinite Summation Theorem** | *Every* strictly dominating series has a Hahn sum — the Conway cut `!{sₙ−2\|tₙ\| ∣ sₙ+2\|tₙ\|}`; corollary: every ω-power series `Σ rₖ ω⁻ᵏ` sums | [`Infinity/Summation.lean`](Infinity/Summation.lean) |
| Derivatives at all finite points | `st(p(x)) = p(st x)`, and the derivative at any finite surreal anchor factors through the standard part | [`Infinity/FiniteDeriv.lean`](Infinity/FiniteDeriv.lean) |
| **Riemann collapse** | The classical ε–δ Riemann integral is *vacuous* on No: no partition has infinitesimal mesh, so **every surreal is a Riemann integral of every function** | [`Infinity/Riemann.lean`](Infinity/Riemann.lean) |
| **`e^(1/ω)` exists** | The exponential series `Σ εᵏ/k!` at any nonzero infinitesimal is strictly dominating, hence has a transfinite sum | [`Infinity/Exp.lean`](Infinity/Exp.lean) |
| **The integral + FTC** | `∫ₐᵇ p` for polynomials with *arbitrary surreal endpoints*; **FTC I & II**; uniqueness (any FTC-compatible operator is this one); linearity; **`∫₀^ω x dx = ω²/2`** as a theorem; term-by-term integration of transfinite series | [`Infinity/Integral.lean`](Infinity/Integral.lean) |
| **The surreal-point derivative** | `HasDerivS`: derivative at *every* surreal point with surreal values (`O(ε²)` error over all infinitesimal increments); unique; every `Surreal[X]` polynomial differentiable everywhere | [`Infinity/GeneralDeriv.lean`](Infinity/GeneralDeriv.lean) |
| **The Galaxy Kernel Theorem** | The galaxy indicator (0 on finite, 1 on infinite) has derivative **zero everywhere** yet isn't constant — so **no FTC integral exists for arbitrary surreal functions**: the Conway–Kruskal–Norton difficulty, as a theorem | [`Infinity/GeneralDeriv.lean`](Infinity/GeneralDeriv.lean) |
| **The full surreal integral** | `integralS` on `Surreal[X]` with surreal endpoints: **FTC I at every surreal point**, FTC II, uniqueness, linearity, compatibility with the real-coefficient integral | [`Infinity/IntegralS.lean`](Infinity/IntegralS.lean) |
| **The exponential functional equation** | Cauchy product: for positive infinitesimals, `expInf ε · expInf δ` is a Hahn sum of the series at `ε+δ` — the multiplicative law modulo domination; exact equality = a new open question (is birthday-minimality multiplicative?) | [`Infinity/ExpMul.lean`](Infinity/ExpMul.lean) |
| **The Fractal Kernel Theorem** | The kernel question, *settled*: the micro-galaxy indicator has derivative **zero at every point** (uniform constant `C = ω^ω`) yet jumps between two points an **infinitesimal** apart — zero-derivative functions vary at every scale; antiderivative increments are ill-defined even over infinitesimal intervals | [`Infinity/MicroKernel.lean`](Infinity/MicroKernel.lean) |
| **The canonical sum + `exp` as a function** | `hahnSum`: **the** birthday-simplest transfinite sum (the Hahn sums are exactly the surreals between two explicit cuts; `simplestBtwn` picks the canonical one); `expInf`: the exponential on nonzero infinitesimals as an honest function, with `st(exp ε) = 1` and `exp ε = 1 + ε + O(ε²)` | [`Infinity/CanonicalSum.lean`](Infinity/CanonicalSum.lean) |

### The fleet results (five parallel provers, one afternoon)

| Result | Statement (informal) | Where |
|---|---|---|
| **Kernel Separation Theorem** | For *every* `a ≠ b` there is a zero-derivative function with `F a ≠ F b` — the derivative on No carries no global information; antiderivative increments ill-defined over every nondegenerate interval | [`Infinity/KernelSeparation.lean`](Infinity/KernelSeparation.lean) |
| **General Cauchy Product** | `IsHahnSum.mul` under a single no-cancellation floor; exactness-at-⊤ lever; exp law re-derived; `Σ(n+1)ω⁻ⁿ = (ω/(ω−1))²` | [`Infinity/CauchyProduct.lean`](Infinity/CauchyProduct.lean) |
| **Square roots** | Exact roots of every `r·ω^x`; canonical `√(1+u)` with square correct below every scale; **every positive surreal has a square root modulo sub-all-scales error** — the doorstep of real-closedness | [`Infinity/Sqrt.lean`](Infinity/Sqrt.lean) |
| **ω+ω summation** | Transfinite summation past length ω: two-block sums via canonicity, composing to ω·3 in lines — the road to full Hahn evaluation | [`Infinity/OrdinalSum.lean`](Infinity/OrdinalSum.lean) |
| **Simplicity uniqueness + exact canonical sums** | The birthday-simplest fit between cuts is *unique* (Conway's simplicity theorem, sign-expansion-free); `hahnSum(−t) = −hahnSum t`; first closed-form canonical sums (`= 1`, `= ω`); `birthday ω = ω`; additivity/multiplicativity reduced to sharp birthday inequalities | [`Infinity/BirthdayHahn.lean`](Infinity/BirthdayHahn.lean) |

### Norton's error and the day-ω census

| Result | Statement (informal) | Where |
|---|---|---|
| **Norton's error as a theorem** | The genetic (simplest-fit) value of `∫₀^ω eˣ dx` over the `ω`-lattice option family is the bare monomial `ω^ω = e^ω` — *Norton's famous wrong value*: the cut is blind to the whole finite halo (both `e^ω` and the true `e^ω − 1` fit), and birthday-simplicity selects the monomial. Simplest-fit is structurally not integration | [`Infinity/Norton.lean`](Infinity/Norton.lean) |
| **Form dependence** | The same genetic principle over naturals-only options gives `ω²` — not even the Archimedean class of `e^ω` survives; Conway's "the integral depends on the form" as theorems | [`Infinity/Norton.lean`](Infinity/Norton.lean) |
| **Conway's day-ω census** | A surreal is born by day `ω` **iff** it is a real, `±ω`, or a dyadic neighbour `d ± 1/ω` — as a single kernel-checked `iff`; `birthday (1/ω) = ω`, every real born by day `ω` (the birthday bound left open upstream) | [`Infinity/DayOmega.lean`](Infinity/DayOmega.lean) |
| **The day-ω exp criterion, settled** | A product of exponentials of positive infinitesimals is born by day `ω` iff it equals `1 + 1/ω` exactly — the census leaves no other value; the geometric halo is empty at day `ω` (every Hahn sum of `Σ ω⁻ᵏ` born ≥ `ω+1`) | [`Infinity/DayOmega.lean`](Infinity/DayOmega.lean) |
| **The first exact exponential value** | `exp (log (1 + 1/ω)) = 1 + 1/ω` on **No**: the canonical-sum exponential at the canonical sum of the log series evaluates *exactly* — truncated `exp ∘ log = id` as polynomial divisibility, pushed through the domination calculus; `birthday (exp (log (1+1/ω))) = ω` while the logarithm itself is born ≥ `ω+1`: the exponential can strictly simplify | [`Infinity/ExpLog.lean`](Infinity/ExpLog.lean) |

### The census ladder and the geometric squeeze (2026-08-30, evening session)

| Result | Statement (informal) | Where |
|---|---|---|
| **The dyadic birth tree, formalized** | Heights, children `x ± 1/(2·den x)`, the **interleaving theorem** (between any two dyadics lies one at most one day younger), finiteness of each day's census | [`Infinity/Census.lean`](Infinity/Census.lean) |
| **The halo grid realized** | `a + r·ω⁻¹` is born by day `ω + hgt r` for every real `a` and dyadic `r` (one day sharper over dyadic anchors) — the day-`ω+n` newborns, by parametric order-pinned cofinality | [`Infinity/HaloRealization.lean`](Infinity/HaloRealization.lean) |
| **The uniform census below `ω·2`** | One induction for all days `ω+n` at once: a finite surreal born by day `ω+n` **is** `a + r·ω⁻¹` with `a` its standard part and `hgt r ≤ n+1` (`≤ n` for non-dyadic `a`); as an **iff**; **exact** birthdays for every grid point | [`Infinity/GeometricBirthday.lean`](Infinity/GeometricBirthday.lean) |
| **The geometric halo is empty on `[ω, ω·2)`** | Every Hahn sum of `Σ ω⁻ᵏ` is born at or after day **`ω·2`** — the uniformity theorem replaces the day-by-day censuses in one stroke | [`Infinity/GeometricBirthday.lean`](Infinity/GeometricBirthday.lean) |
| **The day-`ω+1` census** | Born by day `ω+1` **iff** a grid point of height ≤ 1 over a real / ≤ 2 over a dyadic, or `±ω`, `±(ω+1)`, `±(ω−1)`; `birthday (ω ± 1) = ω + 1` exactly | [`Infinity/DayOmegaOne.lean`](Infinity/DayOmegaOne.lean) |
| **The halving lemma + `ω`-power birthdays** | `G · ½ ≈ !{0 ∣ G}` for chain games (order-pinned halving); `birthday (ω⁻ᵏ·2⁻ʲ) ≤ ω·k + j` with **no** multiplicative birthday bounds (open upstream) | [`Infinity/GeometricUpper.lean`](Infinity/GeometricUpper.lean) |
| **The geometric squeeze** | The canonical sum `hahnSum (Σ ω⁻ᵏ)` is born in the window **`[ω·2, ω²]`** | [`Infinity/GeometricUpper.lean`](Infinity/GeometricUpper.lean) |
| **`ω/(ω−1)` born by day `ω²`** | The Conway **inverse game** breaks the order-pinning deadlock: every inverse-option word sits at distance exactly `ω^k` from `(ω−1)⁻¹` (the word-class invariant), giving mutual cofinality with the partial-sum cut; **the halo-minimality conjecture is now equivalent to the single inequality `birthday (ω/(ω−1)) ≤ birthday (hahnSum Σ ω⁻ᵏ)`**, both sides in `[ω·2, ω²]` | [`Infinity/InverseBirthday.lean`](Infinity/InverseBirthday.lean) |

### The tube census and the close (2026-08-30, night session)

| Result | Statement (informal) | Where |
|---|---|---|
| **The scale-parametric engine** | The order-pinning grid realization, parametric in the scale pair: for any `(V, W)` with `W = {0 ∣ q·V}` and a `V`-separated anchor, the dyadic `W`-grid over the anchor costs one day per birth-tree step over any base ordinal | [`Infinity/ScaleRealization.lean`](Infinity/ScaleRealization.lean) |
| **Partial sums priced exactly** | The level pack: anchors for every partial sum `Sₘ` with `birthday (S_{B+1} + t·ω^{−(B+1)}) ≤ ω·(B+1) + (hgt t − 1)`; in particular `birthday Sₙ = ω·(n−1)` for `n ≥ 2` (exactness in `GeometricClose`) | [`Infinity/TubeCensus.lean`](Infinity/TubeCensus.lean) |
| **THE TUBE CENSUS** | The uniform census below `ω²`, all blocks at once — and the discovery that no two-scale census is needed: in block `[ω·(B+1), ω·(B+2))` the *tube* around `ω/(ω−1)` (distance strictly finer than class `ω^{−B}`) contains **only** the dyadic grid `S_{B+1} + t·ω^{−(B+1)}` over the moving partial-sum anchor. **Tube theorem**: the only surreal born before day `ω·(B+2)` at distance finer than class `ω^{−(B+1)}` is `S_{B+2}` | [`Infinity/TubeCensus.lean`](Infinity/TubeCensus.lean) |
| **The geometric halo is empty below `ω²`** | Every Hahn sum of `Σ ω⁻ᵏ` is born at or after day `ω·ω`: Hahn sums are strictly finer than every scale, but the tube below `ω²` holds only partial sums, which are not | [`Infinity/GeometricClose.lean`](Infinity/GeometricClose.lean) |
| **`birthday (ω/(ω−1)) = ω·ω` exactly** | The Conway-inverse upper bound meets the halo-emptiness lower bound | [`Infinity/GeometricClose.lean`](Infinity/GeometricClose.lean) |
| **THE CANONICAL GEOMETRIC SUM** | **`hahnSum (Σ_{k<ω} ω⁻ᵏ) = ω/(ω−1)`** — the repo's oldest conjecture, closed: birthday-simplicity *selects* the true value; the first computed value of the canonical transfinite summation operator on a series with no exact finite form, born exactly on day `ω·ω`. Any Hahn sum born by day `ω·ω` **is** `ω/(ω−1)` | [`Infinity/GeometricClose.lean`](Infinity/GeometricClose.lean) |
| **THE `ω²`-HARDNESS THEOREM** | The tube census generalized to **every** strictly dominating series `Σ cₖ·ω⁻ᵏ` with nonzero dyadic coefficients, around *any* of its Hahn sums (which can serve as its own tube center): **no monomial series has any consistent sum born below day `ω²`** — transfinite summation is uniformly expensive, whatever the coefficients | [`Infinity/MonomialCensus.lean`](Infinity/MonomialCensus.lean) |

### The first exact functional equation instance (2026-08-31)

| Result | Statement (informal) | Where |
|---|---|---|
| **THE FIRST EXACT FE INSTANCE** | **`exp(logΩ + logΩ) = exp(logΩ)·exp(logΩ)`** — the canonical-sum exponential is multiplicative at `(logΩ, logΩ)`, *exactly*: both sides are `(1+ω⁻¹)² = 1 + 2ω⁻¹ + ω⁻²`. The route: go **up by squaring** (exact field algebra on the banked `exp(log(1+ω⁻¹)) = 1+ω⁻¹`), never down by roots — the Cauchy product supplies the Hahn-sum half for free, and the monomial tube census prices the halo | [`Infinity/ExpFibre.lean`](Infinity/ExpFibre.lean) |
| **The padded census series** | A finite dyadic polynomial is not a Hahn sum of any nonzero-coefficient series — but it **is** a grid point at every level of a *padded* one (`1 + 2ω⁻¹ + ω⁻² + ω⁻³ + ⋯`): the tube around the padded sum polices the polynomial's halo. Every Hahn sum of the exponential series at `logΩ + logΩ` is born at or after day `ω·2` | [`Infinity/ExpFibre.lean`](Infinity/ExpFibre.lean) |
| **The second exact exponential value** | `exp(2·log(1+ω⁻¹)) = 1 + 2ω⁻¹ + ω⁻²` — after `exp(log(1+ω⁻¹)) = 1+ω⁻¹` (day `ω`), the second-ever exact transcendental evaluation, born on day `ω·2` | [`Infinity/ExpFibre.lean`](Infinity/ExpFibre.lean) |
| **Doubling the argument doubles the block** | `birthday (exp(logΩ + logΩ)) = ω·2` **exactly** — the first exact `expInf` birthday beyond day `ω` | [`Infinity/ExpFibre.lean`](Infinity/ExpFibre.lean) |
| **THE FE LADDER** | **`exp(n·logΩ) = (1+ω⁻¹)ⁿ` for every `n ≥ 1`** — the canonical-sum exponential evaluated exactly on the entire lattice `ℕ⁺·logΩ`, by rung-coupled induction: each rung's exact value feeds the next rung's Hahn-sum half through the Cauchy product; the **binomial padded series** `(C(n,0), …, C(n,n), 1, 1, …)` prices each rung. The first exact evaluation of the surreal exponential on an infinite family of arguments | [`Infinity/ExpLadder.lean`](Infinity/ExpLadder.lean) |
| **Every rung priced exactly** | `birthday (exp(n·logΩ)) = ω·n` for every `n ≥ 1` — the exponential of the `n`-fold argument is born on day `ω·n`, uniformly; rung 1 recovers the day-`ω` value | [`Infinity/ExpLadder.lean`](Infinity/ExpLadder.lean) |
| **THE LATTICE FUNCTIONAL EQUATION** | `exp(a + b) = exp(a)·exp(b)` **exactly** for all `a, b ∈ ℕ⁺·logΩ` — infinitely many exact instances of the open multiplicativity question, settled affirmatively at once | [`Infinity/ExpLadder.lean`](Infinity/ExpLadder.lean) |
| **THE EXP∘LOG GRID THEOREM** | **`exp (log (1 + a·ω⁻¹)) = 1 + a·ω⁻¹` for every nonzero dyadic `a`** — the exponential inverts the logarithm on the entire day-`ω` halo grid, for **every** Hahn sum of the log series (the **fibre collapse**: `exp` cannot see which logarithm was chosen); the generic domination half works at *any* nonzero infinitesimal anchor | [`Infinity/ExpLogGrid.lean`](Infinity/ExpLogGrid.lean) |
| **Grid values priced exactly** | `birthday (exp (log (1+a·ω⁻¹))) = ω + (hgt a − 1)` — the exponential's grid values fill the entire block `[ω, ω·2)` rung by rung of the dyadic birth tree | [`Infinity/ExpLogGrid.lean`](Infinity/ExpLogGrid.lean) |
| **THE MIXED FUNCTIONAL EQUATION** | **`exp (log(1+a·ω⁻¹) + log(1+b·ω⁻¹)) = (1+a·ω⁻¹)·(1+b·ω⁻¹)`** for all positive dyadics `a, b` and *any* Hahn sums of the two log series — the FE across **different** anchors, via the pair-padded census series `(1, a+b, ab, 1, 1, …)` | [`Infinity/ExpMixedFE.lean`](Infinity/ExpMixedFE.lean) |

### The moonshot contrast (2026-08-31)

| Result | Statement (informal) | Where |
|---|---|---|
| **`∫₀^ω eˣ dx = e^ω − 1`** | The **forced FTC integral** of the exponential over `[0, ω]` takes the Newton–Leibniz value `ω^ω − 1`: on the integrand class `c·eˣ + P(x)` (rigid across galaxies, as the kernel theorems demand), the fundamental theorem admits **exactly one** integral operator (`integralE_unique`, structural — no kernel constancy needed), FTC I holds with genuine `O(ε²)` surreal-point derivatives at both endpoints, and its value is `e^ω − 1` | [`Infinity/ExpIntegral.lean`](Infinity/ExpIntegral.lean) |
| **The exponential ODE on the lattice** | `exp′ = exp` (`HasDerivS nortonExp x (nortonExp x)`) at every real point *and* every point `ω + r` of the top galaxy — the increment never leaves the galaxy, so the real-point differential equation translates by `ω` and scales by `ω^ω` | [`Infinity/ExpIntegral.lean`](Infinity/ExpIntegral.lean) |
| **NORTON'S OVERSHOOT IS EXACTLY `1`** | `nortonIntegralExp − ∫₀^ω eˣ dx = 1`: the genetic simplest-fit integral exceeds the forced FTC value by precisely the `exp 0` term the cut cannot see. Kruskal's 1970s observation — genetic `e^ω` vs. true `e^ω − 1` — as a single exact kernel-checked equation: **the CKN failure and its repair in one file** | [`Infinity/ExpIntegral.lean`](Infinity/ExpIntegral.lean) |

### The inverse value and the reflection law (2026-08-31, fleet session)

| Result | Statement (informal) | Where |
|---|---|---|
| **THE INVERSE EXPONENTIAL VALUE** | **`exp (−log(1+ω⁻¹)) = (1+ω⁻¹)⁻¹ = ω/(ω+1)`** — the first exact value of the canonical-sum exponential at a **negative** argument, and the first whose series has genuine cancellation. Domination half via the new truncated **reflection identity** `E(X)·E(−X) ≡ 1 (mod Xⁿ)` composed with the banked `exp∘log` divisibility | [`Infinity/InverseValue.lean`](Infinity/InverseValue.lean), [`Infinity/ExpNegLog.lean`](Infinity/ExpNegLog.lean) |
| **THE REFLECTION LAW** | `exp(log(1+ω⁻¹)) · exp(−log(1+ω⁻¹)) = 1` — the multiplicative-inverse identity for the surreal exponential, exact on **No**: the FE program now covers a reflection pair, opening the negative rungs of the lattice | [`Infinity/InverseValue.lean`](Infinity/InverseValue.lean) |
| **THE SECOND CANONICAL SUM** | **`hahnSum (Σ (−1)ᵏ ω⁻ᵏ) = ω/(ω+1)`**, born exactly on day `ω²` — the second computed value of the canonical transfinite summation operator, by the same squeeze as the geometric close | [`Infinity/InverseValue.lean`](Infinity/InverseValue.lean), [`Infinity/AltGeometric.lean`](Infinity/AltGeometric.lean) |
| **Negation explodes the birthday** | `birthday (exp(−logΩ)) = ω·ω` while `birthday (exp(logΩ)) = ω`: negating the argument sends the exponential from day `ω` to a **limit block** — the first exp value priced at day `ω²` | [`Infinity/InverseValue.lean`](Infinity/InverseValue.lean) |
| **The Conway inverse, upgraded** | `birthday ((1+ω⁻¹)⁻¹) ≤ ω²` by inverting the game `1 + ω^{−1}` directly: the inverse recursion's value-`1` word-chain **is** the alternating partial sums (`1 − ω⁻¹·Sₙ = Sₙ₊₁`), flipping sides each step — the two-sided cut comes for free | [`Infinity/AltInverse.lean`](Infinity/AltInverse.lean) |

### The negative grid (2026-08-31, third fleet session)

| Result | Statement (informal) | Where |
|---|---|---|
| **THE NEGATIVE GRID THEOREM** | **`exp (−log (1 + a·ω⁻¹)) = (1 + a·ω⁻¹)⁻¹` for every positive dyadic `a`** and *every* Hahn sum of the log series (fibre-general) — the single inverse value made an infinite family | [`Infinity/NegGridValue.lean`](Infinity/NegGridValue.lean) |
| **THE GRID REFLECTION LAW** | `exp σ · exp (−σ) = 1` across the entire positive-anchor day-`ω` log grid — the multiplicative-inverse identity, exact, grid-wide | [`Infinity/NegGridValue.lean`](Infinity/NegGridValue.lean) |
| **A family of canonical sums** | `hahnSum (Σ (−a)ᵏ ω⁻ᵏ) = (1 + a·ω⁻¹)⁻¹` for every positive dyadic `a`, each born exactly on day `ω²` — the canonical summation operator computed on an infinite family of series | [`Infinity/NegGridValue.lean`](Infinity/NegGridValue.lean), [`Infinity/NegGrid.lean`](Infinity/NegGrid.lean) |
| **Inversion sends the grid to the limit block** | Every negative-grid exponential value is born exactly on day `ω·ω`, while its positive mirror lives in `[ω, ω·2)` | [`Infinity/NegGridValue.lean`](Infinity/NegGridValue.lean) |
| **The general deep-halo trap** | Around *any* Hahn sum of *any* nonzero-dyadic monomial series, anything strictly finer than every scale is born at or after day `ω²` — the identification engine, now fully parametric | [`Infinity/NegGrid.lean`](Infinity/NegGrid.lean) |
| **The gift-horse device** | The Conway-inverse bound `birthday ((1+a·ω⁻¹)⁻¹) ≤ ω²` for all positive dyadic `a`: adjoin a value-`1` left option to the product game `1 + a·ω^{−1}` (a four-line `equiv_of_forall_lf`), and the inverse recursion's word-chain generates the `Σ(−a·ω⁻¹)ᵏ` partial sums straddling the value | [`Infinity/NegGridInverse.lean`](Infinity/NegGridInverse.lean) |
| **The generic negative domination half** | `(1+x)⁻¹` is a Hahn sum of the exponential series at `−σ` for *any* nonzero infinitesimal `x` and *any* Hahn-sum log `σ` — the reflection identity is anchor-free | [`Infinity/ExpNegGrid.lean`](Infinity/ExpNegGrid.lean) |

### The multiplicativity theorem by game cofinality (2026-09-02)

| Result | Statement (informal) | Where |
|---|---|---|
| **The canonical sum is the value of its option game** | `hahnSum t = mk !{sₙ − 2\|tₙ\| ∣ sₙ + 2\|tₙ\|}` — Conway's summation cut, as a game, *is* the birthday-simplest Hahn sum; every Hahn sum fits the game (the next-index estimate `\|w − sₙ\| < 2\|tₙ\|`) | [`Infinity/GameCofinality.lean`](Infinity/GameCofinality.lean) |
| **The identification engine** | To prove `hahnSum t = mk G` it suffices that `mk G` is a Hahn sum and every option of `G` is beaten by an option of the summation game — one application of the simplicity theorem (`Fits.equiv_of_forall_moves`), **no birthday census** | [`Infinity/GameCofinality.lean`](Infinity/GameCofinality.lean) |
| **THE MULTIPLICATIVITY THEOREM** | `hahnSum t · hahnSum u = hahnSum (t ⋆ u)` (Cauchy product) whenever the product scale is cofinal in the term products — the Conway product game's options `P − (x−xᴸ)(y−yᴸ)` are dominated by the product series' options; likewise **additivity** by the sum game | [`Infinity/GameCofinality.lean`](Infinity/GameCofinality.lean) |
| **THE COMPARABLE-CLASS FUNCTIONAL EQUATION** | **`exp(σ + τ) = exp σ · exp τ` for all positive infinitesimals `σ, τ` with comparable Archimedean classes** (neither infinitely finer than the other) — the lattice, grid, and mixed-anchor functional equations of the two preceding days are corollaries; `exp(2σ) = (exp σ)²` for every positive infinitesimal; the day-`ω·2` lattice instance re-derived in one line | [`Infinity/GameCofinality.lean`](Infinity/GameCofinality.lean) |
| **THE MULTIPLICATIVITY DICHOTOMY** | For positive infinitesimals, **`exp(σ + τ) = exp σ · exp τ` if and only if the Archimedean classes of `σ` and `τ` are comparable** (each within a finite power of the other) — the comparable-class functional equation is sharp | [`Infinity/ExpDichotomy.lean`](Infinity/ExpDichotomy.lean) |
| **The blindness theorem** | If `τ` is finer than every power of `σ`, then **`exp(σ + τ) = exp σ`**: the canonical-sum exponential cannot see an infinitely finer perturbation of its argument. Hence `exp` is **not injective**, and the functional equation fails at such pairs (`exp σ · exp τ > exp σ`). Concrete witness: `exp(ω⁻¹ + ω^(−ω)) = exp(ω⁻¹)`. Tool: a congruence lemma — series with equal term classes whose partial sums differ below every term have the same Hahn sums and the same canonical sum | [`Infinity/ExpDichotomy.lean`](Infinity/ExpDichotomy.lean) |
| **Power and root laws** | `exp(n·σ) = (exp σ)ⁿ` and `exp σ = exp(σ/n)ⁿ` for every positive infinitesimal — in particular `exp σ = exp(σ/2)²`, the half-log fibre question of the earlier roadmap, now a one-liner; `exp` is a semigroup homomorphism on every comparability cone | [`Infinity/ExpDichotomy.lean`](Infinity/ExpDichotomy.lean) |
| **The halo game** | `haloGame ε p := !{p − εᴺ ∣ p + εᴺ}` has as value the **birthday-simplest element of the deep halo** of `p` (everything closer to `p` than every power of `ε`); `p` is *halo-simple* iff that value is `p`. **Every real is halo-simple at every scale** (via the day-`ω` census); so are `d ± ω⁻¹` and `1 + a·ω⁻¹`. The identification engine re-targeted at the halo game identifies any game value lying in a halo-simple point's halo | [`Infinity/HaloGame.lean`](Infinity/HaloGame.lean) |
| **THE REFLECTION LAW** | **`exp σ · exp(−σ) = 1` for every nonzero infinitesimal `σ`** (either sign) — the truncated identity `E(X)E(−X) ≡ 1 (mod Xⁿ)` puts the product in the deep halo of `1`, and the product game's options are dominated by the halo game's; hence `exp(−σ) = (exp σ)⁻¹`, `exp σ > 0` always, `exp σ < 1` for negative `σ`, and the **ℤ-lattice law** `exp(n·σ) = (exp σ)ⁿ` for every nonzero integer `n` | [`Infinity/HaloGame.lean`](Infinity/HaloGame.lean) |
| **EXP∘LOG IS HALO SIMPLIFICATION** | For every nonzero infinitesimal `x` and *every* Hahn sum `σ` of the log series at `x`: **`exp σ = haloValue \|x\| (1 + x)`**, the simplest element of the halo of `1 + x`. So `exp(log(1+x)) = 1 + x` **iff `1 + x` is halo-simple** — true on the whole dyadic grid (the grid theorem, read backwards), and **false at `x = ω⁻¹ + ω^(−ω)`**, where `exp(log(1+x)) = 1 + ω⁻¹ ≠ 1 + x` | [`Infinity/HaloGame.lean`](Infinity/HaloGame.lean) |
| **THE SCALE EVALUATION RING HOMOMORPHISM** | For every positive infinitesimal `ε`, evaluation of real formal power series `f ↦ scaleEval ε f` is a **ring homomorphism `PowerSeries ℝ →+* No`** — additive and multiplicative with **no side conditions** (zero coefficients, cancellation, anything): the *scale game* `!{U_N − (\|f_N\|+1)εᴺ ∣ U_N + (\|f_N\|+1)εᴺ}` sees the scale, not the terms, so cofinality is automatic and no no-cancellation floor is needed. Its value is the birthday-simplest *scale sum* (`∀ N, z − U_N ≲ εᴺ`) | [`Infinity/ScaleEval.lean`](Infinity/ScaleEval.lean) |
| **Polynomials, constants, compatibility** | `scaleEval ε p = haloValue ε (p(ε))` for every real polynomial `p` (so `scaleEval ε (C r) = r`, and `scaleEval ε X = ε` iff `ε` is halo-simple); `scaleEval ε f = hahnSum` of `Σ fₖεᵏ` whenever no coefficient vanishes — the canonical-sum semantics **is** formal-power-series semantics at every scale | [`Infinity/ScaleEval.lean`](Infinity/ScaleEval.lean) |
| **`exp` is the image of mathlib's `exp`** | `expInf σ = scaleEval σ (PowerSeries.exp ℝ)`; the reflection law in two lines from `exp_mul_exp_neg_eq_one`; and **the signed functional equation along every scale line**: `exp(r·σ)·exp(s·σ) = exp((r+s)·σ)` for all reals `r, s, r+s ≠ 0` — mixed signs and irrational ratios included, from `exp_mul_exp_eq_exp_add` | [`Infinity/ScaleEval.lean`](Infinity/ScaleEval.lean) |
| **Substitution, rescaling, signed evaluation** | `scaleEval` commutes with power-series substitution (`scaleEval ε (f ∘ g) = scaleEval (scaleEval ε g) f` for `g` of positive order with the expected class), with rescaling (`scaleEval (r·ε) f = scaleEval ε (rescale r f)`), and extends to a signed evaluation `scaleEvalS δ` at infinitesimals of either sign, a ring homomorphism with `scaleEvalS δ exp = exp δ`; the semantics is **blind below its scale**: `scaleEval (ε+δ) f = scaleEval ε f` when `δ` is below every power of `ε` | [`Infinity/ScaleCalculus.lean`](Infinity/ScaleCalculus.lean) |
| **The canonical jet extension is differentiable at every real point** | For every real power series `f` and real `r`, the function `r + δ ↦ scaleEvalS δ f` satisfies `HasDerivS` at `r` with derivative `f₁ = coeff 1 f`, with an explicit real constant; in particular the canonical `exp` has derivative `1` at `0` | [`Infinity/ScaleCalculus.lean`](Infinity/ScaleCalculus.lean) |
| **THE KERNEL EXPONENTIAL THEOREM** | **At every nonzero infinitesimal `σ`, the canonical-sum exponential has derivative exactly `0`, and only `0`: `HasDerivS exp σ d ↔ d = 0`**, so `exp′ = exp` fails at every nonreal infinitesimal point although `exp′ = exp` holds at `0` and `exp` is not constant (`exp σ ≠ exp (σ/2)`). Blindness kills the error along fine increments; a constant above every `σ⁻ᵏ` absorbs the comparable ones. Canonical-sum semantics gives an analytic calculus *exactly on the reals*; beyond them, normal-form semantics is necessary, not merely convenient | [`Infinity/ScaleCalculus.lean`](Infinity/ScaleCalculus.lean) |

### The normal-form chapter opens (2026-09-02, evening)

| Result | Statement (informal) | Where |
|---|---|---|
| **The transfinite canonical sum is a game at every limit stage** | `hahnSumO t γ = mk !{S_β − 2\|t_β\| ∣ S_β + 2\|t_β\|}_{β<γ}` for every limit `γ` (with `S_β` the canonical partial sums), and the identification engine at limit stages | [`Infinity/TransfiniteGame.lean`](Infinity/TransfiniteGame.lean) |
| **THE TRANSFINITE ADDITIVITY THEOREM** | `hahnSumO (t + u) α = hahnSumO t α + hahnSumO u α` at **every ordinal length** `α`, under no cancellation and *mutual class cofinality* below every limit stage — a condition proved necessary by the blindness phenomenon (a block infinitely finer than the other is invisible to the canonical sum) | [`Infinity/TransfiniteGame.lean`](Infinity/TransfiniteGame.lean) |
| **The block theorem (an August question closed)** | `hahnSumO t (ω+ω) = hahnSum (first block) + hahnSum (second block)`: the block-compositional sum *is* birthday-minimal, answering the translation-equivariance question left open in `OrdinalSum`/`NormalForm` | [`Infinity/TransfiniteGame.lean`](Infinity/TransfiniteGame.lean) |
| **Hahn-series evaluation adds on a common support** | `evalHahn (x + y) = evalHahn x + evalHahn y` for the library's `SurrealHahnSeries` with equal supports and no cancellation — the first ring-homomorphism law for Conway's normal-form evaluation | [`Infinity/TransfiniteGame.lean`](Infinity/TransfiniteGame.lean) |
| **Coarse representability** | `CoarseRep X c`: `X` has a numeric game representative all of whose options sit at distance not finer than `c`. Closed under sums and real scaling; limit-stage canonical sums are coarsely representable at their terms' classes; **monomials `r·ω^y` are coarsely representable at `mk (ω^y)`** (via the options of the IGame `ω^ y`); every canonical sum of coarse terms is coarse. Canonical ω-sums are **halo-simple** at any cofinal scale | [`Infinity/Concatenation.lean`](Infinity/Concatenation.lean) |
| **THE CONCATENATION THEOREM** | `hahnSumO t (α+β) = hahnSumO t α + hahnSumO (fun δ ↦ t (α+δ)) β` whenever the first block's value is coarsely representable at the second block's coarsest scale — hence **unconditionally for every normal-form series** `Σ r_ζ·ω^{y_ζ}` split at any ordinal; the ω-shift law `hahnSum t = t₀ + hahnSum (shift)` as the case `α = 1` | [`Infinity/Concatenation.lean`](Infinity/Concatenation.lean) |
| **The boundary** | The coarse hypothesis is necessary: for `t₀ = ω⁻¹ + ω^(−ω)` followed by `ω⁻², ω⁻³, …`, the canonical sum of the whole is **not** `t₀ +` the canonical sum of the rest — the `ω^(−ω)` tail of the first term is invisible to the canonical sum, and `ω⁻¹ + ω^(−ω)` is provably not coarsely representable at scale `ω⁻²` | [`Infinity/Concatenation.lean`](Infinity/Concatenation.lean) |
| **The scaling law** | `hahnSumO (m·t) α = m · hahnSumO t α` at every ordinal length for every coarsely representable factor `m` — in particular every monomial `c·ω^z` and every nonzero real; the product game `G_m × (option game)` with displacements `(m−a)(X−b)` | [`Infinity/HahnMerge.lean`](Infinity/HahnMerge.lean) |
| **THE MERGE THEOREM** | **`evalHahn (x + y) = evalHahn x + evalHahn y`** for the library's Hahn series with **arbitrary supports** (no cancellation): truncations are prefixes (`InitialSeg` + `typein`), `evalHahn (trunc) = hahnSumO` of the prefix, the **split law** `evalHahn x = evalHahn (x.trunc e) + evalHahn (x − x.trunc e)`, and a per-option coarseness notion `TermRep` (each option coarse against *some* term class) that makes the sum-game engine work at limit stages of the merged series | [`Infinity/HahnMerge.lean`](Infinity/HahnMerge.lean) |

### CONWAY'S NORMAL FORM THEOREM (2026-09-02, night)

| Result | Statement (informal) | Where |
|---|---|---|
| **Coarse ⟹ simplest in the fine halo** | If `X` is coarsely representable at class `c`, every `z` with `z − X` strictly finer than `c` has `birthday X ≤ birthday z` (`z` fits the coarse representative). Hence **every coarsely representable point is halo-simple** at every finer scale — the roadmap's conjecture φ — and every successor-length normal-form value is halo-simple below its last term | [`Infinity/NormalFormTheorem.lean`](Infinity/NormalFormTheorem.lean) |
| **The birthday bound along the extraction** | For every stage `β` at which the leading-term extraction of `x` is still alive, `birthday (S_β) ≤ birthday x` (limit stages: `x` fits the option game; successor stages: the coarse representative) | [`Infinity/NormalFormTheorem.lean`](Infinity/NormalFormTheorem.lean) |
| **CONWAY'S NORMAL FORM THEOREM** | **The leading-term extraction of every surreal terminates**: the partial sums are pairwise distinct while alive and all born by day `birthday x`, a small set, so they cannot run through all ordinals. Hence **`x = hahnSumO (cnfTerm x) (cnfLength x)`** — every surreal is the canonical transfinite sum of its normal form `Σ_{β<α} r_β ω^{y_β}`, a strictly dominating series of monomials of a unique length — the gap `CNF.lean` isolated in August, closed. First proof in Lean (Mizar has the only other) | [`Infinity/NormalFormTheorem.lean`](Infinity/NormalFormTheorem.lean) |
| **THE NORMAL-FORM CORRESPONDENCE** | `evalHahn : SurrealHahnSeries → Surreal` is a **bijection** (`hahnEquiv`), with inverse `toHahnSeries` built from the extraction; uniqueness of the normal form at every length (superseding the limit-length-only injectivity of August) | [`Infinity/NormalFormTheorem.lean`](Infinity/NormalFormTheorem.lean) |
| **Additivity with cancellation** | **`evalHahn (x + y) = evalHahn x + evalHahn y` for all Hahn series** — no hypothesis: induction over the stages of the non-cancelling union series, with the cofinal/bounded-away split at limit stages; `evalHahn_neg`, `evalHahn_sub`, `evalHahn_sum`; **`hahnAddEquiv : SurrealHahnSeries ≃+ Surreal`** | [`Infinity/HahnRing.lean`](Infinity/HahnRing.lean) |
| **Products by a term, and by finite series** | The coefficient formula `coeff_mul` (mathlib's Cauchy product through the library's `Lex` layer); `evalHahn (single z c * y) = c·ω^z · evalHahn y` (the support translates, an order isomorphism); `evalHahn 1 = 1`; **`evalHahn (x * y) = evalHahn x · evalHahn y` whenever one factor has finite support** | [`Infinity/HahnRing.lean`](Infinity/HahnRing.lean) |
| **Order-preservation** | `evalHahn x < evalHahn y ↔ x < y`: the lexicographic (colex) order on coefficients is the sign of the leading coefficient of the difference, and the leading term dominates the evaluation; `evalHahn_strictMono` | [`Infinity/HahnProduct.lean`](Infinity/HahnProduct.lean) |
| **THE TRANSFINITE PRODUCT THEOREM** | **`evalHahn (x * y) = evalHahn x · evalHahn y` for all Hahn series.** Induction on the pair of lengths; successor stages by distributivity; at a pair of limit lengths, every option of the product of the two option games is the evaluation of a *shorter* series, so by the induction hypothesis it is `evalHahn (x·y − D)` with `D` of definite sign — the formal product's value **fits the product game**; conversely the surreal product fits a game for the formal product's value because every exponent of `x·y` is a sum of two exponents and both factors keep going; the simplicity theorem (`eq_mk_of_fits_of_birthday_le`) forces equality. No estimate below the support is ever needed, which is what defeats the trap `x · x⁻¹ = 1` with both factors infinite | [`Infinity/HahnProduct.lean`](Infinity/HahnProduct.lean) |
| **CONWAY'S ISOMORPHISM `No ≅ ℝ((ω^No))`** | **`hahnOrderRingIso : SurrealHahnSeries ≃+*o Surreal`** — the surreal numbers are the ordered field of Hahn series with real coefficients and surreal exponents, with evaluation the canonical transfinite sum and inverse the leading-term extraction; `evalHahn_inv`, `evalHahn_div`, `evalHahn_pow`, `toHahnSeries_mul`, `toHahnSeries_inv` | [`Infinity/HahnProduct.lean`](Infinity/HahnProduct.lean) |

### THE FAITHFUL EXPONENTIAL (2026-09-03)

| Result | Statement (informal) | Where |
|---|---|---|
| **Faithful evaluation of power series** | Through the isomorphism, mathlib's `heval` gives **`fevalHom ε : PowerSeries ℝ →+* Surreal` with `X ↦ ε` exactly** for every infinitesimal `ε` (the canonical `scaleEval` only had `X ↦ haloValue ε ε`); the support of the evaluated series is small (the new lemma `small_support_heval`) | [`Infinity/FaithfulExp.lean`](Infinity/FaithfulExp.lean) |
| **THE FAITHFUL EXPONENTIAL** | `expH ε := fevalHS ε (exp ℝ)`: **multiplicative at all infinitesimals** (`heval_exp_add` in the Hahn-series field, from mathlib's `exp_mul_exp_eq_exp_add` read inside `ℝ((ω^No))` plus a generic antidiagonal regrouping of summable families), reflection law, positivity, injectivity, `stdPart = 1`, `\|expH σ − 1 − σ\| ≤ (3/2)σ²` | [`Infinity/FaithfulExp.lean`](Infinity/FaithfulExp.lean) |
| **exp′ = exp, faithfully** | **`HasDerivS expH σ (expH σ)` at every infinitesimal `σ`** with the finite constant `(3/2)\|expH σ\|`, and **`HasDerivS expFinH x (expFinH x)` at every finite `x`** (`expFinH x := e^{st x} · expH (x − st x)`, multiplicative on the finite galaxy) — stated next to `¬ HasDerivS expInf' σ (expInf' σ)`: the first honest exponential ODE on the surreals in a proof assistant, exactly where canonical sums provably fail | [`Infinity/FaithfulExp.lean`](Infinity/FaithfulExp.lean) |
| **Canonical = halo simplification of faithful** | `expInf ε = haloValue \|ε\| (expH ε)` for every nonzero infinitesimal; `expInf ε = expH ε` iff `expH ε` is halo-simple; **equal at every monomial `c·ω^y`**; **different at `ω⁻¹ + ω^(−ω)`**, where the faithful exponential sees the fine term and the canonical one does not | [`Infinity/FaithfulExp.lean`](Infinity/FaithfulExp.lean) |
| **THE JET CALCULUS** | **The Taylor shift law in the Hahn-series field** (`heval (a+b) f = Σ_j heval a (D^j f/j!)·b^j`, for general exponent monoids, via a small summable-family engine); hence for every power series `T` and centre `c`, the jet `x ↦ fevalHS (x − c) T` is **`HasDerivS`-differentiable at every point of the halo of `c` with derivative the jet of the formal derivative**, uniform constant `\|T₂\| + 1`; all higher derivatives likewise | [`Infinity/JetCalculus.lean`](Infinity/JetCalculus.lean) |
| **Composition and the chain rule** | `heval x (f.subst g) = heval (heval x g) f` for `g` without constant term (general `Γ`; a lemma mathlib lacks), so `fevalHS ε (f ∘ g) = fevalHS (fevalHS ε g) f` and the chain rule `(f ∘ g)′ = (f′ ∘ g)·g′` for jet functions | [`Infinity/JetCalculus.lean`](Infinity/JetCalculus.lean) |
| **The faithful logarithm** | `exp ∘ log = 1 + X` and `log ∘ (exp − 1) = X` as power-series identities; `logH1p ε := fevalHS ε log` is a **two-sided inverse of `expH`** on infinitesimals, additive on products, strictly increasing, with **`log′ = 1/x`** at every point of the halo of `1` — an honest inverse pair, where the canonical pair was only halo simplification | [`Infinity/JetCalculus.lean`](Infinity/JetCalculus.lean) |

### THE ANALYTIC CALCULUS ON THE FINITE GALAXY (2026-09-03)

| Result | Statement (informal) | Where |
|---|---|---|
| **Every real function extends to the finite galaxy** | `extC f x := fevalHS (x − st x) (taylorJet f (st x))` with `taylorJet f r = Σ f⁽ⁿ⁾(r) Xⁿ/n!`; `extC f r = f r` on reals; **`HasDerivS (extC f) x (extC (deriv f) x)` at every finite `x`, for every `f : ℝ → ℝ`** (the jet derivative identity `derivative (taylorJet f r) = taylorJet (deriv f) r` is unconditional); higher derivatives; additive and multiplicative on `C^∞` functions, polynomials agree with `IntegralS` | [`Infinity/AnalyticCalculus.lean`](Infinity/AnalyticCalculus.lean) |
| **THE FUNDAMENTAL THEOREM OF CALCULUS ON THE FINITE GALAXY** | `integralC f a b := extC (prim f) b − extC (prim f) a` with `prim f t = ∫₀ᵗ f`. **FTC I**: for continuous `f` and finite `x`, `HasDerivS (integralC f a) x (extC f x)`. **FTC II**: for any real antiderivative `G` of `f`, `integralC f a b = extC G b − extC G a`, for *all* surreal `a, b`. **Uniqueness**: any operator satisfying FTC II on the class equals `integralC`. Interval additivity, linearity, agreement with the real integral at real endpoints and with `Integral.lean` for polynomials | [`Infinity/AnalyticCalculus.lean`](Infinity/AnalyticCalculus.lean) |
| **Showcases** | `extC Real.exp = expFinH`; **`∫₀^ε eˣ dx = expH ε − 1`**; `extC Real.log (1+ε) = logH1p ε`, `extC (·⁻¹) (1+ε) = (1+ε)⁻¹`; **`∫₁^{1+ε} dx/x = logH1p ε`** (for any continuous integrand agreeing with `1/x` near `1`); a local FTC II within a halo | [`Infinity/AnalyticCalculus.lean`](Infinity/AnalyticCalculus.lean) |
| **The Costin–Ehrlich–Friedman obstruction in miniature** | For the smooth flat function `expNegInvGlue` (positive on `(0,∞)`, zero on `(−∞,0]`), **`extC expNegInvGlue ε = 0` for every positive infinitesimal `ε`**: the extension of smooth functions exists but is not order-faithful; `∫₀^ε expNegInvGlue = 0` | [`Infinity/AnalyticCalculus.lean`](Infinity/AnalyticCalculus.lean) |

## The one-paragraph story

On the real numbers, "the series sums to S" and "the partial sums approach S" are the same
concept. On the surreals they come apart — provably. No point of No has a countable
neighborhood base (any countable family of positive surreals has a positive lower bound,
the Conway cut `{0 | z₀, z₁, …}`), so ω-length sequences can never approach anything they
don't eventually equal; yet infinite series still have canonical sums under *domination*
semantics: `x` sums the series when every residual `x − (partial sum)` is dominated (in
Archimedean class) by the first omitted term. This repository proves both halves and
exhibits the flagship instance. The consequence for the fifty-year-open problem of surreal
integration (Conway–Kruskal–Norton) is a precise reframing: an integral on No must be a
domination-semantics object, because approximation-semantics integrals are impossible.

## Building

```
brew install elan-init        # Lean toolchain manager (macOS)
lake exe cache get            # prebuilt mathlib binaries
lake build                    # builds everything incl. CombinatorialGames (~minutes)
```

Toolchain and dependencies are pinned in [`lean-toolchain`](lean-toolchain) and
[`lakefile.toml`](lakefile.toml). Dev loop: `lake env lean Infinity/<File>.lean`
typechecks a single file fast.

## Continuing this work

The design rationale behind the main constructions is in [`notes/`](notes) — limits in
[`notes/limits-design.md`](notes/limits-design.md), Gonshor's exponential in
[`notes/gonshor-exp-design.md`](notes/gonshor-exp-design.md), the exponential at infinite
arguments in [`notes/exp-infinite-design.md`](notes/exp-infinite-design.md), and the
decision-theoretic reading in [`notes/decision-theory.md`](notes/decision-theory.md).

Each Lean file opens with a module docstring stating what it proves and how it relates to
its neighbours; `Infinity.lean` is the import root and reads as a table of contents.

A paper describing these results, *The Simplest Sum*, is in preparation; it cites the Lean
name of every theorem it states.

[mathlib]: https://github.com/leanprover-community/mathlib4
[CombinatorialGames]: https://github.com/vihdzp/combinatorial-games
