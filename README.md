# Surreals

**Machine-checked infinitesimal calculus on Conway's surreal numbers.**

This repository contains, to our knowledge, the first formal (Lean 4) development of
analysis on the surreal number field **No**: the standard-part decomposition, a complete
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

Read [`docs/HANDOFF.md`](docs/HANDOFF.md) — a complete technical handoff (state, proofs
guide, conventions, pitfalls, and the forward roadmap), written so that a new contributor
(human or AI agent) can pick up exactly where this left off. The phase log lives in
[`tasks/todo.md`](tasks/todo.md); the design rationale for limits in
[`notes/limits-design.md`](notes/limits-design.md).

[mathlib]: https://github.com/leanprover-community/mathlib4
[CombinatorialGames]: https://github.com/vihdzp/combinatorial-games
