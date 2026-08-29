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
