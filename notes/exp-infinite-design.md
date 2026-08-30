# Design note: the exponential at infinite arguments, and `∫₀^ω eˣ dx = e^ω − 1`

*Written 2026-08-30, after banking `Infinity/ExpFin.lean` (exp on the finite galaxy,
exact real-translation functional equation, `exp′ = exp` at every real point) and
`Infinity/Darboux.lean` (the genetic experiment). This note maps the road from here to
exp at infinite arguments and the exponential integral — the computation Norton's
integral famously got wrong. Nothing in this note is formalized unless it names a
theorem in the repository.*

## 1. What is banked

- `expInf` (canonical Hahn sum of the exponential series) on nonzero infinitesimals;
  `expFin x := Real.exp (st x) · expInf′(x − st x)` on the whole finite galaxy.
- Exact laws: `expFin_realCast`, `expFin_of_infinitesimal`, `expFin_realCast_add`
  (functional equation, exact, when one argument is real), `stdPart_expFin`,
  positivity, monotonicity across real parts.
- Quantitative law: `abs_expInf'_sub_one_sub_le` (`|expInf′ ε − 1 − ε| ≤ (3/2)ε²`,
  uniform constant) and hence `hasDerivS_expFin_realCast` : **exp′ = exp at every real
  point**, in the strong `O(ε²)` sense over all infinitesimal increments.
- Functional equation at nonzero infinitesimal parts: mod domination
  (`mk_expFin_add_sub_mul`); exact iff a birthday inequality holds
  (`expInf_add_eq_mul_iff`); exact outright if the product is born by day ω
  (`expInf_add_eq_mul_of_birthday_le`).

## 2. Gonshor's genetic definition (the classical object)

Gonshor (1986, ch. 10) defines exp on all of **No** by genetic recursion. In the form
usually quoted (⚠ from memory — *verify against the source before formalizing*): for
`x = {x^L | x^R}`,

```
exp x = { 0, exp(x^L)·[x − x^L]_n, exp(x^R)·[x − x^R]_{2n+1}
        | exp(x^R)/[x^R − x]_n, exp(x^L)/[x^L − x]_{2n+1} }
```

where `[y]_n = Σ_{k≤n} yᵏ/k!` are the partial sums of the exponential series and options
are used only where the relevant `[·]` values are positive. Key classical facts:
`exp : (No, +) ≅ (No^{>0}, ·)`, `exp ω = ω^ω`, and on purely infinite arguments exp is
computed by Gonshor's `g`-function on normal-form exponents (Berarducci–Mantova's survey
has the modern account).

## 3. Three routes to exp at infinite arguments

**Route A (recommended next): the ω-linear galaxy, definitionally.**
CombinatorialGames has `ω^ : Surreal → Surreal` (`wpow`) and leading-term machinery
(`Surreal/Leading.lean`). Define, on the galaxy `D₁ := {x : x = r·ω + f, r ∈ ℝ, f finite}`
(leading-coefficient extraction gives `r` and `f`):

```
expOmega x := (ω^ (ω·r-as-surreal? — care: exponent is r·ω... classical: exp(rω) = ω^(rω)? NO)
```

Care with the classical value: `exp(r·ω) = ω^{ω·r}` is *false* in general;
`exp ω = ω^ω` and for real `r > 0`, `exp(rω) = (ω^ω)^r`-type identities need Gonshor's
normal-form calculus. The safe v1 is the *ℤ-lattice*: `exp(n·ω + f) := (ω^ω)ⁿ · expFin f`
for `n : ℤ`, where `(ω^ω)ⁿ` is an honest surreal power. Provable theorems at v1 scope:
  - functional equation on the lattice, exact up to `expFin`'s own caveats
    (`wpow`/`zpow` addition laws + `expFin_realCast_add`);
  - positivity, monotonicity in `n`;
  - `stdPart`-type leading-term law: `expOmega(n·ω + f)` has leading monomial `(ω^ω)ⁿ·exp(st f)`.
This would be the first exp defined beyond the finite galaxy in a proof assistant, with
honest scope. The generalization to real `r` needs `(ω^ω)^r` — i.e. surreal powers with
real exponents on monomials — which `Sqrt.lean`'s technique (recursive coefficients)
suggests is approachable for dyadic `r` first (iterated square roots).

**Route B: full genetic recursion.** Implement Gonshor's definition on `IGame` by
well-founded recursion (the `igame_wf` machinery upstream handles such definitions).
Cost: the uniformity theorem (independence of representative) and the positivity side
conditions make this a multi-session project. Payoff: the *actual* classical object, on
all of **No**. Do this only after Route A pins the target values.

**Route C: wait for upstream Hahn-series evaluation** (vihdzp is building it), then
define exp by normal-form transport (Gonshor's `g`). Cleanest long-term, not in our
control.

## 4. The Norton-error geometry (what `Darboux.lean` teaches)

`Infinity/Darboux.lean` proves: over `[0, ω]`, the Darboux cut for `∫ x dx` admits both
`ω²/2` and `ω²/2 + ω` as fits — the cut is loose at scale ω, and only the simplicity
principle picks the value. Now run the same geometry for `∫₀^ω eˣ dx` (informally):
any partition-sum cut for exp on `[0, ω]` has width of the same Archimedean class as
`e^ω` itself (a piece of length ≥ ω/n contributes at exp-scale). Hence **both `e^ω` and
`e^ω − 1` fit** — they differ by `1`, which is far below the cut's resolution. The
truncation-simplicity heuristic (a monomial is simpler than monomial-plus-correction,
and classically `e^ω = ω^ω` *is* a monomial) then predicts that the simplest fit is
`e^ω`, not `e^ω − 1`. In other words: **Norton's wrong value is exactly what the naive
simplest-fit principle produces**; the correct genetic integral must inject information
at scales the cut cannot see (this is what Costin–Ehrlich's analyzable-function
machinery does, and what any genetic repair must reproduce). A formal version of "both
`e^ω` and `e^ω − 1` fit the exp-Darboux cut" is provable with today's machinery as soon
as Route A gives `exp` on `[0, ω]`-relevant arguments — a concrete, striking target:
*Norton's error as a theorem.*

## 5. The FTC route to the integral

`∫₀^ω eˣ dx = e^ω − 1` via FTC needs `HasDerivS exp x (exp x)` along `[0, ω]`. Banked:
true at all real `x`. Blocked at: `x` with nonzero infinitesimal part, and at infinite
`x` — both hit the *canonical-sum variation problem* (how does `hahnSum`/simplestBtwn
move as the argument moves? — recorded in `Infinity/Laurent.lean`'s docstring). The
class-internal alternative that worked for Laurent integrands: define an
**exp-polynomial class** `{Σ cᵢ e^{qᵢ x} + P(x)}` with a data-level antiderivative and
prove class-internal FTC/uniqueness, sidestepping pointwise derivatives at bad points.
That template (Laurent.lean) is the shortest credible path to a verified
`∫₀^ω eˣ dx = e^ω − 1` once Route A lands `e^ω`.

## 6. Sharpest open sub-problems, in order

1. **Halo minimality** (BirthdayHahn's named gap): is `ω/(ω−1)` birthday-minimal in its
   micro-halo? Equivalently `hahnSum(Σ ω⁻ᵏ) = ω/(ω−1)`. Needs normal-form/sign-expansion
   birthday theory (day-ω classification, banked, is the first step of exactly this kind;
   the next is a day-`ω·2`/`ω²` classification, or truncation-simplicity directly).
2. **Canonical-sum variation**: bound `|hahnSum(series at x+ε) − hahnSum(series at x)|`
   below all series scales. This unlocks both FTC beyond Laurent and monotonicity of
   `expInf` at equal standard parts.
3. **Route A v1** (§3): exp on the ω-lattice; then Norton's error as a theorem (§4).
4. **Is birthday-minimality multiplicative on exp-products?** (`expInf_add_eq_mul_iff`'s
   right-hand side.) The day-ω classification reduces the first unknown case to a
   concrete question about day-ω surreals infinitesimally close to 1.
