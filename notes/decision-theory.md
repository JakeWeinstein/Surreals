# Surreal expected utility, formally: a map between the theorems and the philosophy

*Written 2026-08-29, accompanying `Infinity/Expectation.lean` and
`Infinity/PascalWager.lean`. Everything cited as a "theorem" below is kernel-checked in
Lean 4 against mathlib + CombinatorialGames; `lake build` green at time of writing.*

## 1. What this is

The philosophy of probability contains a live, twenty-year debate about infinitesimal and
infinite values in probability and decision theory. Three works frame the part of it
addressed here:

- **Chen & Rubio, "Surreal Decisions"**, *Philosophy and Phenomenological Research* 100(1)
  (2020): 54–74 (arXiv:2111.00862). Propose surreal-valued utilities and credences; prove a
  surreal von Neumann–Morgenstern representation theorem for **finite** lottery spaces;
  analyze Pascal's Wager (mixed strategies, many gods, degrees of glory). They explicitly
  restrict to finite state spaces: *"In this work, we confine ourselves to finite state
  spaces"* (§1), flag that *"the technical questions about how to do surreal infinite sum
  … do not come up"* (fn. 11), and promise *"a second paper about surreal infinite sum"*
  (fn. 12); their conclusion defers infinite-state problems (St. Petersburg, Pasadena)
  *"pending ongoing research in surreal analysis"*.
- **Gallow, "Surreal Probabilities"** (PhilArchive: GALSPE-2). Develops surreal-valued
  probability so that intuitive "infinitely more likely" judgements about infinitary events
  (infinite coin-flip sequences, fair lotteries) receive exact numerical values; presented
  as a user's guide with open questions for further research.
- **Pruss, "Underdetermination of infinitesimal probabilities"**, *Synthese* 198 (2021):
  777–799. Against Hájek- and Easwaran-style complaints that hyperreal probabilities are
  *ineffable* (no definable hyperreal field — refuted via Kanovei–Shelah-style
  specifiability), Pruss presses the deeper problem: **any** regular infinitesimal-valued
  probability assignment can be replaced by a different assignment with *all the same
  intuitive features* but other infinitesimal values. The constraints underdetermine the
  values; the choice among them looks arbitrary.

This repository already contained the two halves of a mathematical answer, proved for
independent reasons in the surreal-calculus program:

1. **The obstruction half** (`Infinity/Limits.lean`, `Infinity/Series.lean`): ℕ-indexed
   sequences of surreals converge only by being eventually constant
   (`tendstoSurreal_atTop_iff_eventuallyEq`), so infinite sums on **No** cannot be limits;
   the semantics that survives is *domination* (`IsHahnSum`): a sum is any value whose
   every residual is dominated by the first omitted term. Hahn sums exist for every
   strictly dominating series (`exists_isHahnSum`) and are unique only *modulo domination*
   (`IsHahnSum.mk_sub_le`) — a nondegenerate interval of values.
2. **The selection half** (`Infinity/CanonicalSum.lean`, `Infinity/BirthdayHahn.lean`):
   the Hahn sums of a series form exactly a cut interval (`fits_iff_isHahnSum`), and
   Conway's simplicity machinery selects the **birthday-minimal** element `hahnSum`,
   which is *unique* as a minimal-birthday sum (`hahnSum_eq_iff`), with every rival
   **strictly** more complex (`birthday_hahnSum_lt_of_ne`) and at distance of birthday
   `≥ ω` (`omega0_le_birthday_sub_of_isHahnSum`).

The new files `Infinity/Expectation.lean` and `Infinity/PascalWager.lean` turn this
correspondence into decision theory: the underdetermination Pruss describes **is** the
domination-uniqueness gap, his replacement construction **is** a two-line lemma, the gap
is computed exactly, and the birthday-minimal sum is a principled, definable selection —
with the flagship Pascalian conclusions proved *independently of the selection*.

## 2. The dictionary: philosophical claim ↔ formal theorem

| Philosophical claim | Source | Formal status | Theorem (file) |
|---|---|---|---|
| Expected utility over countably many outcomes cannot be defined by convergence/approximation on No | implicit throughout; the reason Chen–Rubio defer infinite state spaces | **theorem** | `not_tendstoSurreal_partialSum_expectation` (Expectation); instance `not_tendstoSurreal_partialSum_wager` (PascalWager) |
| Infinitesimal expected values are underdetermined: rival assignments fit the same constraints | Pruss 2021 (for hyperreal probabilities) | **theorem**, made exact | `isHahnSum_iff_forall_mk_le` (the solution set is exactly a coset of the tail-halo); `IsHahnSum.add_halo` (the replacement construction); `exists_pos_forall_mk_lt` + `exists_isHahnSum_ne` (rivals always exist) (Expectation) |
| The size of the underdetermination | — (new question, formulable only formally) | **theorem** | halo-coset in the dominating regime (`isHahnSum_iff_forall_mk_le`); full scale-`c` ball when the finest scale is attained (`isHahnSum_iff_of_le_of_attained`); exactly the finite surreals for St. Petersburg (`isHahnSum_one_iff`, `stPetersburg_collapse`) |
| A principled selection exists: the *simplest* consistent value | response to Pruss; unavailable for hyperreals | **theorem** | `hahnSum` + `hahnSum_eq_iff`, `birthday_hahnSum_le` (CanonicalSum/BirthdayHahn); `exists_isHahnSum_ne_hahnSum`: every rival is strictly more complex (Expectation) |
| The alternatives are not merely non-minimal but *transfinitely* more complex | — | **theorem** | `omega0_le_birthday_sub_of_isHahnSum` (BirthdayHahn): distinct consistent values differ by an element born at or after day ω |
| Finite-lottery expected utility is fully determined (the classical theory is untouched) | Chen–Rubio's finite-state theory | **theorem** | `eq_of_isHahnSum_expectation_of_prob_zero` (Expectation) |
| The real-valued shadow of surreal expectation is classical expectation | Chen–Rubio §3.2-style calculations | **theorem** | `stdPart_eq_of_isHahnSum` (Expectation); instance `stdPart_refuseValue = 11` (PascalWager) |
| Dominance reasoning is respected by surreal EU | Chen–Rubio §3.2, §4 ("our theory respects dominance") | **theorem** at countable scope | `pos_of_isHahnSum`, `lt_of_isHahnSum_of_head_lt` (Expectation); `isHahnSum_refuse_lt_isHahnSum_wager` (PascalWager) |
| A fair-lottery-style credence can be positive yet infinitesimal (regularity) | Chen–Rubio §3.3.1 (Rene); Benci–Horsten–Wenmackers; Gallow | **theorem** (existence in No, in a working lottery) | `pascalProb_pos`, `pascalProb_infinitesimal`, `pascalProb_le_one` (PascalWager) |
| A countable lottery can have total probability exactly 1 with all-positive weights | Gallow's desideratum; NAP-style normalization | **theorem** | `isHahnSum_pascalProb_one`, `hahnSum_pascalProb_eq_one` (PascalWager, via `hahnSum_telescoping_eq_one`) |
| Pascal's Wager: wagering has expected utility beyond every real, even at infinitesimal credence | Chen–Rubio §4 (finite-state version) | **theorem** at countable scope, *selection-independent* | `forall_realCast_lt_of_isHahnSum_wager`, `forall_realCast_lt_wagerValue` (PascalWager) |
| The pure wager beats every mixed strategy (Hájek's objection dissolved by non-absorption) | Chen–Rubio §4.1; Hájek 2003 | **theorem**, both for value-mixtures and for the mixed *act as a lottery* | `mixed_lt_wagerValue`, `forall_realCast_lt_mixed` (values); `isHahnSum_mix_lt_isHahnSum_wager`, `forall_realCast_lt_of_isHahnSum_mix`, `mixValue_lt_wagerValue`, `forall_realCast_lt_mixValue` (the mixed lottery itself, across both entire halos, no linearity assumption) (PascalWager) |
| St. Petersburg resists this treatment | Chen–Rubio's conclusion (deferred); Hájek–Nover literature | **theorem** (negative) | `isHahnSum_one_iff` (Expectation), `stPetersburg_collapse` (PascalWager) |

## 3. What is genuinely new here

To our knowledge each of the following is new — not only as formalization, but in some
cases as mathematics/philosophy:

1. **First machine-checked foundation for surreal-valued expected utility.** Chen–Rubio's
   framework is informal mathematics on finite state spaces; Gallow's is informal on
   probabilities; nothing in either literature is formalized. (Ord's *Evaluating the
   Infinite* (2025) assigns hyperreal values to divergent series — a different codomain,
   different semantics, also unformalized.)
2. **The infinite-state step Chen–Rubio deferred.** Their fn. 12 promises a future theory
   of "surreal infinite sum" for expected utility. Domination semantics (`IsHahnSum`) with
   the canonical birthday-minimal sum is such a theory, and the wager analysis of §4 of
   their paper goes through at countable scope, kernel-checked, including total
   probability 1 and the mixed-strategy analysis.
3. **Pruss's underdetermination as an exact theorem, with an exact measure.** Pruss proves
   (for hyperreal probability measures) that rival assignments with the same features
   exist. Here the entire rival set is *computed*: a coset of the tail-halo
   (`isHahnSum_iff_forall_mk_le`), never trivial (`exists_isHahnSum_ne`), a full
   Archimedean ball in the flat regime (`isHahnSum_iff_of_le_of_attained`), collapsing to
   a point exactly for finite lotteries (`eq_of_isHahnSum_expectation_of_prob_zero`).
   Underdetermination is thus not an all-or-nothing objection but a *quantity*, and its
   value is: the finest scale the lottery's stakes can name.
4. **A formal simplicity answer.** The birthday-minimal consistent value exists, is
   unique-as-minimal (`hahnSum_eq_iff`), and every rival is strictly more complex, by a
   transfinite margin (`birthday_hahnSum_lt_of_ne`;
   `omega0_le_birthday_sub_of_isHahnSum`). Two features distinguish this from anything
   available on the hyperreals: (i) **No** is canonical — no ultrafilter, no
   model-theoretic choice, so the Hájek/Easwaran ineffability worry (which Pruss already
   rejects) cannot even get started; (ii) the simplicity order is *intrinsic* structure of
   the number system (Conway's birthday), not an external convention.
5. **Selection-independence of the flagship verdicts.** The Pascalian theorems are proved
   for **every** domination-consistent value, not just the canonical one
   (`forall_realCast_lt_of_isHahnSum_wager`, `isHahnSum_refuse_lt_isHahnSum_wager`). So
   even a reader unmoved by birthday-minimality — who insists the expectation is
   *indeterminate* across the halo — must grant the decision-theoretic conclusions: they
   are supervaluationally true, holding under every admissible precisification. This
   dissolves the practical force of the underdetermination objection for this class of
   problems entirely.
6. **The negative results are theorems, not concessions.** No limit-based expectation
   (`not_tendstoSurreal_partialSum_expectation`); no canonical St. Petersburg value by
   domination semantics, even with genuinely surreal infinitesimal probabilities and
   `ω^n`-scale payoffs (`stPetersburg_collapse`). The scope of surreal expected utility is
   mapped from both sides.

## 4. What the canonical expectation settles — and what it does not

**Settled (as theorems):**
- Existence and canonicity of expected utility for every lottery whose expectation series
  strictly descends through Archimedean scales — the "Pascalian" regime: a hierarchy of
  ever-less-probable, differently-scaled stakes.
- Conservativity over classical finite expected utility (both through `stdPart` and
  through exact determinacy for finite lotteries).
- Dominance, sign, comparison and rescaling laws at the level of the whole solution set.
- The classical Pascal verdicts at countable scope, selection-independently.

**Not settled, and why — the honest ledger:**
- **Why birthday-simplicity?** That the canonical value is *the simplest consistent value*
  is a theorem; that rational agents should *value lotteries by the simplest consistent
  value* is a normative premise no theorem can supply. What the formal work contributes is
  a sharpened dialectic: the selection is definable, canonical, and unique, so the
  residual philosophical question is exactly "is simplicity a reason?" — the same question
  faced by every appeal to naturalness/parsimony — and no longer "isn't this arbitrary?".
  (For the wager itself even this premise is dispensable, by selection-independence.)
- **Additivity of the canonical expectation across lotteries.** `IsHahnSum.add`
  (BirthdayHahn) gives additivity at the consistent-value level under termwise
  non-cancellation; whether `hahnSum (t + u) = hahnSum t + hahnSum u` is **equivalent** to
  a birthday-minimality inequality (`hahnSum_add_eq_iff`) that remains open. The
  mixed-strategy theorems sidestep this entirely: the mixed act is evaluated directly as
  a lottery (`mixSorted`), so no linearity premise is used — but a general identification
  of value-mixtures with canonical expectations of mixed lotteries, and a vNM-style
  representation theorem at countable scope, still sit behind the additivity door.
- **Archimedean-flat lotteries.** St. Petersburg (real or surreal-graded), fair countable
  lotteries with equal-class weights, and Pasadena-style games have galaxy-sized solution
  sets (`isHahnSum_iff_of_le_of_attained`); domination semantics is honestly silent.
  Whatever the right story is there — NAP-style ideal-based summation
  (Benci–Horsten–Wenmackers), Gallow's finer-grained probability values, Ord's hyperreal
  divergent-series calculus, or principled indeterminacy — it is not this mechanism.
  Notably, the collapse theorem shows the failure is *not* repaired by making
  probabilities infinitesimal and payoffs transfinite: flatness of the *products* is what
  matters.
- **Enumeration-dependence.** `IsHahnSum` reads a series in a given order, and the wager's
  expectation series must be enumerated in decreasing scale (the Conway-normal-form
  convention; `wagerSorted` transposes two outcomes). For strictly dominating
  enumerations, the value is enumeration-forced; but a permutation-invariant,
  multiset-level theory of surreal expectation (and its relation to NAP's
  order-independence axioms) is future work.
- **Probability theory proper.** We model a single lottery's weights as a sequence, not a
  measure on an algebra of events: no conditionalization, no independence, no updating,
  no representation theorem. Gallow's fine-grained event probabilities and Chen–Rubio's
  promised countable-additivity analogue (their fn. 12, via Benci et al.'s Ω-limits) are
  natural next targets; the `CauchyProduct` module (products of Hahn sums under a
  no-cancellation floor) is the likely tool for independence.

## 5. Situating the result (related work, precisely)

- *Chen & Rubio 2020*: finite-state surreal vNM theorem; wager analysis. Our work is
  strictly downstream (their framework) and strictly beyond (their deferred infinite
  case). Nothing here contradicts them; their fn. 25 caveat (Continuity⋆ forces
  bribability by infinitesimal credence gaps) is orthogonal to summation.
- *Gallow (PhilArchive)*: surreal probabilities for infinitary events, computed values,
  open questions. Our contribution is on the expectation/summation side he does not
  develop; his fine-grained event probabilities are a complementary input this framework
  could consume as `p`.
- *Pruss 2021*: the underdetermination argument formalized here is the domination-semantics
  analogue of his hyperreal replacement theorem. Two honest differences: (i) Pruss's
  target is *probability assignments*; ours is *expected utilities/sums* — the phenomena
  are the same in kind (constraint sets invariant under small perturbations) and our
  probability weights are themselves surreal values subject to the same analysis
  (`hahnSum_pascalProb_eq_one` selects the canonical total, and rivals exist for the
  weights too); (ii) Pruss concludes arbitrariness is unavoidable *for hyperreal
  probabilities*; the surreal simplicity order is exactly the structure whose absence his
  argument exploits.
- *Hájek 2003* ("Waging War on Pascal's Wager"): the mixed-strategy objection.
  `isHahnSum_mix_lt_isHahnSum_wager` + `forall_realCast_lt_of_isHahnSum_mix` are the
  formal content of Chen–Rubio's reply, proved for the mixed act *as a lottery* and
  across both entire underdetermination halos: mixtures remain transfinitely valuable but
  are strictly dominated by purity, because surreal multiplication by `γ < 1` is
  non-absorptive.
- *Benci–Horsten–Wenmackers (NAP)*: finitely-additive, regular, non-Archimedean
  probability on hyperreal-like fields. Our total-probability theorem realizes NAP's
  normalization desideratum in **No** by canonical transfinite summation rather than by
  ideal/ultrafilter machinery — with the trade-off that NAP handles flat (fair-lottery)
  sums, which domination semantics provably does not.
- *Ord 2025* (arXiv:2509.19389): hyperreal values for divergent sums/integrals, applied to
  infinite EU. Different codomain and semantics; unformalized; the comparison of his
  assignments with canonical Hahn sums on their common domain is an open question worth
  someone's time.
- *Formalization landscape*: we know of no prior machine-checked development of
  non-Archimedean expected utility in any proof assistant (hyperreal constructions exist
  in Isabelle/Lean for analysis, but not probability/EU; surreal decision theory has never
  been formalized). The claim "first" is confined to that conjunction and stated with the
  usual caveat that negative literature searches are fallible.

## 6. Theorem index (new files)

`Infinity/Expectation.lean` — general theory:
`expectationSeries`, `not_tendstoSurreal_partialSum_expectation`,
`isHahnSum_iff_forall_mk_le`, `isHahnSum_iff_of_le_of_attained`,
`eq_of_isHahnSum_expectation_of_prob_zero`, `IsHahnSum.add_halo`,
`exists_pos_forall_mk_lt`, `exists_isHahnSum_ne`, `exists_isHahnSum_ne_hahnSum`,
`stdPart_eq_of_isHahnSum`, `pos_of_isHahnSum`, `lt_of_isHahnSum_of_head_lt`,
`partialSum_const_mul`, `IsHahnSum.const_mul`, `mk_mul_lt_mk_mul_left`,
`strict_dominating_const_mul`, `partialSum_one`, `isHahnSum_one_iff`.

`Infinity/PascalWager.lean` — the flagship:
`pascalProb` (+ `_pos`, `_le_one`, `_infinitesimal`, `_strict_dominating`),
`isHahnSum_pascalProb_one`, `hahnSum_pascalProb_eq_one`,
`wagerUtility`, `refuseUtility`, `wagerSeries`, `refuseSeries`, `wagerSorted`
(+ closed forms and `wagerSorted_strict_dominating`),
`not_tendstoSurreal_partialSum_wager`,
`forall_realCast_lt_of_isHahnSum_wager`, `wagerValue`,
`forall_realCast_lt_wagerValue`, `wagerValue_birthday_le`, `exists_rival_wagerValue`,
`refuseSeries_strict_dominating`, `refuseValue`, `refuseValue_pos`,
`stdPart_refuseValue`, `refuseValue_lt_twelve`,
`isHahnSum_refuse_lt_isHahnSum_wager`, `refuseValue_lt_wagerValue`,
`mixed_lt_wagerValue`, `forall_realCast_lt_mixed`,
`mixUtility`, `mixSorted` (+ closed forms and `mixSorted_strict_dominating`),
`isHahnSum_mix_lt_isHahnSum_wager`, `forall_realCast_lt_of_isHahnSum_mix`,
`mixValue`, `mixValue_lt_wagerValue`, `forall_realCast_lt_mixValue`,
`pascalProb_one_mul_wpow_sq`,
`stPetersburgUtility` (+ `_pos`), `stPetersburg_expectationSeries`,
`stPetersburg_collapse`.

Load-bearing imports from earlier layers: `IsHahnSum`, `partialSum`,
`IsHahnSum.mk_sub_le`, `not_tendstoSurreal_partialSum` (Series);
`exists_isHahnSum`, `ne_zero_of_strict_dominating`, `abs_lt_abs_of_mk_lt` (Summation);
`tendstoSurreal_atTop_iff_eventuallyEq`, `exists_pos_forall_lt`, `isFinite_iff`,
`infinitesimal_iff` (Limits); `stdPart` machinery (StandardPart/DerivRules);
`fits_iff_isHahnSum`, `hahnSum`, `birthday_hahnSum_le` (CanonicalSum);
`hahnSum_eq_iff`, `birthday_hahnSum_lt_of_ne`, `omega0_le_birthday_sub_of_isHahnSum`,
`isHahnSum_telescoping`, `hahnSum_telescoping_eq_one`, `telescoping_strict_dominating`,
`IsHahnSum.add` (BirthdayHahn); `IsHahnSum.eq_partialSum_of_apply_eq_zero`
(CauchyProduct); `natCast_lt_wpow_one` (MicroKernel).

## 7. Next steps, in rough order of value

1. **Canonical additivity / the mixture question**: decide `hahnSum_add_eq_iff`'s
   birthday inequality in the non-cancelling regime (the truncation-simplicity
   conjecture). This unlocks linearity of the canonical expectation, honest mixed
   *lotteries*, and a countable-scope representation theorem.
2. **Permutation invariance**: a multiset-level `IsHahnSum` and the theorem that
   scale-sorted enumeration is the unique dominating one (up to within-class
   rearrangement); relate to NAP's axioms.
3. **Events and conditioning**: probability as a function on a set algebra with
   `hahnSum`-additivity on scale-graded partitions; conditional expected utility;
   independence via `CauchyProduct`.
4. **Fair lotteries**: investigate whether any principled refinement (e.g. Gallow-style
   symmetry constraints, or an Ω-limit analogue inside **No**) selects values on flat
   series where domination semantics provably cannot.
5. **Engage the literature**: the results in §3 items 3–5 are, we believe, statable as a
   short philosophy-journal paper (theorems in an appendix, Lean artifact cited);
   Chen–Rubio's promised sequel apparently never appeared, and this fills that gap from
   the formal side.
