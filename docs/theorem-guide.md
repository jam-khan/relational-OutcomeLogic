# Using the shared and probabilistic developments

For a guided first pass, use the [study plan](study/README.md),
[printable inference rules](study/rules.pdf), and
[checked source index](study/theorem-index.md). The exercises there are intended
for independent paper proofs before reading the existing Lean proofs.

The weighted logic proves properties of actual terminating output weights. Its
couplings have exact marginals, so related outputs have equal termination mass.
Assertions may additionally split outcomes and constrain each piece's mass.

The same structural rules, exact-coupling construction, finite-event certificates,
and synchronous/ranked asynchronous loop proofs now also apply to admissible scalar
semirings. The original Set and probability interfaces remain available.

The [repository structure](architecture.md) separates reusable semantics and logic
from examples. Import paths below follow the current layout; Lean declaration
namespaces remain stable.

## Shared algebra and scalar models

| Need | Definition or theorem | Import |
| --- | --- | --- |
| Additive outcomes and Kleisli sequencing | `RelOL.OutcomeModel` | `Algebra.Outcome.Basic` |
| Shared transformer and kernel judgments | `RelOL.Generic.quadSem`, `quad` | `Generic.Judgment` |
| Shared assertions, splitting, sequencing, and choice | `RelOL.Generic.oplus`, `quad_split`, `quad_seq`, `quad_choice` | `Generic.Rules` |
| Conditional reconstruction and distributional refinement | `RelOL.Generic.lifted`, `quad_lifted`, `quad_lifted_dispatch` | `Generic.Distributional` |
| Bounded iteration and indexed continuation contracts | `RelOL.Generic.quad_boundedSteps`, `quad_boundedRec`, `quad_recursion_family` | `Generic.Loops.Bounded` |
| Scalar assumptions for infinite discrete weights | `RelOL.Algebra.SummationSemiring`, `OmegaSummationSemiring` | `Algebra.Scalar.Basic`, `Algebra.Scalar.Order` |
| Construct weights, sequencing, and exact joints | `RelOL.Algebra.Weighted.Weight`, `bind`, `Coupled.bind` | `Algebra.Weighted.Coupling` |
| Statewise coupling as an outcome-logic fragment | `RelOL.Generic.prhl_iff_quad` | `Generic.Coupling` |
| Full least-fixed-point loop semantics | `RelOL.Generic.loopSem`, `loopSem_eq_lfp` | `Generic.Loops.Semantics` |
| Synchronous and ranked mixed loop rules | `RelOL.Generic.prhl_while`, `prhl_while_async` | `Generic.Loops.Synchronous`, `Generic.Loops.Asynchronous` |
| Quantitative refutation in the scalar order | `RelOL.Generic.MassDeficitCert.refutes`, `BugCert.refutes` | `Generic.Refutation` |
| Scalar-weight observations and finite-event bounds | `RelOL.Algebra.Weighted.pushforward`, `eventMass`, `IsCoupling.eventMass_le` | `Algebra.Weighted.Observation`, `Algebra.Weighted.Events` |
| Weighted loop unfolding and support invariants | `RelOL.Algebra.Weighted.loopSem_support_invariant` | `Generic.Loops.Support` |
| Recover existing Set semantics | `RelOL.Generic.set_loopSem_eq` | `Bridges.Set` |
| Recover existing probability semantics and pRHL | `RelOL.Generic.weight_loopSem_eq`, `ennreal_prhl_commands_iff` | `Bridges.Probability` |
| Boolean weights as Set outcomes | `RelOL.Generic.BooleanBridge.encode_loopSem`, `coupled_iff` | `Bridges.Boolean` |
| Independent draws, discarded normalized samples, and expected costs | `RelOL.Weight.bind_comm`, `bind_const_of_isProbability`, `expectation` | `Algebra.ENNReal.Sequencing`, `Algebra.ENNReal.Expectation` |

Prefix imports with `RelationalOutcomeLogic.`. The five implemented scalar instances
are Boolean reachability, extended nonnegative probability weights, extended-natural
trace counts, tropical minimum costs, and finite-word trace languages. The last uses
noncommutative concatenation. [Semiring models](semiring-models.md) records the actual
operations, assumptions, examples, and differences from the TOPLAS model family.

`Examples.Algebra.Routes` runs the same route and countdown programs in the first
four models, including count/cost certificates for changes invisible to reachability.
`Examples.Algebra.Traces` checks ordered logging and rejects swapped logs.
`Examples.Algebra.AsynchronousCountdown` instantiates a shared schedule with joint
weighted steps and unilateral bookkeeping. These are executions of the constructed
weighted models. Their declaration namespaces remain `RelOL.Generic.InstanceExamples`,
`RelOL.Generic.TraceExamples`, and `RelOL.Generic.AsyncExamples`, respectively.

## Randomized search

Import `RelationalOutcomeLogic.Examples.Probability.Search.Case` for the randomized-search commands,
correctness results, quantitative contract, trial savings, and bug certificate.
The two main statements use the same initial weights and postcondition:

```lean
import RelationalOutcomeLogic.Examples.Probability.Search.Case

open RelOL RelOL.Prob RelOL.Prob.Search

example (T : Trial) (n : ℕ) :
    quad (exactly (seed n) (seed n)) (full T) (early T) (resultSpec T n) :=
  search_outcome_quad T n

example (T : Trial) (hzero : 0 < T.miss) (hone : T.miss < 1)
    {n : ℕ} (hn : 1 < n) :
    ¬ quad (exactly (seed n) (seed n)) (full T) (cached T) (resultSpec T n) :=
  cached_outcome_spec_refuted T hzero hone hn
```

`resultSpec` gives both the failure piece of mass `miss^n` and the success piece,
with answer and consumed-trial relations. `resultSpec_mass_one` derives normalization;
`resultSpec_couple` forgets quantitative details to recover answer agreement;
`resultSpec_observed_eq` derives equality after projecting to the answer flag.
The [case-study explanation](randomized-search.md) describes the programs and bounds.

## Buffered speculative decoding

Import `RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Case`.
The [case guide](speculative-decoding.md) explains the model, proof dependencies,
documented failure provenance, and exact limits of the cost and privacy claims.
Names below are relative to `RelOL.Prob.Speculative`.

| Result | Main declaration |
| --- | --- |
| Accepted/corrected quantitative split, including arbitrary input mass | `step_outcome_quad_mass`, `step_outcome_quad` |
| Local distributional buffer invariant and its recursive derivation | `BufferRefinement.step_quad`, `BufferRefinement.verifier_quad` |
| Eager buffer equals delayed sampling, including traces | `buffered_eq_delayed` |
| Local continuation contracts derive the complete adaptive decoder | `delayed_quad_family`, `decoder_quad_family`, `decoder_outcome_quad` |
| Exact target law and independence of sufficient round fuel | `run_output`, `decode_fuel_irrelevant`, `decode_eq_run` |
| Every first-rejection case retains its exact mass | `RoundLaw.round_count_quad`, `RoundLaw.countSpec_mass_one` |
| History-dependent expected acceptance and emission | `RoundLaw.expected_accepted`, `RoundLaw.expected_emitted` |
| Joint counts and expected emission at a clipped output budget | `RoundLaw.roundWithBudget_stats`, `RoundLaw.expected_emitted_clipped` |
| Geometric specialization under constant conditional overlap | `RoundLaw.expected_emitted_geometric`, `RoundLaw.expected_emitted_clipped_geometric_sum` |
| Actual output and operation accounting | `decode_accounted`, `expected_targetCalls_le`, `expected_draftTokens_le` |
| Exact expected rounds for two tokens and an arbitrary draft | `expected_two_token_calls` |
| Perfect width-K draft emits K+1 tokens in one round | `perfect_single_round`, `expected_perfect_single_round_calls` |
| Wrong fallback violates the same split contract | `wrongFallback_outcome_contract_refuted` |
| Documented bonus-source failure, abstracted as a sampler | `Implementation.bonus_output_contract_refuted` |
| Arbitrary acceptance gaps refute streaming privacy while payload laws agree | `acceptanceGapPacketLeak`, `acceptance_gap_contract_refuted`, `run_payload_private` |
| Buffered release preserves payloads and hides the modeled packet observation | `bufferedRelease_law`, `bufferedRelease_private` |

The proof starts with local sampling identities in `Correction.lean`.
`StepContract.lean` derives the quantitative sampler contract using sequencing and
additive choice; the decoder consumes its consequence for token observations.
`Refinement.lean` lifts the conditional buffer law to a distributional invariant,
then composes its local transition and dispatch rules. `DecoderRules.lean` applies
the shared sequencing and indexed-family recursion rules to arbitrary
continuations satisfying smaller-budget contracts. Output equality is a consequence
of this derivation. `OutcomeContracts.lean` exposes the resulting pRelOL judgments,
including output agreement, completion, and accounting.

The quantitative round contract is a finite additive decomposition. It records
every first-rejection case and complete acceptance, including cases of zero mass.
Expected counts follow from joint prefix-survival probabilities. Geometric formulas
require `RoundLaw.ConstantConditionalOverlap` along supported accepted histories;
an empirical average acceptance rate does not provide that premise. Clipping
preserves the joint acceptance/emission law and handles a final accepted token
that exhausts the budget without a bonus.

`Fuel.lean` proves equality of the entire run distribution, including traces, once
round fuel covers the output budget. This uses bounded recursion rather than a new
unbounded-loop semantics. The generic privacy theorem concerns arbitrary target
and draft models with unequal acceptance masses; the Boolean witness instantiates
it. Its token-count observer excludes timing and encoded byte sizes.

The reusable additions are `Generic.Distributional`, `Generic.Loops.Bounded`,
`Prob.Logic.FiniteOutcomes`, and the ENNReal sequencing/expectation modules. They
derive proof rules from existing semantics. The case guide distinguishes these
compositional interfaces from established sampling identities and from claims
about algorithmic novelty or verified external implementations.

## Choose the level of judgment

All entries below are in `RelOL.Prob` unless qualified otherwise.

| Need | Definition or theorem | Import |
| --- | --- | --- |
| Arbitrary weighted outcome transformers, possibly with different input/output types | `quadSem F G P Q` | `Prob.Logic.Judgment` |
| Commands with weighted pre/postconditions | `quad P c d Q` | `Prob.Semantics.Commands` |
| Pointwise exact-coupling correctness | `prhl R c d S`, `prhlSem` | `Subsumption.PRHL.Embedding` |
| Transfer between pointwise correctness and weighted assertions | `prhl_iff_quad`, `prhlSem_iff_quadSem` | `Subsumption.PRHL.Embedding` |
| Preserve branch masses while splitting a joint | `IsCoupling.restrict`, `Coupled.split_mass` | `Prob.Coupling.Restriction` |
| Retain and compose a finite additive family of outcomes | `finiteCases`, `finiteCases_massEq`, `quadSem_finiteCases` | `Prob.Logic.FiniteOutcomes` |
| Project outputs through deterministic observations | `pushforward`, `Coupled.pushforward` | `Prob.Coupling.Observation` |
| Transport whole outcome judgments to observations | `quadSem.observe` | `Prob.Refutation.Observation` |
| Refute correctness with a quantitative witness | `MassDeficitCert.refutes`, `BugCert.refutes` | `Prob.Refutation.Certificate` |
| Refute a richer contract using an observed-output certificate | `BugCert.refutes_of_observation` | `Prob.Refutation.Observation` |

Prefix the import column with `RelationalOutcomeLogic.`. The root
`RelationalOutcomeLogic` import also exposes the entire development.

The pRHL bridge is semantic equivalence for the implemented command language, with
named admissible rules. It supplies no external procedure/module semantics or proof
script translation. This is the scope to match when integrating another mechanization.

## Observation and refutation

`pushforward f μ` aggregates the weight of all states with the same observed value.
It preserves total mass, addition, scaling, and increasing limits. The observation
need not be injective, and no normalization is performed.

`Coupled.pushforward` transports a relation-supported joint through a left and right
observation when related states give related observations. `quadSem.observe` applies
this idea to a whole specification via a postcondition implication.

For a certificate on the observed outputs of `F` and `G`,
`BugCert.refutes_of_observation` requires two proofs:

1. Its concrete initial weights satisfy the original precondition.
2. The original postcondition implies the observed coupling that the certificate refutes.

It then refutes the original judgment, including postconditions with additional mass
or resource constraints. It makes no converse claim that equal observations determine
the internal outputs. The search client uses this bridge to refute `resultSpec` for
the cached command. The certificate's larger failure mass is on the cached side;
the client reverses the observed equality when presenting full scan on the left.

## Loop rules and their obligations

| Rule | Required premises | Result |
| --- | --- | --- |
| `prhl_while` | Guards agree on the invariant; bodies preserve it by coupling | Exact output coupling with invariant and both exit conditions |
| `prhl_while_left` / `prhl_while_right` | Invariant preservation and whole-loop losslessness on the relevant starts | Loop versus skip |
| `prhl_while_async` | Local joint/unilateral couplings; a natural rank strictly decreases on every supported unilateral step | Exact terminal marginals of the selected product loop |
| `Generic.quad_boundedRec` / `quad_recursion_family` | Base contracts and local layer rules for arbitrary continuations satisfying the previous contracts | A finite recursive derivation, optionally retaining an indexed family of pre/postconditions |

The mixed rule permits joint divergence and arbitrary rank resets on joint steps.
It does not cover unbounded stochastic unilateral phases merely from almost-sure
termination. See [loop alignment](loop-alignment.md) for boundary examples.

## Claims and validation

The search case supplies an end-to-end correctness contract and its quantitative
refutation. Shared structural proofs instantiate with Set and ENNReal; the scalar
factory constructs the weighted algebra and proves coupling, certificate, and loop
theorems for all five instances. Compatibility theorems connect the new constructions
to existing APIs. Model-specific normalization and probability examples retain their
concrete statements. Completeness is not a goal.

A bare semiring is insufficient for unrestricted sums or loops. The current factory
requires total summation and, for loops, the stated order and increasing-limit laws.
It does not implement every partial weight algebra from TOPLAS, mixed probabilistic
and demonic choice, continuous distributions, or infinite-word observations.

Finite-event certificates require a strict gap in the scalar order. Distinct weights
can be incomparable, as with two different singleton trace languages; the trace client
instead refutes equality coupling through the generic equality characterization.

Run `./scripts/check.sh` for the full build, proof-placeholder scan, and axiom gate.
Every production module is imported by the root. The allowed axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The gate verifies Lean declarations; the paper's
presentation and the choice of modeling assumptions still require source review.
The integrated generalization check passed on 2026-09-21: 1,613 build jobs and 3,088
library declarations, no proof placeholders, and only these standard axioms.

After the structure pass on 2026-09-22, the full gate passed with 1,628 build jobs
and 3,090 declarations. The structure check covers 106 modules, and the API comparison
preserved every public mathematical declaration name. The two additional declarations
are generated simplification helpers, not new logic rules.

After adding speculative decoding on 2026-09-22, the full gate passed with 1,639
build jobs, 117 source modules, and 3,510 audited declarations. No proof placeholders
or nonstandard axioms were found. The case guide separates mechanized guarantees
from external implementation, encoding, and timing claims.

After strengthening the case on 2026-09-22, the full gate passed with 1,651 build
jobs, 127 source modules, and 3,836 audited declarations. It covers the derived
buffer/decoder proofs, full-trace fuel independence, general and clipped round
laws, concrete geometric clients, and generalized privacy certificates. No proof
placeholders or nonstandard axioms were found.
