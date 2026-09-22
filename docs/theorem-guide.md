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

## Start with the complete case

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

## Choose the level of judgment

All entries below are in `RelOL.Prob` unless qualified otherwise.

| Need | Definition or theorem | Import |
| --- | --- | --- |
| Arbitrary weighted outcome transformers, possibly with different input/output types | `quadSem F G P Q` | `Prob.Logic.Judgment` |
| Commands with weighted pre/postconditions | `quad P c d Q` | `Prob.Semantics.Commands` |
| Pointwise exact-coupling correctness | `prhl R c d S`, `prhlSem` | `Subsumption.PRHL.Embedding` |
| Transfer between pointwise correctness and weighted assertions | `prhl_iff_quad`, `prhlSem_iff_quadSem` | `Subsumption.PRHL.Embedding` |
| Preserve branch masses while splitting a joint | `IsCoupling.restrict`, `Coupled.split_mass` | `Prob.Coupling.Restriction` |
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
