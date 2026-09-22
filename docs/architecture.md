# pRelOL source architecture

The logic is named **Probabilistic Relational Outcome Logic (pRelOL)**. The Lean
package remains `RelationalOutcomeLogic`, and declaration namespaces remain
`RelOL`; the display-name change does not require rewriting client proofs.

The source tree separates algebra, logic, concrete models, embeddings, and clients.
The reorganization changes module paths while retaining mathematical declaration
names and namespaces. For example, the search case now lives under
`Examples/Probability/Search/`, and its declarations remain in `RelOL.Prob.Search`.

## Directory map

```text
RelationalOutcomeLogic/
├── Algebra/
│   ├── Outcome/       Basic, Iteration: outcome interfaces
│   ├── Scalar/        Basic, Order: scalar and summation laws
│   ├── Weighted/      Basic, Outcome, Iteration, Coupling, Observation, Events
│   ├── ENNReal/       Basic, Limits, Sequencing, Expectation
│   ├── Instances/     Boolean, Probability, Counting, Tropical, Language
│   └── Alignment.lean
├── Generic/
│   ├── Assertions.lean, Judgment.lean, Rules.lean
│   ├── Coupling.lean, Distributional.lean, Refutation.lean
│   └── Loops/         Semantics, Support, Bounded, Synchronous, Asynchronous
├── Set/
│   ├── State.lean, Semantics.lean, Language.lean, Exceptions.lean
│   ├── Assertions.lean, Coupling.lean, Judgment.lean, Rules.lean
│   ├── Metatheory.lean, Refutation.lean
│   └── Loops/         Asynchronous
├── Prob/
│   ├── Semantics/     Commands, Loop
│   ├── Coupling/      Basic, Assertions, Observation, Restriction, Support,
│   │                  SynchronousLoop, AsynchronousLoop
│   ├── Logic/         Assertions, Judgment, Rules, OneSided, FiniteOutcomes
│   ├── Refutation/    EventMass, Certificate, Observation
│   └── Transformations/ GuardedUnroll
├── Subsumption/
│   ├── OL/            Assertions, Judgment, Embedding
│   ├── PRHL/          Embedding, OneSided, Asynchronous
│   └── RHL.lean
├── Bridges/           Set, Probability, Boolean
├── Examples/
│   ├── Set/           Noninterference/, AsynchronousCountdown
│   ├── Probability/   Coins, MassDeficit, GeometricRetry, RetryCoupling,
│   │                  GuardedUnrolling, AsynchronousLoops, AlgebraBoundaries
│   │   ├── Search/    Programs, Alignment, OutcomeContract, Cost,
│   │                  CachedRandomness, Case
│   │   └── SpeculativeDecoding/  Programs, Correction, StepContract, Refinement,
│   │                  DecoderRules, Buffered, Fuel, Costs, OutcomeContracts, RoundLaw,
│   │                  RoundExpectation, RoundClipping, Counterexamples,
│   │                  Security, Implementation, Case
│   ├── Algebra/       Routes, Countdown, AsynchronousCountdown, Traces
│   ├── Subsumption/   Allocation, ProbabilisticHoare
│   ├── Translation/   Languages, Refinement, Overflow, Loops
│   └── Compiler/      Lowering, Correctness
└── Tactic/            Symexec
```

Matching `.lean` files for `Algebra`, `Generic`, `Set`, `Prob`, `Subsumption`,
`Bridges`, and `Examples` import their component modules. `Subsumption/OL.lean`
and `Subsumption/PRHL.lean` are also entry points. The root module imports all
layers and examples; narrow imports can avoid unrelated developments.

## Dependency boundaries

`Algebra/` contains mathematical interfaces and constructions; it does not depend
on program logics. `Generic/` depends only on itself, `Algebra/`, and Mathlib.
Concrete Set and probabilistic semantics and rules live in their own directories.
`Subsumption/` gives the embedded logics, while `Bridges/` proves agreement between
the generic and concrete developments. Examples sit above the library layers.
No library module imports an example.

The [speculative-decoding case](speculative-decoding.md) is self-contained under
`Examples/Probability/SpeculativeDecoding/`. Its reusable additions have explicit
library boundaries:

| Module | Reusable interface |
| --- | --- |
| `Algebra/ENNReal/Sequencing.lean`, `Expectation.lean` | Independent sampling, normalized discard, and nonnegative expected costs |
| `Generic/Distributional.lean` | Conditional reconstruction invariants and local refinement rules, including dispatch |
| `Generic/Loops/Bounded.lean` | Bounded sequencing and recursion rules, with indexed families of continuation contracts |
| `Prob/Logic/FiniteOutcomes.lean` | Finite additive outcome cases, their masses, and composition through additive transformers |

`Correction.lean` proves the local accept/correct sampling identities.
`StepContract.lean` derives their quantitative outcome contract using sequencing
and additive choice. The decoder consumes its token-observation consequence.
`Refinement.lean` uses a conditional reconstruction invariant and the shared
sequencing, dispatch, and recursion rules to verify the eager random buffer.
`DecoderRules.lean` derives the complete decoder contract from local sampler and
continuation contracts. `Buffered.lean` exposes normalization, length, and output
corollaries; `Fuel.lean` proves equality of complete run distributions for any two
sufficient fuel bounds. The executable kernels remain in `Programs.lean`.

`RoundLaw.lean` retains each first-rejection outcome and its history-dependent
survival mass. `RoundExpectation.lean` derives expected counts, and
`RoundClipping.lean` handles finite remaining budgets, including zero budget and
suppressed bonus tokens. `Security.lean` proves a generic acceptance-gap privacy
refutation and instantiates it with the Boolean example. These results reuse the
existing judgment and additive semantics; the new rules are derived from their
laws. Algorithmic novelty and external implementation correspondence are separate
claims whose scope is recorded in the detailed case guide.

Inside the probabilistic development, observation and coupling operations are
separate from judgments and certificates. `Prob/Coupling/AsynchronousLoop.lean`
uses semantic and coupling infrastructure without importing refutation code or
one-sided command rules. The `Prob/Coupling/Support.lean` module explicitly connects
weighted coupling to Set support coupling; ordinary weighted coupling does not
require that bridge.

The generic development has the same separation: finite-event algebra is in
`Algebra/Weighted/Events.lean`, pushforward is in `Algebra/Weighted/Observation.lean`,
and certificates are in `Generic/Refutation.lean`. Loop support lemmas have their
own `Generic/Loops/Support.lean` module. Generic judgment definitions are separate
from their proof rules.

The concrete ENNReal foundation remains available because it supports the concrete
probabilistic API, including its universe-polymorphic state types and direct Mathlib
summation laws. The generic scalar interfaces parameterize a carrier universe.
`Bridges/Probability.lean` proves the relevant agreements. Merging these APIs would
be a further mathematical/API change, beyond reorganizing the implementation.

Set RHL remains one file because its universal-pair postconditions and pRHL's
existential exact couplings express different specifications. Unary OL has a small
self-contained directory; its worked allocation example is under `Examples/`.
The compiler and translation cases share `Set/Exceptions.lean`, so the compiler
case no longer needs to import the translation language.

## Import migration

Prefix dotted imports with `RelationalOutcomeLogic.`. These are the main changes:

| Previous path | Current path |
| --- | --- |
| Top-level `Basic`, `Kleisli`, `Lang`, `Quadruple` | `Set.State`, `Set.Semantics`, `Set.Language`, `Set.Judgment` |
| Top-level Set assertions, rules, coupling, metatheory | Corresponding modules under `Set` |
| `Algebra.OutcomeModel`, `Algebra.IterationModel` | `Algebra.Outcome.Basic`, `Algebra.Outcome.Iteration` |
| `Algebra.Scalar`, `Algebra.OrderedScalar` | `Algebra.Scalar.Basic`, `Algebra.Scalar.Order` |
| `Algebra.Weighted*` | Modules under `Algebra.Weighted` |
| `Algebra.Weight`, `Algebra.WeightOrder` | `Algebra.ENNReal.Basic`, `Algebra.ENNReal.Limits` |
| `Generic.WeightedLogic`, `Generic.WeightedCertificates` | `Generic.Coupling`, `Generic.Refutation` |
| `Generic.Iteration`, `Generic.LoopCoupling`, `Generic.AsyncLoop` | `Generic.Loops.Semantics`, `Synchronous`, `Asynchronous` |
| `Generic.Concrete`, `Generic.Compatibility` | `Bridges.Set` and `Bridges.Probability`, according to the model |
| `Generic.BooleanBridge` | `Bridges.Boolean` |
| Flat `Prob` modules | Subdirectories shown above; examples under `Examples.Probability` |
| `Prob.Observation` | `Prob.Coupling.Observation` for transport; `Prob.Refutation.Observation` for certificates |
| `Prob.SearchCase` | `Examples.Probability.Search.Case` |
| `Subsumption.PRHLOneSided`, `Subsumption.PRHLAsync` | `Subsumption.PRHL.OneSided`, `Subsumption.PRHL.Asynchronous` |
| `Unary` modules | `Subsumption.OL.Assertions` and `Subsumption.OL.Judgment` |
| `Hetero`, `Compiler`, generic example modules | Their corresponding directories under `Examples` |

Existing `Subsumption.OL` and `Subsumption.PRHL` imports now load their complete
fragments. The full root import remains supported. Other moved paths have no
forwarding stubs: update narrow imports to the new location. The
[theorem guide](theorem-guide.md) and [study index](study/theorem-index.md) link to
current files. Example namespace names intentionally remain stable even where a
file now has a clearer name.

## Adding or moving code

Put reusable algebra below the logic, model-independent logic in `Generic/`, and
worked programs in `Examples/`. Import the module from its component entry point;
the component is already imported by the root. Avoid making library helpers depend
on a case study just to reuse one lemma.

Run `./scripts/check.sh`. It checks missing source imports, import cycles, root
coverage, and the layer boundaries above before building. This prevents obsolete
compiled files from hiding a missing source after a move. It then rejects proof
placeholders and audits every imported library declaration for nonstandard axioms.
CI runs the same gate. Rebuild `paper/main.pdf` with `./scripts/build-paper.sh`
and the study PDF with `./scripts/build-study.sh`. Both scripts build in a temporary
directory and copy back only the finished PDF, keeping auxiliary files out of the
source tree.
