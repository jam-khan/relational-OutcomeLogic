# Relational Outcome Logic

A Lean 4 mechanization of Relational Outcome Logic: judgments over pairs of outcome
sets or discrete weighted outcomes. A shared algebra supports Boolean reachability,
probability weights, trace counts, minimum costs, and finite trace languages.
The Set development includes programs in different languages; the probabilistic
development uses a shared command language with possibly different state types.

```
./scripts/check.sh    # build, no sorry, standard axioms only
```

Start with the [theorem guide](docs/theorem-guide.md) for imports and the main APIs.
The [semiring models guide](docs/semiring-models.md) explains the shared algebra,
five proved instances, program examples, and their precise relation to the TOPLAS models.
`RelationalOutcomeLogic.Prob.SearchCase` exposes the complete search example:
`search_outcome_quad` proves its quantitative contract for early exit;
`cached_outcome_spec_refuted` refutes the same contract for cached randomness.

| File | Content |
| --- | --- |
| `Algebra/OutcomeModel.lean`, `Algebra/IterationModel.lean` | Common additive outcome algebra and assumptions for least-fixed-point loops |
| `Algebra/Scalar.lean`, `Algebra/OrderedScalar.lean` | Semiring summation, optional positivity, and increasing-limit laws |
| `Algebra/Weighted.lean`, `Algebra/WeightedModel.lean`, `Algebra/WeightedOrder.lean` | Weighted sequencing and outcome/iteration instances derived from scalar laws |
| `Algebra/WeightedCoupling.lean` | Exact marginal couplings and composition over possibly noncommutative semirings |
| `Algebra/Instances/` | Boolean reachability, ENNReal weights, ENat counts, tropical costs, and finite-word languages |
| `Generic/Assertions.lean`, `Generic/Rules.lean` | Shared judgments, additive splitting, and structural proof rules |
| `Generic/Iteration.lean`, `Generic/LoopCoupling.lean`, `Generic/AsyncLoop.lean` | Shared least-fixed-point semantics, synchronous coupling, and ranked asynchronous rules |
| `Generic/WeightedLogic.lean`, `Generic/WeightedCertificates.lean` | Semiring-parametric relational coupling logic and quantitative refutation certificates |
| `Generic/Concrete.lean`, `Generic/Compatibility.lean`, `Generic/BooleanBridge.lean` | Proved connections to existing Set and probabilistic developments |
| `Generic/WeightedPrograms.lean`, `Generic/InstanceExamples.lean` | One route/countdown proof across models; counting and cost error certificates |
| `Generic/AsyncExamples.lean`, `Generic/TraceExamples.lean` | Shared weighted asynchronous client and noncommutative logging examples |
| `Algebra/Alignment.lean` | Shared left/right/joint/exit modes |
| `Algebra/Weight.lean` | Raw nonnegative weights; sequencing, support, scaling, mass bounds |
| `Algebra/WeightOrder.lean` | Increasing-limit laws and omega-continuity of weighted sequencing |
| `Algebra/WeightBoundary.lean` | Counterexamples to set-specific algebraic and arbitrary-supremum laws |
| `Prob/Assertions.lean` | Weighted assertions, additive splitting, scaling, and mass constraints |
| `Prob/Coupling.lean` | Joint weights with exact marginals; equality, addition, scaling, and sequencing |
| `Prob/CouplingAssertions.lean` | Coupling assertions and additive structural rules |
| `Prob/Support.lean` | Exact weighted couplings imply the existing Set support coupling |
| `Prob/Examples.lean` | Fair/biased coins, termination mass, splitting, and coupling composition |
| `Prob/EventMass.lean` | Finite-event mass and the necessary mass bound for exact couplings |
| `Prob/Quadruple.lean` | Language-independent judgments over weighted outcome transformers |
| `Prob/BugCert.lean` | Quantitative deficit certificates and sound refutation of coupling specifications |
| `Prob/Observation.lean` | Deterministic observations, coupling transport, and refutation of original contracts from observed certificates |
| `Prob/CertificateExamples.lean` | Coin-bias certificates, additive specifications, and sampling counterexamples |
| `Prob/Loop.lean` | Increasing loop approximations, least fixed points, and subprobability preservation |
| `Prob/Lang.lean` | Probabilistic commands with normalized sampling and weighted semantics |
| `Prob/LoopCoupling.lean` | Coherent product-loop construction with exact marginal limits |
| `Prob/Rules.lean` | Structural, sampling, conditional, and synchronous coupling loop rules |
| `Prob/OneSided.lean` | Coupling against point masses, losslessness, and one-sided loop rules |
| `Prob/Unroll.lean`, `Prob/UnrollExamples.lean` | Guarded block unrolling, probabilistic correctness, and a certified extra-sample bug |
| `Prob/AsyncLoop.lean` | Ranked mixed scheduling with proved exact terminal marginals |
| `Prob/AsyncExamples.lean` | Unequal strides, aligned random draws with control catch-up, and progress/mass boundaries |
| `Prob/Restriction.lean` | Restricting a joint coupling into exact quantitative outcome pieces |
| `Prob/Search.lean`, `Prob/SearchCoupling.lean` | Parameterized randomized search and asynchronous correctness of early exit |
| `Prob/SearchOutcome.lean`, `Prob/SearchCost.lean` | Exact success/failure masses, coupled trial bounds, and positive probability of strict savings |
| `Prob/SearchCertificates.lean` | Cached-randomness bug certified for every nondegenerate trial and budget above one |
| `Prob/SearchCase.lean` | Complete case import and refutation of the same quantitative contract proved for early exit |
| `Prob/Geometric.lean`, `Prob/LoopExamples.lean` | Unbounded coin-retry loops, almost-sure termination, relational correctness, and divergence |
| `Subsumption/PRHL.lean` | Exact-coupling pRHL equivalence, core rules, and certificate refutation |
| `Subsumption/PRHLOneSided.lean` | One-sided assignment, sampling, conditionals, loops, and symmetry |
| `Subsumption/PRHLAsync.lean` | Weighted and pRHL mixed while rules and scheduler symmetry |
| `Subsumption/PRHLExamples.lean` | Synchronous and one-sided unbounded-loop proofs and a certified probability mismatch |
| `Kleisli.lean` | Kleisli extension over the powerset monad; Kleene iteration for loops |
| `Lang.lean` | the while-language, its semantics, program notation |
| `Assertions.lean` | `atom`, `atomW`, `⊕`, infinitary `⊕`, entailment |
| `Coupling.lean` | `couple`, `coupleL`, `coupleNE`; the `⊕`-collapse; lifting through bind and loops |
| `Quadruple.lean` | `quadSem`, `quad`, assertion notation |
| `Rules.lean` | the proof rules: structural, product tier, While-Fam, coupling tier |
| `Async.lean`, `Examples/Async.lean` | Ranked mixed Set coupling and a countdown client with different strides |
| `Metatheory.lean` | falsification, denial, failure modes, strongest posts, Seq (in)completeness |
| `BugCert.lean`, `Tactic/Symexec.lean` | certificate objects; the `symexec` tactic |
| `Unary/`, `Subsumption/OL.lean`, `Subsumption/RHL.lean` | unary OL and Set RHL as fragments |
| `Hetero/` | a C-like and a Rust-like language under one judgment; refinement |
| `Compiler/` | a verified exceptions-to-error-codes pass |
| `Examples/` | NI, GNI, coupling NI, translation bugs, miscompilation certificates |

The current development is on `prototype-3`. Branches `prototype` and `prototype-2`
are frozen references.

The concrete weighted foundation, assertions, exact-marginal couplings, quantitative
refutation certificates, and probabilistic while-language are implemented alongside
the Set logic. Their mass and nontermination conventions are fixed in the
[semantic contract](docs/weighted-semantics.md).
Synchronous loop coupling is proved using one coherent product execution. The
[pRHL embedding](docs/prhl-subsumption.md) identifies exact-coupling pRHL with the
coupling-assertion fragment of weighted RelOL, exposes core and one-sided rules,
and lets quantitative certificates refute pRHL specifications. One-sided loops require
explicit whole-loop losslessness. [Loop alignment](docs/loop-alignment.md) adds guarded
unrolling and ranked mixed scheduling with proved marginal preservation.
The [randomized-search case study](docs/randomized-search.md) combines asynchronous
correctness, quantitative outcome splitting, consumed-trial bounds, and a certified
faulty variant with the same possible answers.
The [shared algebra and semiring models](docs/semiring-models.md) now generalize
sequencing, exact couplings, quantitative certificates, and loop reasoning, with
five concrete instances and compatibility proofs for the existing developments.
The [current roadmap](typeclass-plan.md) records remaining consolidation and optional
automation work; completeness is not a target.
