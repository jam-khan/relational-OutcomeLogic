# pRHL subsumption: theorem, rules, and scope

The mechanization proves that exact-coupling pRHL is the coupling-assertion fragment
of pRelOL. Both use the existing probabilistic commands and their terminating
output weights; no second command semantics is introduced.

The concrete bridge and core rules live in `Subsumption/PRHL/Embedding.lean`,
one-sided rules in `Subsumption/PRHL/OneSided.lean`, and ranked mixed rules in
`Subsumption/PRHL/Asynchronous.lean`. Examples live separately under
`Examples/Subsumption/ProbabilisticHoare.lean`. Rules retain the `RelOL.Prob`
namespace; the examples retain `RelOL.Prob.PRHLExamples`.

## Semantic bridge

In namespace `RelOL.Prob`:

```lean
prhl R c d S := ∀ a b, R a b → Coupled S (sem c a) (sem d b)

prhl_iff_quad : prhl R c d S ↔ quad (couple R) c d (couple S)
```

The definition unfolds through `prhlSem`, which also accepts arbitrary discrete
kernels with different input and output types. `prhlSem_iff_quadSem` establishes the
same equivalence for their bind extensions. Pointwise proofs lift by coupling bind;
weighted proofs specialize to related point masses. The weighted side quantifies over
all coupled raw input weights, including weights with mass greater than one.

Command outputs from individual states are subprobabilities. Couplings have exact
marginals, so both sides must have equal termination probability. Divergence is
permitted on both sides. This is not a divergence-insensitive lifting.

## Shared semiring bridge

`Generic/Coupling.lean` now proves `RelOL.Generic.prhl_iff_quad` for the weights
constructed from any `SummationSemiring K`. Here `prhl R k l S` is the statewise
exact-coupling judgment for kernels; its equivalent outcome judgment uses the shared
assertion and sequencing algebra. Coupling composition is proved from scalar summation
laws and does not require commutative multiplication.

`Generic/Loops/Synchronous.lean` and `Generic/Loops/Asynchronous.lean` expose the corresponding
`Generic.prhl_while` and `Generic.prhl_while_async` under the explicit ordered,
increasing-limit assumptions. Both construct a product execution and prove its exact
marginals. `Algebra/Weighted/Events.lean` supplies finite-event bounds, while
`Generic/Refutation.lean` packages finite-event and concrete-input refutations in
each scalar's order. [Semiring models](semiring-models.md) gives the
five checked instances and their concrete clients.

The ENNReal specialization is linked to the existing APIs by
`Generic.ennreal_couple_eq`, `ennreal_prhl_iff`, and `ennreal_prhl_commands_iff` in
`Bridges/Probability.lean`. The rule inventory below remains the concrete
`RelOL.Prob` command API, including its normalized sampling and whole-loop losslessness
rules. The generic kernel development does not claim a new normalized language for
every scalar instance.

## Exposed rule inventory

| Rule | Lean theorem | Main obligation |
| --- | --- | --- |
| Skip | `prhl_skip` | Same input/output relation |
| Consequence | `prhl_consequence` | Strengthen the precondition, weaken the postcondition |
| Paired assignment | `prhl_assign` | Updates establish the output relation |
| Paired sampling | `prhl_sample` | Normalized kernels and pointwise output couplings |
| Sequencing | `prhl_seq` | A shared intermediate relation |
| Synchronized conditional | `prhl_ite` | Guards agree on related inputs; both branches satisfy the postcondition |
| Synchronous while | `prhl_while` | Guards agree on the invariant; bodies preserve it on guarded inputs |
| Case analysis / false precondition | `prhl_case`, `prhl_false` | Both relational cases / no possible starting pair |
| Semantic replacement | `prhl_congr` | Equality of each replaced command's state-indexed semantics |
| Symmetry | `prhl_symm` | Reverse the programs and both relations |
| One-sided assignment | `prhl_assign_left`, `prhl_assign_right` | Update one state against skip |
| One-sided sampling | `prhl_sample_left`, `prhl_sample_right` | Normalization and relation preservation throughout the sample support |
| One-sided conditional | `prhl_ite_left`, `prhl_ite_right` | Each guarded branch relates to the other command |
| One-sided while | `prhl_while_left`, `prhl_while_right` | Body preserves the relation against skip; whole loop is lossless on relevant starts |
| Ranked mixed while | `prhl_while_async` | Local left/right/joint couplings; strict natural-rank descent on supported unilateral steps |

The synchronous while postrelation includes the invariant and both negated guards.
Its proof does not require termination. In the left-only while rule, the postrelation
is `R a b ∧ ¬ g a` and the losslessness premise is:

```lean
LosslessOn (fun a => ∃ b, R a b) (.while g c)
```

The right-only rule uses the opposite projection. `LosslessOn P c` means that
`sem c a` has mass one whenever `P a`. Losslessness of the body alone is insufficient:
`while True do skip` has a mass-one body but zero terminating output mass.

## Correctness and refutation examples

`Examples/Subsumption/ProbabilisticHoare.lean` checks:

1. Opposite Boolean encodings of unbounded fair-coin retry, using `prhl_sample` and
   `prhl_while`, then exporting the proof through `prhl_iff_quad`.
2. Unbounded retry against a passive `Unit` state in both directions, using the
   one-sided while rules and a separate proof of whole-loop losslessness.
3. Sampling followed by assignment, using `prhl_seq`.
4. Failure of a divergent loop versus skip even under a universally true postrelation,
   despite the body being lossless and invariant-preserving.
5. A fair versus biased sampling specification rejected by the existing finite-event
   mass-deficit certificate through `MassDeficitCert.refutes_prhl`, and an equal-input
   specification rejected through a command-indexed `BugCert.refutes_prhl`.

`BugCert.refutes_prhl` also accepts program-level certificates whose transformers
are the commands' lifted semantics. Both refutation methods require an input pair
satisfying the pRHL precondition. Failure to find a correctness proof does not itself
produce a certificate.

The [search case](randomized-search.md) also bridges observed-output certificates
back to richer weighted contracts. `BugCert.refutes_of_observation` refutes an
internal postcondition that requires the failed observed coupling. This lets the
cached-randomness example fail exactly the quantitative contract proved for early
exit, with the concrete input precondition checked. The [theorem guide](theorem-guide.md)
provides client imports and the two statements.

## What has and has not been embedded

This milestone supplies semantic equivalence and named admissible rules for skip,
assignment, normalized discrete sampling, sequencing, conditionals, and while.
Examples are Lean proofs composed from these rules. There is no inductive derivation
datatype or theorem translating a separate syntactic proof calculus yet.

Guarded block unrolling and ranked mixed asynchronous loops are now implemented;
see the [alignment theorems and their limits](loop-alignment.md). The ranked rule
allows joint divergence, while unilateral phases must decrease the chosen natural rank.

There is also no embedding of external procedure, module, oracle, or call semantics,
and no compatibility claim for external proof scripts. The generic kernel bridge is
a possible integration point once an external development exposes matching semantics.
It does not by itself establish such a match. Arbitrary fair or almost-sure phase
scheduling, approximate couplings, and continuous distributions remain outside the
present theorem. Generic-semiring coupling, certificates, and ranked loop rules are
now implemented under explicit assumptions; this does not provide every partial
weight algebra or external language feature. The semantics is denotational; no separate operational
semantics or operational adequacy theorem has been supplied.
