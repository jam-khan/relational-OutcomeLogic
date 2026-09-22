# Guarded unrolling and ranked asynchronous loops

The alignment development has two distinct results: a semantics-preserving block
transformation and mixed left/right/joint execution with proved terminal marginals.
The latter is now proved generically over admissible ordered summation semirings,
as well as being available through the existing Set and probability APIs.

## Guarded two-iteration unrolling

`Prob.sem_guarded_unroll` proves equality of the state-indexed semantics of:

```text
while g do c
while g do (c; if g then c else skip)
```

The kernel-level theorem works for arbitrary raw weights. It assumes neither
normalization nor termination. `loopIter_guardedDouble_succ` identifies positive-fuel
approximations of the transformed loop with original approximations at indices
`2 * n + 1`. These indices are cofinal, so the increasing limits agree. Both programs
therefore preserve the same divergence mass as well as terminating outputs.

`Prob.UnrollExamples` uses a countdown and a Boolean accumulator updated by OR with a
fresh fair bit. A pRHL sampling/while proof and semantic replacement establish guarded
unrolling correctness for every starting count and accumulator. A separate induction
proves mass one for every finite count, so the example is not only a partial-correctness
statement about possibly empty outputs.

The faulty version omits the inner guard. Starting at count one and false, it takes
two samples instead of one. After projecting away the counter, false has probability
one quarter instead of one half; both Boolean supports remain identical. An actual
`MassDeficitCert` and program-indexed `BugCert` refute the equality-coupling specification
on these observed outputs. The certificate concerns the full loop outputs, not a
bounded underapproximation.

## Mixed scheduling

`AsyncMode` has four values: `left`, `right`, `both`, and `done`. The probabilistic
`AsyncSchedule R g h k l` supplies a selector and a natural-valued rank, together with
local obligations at states satisfying the relational invariant:

| Mode | Required local behavior |
| --- | --- |
| Left | Left guard enabled; couple the left body with the unchanged right point mass; preserve the invariant and strictly decrease rank |
| Right | Symmetric obligation |
| Both | Both guards enabled; exactly couple the two bodies and preserve the invariant |
| Done | Both guards false |

One-sided exact coupling to a point mass forces the advancing body to have total mass
one. The rank decreases on every supported unilateral successor. Joint steps may reset
it to any natural number. This proves progress through unilateral phases without a
uniform rank bound across all states and without assuming that the entire joint loop
terminates. Infinite joint execution remains possible.

The implementation selects one local joint witness at each relevant pair of states,
then uses that same kernel throughout the product loop. The key projection theorem
`Prob.pushforward_loopSem` proves both inequalities:

1. Each finite product approximation projects below the full original semantics.
2. Each finite original approximation lies below the projection of the full product
   semantics. Its proof inducts on original fuel and then on the rank of passive steps.

Increasing-limit continuity finishes the equality. Equal fuel on both sides is not
assumed. Neither the final marginal equations nor global losslessness are premises of
the scheduler theorem. The resulting coupling retains the invariant and both exit
conditions; weighted and pRHL rules expose this result to clients.

For Set outcomes, `SetLoopProjection.image_loopSem` proves both set inclusions by the
same fuel/rank argument. `SetAsyncSchedule` accepts an explicit one-step joint set
with local image equations and invariant/rank properties. Its `couples` theorem and
`quad_while_async_couple` establish mixed bitotal matching. This is distinct from the
pre-existing weak-atom `rhl_while_async`, whose universal partial-correctness reading
does not need bitotal matching or these progress obligations.

## Generic scalar loops and schedules

`Generic/Iteration.lean` defines full least-fixed-point iteration once over an
`IterationModel`. The weighted factory constructs this interface from
`SummationSemiring` and `OmegaSummationSemiring`: scalar summation, zero as bottom,
monotonicity, and increasing-limit continuity are explicit requirements. Exact
support equivalences and commutative multiplication are not premises.

`Generic/LoopCoupling.lean` proves synchronous exact couplings from one coherent
increasing family of product executions. `Generic/AsyncLoop.lean` generalizes the
ranked mixed proof: `Algebra.Weighted.AsyncSchedule.isCoupling_loop` establishes both
exact full-loop marginals, and `Generic.prhl_while_async` and
`Generic.quad_couple_while_async` expose the result. The unilateral rank condition,
arbitrary joint rank resets, and allowance for joint divergence are unchanged.

The passive marginal is a point weight with total scalar weight one. In ENNReal this
forces a unilateral step to be probabilistically lossless; in other models it means
the corresponding scalar identity, not a claim about probability. The theorem derives
the final marginal equations from local premises in all cases.

The same generic schedule in `Generic/AsyncExamples.lean` alternates joint weighted
steps and unilateral deterministic bookkeeping. Its instantiated clients recover
Boolean outcomes, extended-natural counts, ENNReal weights, and tropical costs.
All five [scalar instances](semiring-models.md), including noncommutative finite-word
languages, meet the generic theorem assumptions.

`Generic/Compatibility.lean` equates the existing Set/probability full loops with the
shared iteration. `Generic/BooleanBridge.lean` also preserves full Set execution under
Boolean encoding and equates exact Boolean couplings with bitotal Set couplings.
The guarded unrolling client remains available under its existing `Prob` API.

## Clients and limits

The Set client counts down by one versus two. The probabilistic-language clients use
different counter strides and align fresh random draws while one side performs extra
deterministic bookkeeping. Their observed sum distributions agree for every sample
count. An independent countdown proof establishes mass one for the faster loop, and
the proved coupling transfers mass one to the slower loop. Reversing a schedule
exchanges left and right phases.
The examples also check joint divergence and failure boundaries for missing progress
or mass preservation. The later [randomized-search case](randomized-search.md) couples
fresh trials before success and consumes the full scan's remaining trials unilaterally
after early exit. It retains exact outcome probabilities and proves a strict-saving
event bound. The generic projection helpers now live in `Prob/Observation.lean`.

The rule supports ranked finite catch-up between joint steps. It does not yet support
unilateral phases with an unbounded number of iterations that terminate only almost
surely. Those need a more general phase-losslessness theorem. The existing standalone
one-sided loop rule can handle such phases against skip, but does not automatically
compose them into this mixed schedule.

Random draws in the current clients align jointly. Sampling later against an already
fixed passive value must still satisfy the one-sided coupling obligation; the scheduler
does not provide anticipatory sampling. More general control-state scheduling and
arbitrary fair schedulers remain extensions; alignment completeness is outside the plan.

## Validation

The eight original alignment modules are root-imported. Their historical
`./scripts/check.sh` check passed on 2026-09-19:
1,570 build jobs, 2,143 library declarations, no proof placeholders, and standard
axioms only. Independent source review checked the two projection arguments, the
unrolling/cofinality proof, and the actual program outputs used by the certificate.
The shared iteration, generic synchronous/asynchronous proofs, and scalar clients
are now root-imported as well and checked by the same build and axiom gate. The
historical declaration count above predates that generalization.
The integrated generalization check passed on 2026-09-21: 1,613 build jobs and 3,088
library declarations, no proof placeholders, and standard axioms only.
