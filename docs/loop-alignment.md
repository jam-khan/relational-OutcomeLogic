# Guarded unrolling and ranked asynchronous loops

The alignment development has two distinct results: a semantics-preserving block
transformation and mixed left/right/joint execution with proved terminal marginals.

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

## Clients and limits

The Set client counts down by one versus two. The probabilistic-language clients use
different counter strides and align fresh random draws while one side performs extra
deterministic bookkeeping. Their observed sum distributions agree for every sample
count. An independent countdown proof establishes mass one for the faster loop, and
the proved coupling transfers mass one to the slower loop. Reversing a schedule
exchanges left and right phases.
The examples also check joint divergence and failure boundaries for missing progress
or mass preservation.

The rule supports ranked finite catch-up between joint steps. It does not yet support
unilateral phases with an unbounded number of iterations that terminate only almost
surely. Those need a more general phase-losslessness theorem. The existing standalone
one-sided loop rule can handle such phases against skip, but does not automatically
compose them into this mixed schedule.

Random draws in the current clients align jointly. Sampling later against an already
fixed passive value must still satisfy the one-sided coupling obligation; the scheduler
does not provide anticipatory sampling. General control-state scheduling, alignment
completeness, and arbitrary fair schedulers remain separate extensions.

## Validation

All eight new modules are root-imported. `./scripts/check.sh` passed on 2026-09-19:
1,570 build jobs, 2,143 library declarations, no proof placeholders, and standard
axioms only. Independent source review checked the two projection arguments, the
unrolling/cofinality proof, and the actual program outputs used by the certificate.
