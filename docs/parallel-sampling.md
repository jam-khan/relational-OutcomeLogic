# Parallel scientific sampling

Import `RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Case`.
Names below are relative to `RelOL.Prob.ParallelSampling`.

The main implementation is a worker pool that samples jobs at launch and commits
results in launch order. It preserves the **whole joint accepted-population law**
of sequential rejection sampling when runtimes depend on values or acceptance.
The uncapped theorem includes almost-sure termination and the joint distribution
of the population and its stopping ticket. The same development certifies biased
completion-order selection, duplicated results, and stale proposal reuse.

## Model and guarantees

`Job α` contains a value, an acceptance bit, and a positive finite duration
`ticks + 1`. Its normalized discrete law may correlate all three fields.
Successive launches use independent draws from the same law within a generation.
There is no common duration bound. Worker capacity `P` and launch window `W`
must be positive. The window bounds all launched, uncommitted tickets, including
completed results waiting behind an earlier ticket.

The concrete state retains ordered worker slots, remaining durations, a completed
result buffer (slots with zero remaining duration), quota, population, and work
counters. Ticket IDs are implicit contiguous positions: the commitment frontier
plus the slot index. Launch fills free capacity, ticks advance running jobs together,
and only a completed head ticket can commit. Rejection advances the frontier
without emitting a value. At success, outstanding tickets are discarded.

| Interface | Checked guarantee |
| --- | --- |
| `freshCollector_contract` | With cap `M`, exact full population result, including `exhausted partial`; reference stopping ticket and concrete work share one coupling |
| `freshCollector_split` | Success and exhaustion are additive outcome pieces with matching exact masses |
| `uncappedCollector_answer`, `uncappedCollector_probability` | The actual uncapped loop returns the sequential population and terminates with mass one when acceptance probability `a > 0` |
| `uncappedCollector_record` | Joint `(committed proposals, population)` law equals the counted sequential rejection sampler |
| `uncappedCollector_population_length` | Every supported uncapped population has exactly the requested size |
| `eventRun_initial_capacity` | Both capped and uncapped executions preserve worker and launch-window bounds |
| `batchCollector_contract` | A second policy drains the complete proposal cap before selecting the ordered population; exactly `M` jobs start and commit |

For the continuous pool, every supported result satisfies

\[
\mathrm{started}=T_n+\mathrm{discarded},\qquad
\mathrm{discarded}\le W-1.
\]

Here `T_n` is the sequential proposal count through the nth acceptance, including
rejected proposals. Its **joint law with the population** is preserved, not just
its expectation. The checked quantitative results are

\[
\mathbb E[T_n]=n/a,\qquad
\mathbb E[\mathrm{started}]\le n/a+W-1.
\]

These are proposal-work bounds. Elapsed ticks are modeled and retained by the
finite implementation correspondence, but there is no speedup or makespan
comparison theorem. Worker count alone does not imply the `W-1` bound.
The actual pool returns immediately for quota zero. The batch policy deliberately
drains its cap even when the requested population is empty.

## Which proofs use the rules?

1. `Reference/Capped` derives finite eager/lazy sampling correspondence using
   `quad_lifted` and `quad_recursion`. The local premises expose one fresh job
   and discard an unused **normalized** suffix.
2. `Scheduler/Rules` proves one event layer for arbitrary verified continuations.
   Launch and tick preserve the outstanding ordered tape; commitment consumes
   its head. `poolFuel_quad` applies `quad_recursion_family` with a decreasing
   event potential. The public population/stopping-ticket lemmas are consequences
   of this derivation, not an independently assumed whole-program equality.
3. `Scheduler/EventLoop` introduces a finite unlaunched ghost suffix. Already
   launched jobs retain their sampled values and runtime information. The local
   `event_reconstruction_quad` and guard compatibility feed `quad_lifted_while`.
   `Scheduler/Ghost` connects the forward loop to the certified recursive event
   interpreter, preserving every result field.
4. `Correctness` composes these results and couples population and work. Outcome
   restriction produces the success/exhaustion split. `Coupled.expectation_le`
   transports the pathwise work inequality.
5. `Scheduler/Limits` proves the actual uncapped loop equals the increasing limit
   of capped runs that succeed with **`started < cap`**. Ordinary capped success
   laws are not monotone when work counters are observed. `UncappedCorrectness`
   sandwiches these runs between successful sequential prefixes;
   `UncappedRecord` retains the stopping count as well as the population.
6. `Adaptive` sequences per-generation judgments for a job law, quota, and cap
   chosen from the entire committed history. `Versioning` supplies a local
   reconstruction rule for validating or discarding an outstanding candidate.

Primitive probability algebra, geometric expectations, deterministic potential
and accounting invariants, and the forward/backward interpreter correspondence
are semantic lemmas consumed by these derivations. The logic does not discover
the invariant or automatically discharge every quantitative obligation.

The separate `Window/` protocol rotates a finite pending queue and demonstrates
reuse of the same full-loop reconstruction rule with arbitrary update states.
It abstracts waiting and prefetches `W-1` jobs even at quota zero. Its exact
`n/a + W-1` launch expectation belongs to that protocol; the concrete event pool
has the inequality above and zero work at quota zero.

## Faults and adaptation

`Faults/Race` samples independent jobs, then chooses the minimum completion time,
breaking ties in launch order. A true value has duration one and a false value
duration two. With `P` jobs and true probability `θ`, it returns true with
probability `1-(1-θ)^P`. The gap is strict for `P > 1` and `0 < θ < 1`, while both
programs retain identical Boolean support. Checked witnesses are `3/4` for two
fair jobs and `255/256` for eight. `ordered_race_correct` connects the correct
event pool to the exact population equality refuted by the race certificates.

`Faults/Duplication` independently decides whether to reuse the first sample as
the second. The fair-sampling, fair-reuse mutant has correct individual marginals
and the same full output support, but a certificate refutes its joint population law. `Versioning` gives
a stale-law certificate and proves that reuse is sound when validation implies
equality of the generating and required kernels; otherwise it discards the old
normalized candidate. Validation inspects versions, not the sampled value.
The precondition specifies the candidate's conditional law given the version
context. This is a local look-ahead protocol, not a verified multi-generation
Redis cache with arbitrary correlations.

## Implementation correspondence and prior work

The source comparison is pinned to pyABC commit
[`914ce7c07798fd130dc8885e1bea3ac4587018a0`](https://github.com/ICB-DCM/pyABC/tree/914ce7c07798fd130dc8885e1bea3ac4587018a0).
The [multicore collector source](https://github.com/ICB-DCM/pyABC/blob/914ce7c07798fd130dc8885e1bea3ac4587018a0/pyabc/sampler/multicore_evaluation_parallel.py)
assigns launch IDs before simulation, joins workers, then sorts accepted results
by ID before truncating. Our batch policy models this order-preserving collection
pattern. The window policy adds an explicit speculation bound; it is not claimed
to be a literal extraction of pyABC.

| Pinned source | Formal counterpart or abstraction |
| --- | --- |
| Lines 38–43: allocate ID, evaluate job | Fresh launch draw; implicit contiguous ticket order |
| Lines 44–54: acceptance and result queue | Joint acceptance/value law; completed slot buffer |
| Lines 138–152: collect and join workers | Fully drained batch policy |
| Lines 154–156: order by ID and truncate | Ordered accepted prefix and `batchFinish` |
| Lines 167–168: insufficient population | Explicit `Result.exhausted partial` |
| Processes, IPC, worker-health checks | Discrete deterministic event scheduler; not Python/OS verification |
| Completion-driven shared stopping counter | Different from our fixed-cap drain and ordered-window stopping policies |

This is not evidence of a shipped pyABC bias bug: the inspected source explicitly
guards against short-runtime bias. The faulty policies are modeled mutations.
Runtime-dependent Monte Carlo bias is established prior work;
[Anytime Monte Carlo, original 2016 preprint](https://arxiv.org/abs/1612.03319v1)
studies real-time interruption and a different multiple-chain correction.
The contribution evaluated here is the relational proof method, joint work
contract, and quantitative refutations of scheduling transformations.

## Shared-library changes

`Prob/Logic/DistributionalLoop.lean` extends reconstruction to full loops using
guard agreement on reconstruction support, a local body judgment, and increasing
limits. It synchronizes semantic body steps; it is **not** an unrestricted
asynchronous rule. Both the fresh-launch event proof and abstract window proof
use it. Existing assertion and command semantics are unchanged.

`Prob/Coupling/Expectation.lean` transports pointwise inequalities/equalities
through exact couplings. `Algebra/ENNReal/Expectation.lean` adds monotonicity in
the input weight and continuity for increasing weights, needed for uncapped work.
All algorithm-specific definitions remain under this example directory.

Validation: run `./scripts/check.sh` and `./scripts/build-paper.sh` from the root.
`Case` includes checked slow-first-ticket, rejection/exhaustion, empty-quota, and
empty-cap examples; the general theorems also cover ties, repeated values, and
capacities exceeding a finite proposal cap.
