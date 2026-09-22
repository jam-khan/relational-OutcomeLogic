# Parallel scientific sampling: implementation and proof plan

Status: implemented. The current [case guide](parallel-sampling.md) maps the
checked results, proof rules, source correspondence, and precise scope. The steps
below retain the original acceptance criteria. The implementation includes both
concrete collection policies, actual uncapped event-loop termination, joint
population/stopping-count preservation, speculation bounds, quantitative fault
certificates, adaptive generation sequencing, and local look-ahead validation.

The proof uses existing recursion rules plus a derived full-loop reconstruction
rule with explicit guard agreement. It does not introduce an unrestricted
asynchronous rule or claim verification of the complete external Python/Redis
implementation. The two concrete policies are verified; arbitrary schedulers
would need to discharge their own local obligations. The optional multi-output
race tail law and makespan comparison are not part of the implementation.

## Main target

An ordered-commitment worker pool returns the same joint accepted-population law
as sequential rejection sampling, although jobs finish out of order and runtime
may depend on their values and acceptance outcomes. Prove both an explicit
proposal-cap interface and actual uncapped loop semantics. The finite version is
a construction and validation milestone, not the intended final ceiling.

Parameters are a normalized discrete job law over `(value, accepted, duration)`,
an accepted-population quota `n`, positive worker capacity `P`, and, for bounded
speculation, a positive launch-window size `W`. Durations are positive finite
naturals, with no required common bound or independence from values. Job draws
are fresh and independent for a fixed job law. Adaptive changes between completed
generations are a later compositional target.

For proposal cap `M`, return either `success population` or `exhausted partial`.
Correctness compares the whole result law, including exhaustion. Without a cap,
positive acceptance probability `a` and a progressing scheduler should imply
termination mass one and the law of `n` independent draws from the accepted
conditional distribution. Equality of every single output marginal is weaker
than the required joint-population theorem.

## Steps and acceptance criteria

### 1. Fix the contract and implementation correspondence

Pin a pyABC revision and map launch IDs, completion collection, sorting,
truncation, and outstanding-job handling to the formal model. Record what is an
abstraction and what follows the source. Define the job law, population result,
and observable work counters before defining correctness.

Deliverable: theorem signatures and a source-to-model table. The theorem must
allow dependent value/runtime pairs and account explicitly for acceptance,
ties, exhausted budgets, and empty quotas.

### 2. Implement actual reference and collector kernels

Define sequential rejection sampling and an event-driven worker pool with
launch IDs, worker slots, pending jobs, completed results, the next commit ID,
the accepted output list, and cancellation. Supply two policies: collect a
batch then order it; continuously replenish a bounded launch window and commit
the settled prefix. A mutant commits in completion order instead.

Check the two-job fair-bit race immediately. Both jobs are accepted; value `1`
has duration one, value `0` duration two. Completion-order selection returns `1`
with probability `3/4`; sequential and ordered selection return it with `1/2`.
This validates the actual program and observer definitions before the general
proof is built. It is a proposed mutation, not an assertion of a shipped pyABC bug.

### 3. Establish the local proof interface early

Prove local contracts for fresh launch, completion, buffering, rejection,
commitment, and cancellation. Track unique IDs, the committed launch prefix,
stored task identity, and the accepted subsequence of that prefix.

Prototype the derivation using finite hidden task buffers, `quad_lifted`,
sequencing, and the existing asynchronous/bounded loop interfaces. A random
unilateral step can couple to a point mass; the real obligations are retaining
the hidden law and satisfying the support-wise decreasing rank. Sampling an
arbitrarily large duration may require joint launch alignment or a prefetch
reference, rather than a rank-decreasing unilateral step.

If a distributional asynchronous rule makes the direct collector proof materially
better, develop it here. Its statement must cover scheduler branches, guards,
exit observations, progress and, for uncapped loops, increasing limits. Keep the
rule outside `Examples/` and test its reuse in the speculative-decoding proof.
An existing-rule derivation is also a valid outcome; new machinery is justified
by the proof, not by a target count of new rules.

Deliverable: a small collector derived from local rules, with the proof route
decided before investing in the full parameterized development. Whole-program
semantic equality may not be an assumed premise of the main derivation.

### 4. Prove the general capped contract

Prove complete result-law equality for arbitrary cap, population quota, worker
capacity and admissible scheduling policy. Include success/exhaustion outcome
splitting with equal masses and matching populations on both sides. Derive
normalization and output-length consequences from this contract.

Cover zero quota, zero cap, deterministic acceptance/rejection, repeated values,
simultaneous completions, capacity exceeding the cap, and long early jobs.
Both concrete scheduling policies must instantiate the shared interface.

### 5. Reach uncapped rejection sampling

Define the actual uncapped collector using the existing loop semantics. Relate
its successful executions to finite-prefix approximants, prove the limit
correspondence, and establish normalization and the accepted conditional law
when `a > 0` and scheduler progress holds.

Do not sample an infinite iid tape as a discrete `Weight` over streams: that
generally requires a non-atomic measure. Finite buffers/prefixes and the existing
increasing-limit machinery are the intended route. Explicit `exhausted` terminal
outcomes are also not a monotone approximation sequence; use successful parts
and prove their relation to the uncapped loop.

Deliverable: a theorem for the real loop, with no hidden finite-fuel assumption.
Positive acceptance, finite job duration and scheduling progress have separate
roles and must be discharged separately.

### 6. Strengthen the quantitative outcome contract

Let `T_n` be the number of sequential proposals through the nth accepted job.
For a launch window of size `W` relative to the next uncommitted ID, prove under
the shared execution coupling:

\[
\mathrm{started}\le T_n+W-1,\qquad
\mathrm{discarded}\le W-1.
\]

With iid acceptance probability `a > 0`, prove `E[T_n] = n/a` and hence

\[
\mathbb E[\mathrm{started}]\le n/a+W-1.
\]

These bounds count proposals, not elapsed time. Worker capacity alone does not
bound speculative overlaunch; the window invariant is essential. Integrate the
pathwise accounting with population correctness in one pRelOL contract. A
small early-return versus drain time lemma may be added under a shared discrete
execution model, but it is not the core quantitative result.

### 7. Refute realistic faulty policies against the same contract

Generalize the race certificate: with `P` simultaneous independent jobs and
fast-value probability `theta`, first completion returns the fast value with
probability `1-(1-theta)^P`, rather than `theta`. Prove the strict gap when
`0 < theta < 1` and `P > 1`, normalization, and identical value supports.

Add a mutation that cancels an unsettled earlier ticket, and a duplicate-result
mutation if supported by the chosen collector model. Produce certificates for
the original population contract; checking individual output marginals alone
can miss lost independence or duplicate samples. A richer race contract for
multiple returned samples is a useful further target.

### 8. Exercise adaptation and broader reuse

Compose several generations where each new job law depends on the previously
committed population. Apply sequencing to the per-generation contracts, keeping
the law fixed while a generation's work is outstanding.

Then investigate versioned look-ahead work: jobs may be committed only when
their generating kernel agrees with the kernel required by the new generation.
Prove a sound validation/discard protocol if feasible, and certify a naive
stale-proposal variant. This extension is to be attempted after the core
collector; any reduction in its target should be justified by an encountered
obligation, not presumed in advance.

### 9. Evaluate the proof method and prepare the paper artifact

Document a derivation graph separating primitive probability facts from rule
applications, implementation correspondence, scheduler obligations, and cost
interpretation. Report which proof components both collector policies share,
what additionally carries over from decoding, and what new rules were necessary.
Add focused automation only for repeated obligations visible in these proofs.

Run the full structure/build/placeholder/axiom gate and rebuild the paper.
Completion means parameterized collector correctness, uncapped termination,
useful speculation bounds, certificates refuting the same contract, and explicit
evidence that reusable pRelOL rules carried the proof.

## Source organization

Keep case-specific code under `Examples/Probability/ParallelSampling/`, beginning
with `Model`, `Programs`, `Invariant`, `Correctness`, `Outcomes`, `Work`,
`Counterexamples`, `Adaptive`, and `Case` as their responsibilities materialize.
Only genuinely reusable algebra or proof interfaces go into the library layers.
Avoid dependencies on another case's private probability definitions.

## Primary references

- [pyABC multicore collector](https://pyabc.readthedocs.io/en/latest/_modules/pyabc/sampler/multicore_evaluation_parallel.html): source sorts by launch ID before truncation to avoid short-runtime bias.
- [pyABC distributed collector](https://pyabc.readthedocs.io/en/latest/_modules/pyabc/sampler/redis_eps/sampler.html): outstanding work and ordered population construction.
- [Anytime Monte Carlo, original preprint](https://arxiv.org/abs/1612.03319v1): established runtime-dependent Monte Carlo bias and a different, multiple-chain correction. The bias phenomenon itself is not our novelty claim.
