# Randomized search: correctness, outcome probabilities, and a certified bug

This case compares a bounded scan of independent Bernoulli trials with an
optimization that stops at the first hit. A faulty implementation reuses the first
trial. The development covers every natural-number budget and normalized trial
distribution, with explicit hypotheses where a strict probability gap is needed.

Import `RelationalOutcomeLogic.Examples.Probability.Search.Case` for the full example. The
[theorem guide](theorem-guide.md) shows the correctness and refutation statements
side by side.

## Programs and observation

The state is `(remaining, found)`. Initially it is `(n, false)`. A trial has miss
mass `q` and hit mass `r`, with `q + r = 1`. Each fresh trial decrements `remaining`
and updates the sticky `found` flag. Repeated sampling uses the command language's
weighted bind semantics.

```text
full scan                         early exit
while remaining > 0:              while remaining > 0 and not found:
    b := fresh Bernoulli(r)           b := fresh Bernoulli(r)
    found := found or b               found := found or b
    remaining := remaining - 1        remaining := remaining - 1

cached draw (faulty)
if remaining > 0:
    b := Bernoulli(r)
    found := found or b
    remaining := remaining - 1
    while remaining > 0:
        remaining := remaining - 1
```

The cached program drains the budget after one draw. Since the flag is sticky,
repeatedly OR-ing the same draw would leave the same answer. The Lean command
directly implements the draw-then-drain version.

The external observation is `found`; the remaining budget is retained internally
for resource assertions. `consumed n s := n - s.remaining` records trials consumed
by the full and early-exit programs. Their sampling steps each decrement the budget
once, and the early-exit support cannot contain a remaining budget above its input.
This cost interpretation applies to those two programs; the faulty program's
deterministic drain also decrements the counter, so its counter is not a sample count.

## Asynchronous correctness

The invariant relates states with equal flags, at least as much remaining budget on
the early-exit side, and equal budgets before success. Before the first hit, the
schedule couples matching miss/hit branches. After a hit, only the full scan runs.
Its remaining budget strictly decreases during this unilateral phase.

`full_early_prhl` applies the ranked mixed while rule; `full_early_quad` exports
the proof to arbitrary coupled input weights. The product loop has the actual full
and early-exit outputs as its exact marginals. Consequently:

- The observed Boolean distributions agree for every starting state.
- Both programs terminate with mass one, including zero budget and deterministic trials.
- There is an output coupling in which early exit consumes no more trials, while
  the full scan consumes the entire budget.

The result concerns full loop semantics; no finite approximation is substituted for
the output distribution.

## Quantitative outcome contract

Let `S(0) = 0` and `S(n+1) = q * S(n) + r`. The development proves
`q^n + S(n) = 1`. This expresses the success mass without requiring subtraction of
extended nonnegative reals.

`search_outcome_quad` proves one weighted judgment whose postcondition splits the
outputs with `oplus`:

| Outcome piece | Mass on each side | Relation within the piece |
| --- | --- | --- |
| Failure | `q^n` | Both return false with zero remaining budget and consume all `n` trials |
| Success | `S(n)` | Both return true; early exit consumes at most the full scan's `n` trials |

The proof restricts the same asynchronous joint to failure and its complement.
Each restricted joint retains exact restricted marginals. The reusable
`IsCoupling.restrict` and `Coupled.split_mass` theorems expose this construction;
they allow zero-mass pieces and do not renormalize them. `resultSpec_mass_one`
also proves that this postcondition forces total mass one.
`resultSpec_observed_eq` derives equality of the observed answer distributions from
the contract alone, independently of which commands produced the weights.

The outcome assertion records the mass of each class together with its relational
property. A plain equality-of-answers postrelation does not record those masses.
The example illustrates how to combine pRHL-style correctness with quantitative
outcome assertions; it is not a claim that pRHL with auxiliary reasoning cannot
establish the corresponding probability facts.

For budgets `n + 2`, `early_savingEvent_mass_ge_hit` additionally proves that the
probability of a successful return after a nonempty proper prefix is at least `r`.
A hit on the first trial supplies that mass. The full scan has zero mass on this
strict-saving event. Thus a positive hit probability gives positive probability of
strictly fewer consumed trials. This strict-saving result establishes the optimization
benefit; the non-strict cost bound in `resultSpec` alone does not. This is an
event-probability bound, not an expected runtime theorem.

## Certified faulty variant

For any positive budget, cached search has failure probability `q`. The full scan
has failure probability `q^n`. Whenever `0 < q < 1` and `n > 1`, the proof establishes
`q^n < q` and constructs a finite-event mass-deficit certificate using `{false}`.

`cached_bug` attaches the certificate to the actual observed command transformers
and the initial states `(n, false)`. `cached_spec_refuted` then refutes the equality
coupling specification at that input. The cached program is placed on the left of
the certificate, where the failure-event mass is larger.

`cached_outcome_spec_refuted` additionally refutes the same `resultSpec` contract
proved by `search_outcome_quad`, replacing early exit with the cached command on
the right. The generic observation bridge transports the Boolean certificate back
to this full-state weighted judgment. Thus correctness and refutation meet at one
postcondition, including its probability and resource requirements.

Both programs have termination mass one and identical observed supports under the
nondegeneracy hypotheses. The certificate therefore detects a probability error
that support equality would miss. For a fair trial and budget two, the checked
failure masses are exactly `1/2` and `1/4`. Budgets zero and one are checked agreement
cases; the general refutation deliberately excludes them.

## Where the proofs live

Case-specific names below are in `RelOL.Prob.Search`. Generic observation and coupling
restriction lemmas are in `RelOL.Prob`; weight restriction is in `RelOL.Weight`.

| Module | Main declarations |
| --- | --- |
| [`Examples/Probability/Search/Programs.lean`](../RelationalOutcomeLogic/Examples/Probability/Search/Programs.lean) | `Trial`, `full`, `early`, `full_sem_false`, `failure_add_success`, `full_isProbability` |
| [`Examples/Probability/Search/Alignment.lean`](../RelationalOutcomeLogic/Examples/Probability/Search/Alignment.lean) | `schedule`, `full_early_prhl`, `outputJoint_isCoupling`, `observed_equal`, `cost_coupling` |
| [`Prob/Coupling/Restriction.lean`](../RelationalOutcomeLogic/Prob/Coupling/Restriction.lean) | `Weight.restrict`, `IsCoupling.restrict`, `Coupled.split_mass` |
| [`Examples/Probability/Search/OutcomeContract.lean`](../RelationalOutcomeLogic/Examples/Probability/Search/OutcomeContract.lean) | `resultSpec`, `result_split`, `search_outcome_quad`, `resultSpec_mass_one` |
| [`Examples/Probability/Search/Cost.lean`](../RelationalOutcomeLogic/Examples/Probability/Search/Cost.lean) | `mem_savingEvent_iff_consumed`, `early_savingEvent_mass_ge_hit`, `positive_saving_probability` |
| [`Examples/Probability/Search/CachedRandomness.lean`](../RelationalOutcomeLogic/Examples/Probability/Search/CachedRandomness.lean) | `cached_bug`, `cached_spec_refuted`, `cached_full_supports_equal`, `fair_two_false_event_masses` |
| [`Examples/Probability/Search/Case.lean`](../RelationalOutcomeLogic/Examples/Probability/Search/Case.lean) | Complete case import; `cached_outcome_spec_refuted` |
| [`Prob/Coupling/Observation.lean`](../RelationalOutcomeLogic/Prob/Coupling/Observation.lean) | `pushforward`, `Coupled.pushforward` |
| [`Prob/Refutation/Observation.lean`](../RelationalOutcomeLogic/Prob/Refutation/Observation.lean) | `quadSem.observe`, `BugCert.refutes_of_observation` |

All listed modules are root-imported and covered by `./scripts/check.sh`.

This is a parameterized algorithmic case study in the existing denotational
language. It models independent trials, without arrays, an external random-number
generator, or machine arithmetic. There is no separate operational cost adequacy
or expected-cost proof. The certificate is constructed in Lean; automatic discovery
is separate work.
