# Shared algebra and semiring models

The development now proves common relational rules over an outcome algebra and
constructs that algebra from scalar semirings. Five concrete models reuse the
weighted sequencing, exact couplings, quantitative refutation, and loop theory.
The comparison point is Outcome Logic's algebra and examples in
[the TOPLAS paper, §3](https://www.cs.cornell.edu/~noamz/files/pubs/toplas25.pdf).

## What is shared

[`OutcomeModel`](../RelationalOutcomeLogic/Algebra/Outcome/Basic.lean) supplies
empty outcomes, additive choice, pure outcomes, and Kleisli sequencing. Its laws
include an additive commutative monoid, the monad laws, and distributivity of
sequencing over choice. They do not require idempotent addition. The assertions,
additive splitting, and structural rules in
[`Generic/Assertions.lean`](../RelationalOutcomeLogic/Generic/Assertions.lean),
[`Generic/Judgment.lean`](../RelationalOutcomeLogic/Generic/Judgment.lean), and
[`Generic/Rules.lean`](../RelationalOutcomeLogic/Generic/Rules.lean) use this interface.

The scalar construction uses `Weighted.Weight K α = α → K`. It separates the
additional assumptions instead of claiming that every semiring supports loops:

| Interface | Required laws and purpose |
| --- | --- |
| `Semiring K` | Finite addition and multiplication; multiplication may be noncommutative. |
| `SummationSemiring K` | Arbitrary indexed sums, singleton and zero laws, addition, exchange of sums, product indexing, and left/right multiplication through sums. These derive weighted sequencing and exact coupling composition. |
| `PositiveSummation K` | A sum is zero exactly when every summand is zero. Together with `NoZeroDivisors K`, this gives exact support descriptions. |
| `OmegaSummationSemiring K` | A complete lattice with zero as bottom, monotonicity, and preservation of increasing sequential limits by summation and multiplication. These derive the common least-fixed-point loop semantics. |

The interfaces are in
[`Algebra/Scalar/Basic.lean`](../RelationalOutcomeLogic/Algebra/Scalar/Basic.lean) and
[`Algebra/Scalar/Order.lean`](../RelationalOutcomeLogic/Algebra/Scalar/Order.lean).
[`Algebra/Weighted/Outcome.lean`](../RelationalOutcomeLogic/Algebra/Weighted/Outcome.lean) and
[`Algebra/Weighted/Iteration.lean`](../RelationalOutcomeLogic/Algebra/Weighted/Iteration.lean)
construct the outcome and iteration instances. All five models below satisfy
these assumptions, including positivity and absence of zero divisors.

## Concrete instances

Here `0` and `1` name the **semiring identities**, which need not be numerical
zero and one.

| Model and source | Choice `+` | Sequencing `*` | `0`, `1` | Outcome interpretation |
| --- | --- | --- | --- | --- |
| [`Reachability`](../RelationalOutcomeLogic/Algebra/Instances/Boolean.lean) | Disjunction | Conjunction | False, True | Whether an outcome is reachable |
| [`ℝ≥0∞`](../RelationalOutcomeLogic/Algebra/Instances/Probability.lean) | Numerical addition | Numerical multiplication | 0, 1 | Nonnegative weight; probability when the mass bounds hold |
| [`ℕ∞`](../RelationalOutcomeLogic/Algebra/Instances/Counting.lean) | Numerical addition | Numerical multiplication | 0, 1 | Number of traces reaching each outcome |
| [`Cost`](../RelationalOutcomeLogic/Algebra/Instances/Tropical.lean) | Numerical minimum | Numerical addition | ∞, 0 | Cheapest cost of reaching each outcome |
| [`Language Γ`](../RelationalOutcomeLogic/Algebra/Instances/Language.lean) | Union | Ordered concatenation | ∅, {empty word} | Finite words emitted on terminating traces |

`Reachability` uses logical disjunction rather than Boolean XOR. The natural
order for `Cost` reverses numerical order: discovering a cheaper path increases
semantic information. `Cost.value_iSup` and `Cost.value_sum` expose the resulting
numerical infima. Language concatenation genuinely does not commute, as proved
by `TraceExamples.emit_noncommutative`.

For every instance, the chosen sum equals the supremum of all finite subsums:
`Reachability.sum_eq_iSup_finset`, `ennreal_sum_eq_iSup_finset`,
`enat_sum_eq_iSup_finset`, `Cost.sum_eq_iSup_finset`, and
`TraceLanguage.sum_eq_iSup_finset`.

## Programs and refutations

[`InstanceExamples.routes`](../RelationalOutcomeLogic/Examples/Algebra/Routes.lean)
chooses a direct edge to node 2 or two edges through node 1. The single proof
`routes_sem` computes its weight as `direct + first * second`;
`routes_coupled` certifies collapsing the routes to that weight.

| Instance | Edge weights: direct, first, second | Proved result at node 2 |
| --- | --- | --- |
| Boolean | True, True, True | Reachable |
| Counting | 1, 1, 1 | 2 traces |
| Probability weights | 1/4, 1/2, 1/2 | Weight 1/2 |
| Tropical costs | 7, 2, 3 | Minimum cost 5 |

Dropping one route preserves Boolean reachability. In the counting model it
preserves the possible answer while reducing its weight from 2 to 1:
`counting_drop_route_same_support` proves support equality and
`counting_drop_route_certificate` certifies the quantitative failure. Removing
the cheaper tropical route is certified by `tropical_drop_route_certificate`:
the numerical cost changes from 5 to 7. Both use the generic finite-event
certificate machinery in
[`Generic/Refutation.lean`](../RelationalOutcomeLogic/Generic/Refutation.lean).
Its finite-event algebra and coupling bounds are isolated in
[`Algebra/Weighted/Events.lean`](../RelationalOutcomeLogic/Algebra/Weighted/Events.lean),
independent of relational assertions and certificates.

[`WeightedPrograms.countdown_sem`](../RelationalOutcomeLogic/Examples/Algebra/Countdown.lean)
proves once that a loop with `n` weighted steps has outcome `r^n` at counter zero.
Its instances give certain reachability, `2^n` traces, probability weight `q^n`,
and numerical cost `n • d`. The probability example proves mass at most one
when `q ≤ 1`; counting weight two is proved equal to two unit-weight branches.

[`AsyncExamples`](../RelationalOutcomeLogic/Examples/Algebra/AsynchronousCountdown.lean) also reuses
one genuinely asynchronous proof. A slow machine separates each weighted step
from a bookkeeping step; a fast machine combines them. The schedule alternates
joint and left-only steps, using a decreasing phase rank for the latter.
`async_spec` applies `Generic.prhl_while_async`, `observed_equal` proves equality
after forgetting the slow machine's phase, and `slow_mass` gives `r^n`.
Boolean, counting, probability, and tropical specializations are included.

[`TraceExamples`](../RelationalOutcomeLogic/Examples/Algebra/Traces.lean) checks the
noncommutative case: two successive logging actions emit `[a,b]`; swapping
distinct actions fails exact coupling. Branching records both execution orders,
and the shared countdown proof gives repeated emitted words.

## Compatibility and scope

The existing concrete developments remain connected to the abstraction.
[`Bridges/Set.lean`](../RelationalOutcomeLogic/Bridges/Set.lean) supplies
the Set outcome and iteration instances and identifies the Set assertions,
judgments, and full loops with the shared constructions.
[`Bridges/Probability.lean`](../RelationalOutcomeLogic/Bridges/Probability.lean)
supplies the corresponding ENNReal instances and equations, including exact
couplings and pRHL judgments.
[`Bridges/Boolean.lean`](../RelationalOutcomeLogic/Bridges/Boolean.lean)
identifies Set outcomes with Boolean weights, preserving sequencing, loops, and
exact relational couplings.

All scalar examples live under `Examples/Algebra/`; their existing
`RelOL.Generic.*` declaration namespaces are retained. Deterministic observation
laws live in `Algebra/Weighted/Observation.lean`, and weighted loop support laws
live in `Generic/Loops/Support.lean`, so using these facts does not import the
asynchronous scheduler proof.

The relation to the TOPLAS models has these precise limits:

- **Total operations.** This implementation instantiates total semirings. It
  does not implement the paper's partial deterministic Boolean addition or its
  partial probability addition.
- **Probability bounds.** ENNReal is an ambient weight algebra. The existing
  `Prob` language checks normalized sampling and proves subprobability semantics;
  unrestricted generic addition can exceed mass one. ENNReal is not identified
  with the paper's partial `[0,1]` semiring.
- **Support.** Generic weights are arbitrary functions with no countable-support
  field. The paper's weighting functions require countable support. On arbitrary
  state spaces this is a larger domain, not a proved equivalence to that domain.
- **Continuity.** The loop interface uses a complete lattice and increasing
  sequential limits. It is not a mechanization of the paper's full directed-set
  Scott-continuity interface. Arbitrary-supremum preservation is not assumed for
  additive probability weights.
- **Traces.** The language instance contains finite words. The paper's language
  example also includes infinite words; that extension is not implemented.

The generic asynchronous rule retains the ranked-scheduling premise: every
supported unilateral step must decrease a natural-number rank. Semiring
parametricity does not remove that progress requirement. No completeness result
is required or claimed by this extension.
