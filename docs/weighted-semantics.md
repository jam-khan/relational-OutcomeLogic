# Weighted semantics contract

Status: steps 1–4 of the roadmap, 2026-09-19. The existing Set logic remains the
reference implementation. Weighted assertions, exact-marginal couplings, and quantitative
refutation certificates build on the concrete weighted algebra. Probabilistic commands
and a pRHL embedding remain subsequent work.

## Baseline

The pre-change checkout was `af4bac907d0af27e7e38ca779857d33735d63603`, with the
previous infrastructure-audit notes present as untracked files. Its full check passed:
651 build jobs, 1,217 library declarations, no proof placeholders, standard axioms only.
The existing Set semantics, rules, compiler, heterogeneous models, and examples are
regression requirements for the weighted extension.

Lean and Mathlib remain pinned to v4.32.1. The audit established that Mathlib already
supplies the required summation and order theory. No external dependency is needed for
this stage. Adapted ideas from the audited libraries are identified in
[`notes/infrastructure-audit.md`](../notes/infrastructure-audit.md).

## Carrier and operations

`RelOL.Weight α := α → ℝ≥0∞` contains arbitrary nonnegative weights, including infinite
weights and total mass greater than one. Zero, addition, scalar multiplication, and
order are inherited pointwise. The raw carrier is a complete lattice.

- `Weight.pure a` places weight one at `a` and zero elsewhere.
- `Weight.bind μ k b = ∑' a, μ a * k a b` defines discrete sequencing.
- `Weight.support μ = {a | μ a ≠ 0}` records possible outcomes.
- `Weight.mass μ = ∑' a, μ a` records total weight.
- `Weight.IsSubprob μ` means `mass μ ≤ 1`.
- `Weight.IsProbability μ` means `mass μ = 1`.

Addition is total in the raw carrier. The probability mass bound is a separate
predicate, to be preserved by the future probabilistic language. Unrestricted
nondeterministic addition must not be silently interpreted as normalized probability
choice. Probabilistic choice will use nonnegative coefficients whose sum is one.

The weighted API proves algebraic pure/bind laws directly; it does not install a new
global `Monad` instance on the function-type abbreviation.

## Exact couplings and nontermination

For a subprobabilistic program, mass is termination probability; missing mass records
nontermination. Zero denotes no terminating outcomes. A sampling primitive will use
a normalized distribution; loops may produce a subdistribution.

The implemented relational lifting `Prob.Coupled R μ ν` uses an actual joint weight `J`:

```text
∀ a, ∑' b, J (a, b) = μ a
∀ b, ∑' a, J (a, b) = ν b
J (a, b) ≠ 0 → R a b
```

These exact marginals imply equal total mass. Both sides may diverge, including the
zero/zero case, but unequal termination probabilities cannot be related this way.
In particular, comparison with `skip` from a unit-mass initial state requires
termination mass one on the other side. Asynchronous one-sided phases need mass-preservation
obligations. Divergence-insensitive/star liftings are different semantics and must
not be substituted under the same name.

This fixes the contract for the future pRHL bridge; that bridge is not yet implemented.
Matching supports alone is insufficient: distributions can share their support while
assigning different weights. The checked fair/biased coin example has identical supports
and unit total mass, but no equality coupling. Exact equality coupling is equivalent to
equality of the weights.

`Prob.IsCoupling` exposes the joint witness and both marginal equations. Its laws
include zero, pure, diagonal, relation weakening, addition, common scaling, and bind.
The bind construction sequences the outer joint with a joint continuation at each
supported pair. Reordering nonnegative sums proves both exact marginals; the support
law proves the output relation. This construction uses no division and therefore
applies to raw weights, including infinite weights. It does not assert a general
conditional-distribution or transitive-gluing theorem.

The one-way support bridge recovers the existing Set coupling from any weighted
coupling. The fair/biased example refutes the converse.

## Weighted assertions and splitting

`Prob.RAssn α β` is a predicate on pairs of weights. `emp` requires both weights to
be zero; `exactly` fixes the two weights; `massEq p q` fixes their total masses.
`atomW R` checks all pairs of supported outcomes and allows zero weights; `atom R`
also requires positive mass on both sides. These Cartesian atoms are distinct from
existential joint-coupling assertions `Prob.couple R`.

`oplus P Q` splits both weights by addition into a part satisfying `P` and a part
satisfying `Q`. Its laws include associativity, commutativity, an empty unit, and
consequence. Splitting two exact mass assertions adds their masses. In particular,
a fair coin cannot satisfy two unit-mass pieces. Components may share a state, but
their weights must add to the original weight at that state.

Adding two coupling assertions combines their joint witnesses and preserves the
corresponding relation disjunction. Scaling is a common scalar image on both sides;
it does not assume that zero or infinite scalars can be cancelled.

## Quantitative refutation certificates

`Weight.eventMass μ A` sums the weight of a finite event `A`. For an exact
`R`-coupling, finite events satisfy the necessary condition:

```text
(∀ a ∈ A, ∀ b, R a b → b ∈ B)  ⇒  eventMass μ A ≤ eventMass ν B
```

`Prob.MassDeficitCert R μ ν` stores the two events, a proof of that image-cover
condition, and the strict reverse inequality. Its `refutes` theorem rules out every
exact `R`-coupling. Only the events need to be finite; the carriers and total weights
may be infinite. The proof does not subtract infinite quantities or normalize weights.

The constructor `MassDeficitCert.of_bounds` accepts a certified lower bound on the
left event mass and an upper bound on the right event mass, with a strict gap between
them. Underapproximations on both sides do not establish the required right upper bound.
For a relation disjunction, a certificate also refutes additive splitting into the
corresponding coupling assertions, via `MassDeficitCert.refutes_oplus`.

The fair/biased coin certificate uses `A = B = {false}`: the fair coin assigns mass
`1/2`, while the biased coin assigns `1/4`. Every equality-related partner of `false`
is `false`, so the smaller right mass prevents an equality coupling even though both
coins have identical supports and total mass one.

`Prob.quadSem F G P Q` is the language-independent weighted semantic judgment.
`Prob.BugCert F G R` stores a concrete pair of initial states and a mass-deficit
certificate for their actual outputs from unit weights. Its `refutes` theorem also
requires proof that these initial weights satisfy `P`; it then refutes the judgment
with coupling postcondition `R`. Stronger postconditions can be refuted by entailment.
The sampling example instantiates this judgment with bind and the fair/biased kernels.

These are sound certificates, checked by Lean. This stage supplies neither a search
procedure nor a completeness theorem for all failed couplings. It needs no Strassen
theorem, probabilistic command syntax, or loop soundness theorem.

## Increasing limits and algebraic boundaries

The mass and bind continuity theorems require increasing sequences. Bind is continuous
in either argument; if both input weights and continuations increase, it preserves
their common-index limit. These facts support future Kleene loop semantics.

The checked counterexamples show:

- duplicating a unit weight changes it, so addition is not idempotent;
- adding two subprobabilities need not preserve the mass bound;
- taking the pointwise supremum of two incomparable subprobabilities need not preserve
  the mass bound;
- mass and bind need not preserve arbitrary binary suprema.

Subprobabilities are closed under increasing sequential limits and under bind by
subprobability continuations. They are not treated as a pointwise complete lattice.
ENNReal's convention `0 * ∞ = 0` is retained. Cancellation, division, and normalization
require separate hypotheses and are outside this stage.

For the planned increasing-limit proof of loop couplings, a coupling for each marginal
approximation is not enough: construct a coherent increasing family of joint witnesses
before applying increasing-limit results. Other limit constructions would require
their own justification.

## Validation

`RelationalOutcomeLogic.lean` imports the weighted modules so `./scripts/check.sh`
checks their proofs and includes all their declarations in the existing axiom gate.
The gate permits only `propext`, `Classical.choice`, and `Quot.sound` transitively.
The Set development must continue to pass without changing its semantics or examples.

The integrated step 4 check passed on 2026-09-19: 1,552 build jobs and 1,556 library declarations,
all using only the permitted standard axioms.

The next milestones and their acceptance criteria are maintained in
[`typeclass-plan.md`](../typeclass-plan.md).
