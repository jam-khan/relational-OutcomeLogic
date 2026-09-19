# Weighted semantics contract

Status: steps 1–7 of the roadmap, 2026-09-19. The existing Set logic remains the
reference implementation. The weighted development now includes assertions, exact
couplings, quantitative refutation, and a probabilistic while-language with synchronous
loop soundness. The pRHL embedding adds core and one-sided rules, with explicit
whole-loop losslessness for loop-versus-skip reasoning. Guarded unrolling and ranked
mixed asynchronous rules now preserve the complete terminating semantics.

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
predicate, proved invariant under the probabilistic language. Unrestricted
nondeterministic addition must not be silently interpreted as normalized probability
choice. Randomized choices are expressed through sampling kernels with mass one.

The weighted API proves algebraic pure/bind laws directly; it does not install a new
global `Monad` instance on the function-type abbreviation.

## Exact couplings and nontermination

For a subprobabilistic program, mass is termination probability; missing mass records
nontermination. Zero denotes no terminating outcomes. Every sampling primitive carries
a proof of normalization; loops may produce a subdistribution.

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

This is the contract used by the implemented pRHL bridge.
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

These are sound certificates, checked by Lean. Certificate discovery and completeness
for all failed couplings remain separate obligations. The certificate proofs need no
Strassen theorem and are independent of the probabilistic syntax and loop rules.

## Increasing limits and algebraic boundaries

The mass and bind continuity theorems require increasing sequences. Bind is continuous
in either argument; if both input weights and continuations increase, it preserves
their common-index limit. These facts support the implemented Kleene loop semantics.

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

The synchronous loop proof constructs a coherent increasing family of joint witnesses.
A coupling chosen independently for each marginal approximation would not establish
that hypothesis. `IsCoupling.iSup` explicitly requires monotonicity of the joint chain
and proves preservation of both exact marginals and the support relation.

## Probabilistic commands and synchronous loops

`Prob.Cmd α` supplies skip, deterministic state updates, normalized sampling,
sequencing, conditionals, and while over a generic state type. The two sides of a
judgment may use different state types. There is no unrestricted additive branching
command; sampling accepts a kernel only with a proof that every input produces total
mass one.

`sem` maps a starting state to its terminating output weights. `semLift` executes a
command from a weighted input using bind. Every command preserves the subprobability
bound, and its lifted semantics cannot increase total mass. Loop-free commands preserve
all input mass. Addition and scaling remain laws of the lifted raw-weight semantics.

A loop starts with a zero approximation. The next approximation returns a unit weight
when the guard is false, or executes the body followed by the previous approximation
when the guard is true. These approximations increase; their supremum equals the
least fixed point of the loop functional. Increasing-limit continuity proves unfolding
and subprobability preservation. Terminating outcomes satisfy the negated guard;
a guard that is always true produces zero terminating weight.

The synchronous rule requires the guards to agree at related states and the body to
preserve the relation on guarded inputs. The proof selects one body-joint kernel,
then executes its product loop. Each product approximation has exactly the two
separate program approximations as marginals. Its increasing limit yields the loop
coupling, with the invariant and both exit conditions. Neither losslessness nor a
finite iteration bound is assumed.

`Prob.Rules` lifts these facts into weighted judgments: consequence, skip, sequencing,
additive splitting, common scaling, assignment, sampling, synchronized conditionals,
and synchronous while.

The coin-retry example repeatedly samples a fair coin until its stopping value occurs.
It proves almost-sure termination and that every finite approximation has mass strictly
less than one. Two loops with opposite Boolean encodings are related using the sampling
and while rules. Additional examples prove a joint-divergence specification and reject
comparing divergence with terminating skip.

## pRHL embedding and one-sided rules

`Prob.prhl R c d S` requires an exact `S`-coupling of the output subdistributions
from every pair of starting states satisfying `R`. `prhl_iff_quad` proves:

```text
prhl R c d S ↔ quad (couple R) c d (couple S)
```

The generic `prhlSem_iff_quadSem` proves the corresponding result for arbitrary
discrete kernels, independently of command syntax. Its forward direction sequences
the input coupling with pointwise output couplings; its reverse direction specializes
to point masses. Both directions cover raw input weights without normalization.

The core pRHL rules are obtained through the weighted rules. One-sided assignment,
sampling, conditionals, loops, and symmetry are also exposed. `LosslessOn P c` requires
total output mass one at every starting state in `P`. For a loop against skip, the
whole loop must be lossless on the appropriate projection of the relational invariant.
The body must preserve the relation against skip at guarded states. The proof first
establishes invariant and exit support, then combines that support property with
whole-loop losslessness to obtain an exact coupling against the unchanged point mass.

Checked examples derive an unbounded synchronous retry coupling through the new rules,
and derive retry versus skip in both directions over different state types. A divergent
loop with a lossless body refutes even the universally true postrelation against skip,
demonstrating why the whole-loop condition cannot be dropped. `MassDeficitCert.refutes_prhl`
and `BugCert.refutes_prhl` transport quantitative refutation; the fair/biased example
uses the existing finite-event certificate to reject an actual pRHL sample specification.

This is a semantic equivalence with named admissible rules for the current language.
An inductive derivation translation, external procedure/module interfaces, and
semiring abstraction remain separate work. See the
[rule inventory and scope](prhl-subsumption.md).

## Guarded unrolling and ranked mixed scheduling

Guarded two-iteration unrolling preserves full raw-weight loop semantics. Its positive
approximations equal the original approximations at the cofinal indices `2 * n + 1`.
No losslessness premise is needed. The Boolean-OR accumulator client has a separate
mass-one proof and a certified faulty variant whose observed false probability changes
from one half to one quarter while its observed support stays the same.

`Prob.AsyncSchedule` selects left-only, right-only, joint, or done modes. Local body
couplings preserve the invariant; unilateral couplings also decrease a natural rank
and have the passive point mass as an exact marginal. The latter forces mass one for
the advancing body. Done requires both guards false. Joint steps may reset the rank
and may lose mass through matched divergence; no uniform rank bound or global loop
termination is required.

The implementation fixes one joint body kernel. `pushforward_loopSem` proves the
complete projection equality by two inequalities: finite joint approximants project
below the original limit, and finite original approximants lie below the projected
joint limit. The reverse direction inducts on original fuel and on rank for passive
steps. `AsyncSchedule.isCoupling_loop` then establishes both exact terminal marginals
and the invariant with exit conditions. These equations are conclusions, not schedule
premises. The corresponding Set theorem proves exact outcome-set images and bitotal
coupling, extending the existing weak-atom partial-correctness rule.

The rank requirement covers finite unilateral catch-up between joint steps. It does
not cover arbitrary almost-surely terminating unilateral phases with self-loops; those
need a further phase theorem. Random draws in the current clients are aligned jointly.
See [loop alignment](loop-alignment.md) for the theorem inventory and examples.

## Validation

`RelationalOutcomeLogic.lean` imports the weighted modules so `./scripts/check.sh`
checks their proofs and includes all their declarations in the existing axiom gate.
The gate permits only `propext`, `Classical.choice`, and `Quot.sound` transitively.
The Set development must continue to pass without changing its semantics or examples.

The integrated step 7 check passed on 2026-09-19: 1,570 build jobs and 2,143 library declarations,
all using only the permitted standard axioms.

The next milestones and their acceptance criteria are maintained in
[`typeclass-plan.md`](../typeclass-plan.md).
