# RelOL implementation roadmap

Updated 2026-09-19 after implementing quantitative refutation certificates on top of
weighted assertions and exact couplings. This replaces the earlier abstraction-first
proposal. The Set coupling tier, compiler, heterogeneous examples, certificates,
symbolic execution, and axiom gate already exist; they are prerequisites, not work
to repeat.

## Fixed decisions

- Preserve the existing Set development as the regression reference.
- Keep Lean/Mathlib v4.32.1; no additional dependency is needed for this foundation.
- Use raw `Weight α := α → ℝ≥0∞`, with total addition and pointwise order.
- Enforce mass at most one at the future probabilistic language boundary.
- Use joint weights with exact marginals for the first probabilistic lifting.
  Both sides may diverge, but their termination masses must agree.
- Prove concrete weighted results before extracting a generic outcome-model interface.
- Restrict limit-preservation laws to increasing families.

See the [semantic contract](docs/weighted-semantics.md) and the supporting
[infrastructure audit](notes/infrastructure-audit.md).

## 1. Baseline and semantic contract — complete

The pre-change baseline `af4bac907d0af27e7e38ca779857d33735d63603` passed
`./scripts/check.sh`: 651 build jobs, 1,217 declarations, standard axioms only.
The contract fixes raw weights, the mass invariant, exact coupling semantics,
divergence, increasing limits, and the Set regression requirements.

## 2. Concrete weighted foundation — complete

- `Algebra/Weight.lean`: pure, bind, support, mass, `IsSubprob`, `IsProbability`;
  algebraic monad laws, addition/scaling laws, support laws, monotonicity, and mass
  preservation. Continuation hypotheses can be restricted to the input support.
- `Algebra/WeightOrder.lean`: mass and bind preservation of increasing limits,
  subprobability closure, joint increasing limits, and Mathlib omega-continuity interfaces.
- `Algebra/WeightBoundary.lean`: failures of additive idempotence, subprobability
  closure under addition/arbitrary pointwise suprema, and arbitrary-supremum
  preservation by mass and bind.

All three modules are imported by the root and covered by the build and axiom gate.
Post-integration validation passed: 1,543 build jobs and 1,301 library declarations,
with standard axioms only and no proof placeholders.
This stage does not implement weighted assertions, probabilistic commands, couplings,
a generic outcome-model class, or pRHL subsumption.

## 3. Weighted assertions and exact couplings — complete

- `Prob/Assertions.lean`: assertions over pairs of weights, support atoms, positive and
  exact mass constraints, additive splitting, scalar images, and structural rules.
  Associativity, commutativity, empty units, and consequence require no idempotence.
- `Prob/Coupling.lean`: joint weights, exact marginals, relation support, equal-mass
  necessity, pure/zero/diagonal couplings, equality characterization, addition, scaling,
  and sequencing. `IsCoupling.bind` proves both marginals of the constructed joint;
  `Coupled.bind` selects continuation witnesses at related pairs. No division or
  finite-mass assumption is needed.
- `Prob/CouplingAssertions.lean`: coupling as a weighted assertion, relation weakening,
  addition of coupled pieces, common scaling, and equal-mass consequences.
- `Prob/Support.lean`: exact weighted coupling implies the existing Set coupling on
  supports. This bridge is one-way and leaves existing definitions unchanged.
- `Prob/Examples.lean`: checked acceptance examples and probability-sensitive boundaries.

Acceptance met:

- Both fair and biased coins have mass one and identical supports, but only equal
  distributions admit equality coupling.
- An explicit opposite-outcome joint couples two fair coins. Sequencing with negation
  turns this into an equality coupling and proves equality of the resulting weights.
- A fair coin splits into two half-mass pieces, but cannot split into two unit-mass pieces.
- Unequal termination masses cannot be coupled exactly; zero/zero can, and zero/unit cannot.
- Scaling works even for infinite raw weights. The probabilistic language will impose
  subprobability bounds separately.

All five modules are root-imported for the build and axiom gate. The integrated check
passed: 1,548 build jobs, 1,463 library declarations, no proof placeholders, and standard
axioms only. This completes the weighted assertion/coupling milestone, not probabilistic
loop soundness or pRHL subsumption.

## 4. Sound quantitative refutation certificates — complete

- `Prob/EventMass.lean`: finite-event mass and the necessary bound `μ(A) ≤ ν(B)`
  whenever `R(A) ⊆ B` and an exact `R`-coupling exists. Only the events must be finite;
  carriers and total weights may be infinite.
- `Prob/BugCert.lean`: `MassDeficitCert` packages the events, image cover, and strict
  deficit `ν(B) < μ(A)`. Its soundness theorem refutes every exact joint witness.
  `of_bounds` also supports certified left lower/right upper bounds. A deficit for a
  union relation refutes additive splitting between the corresponding coupling assertions.
- `Prob/Quadruple.lean`: language-independent weighted semantic judgments.
  `Prob.BugCert` ties a deficit to the actual outputs from two explicit initial states;
  membership in the precondition is required when refuting the specification.
- `Prob/CertificateExamples.lean`: fair/biased coin certificates using exact masses
  and conservative bounds; additive coupling and sampling-specification refutations;
  unequal termination masses, a finite event over natural-number states, and exclusion
  of false certificates for a valid equality coupling.

The coin certificate uses the false event on both sides: mass one half versus one
quarter, even though both distributions have unit mass and identical supports.
The certificate therefore detects probability disagreement rather than merely a
missing possible outcome.

All four modules are root-imported. The integrated check passed: 1,552 build jobs,
1,556 library declarations, no proof placeholders, and standard axioms only.

This proves soundness without Strassen. Certificate discovery and completeness remain
separate extensions. Probabilistic syntax, mass-preserving command semantics, and loop
rules are not supplied by this milestone.

## 5. Probabilistic commands and synchronous loops — next

Proposed modules: `Prob/Lang.lean`, `Prob/Rules.lean`.

Reuse the weighted `Prob.quadSem` judgment. Add skip, assignment, normalized sampling,
sequencing, conditionals, and while.
Keep probabilistic choice distinct from unrestricted additive branching. Prove
subprobability preservation for every command, including loops.

Construct one coherent product-loop witness. Its approximants must increase, their
marginals must equal the separate program approximants, and their limit must retain
the relation and exact marginals. Reuse `WeightOrder` and Mathlib fixed-point results.

Acceptance: synchronous relational loop soundness, including valid divergent cases
under the exact-subdistribution convention. Independently chosen finite witnesses
are insufficient to justify the limit.

## 6. Genuine pRHL subsumption

Proposed module: `Subsumption/PRHL.lean`.

State pRHL using the agreed exact subdistribution semantics. Prove the semantic bridge
and derive sampling, sequencing, consequence, conditionals, and synchronous loops
through the weighted RelOL rules.

Acceptance: a probabilistic example with an unbounded loop and an explicit derivation.
Any termination assumptions belong in the theorem statements. The existing
possibilistic Set coupling bridge is not genuine pRHL subsumption.

## 7. Asynchronous loops, first Set then probability

The Set work can proceed independently of steps 3–6. Add left-only, right-only, and
joint phases with the appropriate termination assumptions, and use loop unrolling
or differing strides as a client. Weak-atom async RHL and one-sided coupling rules
already exist and should be reused.

For probability, establish losslessness of the required one-sided phases and exact
marginal preservation under the scheduler. This remains a separate research milestone
after the synchronous product-loop construction works.

Acceptance: an actual transformation with different iteration structures. Generic
continuity does not itself establish scheduler correctness.

## 8. Shared algebra and semiring parametricity

Use the concrete Set and ENNReal proofs to choose a small outcome-model interface.
Separate assumptions for idempotence, scaling, support, and increasing limits. Preserve
the Set examples through explicit bridges and audit each rule's hypotheses.

Then develop an admissible weight-algebra factory and establish which relational
results instantiate for Boolean/set weights and ENNReal. An ENNReal implementation
alone is not semiring parametricity; a bare `Semiring` does not provide positivity of
support or the limit structure required for loops.

Corrections to the previous proposal:

- Raw weights are a complete lattice; the mass-bounded subset is not closed under
  arbitrary pointwise suprema.
- Underapproximation and unary embedding should be inspected individually; the old
  blanket claim that they require idempotence was too broad.
- Probabilistic couplings require joint weights and marginal equations, not just
  the support-membership interface used for possibilistic matching.

Acceptance: substantial shared proofs instantiate in both models, with every additional
algebraic assumption stated explicitly.

## 9. Explicit derivations and substantial examples

Introduce explicit derivations and soundness; reconstruct selected NI/GNI, compiler,
and probabilistic examples through the rules. The Set fragment can begin independently.
Restrict completeness claims to the assertion language and rule inventory actually proved.

Acceptance: one substantial transformation with both a correctness derivation and a
certified faulty variant, exercising splitting, sequencing, coupling, and loops.

## 10. Automation and machine-level realism

Extend the existing `symexec` and certificate objects with bounded discovery and checked
reconstruction. Add the bitvector/overflow operations needed by the selected case study.
Keep bounded reachability evidence distinct from exhaustive evidence.

Acceptance: short scripts regenerate the certificates without nonstandard axioms.
Broader arrays, casts, and mixed probability/nondeterminism follow a demonstrated need.

## Validation and the next decision point

Run `./scripts/check.sh` at each milestone. Import production modules in the root so
the axiom gate checks their declarations. Keep standard axioms only and preserve the
existing Set examples. Put mass bounds and chain monotonicity in theorem statements.

The next implementation target is step 5: probabilistic commands and coherent synchronous
loops, using the weighted algebra and exact coupling API. Sound quantitative refutation
is now implemented. The first complete probabilistic logic milestone remains step 6,
with a genuine synchronous pRHL bridge. Full Strassen completeness, arbitrary-semiring coupling theory, and
probabilistic asynchronous soundness remain separate obligations.
