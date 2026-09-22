# RelOL implementation roadmap

Updated 2026-09-21 after shared algebra and semiring generalization: common structural
proofs, constructed scalar-weight semantics, generic exact couplings and certificates,
synchronous/ranked asynchronous loops, and five concrete scalar instances. The earlier
randomized-search case includes asynchronous early-exit correctness, quantitative
splitting, trial savings, and refutation of the same internal contract. The case was
completed before algebra extraction; the original milestone numbers and historical
validation records are retained below. The Set coupling tier,
compiler, heterogeneous examples, certificates,
symbolic execution, and axiom gate already exist; they are prerequisites, not work
to repeat.

## Fixed decisions

- Preserve the existing Set development as the regression reference.
- Keep Lean/Mathlib v4.32.1; no additional dependency is needed for this foundation.
- Preserve raw `Weight α := α → ℝ≥0∞` as the concrete probability carrier. The
  constructed generalization is `Algebra.Weighted.Weight K α := α → K`.
- Enforce normalized sampling and prove that every probabilistic command preserves
  the subprobability bound.
- Use joint weights with exact marginals for the first probabilistic lifting.
  Both sides may diverge, but their termination masses must agree.
- The completed generic interface and scalar factory are grounded in the preceding
  concrete weighted proofs and algorithmic case.
- Restrict limit-preservation laws to increasing families.
- Keep normalization, exact support laws, scalar summation, and increasing-limit
  assumptions separate. Do not assume infinite sums from a bare semiring.
- Completeness results are outside the current plan, as requested. Explicit derivation
  datatypes and proof-tree translation are optional; semantic rules remain the working API.

See the [semantic contract](docs/weighted-semantics.md) and the supporting
[infrastructure audit](notes/infrastructure-audit.md).

## Review after step 6

Source review found no soundness defect in the weighted algebra, increasing-limit
loops, coherent synchronous joint construction, pRHL bridge, or certificate proofs.
The proof gate checks Lean proofs; the review additionally checked that theorem
statements match the documented semantics and side conditions.

Cleanups completed: one-sided sampling examples now use their named one-sided rules;
a command-indexed example exercises `BugCert.refutes_prhl` as well as the existing
mass-deficit path; README describes both current models; the obsolete handoff in
`context.md` is explicitly historical. Full validation after these changes passed:
1,562 build jobs, 1,801 library declarations, no proof placeholders, standard axioms only.

The review identified two distinctions for step 7. Guarded block unrolling is not a general
asynchronous scheduler. Also, normalized bodies and fair scheduling do not alone
preserve terminal marginals: opposite coupling of a terminating branch with a
divergent branch can leave both standalone loops with mass one half while the joint
loop never terminates. Progress and preservation of termination mass must be proved.

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

This proves soundness without Strassen. Certificate discovery is separate work;
certificate completeness is not a current target. Probabilistic syntax, mass-preserving command semantics, and loop
rules are not supplied by this milestone.

## 5. Probabilistic commands and synchronous loops — complete

- `Prob/Loop.lean`: finite-fuel weighted approximations, monotonicity, increasing-limit
  semantics, unfolding, the least-fixed-point characterization, subprobability bounds,
  exit-guard support, and always-true divergence.
- `Prob/Lang.lean`: generic-state skip, assignment, normalized sampling, sequencing,
  conditionals, and while. Every command preserves subprobabilities; every loop-free
  command preserves all mass. Lifted semantics retains addition and scaling laws.
- `Prob/LoopCoupling.lean`: increasing-limit preservation of exact marginals, a single
  joint body kernel, its coherent product-loop approximations, and synchronous loop
  coupling. The proof gives both exact marginals and the invariant with exit conditions.
- `Prob/Rules.lean`: consequence, skip, sequencing, additive splitting, scaling,
  assignment, sampling, synchronized conditionals, and synchronous while.
- `Prob/Geometric.lean`, `Prob/LoopExamples.lean`: almost-surely terminating fair-coin
  retry with every finite approximation strictly below mass one; two opposite Boolean
  encodings related through the sampling and while rules; joint divergence and rejection
  of a divergence-versus-skip specification.

The synchronous theorem assumes synchronized guards and an invariant-preserving body
coupling. It does not assume losslessness, a finite fuel bound, or independently
selected finite witnesses. The product-loop construction supplies the increasing
joint chain needed by the marginal-limit argument.

All six modules are root-imported. The integrated check passed: 1,558 build jobs,
1,746 library declarations, no proof placeholders, and standard axioms only. Existing
Set examples and the quantitative certificate development continue to pass.

This supplies the probabilistic language and weighted relational rules used by step 6.

## 6. Exact-coupling pRHL subsumption — complete

- `Subsumption/PRHL.lean`: pointwise exact-coupling pRHL and the equivalence
  `prhl R c d S ↔ quad (couple R) c d (couple S)`. A generic kernel version is
  independent of syntax and allows different input/output state types. Core skip,
  consequence, assignment, sampling, sequencing, conditional, and synchronous while
  rules are exposed through the weighted rules; case analysis, false preconditions,
  and semantic replacement are also available.
- `Prob/OneSided.lean`: coupling symmetry, exact coupling against a point mass iff
  mass is one and support satisfies the relation, loop support invariants, `LosslessOn`,
  and left/right weighted loop-versus-skip rules.
- `Subsumption/PRHLOneSided.lean`: pRHL symmetry and one-sided assignment, sampling,
  conditional, and while rules. One-sided while requires losslessness of the whole
  loop on the relevant projection of the invariant.
- `MassDeficitCert.refutes_prhl` and `BugCert.refutes_prhl`: quantitative certificates
  refute a pRHL specification at an input pair satisfying its precondition.
- `Subsumption/PRHLExamples.lean`: synchronous unbounded retry derived through
  sampling and while, the weighted export of that proof, heterogeneous one-sided
  unbounded retry in both directions, sampling/assignment sequencing, and a fair/biased
  pRHL specifications refuted both directly by the finite-event certificate and
  through a command-indexed `BugCert`.

The retry example proves total termination mass one while every finite approximation
has mass strictly below one. A divergent loop with a lossless, invariant-preserving
body refutes even a universally true postrelation against skip. This checks why
whole-loop losslessness is necessary for one-sided exact coupling.

This is semantic equivalence and named admissible rules for the current command
language. The examples compose these rules in Lean; an inductive derivation datatype
and proof-tree translation are optional extensions. External procedure/module/oracle semantics
and EasyCrypt integration are not claimed. The exact rule inventory is recorded in
[`docs/prhl-subsumption.md`](docs/prhl-subsumption.md).

All four new modules are root-imported. The integrated check passed: 1,562 build jobs,
1,796 library declarations, no proof placeholders, and standard axioms only. The
existing Set development and all earlier probabilistic examples continue to pass.

## 7. Loop alignment and ranked mixed asynchronous loops — complete

### 7a. Guarded block unrolling and its client — complete

`Prob/Unroll.lean` proves the exact positive-fuel identity
`loopIter g (guardedDouble g k) (n + 1) = loopIter g k (2 * n + 1)`.
Cofinality then proves full loop equality. `sem_guarded_unroll` and its lifted
corollary establish the source transformation `c` to `c; if g then c else skip`
inside a while-loop. The kernel theorem allows raw weights and divergence.

`Prob/UnrollExamples.lean` proves correctness of a fair-bit Boolean-OR/countdown loop
and its guarded double-body version for every count and initial accumulator, through
pRHL sampling/while and semantic replacement. Count induction independently proves
mass one. The faulty unguarded version has false probability one quarter instead of
one half at `(1, false)`, despite identical observed Boolean supports. An actual
mass-deficit certificate and program-indexed `BugCert` refute the observed equality
specification. All these claims concern full loop semantics.

### 7b. Mixed left-only, right-only, and joint phases — complete

- `Algebra/Alignment.lean`: shared left, right, both, and done modes and their swap.
- `Async.lean`: Set projection equality by two inclusions, a locally specified
  `SetAsyncSchedule`, its bitotal loop coupling, and `quad_while_async_couple`.
  `Examples/Async.lean` applies it to countdown by one versus two for every natural
  starting count, including odd counts.
- `Prob/AsyncLoop.lean`: `AsyncSchedule`, one fixed selected joint kernel, and the
  generic `pushforward_loopSem` theorem. Finite product approximants project below
  the original limit; original-fuel/rank induction proves the reverse inequality.
  `AsyncSchedule.isCoupling_loop` proves both exact terminal marginals and exit support;
  `coupled_loop_async` exposes their coupling. Final marginal equality is not a premise.
- `Subsumption/PRHLAsync.lean`: schedule swapping and weighted/pRHL mixed while rules.
- `Prob/AsyncExamples.lean`: different deterministic strides, fresh random draws
  aligned while one program performs extra deterministic bookkeeping, mirrored
  right-only catch-up, equality of observed sum distributions for every count,
  independent/transferred mass-one proofs, joint divergence, and progress/mass
  boundary examples.

The implementation improves on the proposed uniform bound: a natural rank decreases
on every supported unilateral transition, while joint steps can reset it to any
natural value. Nested fuel/rank induction removes the need for one global bound.
Unilateral exact couplings against a passive point mass force body losslessness.
Joint divergence is allowed; whole-program termination is not a theorem premise.

This completes **ranked mixed scheduling**. Almost-surely terminating phases with
unbounded stochastic stuttering and unrestricted fair schedulers remain extensions.
Alignment completeness is outside the plan. The standalone lossless one-sided loop rule already
supports geometric retry against skip, but that fact alone does not extend the ranked
mixed theorem. See [`docs/loop-alignment.md`](docs/loop-alignment.md) for the scope.

All eight new modules are root-imported. The integrated step 7 check passed:
1,570 build jobs, 2,143 library declarations, no proof placeholders, and standard
axioms only. Independent source reviews found no mathematical issue in the unrolling,
certificate, Set projection, or probabilistic projection proofs.

## 8. Shared algebra and semiring parametricity — complete

- `Algebra/OutcomeModel.lean`, `Generic/Assertions.lean`, and `Generic/Rules.lean`
  provide additive outcome semantics and shared structural assertion, sequencing,
  choice, and splitting proofs. `Generic/Concrete.lean` instantiates them with the
  existing Set and ENNReal APIs without replacing those APIs.
- `Algebra/Scalar.lean` states the additional arbitrary-summation laws explicitly.
  `Algebra/Weighted.lean`, `WeightedModel.lean`, and `WeightedCoupling.lean` construct
  weights, pure/bind, addition, scaling, mass, exact marginals, and supported coupling
  composition. The construction permits noncommutative multiplication. Positivity
  and no zero divisors are separate requirements for exact support equivalences;
  the coupling construction itself needs neither.
- `Algebra/OrderedScalar.lean`, `IterationModel.lean`, and `WeightedOrder.lean`
  state and lift order/increasing-limit assumptions. `Generic/Iteration.lean` proves
  unfolding and least-fixed-point iteration once for the shared model.
- `Generic/WeightedLogic.lean` proves the generic statewise coupling/outcome-judgment
  equivalence. `Generic/LoopCoupling.lean` constructs coherent synchronous joint
  executions. `Generic/AsyncLoop.lean` proves exact full-loop marginals for ranked
  mixed schedules, with local one-step obligations and strict unilateral rank descent.
  Final marginal equality is a conclusion, not a scheduler premise.
- `Generic/WeightedCertificates.lean` derives finite-event coupling bounds from
  the scalar laws and proves generic `MassDeficitCert` and actual-input `BugCert`
  soundness. Scalar order determines the comparison; tropical order reverses
  numerical cost. No subtraction, normalization, or extra event-bound axiom is used.
- `Algebra/Instances/` contains five checked instances: Boolean reachability,
  ENNReal weights, extended-natural trace counts, tropical minimum costs, and
  noncommutative languages of finite traces. Their summations agree with canonical
  finite-subsum suprema. `Generic/InstanceExamples.lean` instantiates common route and
  countdown proofs and certifies count/cost errors invisible to reachability.
  `Generic/TraceExamples.lean` checks ordered logging and its faulty swap.
  `Generic/AsyncExamples.lean` runs one mixed schedule with joint weighted steps and
  unilateral bookkeeping in multiple scalar models.
- `Generic/Compatibility.lean` proves agreement with old Set/ENNReal full loops and
  ENNReal coupling and pRHL definitions. `Generic/BooleanBridge.lean` preserves
  union, sequencing, and full loops under Boolean encoding and proves equivalence
  between Boolean exact marginals and existing bitotal Set matching.

See [semiring models](docs/semiring-models.md) for the operations, theorem inventory,
clients, and TOPLAS comparison. The supported class consists of total summation
semirings with explicit order/continuity laws for loops. It does not encode every
partial weight algebra from TOPLAS. Finite-word languages record terminating traces;
infinite-word observations and mixed probability/demonic choice remain outside scope.

Acceptance met: substantial structural, coupling, certificate, synchronous-loop, and
ranked-asynchronous proofs are shared across actual constructed models. A bare
`Semiring` is never treated as supplying infinite sums. Normalization remains a
separate ENNReal property, and the probability-bounded subset is not incorrectly
declared a pointwise complete lattice. The original Set-specific proof APIs remain
available alongside the checked compatibility maps.

The integrated generalization check passed: 1,613 build jobs, 3,088 library
declarations, no proof placeholders, and standard axioms only. Concrete bridge
checks also confirmed that Boolean weights select the intended factory instance
when imported together with the existing Set/probability models.

## 9. End-to-end algorithmic case — complete

The [randomized-search case](docs/randomized-search.md) compares a full budget of
independent Bernoulli trials with early exit at the first hit, for every budget and
normalized miss/hit distribution.

- `Prob/Search.lean`: actual commands, exact full-scan output weights, and mass one.
- `Prob/SearchCoupling.lean`: a mixed schedule with joint draws before success and
  unilateral cleanup afterwards; exact output marginals, pRHL/weighted judgments,
  observed answer equality, and a coupled non-strict trial bound.
- `Prob/Restriction.lean`: restrict a single joint by a shared observable, preserving
  exact restricted marginals; split the result into complementary quantified pieces.
- `Prob/SearchOutcome.lean`: a weighted program judgment whose additive failure and
  success pieces have exact masses `q^n` and `S(n)`, with `q^n + S(n) = 1`.
  Failure requires both remaining budgets to be zero, including at initial budget zero.
- `Prob/SearchCost.lean`: for budgets at least two, the probability of a nonempty
  proper-prefix success is at least the hit probability. This is the strict-saving
  result; the non-strict cost bound alone does not establish an improvement.
- `Prob/SearchCertificates.lean`: a cached-draw command has failure probability `q`
  instead of `q^n`. For `0 < q < 1` and `n > 1`, an actual command-indexed certificate
  refutes observed equivalence even though both programs have mass one and the same
  Boolean support. Zero/one-budget agreement is also proved.

This completes the parameterized correct/faulty algorithmic case. It uses the existing
semantic proof-rule API; it does not require a new derivation datatype. The example
combines relational correctness with class-specific masses and a quantitative
counterexample. It is not a production application or a proof of expected running time.

All six modules are root-imported. The integrated check passed: 1,576 build jobs,
2,312 library declarations, no proof placeholders, and standard axioms only.
Independent reviews checked the joint restriction, scheduler, cost events, and
zero-budget specification. No new dependency was needed.

Optional: if an external integration needs explicit proof objects, introduce a
derivation datatype with a fixed rule inventory and prove soundness by induction.
Semantic pRHL equivalence already holds; proof-tree translation is a separate theorem.

### Presentation and API consolidation — complete

- `Prob/Observation.lean` now owns the deterministic pushforward helpers previously
  local to asynchronous loops, preserving their names. It supplies coupling and
  judgment transport plus `BugCert.refutes_of_observation`, independent of command syntax.
- `resultSpec_couple` and `resultSpec_observed_eq` expose the observable consequence
  of the quantitative postcondition. `Prob/SearchCase.lean` is the complete case's
  public import; `cached_outcome_spec_refuted` refutes exactly the judgment proved by
  `search_outcome_quad`, substituting cached search for early exit.
- The [theorem guide](docs/theorem-guide.md) gives imports, checked client examples,
  loop obligations, and the observation/refutation workflow. The reference paper
  now includes weighted semantics, the semantic pRHL bridge, ranked asynchronous
  rules, finite-event certificates, and the search case with a matching theorem index.
  Existing Set-specific results remain explicitly scoped to that model.

Validation passed: 1,578 build jobs, 2,321 declarations, no proof placeholders, standard
axioms only. The guide's Lean examples compile from the public import. Independent
review checked the observed certificate's precondition and orientation and confirmed
that the correct and faulty variants use the same contract. This is presentation of
the checked results, not a completed related-work or publication novelty assessment.

## 10. Automation and machine-level realism

1. Extend existing `symexec` and certificate objects with discovery for finite-support
   rational examples, followed by Lean-checked reconstruction. Reuse the current
   certificate soundness theorems; discovery need not be trusted.
2. For loops, certify the required lower and upper event-mass bounds. A bounded run
   gives no automatic upper bound on all remaining probability, so certify the tail
   bound before using a bounded search result to refute a specification.
3. Add bitvector/overflow operations only where the chosen case needs them. Preserve
   standard-axiom checks for all reconstructed results.

Acceptance: short scripts reproduce correctness/refutation results and report bounds
with their hypotheses. Broader arrays, casts, and mixed probability/nondeterminism
follow a demonstrated need.

## Deferred integration and paper work

EasyCrypt-in-Lean integration waits for an available interface. Match its state,
sampling, observation, and divergence semantics before reusing correctness results;
procedure/module/oracle support must be handled explicitly if present. No current
milestone depends on access to that project.

The main algorithmic case and reference paper's theorem map are now checked. The
presentation distinguishes the semantic embedding, asynchronous rule, quantitative
outcome contract, refutation certificate, and the now-completed generic algebra and
five scalar models. Revisit related work before making novelty claims. Finite-event
certificates prove soundness; no discovery completeness or Strassen converse is a
current objective. Continuous probability and approximate couplings remain out of scope.

## Validation and the next decision point

Run `./scripts/check.sh` at each milestone. Import production modules in the root so
the axiom gate checks their declarations. Keep standard axioms only and preserve the
existing Set examples. Put mass bounds and chain monotonicity in theorem statements.

Steps 1–9 and the case's presentation/API consolidation are complete. Remaining work
is driven by the intended artifact and paper contribution:

1. Add step 10's finite-support certificate discovery if automation is part of the
   contribution, reconstructing every result through the sound certificate API.
2. Polish the paper's examples, assumption table, and comparison with the TOPLAS model
   family and related relational logics. The implemented theorem inventory is the
   boundary for claims; publication novelty remains a separate research assessment.
3. When EasyCrypt-in-Lean exposes an interface, establish semantic compatibility and
   reuse its infrastructure through the existing kernel/pRHL bridge. This work remains
   deferred until that interface is available.

Completeness is excluded. Explicit derivation objects, expected-cost semantics,
machine-level realism, external integration, and more general almost-sure phase
scheduling are optional extensions driven by a concrete need.
