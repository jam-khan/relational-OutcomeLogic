# pRelOL core rules: Lean source index

This is a reading index for the implemented development on `prototype-3`, checked
on 22 September 2026. It selects 59 core declarations; it is not an exhaustive API
reference. Each name below is fully qualified and can be used after
`import RelationalOutcomeLogic`. Follow the source link to read the exact statement
and proof. For broader navigation, see the [theorem guide](../theorem-guide.md).

Source links and line anchors follow the reorganized module tree. Declaration
namespaces are preserved: a file under `Examples/` can still declare a theorem in
`RelOL.Prob.Search`, and bridge theorems retain their `RelOL.Generic` names.

Read the concrete Set and probability layers first if the generic algebra obscures
the idea. The shared layer explains which arguments can subsequently be reused.

## 1. Shared outcome judgments and structural rules

These rules use `OutcomeModel M`: an additive commutative monoid of outcomes with
the pure/bind monad laws, zero annihilation, and bind distributing over addition
in both arguments. No
idempotence, normalization, scalar order, or termination assumption is implicit.
For arbitrary semantic transformers, splitting needs their additivity explicitly;
the kernel version obtains it from bind. `P ⊕ Q` decomposes both input outcomes
additively; its pieces need not have disjoint support.

| Declaration | Reading target / assumptions | Source |
| --- | --- | --- |
| `RelOL.Generic.quadSem_exactly_iff` | An exact-input judgment is precisely its postcondition on the actual outputs. | [Generic/Rules](../../RelationalOutcomeLogic/Generic/Rules.lean#L19) |
| `RelOL.Generic.quadSem_consequence` | Strengthen the precondition and weaken the postcondition. No outcome algebra is needed. | [Generic/Rules](../../RelationalOutcomeLogic/Generic/Rules.lean#L29) |
| `RelOL.Generic.quadSem_swap` | Swap the two programs and the argument order of both assertions. | [Generic/Rules](../../RelationalOutcomeLogic/Generic/Rules.lean#L42) |
| `RelOL.Generic.quad_skip` | Pure kernels preserve any relational outcome assertion. | [Generic/Rules](../../RelationalOutcomeLogic/Generic/Rules.lean#L61) |
| `RelOL.Generic.quad_seq` | Compose through an intermediate assertion, using associativity of bind. | [Generic/Rules](../../RelationalOutcomeLogic/Generic/Rules.lean#L65) |
| `RelOL.Generic.quad_split` | Execute each additive input piece through the same two kernels. | [Generic/Rules](../../RelationalOutcomeLogic/Generic/Rules.lean#L77) |
| `RelOL.Generic.quad_choice` | Both premises have the **same precondition**; add their kernels and split their postconditions. This is raw additive choice, not normalized probabilistic choice. | [Generic/Rules](../../RelationalOutcomeLogic/Generic/Rules.lean#L93) |
| `RelOL.Generic.quad_empty` | Empty inputs remain empty. | [Generic/Rules](../../RelationalOutcomeLogic/Generic/Rules.lean#L83) |
| `RelOL.Generic.quad_abort` | Two empty-output kernels establish the empty-outcome assertion from any precondition. | [Generic/Rules](../../RelationalOutcomeLogic/Generic/Rules.lean#L87) |
| `RelOL.Generic.quad_disj` | Prove the same postcondition separately for each disjunctive precondition. | [Generic/Rules](../../RelationalOutcomeLogic/Generic/Rules.lean#L102) |
| `RelOL.Generic.refute_quad` | A concrete permitted pair of input outcomes whose actual outputs violate the postcondition refutes the universal judgment. | [Generic/Rules](../../RelationalOutcomeLogic/Generic/Rules.lean#L111) |

## 2. Exact weighted couplings and the pRHL bridge

Here weights have type `α → K`, with `Semiring K` and `SummationSemiring K`.
`IsCoupling R μ ν J` requires **exact** left and right marginals and
`J (a,b) ≠ 0 → R a b`. `Coupled` existentially hides the joint `J`.
These declarations do not require multiplication to commute, finite support,
positivity of summation, or absence of zero divisors. In the probability instance,
exact coupling requires equal termination mass and permits both sides to diverge.

| Declaration | Reading target / assumptions | Source |
| --- | --- | --- |
| `RelOL.Algebra.Weighted.Coupled.mass_eq` | Every exact coupling has equal total scalar weight on both sides. | [Algebra/Weighted/Coupling](../../RelationalOutcomeLogic/Algebra/Weighted/Coupling.lean#L88) |
| `RelOL.Algebra.Weighted.Coupled.pure` | Related states give a point-mass coupling. | [Algebra/Weighted/Coupling](../../RelationalOutcomeLogic/Algebra/Weighted/Coupling.lean#L115) |
| `RelOL.Algebra.Weighted.Coupled.add` | Add two joints supported by the same relation. | [Algebra/Weighted/Coupling](../../RelationalOutcomeLogic/Algebra/Weighted/Coupling.lean#L142) |
| `RelOL.Algebra.Weighted.Coupled.scale` | Scale both marginals and the joint by the same scalar on the left. | [Algebra/Weighted/Coupling](../../RelationalOutcomeLogic/Algebra/Weighted/Coupling.lean#L155) |
| `RelOL.Algebra.Weighted.Coupled.bind` | Couple inputs, then supply a continuation coupling for every related pair of states. | [Algebra/Weighted/Coupling](../../RelationalOutcomeLogic/Algebra/Weighted/Coupling.lean#L274) |
| `RelOL.Algebra.Weighted.coupled_eq_iff` | An equality-supported exact coupling exists exactly when the two weights are equal. | [Algebra/Weighted/Coupling](../../RelationalOutcomeLogic/Algebra/Weighted/Coupling.lean#L208) |
| `RelOL.Generic.prhl_iff_quad` | Statewise exact coupling is equivalent to the outcome judgment between coupling assertions. This is a semantic equivalence. | [Generic/Coupling](../../RelationalOutcomeLogic/Generic/Coupling.lean#L38) |
| `RelOL.Generic.quad_couple` | Convenient forward direction: lift statewise couplings to arbitrary coupled input weights. | [Generic/Coupling](../../RelationalOutcomeLogic/Generic/Coupling.lean#L64) |

## 3. Limits, synchronous loops, and ranked asynchronous loops

General iteration requires a complete lattice of outcomes and `IterationModel`:
empty is bottom, bind is monotone, and bind preserves increasing countable suprema
in its continuation. Weighted loop coupling additionally uses the ordered
summation laws in `OmegaSummationSemiring`. The loop semantics records terminating
outcomes; an always-true loop has empty semantics.

For synchronous loops, the invariant synchronizes the guards, and the two bodies
preserve that invariant through an exact coupling. No separate losslessness premise
is needed. The proof constructs one joint execution: independently selecting a
coupling for each finite approximation would not supply the monotonicity premise
of the limit theorem.

| Declaration | Reading target / assumptions | Source |
| --- | --- | --- |
| `RelOL.Generic.loopSem_unfold` | The increasing limit of bounded approximants satisfies one-step unfolding. | [Generic/Loops/Semantics](../../RelationalOutcomeLogic/Generic/Loops/Semantics.lean#L79) |
| `RelOL.Generic.loopSem_eq_lfp` | This limit is the least fixed point of the loop functional. | [Generic/Loops/Semantics](../../RelationalOutcomeLogic/Generic/Loops/Semantics.lean#L120) |
| `RelOL.Generic.loopSem_true` | An always-true loop has empty terminating semantics. | [Generic/Loops/Semantics](../../RelationalOutcomeLogic/Generic/Loops/Semantics.lean#L140) |
| `RelOL.Algebra.Weighted.IsCoupling.iSup` | Take the supremum of a **monotone family of joint weights**, preserving exact marginals and support. | [Generic/Loops/Synchronous](../../RelationalOutcomeLogic/Generic/Loops/Synchronous.lean#L38) |
| `RelOL.Generic.prhl_while` | Synchronized guards and a body coupling invariant yield the invariant plus both exit conditions. | [Generic/Loops/Synchronous](../../RelationalOutcomeLogic/Generic/Loops/Synchronous.lean#L132) |
| `RelOL.Generic.quad_couple_while` | The synchronous rule with outcome-level coupling assertions as premises and conclusion. | [Generic/Loops/Synchronous](../../RelationalOutcomeLogic/Generic/Loops/Synchronous.lean#L142) |
| `RelOL.Algebra.Weighted.AsyncSchedule` | **Definition.** A state-pair scheduler selects left/right/both/done. Unilateral body-versus-pure couplings preserve the invariant and strictly decrease a natural rank on every supported joint successor. Both mode only preserves the invariant. | [Generic/Loops/Asynchronous](../../RelationalOutcomeLogic/Generic/Loops/Asynchronous.lean#L27) |
| `RelOL.Algebra.Weighted.AsyncSchedule.isCoupling_loop` | The scheduled product loop has the two original full loops as exact marginals. These marginal equalities are proved, not scheduler premises. | [Generic/Loops/Asynchronous](../../RelationalOutcomeLogic/Generic/Loops/Asynchronous.lean#L243) |
| `RelOL.Generic.quad_couple_while_async` | Lift a valid ranked scheduler to the outcome-level asynchronous while rule. | [Generic/Loops/Asynchronous](../../RelationalOutcomeLogic/Generic/Loops/Asynchronous.lean#L333) |

In unilateral modes, coupling with a pure state forces total weight one. Over
probabilities this is losslessness of that step. Strict natural-rank decrease rules
out an infinite unilateral phase; it is stronger than almost-sure termination of
an unbounded retry phase. Joint steps may reset the rank, and the two programs may
still diverge together. A general weighted outcome-family `While-Fam` rule is not
implemented; the coupling loop rules above and the Set rule below are different APIs.

## 4. Concrete probability commands and one-sided rules

`Prob.Cmd` has skip, assignment, normalized sampling, sequencing, conditionals,
and while. Sampling contains a proof that its kernel has mass one **at every
state**. There is no unrestricted additive-choice constructor. Lifted execution
accepts arbitrary ENNReal input weights; probability bounds are separate predicates.

| Declaration | Reading target / assumptions | Source |
| --- | --- | --- |
| `RelOL.Prob.sem_isSubprob` | Every command has termination mass at most one from a single state. | [Prob/Semantics/Commands](../../RelationalOutcomeLogic/Prob/Semantics/Commands.lean#L90) |
| `RelOL.Prob.sem_isProbability` | A syntactically loop-free command has mass one. | [Prob/Semantics/Commands](../../RelationalOutcomeLogic/Prob/Semantics/Commands.lean#L120) |
| `RelOL.Prob.quad_scale` | Scale the input and output assertions by the same ENNReal scalar. | [Prob/Logic/Rules](../../RelationalOutcomeLogic/Prob/Logic/Rules.lean#L40) |
| `RelOL.Prob.prhl_iff_quad` | The concrete command judgment is exactly its coupling-assertion pRelOL fragment. It does not formalize a separate proof-system derivation datatype or external procedure language. | [Subsumption/PRHL/Embedding](../../RelationalOutcomeLogic/Subsumption/PRHL/Embedding.lean#L41) |
| `RelOL.Prob.prhl_assign` | Relate the two deterministic updated states. | [Subsumption/PRHL/Embedding](../../RelationalOutcomeLogic/Subsumption/PRHL/Embedding.lean#L55) |
| `RelOL.Prob.prhl_sample` | Supply normalized kernels and an exact output coupling for each permitted state pair. | [Subsumption/PRHL/Embedding](../../RelationalOutcomeLogic/Subsumption/PRHL/Embedding.lean#L61) |
| `RelOL.Prob.prhl_ite` | Guard agreement under the relation, then one judgment per synchronized branch. | [Subsumption/PRHL/Embedding](../../RelationalOutcomeLogic/Subsumption/PRHL/Embedding.lean#L74) |
| `RelOL.Prob.prhl_while_left` | Body-versus-skip preserves the invariant; additionally the **whole loop** is lossless at every left state having a related partner. Conclude the invariant and the left exit condition. | [Subsumption/PRHL/OneSided](../../RelationalOutcomeLogic/Subsumption/PRHL/OneSided.lean#L69) |

The same files provide sequence, consequence, symmetry, right-sided rules, and
one-sided assignment/sampling/conditionals. Body losslessness alone cannot justify
the one-sided while rule: `while true do skip` is a counterexample.

## 5. Quantitative refutation, observations, and splitting

For finite events `A` and `B`, every exact `R`-coupling obeys
`μ(A) ≤ ν(B)` when **all** `R`-partners of `A` lie in `B`.
The current cover condition is `∀ a ∈ A, ∀ b, R a b → b ∈ B`; it is not restricted
to states in the support of `ν`. Only the events must be finite. No global
finite-support or normalization requirement is imposed on the weights.

The generic deficit argument uses the semiring's chosen order. For tropical
costs, that order reverses numerical cost. Rich observation transport and
mass-labelled restriction/splitting below currently use the concrete probability API.

| Declaration | Reading target / assumptions | Source |
| --- | --- | --- |
| `RelOL.Algebra.Weighted.IsCoupling.eventMass_le` | Exact marginals plus the global cover condition imply the finite-event bound. | [Algebra/Weighted/Events](../../RelationalOutcomeLogic/Algebra/Weighted/Events.lean#L120) |
| `RelOL.Generic.MassDeficitCert.refutes` | A strict reverse inequality `ν(B) < μ(A)` refutes every exact coupling. | [Generic/Refutation](../../RelationalOutcomeLogic/Generic/Refutation.lean#L32) |
| `RelOL.Generic.MassDeficitCert.of_bounds` | **Constructor.** A certified lower bound on left mass and upper bound on right mass suffice when upper < lower. Two lower bounds do not suffice. | [Generic/Refutation](../../RelationalOutcomeLogic/Generic/Refutation.lean#L44) |
| `RelOL.Generic.BugCert.refutes_of_entails` | A deficit in actual outputs refutes a stronger original contract, given its implication to the coupling and a proof that the certificate input satisfies its precondition. | [Generic/Refutation](../../RelationalOutcomeLogic/Generic/Refutation.lean#L94) |
| `RelOL.Prob.quadSem.observe` | Transport an entire outcome contract along deterministic observation maps and a proved implication on its postcondition. | [Prob/Refutation/Observation](../../RelationalOutcomeLogic/Prob/Refutation/Observation.lean#L16) |
| `RelOL.Prob.BugCert.refutes_of_observation` | A certificate about actual observed outputs refutes the original internal contract when that contract implies the observed coupling. | [Prob/Refutation/Observation](../../RelationalOutcomeLogic/Prob/Refutation/Observation.lean#L24) |
| `RelOL.Prob.IsCoupling.restrict` | Predicates agreeing on every related state pair restrict a joint with exactly the restricted marginals, without renormalizing. | [Prob/Coupling/Restriction](../../RelationalOutcomeLogic/Prob/Coupling/Restriction.lean#L76) |
| `RelOL.Prob.Coupled.split_mass` | Split one joint along agreeing predicates into complementary pieces, recording each piece's actual mass. Empty pieces are permitted. | [Prob/Coupling/Restriction](../../RelationalOutcomeLogic/Prob/Coupling/Restriction.lean#L117) |

## 6. Set assertions, family loops, and reachable evidence

In the Set model, addition is union and is idempotent. The product atom requires
both sets to be nonempty and **every cross pair** to satisfy the relation. The weak
atom omits nonemptiness. Bitotal coupling instead requires each outcome to have a
related partner on the other side; it allows both sets to be empty. A single bad
cross pair therefore does not generally refute a coupling.

| Declaration | Reading target / assumptions | Source |
| --- | --- | --- |
| `RelOL.atom_iff_atomW` | Strong atom = both sets nonempty + weak product atom. | [Set/Assertions](../../RelationalOutcomeLogic/Set/Assertions.lean#L68) |
| `RelOL.couple_iff_witness` | Bitotal coupling is equivalent to a supported relation whose projections equal the two outcome sets. | [Set/Coupling](../../RelationalOutcomeLogic/Set/Coupling.lean#L28) |
| `RelOL.coupleNE_oplus_top_iff` | A nonempty coupling piece plus arbitrary remaining outcomes is equivalent to a reachable related pair. | [Set/Coupling](../../RelationalOutcomeLogic/Set/Coupling.lean#L164) |
| `RelOL.couple_oplus_top` | A coupling piece without nonemptiness plus top is always true, by choosing the empty piece. | [Set/Coupling](../../RelationalOutcomeLogic/Set/Coupling.lean#L179) |
| `RelOL.quad_choice_left` | One-sided choice duplicates the passive outcome set using union idempotence. Do not transfer this rule directly to probability addition. | [Set/Rules](../../RelationalOutcomeLogic/Set/Rules.lean#L164) |
| `RelOL.Converges` | **Definition.** Every family of pairs satisfying `ψ n` must have its two countable unions satisfy `ψ∞`. No monotonicity premise on the family is built in. | [Set/Rules](../../RelationalOutcomeLogic/Set/Rules.lean#L270) |
| `RelOL.quad_while_fam` | Active assertions `φ n` force both guards; exit assertions `ψ n` force both negated guards. Each body step maps `φ n` to `φ (n+1) ⊕ ψ (n+1)`; `Converges ψ ψ∞` yields the final judgment from `φ 0 ⊕ ψ 0`. No termination premise. | [Set/Rules](../../RelationalOutcomeLogic/Set/Rules.lean#L318) |
| `RelOL.BugCert.refutes` | Reachable bad-pair evidence refutes the contract only with its precondition and an incompatibility proof valid for every pair of outcome sets containing that pair. | [Set/Refutation](../../RelationalOutcomeLogic/Set/Refutation.lean#L22) |
| `RelOL.OrphanCert.refutes` | A reachable left outcome with no related partner among **all actual right outputs** refutes a left-total coupling contract. A truncated right execution is insufficient. | [Set/Refutation](../../RelationalOutcomeLogic/Set/Refutation.lean#L39) |

## 7. Bridges between the interfaces

These theorems justify reuse rather than merely giving similarly named APIs.
The Boolean scalar is reachability with OR/AND, not the XOR Boolean ring.

| Declaration | Reading target / assumptions | Source |
| --- | --- | --- |
| `RelOL.Generic.BooleanBridge.encode_loopSem` | Encoding outcome sets as reachability weights commutes with full loop semantics. | [Bridges/Boolean](../../RelationalOutcomeLogic/Bridges/Boolean.lean#L81) |
| `RelOL.Generic.BooleanBridge.coupled_iff` | Set bitotal coupling and exact reachability-weight coupling coincide. | [Bridges/Boolean](../../RelationalOutcomeLogic/Bridges/Boolean.lean#L111) |
| `RelOL.Generic.ennreal_prhl_commands_iff` | Generic ENNReal statewise coupling and concrete probabilistic pRHL coincide on commands. | [Bridges/Probability](../../RelationalOutcomeLogic/Bridges/Probability.lean#L101) |
| `RelOL.Generic.weight_loopSem_eq` | Shared iteration and the original concrete probability loop semantics agree. | [Bridges/Probability](../../RelationalOutcomeLogic/Bridges/Probability.lean#L113) |

## 8. Two end-to-end results to reconstruct after studying the rules

| Declaration | Reading target / assumptions | Source |
| --- | --- | --- |
| `RelOL.Prob.Search.search_outcome_quad` | Full scan versus early exit, for every budget and normalized hit/miss trial: an additive failure/success contract records exact masses, answer agreement, and trial-count bounds. | [Examples/Probability/Search/OutcomeContract](../../RelationalOutcomeLogic/Examples/Probability/Search/OutcomeContract.lean#L88) |
| `RelOL.Prob.Search.cached_outcome_spec_refuted` | For `0 < miss < 1` and budget at least two, cached randomness refutes that same outcome contract through an observed event-mass deficit. | [Examples/Probability/Search/Case](../../RelationalOutcomeLogic/Examples/Probability/Search/Case.lean#L20) |

The search results count consumed trials; they are not an operational adequacy or
expected-runtime theorem. Certificate discovery, coupling synthesis, a general
weighted `While-Fam`, and an external LeanCrypt integration are not provided by
these results.

## Checking a name while studying

Use a scratch file outside the production import tree:

```lean
import RelationalOutcomeLogic

#check RelOL.Generic.quad_seq
#check RelOL.Prob.prhl_while_left
#print RelOL.Generic.prhl_iff_quad
```

Run `lake env lean /path/to/your/scratch.lean` from the repository root. Use
`#check` for the elaborated type and `#print` when ready to compare your own proof
with the implementation.
