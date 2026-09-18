# RelOL infrastructure audit — 2026-09-18

Preliminary de-risking of the proposed outcome abstraction, pRHL embedding, probabilistic loops,
and quantitative refutation. Production Lean modules and dependency configuration were not changed.

## Scope and versions

| Source | Audited revision | Declared Lean/Mathlib |
| --- | --- | --- |
| Installed Mathlib | `520045ab14e26149ee970e2e617ca04b09bde5d6` | v4.32.1 |
| [domain-theory](https://github.com/zilberstein/domain-theory/tree/5c667c350be8b83ab49e3f9d26d7db8fb90b5f50) | `5c667c350be8b83ab49e3f9d26d7db8fb90b5f50` | v4.32.2 |
| [convex-powerset](https://github.com/zilberstein/convex-powerset/tree/1ca469942cab628084b9fcd7bcb0958679d184cd) | `1ca469942cab628084b9fcd7bcb0958679d184cd` | v4.32.2 |

Both external repositories are Apache-2.0. All substantive domain-theory modules compiled unchanged
against the installed v4.32.1 dependencies. All 13 convex-powerset source modules also compiled against
v4.32.1 in a temporary flattened source probe, with imports reorganized and no proof-body changes.
This checks source compatibility; it is not a normal Lake installation/build of their declared packages.
Their root modules do not import every supplementary file: explicit imports are needed for, e.g.,
domain-theory's Markowsky module and convex-powerset's MinProb and Monad/Laws modules.

Source scans found no `sorry`, `admit`, declared `axiom`, or `unsafe` in either external library;
convex-powerset also had no `native_decide` matches. Selected central theorems were checked with
`#print axioms` and used only `propext`, `Classical.choice`, and `Quot.sound`.
This is a sampled transitive axiom check, not a full library axiom census.

## What is already available

### Mathlib: raw weights, probabilities, marginals

The raw carrier `Weight α := α → ℝ≥0∞` already inherits pointwise addition, scalar operations,
and a complete lattice. Discrete semantics can use nonnegative sums directly, without adopting
measurable-space/kernel infrastructure.

| Need | Exact API | Source |
| --- | --- | --- |
| Infinite sums and Fubini | `ENNReal.tsum_eq_iSup_sum`, `tsum_prod`, `tsum_comm`, `tsum_add`, `tsum_le_tsum`, `tsum_eq_zero` | [InfiniteSum/ENNReal](https://github.com/leanprover-community/mathlib4/blob/520045ab14e26149ee970e2e617ca04b09bde5d6/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L58) |
| Multiplication through sums | `ENNReal.tsum_mul_left`, `tsum_mul_right` | [same file](https://github.com/leanprover-community/mathlib4/blob/520045ab14e26149ee970e2e617ca04b09bde5d6/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L179) |
| Increasing-limit continuity | `ENNReal.finsetSum_iSup_of_monotone`, `ENNReal.mul_iSup`, `ENNReal.iSup_mul` | [BigOperators](https://github.com/leanprover-community/mathlib4/blob/520045ab14e26149ee970e2e617ca04b09bde5d6/Mathlib/Data/ENNReal/BigOperators.lean#L181), [Inv](https://github.com/leanprover-community/mathlib4/blob/520045ab14e26149ee970e2e617ca04b09bde5d6/Mathlib/Data/ENNReal/Inv.lean#L807) |
| Full discrete probabilities | `PMF`, `PMF.tsum_coe`, countable support | [PMF/Basic](https://github.com/leanprover-community/mathlib4/blob/520045ab14e26149ee970e2e617ca04b09bde5d6/Mathlib/Probability/ProbabilityMassFunction/Basic.lean#L46) |
| Probability monad | `PMF.pure`, `bind`, `bind_apply`, `support_bind`, `pure_bind`, `bind_pure`, `bind_bind`, `bind_comm` | [PMF/Monad](https://github.com/leanprover-community/mathlib4/blob/520045ab14e26149ee970e2e617ca04b09bde5d6/Mathlib/Probability/ProbabilityMassFunction/Monad.lean#L105) |
| Support-dependent continuations | `PMF.bindOnSupport`, `bindOnSupport_bindOnSupport` | [PMF/Monad](https://github.com/leanprover-community/mathlib4/blob/520045ab14e26149ee970e2e617ca04b09bde5d6/Mathlib/Probability/ProbabilityMassFunction/Monad.lean#L191) |
| Marginals through sequencing | `PMF.map`, `map_bind`, `bind_map`; marginal = map along a projection | [PMF/Constructions](https://github.com/leanprover-community/mathlib4/blob/520045ab14e26149ee970e2e617ca04b09bde5d6/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean#L45) |
| Finite samplers | `PMF.ofFinset`, `ofFintype`, `normalize`, `bernoulli` | [PMF/Constructions](https://github.com/leanprover-community/mathlib4/blob/520045ab14e26149ee970e2e617ca04b09bde5d6/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean#L164) |

The monotone-convergence ingredients are sufficient for a three-line proof that an ENNReal sum
commutes with the supremum of an increasing sequence. Raw weighted bind associativity and
continuity in each argument also have short proofs; these were actually compiled (see probes below).

Further infrastructure exists for a later measure-theoretic extension:

- `Measure.fst` / `snd`, their add/sum laws: `Mathlib/MeasureTheory/Measure/Prod.lean`.
- `Measure.bind`, `bind_bind`: `Mathlib/MeasureTheory/Measure/GiryMonad.lean`, with measurability conditions.
- `Measure.condKernel`, `Measure.disintegrate`: `Mathlib/Probability/Kernel/Disintegration/`, with finite-measure and standard-Borel/nonempty-space hypotheses.
- `Kernel.traj`, finite-prefix consistency: `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`.

Those provide substantial ingredients, but importing path distributions or disintegration does not
establish asynchronous scheduler correctness. The discrete Weight route avoids these extra hypotheses.

### Mathlib and domain-theory: loops

Already-installed Mathlib supplies `OmegaCompletePartialOrder`, bundled `ContinuousHom`,
`ωScottContinuous`, function-space instances, and the generic Kleene construction:

- `OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_mem_fixedPoint` and
  `ωSup_iterate_le_prefixedPoint`: [OmegaCompletePartialOrder.lean](https://github.com/leanprover-community/mathlib4/blob/520045ab14e26149ee970e2e617ca04b09bde5d6/Mathlib/Order/OmegaCompletePartialOrder.lean#L746).
- `OrderHom.lfp`, `OrderHom.map_lfp`, and `fixedPoints.lfp_eq_sSup_iterate`:
  [FixedPoints.lean](https://github.com/leanprover-community/mathlib4/blob/520045ab14e26149ee970e2e617ca04b09bde5d6/Mathlib/Order/FixedPoints.lean#L272).

domain-theory adds a convenient nonempty-directed-set interface (`DSet`), a nonpointed `DCPO`,
pointwise DCPO function spaces, compact/way-below definitions, and Markowsky's theorem converting
nonempty arbitrary-chain completeness into directed completeness. Its `Chain.lfp_is_lfp`
wraps Mathlib's existing omega-iteration results. See
[DCPO.lean](https://github.com/zilberstein/domain-theory/blob/5c667c350be8b83ab49e3f9d26d7db8fb90b5f50/DomainTheory/DCPO.lean#L15)
and [Markowsky.lean](https://github.com/zilberstein/domain-theory/blob/5c667c350be8b83ab49e3f9d26d7db8fb90b5f50/DomainTheory/Markowsky.lean#L277).

For `Set` and raw `Weight`, the existing complete lattices make this additional dependency optional.
The repo does not contain distribution, coupling, or semiring-specific probability machinery.

### convex-powerset: the directly reusable lower layer

`Distr α := PMF (WithBot α)` represents subprobabilities by recording missing mass at divergence.
The library supplies:

- `Distr.prob_bot`, `prob_not_bot`, bridges to full PMFs:
  [Distr/Basic.lean](https://github.com/zilberstein/convex-powerset/blob/1ca469942cab628084b9fcd7bcb0958679d184cd/ConvexPowerset/Distr/Basic.lean#L14).
- Divergence-propagating `Bind` and `LawfulMonad`:
  [Distr/Monad.lean](https://github.com/zilberstein/convex-powerset/blob/1ca469942cab628084b9fcd7bcb0958679d184cd/ConvexPowerset/Distr/Monad.lean#L9).
- Pointwise order on terminating coordinates, bottom, omega-CPO instance, and
  `Distr.tsum_iSup_eq_iSup_tsum`:
  [Distr/Powerdomain.lean](https://github.com/zilberstein/convex-powerset/blob/1ca469942cab628084b9fcd7bcb0958679d184cd/ConvexPowerset/Distr/Powerdomain.lean#L50).
- `Distr.bind_monotone` and joint-chain `Distr.bind_continuous`:
  [Distr/Monad/Order.lean](https://github.com/zilberstein/convex-powerset/blob/1ca469942cab628084b9fcd7bcb0958679d184cd/ConvexPowerset/Distr/Monad/Order.lean#L48).

This changes basic probability-monad/order/loop infrastructure from a substantial construction
task into a reuse or adaptation task.

The full convex powerdomain additionally has a lawful monad, continuous bind, probability and
nondeterministic choice, loop semantics, and a `minProb` API (attained worst-case probabilities,
bind equation, nondeterministic minimum, continuity). See
[Semantics.lean](https://github.com/zilberstein/convex-powerset/blob/1ca469942cab628084b9fcd7bcb0958679d184cd/ConvexPowerset/Semantics.lean#L43)
and [MinProb.lean](https://github.com/zilberstein/convex-powerset/blob/1ca469942cab628084b9fcd7bcb0958679d184cd/ConvexPowerset/MinProb.lean#L41).
This is optional support for combined demonic nondeterminism and probability, beyond the initial pRHL milestone.

## Interfaces and gaps that still matter

1. **Normalized distributions are not raw additive weights.** `Distr` has total mass one including
   divergence. Adding two distributions pointwise doubles that mass. Keep raw `Weight` plus a
   mass-at-most-one predicate for the planned total `oadd`, or deliberately choose a different
   partial-addition/convex interface. An explicit bridge can reuse `Distr` without changing RelOL's semantics.
2. **Increasing limits, not arbitrary suprema.** The proposed bind-continuity fields must include
   chain/directedness hypotheses. The supremum of two incomparable Dirac weights has mass two;
   their individual masses both equal one. The probe proves this counterexample. Subprobabilities
   are consequently not closed under pointwise binary suprema, although raw weights are a complete lattice.
3. **Convex-powerdomain membership is not exact reachability.** The Smyth carrier consists of
   nonempty closed convex upper sets, ordered by reverse inclusion. Bottom contains all distributions;
   embeddings take upper closures. A member is therefore not automatically a reachable execution.
   RelOL's existing bug-certificate membership interpretation needs an adequacy argument before reuse.
   See [Basic.lean](https://github.com/zilberstein/convex-powerset/blob/1ca469942cab628084b9fcd7bcb0958679d184cd/ConvexPowerset/Basic.lean#L30)
   and [Operations.lean](https://github.com/zilberstein/convex-powerset/blob/1ca469942cab628084b9fcd7bcb0958679d184cd/ConvexPowerset/Operations.lean#L103).
4. **Relational layers remain to be built.** Neither external repo supplies pRHL subsumption,
   relation-supported joint distributions with prescribed marginals, or an asynchronous relational
   loop rule. PMF map/bind laws make local marginal composition accessible, but the product-loop
   construction and asynchronous marginal-preservation arguments remain project work.
5. **No ready Strassen API was found.** Searches covered the pinned Mathlib and both external
   repositories for coupling, Strassen, weighted Hall/transport, and related terms. Mathlib has
   ordinary Hall matching and geometric Farkas/separation results; neither is a drop-in theorem
   for the desired real-weight coupling criterion. This is a search result, not proof that no
   equivalent theorem exists under other names.
6. **Sound quantitative refutation does not require Strassen.** We compiled a finite event-mass
   obstruction theorem: if `R(A) ⊆ B` and `μ(A) > ν(B)`, no exact `R`-supported coupling exists.
   This uses finite sums and marginals only. Strassen or an equivalent converse is needed to
   prove that such certificates capture every coupling failure.
7. **General semiring parametricity remains separate.** These probabilistic results use ENNReal.
   They validate that concrete instance, not every semiring, generic coupling decomposition,
   or a full Scott-continuous partial-semiring outcome-model factory.

## Reproducible local probes

Saved independently of production imports in `notes/probes/infrastructure-audit/`:

| Probe | Verified statements |
| --- | --- |
| `Probability.lean` | 9 theorems: weighted bind associativity/support, monotone sum-limit interchange, bind continuity in each argument, subprobability preservation under bind/limits, PMF map-through-bind, exact left marginal sequencing |
| `MassCertificate.lean` | 2 theorems: supported finite coupling event bound, mass-deficit refutation |
| `Order.lean` | 3 theorems: raw-weight Kleene theorem, failure of arbitrary-sup mass preservation, failure of pointwise-sup closure for subprobabilities; also complete-lattice/omega-CPO instance checks |

All use `autoImplicit=false` and `relaxedAutoImplicit=false`. All 14 named theorem axiom checks
report only `propext`, `Classical.choice`, and `Quot.sound`. These are targeted infrastructure
smoke tests, not an implementation of the roadmap or a proof of relational loop soundness.

Run from the repository root:

```sh
lake env lean notes/probes/infrastructure-audit/Probability.lean
lake env lean notes/probes/infrastructure-audit/MassCertificate.lean
lake env lean notes/probes/infrastructure-audit/Order.lean
```

External clones and compatibility probes used during this audit are under
`/private/tmp/relol-infra-audit.lWUzQs/`; these temporary paths may disappear.
The pinned links above identify the external sources independently of those temporary files.

## Recommended next de-risking milestone

Keep existing dependencies for now. Specify exact probabilistic coupling over raw ENNReal weights;
prove both marginal laws for coupling bind; prove the synchronous loop rule by a coherent product-loop
witness; instantiate the pRHL bridge; and add one finite mass-deficit bug certificate.

The probability arithmetic and domain-theory foundation is now low risk. The main unresolved risks
are coherent relational loop witnesses, probabilistic asynchrony, semantic alignment of outcome
assertions with the chosen carrier, and any full completeness/general-semiring claim.
