# Speculative decoding in pRelOL

This case proves exact output preservation for an actual pre-sampled draft buffer,
accounts for speculative work, certifies two probability-changing bugs, and
separates output privacy from streaming-observation privacy. Its programs are
denotational kernels built using `Weight.bind`, with finite output budgets.

Import `RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Case`.
Declarations live in `RelOL.Prob.Speculative`; the documented bonus-token
regression has the further namespace `Implementation`.

## Source organization and reading order

All case-specific code is under
[`Examples/Probability/SpeculativeDecoding/`](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/).

| File | What to read |
| --- | --- |
| [Programs.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/Programs.lean) | History-dependent target/draft models, eager draft buffer, verifier, adaptive decoder, and round traces. |
| [Correction.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/Correction.lean) | Actual proposal, clipped-ratio acceptance, normalized residual correction, and exact accepted/rejected subweights. |
| [StepContract.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/StepContract.lean) | Derive the accepted/corrected quantitative contract using sequencing, additive choice, and consequence. |
| [Refinement.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/Refinement.lean) | One-step buffer reconstruction square, then distributional invariant, sequencing, and bounded recursion. |
| [DecoderRules.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/DecoderRules.lean) | Verifier and full decoder derivations using indexed continuation contracts. |
| [Buffered.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/Buffered.lean) | Public output equality, normalization, and exact output length. |
| [Fuel.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/Fuel.lean) | Independence of sufficient fuel for the full token-and-trace distribution. |
| [OutcomeContracts.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/OutcomeContracts.lean) | Complete decoder judgment combining output agreement with trace accounting. |
| [RoundLaw.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/RoundLaw.lean) | Accepted-prefix survival, exact first-rejection masses, and finite additive outcome contracts. |
| [RoundExpectation.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/RoundExpectation.lean) | General expected accepted/emitted tokens, geometric formula, and rate-one boundary. |
| [RoundClipping.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/RoundClipping.lean) | Joint accepted/emitted count law with arbitrary remaining budget, including zero. |
| [Costs.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/Costs.lean) | Actual-trace work bounds, exact two-token expectation, and perfect-draft batching benefit. |
| [Counterexamples.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/Counterexamples.lean) | Wrong rejection fallback, normalization, equal token support, and quantitative refutation. |
| [Security.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/Security.lean) | General buffered-release mitigation and acceptance-gap leakage certificates; concrete secret-draft witness. |
| [Implementation.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/Implementation.lean) | Mathematical regression for the documented bonus-from-draft failure. |
| [Case.lean](../RelationalOutcomeLogic/Examples/Probability/SpeculativeDecoding/Case.lean) | Entry point, adaptive-policy client, and refutation of the same quantitative outcome contract. |

## What is proved

**Local correction.** For normalized discrete target `p` and draft `q`, the program
samples a proposal from `q`, accepts it with the clipped target/draft ratio, and
otherwise samples the normalized positive residual. Its accepted token subweight
is `min(p,q)` and its corrected subweight is `p - min(p,q)`. Their sum is exactly
`p`. The definition handles zero proposal probability and zero rejection mass;
there is no full-support assumption or finite-alphabet requirement.

`step_outcome_quad` derives an additive pRelOL contract: sampling and tagging use
sequencing, the accepted/corrected branches use additive choice, and consequence
specializes the arbitrary-input-mass judgment. Each piece retains token agreement,
its verification flag, and its exact probability mass.
`stepSpec_mass_one` derives normalization from that contract.

**Buffered execution.** `draftBlock` samples the entire autoregressive draft block
before verification. Rejection emits a corrected token and discards the suffix;
complete acceptance emits a target bonus if the output budget permits it.
`buffered_eq_delayed` proves equality with delayed proposal sampling, including
the complete trace. The primitive semantic obligation concerns **one verifier
transition**: exchange independent suffix/verifier randomness, discard normalized
unused samples, and advance the conditional history only on acceptance.
`Generic.quad_lifted` turns this local square into a distributional invariant over
arbitrary input weights. Sequencing and dispatch compose the step with a pending
continuation; `Generic.quad_recursion` proves the entire verifier. A fixed buffer
need not itself be target-distributed.

`delayed_quad_family` and `decoder_quad_family` use the reusable
`Generic.quad_recursion_family` rule. Its layer premise quantifies over arbitrary
continuations satisfying the smaller-budget contracts; it never assumes a theorem
about the completed decoder. The local quantitative step contract supplies the
sampler's token-observation contract, and sequencing connects it to continuations.
The outer families use indexed exact-state preconditions; the buffer invariant
is the part proved for arbitrary mixtures. All these declarations are in
`RelOL.Prob.Speculative` (the file name adds no namespace).

`run_output` consequently proves that the complete adaptive decoder has precisely the ordinary
autoregressive target law for every finite budget and history. A width policy can
depend on the already emitted history and remaining budget. `fixedWidth` clips
proposals to that budget. Zero width samples a target token each round; zero
budget emits nothing new. General widths may exceed the budget, and all sampled
proposals are still charged. `decoder_outcome_quad` packages output coupling,
normalization, exact output length, and trace accounting into one judgment.

The raw auxiliary `decode` takes a round-fuel argument. Each nonempty round emits
at least one token, so generating `N` tokens needs at most `N` rounds.
`decode_fuel_irrelevant` proves equality of the **entire output weight, including
traces**, for any two fuels at least `N`; `decode_eq_run` identifies every such
execution with the public `run`. Thus sufficient fuel is a proof device for the
public semantics. Insufficient fuel in the auxiliary kernel returns a partial
history. These are bounded recursive kernels; the derivation does not instantiate
the ranked asynchronous `Cmd.while` rule.

**General round law.** Let `S_i` be the mass of the subdistribution of histories
after `i` consecutive accepted proposals, starting with `S_0 = 1`. The next
accepted prefix extends this subdistribution with `min(p,q)` at each history.
No independent-token or constant-rate assumption is needed. For width `K`, with
room for the full round, the actual eager sampler has

\[
\Pr[A=i]=S_i-S_{i+1}\ (i<K),\qquad \Pr[A=K]=S_K,
\]

where `A` counts accepted proposals. A correction or target bonus supplies one
additional emitted token, so `L = A+1` and

\[
\mathbb E[A]=\sum_{i=1}^{K}S_i,\qquad
\mathbb E[L]=\sum_{i=0}^{K}S_i.
\]

`round_count_contract` retains these exact masses in a finite additive assertion.
`round_emitted_contract` maps all cases using `quadSem_finiteCases`, retaining the
decomposition instead of just calculating its mean.

If the overlap mass equals `a` at **every reachable accepted history** before the
end of the block, then `S_i = a^i`. Under this explicit conditional assumption,
`expected_emitted_geometric` proves `(1-a^(K+1))/(1-a)` for `a < 1`, and
`expected_emitted_rate_one` proves `K+1` for `a = 1`. This is expected **emitted**
tokens, including correction/bonus, rather than accepted proposals alone. An
unconditional empirical average acceptance rate is insufficient for the theorem.

The actual clipped sampler `roundWithBudget` also has a checked joint law:
take `i` from the acceptance-count distribution at width `min(K,N)` and return
`(i, min(i+1,N))`. Consequently

\[
\mathbb E[A]=\sum_{i=1}^{\min(K,N)}S_i,\qquad
\mathbb E[L]=\sum_{i=0}^{\min(K+1,N)-1}S_i.
\]

An empty sum is zero. This covers zero budget and budget exhaustion without a
bonus. Positive-budget rounds still sample all `K` draft proposals even when
fewer fit. The formulas describe one round conditional on its starting history;
they do not assume that successive adaptive rounds are identically distributed.

**Work.** Every supported complete run emits exactly `N` new tokens, uses at most
`N` target-verification rounds, and charges every draft proposal, even discarded
ones. If every width is at most `K`, draft work is at most `K × N`. The bounds also
hold in expectation. Correction and bonus are exclusive within a round.
For arbitrary imperfect drafts, `expected_two_token_calls` gives the exact
width-one, two-token expectation `1 + rejectionMass (p h) (q h)`.
`perfect_single_round` proves that a perfect width-`K` draft emits `K+1` exact
target tokens in one round, with exactly `K` draft proposals; its expected round
count is one. These counters model batched verification, not the number of kernel
function applications or elapsed time. A perfect draft is a mathematical witness;
the theorem does not assume or establish a cheap physical implementation of it.

**Security and faults.** The general mitigation is `bufferedRelease_law`: releasing
the completed result in one packet has exactly the reference payload law with its
length attached. `bufferedRelease_private` makes the whole released-packet law
independent of the draft and width policy, for every finite public budget. The
payload includes the public prompt, so its length is `prompt.length + N`.

For streaming, `two_token_firstRoundSize_mass` identifies the probability that
the first round emits two tokens with the actual initial `acceptanceMass`, for
arbitrary target and draft models. `acceptanceGapPacketLeak` turns any strict gap
between two drafts into a finite-event certificate. `run_payload_private` proves
that their complete payload laws nevertheless agree; `acceptance_gap_contract_refuted`
refutes the corresponding packet privacy contract. The Boolean witness below is
an instance of this general result.

Each gap comes from the defined sampler, not an assumed probability table:

| Case | Correct/reference event mass | Faulty/other event mass | Checked consequence |
| --- | --- | --- | --- |
| Fair target, always-true draft; sample the whole target on rejection | False token: `1/2` | False token: `1/4` | Same token support and normalization, but `wrongFallback_outcome_contract_refuted` rejects the exact split contract proved for correction. |
| Bonus sampled from draft after an accepted first token | Second token false: `1/2` | Second token false: `1/4` | Same complete two-token support and normalization, but `Implementation.bonus_output_contract_refuted` rejects output equality. |
| Secret chooses perfect versus always-true draft; fixed fair target | First round emits two tokens: `1` | First round emits two tokens: `1/2` | Whole two-token payload laws agree, but `fullRun_packet_contract_refuted` rejects packet-observation privacy. |

The security example observes the number of tokens released after a verification
round. `two_token_firstRoundSize` connects this observation to the actual eager
decoder, including the second round after rejection. The secret influences the
proposal model while the target and prompt remain fixed.

This models token counts, with no timestamps, byte
encoding, transport behavior, or variable stopping rule. It does not establish
timing noninterference or verify the empirical mitigations in the cited paper.

## Library changes, kept separate

Existing judgment definitions and rules remain valid. New derived rules expose
the proof structure needed by this case, in separate reusable modules:

| Module | Addition | Why this case needs it |
| --- | --- | --- |
| [Generic/Distributional.lean](../RelationalOutcomeLogic/Generic/Distributional.lean) | `lifted`, `quad_lifted`, `quad_lifted_dispatch` | Reconstruct hidden random buffers; compose local transitions with continuations. |
| [Generic/Loops/Bounded.lean](../RelationalOutcomeLogic/Generic/Loops/Bounded.lean) | Bounded steps and recursion, including `quad_recursion_family` | Derive complete programs from indexed local continuation contracts. |
| [Prob/Logic/FiniteOutcomes.lean](../RelationalOutcomeLogic/Prob/Logic/FiniteOutcomes.lean) | `finiteCases`, `quadSem_finiteCases` | Preserve every first-rejection case and its mass under composition and clipping. |
| [Algebra/ENNReal/Sequencing.lean](../RelationalOutcomeLogic/Algebra/ENNReal/Sequencing.lean) | `Weight.bind_comm`, `Weight.bind_const_of_isProbability` | Exchange independent suffix/verifier draws and discard a normalized unused suffix. |
| [Algebra/ENNReal/Expectation.lean](../RelationalOutcomeLogic/Algebra/ENNReal/Expectation.lean) | Nonnegative expectation, sequencing/addition laws, support-based bounds | Lift actual trace cost bounds to expectations. |

The first two modules are generic over `OutcomeModel`; finite outcome assertions
and expectation laws here use the concrete probability interface. Independent
draw commutation is proved for ENNReal, not asserted for noncommutative scalars.
Case-specific samplers, invariants, costs, and observers stay under `Examples/`.
The existing aggregate modules expose all additions.

## Which parts use the logic?

| Part | Proof method |
| --- | --- |
| Clipped-ratio acceptance and residual correction | Semantic probability algebra for the primitive sampler. |
| Accepted/corrected step contract | Sampling/tagging sequencing, additive choice, and consequence. |
| One buffer transition | Semantic local reconstruction square: commutation, normalization, and accepted-token identity. |
| Whole buffer and decoder correctness | Distributional invariant, sequencing/dispatch, and bounded continuation recursion; no complete-program equality premise. |
| Prefix survival and expected values | Semantic recurrence and finite-sum mathematics, connected to the actual eager sampler. |
| Transport of first-rejection contracts | Finite additive composition rule, including merged observations after clipping. |
| Full accounting contract and privacy observations | Rule-derived output equality combined with separate semantic accounting/observation lemmas. |
| Certified failures | Existing finite-event certificate soundness and contract-refutation rules. |

The full decoder derivation consumes the local split contract after forgetting
its flag and mass annotations. It does **not** carry all quantitative annotations
through the outer recursion: accounting and round expectations are separate
theorems. The final combined contract packages these established properties.
The reusable simulation and induction rules are derived proof infrastructure;
their existence alone is not a novelty claim.

## Provenance and scope

The accept/correct algorithm and its target-distribution identity are established
speculative-decoding mathematics, described by
[Leviathan, Kalman, and Matias, ICML 2023](https://proceedings.mlr.press/v202/leviathan23a.html).
The mechanization's purpose is to connect buffered execution, outcome contracts,
resource observations, and certified failures in the same development; the local
identity itself is not a novelty claim.

The packet observer is motivated by
[When Speculation Spills Secrets, arXiv v4](https://arxiv.org/html/2411.01076v4),
especially its private-datastore proposal mechanism (§5): a secret changes the
proposal distribution, acceptance changes the per-round token count, and payload
preservation alone does not hide that observation. We reduce that mechanism to
two history-dependent draft kernels with a common public target. The reduction
assumes the relevant private state is represented by those kernels; it does not
extract a datastore implementation or reproduce classifiers or deployments.
The buffered-release theorem verifies our explicit token-count abstraction of
aggregation, not every empirical mitigation in that paper.

The bonus-source failure is reported for DSD in Appendix A, Table 3 of
[Batch Speculative Decoding Done Right, arXiv v3](https://arxiv.org/html/2510.22876v3).
`Implementation.program` changes only the accepted-path bonus source. Its two-token
probabilistic example is an abstraction of that documented failure class, not an
extraction or verification of DSD's code. The source paper also discusses greedy
verification and separate cache/batching failures; those are not silently covered
by this sampler proof. No claim about the current state of that repository follows.

The verified model excludes floating-point approximation, concrete neural networks,
KV caches, multi-request scheduling, continuous distributions, and unbounded or
secret-dependent stopping times. It proves exact discrete semantic statements.
This case demonstrates pRelOL's combined specification/refutation workflow without
claiming that another logic could not establish the same mathematical facts.

## Checking and a small client

```lean
import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Case

open RelOL RelOL.Prob RelOL.Prob.Speculative

example {α : Type*} (p q : Model α) (width : List α → ℕ → ℕ)
    (n : ℕ) (h : List α) :
    pushforward Run.tokens (run p q width n h) = autoregressive p n h :=
  run_output p q width n h

example : ¬ Coupled Eq (pushforward firstRoundSize (secretRun false))
    (pushforward firstRoundSize (secretRun true)) :=
  secretRun_packet_not_private
```

Run `lake build RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Case`
for this case, or `./scripts/check.sh` for source structure, the full build,
placeholder rejection, and the repository-wide axiom audit.
