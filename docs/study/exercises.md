# pRelOL manual proof workbook

Attempt each question on paper before reading its proof in Lean. This workbook
contains statements and proof directions, not completed solutions. The
[study schedule](README.md) assigns the ten core groups; E11–E13 are optional.

For each attempt, write: **statement → assumptions → witness/invariant → argument
→ failure without a premise**. A convincing explanation of a long loop proof is
enough for the core pass. Aim to reconstruct three or four short proofs in Lean,
not every exercise.

## Notation

`δa` denotes the pure outcome at `a`. For sets, `+` below means union; for weights
it means pointwise scalar addition. `μ >>= k` is bind. `P ⊕ Q` means that each
side decomposes additively into a `P` piece and a `Q` piece; pieces need not be
disjoint. The kernel judgment is

```text
⟨P⟩ k ∼ l ⟨Q⟩  iff  ∀ μ ν, P μ ν → Q (μ >>= k) (ν >>= l).
```

For ENNReal weights, `C_R(μ,ν)` means that a joint weight exists with exact
marginals `μ,ν` and support contained in relation `R`. `mass(μ)` sums all weights;
`μ(A)` sums over the finite event `A`. ENNReal arithmetic is intended unless a
different scalar model is specified.

## E1. Read the quantifiers before the notation

For Set outcomes `A,B` and a relation `R`, expand `atom R`, `atomW R`, `couple R`,
`coupleL R`, and `coupleNE R` into quantifiers.

1. Prove `couple R {a} {b} ↔ R a b`.
2. Find nonempty finite `A,B` for which `couple Eq A B` holds but `atom Eq A B`
   fails. Explain what the missing quantifier change is.
3. Classify all five assertions on `(∅,∅)` and on `({a},∅)`.
4. Prove that `couple R A B` implies `A.Nonempty ↔ B.Nonempty`.
5. Explain why `couple R ⊕ top` always holds, while `coupleNE R ⊕ top` need not.

**Deliverable:** a quantifier table and one explicit counterexample. Do not assume
that one unrelated reachable pair refutes an existential coupling.

## E2. Reconstruct the two main structural proofs

Work first with sets, then with an arbitrary `OutcomeModel`.

**Sequencing.** Given

```text
⟨P⟩ k ∼ l ⟨Q⟩          ⟨Q⟩ k' ∼ l' ⟨S⟩,
```

prove

```text
⟨P⟩ (a ↦ k a >>= k') ∼ (b ↦ l b >>= l') ⟨S⟩.
```

**Splitting.** Given `⟨P⟩ k ∼ l ⟨Q⟩` and `⟨P'⟩ k ∼ l ⟨Q'⟩`, prove
`⟨P ⊕ P'⟩ k ∼ l ⟨Q ⊕ Q'⟩`.

Unpack all four witnesses in the input split. State where bind associativity and
additivity are used. Check whether either argument uses additive idempotence,
probability normalization, or a state-level relation.

**Deliverable:** two proofs of at most one page each, followed by your own Lean
proof of one theorem under a fresh name.

## E3. A coupling is a joint, not just a relation on supports

Let `J : α × β → ℝ≥0∞` have marginals `μ,ν`, with `J(a,b) ≠ 0 → R(a,b)`.

1. Prove `mass μ = mass ν` by summing the marginal equations. Identify the sum
   exchange fact needed for infinite discrete carriers.
2. Given `R(a,b)`, construct a joint proving `C_R(δa,δb)`.
3. Construct an equality coupling for a fair Boolean coin with itself. Write all
   four entries of its `2 × 2` joint table.
4. Can the weight `2 · δa` couple exactly to `δb` under the relation `True`?
   Justify your answer using marginals, not intuition about supports.

**Deliverable:** the joint table and a short marginal argument. Explain why raw
ENNReal weights can be legal outcomes even when they are not probability distributions.

## E4. Prove both directions of the pRHL bridge

For kernels `k : α → Weight γ`, `l : β → Weight δ`, define

```text
prhl R k l S  iff  ∀ a b, R a b → C_S(k a, l b).
```

Prove

```text
prhl R k l S  ↔  ⟨C_R⟩ k ∼ l ⟨C_S⟩.
```

In the forward direction, identify the initial joint and the family of body
joints. In the reverse direction, identify which input weights to instantiate.
Then explain why the forward statement quantifies over coupled input weights of
arbitrary mass, even when each command started from a single state is subprobabilistic.

**Deliverable:** a two-direction proof and a paragraph explaining why this theorem
alone does not translate another project's procedures, modules, or proof scripts.

## E5. Refute a coupling, then refute the original specification

Let `μ(false)=1/2`, `μ(true)=1/2`, `ν(false)=1/4`, and `ν(true)=3/4`.
Both distributions have Boolean support and mass one.

1. Choose finite events `A,B` to refute `C_Eq(μ,ν)`. Prove every field of
   `MassDeficitCert`: the events, the cover condition
   `∀ a ∈ A, ∀ b, a = b → b ∈ B`, and `ν(B) < μ(A)`.
2. Suppose only `lower ≤ μ(A)` and `ν(B) ≤ upper` are known. Prove that
   `upper < lower` is sufficient. Construct a numerical counterexample to the
   argument obtained by replacing the right upper bound with a right lower bound.
3. Suppose `F(δs)=μ`, `G(δt)=ν`, `P(δs,δt)`, and
   `∀ x y, Q(x,y) → C_Eq(x,y)`. Derive `¬quadSem F G P Q`.
4. Repeat the last statement with deterministic observations on the outputs.
   State the implication from the **original** postcondition that must be proved.

**Deliverable:** one complete finite certificate and a diagram from a concrete
initial pair through program outputs and observations to failure of the original
postcondition. Do not replace that postcondition with a conveniently weaker test
without proving the implication.

## E6. Loop fuel, divergence, and losslessness

The finite approximation is

```text
L₀(s) = 0
Lₘ₊₁(s) = if g(s) then k(s) >>= Lₘ else δs
loopSem(g,k,s) = supₘ Lₘ(s).
```

1. For `g(n) := 0 < n` and `k(n) := δ(n-1)`, calculate the approximations at
   starts `0,1,2`. Prove `Lₙ(n)=0` and `Lₙ₊₁(n)=δ0` for every `n : ℕ`.
   Be careful: detecting an exit also uses a positive fuel index.
2. For `g := True`, prove every finite approximation is zero, regardless of `k`.
   Deduce the full semantics of `while True do skip`.
3. Refute an exact coupling between that loop and `skip`, even with postrelation
   `True`. Explain why a lossless body does not justify the one-sided loop rule.
4. Write the synchronous rule's invariant, guard-agreement premise, and body
   premise. Explain why equal termination masses do not require mass one.

**Deliverable:** the small approximation table and a proof outline. Mark the exact
point where the full-loop rule uses increasing-limit continuity.

## E7. Design a ranked schedule by hand

Use the existing slow/fast countdown example. A slow state is `(i,p)` with phase
`p : Bool`; the fast state is `j : ℕ`. Both guards test a positive counter.

```text
slowStep r (i,false) = r · δ(i,true)
slowStep r (i,true)  = δ(i-1,false)
fastStep r j        = r · δ(j-1)

R((i,p),j) := if p then i=j+1 else i=j.
```

1. Give a mode selector using `left`, `both`, and `done`, together with a natural
   rank. Check every guard obligation under `R`.
2. Construct the local joint in each active mode. Prove preservation of `R` and
   strict rank descent on **every supported** left-only successor.
3. Trace the schedule from `((2,false),2)` to termination. Record which transitions
   contribute scalar weight `r` and which contribute scalar identity `1`.
4. Explain why the terminal marginal equations must be proved from these local
   conditions. Identify the two directions of the projection proof and where
   induction on rank is needed.

**Deliverable:** a mode/rank table, local coupling witnesses, and the trace. The
core exercise does not require reimplementing the full projection theorem.

## E8. Own the search example end to end

Use `Trial.fair`, budget `2`, and start state `(2,false)`. The state records
remaining budget and whether a hit has been seen. Full scan samples twice; early
exit stops at the first hit; the cached mutant samples once and then drains the
counter without fresh randomness.

1. Compute the complete terminating output table of each program. Keep the
   remaining counter visible before projecting to the answer flag.
2. Construct an exact joint between full scan and early exit. Check answer
   agreement and `consumed(early) ≤ consumed(full)` on every supported pair.
3. Split that same joint into failure and success. Check the required branch
   masses and state the `resultSpec` contract for this concrete input.
4. Project to the Boolean flag and construct a deficit certificate for the cached
   mutant against full scan. Choose the orientation of the two sides carefully.
5. Explain how symmetry and the observation implication turn this into failure of
   the original `resultSpec` with full scan on the left and cached search on the right.
6. For general budget `n`, derive the recurrence for failure and success masses.
   Check budgets `0` and `1` before stating the faulty case's assumptions.

**Deliverable:** three output tables, one correctness joint, and one certificate.
Distinguish consumed-trial statements from expected-running-time claims.

## E9. Find the boundary of algebraic reuse

Let `P := exactly δ0 δ0` and `Q := exactly δ0 δ0`, over ENNReal weights.
Both copies of the skip/skip judgment `⟨P⟩ pure ∼ pure ⟨Q⟩` hold.

Someone proposes a one-sided additive-choice rule concluding

```text
⟨P⟩ (a ↦ δa + δa) ∼ pure ⟨Q ⊕ Q⟩.
```

1. Evaluate both outputs at the specified input and show this conclusion fails.
2. Explain why the analogous duplication can work for Set outcomes.
3. State the implemented generic `quad_choice` rule, including what happens on
   **both** sides and which input assertion its two premises share.
4. Sort the laws you used in E2–E7 into `OutcomeModel`, `SummationSemiring`,
   `PositiveSummation`, and `OmegaSummationSemiring`. Check whether exact support
   equivalences were actually needed by each proof.

**Deliverable:** the counterexample and an assumptions table. Do not treat raw
additive choice as a normalized probabilistic sampling command.

## E10. One proof, several meanings

For a summation semiring, define

```text
routes(d,a,b) = d · δ2 + ((a · δ1) >>= (fun _ => b · δ2)).
```

1. Prove `routes(d,a,b) = (d + a*b) · δ2`. Preserve multiplication order.
2. Evaluate the destination weight for Boolean reachability with `(True,True,True)`,
   counting with `(1,1,1)`, ENNReal with `(1/4,1/2,1/2)`, and tropical costs with
   numerical edge costs `(7,2,3)`.
3. Remove the indirect route. Which of those observations changes? Give a count
   certificate and a cost certificate, taking the tropical order into account.
4. For the weighted countdown from E6 with `k(n) := r · δ(n-1)`, prove the full
   semantics is `r^n · δ0`. Identify the induction parameter and the algebraic
   laws needed; decide whether multiplication must commute.

**Deliverable:** the route calculation and one short generic proof. The countdown
proof may be carried into the optional week.

## Optional exercises

**E11 — Outcome-family loop rule.** Transcribe the exact Set `Converges`
definition and `quad_while_fam` statement from `Set/Rules.lean`. Name the active and
exit assertions at each index. For deterministic countdown, choose a fixed initial
counter and describe suitable families on paper. Explain why the existing weighted
coupling loop rule does not itself establish an arbitrary weighted `While-Fam` rule.

**E12 — Coherence and progress.** Read the construction behind
`Weighted.IsCoupling.iSup` and the asynchronous projection theorem. List its
monotonicity premises explicitly. Explain why choosing unrelated coupling witnesses
for each finite fuel does not supply a monotone joint family. Then give a unilateral
retry process that can run arbitrarily many times with positive probability and
explain why almost-sure termination alone supplies no rank decreasing on every
supported step of the existing mixed schedule.

**E13 — Noncommutative observations.** In the finite-word language model, let
`emit a` record the singleton word `[a]`. For distinct `a,b`, calculate the output
languages of `emit a; emit b` and `emit b; emit a`, and refute equality coupling.
Explain why two different singleton languages can be incomparable in the scalar
order, and why the equality-coupling characterization still detects the difference.

## Hints and source pointers — open after attempting

All paths below start from the repository's `RelationalOutcomeLogic/` directory.
The links lead to existing proofs; postpone opening them until you have written
your own argument.

| Exercise | Small hint | Existing definition or proof |
| --- | --- | --- |
| E1 | Compare a universal cross-product with a relation that only needs a partner for each outcome. Empty pieces are allowed by `oplus`. | [`Set/Assertions.lean`](../../RelationalOutcomeLogic/Set/Assertions.lean); [`Set/Coupling.lean`](../../RelationalOutcomeLogic/Set/Coupling.lean): `couple_singleton_iff`, `couple_nonempty_iff`. |
| E2 | Apply the second judgment to the first judgment's outputs; for splitting, transport the four input pieces through bind. | [`Generic/Rules.lean`](../../RelationalOutcomeLogic/Generic/Rules.lean): `quad_seq`, `quad_split`. |
| E3 | Both marginal masses equal the mass of the same joint. For point masses, try a joint concentrated on one pair. | [`Algebra/Weighted/Coupling.lean`](../../RelationalOutcomeLogic/Algebra/Weighted/Coupling.lean): `IsCoupling.mass_eq`, `IsCoupling.pure`. |
| E4 | Forward: compose joints. Reverse: specialize the universal outcome judgment to pure inputs. | [`Subsumption/PRHL/Embedding.lean`](../../RelationalOutcomeLogic/Subsumption/PRHL/Embedding.lean): `prhlSem_iff_quadSem`; [`Generic/Coupling.lean`](../../RelationalOutcomeLogic/Generic/Coupling.lean): `prhl_iff_quad`. |
| E5 | All permitted partners of the selected left event must lie in the right event. The inequality compares actual event masses. | [`Prob/Refutation/Certificate.lean`](../../RelationalOutcomeLogic/Prob/Refutation/Certificate.lean): `MassDeficitCert.refutes`, `of_bounds`, `BugCert.refutes_of_entails`; [`Prob/Refutation/Observation.lean`](../../RelationalOutcomeLogic/Prob/Refutation/Observation.lean): `BugCert.refutes_of_observation`. |
| E6 | At fuel zero even a state outside the guard produces zero. A loop against skip must match skip's unit termination mass. | [`Prob/Semantics/Loop.lean`](../../RelationalOutcomeLogic/Prob/Semantics/Loop.lean): `loopIter`, `loopSem_unfold`, `loopSem_true`; [`Subsumption/PRHL/OneSided.lean`](../../RelationalOutcomeLogic/Subsumption/PRHL/OneSided.lean): `prhl_while_left`. |
| E7 | Use the pending bookkeeping phase as the rank. Joint steps may increase or reset it. | [`Examples/Algebra/AsynchronousCountdown.lean`](../../RelationalOutcomeLogic/Examples/Algebra/AsynchronousCountdown.lean): `Related`, `phaseRank`, `schedule`; [`Generic/Loops/Asynchronous.lean`](../../RelationalOutcomeLogic/Generic/Loops/Asynchronous.lean): `pushforward_loopSem`, `AsyncSchedule.isCoupling_loop`. |
| E8 | Couple fresh trials while neither side has stopped. After early success, the full scan continues against a fixed successful state. | [`Examples/Probability/Search/Alignment.lean`](../../RelationalOutcomeLogic/Examples/Probability/Search/Alignment.lean); [`Examples/Probability/Search/OutcomeContract.lean`](../../RelationalOutcomeLogic/Examples/Probability/Search/OutcomeContract.lean): `result_split`; [`Examples/Probability/Search/CachedRandomness.lean`](../../RelationalOutcomeLogic/Examples/Probability/Search/CachedRandomness.lean): `fair_two_bug`; [`Examples/Probability/Search/Case.lean`](../../RelationalOutcomeLogic/Examples/Probability/Search/Case.lean): `cached_outcome_spec_refuted`. |
| E9 | The proposed postcondition requires two copies of the passive output. Check its total mass. | [`Generic/Rules.lean`](../../RelationalOutcomeLogic/Generic/Rules.lean): `quad_choice`; [`Algebra/Outcome/Basic.lean`](../../RelationalOutcomeLogic/Algebra/Outcome/Basic.lean). |
| E10 | Move a left scale through bind and use the pure-bind law. In the countdown induction, use the power identity with the factor on the correct side. | [`Examples/Algebra/Routes.lean`](../../RelationalOutcomeLogic/Examples/Algebra/Routes.lean): `routes_sem`; [`Examples/Algebra/Countdown.lean`](../../RelationalOutcomeLogic/Examples/Algebra/Countdown.lean): `countdown_sem`. |
| E11 | Separate active outcomes from exits already accumulated. The limit obligation is part of the rule. | [`Set/Rules.lean`](../../RelationalOutcomeLogic/Set/Rules.lean): `Converges`, `quad_while_fam`. |
| E12 | Monotone marginals alone do not assert that your chosen joints are monotone. The implemented product kernel fixes the witnesses used along execution. | [`Generic/Loops/Synchronous.lean`](../../RelationalOutcomeLogic/Generic/Loops/Synchronous.lean); [`Generic/Loops/Asynchronous.lean`](../../RelationalOutcomeLogic/Generic/Loops/Asynchronous.lean). |
| E13 | Concatenation records order. To refute equality coupling, compare the resulting weights directly. | [`Examples/Algebra/Traces.lean`](../../RelationalOutcomeLogic/Examples/Algebra/Traces.lean). |

## Record progress

Mark each exercise **unattempted**, **paper argument**, **checked against source**,
or **reconstructed in Lean**. Add one sentence for the remaining gap. An honest
list of gaps is more useful than checking every box after reading the answers.
