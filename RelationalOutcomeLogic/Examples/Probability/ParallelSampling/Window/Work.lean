import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Reference.Loop

/-!
# Exact proposal accounting for the sliding window

The reference's flat proposal loop agrees with the counted sequence of retries.
The window launches one new job at each commit and retains exactly `W - 1`
pending jobs. Thus work is coupled to the same stopping-time counter, rather
than estimated from a separate surrogate law.
-/
namespace RelOL.Prob.ParallelSampling

open scoped ENNReal
universe u
variable {α σ : Type u}
noncomputable section

private def countedSpecification (law : Weight (Job α)) (s : PopulationState α) :
    Weight (PopulationState α) :=
  Weight.bind (countedPopulation law s.remaining) fun p =>
    Weight.pure ⟨0, s.values ++ p.2, s.proposals + p.1⟩

private lemma bind_waiting_split (law : Weight (Job α)) {β : Type u}
    (f : Nat × α → Weight β) :
    Weight.bind (waiting law) f =
      Weight.bind (acceptedWeight law) (fun a => f (0, a)) +
      rejection law • Weight.bind (waiting law) (fun p => f (p.1 + 1, p.2)) := by
  conv_lhs => rw [waiting_recursion]
  rw [Weight.add_bind, Weight.smul_bind, bind_pushforward, Weight.bind_assoc]
  simp only [Weight.pure_bind]

private lemma countedSpecification_zero (law : Weight (Job α)) (xs : List α) (c : Nat) :
    countedSpecification law ⟨0, xs, c⟩ = Weight.pure ⟨0, xs, c⟩ := by
  simp [countedSpecification, countedPopulation]

private lemma countedSpecification_succ (law : Weight (Job α))
    (n c : Nat) (xs : List α) :
    countedSpecification law ⟨n + 1, xs, c⟩ =
      rejection law • countedSpecification law ⟨n + 1, xs, c + 1⟩ +
      Weight.bind (acceptedWeight law) (fun a =>
        countedSpecification law ⟨n, xs ++ [a], c + 1⟩) := by
  unfold countedSpecification
  simp only [countedPopulation, Weight.bind_assoc, Weight.pure_bind]
  rw [bind_waiting_split]
  rw [add_comm]
  congr 1
  · congr 1
    congr 1
    funext p
    congr 1
    funext rest
    simp [Nat.add_left_comm, Nat.add_comm]
  · congr 1
    funext a
    congr 1
    funext rest
    simp [Nat.add_assoc]

private lemma countedSpecification_fixed (law : Weight (Job α)) :
    loopHom populationGuard (proposalStep law populationUpdate)
      (countedSpecification law) ≤ countedSpecification law := by
  intro s
  rcases s with ⟨n, xs, c⟩
  cases n with
  | zero => simp [loopHom_apply, populationGuard, countedSpecification_zero]
  | succ n =>
      rw [loopHom_apply, if_pos (by simp [populationGuard])]
      simp only [proposalStep, Weight.bind_assoc, Weight.pure_bind]
      have h : (fun j : Job α => countedSpecification law
          (populationUpdate ⟨n + 1, xs, c⟩ j)) =
          (fun j => if j.accepted then countedSpecification law ⟨n, xs ++ [j.value], c + 1⟩
            else countedSpecification law ⟨n + 1, xs, c + 1⟩) := by
        funext j
        cases hj : j.accepted <;> simp [populationUpdate, hj]
      rw [h, proposal_split law
        (fun a => countedSpecification law ⟨n, xs ++ [a], c + 1⟩)
        (countedSpecification law ⟨n + 1, xs, c + 1⟩),
        ← countedSpecification_succ]

private lemma probability_eq_of_le {β : Type*} {μ ν : Weight β}
    (hμ : Weight.IsProbability μ) (hν : Weight.IsProbability ν) (hle : μ ≤ ν) : μ = ν := by
  funext b
  apply le_antisymm (hle b)
  by_contra h
  have hstrict : μ b < ν b := lt_of_not_ge h
  have hfinite : (∑' b, μ b) ≠ ∞ := by
    change Weight.mass μ ≠ ∞
    rw [hμ]
    exact ENNReal.one_ne_top
  have ht := ENNReal.tsum_lt_tsum hfinite hle hstrict
  change Weight.mass μ < Weight.mass ν at ht
  rw [hμ, hν] at ht
  exact (lt_irrefl _ ht)

/-- Exact joint population and stopping-time law for the single operational loop. -/
theorem proposalLoop_counted (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (s : PopulationState α) :
    proposalLoop law s = Weight.bind (countedPopulation law s.remaining) fun p =>
      Weight.pure (⟨0, s.values ++ p.2, s.proposals + p.1⟩ : PopulationState α) := by
  apply probability_eq_of_le (proposalLoop_probability law hlaw ha s)
    ((countedPopulation_probability law hlaw ha s.remaining).bind
      (fun _ => Weight.isProbability_pure _))
  exact loopSem_le _ _ (countedSpecification law) (countedSpecification_fixed law) s

/-- Actual flat-loop proposal work has expectation initialCount + n/a. -/
theorem proposalLoop_expected_proposals (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law) (s : PopulationState α) :
    Weight.expectation (proposalLoop law s) (fun t => t.proposals) =
      s.proposals + s.remaining / acceptance law := by
  rw [proposalLoop_counted law hlaw ha, Weight.expectation_bind]
  simp only [Weight.expectation_pure, Nat.cast_add]
  rw [Weight.expectation_add_cost, Weight.expectation_const,
    show Weight.mass (countedPopulation law s.remaining) = 1 from
      countedPopulation_probability law hlaw ha s.remaining,
    one_mul, countedPopulation_expected_proposals law hlaw ha]

private lemma consume_length (update : σ → Job α → σ) (s : σ)
    (js : List (Job α)) (j : Job α) : (consume update s (js ++ [j])).2.length = js.length := by
  cases js <;> simp [consume]

/-- Every committed step preserves the fixed number of pending tickets. -/
lemma windowStep_length (law : Weight (Job α)) (update : σ → Job α → σ)
    (s t : σ × List (Job α)) (ht : t ∈ Weight.support (windowStep law update s)) :
    t.2.length = s.2.length := by
  obtain ⟨j, _, hj⟩ := (Weight.mem_support_bind_iff _ _ _).mp ht
  rw [Weight.support_pure, Set.mem_singleton_iff] at hj
  subst t
  exact consume_length _ _ _ _

/-- At termination the W−1 pending jobs are the entire canceled suffix. -/
theorem windowPopulation_discarded (law : Weight (Job α)) (w n : Nat)
    (t : PopulationState α × List (Job α))
    (ht : t ∈ Weight.support (windowPopulation law w n)) : t.2.length = w := by
  obtain ⟨s, hs, hst⟩ := (Weight.mem_support_bind_iff _ _ _).mp ht
  obtain ⟨js, hjs, hs⟩ := (Weight.mem_support_bind_iff _ _ _).mp hs
  rw [Weight.support_pure, Set.mem_singleton_iff] at hs
  subst s
  apply (loopSem_support_invariant _ _ (fun t => t.2.length = w) ?_
    _ (draws_support_length law w js hjs) t hst).1
  intro s hs _ t ht
  exact (windowStep_length law populationUpdate s t ht).trans hs

/-- Initial prefetch plus one launch per committed proposal. -/
def windowStarted (w : Nat) (s : PopulationState α × List (Job α)) : Nat :=
  w + s.1.proposals

/-- The stopping-time law and the speculation bound hold under the same reconstruction. -/
theorem windowPopulation_expected_started (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law) (w n : Nat) :
    Weight.expectation (windowPopulation law w n) (fun t => windowStarted w t) =
      n / acceptance law + w := by
  have hc := congrArg (fun μ => Weight.expectation μ (fun s : PopulationState α =>
    (w : ℝ≥0∞) + s.proposals)) (windowPopulation_reference law hlaw w n)
  simp only [pushforward, Weight.expectation_bind, Weight.expectation_pure] at hc
  simp only [windowStarted, Nat.cast_add]
  rw [hc, Weight.expectation_add_cost, Weight.expectation_const,
    show Weight.mass (proposalLoop law (⟨n, [], 0⟩ : PopulationState α)) = 1 from
      proposalLoop_probability law hlaw ha _, one_mul,
    proposalLoop_expected_proposals law hlaw ha]
  simp [add_comm]

end
end RelOL.Prob.ParallelSampling
