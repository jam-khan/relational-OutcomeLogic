import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.UncappedCorrectness
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Window.Work

/-!
# The actual worker pool's joint population and stopping-ticket law

Strictly interior executions refine finite successful proposal prefixes. These
prefixes lie below the flat reference loop. Both uncapped programs have mass
one, so domination gives equality of the full population-and-count law. The
stopping ticket used in the speculation contract is therefore the actual
negative-binomial proposal count, jointly with the returned population.
-/
namespace RelOL.Prob.ParallelSampling

universe u
variable {α : Type u}
noncomputable section

private def successState (s : PopulationState α) (jobs : List (Job α)) :
    Weight (PopulationState α) :=
  match select s.remaining jobs with
  | .success ys => Weight.pure ⟨0, s.values ++ ys, s.proposals + used s.remaining jobs⟩
  | .exhausted _ => 0

private def successfulState (law : Weight (Job α)) (cap : Nat) (s : PopulationState α) :
    Weight (PopulationState α) := Weight.bind (draws law cap) (successState s)

private lemma successfulState_zero_quota (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (cap c : Nat) (xs : List α) :
    successfulState law cap ⟨0, xs, c⟩ = Weight.pure ⟨0, xs, c⟩ := by
  change Weight.bind (draws law cap) (fun jobs => successState ⟨0, xs, c⟩ jobs) = _
  simp only [successState, select, used, List.append_nil, Nat.add_zero]
  exact Weight.bind_const_of_isProbability _ (draws_probability law hlaw cap) _

private lemma successState_cons (n c : Nat) (xs : List α) (j : Job α)
    (js : List (Job α)) :
    successState ⟨n + 1, xs, c⟩ (j :: js) =
      successState (populationUpdate ⟨n + 1, xs, c⟩ j) js := by
  cases hj : j.accepted with
  | false =>
      cases hs : select (n + 1) js <;>
        simp [successState, select, used, populationUpdate, hj, hs, Nat.add_assoc]
  | true =>
      cases hs : select n js <;>
        simp [successState, select, used, populationUpdate, hj, hs,
          Result.prepend, Nat.add_assoc]

private lemma successfulState_succ (law : Weight (Job α)) (cap n c : Nat) (xs : List α) :
    successfulState law (cap + 1) ⟨n + 1, xs, c⟩ =
      Weight.bind law (fun j => successfulState law cap
        (populationUpdate ⟨n + 1, xs, c⟩ j)) := by
  simp only [successfulState, draws, Weight.bind_assoc, Weight.pure_bind,
    successState_cons]

/-- Every successful finite prefix is a genuine prefix of the flat proposal loop. -/
private lemma successfulState_le_proposalLoop (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (cap : Nat) (s : PopulationState α) :
    successfulState law cap s ≤ proposalLoop law s := by
  induction cap generalizing s with
  | zero =>
      rcases s with ⟨n, xs, c⟩
      cases n with
      | zero => simp [successfulState, successState, draws, select, used, proposalLoop,
          populationGuard, loopSem_neg]
      | succ n => simp only [successfulState, draws, Weight.pure_bind, successState,
          select]; exact bot_le
  | succ cap ih =>
      rcases s with ⟨n, xs, c⟩
      cases n with
      | zero =>
          rw [successfulState_zero_quota law hlaw]
          simp [proposalLoop, populationGuard, loopSem_neg]
      | succ n =>
          rw [successfulState_succ]
          have hstep : proposalLoop law (⟨n + 1, xs, c⟩ : PopulationState α) =
              Weight.bind law (fun j => proposalLoop law
                (populationUpdate ⟨n + 1, xs, c⟩ j)) := by
            change loopSem _ _ _ = _
            rw [loopSem_pos (g := populationGuard) (by simp [populationGuard])]
            simp only [proposalStep, Weight.bind_assoc, Weight.pure_bind]
            rfl
          rw [hstep]
          exact Weight.bind_mono_right _ fun j => ih _

private def populationRecord (s : PopulationState α) : Nat × List α :=
  (s.proposals, s.values)

/-- The public observer retains the stopping ticket and the complete population. -/
def PoolResult.record (p : PoolResult α) : Nat × List α := (p.committed, p.population)

private lemma interior_record_le_prefix (workers window quota cap : Nat)
    (hw : 0 < workers) (hwindow : 0 < window) (jobs : List (Job α)) :
    pushforward PoolResult.record (interiorSuccess cap (pool workers window quota jobs)) ≤
      pushforward populationRecord (successState (⟨quota, [], 0⟩ : PopulationState α) jobs) := by
  have hp := pool_answer workers window quota hw hwindow jobs
  have hc := pool_committed workers window quota hw hwindow jobs
  cases hs : select quota jobs with
  | exhausted xs => simp [interiorSuccess, hp, hs, successState]
  | success xs =>
      by_cases hb : (pool workers window quota jobs).started < cap
      · simp [interiorSuccess, hp, hs, hb, successState, populationRecord,
          PoolResult.record, PoolResult.population, hc, Result.population]
      · simp only [interiorSuccess, hp, hs, if_neg hb, pushforward_zero]
        exact bot_le

private lemma interiorRecord_le_proposalLoop (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (workers window quota cap : Nat)
    (hw : 0 < workers) (hwindow : 0 < window) :
    pushforward PoolResult.record (interiorCollector law workers window quota cap) ≤
      pushforward populationRecord (proposalLoop law ⟨quota, [], 0⟩) := by
  rw [interiorCollector, freshCollector_eq_scheduledPrefix law hlaw workers window quota
    cap hw hwindow]
  simp only [scheduledPrefix, bind_pushforward, pushforward_bind]
  calc
    _ ≤ Weight.bind (draws law cap) (fun jobs => pushforward populationRecord
        (successState (⟨quota, [], 0⟩ : PopulationState α) jobs)) :=
      Weight.bind_mono_right _ (interior_record_le_prefix workers window quota cap hw hwindow)
    _ = pushforward populationRecord (successfulState law cap ⟨quota, [], 0⟩) :=
      (pushforward_bind _ _ _).symm
    _ ≤ _ := Weight.bind_mono_left (successfulState_le_proposalLoop law hlaw cap _)
      (fun s => Weight.pure (populationRecord s))

private lemma proposalLoop_record (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (quota : Nat) :
    pushforward populationRecord (proposalLoop law ⟨quota, [], 0⟩) =
      countedPopulation law quota := by
  rw [proposalLoop_counted law hlaw ha, pushforward_bind]
  simp only [pushforward_pure, populationRecord, List.nil_append, Nat.zero_add]
  exact Weight.bind_pure _

/-- The exact joint law of output population and proposals through its final acceptance. -/
theorem uncappedCollector_record (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (workers window quota : Nat)
    (hw : 0 < workers) (hwindow : 0 < window) :
    pushforward PoolResult.record (uncappedCollector law workers window quota) =
      countedPopulation law quota := by
  have hle : pushforward PoolResult.record (uncappedCollector law workers window quota) ≤
      countedPopulation law quota := by
    rw [uncappedCollector_eq_iSup_interior law workers window quota hw hwindow,
      pushforward_iSup _ _ (interiorCollector_monotone law workers window quota)]
    apply iSup_le
    intro cap
    rw [← proposalLoop_record law hlaw ha quota]
    exact interiorRecord_le_proposalLoop law hlaw workers window quota cap hw hwindow
  have hm : Weight.mass (pushforward PoolResult.record
      (uncappedCollector law workers window quota)) = 1 := by
    rw [mass_pushforward]
    exact uncappedCollector_probability law hlaw ha workers window quota hw hwindow
  have hn : Weight.mass (countedPopulation law quota) = 1 :=
    countedPopulation_probability law hlaw ha quota
  funext r
  apply le_antisymm (hle r)
  by_contra h
  have hfinite : (∑' r, pushforward PoolResult.record
      (uncappedCollector law workers window quota) r) ≠ ⊤ := by
    change Weight.mass _ ≠ ⊤
    rw [hm]
    exact ENNReal.one_ne_top
  have ht := ENNReal.tsum_lt_tsum hfinite hle (lt_of_not_ge h)
  change Weight.mass _ < Weight.mass _ at ht
  rw [hm, hn] at ht
  exact (lt_irrefl _ ht)

/-- The actual worker-pool stopping ticket has expectation n/a. -/
theorem uncappedCollector_expected_committed (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law)
    (workers window quota : Nat) (hw : 0 < workers) (hwindow : 0 < window) :
    Weight.expectation (uncappedCollector law workers window quota) (fun r => r.committed) =
      quota / acceptance law := by
  have h := congrArg (fun μ => Weight.expectation μ (fun r : Nat × List α => r.1))
    (uncappedCollector_record law hlaw ha workers window quota hw hwindow)
  simpa only [pushforward, Weight.expectation_bind, Weight.expectation_pure,
    PoolResult.record, countedPopulation_expected_proposals law hlaw ha] using h

end
end RelOL.Prob.ParallelSampling
