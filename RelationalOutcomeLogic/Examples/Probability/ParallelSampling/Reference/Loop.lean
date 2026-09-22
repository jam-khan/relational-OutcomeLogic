import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Window.Refinement
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Reference.Limits

/-!
# The whole-population proposal loop

A single least-fixed-point loop samples proposals until the accepted-population
quota is reached. Its counters and accumulated population are operational state.
The complete population law agrees with the independently specified sequence of
uncapped retries; no finite proposal or runtime bound is assumed.
-/
namespace RelOL.Prob.ParallelSampling

open scoped ENNReal
universe u
variable {α : Type u}
noncomputable section

structure PopulationState (α : Type u) where
  remaining : Nat
  values : List α
  proposals : Nat
  deriving DecidableEq

def populationUpdate (s : PopulationState α) (j : Job α) : PopulationState α :=
  { remaining := if j.accepted then s.remaining - 1 else s.remaining
    values := if j.accepted then s.values ++ [j.value] else s.values
    proposals := s.proposals + 1 }

def populationGuard (s : PopulationState α) : Prop := s.remaining ≠ 0

def proposalLoop (law : Weight (Job α)) : PopulationState α → Weight (PopulationState α) :=
  loopSem populationGuard (proposalStep law populationUpdate)

def valueUpdate (s : Nat × List α) (j : Job α) : Nat × List α :=
  if j.accepted then (s.1 - 1, s.2 ++ [j.value]) else s

def valueLoop (law : Weight (Job α)) : (Nat × List α) → Weight (Nat × List α) :=
  loopSem (fun s => s.1 ≠ 0) (proposalStep law valueUpdate)

@[simp] lemma valueLoop_zero (law : Weight (Job α)) (xs : List α) :
    valueLoop law (0, xs) = Weight.pure (0, xs) := loopSem_neg (by simp) _

lemma valueLoop_unfold (law : Weight (Job α)) (n : Nat) (xs : List α) :
    valueLoop law (n + 1, xs) = rejection law • valueLoop law (n + 1, xs) +
      Weight.bind (acceptedWeight law) (fun a => valueLoop law (n, xs ++ [a])) := by
  calc
    valueLoop law (n + 1, xs) =
        Weight.bind (proposalStep law valueUpdate (n + 1, xs)) (valueLoop law) :=
      loopSem_pos (g := fun s : Nat × List α => s.1 ≠ 0) (by simp) _
    _ = Weight.bind law (fun j => if j.accepted then valueLoop law (n, xs ++ [j.value])
        else valueLoop law (n + 1, xs)) := by
      simp only [proposalStep, Weight.bind_assoc, Weight.pure_bind]
      congr 1
      funext j
      cases hj : j.accepted <;> simp [valueUpdate, hj]
    _ = _ := proposal_split law (fun a => valueLoop law (n, xs ++ [a]))
      (valueLoop law (n + 1, xs))

lemma valueLoop_subprob (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (s : Nat × List α) : Weight.IsSubprob (valueLoop law s) :=
  loopSem_isSubprob _ _ (fun _ =>
    (hlaw.bind (fun _ => Weight.isProbability_pure _)).isSubprob) s

/-- The full joint population law of a single proposal loop. -/
theorem valueLoop_eq_population (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (n : Nat) (xs : List α) :
    valueLoop law (n, xs) =
      pushforward (fun ys => (0, xs ++ ys)) (population law n) := by
  induction n generalizing xs with
  | zero => simp [population]
  | succ n ih =>
      have hrec : valueLoop law (n + 1, xs) = Weight.bind (conditional law)
          (fun a => valueLoop law (n, xs ++ [a])) := by
        funext t
        have hx : valueLoop law (n + 1, xs) t ≠ ∞ :=
          ne_of_lt ((ENNReal.le_tsum t).trans_lt
            ((valueLoop_subprob law hlaw _).trans_lt ENNReal.one_lt_top))
        have h := solve_accept_retry law hlaw ha _ _ hx
          (congrFun (valueLoop_unfold law n xs) t)
        simpa only [conditional, Weight.smul_bind, Pi.smul_apply, smul_eq_mul] using h
      rw [hrec]
      simp only [ih, population, sample_eq_conditional law hlaw ha,
        pushforward, Weight.bind_assoc, Weight.pure_bind]
      congr 1
      funext a
      congr 1
      funext ys
      simp

def observePopulationState (s : PopulationState α) : Nat × List α :=
  (s.remaining, s.values)

/-- Erasing the proposal counter commutes with each local draw. -/
lemma population_projection_square (law : Weight (Job α)) (s : PopulationState α) :
    pushforward observePopulationState (proposalStep law populationUpdate s) =
      proposalStep law valueUpdate (observePopulationState s) := by
  simp only [proposalStep, pushforward_bind, pushforward_pure]
  congr 1
  funext j
  cases hj : j.accepted <;> simp [observePopulationState, populationUpdate, valueUpdate, hj]

theorem proposalLoop_observe (law : Weight (Job α)) (s : PopulationState α) :
    pushforward observePopulationState (proposalLoop law s) =
      valueLoop law (observePopulationState s) := by
  have h := bind_loopSem_reconstruction
    (fun s => Weight.pure (observePopulationState s)) populationGuard (fun s => s.1 ≠ 0)
    (proposalStep law populationUpdate) (proposalStep law valueUpdate)
    (fun a b hb => by
      rw [Weight.support_pure, Set.mem_singleton_iff] at hb
      subst b
      rfl)
    (fun a _ => by
      rw [Weight.pure_bind]
      exact (population_projection_square law a).symm) s
  simpa only [Weight.pure_bind, pushforward, proposalLoop, valueLoop] using h.symm

/-- The real counter-bearing loop terminates almost surely and returns the complete iid law. -/
theorem proposalLoop_population (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (s : PopulationState α) :
    pushforward observePopulationState (proposalLoop law s) =
      pushforward (fun ys => (0, s.values ++ ys)) (population law s.remaining) := by
  rw [proposalLoop_observe]
  exact valueLoop_eq_population law hlaw ha _ _

theorem proposalLoop_probability (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (s : PopulationState α) :
    Weight.IsProbability (proposalLoop law s) := by
  have h := congrArg Weight.mass (proposalLoop_population law hlaw ha s)
  simp only [mass_pushforward] at h
  exact h.trans (population_probability law hlaw ha s.remaining)

/-- The sliding-window collector is also a real unbounded loop on its pending state. -/
def windowPopulation (law : Weight (Job α)) (w : Nat) (n : Nat) :
    Weight (PopulationState α × List (Job α)) :=
  Weight.bind (pending law w ⟨n, [], 0⟩)
    (loopSem (fun s => populationGuard s.1) (windowStep law populationUpdate))

theorem windowPopulation_reference (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (w n : Nat) :
    pushforward Prod.fst (windowPopulation law w n) = proposalLoop law ⟨n, [], 0⟩ :=
  window_loop_observe law hlaw w populationUpdate populationGuard _

theorem windowPopulation_probability (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (w n : Nat) : Weight.IsProbability (windowPopulation law w n) := by
  have h := congrArg Weight.mass (windowPopulation_reference law hlaw w n)
  rw [mass_pushforward] at h
  exact h.trans (proposalLoop_probability law hlaw ha _)

/-- The whole accepted-population law, with positive acceptance supplying mass one. -/
theorem windowPopulation_values (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (w n : Nat) :
    pushforward (fun s => s.1.values) (windowPopulation law w n) =
      iid (conditional law) n := by
  calc
    _ = pushforward (fun s : PopulationState α => s.values)
        (pushforward Prod.fst (windowPopulation law w n)) := by
      simp only [pushforward, Weight.bind_assoc, Weight.pure_bind]
    _ = pushforward (fun s : PopulationState α => s.values)
        (proposalLoop law ⟨n, [], 0⟩) := by rw [windowPopulation_reference law hlaw]
    _ = pushforward Prod.snd
        (pushforward observePopulationState (proposalLoop law ⟨n, [], 0⟩)) := by
      simp only [pushforward, Weight.bind_assoc, Weight.pure_bind, observePopulationState]
    _ = population law n := by
      rw [proposalLoop_population law hlaw ha]
      simp only [pushforward, Weight.bind_assoc, Weight.pure_bind, List.nil_append,
        Weight.bind_pure]
    _ = iid (conditional law) n := population_eq_iid law hlaw ha n

end
end RelOL.Prob.ParallelSampling
