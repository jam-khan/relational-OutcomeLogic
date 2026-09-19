import RelationalOutcomeLogic.Prob.SearchCoupling
import RelationalOutcomeLogic.Prob.Restriction

/-!
# Quantitative outcome contract for early-exit search

Split the actual asynchronous joint by failure and success. Each branch retains
its probability, answer relation, and consumed-trial bound. This states more than
agreement of answers: it records the n-dependent failure probability and includes
the probability-zero success branch at budget zero.
-/

namespace RelOL.Prob.Search

open scoped ENNReal

noncomputable section

/-- Failure exhausts the budget on both sides. -/
def failureResult (n : ℕ) (s t : State) : Prop :=
  s.2 = false ∧ t.2 = false ∧ consumed n s = n ∧ consumed n t = n

/-- Success permits early exit, with a coupled upper bound on the number of consumed trials. -/
def successResult (n : ℕ) (s t : State) : Prop :=
  s.2 = true ∧ t.2 = true ∧ consumed n t ≤ consumed n s ∧ consumed n s = n

/-- The two outcome classes retain exact masses as well as relational properties. -/
def resultSpec (T : Trial) (n : ℕ) : RAssn State State :=
  oplus
    (fun μ ν => couple (failureResult n) μ ν ∧ massEq (T.miss ^ n) (T.miss ^ n) μ ν)
    (fun μ ν => couple (successResult n) μ ν ∧ massEq (successMass T n) (successMass T n) μ ν)

theorem full_failure_mass (T : Trial) (n : ℕ) :
    Weight.mass (Weight.restrict (sem (full T) (n, false)) (fun s => s.2 = false)) =
      T.miss ^ n := by
  rw [full_sem_false, Weight.restrict_add, Weight.restrict_smul, Weight.restrict_smul]
  simp

theorem full_success_mass (T : Trial) (n : ℕ) :
    Weight.mass (Weight.restrict (sem (full T) (n, false)) (fun s => s.2 ≠ false)) =
      successMass T n := by
  rw [full_sem_false, Weight.restrict_add, Weight.restrict_smul, Weight.restrict_smul]
  simp

/-- The scheduler's exact marginal equations transfer each branch probability to early exit. -/
theorem early_failure_mass (T : Trial) (n : ℕ) :
    Weight.mass (Weight.restrict (sem (early T) (n, false)) (fun s => s.2 = false)) =
      T.miss ^ n := by
  have h := (outputs_coupled T (n, false)).restrict
    (fun s => s.2 = false) (fun t => t.2 = false) (fun s t h => by rw [h.1.1])
  rw [← h.mass_eq]
  exact full_failure_mass T n

theorem early_success_mass (T : Trial) (n : ℕ) :
    Weight.mass (Weight.restrict (sem (early T) (n, false)) (fun s => s.2 ≠ false)) =
      successMass T n := by
  have h := (outputs_coupled T (n, false)).restrict
    (fun s => s.2 ≠ false) (fun t => t.2 ≠ false) (fun s t h => by rw [h.1.1])
  rw [← h.mass_eq]
  exact full_success_mass T n

/-- The split is obtained from the same joint execution used for asynchronous correctness. -/
theorem result_split (T : Trial) (n : ℕ) :
    resultSpec T n (sem (full T) (n, false)) (sem (early T) (n, false)) := by
  have hc : Coupled (fun s t => Related s t ∧ ¬ fullGuard s ∧ ¬ earlyGuard t)
      (sem (full T) (n, false)) (sem (early T) (n, false)) :=
    ⟨outputJoint T (n, false), outputJoint_isCoupling T (n, false)⟩
  have hsplit := hc.split_mass (fun s => s.2 = false) (fun t => t.2 = false)
    (fun s t h => by rw [h.1.1])
  rw [full_failure_mass, full_success_mass] at hsplit
  apply oplus_mono ?_ ?_ _ _ hsplit
  · intro μ ν h
    refine ⟨h.1.mono ?_, h.2⟩
    rintro s t ⟨hexit, hs, ht⟩
    have hszero : s.1 = 0 := Nat.eq_zero_of_not_pos hexit.2.1
    have htzero : t.1 = 0 := (hexit.1.2.2 hs).symm.trans hszero
    exact ⟨hs, ht, by simp [consumed, hszero], by simp [consumed, htzero]⟩
  · intro μ ν h
    refine ⟨h.1.mono ?_, h.2⟩
    rintro s t ⟨hexit, hs, ht⟩
    have hs' : s.2 = true := by cases hb : s.2 <;> simp_all
    have ht' : t.2 = true := by cases hb : t.2 <;> simp_all
    have hszero : s.1 = 0 := Nat.eq_zero_of_not_pos hexit.2.1
    exact ⟨hs', ht', consumed_bound hexit.1 n, by simp [consumed, hszero]⟩

/-- A weighted program judgment with quantitative success/failure and resource postconditions. -/
theorem search_outcome_quad (T : Trial) (n : ℕ) :
    quad (exactly (seed n) (seed n)) (full T) (early T) (resultSpec T n) := by
  rintro μ ν ⟨rfl, rfl⟩
  simpa only [seed, semLift_pure] using result_split T n

/-- The postcondition itself enforces total mass one, including zero-budget boundary cases. -/
theorem resultSpec_mass_one (T : Trial) (n : ℕ) :
    entail (resultSpec T n) (massEq 1 1) := by
  intro μ ν h
  have hm := oplus_mono (fun _ _ h => h.2) (fun _ _ h => h.2) μ ν h
  have hsum := oplus_massEq (T.miss ^ n) (T.miss ^ n)
    (successMass T n) (successMass T n) μ ν hm
  simpa only [failure_add_success] using hsum

end

end RelOL.Prob.Search
