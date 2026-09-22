import RelationalOutcomeLogic.Examples.Probability.Search.Alignment
import RelationalOutcomeLogic.Prob.Refutation.EventMass

/-!
# Positive probability of saving trials

For any budget of at least two trials, a first-trial success saves at least one
trial. Its probability is at least the trial's hit mass. This compares actual
finite output events; no expected-cost semantics is needed.
-/

namespace RelOL.Prob.Search

open scoped ENNReal

noncomputable section

/-- A success stops early search immediately, retaining its unused budget. -/
@[simp] theorem early_sem_true (T : Trial) (n : ℕ) :
    sem (early T) (n, true) = Weight.pure (n, true) := by
  rw [early, sem_while_neg (g := earlyGuard) (by simp [earlyGuard])]

/-- One unsuccessful trial recurses, while the hit branch returns immediately. -/
theorem early_sem_succ_false (T : Trial) (n : ℕ) :
    sem (early T) (n + 1, false) =
      T.miss • sem (early T) (n, false) + T.hit • Weight.pure (n, true) := by
  rw [early, sem_while_pos (g := earlyGuard) (by simp [earlyGuard])]
  change Weight.bind (draw T (n + 1, false)) (sem (early T)) = _
  simp only [draw, Weight.add_bind, Weight.smul_bind, Weight.pure_bind, Nat.add_sub_cancel,
    early_sem_true]
  rfl

/-- The first-hit branch alone supplies this much mass to the corresponding terminal state. -/
theorem early_first_hit_lower_bound (T : Trial) (n : ℕ) :
    T.hit ≤ (sem (early T) (n + 1, false)) (n, true) := by
  rw [early_sem_succ_false]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Weight.pure_apply, ite_true, mul_one]
  exact le_add_left le_rfl

/-- Successful returns that consume a nonempty proper prefix of the initial budget. -/
def savingEvent (N : ℕ) : Finset State :=
  ((Finset.range N).filter (fun remaining => 0 < remaining)).image
    (fun remaining => (remaining, true))

@[simp] theorem mem_savingEvent_iff (N : ℕ) (s : State) :
    s ∈ savingEvent N ↔ 0 < s.1 ∧ s.1 < N ∧ s.2 = true := by
  rcases s with ⟨remaining, found⟩
  simp [savingEvent, and_comm, and_assoc]

theorem mem_savingEvent_iff_consumed (N : ℕ) (s : State) :
    s ∈ savingEvent N ↔ s.2 = true ∧ 0 < consumed N s ∧ consumed N s < N := by
  rw [mem_savingEvent_iff]
  unfold consumed
  constructor
  · rintro ⟨hpos, hlt, hfound⟩
    exact ⟨hfound, by omega, by omega⟩
  · rintro ⟨hfound, hpos, hlt⟩
    exact ⟨by omega, by omega, hfound⟩

/-- With at least two trials available, hitting on the first has used exactly one trial. -/
theorem first_hit_consumed (n : ℕ) : consumed (n + 2) (n + 1, true) = 1 ∧ 1 < n + 2 := by
  simp only [consumed]
  omega

/-- At least the first-hit mass yields a strict saving over a full scan. -/
theorem early_savingEvent_mass_ge_hit (T : Trial) (n : ℕ) :
    T.hit ≤ Weight.eventMass (sem (early T) (n + 2, false)) (savingEvent (n + 2)) := by
  calc
    T.hit ≤ (sem (early T) (n + 2, false)) (n + 1, true) :=
      early_first_hit_lower_bound T (n + 1)
    _ = Weight.eventMass (sem (early T) (n + 2, false)) {(n + 1, true)} :=
      (Weight.eventMass_singleton _ _).symm
    _ ≤ Weight.eventMass (sem (early T) (n + 2, false)) (savingEvent (n + 2)) := by
      apply Weight.eventMass_mono_set
      apply Finset.singleton_subset_iff.mpr
      rw [mem_savingEvent_iff]
      exact ⟨by omega, by omega, rfl⟩

/-- The full scan never returns with a strict saving, irrespective of its result. -/
theorem full_savingEvent_mass_zero (T : Trial) (N : ℕ) :
    Weight.eventMass (sem (full T) (N, false)) (savingEvent N) = 0 := by
  rw [full_sem_false, Weight.eventMass_add, Weight.eventMass_smul, Weight.eventMass_smul]
  simp

/-- Positive hit probability gives a positive probability of consuming fewer trials. -/
theorem positive_saving_probability (T : Trial) (n : ℕ) (hhit : 0 < T.hit) :
    0 < Weight.eventMass (sem (early T) (n + 2, false)) (savingEvent (n + 2)) :=
  lt_of_lt_of_le hhit (early_savingEvent_mass_ge_hit T n)

end

end RelOL.Prob.Search
