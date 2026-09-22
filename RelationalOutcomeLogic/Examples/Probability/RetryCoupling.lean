import RelationalOutcomeLogic.Prob.Logic.Rules
import RelationalOutcomeLogic.Examples.Probability.GeometricRetry

/-!
# Probabilistic commands and unbounded-loop examples

Two coin-retry loops use opposite Boolean encodings. A body coupling preserves the
encoding relation, and the synchronous loop rule transports it to the outputs. The
left loop terminates with probability one but no finite fuel captures all its mass.
Always-true loops also exercise the rule's divergence-tolerant exact marginals.
-/

namespace RelOL.Prob.LoopExamples

open Examples

noncomputable section

/-- A normalized fair coin updates the Boolean state. -/
def coin : Cmd Bool := .sample (fun _ => fair) (fun _ => fair_isProbability)

/-- Retry a fair coin while the state is true. -/
def retryTrue : Cmd Bool := .while (fun s => s = true) coin

/-- The same retry algorithm with the opposite Boolean encoding. -/
def retryFalse : Cmd Bool := .while (fun s => s = false) coin

/-- Correctness is derived through the sampling and synchronous loop rules. -/
theorem retry_opposite_spec :
    quad (couple (fun a b : Bool => a = !b)) retryTrue retryFalse
      (couple (fun a b => a = !b ∧ a ≠ true ∧ b ≠ false)) := by
  apply quad_couple_while
  · intro a b hab
    cases a <;> cases b <;> simp_all
  · apply quad_couple_sample
    intro a b _
    exact fair_opposite_coupling

theorem retry_outputs_coupled :
    Coupled (fun a b : Bool => a = !b ∧ a ≠ true ∧ b ≠ false)
      (sem retryTrue true) (sem retryFalse false) := by
  simpa only [semLift_pure, couple] using
    retry_opposite_spec (Weight.pure true) (Weight.pure false) (Coupled.pure rfl)

theorem retryTrue_result : sem retryTrue true = Weight.pure false := by
  exact geometricLoop_true

/-- Coupling transfers the first loop's almost-sure termination to the second. -/
theorem retryFalse_isProbability : Weight.IsProbability (sem retryFalse false) := by
  change Weight.mass (sem retryFalse false) = 1
  rw [← retry_outputs_coupled.mass_eq, retryTrue_result, Weight.mass_pure]

/-- Every finite approximation omits some terminating mass. -/
theorem retryTrue_no_finite_fuel (n : ℕ) :
    loopIter (fun s => s = true) (sem coin) n true ≠ sem retryTrue true := by
  intro h
  have hlt := geometricLoop_iter_mass_lt_one n
  change Weight.mass (loopIter (fun s => s = true) (sem coin) n true) < 1 at hlt
  rw [h, retryTrue_result, Weight.mass_pure] at hlt
  exact (lt_irrefl _ hlt)

/-- An always-true loop has zero terminating weight. -/
def spin : Cmd Unit := .while (fun _ => True) .skip

/-- The synchronous rule also handles joint divergence, with an impossible exit relation. -/
theorem spin_spec :
    quad (couple (Eq : Unit → Unit → Prop)) spin spin
      (couple (fun a b => a = b ∧ ¬ True ∧ ¬ True)) := by
  apply quad_couple_while
  · intro _ _ _
    rfl
  · exact quad_consequence (couple_mono fun _ _ h => h.1)
      (quad_skip (couple Eq)) (entail_refl _)

theorem spin_result : sem spin () = 0 := sem_while_true .skip ()

/-- Exact marginals correctly reject comparing divergence with a terminating skip. -/
theorem spin_skip_refuted : ¬ quad (couple Eq) spin .skip (couple Eq) := by
  intro h
  have hc := h (Weight.pure ()) (Weight.pure ()) (Coupled.pure rfl)
  have hm := hc.mass_eq
  simp only [semLift_pure, spin_result, sem_skip, Weight.mass_zero, Weight.mass_pure] at hm
  exact zero_ne_one hm

end

end RelOL.Prob.LoopExamples
