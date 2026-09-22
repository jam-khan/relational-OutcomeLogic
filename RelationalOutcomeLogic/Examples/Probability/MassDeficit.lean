import RelationalOutcomeLogic.Prob.Refutation.Certificate
import RelationalOutcomeLogic.Examples.Probability.Coins

/-!
# Checked quantitative refutation examples

Finite events certify a probability deficit even when both distributions have the
same support and total mass. The final example ties the output certificate to
weighted sampling functions and an explicit input assertion.
-/

namespace RelOL.Prob.CertificateExamples

open scoped ENNReal
open Examples

noncomputable section

/-- The false outcome has mass one half on the left and one quarter on the right. -/
def fair_biased_cert : MassDeficitCert Eq fair biased where
  left := {false}
  right := {false}
  cover := by
    intro a ha b hab
    simpa only [← hab] using ha
  deficit := by
    norm_num [Weight.eventMass, fair, half, biased, Weight.pure]

theorem fair_biased_refuted : ¬ Coupled Eq fair biased := fair_biased_cert.refutes

/-- A conservative left lower bound of one third still separates the two event masses. -/
def fair_biased_bounds_cert : MassDeficitCert Eq fair biased :=
  MassDeficitCert.of_bounds {false} {false} fair_biased_cert.cover
    (lower := 1 / 3) (upper := 1 / 4)
    (by norm_num [Weight.eventMass, fair, half, Weight.pure])
    (by norm_num [Weight.eventMass, biased, Weight.pure])
    (by norm_num)

/-- Sound certificates cannot reject the valid equality coupling. -/
theorem no_fair_fair_certificate : ¬ Nonempty (MassDeficitCert Eq fair fair) :=
  fair_equality_coupling.no_massDeficitCert

/-- Allowing true to match false still cannot repair a deficit at false on the left. -/
def fair_biased_lowering_cert :
    MassDeficitCert (fun a b : Bool => a = b ∨ (a = true ∧ b = false)) fair biased where
  left := {false}
  right := {false}
  cover := by
    intro a ha b hab
    rcases hab with hab | ⟨_, hb⟩
    · simpa only [← hab] using ha
    · exact Finset.mem_singleton.mpr hb
  deficit := by
    norm_num [Weight.eventMass, fair, half, biased, Weight.pure]

theorem fair_biased_lowering_refuted :
    ¬ Coupled (fun a b : Bool => a = b ∨ (a = true ∧ b = false)) fair biased :=
  fair_biased_lowering_cert.refutes

/-- Splitting outcomes between equality and the additional edge cannot evade the deficit. -/
theorem fair_biased_split_refuted :
    ¬ oplus (couple Eq) (couple (fun a b : Bool => a = true ∧ b = false)) fair biased :=
  fair_biased_lowering_cert.refutes_oplus

/-- A termination-mass mismatch yields a certificate even for the unrestricted relation. -/
def unequal_termination_cert :
    MassDeficitCert (fun _ _ : Unit => True)
      (Weight.pure ()) ((1 / 2 : ℝ≥0∞) • Weight.pure ()) where
  left := {()}
  right := {()}
  cover := by
    intro _ _ b _
    cases b
    exact Finset.mem_singleton_self ()
  deficit := by
    norm_num [Weight.eventMass, Weight.pure]

theorem unequal_termination_refuted :
    ¬ Coupled (fun _ _ : Unit => True)
      (Weight.pure ()) ((1 / 2 : ℝ≥0∞) • Weight.pure ()) :=
  unequal_termination_cert.refutes

/-- Only the selected events are finite; the state space can be all natural numbers. -/
def nat_finite_event_cert :
    MassDeficitCert Eq (Weight.pure (0 : ℕ)) (Weight.pure 1) where
  left := {0}
  right := {0}
  cover := by
    intro a ha b hab
    simpa only [← hab] using ha
  deficit := by
    norm_num [Weight.eventMass, Weight.pure]

/-- A normalized fair sample, expressed directly using weighted sequencing. -/
def sampleFair (μ : Weight Unit) : Weight Bool := Weight.bind μ (fun _ => fair)

/-- A normalized biased sample with the same possible outcomes. -/
def sampleBiased (μ : Weight Unit) : Weight Bool := Weight.bind μ (fun _ => biased)

/-- The output certificate is attached to actual executions from unit input weights. -/
def sampling_bug : BugCert sampleFair sampleBiased Eq where
  s₀ := ()
  s₀' := ()
  deficit := by
    simpa only [sampleFair, sampleBiased, Weight.pure_bind] using fair_biased_cert

theorem sampling_spec_refuted :
    ¬ quadSem sampleFair sampleBiased (exactly (Weight.pure ()) (Weight.pure ())) (couple Eq) :=
  sampling_bug.refutes (exactly_self _ _)

end

end RelOL.Prob.CertificateExamples
