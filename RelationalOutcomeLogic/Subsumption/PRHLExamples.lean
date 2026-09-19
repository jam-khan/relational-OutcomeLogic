import RelationalOutcomeLogic.Subsumption.PRHL
import RelationalOutcomeLogic.Subsumption.PRHLOneSided
import RelationalOutcomeLogic.Prob.LoopExamples
import RelationalOutcomeLogic.Prob.CertificateExamples

/-!
# Examples derived through the probabilistic relational rules

The synchronous example uses sampling and while rules before crossing the weighted
embedding. One-sided retry loops rely on proved losslessness of the entire loop;
a divergent skip loop shows why normalization of the body alone is insufficient.
Probability disagreement is refuted with an actual finite mass-deficit certificate.
-/

namespace RelOL.Prob.PRHLExamples

open scoped ENNReal
open Examples LoopExamples

noncomputable section

/-- A derivation through the pRHL sampling and synchronous while rules. -/
theorem retry_opposite_prhl :
    prhl (fun a b : Bool => a = !b) retryTrue retryFalse
      (fun a b => a = !b ∧ a ≠ true ∧ b ≠ false) := by
  apply prhl_while
  · intro a b hab
    cases a <;> cases b <;> simp_all
  · apply prhl_sample
    intro a b _
    exact fair_opposite_coupling

/-- The new derivation embeds as a judgment over arbitrary coupled input weights. -/
theorem retry_opposite_weighted :
    quad (couple (fun a b : Bool => a = !b)) retryTrue retryFalse
      (couple (fun a b => a = !b ∧ a ≠ true ∧ b ≠ false)) :=
  prhl_iff_quad.mp retry_opposite_prhl

/-- The client is almost surely terminating but genuinely requires the infinite limit. -/
theorem retry_unbounded :
    Weight.IsProbability (sem retryTrue true) ∧
      ∀ n, Weight.mass (loopIter (fun s => s = true) (sem coin) n true) < 1 :=
  ⟨geometricLoop_isProbability, geometricLoop_iter_mass_lt_one⟩

/-- Relating a normalized fair sample to a passive unit state uses both probability branches. -/
theorem fair_to_unit (b : Unit) :
    Coupled (fun _ : Bool => fun _ : Unit => True) fair (Weight.pure b) := by
  have h₀ := (Coupled.pure (R := fun _ : Bool => fun _ : Unit => True)
    (a := false) (b := b) trivial).smul (1 / 2)
  have h₁ := (Coupled.pure (R := fun _ : Bool => fun _ : Unit => True)
    (a := true) (b := b) trivial).smul (1 / 2)
  have h := h₀.add h₁
  rw [← add_smul, ENNReal.add_halves, one_smul] at h
  exact h

/-- Losslessness is established for every starting state, not just the loop body. -/
theorem retryTrue_lossless : LosslessOn (fun _ => True) retryTrue := by
  intro s _
  cases s
  · change Weight.IsProbability (geometricLoop false)
    rw [geometricLoop_false]
    exact Weight.isProbability_pure false
  · exact geometricLoop_isProbability

/-- A loop can take arbitrarily many steps while the other program remains at skip. -/
theorem retry_skip_prhl :
    prhl (fun _ : Bool => fun _ : Unit => True) retryTrue .skip
      (fun a _ => a = false) := by
  have hbody : prhl (fun a : Bool => fun _ : Unit => True ∧ a = true)
      coin .skip (fun _ _ => True) := by
    exact prhl_sample_left (fun _ => fair) (fun _ => fair_isProbability)
      (fun _ _ _ _ _ => trivial)
  have hloss : LosslessOn (fun _ : Bool => ∃ _ : Unit, True) retryTrue :=
    fun s _ => retryTrue_lossless s trivial
  have hloop := prhl_while_left (fun s : Bool => s = true) hbody hloss
  apply prhl_consequence (fun _ _ h => h) hloop
  intro a _ ha
  cases a
  · rfl
  · exact (ha.2 rfl).elim

/-- The mirror rule supports the same unbounded computation on the right. -/
theorem skip_retry_prhl :
    prhl (fun _ : Unit => fun _ : Bool => True) .skip retryTrue
      (fun _ b => b = false) := by
  have hbody : prhl (fun _ : Unit => fun b : Bool => True ∧ b = true)
      .skip coin (fun _ _ => True) := by
    exact prhl_sample_right (fun _ => fair) (fun _ => fair_isProbability)
      (fun _ _ _ _ _ => trivial)
  have hloss : LosslessOn (fun _ : Bool => ∃ _ : Unit, True) retryTrue :=
    fun s _ => retryTrue_lossless s trivial
  have hloop := prhl_while_right (fun s : Bool => s = true) hbody hloss
  apply prhl_consequence (fun _ _ h => h) hloop
  intro _ b hb
  cases b
  · rfl
  · exact (hb.2 rfl).elim

/-- Sampling and deterministic assignment compose through the pRHL rules. -/
theorem sample_then_negate_prhl :
    prhl (fun _ _ : Bool => True) (.seq coin (.assign id))
      (.seq coin (.assign fun b => !b)) Eq := by
  have hsample : prhl (fun _ _ : Bool => True) coin coin (fun a b => a = !b) := by
    apply prhl_sample
    intro _ _ _
    exact fair_opposite_coupling
  exact prhl_seq hsample (prhl_assign id (fun b => !b) (fun _ _ h => h))

/-- A mass-one invariant-preserving body can nevertheless diverge when repeated. -/
theorem skip_body_preserves_true :
    prhl (fun _ _ : Unit => True) .skip .skip (fun _ _ => True) :=
  prhl_skip _

theorem skip_body_lossless : LosslessOn (fun _ : Unit => True) .skip :=
  fun s _ => Weight.isProbability_pure s

/-- Dropping whole-loop losslessness is unsound even with the weakest postrelation. -/
theorem spin_skip_true_refuted :
    ¬ prhl (fun _ _ : Unit => True) spin .skip (fun _ _ => True) := by
  intro h
  have hm := (h () () trivial).mass_eq
  simp only [spin_result, sem_skip, Weight.mass_zero, Weight.mass_pure] at hm
  exact zero_ne_one hm

/-- A legal normalized primitive whose probabilities disagree with the fair sample. -/
def biasedCoin : Cmd Bool := .sample (fun _ => biased) (fun _ => biased_isProbability)

/-- The pRHL rejection is obtained from the existing checked false-event deficit. -/
theorem fair_biased_prhl_refuted :
    ¬ prhl (fun _ _ : Bool => True) coin biasedCoin Eq := by
  have C : MassDeficitCert Eq (sem coin false) (sem biasedCoin false) :=
    CertificateExamples.fair_biased_cert
  exact C.refutes_prhl trivial

/-- A program-level certificate is indexed by the actual commands' lifted semantics. -/
def fair_biased_command_bug : BugCert (semLift coin) (semLift biasedCoin) Eq where
  s₀ := false
  s₀' := false
  deficit := by
    simpa only [semLift_pure, coin, biasedCoin, sem_sample] using
      CertificateExamples.fair_biased_cert

/-- The command-indexed certificate also refutes a specification with equal initial states. -/
theorem fair_biased_command_prhl_refuted : ¬ prhl Eq coin biasedCoin Eq :=
  fair_biased_command_bug.refutes_prhl rfl

end

end RelOL.Prob.PRHLExamples
