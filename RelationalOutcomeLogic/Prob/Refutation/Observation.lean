import RelationalOutcomeLogic.Prob.Coupling.Observation
import RelationalOutcomeLogic.Prob.Refutation.Certificate

/-!
# Observed contracts and quantitative refutation

Transport an outcome judgment through deterministic observations, then use an
observed mass deficit to refute the original internal contract.
-/

namespace RelOL.Prob

variable {α β γ δ σ τ : Type*}

/-- Transport a complete outcome contract to its externally observed consequence. -/
theorem quadSem.observe {F : Weight α → Weight γ} {G : Weight β → Weight δ}
    {P : RAssn α β} {Q : RAssn γ δ} {S : RAssn σ τ}
    (h : quadSem F G P Q) (f : γ → σ) (g : δ → τ)
    (hQ : ∀ μ ν, Q μ ν → S (pushforward f μ) (pushforward g ν)) :
    quadSem (fun μ => pushforward f (F μ)) (fun ν => pushforward g (G ν)) P S :=
  fun μ ν hP => hQ _ _ (h μ ν hP)

/-- An observed deficit refutes any internal contract that requires the observed coupling. -/
theorem BugCert.refutes_of_observation
    {F : Weight α → Weight γ} {G : Weight β → Weight δ}
    {f : γ → σ} {g : δ → τ} {R : σ → τ → Prop}
    (C : BugCert (fun μ => pushforward f (F μ)) (fun ν => pushforward g (G ν)) R)
    {P : RAssn α β} {Q : RAssn γ δ}
    (hP : P (Weight.pure C.s₀) (Weight.pure C.s₀'))
    (hQ : ∀ μ ν, Q μ ν → Coupled R (pushforward f μ) (pushforward g ν)) :
    ¬ quadSem F G P Q := by
  intro h
  exact C.refutes hP (h.observe f g hQ)

end RelOL.Prob
