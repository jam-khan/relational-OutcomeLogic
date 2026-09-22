import RelationalOutcomeLogic.Algebra.WeightOrder
import RelationalOutcomeLogic.Prob.BugCert

/-!
# Observations of weighted program outcomes

Deterministic observations preserve all mass and transport exact couplings. This
module connects internal relational outcome contracts with observable correctness
and quantitative bug certificates, independently of the command language.
-/

namespace RelOL.Prob

open scoped ENNReal

variable {α β γ δ σ τ : Type*}

/-- Push a discrete weight through a deterministic observation. -/
noncomputable def pushforward (π : σ → τ) (μ : Weight σ) : Weight τ :=
  Weight.bind μ (fun s => Weight.pure (π s))

@[simp] theorem pushforward_zero (π : σ → τ) : pushforward π 0 = 0 :=
  Weight.zero_bind _

@[simp] theorem pushforward_pure (π : σ → τ) (s : σ) :
    pushforward π (Weight.pure s) = Weight.pure (π s) := Weight.pure_bind _ _

theorem pushforward_add (π : σ → τ) (μ ν : Weight σ) :
    pushforward π (μ + ν) = pushforward π μ + pushforward π ν :=
  Weight.add_bind _ _ _

theorem pushforward_smul (π : σ → τ) (r : ℝ≥0∞) (μ : Weight σ) :
    pushforward π (r • μ) = r • pushforward π μ :=
  Weight.smul_bind _ _ _

/-- Forgetting internal state preserves total mass, including divergence and infinite weights. -/
@[simp] theorem mass_pushforward (π : σ → τ) (μ : Weight σ) :
    Weight.mass (pushforward π μ) = Weight.mass μ :=
  Weight.mass_bind_of_isProbability μ _ (fun _ _ => Weight.isProbability_pure _)

theorem pushforward_bind (π : σ → τ) (μ : Weight α) (K : α → Weight σ) :
    pushforward π (Weight.bind μ K) = Weight.bind μ (fun s => pushforward π (K s)) :=
  Weight.bind_assoc _ _ _

theorem bind_pushforward (π : σ → τ) (μ : Weight σ) (f : τ → Weight β) :
    Weight.bind (pushforward π μ) f = Weight.bind μ (fun s => f (π s)) := by
  simp only [pushforward, Weight.bind_assoc, Weight.pure_bind]

theorem pushforward_iSup (π : σ → τ) (μ : ℕ → Weight σ) (hμ : Monotone μ) :
    pushforward π (⨆ n, μ n) = ⨆ n, pushforward π (μ n) :=
  Weight.bind_iSup_left μ hμ _

@[simp] theorem pushforward_fst (J : Weight (α × β)) :
    pushforward Prod.fst J = margL J := by
  rw [pushforward, bind_fst, Weight.bind_pure]

@[simp] theorem pushforward_snd (J : Weight (α × β)) :
    pushforward Prod.snd J = margR J := by
  rw [pushforward, bind_snd, Weight.bind_pure]

/-- Related internal states yield a coupling of observations through possibly different maps. -/
theorem Coupled.pushforward {R : α → β → Prop} {S : γ → δ → Prop}
    {μ : Weight α} {ν : Weight β} (h : Coupled R μ ν)
    (f : α → γ) (g : β → δ) (hRS : ∀ a b, R a b → S (f a) (g b)) :
    Coupled S (pushforward f μ) (pushforward g ν) :=
  h.bind (fun a => Weight.pure (f a)) (fun b => Weight.pure (g b))
    (fun a b hab => Coupled.pure (hRS a b hab))

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
