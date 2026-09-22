import RelationalOutcomeLogic.Algebra.ENNReal.Limits
import RelationalOutcomeLogic.Prob.Coupling.Basic

/-!
# Observations of weighted outcomes and couplings

Deterministic observations preserve total weight and transport exact couplings.
These language-independent laws support loop alignment without depending on
program assertions or refutation certificates.
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

end RelOL.Prob
