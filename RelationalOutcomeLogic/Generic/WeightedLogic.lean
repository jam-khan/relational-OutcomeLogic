import RelationalOutcomeLogic.Algebra.WeightedCoupling
import RelationalOutcomeLogic.Algebra.WeightedModel
import RelationalOutcomeLogic.Generic.Rules

/-!
# Relational coupling rules over a summation semiring

Statewise relational judgments embed exactly into the common outcome judgment.
The scalar need not be probabilistic or have commutative multiplication. Probability
normalization is a separate property of particular kernels and scalar instances.
-/

universe u v

namespace RelOL.Generic

open Algebra

variable {K : Type v} [Semiring K] [SummationSemiring.{u} K]
variable {α β γ δ ε ζ : Type u}

/-- An exact coupling assertion, including its joint's support restriction. -/
def couple (R : α → β → Prop) : RAssn (Weighted.Weight K) α β := Weighted.Coupled R

/-- The statewise coupling judgment underlying semantic probabilistic RHL. -/
def prhl (R : α → β → Prop) (k : α → Weighted.Weight K γ) (l : β → Weighted.Weight K δ)
    (S : γ → δ → Prop) : Prop := ∀ a b, R a b → Weighted.Coupled S (k a) (l b)

theorem couple_mono {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    entail (couple (K := K) R) (couple S) := fun _ _ hc => hc.mono h

theorem couple_split (R : α → β → Prop) :
    entail (oplus (couple (K := K) R) (couple R)) (couple R) := by
  rintro _ _ ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁, h₂⟩
  exact Weighted.Coupled.add h₁ h₂

/-- Exact equivalence, not merely one sound direction of an embedding. -/
theorem prhl_iff_quad {R : α → β → Prop} {S : γ → δ → Prop}
    {k : α → Weighted.Weight K γ} {l : β → Weighted.Weight K δ} :
    prhl R k l S ↔ quad (couple R) k l (couple S) := by
  constructor
  · intro h μ ν hμν
    exact Weighted.Coupled.bind hμν k l h
  · intro h a b hab
    have hout := h (Weighted.pure a) (Weighted.pure b) (Weighted.Coupled.pure hab)
    simpa only [couple, OutcomeModel.bind, Weighted.outcomeModel, Weighted.pure_bind] using hout

theorem prhl_skip (R : α → β → Prop) : prhl (K := K) R Weighted.pure Weighted.pure R :=
  fun _ _ h => Weighted.Coupled.pure h

theorem prhl_consequence {R R' : α → β → Prop} {S S' : γ → δ → Prop}
    {k : α → Weighted.Weight K γ} {l : β → Weighted.Weight K δ}
    (hR : ∀ a b, R' a b → R a b) (h : prhl R k l S)
    (hS : ∀ c d, S c d → S' c d) : prhl R' k l S' :=
  fun a b hab => (h a b (hR a b hab)).mono hS

theorem prhl_seq {R : α → β → Prop} {S : γ → δ → Prop} {T : ε → ζ → Prop}
    {k : α → Weighted.Weight K γ} {l : β → Weighted.Weight K δ}
    {k' : γ → Weighted.Weight K ε} {l' : δ → Weighted.Weight K ζ}
    (h : prhl R k l S) (h' : prhl S k' l' T) :
    prhl R (fun a => Weighted.bind (k a) k') (fun b => Weighted.bind (l b) l') T :=
  fun a b hab => (h a b hab).bind k' l' h'

theorem quad_couple {R : α → β → Prop} {S : γ → δ → Prop}
    {k : α → Weighted.Weight K γ} {l : β → Weighted.Weight K δ}
    (h : ∀ a b, R a b → Weighted.Coupled S (k a) (l b)) :
    quad (couple R) k l (couple S) := prhl_iff_quad.mp h

/-- Statewise branch couplings combine through the common additive splitting rule. -/
theorem quad_couple_choice {R : α → β → Prop} {S T : γ → δ → Prop}
    {k k' : α → Weighted.Weight K γ} {l l' : β → Weighted.Weight K δ}
    (h : prhl R k l S) (h' : prhl R k' l' T) :
    quad (couple R) (fun a => k a + k' a) (fun b => l b + l' b)
      (oplus (couple S) (couple T)) :=
  quad_choice (prhl_iff_quad.mp h) (prhl_iff_quad.mp h')

end RelOL.Generic
