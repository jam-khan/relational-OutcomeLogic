import RelationalOutcomeLogic.Prob.Rules
import RelationalOutcomeLogic.Prob.BugCert

/-!
# Exact-coupling pRHL as a fragment of weighted RelOL

The pointwise judgment relates the terminating output weights by an exact supported
joint. It allows divergence but requires equal termination masses. Its semantic
embedding into weighted RelOL transports the named rules and quantitative refutations.

This file proves a semantic equivalence and admissible rules. It does not define a
derivation datatype or claim an embedding of a procedure/module language.
-/

namespace RelOL.Prob

variable {α β γ δ : Type*}

/-- Pointwise relational correctness for arbitrary discrete weighted kernels. -/
def prhlSem (R : α → β → Prop) (k : α → Weight γ) (l : β → Weight δ)
    (S : γ → δ → Prop) : Prop :=
  ∀ a b, R a b → Coupled S (k a) (l b)

/-- Exact-subdistribution pRHL for the probabilistic while-language. -/
def prhl (R : α → β → Prop) (c : Cmd α) (d : Cmd β) (S : α → β → Prop) : Prop :=
  prhlSem R (sem c) (sem d) S

/-- Pointwise kernel couplings are equivalent to preserving coupling assertions on weights. -/
theorem prhlSem_iff_quadSem {R : α → β → Prop} {k : α → Weight γ}
    {l : β → Weight δ} {S : γ → δ → Prop} :
    prhlSem R k l S ↔
      quadSem (fun μ => Weight.bind μ k) (fun ν => Weight.bind ν l) (couple R) (couple S) := by
  constructor
  · intro h μ ν hμν
    exact hμν.bind k l h
  · intro h a b hab
    simpa only [Weight.pure_bind, couple] using
      h (Weight.pure a) (Weight.pure b) (Coupled.pure hab)

/-- The pRHL judgment is exactly the coupling-assertion fragment of weighted RelOL. -/
theorem prhl_iff_quad {R S : α → β → Prop} {c : Cmd α} {d : Cmd β} :
    prhl R c d S ↔ quad (couple R) c d (couple S) :=
  prhlSem_iff_quadSem

theorem prhl_skip (R : α → β → Prop) : prhl R .skip .skip R := by
  rw [prhl_iff_quad]
  exact quad_skip (couple R)

theorem prhl_consequence {R R' S S' : α → β → Prop} {c : Cmd α} {d : Cmd β}
    (hpre : ∀ a b, R' a b → R a b) (h : prhl R c d S)
    (hpost : ∀ a b, S a b → S' a b) : prhl R' c d S' := by
  rw [prhl_iff_quad] at h ⊢
  exact quad_consequence (couple_mono hpre) h (couple_mono hpost)

theorem prhl_assign {R S : α → β → Prop} (f : α → α) (g : β → β)
    (h : ∀ a b, R a b → S (f a) (g b)) :
    prhl R (.assign f) (.assign g) S := by
  rw [prhl_iff_quad]
  exact quad_couple_assign f g h

theorem prhl_sample {R S : α → β → Prop} (k : α → Weight α) (l : β → Weight β)
    (hk : ∀ a, Weight.IsProbability (k a)) (hl : ∀ b, Weight.IsProbability (l b))
    (h : ∀ a b, R a b → Coupled S (k a) (l b)) :
    prhl R (.sample k hk) (.sample l hl) S := by
  rw [prhl_iff_quad]
  exact quad_couple_sample k l hk hl h

theorem prhl_seq {R M S : α → β → Prop} {c₁ c₂ : Cmd α} {d₁ d₂ : Cmd β}
    (h₁ : prhl R c₁ d₁ M) (h₂ : prhl M c₂ d₂ S) :
    prhl R (.seq c₁ c₂) (.seq d₁ d₂) S := by
  rw [prhl_iff_quad] at h₁ h₂ ⊢
  exact quad_seq h₁ h₂

theorem prhl_ite {R S : α → β → Prop} (g : α → Prop) (h : β → Prop)
    {c₁ c₂ : Cmd α} {d₁ d₂ : Cmd β}
    (hsync : ∀ a b, R a b → (g a ↔ h b))
    (hthen : prhl (fun a b => R a b ∧ g a) c₁ d₁ S)
    (helse : prhl (fun a b => R a b ∧ ¬ g a) c₂ d₂ S) :
    prhl R (.ite g c₁ c₂) (.ite h d₁ d₂) S := by
  rw [prhl_iff_quad] at hthen helse ⊢
  exact quad_couple_ite g h hsync hthen helse

/-- Synchronous loops retain the invariant and both exit conditions, including divergence. -/
theorem prhl_while {R : α → β → Prop} (g : α → Prop) (h : β → Prop)
    {c : Cmd α} {d : Cmd β}
    (hsync : ∀ a b, R a b → (g a ↔ h b))
    (hbody : prhl (fun a b => R a b ∧ g a) c d R) :
    prhl R (.while g c) (.while h d) (fun a b => R a b ∧ ¬ g a ∧ ¬ h b) := by
  rw [prhl_iff_quad] at hbody ⊢
  exact quad_couple_while g h hsync hbody

/-- Split the input-state proof by an arbitrary predicate on the pair of states. -/
theorem prhl_case {R S : α → β → Prop} {c : Cmd α} {d : Cmd β}
    (B : α → β → Prop)
    (hpos : prhl (fun a b => R a b ∧ B a b) c d S)
    (hneg : prhl (fun a b => R a b ∧ ¬ B a b) c d S) : prhl R c d S := by
  rw [prhl_iff_quad]
  apply quad_couple_of_pointwise
  intro a b hab
  by_cases hB : B a b
  · exact hpos a b ⟨hab, hB⟩
  · exact hneg a b ⟨hab, hB⟩

theorem prhl_false (c : Cmd α) (d : Cmd β) (S : α → β → Prop) :
    prhl (fun _ _ => False) c d S := by
  rw [prhl_iff_quad]
  exact quad_couple_of_pointwise fun _ _ h => h.elim

/-- Replacing either command by an equal state-indexed semantics preserves the judgment. -/
theorem prhl_congr {R S : α → β → Prop} {c c' : Cmd α} {d d' : Cmd β}
    (hc : sem c = sem c') (hd : sem d = sem d') :
    prhl R c d S ↔ prhl R c' d' S := by
  unfold prhl
  rw [hc, hd]

/-- A certified deficit at a permitted input pair refutes the pRHL specification. -/
theorem MassDeficitCert.refutes_prhl {R S : α → β → Prop} {c : Cmd α} {d : Cmd β}
    {a : α} {b : β} (C : MassDeficitCert S (sem c a) (sem d b)) (hR : R a b) :
    ¬ prhl R c d S := fun h => C.refutes (h a b hR)

/-- A program-level certificate also refutes the corresponding pRHL judgment. -/
theorem BugCert.refutes_prhl {R S : α → β → Prop} {c : Cmd α} {d : Cmd β}
    (C : BugCert (semLift c) (semLift d) S) (hR : R C.s₀ C.s₀') : ¬ prhl R c d S := by
  intro h
  exact C.refutes (P := couple R) (Coupled.pure hR) (prhl_iff_quad.mp h)

end RelOL.Prob
