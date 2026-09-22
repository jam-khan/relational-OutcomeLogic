import RelationalOutcomeLogic.Subsumption.PRHL.Embedding
import RelationalOutcomeLogic.Prob.Logic.OneSided

/-!
# One-sided rules for exact-coupling pRHL

Assignments and normalized sampling can advance one program against skip.
Conditionals can select a branch on one side against an arbitrary other command.
A one-sided loop additionally needs whole-loop losslessness on the relevant initial
states; exact coupling with skip cannot discard termination mass.
-/

namespace RelOL.Prob

variable {α β : Type*}

theorem prhl_symm {R S : α → β → Prop} {c : Cmd α} {d : Cmd β}
    (h : prhl R c d S) : prhl (fun b a => R a b) d c (fun b a => S a b) := by
  rw [prhl_iff_quad] at h ⊢
  exact quad_couple_symm h

theorem prhl_assign_left {R S : α → β → Prop} (f : α → α)
    (h : ∀ a b, R a b → S (f a) b) : prhl R (.assign f) .skip S := by
  rw [prhl_iff_quad]
  apply quad_couple_of_pointwise
  intro a b hab
  exact Coupled.pure (h a b hab)

theorem prhl_assign_right {R S : α → β → Prop} (f : β → β)
    (h : ∀ a b, R a b → S a (f b)) : prhl R .skip (.assign f) S :=
  prhl_symm (prhl_assign_left f fun b a hab => h a b hab)

theorem prhl_sample_left {R S : α → β → Prop} (k : α → Weight α)
    (hk : ∀ a, Weight.IsProbability (k a))
    (h : ∀ a b, R a b → ∀ t ∈ Weight.support (k a), S t b) :
    prhl R (.sample k hk) .skip S := by
  rw [prhl_iff_quad]
  apply quad_couple_of_pointwise
  intro a b hab
  exact Coupled.pure_right_iff.mpr ⟨hk a, h a b hab⟩

theorem prhl_sample_right {R S : α → β → Prop} (k : β → Weight β)
    (hk : ∀ b, Weight.IsProbability (k b))
    (h : ∀ a b, R a b → ∀ t ∈ Weight.support (k b), S a t) :
    prhl R .skip (.sample k hk) S :=
  prhl_symm (prhl_sample_left k hk fun b a hab => h a b hab)

theorem prhl_ite_left {R S : α → β → Prop} (g : α → Prop)
    {c₁ c₂ : Cmd α} {d : Cmd β}
    (hthen : prhl (fun a b => R a b ∧ g a) c₁ d S)
    (helse : prhl (fun a b => R a b ∧ ¬g a) c₂ d S) :
    prhl R (.ite g c₁ c₂) d S := by
  rw [prhl_iff_quad]
  apply quad_couple_of_pointwise
  intro a b hab
  by_cases hg : g a
  · rw [sem_ite_pos hg]
    exact hthen a b ⟨hab, hg⟩
  · rw [sem_ite_neg hg]
    exact helse a b ⟨hab, hg⟩

theorem prhl_ite_right {R S : α → β → Prop} (g : β → Prop)
    {c : Cmd α} {d₁ d₂ : Cmd β}
    (hthen : prhl (fun a b => R a b ∧ g b) c d₁ S)
    (helse : prhl (fun a b => R a b ∧ ¬g b) c d₂ S) :
    prhl R c (.ite g d₁ d₂) S :=
  prhl_symm (prhl_ite_left g (prhl_symm hthen) (prhl_symm helse))

theorem prhl_while_left {R : α → β → Prop} (g : α → Prop) {c : Cmd α}
    (hbody : prhl (fun a b => R a b ∧ g a) c .skip R)
    (hloss : LosslessOn (fun a => ∃ b, R a b) (.while g c)) :
    prhl R (.while g c) .skip (fun a b => R a b ∧ ¬g a) := by
  rw [prhl_iff_quad] at hbody ⊢
  exact quad_couple_while_left g hbody hloss

theorem prhl_while_right {R : α → β → Prop} (g : β → Prop) {d : Cmd β}
    (hbody : prhl (fun a b => R a b ∧ g b) .skip d R)
    (hloss : LosslessOn (fun b => ∃ a, R a b) (.while g d)) :
    prhl R .skip (.while g d) (fun a b => R a b ∧ ¬g b) := by
  rw [prhl_iff_quad] at hbody ⊢
  exact quad_couple_while_right g hbody hloss

end RelOL.Prob
