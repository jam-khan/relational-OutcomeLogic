import RelationalOutcomeLogic.Prob.Logic.Rules

/-!
# One-sided exact relational reasoning

Coupling against a point mass requires total mass one on the advancing side.
The one-sided loop rules therefore require losslessness of the whole loop on the
states covered by the precondition. Losslessness of its body alone is insufficient.
-/

namespace RelOL.Prob

variable {α β : Type*}

/-- The command terminates with total mass one on the specified starting states. -/
def LosslessOn (P : α → Prop) (c : Cmd α) : Prop :=
  ∀ a, P a → Weight.IsProbability (sem c a)

/-- Swapping the programs swaps the relation on both sides of the judgment. -/
theorem quad_couple_symm {R S : α → β → Prop} {c : Cmd α} {d : Cmd β}
    (h : quad (couple R) c d (couple S)) :
    quad (couple (fun b a => R a b)) d c (couple (fun b a => S a b)) :=
  fun μ ν hμν => (h ν μ hμν.swap).swap

/-- A left-only loop must preserve the relation and be lossless on relevant starts. -/
theorem quad_couple_while_left {R : α → β → Prop} (g : α → Prop) {c : Cmd α}
    (hbody : quad (couple (fun a b => R a b ∧ g a)) c .skip (couple R))
    (hloss : LosslessOn (fun a => ∃ b, R a b) (.while g c)) :
    quad (couple R) (.while g c) .skip (couple (fun a b => R a b ∧ ¬g a)) := by
  apply quad_couple_of_pointwise
  intro a b hab
  apply Coupled.pure_right_iff.mpr
  refine ⟨hloss a ⟨b, hab⟩, ?_⟩
  intro t ht
  apply loopSem_support_invariant g (sem c) (fun x => R x b) ?_ a hab t ht
  intro x hxb hg y hy
  have hc : Coupled R (sem c x) (Weight.pure b) := by
    simpa only [semLift_pure, sem_skip, couple] using
      hbody (Weight.pure x) (Weight.pure b) (Coupled.pure ⟨hxb, hg⟩)
  exact (Coupled.pure_right_iff.mp hc).2 y hy

/-- The symmetric one-sided loop rule, with losslessness only on its relevant starts. -/
theorem quad_couple_while_right {R : α → β → Prop} (g : β → Prop) {d : Cmd β}
    (hbody : quad (couple (fun a b => R a b ∧ g b)) .skip d (couple R))
    (hloss : LosslessOn (fun b => ∃ a, R a b) (.while g d)) :
    quad (couple R) .skip (.while g d) (couple (fun a b => R a b ∧ ¬g b)) :=
  quad_couple_symm (quad_couple_while_left g (quad_couple_symm hbody) hloss)

end RelOL.Prob
