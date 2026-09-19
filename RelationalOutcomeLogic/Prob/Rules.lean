import RelationalOutcomeLogic.Prob.Lang
import RelationalOutcomeLogic.Prob.LoopCoupling
import RelationalOutcomeLogic.Prob.CouplingAssertions

/-!
# Sound rules for probabilistic commands

The structural rules act on arbitrary weighted assertions. The coupling rules use
exact joint marginals, including for synchronous loops with possible divergence.
Sampling carries its normalization proof in the command itself.
-/

namespace RelOL.Prob

open scoped ENNReal

variable {α β : Type*}

theorem quad_skip (P : RAssn α β) : quad P .skip .skip P := by
  intro μ ν h
  simpa only [semLift_skip] using h

theorem quad_consequence {P P' Q Q' : RAssn α β} {c : Cmd α} {d : Cmd β}
    (hP : entail P' P) (h : quad P c d Q) (hQ : entail Q Q') : quad P' c d Q' :=
  fun μ ν hp => hQ _ _ (h μ ν (hP μ ν hp))

theorem quad_seq {P Q S : RAssn α β} {c₁ c₂ : Cmd α} {d₁ d₂ : Cmd β}
    (h₁ : quad P c₁ d₁ Q) (h₂ : quad Q c₂ d₂ S) :
    quad P (.seq c₁ c₂) (.seq d₁ d₂) S := by
  intro μ ν hp
  simpa only [semLift_seq] using h₂ _ _ (h₁ μ ν hp)

/-- Each additive piece is executed once on each side. -/
theorem quad_oplus {P₁ P₂ Q₁ Q₂ : RAssn α β} {c : Cmd α} {d : Cmd β}
    (h₁ : quad P₁ c d Q₁) (h₂ : quad P₂ c d Q₂) :
    quad (oplus P₁ P₂) c d (oplus Q₁ Q₂) := by
  rintro μ ν ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, hp₁, hp₂⟩
  simpa only [semLift_add] using oplus_intro (h₁ _ _ hp₁) (h₂ _ _ hp₂)

theorem quad_scale (r : ℝ≥0∞) {P Q : RAssn α β} {c : Cmd α} {d : Cmd β}
    (h : quad P c d Q) : quad (scale r P) c d (scale r Q) := by
  rintro μ ν ⟨μ₀, ν₀, rfl, rfl, hp⟩
  simpa only [semLift_smul] using scale_intro r (h _ _ hp)

/-- Pointwise continuation joints lift to every coupled pair of input weights. -/
theorem quad_couple_of_pointwise {R S : α → β → Prop} {c : Cmd α} {d : Cmd β}
    (h : ∀ a b, R a b → Coupled S (sem c a) (sem d b)) :
    quad (couple R) c d (couple S) :=
  fun _ _ hμν => hμν.bind (sem c) (sem d) h

theorem quad_couple_assign {R S : α → β → Prop} (f : α → α) (g : β → β)
    (h : ∀ a b, R a b → S (f a) (g b)) :
    quad (couple R) (.assign f) (.assign g) (couple S) := by
  apply quad_couple_of_pointwise
  intro a b hab
  exact Coupled.pure (h a b hab)

theorem quad_couple_sample {R S : α → β → Prop}
    (k : α → Weight α) (l : β → Weight β)
    (hk : ∀ a, Weight.IsProbability (k a)) (hl : ∀ b, Weight.IsProbability (l b))
    (h : ∀ a b, R a b → Coupled S (k a) (l b)) :
    quad (couple R) (.sample k hk) (.sample l hl) (couple S) :=
  quad_couple_of_pointwise h

/-- Synchronized guards choose the corresponding proved branch. -/
theorem quad_couple_ite {R S : α → β → Prop} (g : α → Prop) (h : β → Prop)
    {c₁ c₂ : Cmd α} {d₁ d₂ : Cmd β}
    (hsync : ∀ a b, R a b → (g a ↔ h b))
    (hthen : quad (couple (fun a b => R a b ∧ g a)) c₁ d₁ (couple S))
    (helse : quad (couple (fun a b => R a b ∧ ¬ g a)) c₂ d₂ (couple S)) :
    quad (couple R) (.ite g c₁ c₂) (.ite h d₁ d₂) (couple S) := by
  apply quad_couple_of_pointwise
  intro a b hab
  by_cases hg : g a
  · have hb := (hsync a b hab).mp hg
    rw [sem_ite_pos hg, sem_ite_pos hb]
    simpa only [semLift_pure, couple] using
      hthen _ _ (Coupled.pure (show R a b ∧ g a from ⟨hab, hg⟩))
  · have hb : ¬ h b := fun hh => hg ((hsync a b hab).mpr hh)
    rw [sem_ite_neg hg, sem_ite_neg hb]
    simpa only [semLift_pure, couple] using
      helse _ _ (Coupled.pure (show R a b ∧ ¬ g a from ⟨hab, hg⟩))

/-- A coherent joint loop proves exact coupling, without assuming either loop terminates. -/
theorem quad_couple_while {R : α → β → Prop} (g : α → Prop) (h : β → Prop)
    {c : Cmd α} {d : Cmd β}
    (hsync : ∀ a b, R a b → (g a ↔ h b))
    (hbody : quad (couple (fun a b => R a b ∧ g a)) c d (couple R)) :
    quad (couple R) (.while g c) (.while h d)
      (couple (fun a b => R a b ∧ ¬ g a ∧ ¬ h b)) := by
  apply quad_couple_of_pointwise
  intro a b hab
  apply coupled_loop g h (sem c) (sem d) hsync ?_ hab
  intro x y hxy hg
  simpa only [semLift_pure, couple] using
    hbody _ _ (Coupled.pure (show R x y ∧ g x from ⟨hxy, hg⟩))

end RelOL.Prob
