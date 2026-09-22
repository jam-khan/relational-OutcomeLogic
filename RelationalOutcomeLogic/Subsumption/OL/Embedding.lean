import RelationalOutcomeLogic.Set.Rules
import RelationalOutcomeLogic.Subsumption.OL.Judgment

/-! # Unary Outcome Logic is the one-sided degeneration of RelOL -/

namespace RelOL

open OL

variable {α : Type*}

/-- Embed a unary assertion as a relational assertion over a trivial second carrier. -/
def embedU (P : OL.Assn α) : RAssn α Unit := fun m _ => P m

/-- OL subsumption, judgment level. -/
theorem triple_iff_quadSem {P Q : OL.Assn State} {c : Cmd} :
    OL.triple P c Q ↔ quadSem (semLift c) id (embedU P) (embedU Q) :=
  ⟨fun h m _ hm => h m hm, fun h m hm => h m ∅ hm⟩

/-- The embedding maps unary `⊕` to relational `⊕` — exactly. -/
theorem embedU_oplus (P Q : OL.Assn α) :
    embedU (oplusU P Q) = (embedU P ⊕ₒ embedU Q) := by
  funext m m'
  apply propext
  constructor
  · rintro ⟨m₁, m₂, rfl, hP, hQ⟩
    exact ⟨m₁, m₂, m', m', rfl, (Set.union_self m').symm, hP, hQ⟩
  · rintro ⟨m₁, m₂, m₁', m₂', rfl, -, hP, hQ⟩
    exact ⟨m₁, m₂, rfl, hP, hQ⟩

theorem embedU_entail {P Q : OL.Assn α} (h : ∀ m, P m → Q m) :
    entail (embedU P) (embedU Q) :=
  fun m _ hm => h m hm

/-! ## Rule-level subsumption -/

/-- Unary `Conseq` from relational `Conseq`. -/
theorem triple_conseq_via_relational {P P' Q Q' : OL.Assn State} {c : Cmd}
    (hP : ∀ m, P' m → P m) (h : OL.triple P c Q) (hQ : ∀ m, Q m → Q' m) :
    OL.triple P' c Q' := by
  rw [triple_iff_quadSem] at h ⊢
  exact quadSem_conseq (embedU_entail hP) h (embedU_entail hQ)

/-- Unary `Seq` from relational composition. -/
theorem triple_seq_via_relational {P Q R : OL.Assn State} {c₁ c₂ : Cmd}
    (h₁ : OL.triple P c₁ Q) (h₂ : OL.triple Q c₂ R) :
    OL.triple P (.seq c₁ c₂) R := by
  rw [triple_iff_quadSem] at h₁ h₂ ⊢
  intro m m' hm
  rw [semLift_seq]
  exact h₂ (semLift c₁ m) m' (h₁ m m' hm)

/-- Unary `Split` from relational `Split`. -/
theorem triple_split_via_relational {P₁ P₂ Q₁ Q₂ : OL.Assn State} {c : Cmd}
    (h₁ : OL.triple P₁ c Q₁) (h₂ : OL.triple P₂ c Q₂) :
    OL.triple (oplusU P₁ P₂) c (oplusU Q₁ Q₂) := by
  rw [triple_iff_quadSem] at h₁ h₂ ⊢
  rw [embedU_oplus, embedU_oplus]
  exact quadSem_split (semLift_union c) (fun _ _ => rfl) h₁ h₂

/-- Unary `Choice` (the OL `Plus` rule) from the one-sided relational Choice. -/
theorem triple_choice_via_relational {P Q₁ Q₂ : OL.Assn State} {c₁ c₂ : Cmd}
    (h₁ : OL.triple P c₁ Q₁) (h₂ : OL.triple P c₂ Q₂) :
    OL.triple P (.choice c₁ c₂) (oplusU Q₁ Q₂) := by
  rw [triple_iff_quadSem] at h₁ h₂ ⊢
  intro m m' hm
  rw [semLift_choice, embedU_oplus]
  have := oplus_intro (P := embedU Q₁) (Q := embedU Q₂) (h₁ m m' hm) (h₂ m m' hm)
  rwa [Set.union_self] at this

end RelOL
