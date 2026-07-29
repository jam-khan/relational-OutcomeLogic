import RelationalOutcomeLogic.Rules
import RelationalOutcomeLogic.Unary.Triple

/-!
# Unary Outcome Logic is the one-sided degeneration of RelOL

`embedU` reads a unary assertion as a relational one that ignores the (trivial)
second side. Under this embedding:

* `triple_iff_quadSem` — the unary OL triple **is** a relational quadruple with
  the identity lift on a `Unit` carrier as its second side; an exact iff, no
  side conditions.
* `embedU_oplus` — the embedding maps `⊕` to `⊕`. The iff direction needs the
  overlap-friendly `⊕`: the trivial side self-splits `m' = m' ∪ m'`.
* The unary rules (`Conseq`, `Seq`, `Split`, `Choice`) re-derive from the
  relational rules through the embedding — subsumption at the rule level, not
  just the judgment level.

Note the embedding is at the *assertion* level: `embedU (atomU p)` is not the
relational `atom` (which would demand nonemptiness of the trivial side too),
and does not need to be — the iffs below are exact as stated.
-/

namespace RelOL

open OL

variable {α : Type*}

/-- Embed a unary assertion as a relational assertion over a trivial second
carrier. -/
def embedU (P : OL.Assn α) : RAssn α Unit := fun m _ => P m

/-- **OL subsumption, judgment level**: the unary triple is exactly the
relational quadruple whose second side is the identity lift on the trivial
carrier. -/
theorem triple_iff_quadSem {P Q : OL.Assn State} {c : Cmd} :
    OL.triple P c Q ↔ quadSem (semLift c) id (embedU P) (embedU Q) :=
  ⟨fun h m _ hm => h m hm, fun h m hm => h m ∅ hm⟩

/-- The embedding maps unary `⊕` to relational `⊕` — exactly. The backward
direction is where the overlap-friendly `⊕` earns its keep: the trivial side
splits as `m' = m' ∪ m'`. -/
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

/-! ## Rule-level subsumption

Each unary OL rule is an instance of its relational counterpart. -/

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

/-- Unary `Split` from relational `Split` (union-preservation of the identity
lift is definitional). -/
theorem triple_split_via_relational {P₁ P₂ Q₁ Q₂ : OL.Assn State} {c : Cmd}
    (h₁ : OL.triple P₁ c Q₁) (h₂ : OL.triple P₂ c Q₂) :
    OL.triple (oplusU P₁ P₂) c (oplusU Q₁ Q₂) := by
  rw [triple_iff_quadSem] at h₁ h₂ ⊢
  rw [embedU_oplus, embedU_oplus]
  exact quadSem_split (semLift_union c) (fun _ _ => rfl) h₁ h₂

/-- Unary `Choice` (the OL `Plus` rule) from the one-sided relational Choice:
the trivial side is passive and self-splits — the same mechanism as
`quad_choice_left`. -/
theorem triple_choice_via_relational {P Q₁ Q₂ : OL.Assn State} {c₁ c₂ : Cmd}
    (h₁ : OL.triple P c₁ Q₁) (h₂ : OL.triple P c₂ Q₂) :
    OL.triple P (.choice c₁ c₂) (oplusU Q₁ Q₂) := by
  rw [triple_iff_quadSem] at h₁ h₂ ⊢
  intro m m' hm
  rw [semLift_choice, embedU_oplus]
  have := oplus_intro (P := embedU Q₁) (Q := embedU Q₂) (h₁ m m' hm) (h₂ m m' hm)
  rwa [Set.union_self] at this

end RelOL
