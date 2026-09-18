import RelationalOutcomeLogic.Kleisli

/-! # Unary outcome assertions (powerset instance) -/

namespace OL

open RelOL

variable {α : Type*}

def Assn (α : Type*) := Set α → Prop

/-- Atomic satisfaction: reachable, and every outcome satisfies `p`. -/
def atomU (p : α → Prop) : Assn α := fun m => m.Nonempty ∧ ∀ x ∈ m, p x

def oplusU (P Q : Assn α) : Assn α := fun m => ∃ m₁ m₂, m = m₁ ∪ m₂ ∧ P m₁ ∧ Q m₂

def topU : Assn α := fun _ => True

/-- Divergence: no outcomes. -/
def emptyU : Assn α := fun m => m = ∅

def entailsU (P Q : Assn α) : Prop := ∀ m, P m → Q m

scoped infixr:60 " ⊕ᵤ " => oplusU
scoped notation "⊤ᵤ" => topU
scoped notation "∅ᵤ" => emptyU
scoped infixr:25 " ⟹ᵤ " => entailsU

@[simp] theorem atomU_singleton {p : α → Prop} {x : α} : atomU p {x} ↔ p x := by
  simp [atomU]

theorem oplusU_intro {P Q : Assn α} {m₁ m₂ : Set α} (h₁ : P m₁) (h₂ : Q m₂) :
    (P ⊕ᵤ Q) (m₁ ∪ m₂) :=
  ⟨m₁, m₂, rfl, h₁, h₂⟩

theorem oplusU_left_top {P : Assn α} {m : Set α} (h : P m) : (P ⊕ᵤ ⊤ᵤ) m :=
  ⟨m, ∅, (Set.union_empty m).symm, h, trivial⟩

theorem oplusU_drop {P Q : Assn α} {m : Set α} (h : (P ⊕ᵤ Q) m) : (P ⊕ᵤ ⊤ᵤ) m := by
  obtain ⟨m₁, m₂, rfl, h₁, _⟩ := h
  exact ⟨m₁, m₂, rfl, h₁, trivial⟩

/-- True positives: `atomU p ⊕ ⊤` yields a reachable outcome satisfying `p`. -/
theorem true_positivesU {p : α → Prop} {m : Set α} (h : (atomU p ⊕ᵤ ⊤ᵤ) m) :
    ∃ x ∈ m, p x := by
  obtain ⟨m₁, m₂, rfl, ⟨⟨x, hx⟩, hall⟩, -⟩ := h
  exact ⟨x, Set.mem_union_left _ hx, hall x hx⟩

end OL
