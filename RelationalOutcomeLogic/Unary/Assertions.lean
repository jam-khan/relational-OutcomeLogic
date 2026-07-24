import RelationalOutcomeLogic.Kleisli

/-!
# Unary outcome assertions (powerset instance)

Outcome assertions over `Set α`, per Outcome Logic's powerset instance
(Zilberstein et al., OOPSLA 2023, Def. 5.4): the atomic assertion bakes
**reachability** into satisfaction via the nonemptiness clause, and the outcome
conjunction `oplusU` splits the outcome set along (possibly overlapping) `∪`.

Trap recorded in Notes.md: OL's `⟨true⟩` precondition is `atomU (fun _ => True)`
— which still requires nonemptiness — NOT `topU`.
-/

namespace OL

open RelOL

variable {α : Type*}

/-- Unary outcome assertions: predicates over outcome *sets*, not states. -/
def Assn (α : Type*) := Set α → Prop

/-- Atomic satisfaction (OL Def. 5.4): `m ⊨ p` iff `m` is nonempty and every
outcome in `m` satisfies `p`. Nonemptiness bakes reachability into satisfaction. -/
def atomU (p : α → Prop) : Assn α := fun m => m.Nonempty ∧ ∀ x ∈ m, p x

/-- Outcome conjunction `⊕`: the outcome set splits (overlap-friendly) into a
part satisfying `P` and a part satisfying `Q`. -/
def oplusU (P Q : Assn α) : Assn α := fun m => ∃ m₁ m₂, m = m₁ ∪ m₂ ∧ P m₁ ∧ Q m₂

/-- The trivial assertion `⊤` (holds of every outcome set, including `∅`). -/
def topU : Assn α := fun _ => True

/-- `⊤^⊕`: the assertion of divergence — no outcomes at all. -/
def emptyU : Assn α := fun m => m = ∅

@[simp] theorem atomU_singleton {p : α → Prop} {x : α} : atomU p {x} ↔ p x := by
  simp [atomU]

theorem atomU_sat {p : α → Prop} {x : α} (h : p x) : atomU p {x} := atomU_singleton.mpr h

theorem oplusU_intro {P Q : Assn α} {m₁ m₂ : Set α} (h₁ : P m₁) (h₂ : Q m₂) :
    oplusU P Q (m₁ ∪ m₂) := ⟨m₁, m₂, rfl, h₁, h₂⟩

/-- `P ⊨ P ⊕ ⊤` via the trivial split `m = m ∪ ∅`. -/
theorem oplusU_left_top {P : Assn α} {m : Set α} (h : P m) : oplusU P topU m :=
  ⟨m, ∅, (Set.union_empty m).symm, h, trivial⟩

/-- Dropping outcomes (OL Lemma B.1): `P ⊕ Q ⟹ P ⊕ ⊤`. -/
theorem oplusU_drop {P Q : Assn α} {m : Set α} (h : oplusU P Q m) : oplusU P topU m := by
  obtain ⟨m₁, m₂, rfl, h₁, _⟩ := h
  exact ⟨m₁, m₂, rfl, h₁, trivial⟩

/-- Reachability extraction: an under-approximate atomic claim `atomU p ⊕ ⊤`
guarantees a *witness* outcome satisfying `p`. -/
theorem true_positivesU {p : α → Prop} {m : Set α} (h : oplusU (atomU p) topU m) :
    ∃ x ∈ m, p x := by
  obtain ⟨m₁, m₂, rfl, ⟨⟨x, hx⟩, hall⟩, -⟩ := h
  exact ⟨x, Set.mem_union_left _ hx, hall x hx⟩

end OL
