import Mathlib.Data.Set.Lattice

/-!
# The powerset Kleisli engine

`kleisli k` is the Kleisli extension of `k : α → Set β` over the powerset monad.
This file is the single place where the execution-model structure of the
prototype lives: `kleisli_union` and `kleisli_empty` are exactly the two
PCM-compatibility laws of an Outcome-Logic execution model (Zilberstein et al.,
OOPSLA 2023, Def. 3.3) specialized to the powerset instance ⟨Set Σ, ∪, ∅⟩:

* `bind (m₁ ⋄ m₂) k = bind m₁ k ⋄ bind m₂ k`  ↝  `kleisli_union`
* `bind ∅ k = ∅`                              ↝  `kleisli_empty`

Every language semantics in this development defines its lift as `kleisli`
applied to a step function, and thereby inherits these laws for free.
-/

namespace RelOL

variable {α β γ : Type*}

/-- Kleisli extension of `k : α → Set β` over the powerset monad. -/
def kleisli (k : α → Set β) (m : Set α) : Set β := ⋃ x ∈ m, k x

@[simp] theorem mem_kleisli {k : α → Set β} {m : Set α} {y : β} :
    y ∈ kleisli k m ↔ ∃ x ∈ m, y ∈ k x := by
  simp [kleisli]

@[simp] theorem kleisli_empty (k : α → Set β) : kleisli k (∅ : Set α) = ∅ := by
  simp [kleisli]

@[simp] theorem kleisli_singleton (k : α → Set β) (x : α) : kleisli k {x} = k x := by
  simp [kleisli]

/-- The bind/⋄ compatibility law of the powerset execution model. -/
theorem kleisli_union (k : α → Set β) (m₁ m₂ : Set α) :
    kleisli k (m₁ ∪ m₂) = kleisli k m₁ ∪ kleisli k m₂ := by
  ext y; simp [mem_kleisli, or_and_right, exists_or]

/-- Kleisli extension distributes over pointwise union of continuations. -/
theorem kleisli_pointwise_union (k₁ k₂ : α → Set β) (m : Set α) :
    kleisli (fun x => k₁ x ∪ k₂ x) m = kleisli k₁ m ∪ kleisli k₂ m := by
  ext y
  simp only [mem_kleisli, Set.mem_union]
  constructor
  · rintro ⟨x, hx, hy | hy⟩
    · exact Or.inl ⟨x, hx, hy⟩
    · exact Or.inr ⟨x, hx, hy⟩
  · rintro (⟨x, hx, hy⟩ | ⟨x, hx, hy⟩)
    · exact ⟨x, hx, Or.inl hy⟩
    · exact ⟨x, hx, Or.inr hy⟩

/-- Kleisli composition (associativity of bind). -/
theorem kleisli_comp (k₁ : α → Set β) (k₂ : β → Set γ) (m : Set α) :
    kleisli k₂ (kleisli k₁ m) = kleisli (fun x => kleisli k₂ (k₁ x)) m := by
  ext z
  simp only [mem_kleisli]
  constructor
  · rintro ⟨y, ⟨x, hx, hy⟩, hz⟩
    exact ⟨x, hx, y, hy, hz⟩
  · rintro ⟨x, hx, y, hy, hz⟩
    exact ⟨y, ⟨x, hx, hy⟩, hz⟩

theorem kleisli_nonempty {k : α → Set β} {m : Set α} (hm : m.Nonempty)
    (h : ∀ x ∈ m, (k x).Nonempty) : (kleisli k m).Nonempty := by
  obtain ⟨x, hx⟩ := hm
  obtain ⟨y, hy⟩ := h x hx
  exact ⟨y, mem_kleisli.mpr ⟨x, hx, hy⟩⟩

end RelOL
