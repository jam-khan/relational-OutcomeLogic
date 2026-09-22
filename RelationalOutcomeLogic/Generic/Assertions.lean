import RelationalOutcomeLogic.Algebra.OutcomeModel

/-! # Relational assertions shared by additive outcome models -/

namespace RelOL.Generic

universe u v
variable {M : Type u → Type v} [OutcomeModel M]
variable {α β : Type u}
open OutcomeModel

abbrev RAssn (M : Type u → Type v) (α β : Type u) := M α → M β → Prop

def entail (P Q : RAssn M α β) : Prop := ∀ x y, P x y → Q x y
def rtop : RAssn M α β := fun _ _ => True
def rbot : RAssn M α β := fun _ _ => False
def emp : RAssn M α β := fun x y => x = empty ∧ y = empty
def exactly (x₀ : M α) (y₀ : M β) : RAssn M α β := fun x y => x = x₀ ∧ y = y₀
def disj (P Q : RAssn M α β) : RAssn M α β := fun x y => P x y ∨ Q x y

/-- Additive splitting; the pieces need not be disjoint or idempotent. -/
def oplus (P Q : RAssn M α β) : RAssn M α β :=
  fun x y => ∃ x₁ x₂ y₁ y₂,
    x = add x₁ x₂ ∧ y = add y₁ y₂ ∧ P x₁ y₁ ∧ Q x₂ y₂

def RAssn.swap (P : RAssn M α β) : RAssn M β α := fun y x => P x y

omit [OutcomeModel M] in
theorem entail_refl (P : RAssn M α β) : entail P P := fun _ _ h => h
omit [OutcomeModel M] in
theorem entail_trans {P Q S : RAssn M α β} (h : entail P Q) (h' : entail Q S) :
    entail P S := fun x y hx => h' x y (h x y hx)

omit [OutcomeModel M] in
@[simp] theorem exactly_self (x : M α) (y : M β) : exactly x y x y := ⟨rfl, rfl⟩
@[simp] theorem emp_empty : emp (empty : M α) (empty : M β) := ⟨rfl, rfl⟩

theorem oplus_intro {P Q : RAssn M α β} {x₁ x₂ : M α} {y₁ y₂ : M β}
    (hP : P x₁ y₁) (hQ : Q x₂ y₂) : oplus P Q (add x₁ x₂) (add y₁ y₂) :=
  ⟨x₁, x₂, y₁, y₂, rfl, rfl, hP, hQ⟩

theorem oplus_mono {P P' Q Q' : RAssn M α β} (hP : entail P P') (hQ : entail Q Q') :
    entail (oplus P Q) (oplus P' Q') := by
  rintro _ _ ⟨x₁, x₂, y₁, y₂, rfl, rfl, h₁, h₂⟩
  exact oplus_intro (hP _ _ h₁) (hQ _ _ h₂)

theorem oplus_comm (P Q : RAssn M α β) : oplus P Q = oplus Q P := by
  funext x y
  apply propext
  constructor <;> rintro ⟨x₁, x₂, y₁, y₂, rfl, rfl, h₁, h₂⟩ <;>
    exact ⟨x₂, x₁, y₂, y₁, add_comm _ _, add_comm _ _, h₂, h₁⟩

theorem oplus_assoc (P Q S : RAssn M α β) :
    oplus (oplus P Q) S = oplus P (oplus Q S) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨x₁₂, x₃, y₁₂, y₃, rfl, rfl,
      ⟨x₁, x₂, y₁, y₂, rfl, rfl, h₁, h₂⟩, h₃⟩
    exact ⟨x₁, add x₂ x₃, y₁, add y₂ y₃, add_assoc _ _ _, add_assoc _ _ _, h₁,
      oplus_intro h₂ h₃⟩
  · rintro ⟨x₁, x₂₃, y₁, y₂₃, rfl, rfl, h₁,
      ⟨x₂, x₃, y₂, y₃, rfl, rfl, h₂, h₃⟩⟩
    exact ⟨add x₁ x₂, x₃, add y₁ y₂, y₃, (add_assoc _ _ _).symm,
      (add_assoc _ _ _).symm, oplus_intro h₁ h₂, h₃⟩

@[simp] theorem oplus_emp (P : RAssn M α β) : oplus P emp = P := by
  funext x y
  apply propext
  constructor
  · rintro ⟨x₁, x₂, y₁, y₂, rfl, rfl, hP, rfl, rfl⟩
    simpa using hP
  · intro hP
    exact ⟨x, empty, y, empty, (add_empty _).symm, (add_empty _).symm, hP, rfl, rfl⟩

@[simp] theorem emp_oplus (P : RAssn M α β) : oplus emp P = P := by
  rw [oplus_comm, oplus_emp]

theorem oplus_exactly (x₁ x₂ : M α) (y₁ y₂ : M β) :
    oplus (exactly x₁ y₁) (exactly x₂ y₂) = exactly (add x₁ x₂) (add y₁ y₂) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨_, _, _, _, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact oplus_intro (exactly_self _ _) (exactly_self _ _)

theorem oplus_left_top {P : RAssn M α β} {x : M α} {y : M β} (hP : P x y) :
    oplus P rtop x y :=
  ⟨x, empty, y, empty, (add_empty _).symm, (add_empty _).symm, hP, trivial⟩

/-- An under-approximate certificate survives adding further outcomes. -/
theorem oplus_top_mono {P : RAssn M α β} {x x' : M α} {y y' : M β}
    (h : oplus P rtop x y) (hx : Suboutcome x x') (hy : Suboutcome y y') :
    oplus P rtop x' y' := by
  obtain ⟨x₁, x₂, y₁, y₂, rfl, rfl, hP, _⟩ := h
  obtain ⟨x₃, rfl⟩ := hx
  obtain ⟨y₃, rfl⟩ := hy
  exact ⟨x₁, add x₂ x₃, y₁, add y₂ y₃, add_assoc _ _ _, add_assoc _ _ _, hP, trivial⟩

omit [OutcomeModel M] in
@[simp] theorem RAssn.swap_swap (P : RAssn M α β) : P.swap.swap = P := rfl

theorem RAssn.swap_oplus (P Q : RAssn M α β) :
    (oplus P Q).swap = oplus P.swap Q.swap := by
  funext y x
  apply propext
  constructor <;> rintro ⟨x₁, x₂, y₁, y₂, hx, hy, hP, hQ⟩ <;>
    exact ⟨y₁, y₂, x₁, x₂, hy, hx, hP, hQ⟩

end RelOL.Generic
