import Mathlib.Logic.Function.Basic

/-!
# Shared additive outcome semantics

The model consists of a commutative additive outcome monoid and Kleisli sequencing.
The operations are explicit: sets use union and weights use addition, without
installing competing `Add` instances. Idempotence, scalar multiplication, order,
normalization, and infinite iteration are deliberately not assumed here.
-/

namespace RelOL

universe u v

/-- The algebra needed by the common structural relational outcome rules. -/
class OutcomeModel (M : Type u → Type v) where
  empty : {α : Type u} → M α
  add : {α : Type u} → M α → M α → M α
  pure : {α : Type u} → α → M α
  bind : {α β : Type u} → M α → (α → M β) → M β
  add_assoc : ∀ {α} (x y z : M α), add (add x y) z = add x (add y z)
  add_comm : ∀ {α} (x y : M α), add x y = add y x
  empty_add : ∀ {α} (x : M α), add empty x = x
  add_empty : ∀ {α} (x : M α), add x empty = x
  pure_bind : ∀ {α β} (a : α) (k : α → M β), bind (pure a) k = k a
  bind_pure : ∀ {α} (x : M α), bind x pure = x
  bind_assoc : ∀ {α β γ} (x : M α) (k : α → M β) (l : β → M γ),
    bind (bind x k) l = bind x (fun a => bind (k a) l)
  empty_bind : ∀ {α β} (k : α → M β), bind empty k = empty
  bind_empty : ∀ {α β} (x : M α), bind x (fun _ => (empty : M β)) = empty
  add_bind : ∀ {α β} (x y : M α) (k : α → M β),
    bind (add x y) k = add (bind x k) (bind y k)
  bind_add : ∀ {α β} (x : M α) (k l : α → M β),
    bind x (fun a => add (k a) (l a)) = add (bind x k) (bind x l)

namespace OutcomeModel

variable {M : Type u → Type v} [OutcomeModel M]
variable {α β γ : Type u}

attribute [simp] empty_add add_empty pure_bind bind_pure empty_bind bind_empty

/-- The additive order is available without choosing an ambient order on outcomes. -/
def Suboutcome (x y : M α) : Prop := ∃ z, y = add x z

theorem Suboutcome.refl (x : M α) : Suboutcome x x :=
  ⟨empty, (add_empty x).symm⟩

theorem Suboutcome.trans {x y z : M α} (hxy : Suboutcome x y)
    (hyz : Suboutcome y z) : Suboutcome x z := by
  obtain ⟨a, rfl⟩ := hxy
  obtain ⟨b, rfl⟩ := hyz
  exact ⟨add a b, add_assoc _ _ _⟩

theorem Suboutcome.bind {x y : M α} (h : Suboutcome x y) (k : α → M β) :
    Suboutcome (bind x k) (bind y k) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨OutcomeModel.bind z k, add_bind _ _ _⟩

/-- Mapping observations is just sequencing with pure outcomes. -/
def map (f : α → β) (x : M α) : M β := bind x (fun a => pure (f a))

@[simp] theorem map_pure (f : α → β) (a : α) : map f (pure a : M α) = pure (f a) :=
  pure_bind _ _

@[simp] theorem map_id (x : M α) : map id x = x := bind_pure _

theorem map_comp (f : α → β) (g : β → γ) (x : M α) :
    map g (map f x) = map (g ∘ f) x := by
  simp [map, bind_assoc]

theorem map_add (f : α → β) (x y : M α) :
    map f (add x y) = add (map f x) (map f y) := add_bind _ _ _

end OutcomeModel
end RelOL
