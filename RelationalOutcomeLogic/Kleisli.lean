import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints

namespace RelOL

-- `Type*` enables an implicit universe level
variable {α β γ : Type*}

/-
  Kleisli extension of `k : α → Set β` over the powerset monad.

  It means run `k` from every state in `m`, and
  collect all outcomes

  `k` is some non-deterministic program,
  state of type `α` to a set of outcomes of type `β`.

  `k†` : Set α → Set β
-/
def kleisli (k : α → Set β) (m : Set α) : Set β :=
  ⋃ x ∈ m, k x

/-
  It means that `y : β` is a possible outcome, given
  a program `k : α → Set β` and the set of input
  states `m : Set α`.
-/
@[simp] theorem mem_kleisli
  {k : α → Set β} {m : Set α} {y : β} :
    y ∈ kleisli k m ↔ ∃ x ∈ m, y ∈ k x := by
  unfold kleisli
  constructor
  repeat simp_all

-- k† ∅ = ∅
@[simp] theorem kleisli_empty
  (k : α → Set β) :
    kleisli k (∅ : Set α) = ∅ := by
  unfold kleisli
  simp

-- k† {x} = k x
@[simp] theorem kleisli_singleton
  (k : α → Set β) (x : α) :
    kleisli k {x} = k x := by
  unfold kleisli
  simp


end RelOL
