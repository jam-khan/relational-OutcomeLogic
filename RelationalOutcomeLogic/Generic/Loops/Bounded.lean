import RelationalOutcomeLogic.Generic.Rules

/-!
# Relational rules for bounded iteration and continuation recursion

These rules operate on arbitrary relational outcome assertions, including
distributional invariants. `quad_boundedRec` separates the base case from a
single recursive layer: a client proves that layer preserves a specification
for any continuations satisfying the previous index's specification. It does
not assume a property of an already completed recursive program.
-/

namespace RelOL.Generic

universe u v
variable {M : Type u → Type v} [OutcomeModel M]
variable {α β γ δ : Type u}
open OutcomeModel

/-- Execute descending indexed transitions, ending in the identity kernel. -/
def boundedSteps (step : Nat → α → M α) : Nat → α → M α
  | 0 => pure
  | n + 1 => fun a => bind (step n a) (boundedSteps step n)

/-- Local preservation of an indexed assertion proves the whole bounded run. -/
theorem quad_boundedSteps (P : Nat → RAssn M α β)
    (k : Nat → α → M α) (l : Nat → β → M β)
    (hstep : ∀ n, quad (P (n + 1)) (k n) (l n) (P n)) (n : Nat) :
    quad (P n) (boundedSteps k n) (boundedSteps l n) (P 0) := by
  induction n with
  | zero => exact quad_skip (P 0)
  | succ n ih => exact quad_seq (hstep n) ih

/-- Invariant form of bounded iteration, derived through sequencing. -/
theorem quad_boundedSteps_invariant (P : RAssn M α β)
    (k : Nat → α → M α) (l : Nat → β → M β)
    (hstep : ∀ n, quad P (k n) (l n) P) (n : Nat) :
    quad P (boundedSteps k n) (boundedSteps l n) P :=
  quad_boundedSteps (fun _ => P) k l hstep n

/-- Unfold a continuation-based program for a finite number of layers. Each
layer may sequence, split, or branch before invoking its supplied continuation. -/
def boundedRec (base : α → M γ)
    (layer : Nat → (α → M γ) → α → M γ) : Nat → α → M γ
  | 0 => base
  | n + 1 => layer n (boundedRec base layer n)

/-- A relational bounded-recursion rule. The layer premise is parametric in
the recursive continuations and consumes their relational specification. -/
theorem quad_boundedRec (P : Nat → RAssn M α β) (Q : RAssn M γ δ)
    (baseF : α → M γ) (baseG : β → M δ)
    (layerF : Nat → (α → M γ) → α → M γ)
    (layerG : Nat → (β → M δ) → β → M δ)
    (hbase : quad (P 0) baseF baseG Q)
    (hlayer : ∀ n k l, quad (P n) k l Q →
      quad (P (n + 1)) (layerF n k) (layerG n l) Q) (n : Nat) :
    quad (P n) (boundedRec baseF layerF n) (boundedRec baseG layerG n) Q := by
  induction n with
  | zero => exact hbase
  | succ n ih => exact hlayer n _ _ ih

/-- The same rule consumes existing recursive definitions through their local
unfolding equations, avoiding a second implementation solely for verification. -/
theorem quad_recursion (P : Nat → RAssn M α β) (Q : RAssn M γ δ)
    (F : Nat → α → M γ) (G : Nat → β → M δ)
    (layerF : Nat → (α → M γ) → α → M γ)
    (layerG : Nat → (β → M δ) → β → M δ)
    (hF : ∀ n, F (n + 1) = layerF n (F n))
    (hG : ∀ n, G (n + 1) = layerG n (G n))
    (hbase : quad (P 0) (F 0) (G 0) Q)
    (hlayer : ∀ n k l, quad (P n) k l Q →
      quad (P (n + 1)) (layerF n k) (layerG n l) Q) (n : Nat) :
    quad (P n) (F n) (G n) Q := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
    rw [hF n, hG n]
    exact hlayer n _ _ ih

/-- Indexed families retain the specification of each possible continuation
input. This permits one recursive layer to consume a variable amount of work,
while consulting earlier contracts at several different budgets or histories.
Both preconditions and postconditions may depend on the recursion index. The
layer premise remains parametric in arbitrary recursive continuations. -/
theorem quad_recursion_family {ι : Sort*}
    (P : Nat → ι → RAssn M α β) (Q : Nat → ι → RAssn M γ δ)
    (F : Nat → α → M γ) (G : Nat → β → M δ)
    (layerF : Nat → (α → M γ) → α → M γ)
    (layerG : Nat → (β → M δ) → β → M δ)
    (hF : ∀ n, F (n + 1) = layerF n (F n))
    (hG : ∀ n, G (n + 1) = layerG n (G n))
    (hbase : ∀ i, quad (P 0 i) (F 0) (G 0) (Q 0 i))
    (hlayer : ∀ n k l, (∀ i, quad (P n i) k l (Q n i)) →
      ∀ i, quad (P (n + 1) i) (layerF n k) (layerG n l) (Q (n + 1) i))
    (n : Nat) (i : ι) : quad (P n i) (F n) (G n) (Q n i) := by
  induction n generalizing i with
  | zero => exact hbase i
  | succ n ih =>
    rw [hF n, hG n]
    exact hlayer n _ _ ih i

end RelOL.Generic
