import RelationalOutcomeLogic.Generic.Rules

/-!
# Distributional invariants induced by a reconstruction kernel

`lifted B` relates an abstract outcome to the concrete outcome obtained by
sequencing it with `B`. Unlike a relation on individual states, it retains the
conditional law of hidden random state. For example, `B` can reconstruct a
pending random buffer conditional on an already emitted history.

The one-step rule requires a local commuting square. It lifts that square to
arbitrary input outcomes, so sequencing and bounded-recursion rules can consume
it without assuming the equality of complete executions. No normalization
assumption is necessary for this algebraic rule; a probabilistic application can
separately require its reconstruction kernels to be normalized.
-/

namespace RelOL.Generic

universe u v
variable {M : Type u → Type v} [OutcomeModel M]
variable {α β γ δ : Type u}
open OutcomeModel

/-- The concrete outcome has the prescribed conditional reconstruction law. -/
def lifted (B : α → M β) : RAssn M α β := fun μ ν => ν = bind μ B

@[simp] theorem lifted_pure (B : α → M β) (a : α) :
    lifted B (pure a) (B a) := by
  simp only [lifted, OutcomeModel.pure_bind]

theorem lifted_add (B : α → M β) {μ₁ μ₂ : M α} {ν₁ ν₂ : M β}
    (h₁ : lifted B μ₁ ν₁) (h₂ : lifted B μ₂ ν₂) :
    lifted B (add μ₁ μ₂) (add ν₁ ν₂) := by
  change add ν₁ ν₂ = bind (add μ₁ μ₂) B
  rw [add_bind, h₁, h₂]

/-- A local reconstruction square is a relational judgment on every pair of
input outcomes satisfying the distributional invariant. -/
theorem quad_lifted {B : α → M β} {B' : γ → M δ}
    {k : α → M γ} {l : β → M δ}
    (hstep : ∀ a, bind (B a) l = bind (k a) B') :
    quad (lifted B) k l (lifted B') := by
  intro μ ν h
  change bind ν l = bind (bind μ k) B'
  rw [show ν = bind μ B from h, OutcomeModel.bind_assoc, OutcomeModel.bind_assoc]
  exact congrArg (bind μ) (funext hstep)

/-- The one-step premise is exactly the pure-input obligation of the lifted
judgment. Its conclusion, however, applies to arbitrary mixtures. -/
theorem quad_lifted_iff {B : α → M β} {B' : γ → M δ}
    {k : α → M γ} {l : β → M δ} :
    quad (lifted B) k l (lifted B') ↔
      ∀ a, bind (B a) l = bind (k a) B' := by
  constructor
  · intro h a
    have ha := h (pure a) (B a) (lifted_pure B a)
    simpa only [lifted, OutcomeModel.pure_bind] using ha
  · exact quad_lifted

/-- The same invariant with the concrete program on the left. -/
theorem quad_lifted_swap {B : α → M β} {B' : γ → M δ}
    {k : α → M γ} {l : β → M δ}
    (hstep : ∀ a, bind (B a) l = bind (k a) B') :
    quad (lifted B).swap l k (lifted B').swap :=
  quad_swap (quad_lifted hstep)

/-- Extend reconstruction across a branch that has already returned a result. -/
def extendReconstruction (B : α → M β) : Sum α γ → M (Sum β γ)
  | .inl a => bind (B a) (fun b => pure (.inl b))
  | .inr c => pure (.inr c)

/-- Continue a pending state, or retain an already returned result. -/
def dispatch (k : α → M γ) : Sum α γ → M γ
  | .inl a => k a
  | .inr c => pure c

/-- Branching consumes the continuation's specification. Returned outcomes do
not execute that continuation; pending outcomes retain their reconstruction law. -/
theorem quad_lifted_dispatch {B : α → M β}
    {k : α → M γ} {l : β → M γ}
    (h : quad (lifted B) k l (lifted (pure : γ → M γ))) :
    quad (lifted (extendReconstruction (γ := γ) B)) (dispatch k) (dispatch l)
      (lifted (pure : γ → M γ)) := by
  apply quad_lifted
  intro s
  cases s with
  | inl a =>
    simpa only [extendReconstruction, dispatch,
      OutcomeModel.bind_assoc, OutcomeModel.pure_bind] using
      (quad_lifted_iff.mp h) a
  | inr c => simp only [extendReconstruction, dispatch, OutcomeModel.pure_bind]

end RelOL.Generic
