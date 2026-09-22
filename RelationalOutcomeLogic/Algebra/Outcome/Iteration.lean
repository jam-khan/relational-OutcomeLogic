import RelationalOutcomeLogic.Algebra.Outcome.Basic
import Mathlib.Order.FixedPoints

/-!
# Ordered outcome models for iteration

The shared loop construction needs a bottom outcome, monotone sequencing, and
preservation of increasing limits in the continuation. It does not assume
idempotent outcome addition or preservation of arbitrary suprema.
-/

universe u v

namespace RelOL

class IterationModel (M : Type u → Type v) [OutcomeModel M]
    [∀ α, CompleteLattice (M α)] : Prop where
  empty_eq_bot {α : Type u} : (OutcomeModel.empty : M α) = ⊥
  bind_mono {α β : Type u} {x y : M α} {k l : α → M β} :
    x ≤ y → k ≤ l → OutcomeModel.bind x k ≤ OutcomeModel.bind y l
  bind_iSup_right {α β : Type u} (x : M α) (k : ℕ → α → M β)
      (hk : Monotone k) :
    OutcomeModel.bind x (⨆ n, k n) = ⨆ n, OutcomeModel.bind x (k n)

end RelOL
