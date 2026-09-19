/-!
# Modes for relational loop alignment

A selector chooses which program advances. Progress and marginal preservation are
proved separately for each outcome model.
-/

namespace RelOL

inductive AsyncMode where
  | left
  | right
  | both
  | done
  deriving DecidableEq

/-- Reverse the two programs while preserving joint execution and exit. -/
def AsyncMode.swap : AsyncMode → AsyncMode
  | .left => .right
  | .right => .left
  | .both => .both
  | .done => .done

@[simp] theorem AsyncMode.swap_swap (m : AsyncMode) : m.swap.swap = m := by
  cases m <;> rfl

end RelOL
