import Mathlib.Data.Int.Basic

/-!
# Basic definitions: program states and concrete state builders

`State` is the homogeneous store used by the unary logic and the homogeneous
relational examples. `st` builds concrete states for counterexample witnesses
(e.g. in `not_NI`); its `@[simp]` evaluation lemmas let examples close by `simp`.
-/

namespace RelOL

/-- A program state: a total store mapping variable names to integers. -/
abbrev State := String → Int

/-- Concrete-state builder for the NI example: `st x low` maps `"x" ↦ x`,
`"low" ↦ low`, and every other variable to `0`. -/
def st (x low : Int) : State := fun v => if v = "x" then x else if v = "low" then low else 0

@[simp] theorem st_x (x low : Int) : st x low "x" = x := by simp [st]

@[simp] theorem st_low (x low : Int) : st x low "low" = low := by simp [st]

end RelOL
