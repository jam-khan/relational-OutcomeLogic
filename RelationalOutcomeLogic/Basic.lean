import Mathlib.Data.Int.Basic

/-! # Basic definitions: program states and concrete state builders -/

namespace RelOL

/-- A program state. -/
abbrev State := String → Int

/-- Concrete-state builder for the NI example. -/
def st (x low : Int) : State := fun v => if v = "x" then x else if v = "low" then low else 0

@[simp] theorem st_x (x low : Int) : st x low "x" = x := by simp [st]

@[simp] theorem st_low (x low : Int) : st x low "low" = low := by simp [st]

end RelOL
