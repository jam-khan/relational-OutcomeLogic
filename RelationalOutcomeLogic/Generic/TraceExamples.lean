import RelationalOutcomeLogic.Algebra.Instances.Language
import RelationalOutcomeLogic.Generic.WeightedLogic
import RelationalOutcomeLogic.Generic.WeightedPrograms

/-!
# Noncommutative finite-trace examples

Sequencing two log actions preserves their order. The same generic weighted
semantics and countdown theorem used for numeric weights also record finite
trace languages. No infinite traces are represented by this instance.
-/

namespace RelOL.Generic.TraceExamples

open Algebra Algebra.Weighted WeightedPrograms

noncomputable section

/-- Log one alphabet symbol. -/
def emit (a : Bool) : Language Bool := {[a]}

theorem emit_mul (a b : Bool) : emit a * emit b = ({[a, b]} : Language Bool) := by
  change Set.image2 (· ++ ·) ({[a]} : Set (List Bool)) {[b]} = {[a, b]}
  simp

/-- Two logging actions composed with the generic weighted bind. -/
def logPair (a b : Bool) : Weighted.Weight (Language Bool) Unit :=
  Weighted.bind (Weighted.scale (emit a) (Weighted.pure ()))
    (fun _ => Weighted.scale (emit b) (Weighted.pure ()))

theorem logPair_value (a b : Bool) : logPair a b () = ({[a, b]} : Language Bool) := by
  rw [logPair, scale_bind, Weighted.pure_bind]
  simpa using emit_mul a b

/-- The instance's multiplication really does not commute. -/
theorem emit_noncommutative : emit false * emit true ≠ emit true * emit false := by
  rw [emit_mul, emit_mul]
  intro h
  have he : ({[false, true]} : Set (List Bool)) = {[true, false]} := h
  have hm := Set.ext_iff.mp he [false, true]
  simp at hm

/-- Swapping two log actions is refuted by the generic exact coupling relation. -/
theorem swapped_logs_not_coupled : ¬ Coupled Eq (logPair false true) (logPair true false) := by
  intro h
  have he := congrFun (coupled_eq_iff.mp h) ()
  rw [logPair_value, logPair_value] at he
  change ({[false, true]} : Set (List Bool)) = {[true, false]} at he
  have hm := Set.ext_iff.mp he [false, true]
  simp at hm

/-- Branching between the two execution orders records both words. -/
theorem log_choice_value :
    (logPair false true + logPair true false) () =
      ({[false, true], [true, false]} : Language Bool) := by
  rw [Pi.add_apply, logPair_value, logPair_value, Language.add_def]
  change ({[false, true]} : Set (List Bool)) ∪ {[true, false]} =
    ({[false, true], [true, false]} : Set (List Bool))
  ext w
  simp [or_comm]

/-- The shared loop theorem counts iterations by concatenating the emitted word. -/
theorem logging_countdown (a : Bool) (n : ℕ) :
    Weighted.mass (countdown (emit a) n) = emit a ^ n := countdown_mass _ _

/-- A concrete two-iteration loop emits exactly two copies of its symbol. -/
theorem logging_countdown_two (a : Bool) :
    Weighted.mass (countdown (emit a) 2) = ({[a, a]} : Language Bool) := by
  rw [logging_countdown, pow_two, emit_mul]

end
end RelOL.Generic.TraceExamples
