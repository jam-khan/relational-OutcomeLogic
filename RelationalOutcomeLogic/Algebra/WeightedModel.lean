import RelationalOutcomeLogic.Algebra.Weighted
import RelationalOutcomeLogic.Algebra.OutcomeModel

/-! The shared outcome algebra, constructed from the scalar summation laws. -/

universe u v

namespace RelOL.Algebra.Weighted

variable {K : Type v} [Semiring K] [SummationSemiring.{u} K]

/-- Low priority preserves the existing concrete ENNReal model when both are
imported; its operations agree with this construction. -/
noncomputable instance (priority := 100) outcomeModel :
    OutcomeModel (Weight K : Type u → Type _) where
  empty := 0
  add := (· + ·)
  pure := pure
  bind := bind
  add_assoc := fun _ _ _ => add_assoc _ _ _
  add_comm := fun _ _ => add_comm _ _
  empty_add := fun _ => zero_add _
  add_empty := fun _ => add_zero _
  pure_bind := pure_bind
  bind_pure := bind_pure
  bind_assoc := bind_assoc
  empty_bind := zero_bind
  bind_empty := bind_zero
  add_bind := add_bind
  bind_add := bind_add

end RelOL.Algebra.Weighted
