import RelationalOutcomeLogic.Algebra.ENNReal.Limits
import Mathlib.Tactic.NormNum

/-!
# Boundaries of the weighted model

These counterexamples explain why the generic execution model does not assume
set-specific laws. They use two finite states and exact arithmetic.
-/

namespace RelOL.Weight

open scoped ENNReal

/-- Copying a unit outcome doubles its mass; addition is not idempotent. -/
theorem pure_add_self_ne : pure () + pure () ≠ pure () := by
  intro h
  have hm := congrArg mass h
  norm_num [mass_add, mass_pure] at hm

/-- Total addition belongs to raw weights, not to the subprobability subset. -/
theorem subprob_add_not_closed :
    ∃ μ ν : Weight Unit, IsSubprob μ ∧ IsSubprob ν ∧ ¬ IsSubprob (μ + ν) := by
  refine ⟨pure (), pure (), ?_, ?_, ?_⟩ <;>
    norm_num [IsSubprob, mass_add, mass_pure]

/-- Incomparable Dirac weights show why mass continuity requires an increasing family. -/
theorem mass_sup_ne_sup_mass :
    mass (pure false ⊔ pure true) ≠ mass (pure false) ⊔ mass (pure true) := by
  norm_num [mass, pure, tsum_fintype, Pi.sup_apply]

/-- Subprobabilities are not closed under arbitrary pointwise binary suprema. -/
theorem subprob_sup_not_closed :
    IsSubprob (pure false) ∧ IsSubprob (pure true) ∧
      ¬ IsSubprob (pure false ⊔ pure true) := by
  norm_num [IsSubprob, mass, pure, tsum_fintype, Pi.sup_apply]

/-- A continuation merging two states refutes arbitrary-supremum preservation by bind. -/
theorem bind_sup_ne_sup_bind :
    bind (pure false ⊔ pure true) (fun _ => pure ()) ≠
      bind (pure false) (fun _ => pure ()) ⊔ bind (pure true) (fun _ => pure ()) := by
  intro h
  have hx := congrFun h ()
  norm_num [bind, pure, tsum_fintype, Pi.sup_apply] at hx

end RelOL.Weight
