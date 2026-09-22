import RelationalOutcomeLogic.Prob.Coupling.Assertions
import RelationalOutcomeLogic.Prob.Coupling.Support
import Mathlib.Tactic.NormNum

/-!
# Probability-sensitive coupling examples

These finite examples exercise exact marginal equality, additive assertion splitting,
and sequencing. Equal supports do not imply equal probabilities. Missing mass is
allowed on both sides, but exact coupling requires the same termination mass.
-/

namespace RelOL.Prob.Examples

open scoped ENNReal

noncomputable section

/-- One half of a unit outcome. -/
def half (b : Bool) : Weight Bool := (1 / 2 : ℝ≥0∞) • Weight.pure b

/-- A fair coin. -/
def fair : Weight Bool := half false + half true

/-- True with probability three quarters. -/
def biased : Weight Bool :=
  (1 / 4 : ℝ≥0∞) • Weight.pure false + (3 / 4 : ℝ≥0∞) • Weight.pure true

theorem fair_isProbability : Weight.IsProbability fair := by
  change Weight.mass fair = 1
  simp only [fair, half, Weight.mass_add, Weight.mass_smul, Weight.mass_pure, mul_one]
  rw [← ENNReal.add_div]
  norm_num only [one_add_one_eq_two]
  exact ENNReal.div_self (by norm_num) (by norm_num)

theorem biased_isProbability : Weight.IsProbability biased := by
  change Weight.mass biased = 1
  simp only [biased, Weight.mass_add, Weight.mass_smul, Weight.mass_pure, mul_one]
  rw [← ENNReal.add_div]
  norm_num only [show (1 + 3 : ℝ≥0∞) = 4 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

theorem fair_support : Weight.support fair = Set.univ := by
  ext b
  cases b <;> norm_num [Weight.support, fair, half, biased, Weight.pure]

theorem biased_support : Weight.support biased = Set.univ := by
  ext b
  cases b <;> norm_num [Weight.support, biased, Weight.pure]

theorem same_support : Weight.support fair = Weight.support biased := by
  rw [fair_support, biased_support]

theorem fair_ne_biased : fair ≠ biased := by
  intro h
  have := congrFun h false
  norm_num [fair, half, biased, Weight.pure] at this

theorem fair_equality_coupling : Coupled Eq fair fair := coupled_eq_iff.mpr rfl

/-- Equal supports and equal total mass still do not imply an equality coupling. -/
theorem no_fair_biased_equality_coupling : ¬ Coupled Eq fair biased := by
  simpa only [coupled_eq_iff] using fair_ne_biased

theorem support_coupling_not_enough :
    RelOL.couple Eq (Weight.support fair) (Weight.support biased) ∧
      ¬ Coupled Eq fair biased := by
  refine ⟨?_, no_fair_biased_equality_coupling⟩
  rw [← same_support]
  exact fair_equality_coupling.support_couple

/-- An explicit joint couples opposite coin outcomes. -/
def oppositeJoint : Weight (Bool × Bool) :=
  (1 / 2 : ℝ≥0∞) • Weight.pure (false, true) +
    (1 / 2 : ℝ≥0∞) • Weight.pure (true, false)

theorem oppositeJoint_isCoupling :
    IsCoupling (fun a b : Bool => a = !b) fair fair oppositeJoint := by
  have h₀ := (IsCoupling.pure (R := fun a b : Bool => a = !b)
    (a := false) (b := true) rfl).smul (1 / 2)
  have h₁ := (IsCoupling.pure (R := fun a b : Bool => a = !b)
    (a := true) (b := false) rfl).smul (1 / 2)
  have h : IsCoupling (fun a b : Bool => a = !b)
      (half false + half true) (half true + half false) oppositeJoint := h₀.add h₁
  simpa only [fair, add_comm (half true) (half false)] using h

theorem fair_opposite_coupling : Coupled (fun a b : Bool => a = !b) fair fair :=
  ⟨oppositeJoint, oppositeJoint_isCoupling⟩

/-- Sequencing preserves the exact marginals while negation changes the relation. -/
theorem opposite_then_negate :
    Coupled Eq (Weight.bind fair Weight.pure)
      (Weight.bind fair (fun b => Weight.pure (!b))) := by
  apply fair_opposite_coupling.bind
  intro a b hab
  exact Coupled.pure hab

theorem fair_negation_preserves_weights :
    Weight.bind fair (fun b => Weight.pure (!b)) = fair := by
  simpa only [Weight.bind_pure] using (coupled_eq_iff.mp opposite_then_negate).symm

/-- Each coin branch carries one half of the mass on each side. -/
theorem fair_mass_split :
    oplus (massEq (1 / 2) (1 / 2)) (massEq (1 / 2) (1 / 2)) fair fair := by
  apply oplus_intro <;> constructor <;> simp [half, Weight.mass_smul]

theorem fair_coupled_by_splitting : couple Eq fair fair := by
  apply oplus_couple_same fair fair
  exact oplus_intro (coupled_eq_iff.mpr rfl : couple Eq (half false) (half false))
    (coupled_eq_iff.mpr rfl : couple Eq (half true) (half true))

/-- The additive assertion cannot silently copy a probability distribution. -/
theorem fair_cannot_split_into_two_unit_masses :
    ¬ oplus (massEq 1 1) (massEq 1 1) fair fair := by
  intro h
  have hmass := (oplus_massEq 1 1 1 1 fair fair h).1
  rw [fair_isProbability] at hmass
  norm_num at hmass

/-- Positive but unequal termination probabilities refute every exact relation. -/
theorem no_unequal_termination_coupling (R : Unit → Unit → Prop) :
    ¬ Coupled R (Weight.pure ()) ((1 / 2 : ℝ≥0∞) • Weight.pure ()) := by
  intro h
  have hmass := h.mass_eq
  norm_num [Weight.mass_smul] at hmass
  exact ENNReal.one_half_lt_one.ne' hmass

/-- Exact coupling permits both sides to have no terminating outcomes. -/
theorem joint_divergence_couples (R : Bool → Unit → Prop) :
    Coupled R 0 0 := Coupled.zero R

theorem one_sided_divergence_does_not_couple (R : Bool → Unit → Prop) :
    ¬ Coupled R 0 (Weight.pure ()) := by
  intro h
  have hmass := h.mass_eq
  norm_num at hmass

/-- The raw coupling algebra also admits infinite weights, without division. -/
theorem infinite_scaling_couples :
    Coupled (fun a b : Bool => a = !b) (∞ • fair) (∞ • fair) :=
  fair_opposite_coupling.smul ∞

end

end RelOL.Prob.Examples
