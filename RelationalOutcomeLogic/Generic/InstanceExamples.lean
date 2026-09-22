import RelationalOutcomeLogic.Algebra.Instances.Boolean
import RelationalOutcomeLogic.Algebra.Instances.Probability
import RelationalOutcomeLogic.Algebra.Instances.Counting
import RelationalOutcomeLogic.Algebra.Instances.Tropical
import RelationalOutcomeLogic.Generic.WeightedLogic
import RelationalOutcomeLogic.Generic.WeightedPrograms
import RelationalOutcomeLogic.Generic.WeightedCertificates
import Mathlib.Tactic.NormNum

/-!
# The same weighted programs in four models

A two-route graph and a bounded loop are defined once. The concrete scalar
instances turn their generic proofs into reachability, trace-counting,
probability-weight, and minimum-cost results.
-/

open scoped ENNReal

namespace RelOL.Generic.InstanceExamples

open Algebra Algebra.Weighted WeightedPrograms

noncomputable section

section Routes

variable {K : Type*} [Semiring K] [SummationSemiring.{0} K]

/-- A direct edge to node 2, or two successive edges through node 1. -/
def routes (direct first second : K) : Weighted.Weight K ℕ :=
  scale direct (pure 2) + bind (scale first (pure 1)) (fun _ => scale second (pure 2))

/-- Choice adds route weights and sequencing multiplies edge weights. -/
theorem routes_sem (direct first second : K) :
    routes direct first second = scale (direct + first * second) (pure 2) := by
  rw [routes, scale_bind, Weighted.pure_bind]
  funext i
  simp only [Pi.add_apply, scale_apply, add_mul, mul_assoc]

/-- The generic coupling logic certifies the route-collapsing transformation. -/
theorem routes_coupled (direct first second : K) :
    Coupled Eq (routes direct first second) (scale (direct + first * second) (pure 2)) :=
  coupled_eq_iff.mpr (routes_sem direct first second)

theorem routes_mass (direct first second : K) :
    mass (routes direct first second) = direct + first * second := by
  rw [routes_sem, mass_scale, mass_pure, mul_one]

theorem routes_at_destination (direct first second : K) :
    routes direct first second 2 = direct + first * second := by
  rw [routes_sem]
  simp

theorem routes_elsewhere (direct first second : K) {i : ℕ} (hi : i ≠ 2) :
    routes direct first second i = 0 := by
  rw [routes_sem]
  simp [hi]

end Routes

/-- Both alternatives reach the target; Boolean choice forgets multiplicity. -/
theorem boolean_routes : Reachability.holds (routes (1 : Reachability) 1 1 2) := by
  rw [routes_at_destination]
  exact Or.inl True.intro

/-- The two distinct routes have total trace count two. -/
theorem counting_routes : routes (1 : ℕ∞) 1 1 2 = 2 := by
  rw [routes_at_destination]
  norm_num

/-- A direct quarter-weight route and two half-weight steps have total weight one half. -/
theorem probability_routes : routes (1 / 4 : ℝ≥0∞) (1 / 2) (1 / 2) 2 = 1 / 2 := by
  rw [routes_at_destination]
  have hquarter : (1 / 2 : ℝ≥0∞) / 2 = 1 / 4 := by
    simp only [div_eq_mul_inv, one_mul]
    rw [← ENNReal.mul_inv (a := 2) (b := 2) (Or.inl (by norm_num))
      (Or.inl (by norm_num))]
    norm_num
  rw [← hquarter]
  simpa only [div_eq_mul_inv, one_mul] using ENNReal.add_halves (1 / 2 : ℝ≥0∞)

/-- The two-edge route costs 2+3, beating the direct edge of cost 7. -/
theorem tropical_routes :
    Cost.value (routes (Cost.ofValue 7) (Cost.ofValue 2) (Cost.ofValue 3) 2) = 5 := by
  rw [routes_at_destination]
  norm_num

/-- The common loop proof specializes to certain reachability. -/
theorem boolean_countdown (n : ℕ) : countdown (1 : Reachability) n = Weighted.pure 0 := by
  rw [countdown_sem]
  funext i
  simp

/-- Two distinguishable choices at each iteration give exactly `2^n` traces. -/
theorem counting_countdown (n : ℕ) : mass (countdown (2 : ℕ∞) n) = 2 ^ n :=
  countdown_mass 2 n

/-- Weight two really is the sum of two distinguishable unit-weight branches. -/
theorem counting_countdown_step (n : ℕ) :
    countdownStep (2 : ℕ∞) n =
      (Weighted.pure (n - 1) : Weighted.Weight ℕ∞ ℕ) + Weighted.pure (n - 1) := by
  funext i
  simp only [countdownStep, scale_apply, Pi.add_apply, two_mul]

/-- A repeated weighted test contributes one factor of `q` per iteration. -/
theorem probability_countdown (q : ℝ≥0∞) (n : ℕ) : mass (countdown q n) = q ^ n :=
  countdown_mass q n

/-- Unit-or-less test weights remain a subprobability in this loop. -/
theorem probability_countdown_subprob (q : ℝ≥0∞) (hq : q ≤ 1) (n : ℕ) :
    mass (countdown q n) ≤ 1 := by
  rw [countdown_mass]
  exact pow_le_one₀ zero_le hq

/-- Tropical multiplication accumulates the numerical cost of all iterations. -/
theorem tropical_countdown (d : ℝ≥0∞) (n : ℕ) :
    Cost.value (mass (countdown (Cost.ofValue d) n)) = n • d := by
  rw [countdown_mass]
  exact Tropical.untrop_pow (Tropical.trop d) n

/-- Dropping an alternative preserves reachable answers in the Boolean model. -/
theorem boolean_drop_route : routes (1 : Reachability) 1 1 = Weighted.pure 2 := by
  rw [routes_sem]
  have h : (1 : Reachability) + 1 * 1 = 1 := propext ⟨fun _ => True.intro, fun h => Or.inl h⟩
  rw [h]
  funext i
  simp

/-- In the counting model the same transformation still preserves support. -/
theorem counting_drop_route_same_support :
    support (routes (1 : ℕ∞) 1 1) = support (pure 2 : Weighted.Weight ℕ∞ ℕ) := by
  ext i
  by_cases hi : i = 2
  · subst i
    simp [mem_support_iff, counting_routes]
  · simp [mem_support_iff, routes_elsewhere (1 : ℕ∞) 1 1 hi, hi]

/-- Exact relational equivalence detects the lost trace despite equal supports. -/
theorem counting_drop_route_not_coupled :
    ¬ Coupled Eq (routes (1 : ℕ∞) 1 1) (pure 2) := by
  intro h
  have he := congrFun (coupled_eq_iff.mp h) 2
  rw [counting_routes] at he
  norm_num at he

/-- A reusable finite-event certificate records the lost counting weight. -/
def counting_drop_route_certificate :
    MassDeficitCert Eq (routes (1 : ℕ∞) 1 1) (Weighted.pure 2) :=
  MassDeficitCert.singletonEq 2 (by rw [counting_routes]; norm_num)

/-- Discarding the cheaper path loses minimum-cost equivalence. The scalar order
is reversed, so the numerical inequality is `5 < 7`. -/
def tropical_drop_route_certificate :
    MassDeficitCert Eq (routes (Cost.ofValue 7) (Cost.ofValue 2) (Cost.ofValue 3))
      (scale (Cost.ofValue 7) (Weighted.pure 2)) :=
  MassDeficitCert.singletonEq 2 (by
    rw [Cost.lt_iff, tropical_routes]
    norm_num)

theorem tropical_drop_route_not_coupled :
    ¬ Coupled Eq (routes (Cost.ofValue 7) (Cost.ofValue 2) (Cost.ofValue 3))
      (scale (Cost.ofValue 7) (Weighted.pure 2)) :=
  tropical_drop_route_certificate.refutes

end
end RelOL.Generic.InstanceExamples
