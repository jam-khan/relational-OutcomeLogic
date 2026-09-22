import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Outcomes
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Reference.Costs

/-! # Proposal work before a cap

The reference bound is uniform in the cap. Combined with the coupling's
pathwise accounting it bounds actual launched proposals, including discarded
speculation. No claim about makespan is made.
-/

namespace RelOL.Prob.ParallelSampling
open scoped ENNReal
universe u
variable {α : Type u}
noncomputable section

def prefixWork (law : Weight (Job α)) (cap quota : Nat) : ℝ≥0∞ :=
  Weight.expectation (draws law cap) (fun js => used quota js)

theorem expectation_acceptance_split (law : Weight (Job α)) (x y : ℝ≥0∞) :
    Weight.expectation law (fun j => if j.accepted then x else y) =
      acceptance law * x + rejection law * y := by
  rw [Weight.expectation, acceptance_eq, rejection,
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply tsum_congr
  intro j
  cases j.accepted <;> simp

theorem prefixWork_zero_quota (law : Weight (Job α)) (cap : Nat) :
    prefixWork law cap 0 = 0 := by simp [prefixWork, used, Weight.expectation]

theorem prefixWork_succ (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (cap quota : Nat) :
    prefixWork law (cap + 1) (quota + 1) =
      1 + acceptance law * prefixWork law cap quota +
        rejection law * prefixWork law cap (quota + 1) := by
  have hm : Weight.mass (draws law cap) = 1 := draws_probability law hlaw cap
  have hi (j : Job α) :
      Weight.expectation (draws law cap) (fun js =>
        (1 + if j.accepted then used quota js else used (quota + 1) js : Nat)) =
      1 + if j.accepted then prefixWork law cap quota else prefixWork law cap (quota + 1) := by
    cases hj : j.accepted <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one,
        Weight.expectation_add_cost, Weight.expectation_const, hm, one_mul, prefixWork]
  simp only [prefixWork, draws, Weight.expectation_bind, Weight.expectation_pure,
    used]
  change Weight.expectation law (fun j => Weight.expectation (draws law cap)
    (fun js => (1 + if j.accepted then used quota js else used (quota + 1) js : Nat))) = _
  simp_rw [hi]
  rw [Weight.expectation_add_cost, Weight.expectation_const, hlaw, one_mul,
    expectation_acceptance_split]
  exact (add_assoc _ _ _).symm

theorem prefixWork_le (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (cap quota : Nat) :
    prefixWork law cap quota ≤ quota / acceptance law := by
  have hc : acceptance law * (acceptance law)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel ha.ne'
      (ne_of_lt ((acceptance_le_one law hlaw).trans_lt ENNReal.one_lt_top))
  have hp : acceptance law + rejection law = 1 := (acceptance_add_rejection law).trans hlaw
  induction cap generalizing quota with
  | zero => cases quota <;> simp [prefixWork, draws, used]
  | succ cap ih =>
    cases quota with
    | zero => rw [prefixWork_zero_quota]; exact bot_le
    | succ n =>
      rw [prefixWork_succ law hlaw]
      calc
        1 + acceptance law * prefixWork law cap n +
            rejection law * prefixWork law cap (n + 1) ≤
            1 + acceptance law * (n / acceptance law) +
              rejection law * ((n + 1 : Nat) / acceptance law) := by
          exact add_le_add (add_le_add_right (mul_le_mul_right (ih n) _) _)
            (mul_le_mul_right (ih (n + 1)) _)
        _ = (acceptance law + rejection law) * ((n + 1 : Nat) / acceptance law) := by
          simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one]
          calc
            1 + acceptance law * (n * (acceptance law)⁻¹) +
                rejection law * ((n + 1) * (acceptance law)⁻¹) =
                acceptance law * (acceptance law)⁻¹ +
                  acceptance law * (n * (acceptance law)⁻¹) +
                    rejection law * ((n + 1) * (acceptance law)⁻¹) := by rw [hc]
            _ = _ := by ring
        _ = _ := by rw [hp, one_mul]

theorem referenceRecord_expected_proposals (law : Weight (Job α)) (cap quota : Nat) :
    Weight.expectation (referenceRecord law cap quota) (fun r => r.2) =
      prefixWork law cap quota := by
  simp [referenceRecord, pushforward, Weight.expectation_bind, prefixWork]

theorem scheduledPrefix_expected_started_le (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law)
    (workers window quota cap : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    Weight.expectation (scheduledPrefix law workers window quota cap) (fun p => p.started) ≤
      quota / acceptance law + (window - 1 : Nat) := by
  apply (scheduledPrefix_expected_started law hlaw workers window quota cap hworkers hwindow).trans
  rw [referenceRecord_expected_proposals]
  exact add_le_add_left (prefixWork_le law hlaw ha cap quota) _

end
end RelOL.Prob.ParallelSampling
