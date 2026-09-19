import RelationalOutcomeLogic.Prob.Loop
import RelationalOutcomeLogic.Prob.Examples

/-!
# An unbounded fair-coin retry loop

The loop retries while its state is true. It exits at false with probability one,
but every finite approximation from true omits some terminating mass.
-/

namespace RelOL.Prob

open scoped ENNReal
open Examples

noncomputable section

/-- Each retry draws a fresh fair Boolean outcome. -/
def geometricStep : Bool → Weight Bool := fun _ => fair

/-- Keep retrying until the coin produces false. -/
def geometricLoop : Bool → Weight Bool := loopSem (fun s => s = true) geometricStep

private theorem bind_fair {α : Type*} (f : Bool → Weight α) :
    Weight.bind fair f = (1 / 2 : ℝ≥0∞) • f false + (1 / 2 : ℝ≥0∞) • f true := by
  simp only [fair, half, Weight.add_bind, Weight.smul_bind, Weight.pure_bind]

theorem geometricLoop_false : geometricLoop false = Weight.pure false :=
  loopSem_neg (by decide) geometricStep

theorem geometricLoop_isSubprob (s : Bool) : Weight.IsSubprob (geometricLoop s) :=
  loopSem_isSubprob _ _ (fun _ => fair_isProbability.isSubprob) s

theorem geometricLoop_unfold :
    geometricLoop true = (1 / 2 : ℝ≥0∞) • Weight.pure false +
      (1 / 2 : ℝ≥0∞) • geometricLoop true := by
  calc
    geometricLoop true = Weight.bind fair geometricLoop :=
      loopSem_pos (g := fun s => s = true) rfl geometricStep
    _ = (1 / 2 : ℝ≥0∞) • geometricLoop false +
        (1 / 2 : ℝ≥0∞) • geometricLoop true := bind_fair geometricLoop
    _ = _ := by rw [geometricLoop_false]

/-- The only finite-mass solution of the loop's mass equation has total mass one. -/
theorem geometricLoop_isProbability : Weight.IsProbability (geometricLoop true) := by
  have hm := congrArg Weight.mass geometricLoop_unfold
  simp only [Weight.mass_add, Weight.mass_smul, Weight.mass_pure, mul_one] at hm
  have hfinite : Weight.mass (geometricLoop true) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (geometricLoop_isSubprob true) ENNReal.one_lt_top)
  have htwo : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
    simpa only [one_div] using
      ENNReal.mul_inv_cancel (a := 2) (by norm_num) (by norm_num)
  have hdouble := congrArg (fun x : ℝ≥0∞ => 2 * x) hm
  simp only [mul_add, ← mul_assoc, htwo, one_mul, two_mul] at hdouble
  exact (ENNReal.add_left_inj hfinite).mp hdouble

/-- The retry loop terminates almost surely at false. -/
theorem geometricLoop_true : geometricLoop true = Weight.pure false := by
  have htrue : geometricLoop true true = 0 :=
    loopSem_apply_eq_zero_of_guard _ _ _ rfl
  have hfalse : geometricLoop true false = 1 := by
    have hm := geometricLoop_isProbability
    simpa only [Weight.IsProbability, Weight.mass, tsum_fintype, Fintype.sum_bool,
      htrue, zero_add] using hm
  funext b
  cases b <;> simp only [htrue, hfalse, Weight.pure_apply, ↓reduceIte, Bool.true_eq_false]

/-- No finite amount of fuel captures all the terminating probability. -/
theorem geometricLoop_iter_mass_lt_one (n : ℕ) :
    Weight.mass (loopIter (fun s => s = true) geometricStep n true) < 1 := by
  induction n with
  | zero => simp only [loopIter_zero, Weight.mass_zero, zero_lt_one]
  | succ n ih =>
    rw [loopIter_succ_pos (g := fun s => s = true) rfl]
    change Weight.mass (Weight.bind fair (loopIter (fun s => s = true) geometricStep n)) < 1
    rw [bind_fair, Weight.mass_add, Weight.mass_smul, Weight.mass_smul]
    have hleft : (1 / 2 : ℝ≥0∞) *
        Weight.mass (loopIter (fun s => s = true) geometricStep n false) ≤ 1 / 2 := by
      simpa only [mul_one] using mul_le_mul_right
        (loopIter_isSubprob (fun s => s = true) geometricStep
          (fun _ => fair_isProbability.isSubprob) n false) (1 / 2 : ℝ≥0∞)
    have hright : (1 / 2 : ℝ≥0∞) *
        Weight.mass (loopIter (fun s => s = true) geometricStep n true) < 1 / 2 := by
      simpa only [mul_one] using
        ENNReal.mul_lt_mul_right (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞) ih
    calc
      _ ≤ 1 / 2 + (1 / 2 : ℝ≥0∞) *
          Weight.mass (loopIter (fun s => s = true) geometricStep n true) :=
        add_le_add hleft le_rfl
      _ < (1 / 2 : ℝ≥0∞) + 1 / 2 := ENNReal.add_lt_add_left (by norm_num) hright
      _ = 1 := ENNReal.add_halves 1

end

end RelOL.Prob
