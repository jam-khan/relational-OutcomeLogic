import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Model
import RelationalOutcomeLogic.Prob.Semantics.Loop
import RelationalOutcomeLogic.Algebra.ENNReal.Expectation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uncapped sequential rejection sampling

The reference uses the library's least-fixed-point loop semantics. Its accepted
law is obtained from the actual retry loop, including its termination mass;
positive acceptance is the only extra assumption needed. Runtime may depend on
both the acceptance decision and returned value.
-/

namespace RelOL.Prob.ParallelSampling

open scoped ENNReal
universe u
variable {α : Type u}
noncomputable section

/-- Subdistribution of accepted values in one proposal. -/
def acceptedWeight (law : Weight (Job α)) : Weight α :=
  Weight.bind law fun j => if j.accepted then Weight.pure j.value else 0

/-- Acceptance probability of one fresh proposal. -/
def acceptance (law : Weight (Job α)) : ℝ≥0∞ := Weight.mass (acceptedWeight law)

/-- Rejected proposal mass. -/
def rejection (law : Weight (Job α)) : ℝ≥0∞ :=
  ∑' j, if j.accepted then 0 else law j

/-- The conditional accepted-value law. -/
def conditional (law : Weight (Job α)) : Weight α :=
  (acceptance law)⁻¹ • acceptedWeight law

/-- A retry is represented by `none`; an accepted value exits at `some value`. -/
def trial (law : Weight (Job α)) : Weight (Option α) :=
  Weight.bind law fun j => Weight.pure (if j.accepted then some j.value else none)

lemma acceptance_eq (law : Weight (Job α)) :
    acceptance law = ∑' j, if j.accepted then law j else 0 := by
  rw [acceptance, acceptedWeight, Weight.mass_bind]
  apply tsum_congr
  intro j
  cases j.accepted <;> simp

lemma acceptance_add_rejection (law : Weight (Job α)) :
    acceptance law + rejection law = Weight.mass law := by
  rw [acceptance_eq, rejection, ← ENNReal.tsum_add]
  apply tsum_congr
  intro j
  cases j.accepted <;> simp

lemma acceptance_le_one (law : Weight (Job α)) (hlaw : Weight.IsProbability law) :
    acceptance law ≤ 1 := by
  calc
    acceptance law ≤ acceptance law + rejection law := le_self_add
    _ = 1 := (acceptance_add_rejection law).trans hlaw

lemma rejection_le_one (law : Weight (Job α)) (hlaw : Weight.IsProbability law) :
    rejection law ≤ 1 := by
  calc
    rejection law ≤ acceptance law + rejection law := le_add_self
    _ = 1 := (acceptance_add_rejection law).trans hlaw

lemma conditional_probability (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) : Weight.IsProbability (conditional law) := by
  rw [Weight.IsProbability, conditional, Weight.mass_smul]
  exact ENNReal.inv_mul_cancel ha.ne' (ne_of_lt ((acceptance_le_one law hlaw).trans_lt
    ENNReal.one_lt_top))

lemma trial_probability (law : Weight (Job α)) (hlaw : Weight.IsProbability law) :
    Weight.IsProbability (trial law) := by
  apply Weight.IsProbability.bind hlaw
  intro j
  exact Weight.isProbability_pure _

lemma trial_decomposition (law : Weight (Job α)) :
    trial law = rejection law • Weight.pure none +
      Weight.bind (acceptedWeight law) (fun a => Weight.pure (some a)) := by
  have hc : (fun j : Job α => Weight.bind
      (if j.accepted then Weight.pure j.value else 0 : Weight α)
      (fun a => Weight.pure (some a))) =
      (fun j => if j.accepted then Weight.pure (some j.value) else 0) := by
    funext j
    cases j.accepted <;> simp
  rw [acceptedWeight, Weight.bind_assoc, hc]
  funext o
  simp only [trial, Weight.bind_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, rejection,
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply tsum_congr
  intro j
  cases j.accepted <;> simp

/-- This is an actual unbounded loop, not a stipulated conditional distribution. -/
def retry (law : Weight (Job α)) : Option α → Weight (Option α) :=
  loopSem (fun s => s = none) (fun _ => trial law)

@[simp] lemma retry_some (law : Weight (Job α)) (a : α) :
    retry law (some a) = Weight.pure (some a) :=
  loopSem_neg (by simp) _

lemma retry_none_apply_none (law : Weight (Job α)) : retry law none none = 0 :=
  loopSem_apply_eq_zero_of_guard _ _ _ rfl

lemma retry_subprob (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (s : Option α) : Weight.IsSubprob (retry law s) :=
  loopSem_isSubprob _ _ (fun _ => (trial_probability law hlaw).isSubprob) s

lemma retry_unfold (law : Weight (Job α)) :
    retry law none = rejection law • retry law none +
      Weight.bind (acceptedWeight law) (fun a => Weight.pure (some a)) := by
  calc
    retry law none = Weight.bind (trial law) (retry law) :=
      loopSem_pos (g := fun s => s = none) rfl _
    _ = _ := by
      rw [trial_decomposition, Weight.add_bind, Weight.smul_bind,
        Weight.pure_bind, Weight.bind_assoc]
      simp only [Weight.pure_bind, retry_some]

/-- Solve the local retry equation using the subprobability bound. -/
lemma retry_none_apply_some (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (a : α) :
    retry law none (some a) = conditional law a := by
  classical
  have heq := congrFun (retry_unfold law) (some a)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Weight.bind_apply,
    Weight.pure_apply, Option.some.injEq, mul_ite, mul_one, mul_zero,
    tsum_ite_eq'] at heq
  have hfinite : retry law none (some a) ≠ ∞ :=
    ne_of_lt ((ENNReal.le_tsum (some a)).trans_lt
      ((retry_subprob law hlaw none).trans_lt ENNReal.one_lt_top))
  have hrfinite : rejection law ≠ ∞ :=
    ne_of_lt ((rejection_le_one law hlaw).trans_lt ENNReal.one_lt_top)
  have hparts := congrArg (fun p => p * retry law none (some a))
    ((acceptance_add_rejection law).trans hlaw)
  rw [add_mul, one_mul] at hparts
  have hcancel : acceptance law * retry law none (some a) = acceptedWeight law a := by
    apply (ENNReal.add_right_inj (ENNReal.mul_ne_top hrfinite hfinite)).mp
    calc
      rejection law * retry law none (some a) +
          acceptance law * retry law none (some a) = retry law none (some a) := by
            rw [add_comm, hparts]
      _ = _ := heq
  have h := congrArg (fun x => (acceptance law)⁻¹ * x) hcancel
  rw [← mul_assoc, ENNReal.inv_mul_cancel ha.ne'
    (ne_of_lt ((acceptance_le_one law hlaw).trans_lt ENNReal.one_lt_top)), one_mul] at h
  exact h

/-- The loop returns precisely the accepted conditional law and has no retry exits. -/
theorem retry_eq_conditional (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) :
    retry law none = Weight.bind (conditional law) (fun a => Weight.pure (some a)) := by
  classical
  funext o
  cases o with
  | none => simp [retry_none_apply_none, Weight.bind, Weight.pure]
  | some a => simpa [Weight.bind, Weight.pure] using retry_none_apply_some law hlaw ha a

/-- Almost-sure completion of one accepted draw. -/
theorem retry_probability (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) : Weight.IsProbability (retry law none) := by
  rw [retry_eq_conditional law hlaw ha]
  exact (conditional_probability law hlaw ha).bind (fun _ => Weight.isProbability_pure _)

/-- Observe the accepted value, dropping the unreachable retry marker. -/
def sample (law : Weight (Job α)) : Weight α :=
  Weight.bind (retry law none) (fun o => match o with
    | none => 0
    | some a => Weight.pure a)

theorem sample_eq_conditional (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) : sample law = conditional law := by
  rw [sample, retry_eq_conditional law hlaw ha, Weight.bind_assoc]
  simp only [Weight.pure_bind, Weight.bind_pure]

/-- A whole accepted population: each element is produced by its own uncapped retry loop. -/
def population (law : Weight (Job α)) : Nat → Weight (List α)
  | 0 => Weight.pure []
  | n + 1 => Weight.bind (sample law) fun a =>
      Weight.bind (population law n) fun xs => Weight.pure (a :: xs)

/-- The joint iid law, retaining the entire population rather than only marginals. -/
def iid (μ : Weight α) : Nat → Weight (List α)
  | 0 => Weight.pure []
  | n + 1 => Weight.bind μ fun a =>
      Weight.bind (iid μ n) fun xs => Weight.pure (a :: xs)

theorem population_eq_iid (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (n : Nat) :
    population law n = iid (conditional law) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [population, iid, sample_eq_conditional law hlaw ha, ih]

theorem population_probability (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (n : Nat) : Weight.IsProbability (population law n) := by
  have hs : Weight.IsProbability (sample law) := by
    rw [sample_eq_conditional law hlaw ha]
    exact conditional_probability law hlaw ha
  induction n with
  | zero => exact Weight.isProbability_pure _
  | succ n ih => exact hs.bind (fun _ => ih.bind (fun _ => Weight.isProbability_pure _))

end
end RelOL.Prob.ParallelSampling
