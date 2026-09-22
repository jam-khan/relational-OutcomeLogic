import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Reference.Capped
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Reference.Rejection

/-!
# Successful finite prefixes and the uncapped population law

Explicit exhausted results do not form an increasing approximation. Erasing just
those results gives a monotone sequence. Its limit is proved equal to the actual
reference population of unbounded retry loops, rather than defined to be that law.
-/

namespace RelOL.Prob.ParallelSampling
open scoped ENNReal
universe u
variable {α β : Type u}
noncomputable section

def successValues : Result α → Weight (List α)
  | .success xs => Weight.pure xs
  | .exhausted _ => 0

def successful (law : Weight (Job α)) : Nat → Nat → Weight (List α)
  | _, 0 => Weight.pure []
  | 0, _ + 1 => 0
  | m + 1, n + 1 => Weight.bind law fun j =>
      if j.accepted then pushforward (List.cons j.value) (successful law m n)
      else successful law m (n + 1)

theorem successful_eq_capped (law : Weight (Job α)) (m n : Nat) :
    successful law m n = Weight.bind (capped law m n) successValues := by
  induction m generalizing n with
  | zero => cases n <;> simp [successful, capped, successValues]
  | succ m ih =>
    cases n with
    | zero => simp [successful, capped, successValues]
    | succ n =>
      simp only [successful, capped, Weight.bind_assoc]
      congr 1
      funext j
      cases hj : j.accepted
      · simp only [Bool.false_eq_true, ↓reduceIte, ih]
      · simp only [↓reduceIte, pushforward, Weight.bind_assoc,
          Weight.pure_bind, ih]
        congr 1
        funext r
        cases r <;> simp [Result.prepend, successValues]

theorem successful_mono_succ (law : Weight (Job α)) (m n : Nat) :
    successful law m n ≤ successful law (m + 1) n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => exact le_rfl
    | succ n => exact bot_le
  | succ m ih =>
    cases n with
    | zero => exact le_rfl
    | succ n =>
      apply Weight.bind_mono_right
      intro j
      cases hj : j.accepted
      · simpa only [hj, Bool.false_eq_true, ↓reduceIte] using ih (n + 1)
      · simpa only [hj, ↓reduceIte, pushforward] using
          Weight.bind_mono_left (ih n) (fun xs => Weight.pure (j.value :: xs))

theorem successful_monotone (law : Weight (Job α)) (n : Nat) :
    Monotone (fun m => successful law m n) :=
  monotone_nat_of_le_succ (fun m => successful_mono_succ law m n)

def successfulLimit (law : Weight (Job α)) (n : Nat) : Weight (List α) :=
  ⨆ m, successful law m n

theorem successful_subprob (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (m n : Nat) : Weight.IsSubprob (successful law m n) := by
  rw [successful_eq_capped]
  apply (capped_probability law hlaw m n).isSubprob.bind
  intro r
  cases r <;> simp [successValues]

theorem successfulLimit_subprob (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (n : Nat) : Weight.IsSubprob (successfulLimit law n) :=
  Weight.IsSubprob.iSup (successful_monotone law n) (fun m => successful_subprob law hlaw m n)

/-- The primitive accept/retry split, reused at every population size. -/
theorem proposal_split (law : Weight (Job α)) (k : α → Weight β) (retry : Weight β) :
    Weight.bind law (fun j => if j.accepted then k j.value else retry) =
      rejection law • retry + Weight.bind (acceptedWeight law) k := by
  have h := congrArg (fun μ => Weight.bind μ (fun o => match o with
    | none => retry
    | some a => k a)) (trial_decomposition law)
  simp only [trial, Weight.bind_assoc, Weight.pure_bind, Weight.add_bind,
    Weight.smul_bind] at h
  rw [← h]
  congr 1
  funext j
  cases j.accepted <;> rfl

theorem successfulLimit_succ (law : Weight (Job α)) (n : Nat) :
    successfulLimit law (n + 1) =
      rejection law • successfulLimit law (n + 1) +
      Weight.bind (acceptedWeight law) (fun a =>
        pushforward (List.cons a) (successfulLimit law n)) := by
  have hshift : successfulLimit law (n + 1) = ⨆ m, successful law (m + 1) (n + 1) := by
    apply le_antisymm
    · exact iSup_le (fun m => le_iSup_of_le m (successful_mono_succ law m (n + 1)))
    · exact iSup_le (fun m => le_iSup (fun i => successful law i (n + 1)) (m + 1))
  conv_lhs => rw [hshift]
  simp only [successful]
  have hm : Monotone (fun (m : Nat) (j : Job α) => if j.accepted then
      pushforward (List.cons j.value) (successful law m n) else successful law m (n + 1)) := by
    intro i j hij x
    cases hx : x.accepted
    · simpa only [hx, Bool.false_eq_true, ↓reduceIte] using successful_monotone law (n + 1) hij
    · simpa only [hx, ↓reduceIte, pushforward] using Weight.bind_mono_left
        (successful_monotone law n hij) (fun xs => Weight.pure (x.value :: xs))
  rw [← Weight.bind_iSup_right _ _ hm]
  have hi : (⨆ m, fun j : Job α => if j.accepted then
      pushforward (List.cons j.value) (successful law m n) else successful law m (n + 1)) =
      (fun j => if j.accepted then pushforward (List.cons j.value) (successfulLimit law n)
        else successfulLimit law (n + 1)) := by
    funext j
    cases hj : j.accepted
    · simp [hj, successfulLimit]
    · simp only [hj, ↓reduceIte, iSup_apply]
      exact (pushforward_iSup _ _ (successful_monotone law n)).symm
  rw [hi]
  exact proposal_split law (fun a => pushforward (List.cons a) (successfulLimit law n))
    (successfulLimit law (n + 1))

/-- The normalized conditional law follows from a fixed-point equation and a
finite mass bound; infinite fixed points are excluded by that bound. -/
theorem solve_accept_retry (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (x z : ℝ≥0∞) (hx : x ≠ ∞)
    (heq : x = rejection law * x + z) : x = (acceptance law)⁻¹ * z := by
  have hr : rejection law ≠ ∞ := ne_of_lt ((rejection_le_one law hlaw).trans_lt ENNReal.one_lt_top)
  have hp := congrArg (fun t => t * x) ((acceptance_add_rejection law).trans hlaw)
  rw [add_mul, one_mul] at hp
  have hc : acceptance law * x = z := by
    apply (ENNReal.add_right_inj (ENNReal.mul_ne_top hr hx)).mp
    calc
      rejection law * x + acceptance law * x = x := by rw [add_comm, hp]
      _ = _ := heq
  have h := congrArg (fun t => (acceptance law)⁻¹ * t) hc
  rw [← mul_assoc, ENNReal.inv_mul_cancel ha.ne'
    (ne_of_lt ((acceptance_le_one law hlaw).trans_lt ENNReal.one_lt_top)), one_mul] at h
  exact h

theorem successfulLimit_eq_population (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law) (n : Nat) :
    successfulLimit law n = population law n := by
  induction n with
  | zero => simp [successfulLimit, successful, population]
  | succ n ih =>
    have hrec : successfulLimit law (n + 1) =
        Weight.bind (conditional law) (fun a => pushforward (List.cons a)
          (successfulLimit law n)) := by
      funext xs
      have hx : successfulLimit law (n + 1) xs ≠ ∞ :=
        ne_of_lt ((ENNReal.le_tsum xs).trans_lt
          ((successfulLimit_subprob law hlaw (n + 1)).trans_lt ENNReal.one_lt_top))
      have h := solve_accept_retry law hlaw ha _ _ hx (congrFun (successfulLimit_succ law n) xs)
      simpa only [conditional, Weight.smul_bind, Pi.smul_apply, smul_eq_mul] using h
    rw [hrec, ih, population, sample_eq_conditional law hlaw ha]
    rfl

end
end RelOL.Prob.ParallelSampling
