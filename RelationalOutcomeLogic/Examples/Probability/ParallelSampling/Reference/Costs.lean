import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Reference.Rejection
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Proposal counts of actual rejection loops

A retry counter is part of the operational state. The geometric law is proved
from the least-fixed-point loop, then used to calculate the expected proposals
for an entire accepted population. Costs count proposals, not elapsed time.
-/
namespace RelOL.Prob.ParallelSampling

open scoped ENNReal
universe u
variable {α : Type u}
noncomputable section

/-- Failed proposals increment the counter; success records its accepted value. -/
def countedTrial (law : Weight (Job α)) (s : Nat × Option α) : Weight (Nat × Option α) :=
  Weight.bind law fun j =>
    Weight.pure (if j.accepted then (s.1, some j.value) else (s.1 + 1, none))

def countedRetry (law : Weight (Job α)) : (Nat × Option α) → Weight (Nat × Option α) :=
  loopSem (fun s => s.2 = none) (countedTrial law)

lemma countedTrial_decomposition (law : Weight (Job α)) (s : Nat × Option α) :
    countedTrial law s = rejection law • Weight.pure (s.1 + 1, none) +
      Weight.bind (acceptedWeight law) (fun a => Weight.pure (s.1, some a)) := by
  have hc : (fun j : Job α => Weight.bind
      (if j.accepted then Weight.pure j.value else 0 : Weight α)
      (fun a => Weight.pure (s.1, some a))) =
      (fun j => if j.accepted then Weight.pure (s.1, some j.value) else 0) := by
    funext j
    cases j.accepted <;> simp
  rw [acceptedWeight, Weight.bind_assoc, hc]
  funext o
  simp only [countedTrial, Weight.bind_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    rejection, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply tsum_congr
  intro j
  cases j.accepted <;> simp

@[simp] lemma countedRetry_some (law : Weight (Job α)) (k : Nat) (a : α) :
    countedRetry law (k, some a) = Weight.pure (k, some a) :=
  loopSem_neg (by simp) _

lemma countedRetry_unfold (law : Weight (Job α)) (k : Nat) :
    countedRetry law (k, none) = rejection law • countedRetry law (k + 1, none) +
      Weight.bind (acceptedWeight law) (fun a => Weight.pure (k, some a)) := by
  calc
    countedRetry law (k, none) =
        Weight.bind (countedTrial law (k, none)) (countedRetry law) :=
      loopSem_pos (g := fun s : Nat × Option α => s.2 = none) rfl _
    _ = _ := by
      rw [countedTrial_decomposition, Weight.add_bind, Weight.smul_bind,
        Weight.pure_bind, Weight.bind_assoc]
      simp only [Weight.pure_bind, countedRetry_some]

lemma countedRetry_apply_none (law : Weight (Job α)) (s : Nat × Option α) (k : Nat) :
    countedRetry law s (k, none) = 0 :=
  loopSem_apply_eq_zero_of_guard _ _ _ rfl

lemma countedRetry_apply_of_lt (law : Weight (Job α)) (k m : Nat) (hm : m < k)
    (o : Option α) : countedRetry law (k, none) (m, o) = 0 := by
  by_contra h
  have hinv := loopSem_support_invariant (fun s : Nat × Option α => s.2 = none)
    (countedTrial law) (fun s => k ≤ s.1) (s := (k, none)) ?_ (by omega) (m, o) h
  · omega
  · intro s hs _ t ht
    obtain ⟨j, _, hj⟩ := (Weight.mem_support_bind_iff _ _ _).mp ht
    rw [Weight.support_pure, Set.mem_singleton_iff] at hj
    subst t
    cases j.accepted <;> simpa using hs.trans (by omega)

/-- The exact geometric waiting law is derived from the operational loop. -/
lemma countedRetry_apply (law : Weight (Job α)) (k d : Nat) (a : α) :
    countedRetry law (k, none) (k + d, some a) =
      rejection law ^ d * acceptedWeight law a := by
  classical
  induction d generalizing k with
  | zero =>
      have h := congrFun (countedRetry_unfold law k) (k, some a)
      simpa [countedRetry_apply_of_lt law (k + 1) k (by omega), Weight.bind, Weight.pure]
        using h
  | succ d ih =>
      have h := congrFun (countedRetry_unfold law k) (k + (d + 1), some a)
      have hne : k + (d + 1) ≠ k := by omega
      have hne2 : k + 1 + d ≠ k := by omega
      have hcount : k + (d + 1) = (k + 1) + d := by omega
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Weight.bind, Weight.pure,
        Prod.mk.injEq, hne, hne2, hcount, ih, pow_succ', mul_assoc] using h

/-- Observe failed-proposal count and accepted value from the real counted loop. -/
def waiting (law : Weight (Job α)) : Weight (Nat × α) :=
  Weight.bind (countedRetry law (0, none)) (fun s => match s.2 with
    | none => 0
    | some a => Weight.pure (s.1, a))

lemma waiting_apply (law : Weight (Job α)) (k : Nat) (a : α) :
    waiting law (k, a) = rejection law ^ k * acceptedWeight law a := by
  classical
  rw [waiting, Weight.bind_apply]
  calc
    _ = countedRetry law (0, none) (k, some a) := by
      rw [tsum_eq_single (k, some a)]
      · simp
      · rintro ⟨m, o⟩ hne
        cases o with
        | none => simp
        | some b =>
            have hne' : (k, a) ≠ (m, b) := by
              intro h
              cases h
              exact hne rfl
            simp [Weight.pure, hne']
    _ = _ := by simpa using countedRetry_apply law 0 k a

lemma rejection_complement (law : Weight (Job α)) (hlaw : Weight.IsProbability law) :
    1 - rejection law = acceptance law := by
  apply ENNReal.sub_eq_of_eq_add
    (ne_of_lt ((rejection_le_one law hlaw).trans_lt ENNReal.one_lt_top))
  exact ((acceptance_add_rejection law).trans hlaw).symm

lemma waiting_probability (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) : Weight.IsProbability (waiting law) := by
  rw [Weight.IsProbability, Weight.mass, ENNReal.tsum_prod']
  simp only [waiting_apply, ENNReal.tsum_mul_left]
  change (∑' k, rejection law ^ k * acceptance law) = 1
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, rejection_complement law hlaw]
  exact ENNReal.inv_mul_cancel ha.ne'
    (ne_of_lt ((acceptance_le_one law hlaw).trans_lt ENNReal.one_lt_top))

lemma waiting_value (law : Weight (Job α)) (hlaw : Weight.IsProbability law) :
    pushforward Prod.snd (waiting law) = conditional law := by
  rw [pushforward_snd]
  funext a
  change (∑' k, waiting law (k, a)) = _
  simp only [waiting_apply, ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    rejection_complement law hlaw, conditional, Pi.smul_apply, smul_eq_mul]

private lemma geometric_first_moment (q : ℝ≥0∞) :
    (∑' k : Nat, q ^ k * (k + 1 : Nat)) = (1 - q)⁻¹ * (1 - q)⁻¹ := by
  rw [← ENNReal.tsum_geometric]
  have hcauchy : (∑' n : Nat, q ^ n) * (∑' n : Nat, q ^ n) =
      ∑' n : Nat, ∑ p ∈ Finset.antidiagonal n, q ^ p.1 * q ^ p.2 := by
    calc
      _ = ∑' p : Nat × Nat, q ^ p.1 * q ^ p.2 := by
        simp only [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      _ = _ := by
        rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
          (fun p : Nat × Nat => q ^ p.1 * q ^ p.2), ENNReal.tsum_sigma']
        apply tsum_congr
        intro n
        simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
          tsum_fintype]
        exact Finset.sum_finset_coe (fun p : Nat × Nat => q ^ p.1 * q ^ p.2) _
  rw [hcauchy]
  apply tsum_congr
  intro k
  calc
    q ^ k * (k + 1 : Nat) = ∑ _p ∈ Finset.antidiagonal k, q ^ k := by
      simp [Finset.Nat.card_antidiagonal, nsmul_eq_mul, mul_comm]
    _ = _ := Finset.sum_congr rfl fun p hp => by
      rw [← pow_add, Finset.mem_antidiagonal.mp hp]

/-- Expected proposals through the first acceptance, derived from the counted loop. -/
theorem waiting_expected_proposals (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law) :
    Weight.expectation (waiting law) (fun p => (p.1 + 1 : Nat)) =
      (acceptance law)⁻¹ := by
  rw [Weight.expectation, ENNReal.tsum_prod']
  simp only [waiting_apply]
  calc
    (∑' k, ∑' a, rejection law ^ k * acceptedWeight law a * (k + 1 : Nat)) =
        (∑' k, rejection law ^ k * (k + 1 : Nat)) * acceptance law := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro k
      change (∑' a, rejection law ^ k * acceptedWeight law a * (k + 1 : Nat)) =
        (rejection law ^ k * (k + 1 : Nat)) * ∑' a, acceptedWeight law a
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro a
      ac_rfl
    _ = (acceptance law)⁻¹ := by
      rw [geometric_first_moment, rejection_complement law hlaw, mul_assoc,
        ENNReal.inv_mul_cancel ha.ne'
          (ne_of_lt ((acceptance_le_one law hlaw).trans_lt ENNReal.one_lt_top)), mul_one]

/-- Sequentially compose actual counted retry loops, retaining total proposal work. -/
def countedPopulation (law : Weight (Job α)) : Nat → Weight (Nat × List α)
  | 0 => Weight.pure (0, [])
  | n + 1 => Weight.bind (waiting law) fun p =>
      Weight.bind (countedPopulation law n) fun rest =>
        Weight.pure (p.1 + 1 + rest.1, p.2 :: rest.2)

theorem countedPopulation_probability (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law) (n : Nat) :
    Weight.IsProbability (countedPopulation law n) := by
  induction n with
  | zero => exact Weight.isProbability_pure _
  | succ n ih =>
      exact (waiting_probability law hlaw ha).bind
        (fun _ => ih.bind (fun _ => Weight.isProbability_pure _))

/-- The total number of proposals through the nth acceptance has mean n/a. -/
theorem countedPopulation_expected_proposals (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law) (n : Nat) :
    Weight.expectation (countedPopulation law n) (fun p => p.1) =
      n / acceptance law := by
  induction n with
  | zero => simp [countedPopulation]
  | succ n ih =>
      have hn : Weight.mass (countedPopulation law n) = 1 :=
        countedPopulation_probability law hlaw ha n
      have hw : Weight.mass (waiting law) = 1 := waiting_probability law hlaw ha
      have hi (p : Nat × α) :
          Weight.expectation (countedPopulation law n)
            (fun rest => (p.1 + 1 + rest.1 : Nat)) =
          (p.1 + 1 : Nat) + n / acceptance law := by
        simp only [Nat.cast_add]
        rw [Weight.expectation_add_cost, Weight.expectation_const, hn, one_mul, ih]
      rw [countedPopulation, Weight.expectation_bind]
      simp_rw [Weight.expectation_bind, Weight.expectation_pure, hi]
      rw [Weight.expectation_add_cost, waiting_expected_proposals law hlaw ha,
        Weight.expectation_const, hw, one_mul]
      simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, add_mul, one_mul]
      exact add_comm _ _

/-- Counting proposals preserves the complete accepted-population law. -/
theorem countedPopulation_value (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law) (n : Nat) :
    pushforward Prod.snd (countedPopulation law n) = population law n := by
  induction n with
  | zero => simp [countedPopulation, population]
  | succ n ih =>
      simp only [countedPopulation, population, pushforward_bind, pushforward_pure]
      have hc (p : Nat × α) :
          Weight.bind (countedPopulation law n) (fun rest => Weight.pure (p.2 :: rest.2)) =
          Weight.bind (population law n) (fun xs => Weight.pure (p.2 :: xs)) := by
        rw [← ih, bind_pushforward]
      simp only [hc]
      rw [← bind_pushforward Prod.snd (waiting law)
        (fun a => Weight.bind (population law n) (fun xs => Weight.pure (a :: xs))),
        waiting_value law hlaw,
        sample_eq_conditional law hlaw ha]

/-- First-proposal decomposition of the operational waiting law. -/
theorem waiting_recursion (law : Weight (Job α)) :
    waiting law = Weight.bind (acceptedWeight law) (fun a => Weight.pure (0, a)) +
      rejection law • pushforward (fun p : Nat × α => (p.1 + 1, p.2)) (waiting law) := by
  classical
  funext p
  rcases p with ⟨k, a⟩
  cases k with
  | zero =>
      simp [waiting_apply, pushforward, Weight.bind, Weight.pure]
  | succ k =>
      simp only [waiting_apply, pushforward, Weight.bind, Weight.pure, ENNReal.tsum_prod',
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.mk.injEq,
        Nat.succ_ne_zero, false_and, ↓reduceIte, mul_zero, tsum_zero,
        zero_add, Nat.add_right_cancel_iff, pow_succ', mul_assoc, mul_ite,
        mul_one, ite_and]
      apply congrArg (fun x => rejection law * x)
      symm
      rw [tsum_eq_single k]
      · simp
      · intro i hi
        simp [Ne.symm hi]

end
end RelOL.Prob.ParallelSampling
