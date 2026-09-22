import RelationalOutcomeLogic.Prob.Coupling.Observation

/-!
# Exact speculative acceptance and residual correction

A proposal is sampled from `q`, accepted with probability `min (p / q) 1`,
and otherwise replaced by a sample from the normalized positive residual of `p`.
The definitions retain the acceptance flag. Theorems identify both output
subweights, not merely their sum. Zero proposal weights and zero rejection mass
are handled explicitly; no full-support assumption is imposed.
-/

namespace RelOL.Prob.Speculative

open scoped ENNReal

variable {α : Type*}

/-- An exact discrete probability distribution. -/
structure Distribution (α : Type*) where
  weight : Weight α
  normalized : Weight.IsProbability weight

namespace Distribution

theorem weight_le_one (p : Distribution α) (x : α) : p.weight x ≤ 1 :=
  (ENNReal.le_tsum x).trans_eq p.normalized

theorem weight_ne_top (p : Distribution α) (x : α) : p.weight x ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (p.weight_le_one x)

end Distribution

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The accepted output subweight. -/
def overlap (p q : Distribution α) : Weight α := fun x => min (p.weight x) (q.weight x)

/-- The target mass left after accepting the common subweight. -/
def residual (p q : Distribution α) : Weight α := fun x => p.weight x - overlap p q x

/-- The proposal mass rejected by the acceptance test. -/
def rejectedProposal (p q : Distribution α) : Weight α :=
  fun x => q.weight x - overlap p q x

def acceptanceMass (p q : Distribution α) : ℝ≥0∞ := Weight.mass (overlap p q)

def rejectionMass (p q : Distribution α) : ℝ≥0∞ := Weight.mass (residual p q)

theorem overlap_add_residual (p q : Distribution α) :
    overlap p q + residual p q = p.weight := by
  funext x
  exact add_tsub_cancel_of_le (min_le_left _ _)

theorem overlap_add_rejectedProposal (p q : Distribution α) :
    overlap p q + rejectedProposal p q = q.weight := by
  funext x
  exact add_tsub_cancel_of_le (min_le_right _ _)

theorem acceptance_add_rejection (p q : Distribution α) :
    acceptanceMass p q + rejectionMass p q = 1 := by
  rw [acceptanceMass, rejectionMass, ← Weight.mass_add, overlap_add_residual]
  exact p.normalized

theorem acceptanceMass_le_one (p q : Distribution α) : acceptanceMass p q ≤ 1 :=
  le_add_right (le_refl _) |>.trans_eq (acceptance_add_rejection p q)

theorem rejectionMass_le_one (p q : Distribution α) : rejectionMass p q ≤ 1 :=
  le_add_left (le_refl _) |>.trans_eq (acceptance_add_rejection p q)

theorem mass_rejectedProposal (p q : Distribution α) :
    Weight.mass (rejectedProposal p q) = rejectionMass p q := by
  apply (ENNReal.add_right_inj
    (ne_top_of_le_ne_top ENNReal.one_ne_top (acceptanceMass_le_one p q))).mp
  change Weight.mass (overlap p q) + _ = acceptanceMass p q + _
  rw [← Weight.mass_add, overlap_add_rejectedProposal, q.normalized,
    acceptance_add_rejection]

/-- Acceptance is arbitrary on impossible proposal values; choosing one keeps
the conditional verifier normalized on every input. -/
def accept (p q : Distribution α) (x : α) : ℝ≥0∞ :=
  if q.weight x = 0 then 1 else overlap p q x / q.weight x

theorem accept_le_one (p q : Distribution α) (x : α) : accept p q x ≤ 1 := by
  unfold accept
  split
  · exact le_rfl
  · exact (ENNReal.div_le_div_right (min_le_right _ _) _).trans ENNReal.div_self_le_one

/-- On possible proposals this is the usual clipped probability ratio. -/
theorem accept_eq_min_ratio (p q : Distribution α) (x : α) (hq : q.weight x ≠ 0) :
    accept p q x = min (p.weight x / q.weight x) 1 := by
  by_cases h : p.weight x ≤ q.weight x
  · have hd : p.weight x / q.weight x ≤ 1 := by
      simpa only [ENNReal.div_self hq (q.weight_ne_top x)] using
        ENNReal.div_le_div_right h (q.weight x)
    simp only [accept, if_neg hq, overlap, min_eq_left h, min_eq_left hd]
  · have h' : q.weight x ≤ p.weight x := le_of_not_ge h
    have hd : 1 ≤ p.weight x / q.weight x := by
      simpa only [ENNReal.div_self hq (q.weight_ne_top x)] using
        ENNReal.div_le_div_right h' (q.weight x)
    simp only [accept, if_neg hq, overlap, min_eq_right h',
      ENNReal.div_self hq (q.weight_ne_top x), min_eq_right hd]

theorem proposal_mul_accept (p q : Distribution α) (x : α) :
    q.weight x * accept p q x = overlap p q x := by
  by_cases h : q.weight x = 0
  · simp [accept, h, overlap]
  · simp only [accept, if_neg h]
    exact ENNReal.mul_div_cancel h (q.weight_ne_top x)

theorem proposal_mul_reject (p q : Distribution α) (x : α) :
    q.weight x * (1 - accept p q x) = rejectedProposal p q x := by
  rw [ENNReal.mul_sub (fun _ _ => q.weight_ne_top x), mul_one, proposal_mul_accept]
  rfl

/-- Normalize the residual only when rejection has positive mass. When its mass
is zero, `p` supplies a harmless normalized continuation for an unreachable branch. -/
def correction (p q : Distribution α) : Weight α :=
  if rejectionMass p q = 0 then p.weight
  else (rejectionMass p q)⁻¹ • residual p q

theorem correction_isProbability (p q : Distribution α) :
    Weight.IsProbability (correction p q) := by
  unfold correction
  split
  · exact p.normalized
  · rename_i h
    rw [Weight.IsProbability, Weight.mass_smul]
    exact ENNReal.inv_mul_cancel h
      (ne_top_of_le_ne_top ENNReal.one_ne_top (rejectionMass_le_one p q))

theorem rejection_smul_correction (p q : Distribution α) :
    rejectionMass p q • correction p q = residual p q := by
  by_cases h : rejectionMass p q = 0
  · have hz : residual p q = 0 := (Weight.mass_eq_zero_iff _).mp h
    simp [h, hz]
  · funext x
    simp only [correction, if_neg h, Pi.smul_apply, smul_eq_mul]
    exact ENNReal.mul_inv_cancel_left h
      (ne_top_of_le_ne_top ENNReal.one_ne_top (rejectionMass_le_one p q))

/-- The actual conditional acceptance test, followed on rejection by residual
sampling. `true` records that the proposal was accepted. -/
def verify (p q : Distribution α) (x : α) : Weight (Bool × α) :=
  accept p q x • Weight.pure (true, x) +
    (1 - accept p q x) • pushforward (fun y => (false, y)) (correction p q)

theorem verify_isProbability (p q : Distribution α) (x : α) :
    Weight.IsProbability (verify p q x) := by
  rw [Weight.IsProbability, verify, Weight.mass_add, Weight.mass_smul,
    Weight.mass_smul, Weight.mass_pure, mass_pushforward, correction_isProbability,
    mul_one, mul_one]
  exact add_tsub_cancel_of_le (accept_le_one p q x)

/-- Draw a proposal and run its conditional verifier. -/
def step (p q : Distribution α) : Weight (Bool × α) :=
  Weight.bind q.weight (verify p q)

theorem step_isProbability (p q : Distribution α) : Weight.IsProbability (step p q) :=
  q.normalized.bind (verify_isProbability p q)

theorem verify_apply_true (p q : Distribution α) (x y : α) :
    verify p q x (true, y) = if y = x then accept p q x else 0 := by
  classical
  simp [verify, pushforward, Weight.bind, Weight.pure, mul_ite]

theorem verify_apply_false (p q : Distribution α) (x y : α) :
    verify p q x (false, y) = (1 - accept p q x) * correction p q y := by
  classical
  simp [verify, pushforward, Weight.bind, Weight.pure, mul_ite]

/-- An accepted outcome is the proposed token itself. -/
theorem verify_accepts_same (p q : Distribution α) (x y : α)
    (h : verify p q x (true, y) ≠ 0) : y = x := by
  by_contra hne
  exact h (by simp [verify_apply_true, hne])

theorem step_apply_true (p q : Distribution α) (x : α) :
    step p q (true, x) = overlap p q x := by
  classical
  simp only [step, Weight.bind, verify_apply_true, mul_ite, mul_zero]
  rw [tsum_eq_single x]
  · simpa using proposal_mul_accept p q x
  · intro y hy
    simp [Ne.symm hy]

theorem step_apply_false (p q : Distribution α) (x : α) :
    step p q (false, x) = residual p q x := by
  simp only [step, Weight.bind, verify_apply_false, ← mul_assoc, proposal_mul_reject]
  rw [ENNReal.tsum_mul_right]
  change Weight.mass (rejectedProposal p q) * correction p q x = _
  rw [mass_rejectedProposal]
  exact congrFun (rejection_smul_correction p q) x

/-- Discarding the acceptance flag gives exactly the target distribution. -/
theorem step_output (p q : Distribution α) :
    pushforward Prod.snd (step p q) = p.weight := by
  rw [pushforward_snd]
  funext x
  simp only [margR, tsum_bool, step_apply_true, step_apply_false]
  simpa only [Pi.add_apply, add_comm] using congrFun (overlap_add_residual p q) x

theorem step_acceptance_mass (p q : Distribution α) :
    Weight.mass (fun x => step p q (true, x)) = acceptanceMass p q := by
  simp only [step_apply_true, acceptanceMass]

theorem step_rejection_mass (p q : Distribution α) :
    Weight.mass (fun x => step p q (false, x)) = rejectionMass p q := by
  simp only [step_apply_false, rejectionMass]

@[simp] theorem overlap_self (p : Distribution α) : overlap p p = p.weight := by
  funext x
  simp [overlap]

@[simp] theorem residual_self (p : Distribution α) : residual p p = 0 := by
  funext x
  simp [residual, overlap]

@[simp] theorem rejectionMass_self (p : Distribution α) : rejectionMass p p = 0 := by
  simp [rejectionMass]

@[simp] theorem acceptanceMass_self (p : Distribution α) : acceptanceMass p p = 1 := by
  simpa [acceptanceMass, Weight.IsProbability] using p.normalized

@[simp] theorem accept_self (p : Distribution α) (x : α) : accept p p x = 1 := by
  by_cases hx : p.weight x = 0
  · simp [accept, hx]
  · simp [accept, hx, overlap, ENNReal.div_self hx (p.weight_ne_top x)]

@[simp] theorem verify_self (p : Distribution α) (x : α) :
    verify p p x = Weight.pure (true, x) := by
  simp [verify]

/-- Identical draft and target distributions never reject. -/
theorem step_self (p : Distribution α) :
    step p p = pushforward (fun x => (true, x)) p.weight := by
  classical
  funext bx
  rcases bx with ⟨b, x⟩
  cases b <;> simp [step_apply_true, step_apply_false, pushforward, Weight.bind,
    Weight.pure, mul_ite]

end

end RelOL.Prob.Speculative
