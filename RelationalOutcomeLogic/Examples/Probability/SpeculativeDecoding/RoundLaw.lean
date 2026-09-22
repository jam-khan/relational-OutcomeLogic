import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.OutcomeContracts
import RelationalOutcomeLogic.Prob.Logic.FiniteOutcomes

/-!
# History-dependent quantitative law of an eager speculative round

Survival weights iterate the accepted overlap, preserving its conditional history.
They need not be powers of an average acceptance probability. An actual eager
round has room for all proposals and its final correction or bonus token.
-/

namespace RelOL.Prob.Speculative.RoundLaw

open scoped ENNReal

variable {α β : Type*}

noncomputable section

/-- Histories reached after exactly `i` accepted proposals, with their unnormalized weights. -/
def acceptedPrefix (p q : Model α) : ℕ → List α → Weight (List α)
  | 0, h => Weight.pure h
  | i + 1, h => Weight.bind (overlap (p h) (q h))
      (fun x => acceptedPrefix p q i (h ++ [x]))

/-- Probability that the first `i` proposals would all be accepted. -/
def survival (p q : Model α) (i : ℕ) (h : List α) : ℝ≥0∞ :=
  Weight.mass (acceptedPrefix p q i h)

/-- Probability of accepting `i` proposals and rejecting the next one. -/
def rejectionAt (p q : Model α) (i : ℕ) (h : List α) : ℝ≥0∞ :=
  Weight.expectation (acceptedPrefix p q i h) (fun h' => rejectionMass (p h') (q h'))

@[simp] theorem survival_zero (p q : Model α) (h : List α) : survival p q 0 h = 1 := by
  simp [survival, acceptedPrefix]

theorem survival_succ (p q : Model α) (i : ℕ) (h : List α) :
    survival p q (i + 1) h =
      Weight.expectation (overlap (p h) (q h)) (fun x => survival p q i (h ++ [x])) := by
  rw [survival, acceptedPrefix, Weight.mass_bind]
  rfl

@[simp] theorem rejectionAt_zero (p q : Model α) (h : List α) :
    rejectionAt p q 0 h = rejectionMass (p h) (q h) := by
  simp [rejectionAt, acceptedPrefix]

theorem rejectionAt_succ (p q : Model α) (i : ℕ) (h : List α) :
    rejectionAt p q (i + 1) h =
      Weight.expectation (overlap (p h) (q h)) (fun x => rejectionAt p q i (h ++ [x])) := by
  rw [rejectionAt, acceptedPrefix, Weight.expectation_bind]
  rfl

theorem acceptedPrefix_isSubprob (p q : Model α) (i : ℕ) (h : List α) :
    Weight.IsSubprob (acceptedPrefix p q i h) := by
  induction i generalizing h with
  | zero => exact Weight.isSubprob_pure h
  | succ i ih =>
    exact Weight.IsSubprob.bind (acceptanceMass_le_one (p h) (q h))
      (fun x => ih (h ++ [x]))

theorem survival_le_one (p q : Model α) (i : ℕ) (h : List α) : survival p q i h ≤ 1 :=
  acceptedPrefix_isSubprob p q i h

theorem survival_ne_top (p q : Model α) (i : ℕ) (h : List α) : survival p q i h ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (survival_le_one p q i h)

/-- Each surviving prefix either survives the next test or first fails there. -/
theorem survival_balance (p q : Model α) (i : ℕ) (h : List α) :
    survival p q (i + 1) h + rejectionAt p q i h = survival p q i h := by
  induction i generalizing h with
  | zero =>
    rw [survival_succ]
    simp only [survival_zero, Weight.expectation_const, mul_one, rejectionAt_zero]
    exact acceptance_add_rejection (p h) (q h)
  | succ i ih =>
    rw [survival_succ p q (i + 1), rejectionAt_succ,
      ← Weight.expectation_add_cost]
    simp only [ih]
    exact (survival_succ p q i h).symm

theorem rejectionAt_eq_sub (p q : Model α) (i : ℕ) (h : List α) :
    rejectionAt p q i h = survival p q i h - survival p q (i + 1) h :=
  ENNReal.eq_sub_of_add_eq (survival_ne_top p q (i + 1) h)
    (by simpa only [add_comm] using survival_balance p q i h)

theorem survival_antitone (p q : Model α) (h : List α) :
    Antitone (fun i => survival p q i h) := by
  apply antitone_nat_of_succ_le
  intro i
  exact (le_add_right (le_refl _)).trans_eq (survival_balance p q i h)

/-- The actual eager round, with space for all `K` proposals and one final token. -/
def round (p q : Model α) (K : ℕ) (h : List α) : Weight (List α × RoundTrace) :=
  Weight.bind (draftBlock q h K) (fun buffer =>
    verifyBuffer p q (fun _ h' trace => Weight.pure (h', trace)) (K + 1) h buffer K 0)

theorem round_eq_delayed (p q : Model α) (K : ℕ) (h : List α) :
    round p q K h =
      delayed p q (fun _ h' trace => Weight.pure (h', trace)) (K + 1) h K K 0 :=
  buffered_eq_delayed p q _ _ _ _ _ _

/-- Scalar acceptance-count recurrence: accept and continue, or reject now. -/
def counting (p q : Model α) : ℕ → List α → Weight ℕ
  | 0, _ => Weight.pure 0
  | K + 1, h =>
      Weight.bind (overlap (p h) (q h))
        (fun x => pushforward Nat.succ (counting p q K (h ++ [x]))) +
      rejectionMass (p h) (q h) • Weight.pure 0

private theorem bind_const_weight (μ : Weight α) (ν : Weight β) :
    Weight.bind μ (fun _ => ν) = Weight.mass μ • ν := by
  funext b
  exact ENNReal.tsum_mul_right

private theorem pushforward_comp (f : α → β) {γ : Type*} (g : β → γ) (μ : Weight α) :
    pushforward g (pushforward f μ) = pushforward (fun x => g (f x)) μ := by
  simp only [pushforward, Weight.bind_assoc, Weight.pure_bind]

/-- Erasing history from the complete delayed trace gives the count recurrence. -/
theorem delayed_count (p q : Model α) (K : ℕ) (h : List α) (drafted accepted : ℕ) :
    pushforward (fun out : List α × RoundTrace => out.2.accepted)
      (delayed p q (fun _ h' trace => Weight.pure (h', trace))
        (K + 1) h K drafted accepted) =
      pushforward (fun i => accepted + i) (counting p q K h) := by
  induction K generalizing h accepted with
  | zero =>
    simp only [delayed, pushforward_bind, pushforward_pure, counting,
      Nat.add_zero]
    exact Weight.bind_const_of_isProbability _ (p h).normalized _
  | succ K ih =>
    rw [delayed, step_decomposition, Weight.add_bind, pushforward_add]
    simp only [bind_pushforward, ↓reduceIte, Bool.false_eq_true,
      pushforward_bind, pushforward_pure]
    rw [counting, pushforward_add, pushforward_bind, pushforward_smul, pushforward_pure]
    simp only [Nat.add_zero, ih, pushforward_comp]
    congr 1
    · apply congrArg (Weight.bind (overlap (p h) (q h)))
      funext x
      congr 1
      funext i
      omega
    · exact bind_const_weight _ _

/-- Exact accepted-count marginal of the eager sampler, including discarded proposals. -/
theorem round_count (p q : Model α) (K : ℕ) (h : List α) :
    pushforward (fun out : List α × RoundTrace => out.2.accepted) (round p q K h) =
      counting p q K h := by
  rw [round_eq_delayed, delayed_count]
  simp only [Nat.zero_add, pushforward, Weight.bind_pure]

@[simp] theorem counting_zero (p q : Model α) (K : ℕ) (h : List α) :
    counting p q (K + 1) h 0 = rejectionMass (p h) (q h) := by
  classical
  simp [counting, pushforward, Weight.bind, Weight.pure]

theorem counting_succ (p q : Model α) (K i : ℕ) (h : List α) :
    counting p q (K + 1) h (i + 1) =
      Weight.expectation (overlap (p h) (q h)) (fun x => counting p q K (h ++ [x]) i) := by
  classical
  simp [counting, pushforward, Weight.bind, Weight.pure, Weight.expectation, mul_ite]

/-- First rejection at position `i+1`, after precisely `i` accepted tokens. -/
theorem counting_first_rejection (p q : Model α) (K i : ℕ) (hi : i < K) (h : List α) :
    counting p q K h i = rejectionAt p q i h := by
  induction K generalizing i h with
  | zero => omega
  | succ K ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [counting_succ, rejectionAt_succ]
      simp only [ih i (by omega)]

/-- Accepting the complete block has its joint survival probability. -/
theorem counting_all_accepted (p q : Model α) (K : ℕ) (h : List α) :
    counting p q K h K = survival p q K h := by
  induction K generalizing h with
  | zero => simp [counting, Weight.pure]
  | succ K ih => rw [counting_succ, survival_succ]; simp only [ih]

theorem counting_above (p q : Model α) (K i : ℕ) (hi : K < i) (h : List α) :
    counting p q K h i = 0 := by
  induction K generalizing i h with
  | zero => simp [counting, Weight.pure, Nat.ne_of_gt hi]
  | succ K ih =>
    cases i with
    | zero => omega
    | succ i =>
      rw [counting_succ]
      simp only [ih i (by omega), Weight.expectation_const, mul_zero]

theorem counting_isProbability (p q : Model α) (K : ℕ) (h : List α) :
    Weight.IsProbability (counting p q K h) := by
  induction K generalizing h with
  | zero => exact Weight.isProbability_pure 0
  | succ K ih =>
    change Weight.mass (_ + _) = 1
    rw [Weight.mass_add, Weight.mass_bind_of_isProbability, Weight.mass_smul,
      Weight.mass_pure, mul_one]
    · exact acceptance_add_rejection (p h) (q h)
    · intro x _
      simpa only [Weight.IsProbability, mass_pushforward] using ih (h ++ [x])

theorem round_isProbability (p q : Model α) (K : ℕ) (h : List α) :
    Weight.IsProbability (round p q K h) := by
  have hm := congrArg Weight.mass (round_count p q K h)
  rw [mass_pushforward, counting_isProbability] at hm
  exact hm

@[simp] theorem counting_mass (p q : Model α) (K : ℕ) (h : List α) :
    Weight.mass (counting p q K h) = 1 := counting_isProbability p q K h

/-- Growing accepted prefixes at their right boundary exposes the conditional
acceptance probability at the history actually reached. -/
theorem acceptedPrefix_succ_right (p q : Model α) (i : ℕ) (h : List α) :
    acceptedPrefix p q (i + 1) h =
      Weight.bind (acceptedPrefix p q i h) (fun h' =>
        pushforward (fun x => h' ++ [x]) (overlap (p h') (q h'))) := by
  induction i generalizing h with
  | zero => simp only [acceptedPrefix, Weight.pure_bind, pushforward]
  | succ i ih =>
    simp only [acceptedPrefix, Weight.bind_assoc]
    apply congrArg (Weight.bind (overlap (p h) (q h)))
    funext x
    exact ih (h ++ [x])

theorem survival_succ_right (p q : Model α) (i : ℕ) (h : List α) :
    survival p q (i + 1) h =
      Weight.expectation (acceptedPrefix p q i h) (fun h' => acceptanceMass (p h') (q h')) := by
  rw [survival, acceptedPrefix_succ_right, Weight.mass_bind]
  simp only [mass_pushforward]
  rfl

/-- The scalar rate is constant conditional on each reachable accepted history.
This is strictly stronger than an unconditional average acceptance rate. -/
def ConstantConditionalOverlap (p q : Model α) (K : ℕ) (h : List α) (a : ℝ≥0∞) : Prop :=
  ∀ i < K, ∀ h' ∈ Weight.support (acceptedPrefix p q i h),
    acceptanceMass (p h') (q h') = a

theorem survival_eq_pow (p q : Model α) (K : ℕ) (h : List α) (a : ℝ≥0∞)
    (hc : ConstantConditionalOverlap p q K h a) (i : ℕ) (hi : i ≤ K) :
    survival p q i h = a ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [survival_succ_right]
    rw [Weight.expectation_congr_on_support _ (hc i (by omega)), Weight.expectation_const]
    change survival p q i h * a = _
    rw [ih (by omega), pow_succ]

theorem rejectionAt_eq_geometric (p q : Model α) (K : ℕ) (h : List α) (a : ℝ≥0∞)
    (hc : ConstantConditionalOverlap p q K h a) (i : ℕ) (hi : i < K) :
    rejectionAt p q i h = a ^ i - a ^ (i + 1) := by
  rw [rejectionAt_eq_sub, survival_eq_pow p q K h a hc i (by omega),
    survival_eq_pow p q K h a hc (i + 1) (by omega)]

/-- The mutually exclusive first-rejection cases and the all-accepted case. -/
def branchMass (p q : Model α) (K : ℕ) (h : List α) (i : ℕ) : ℝ≥0∞ :=
  if i < K then rejectionAt p q i h else if i = K then survival p q K h else 0

theorem counting_eq_branchMass (p q : Model α) (K i : ℕ) (h : List α) :
    counting p q K h i = branchMass p q K h i := by
  rcases lt_trichotomy i K with hi | rfl | hi
  · simp [branchMass, hi, counting_first_rejection p q K i hi h]
  · simp [branchMass, counting_all_accepted]
  · have hn : ¬ i < K := by omega
    have he : i ≠ K := by omega
    rw [counting_above p q K i hi h, branchMass, if_neg hn, if_neg he]

/-- Explicit finite additive decomposition of the actual acceptance-count law. -/
theorem counting_decomposition (p q : Model α) (K : ℕ) (h : List α) :
    counting p q K h =
      ∑ i ∈ Finset.range (K + 1), branchMass p q K h i • Weight.pure i := by
  classical
  funext i
  rw [counting_eq_branchMass]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Weight.pure,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  by_cases hi : i < K + 1
  · simp only [Finset.mem_range, hi, if_true]
  · simp only [Finset.mem_range, hi, if_false]
    have hn : ¬ i < K := by omega
    have he : i ≠ K := by omega
    rw [branchMass, if_neg hn, if_neg he]

theorem branchMass_sum (p q : Model α) (K : ℕ) (h : List α) :
    (∑ i ∈ Finset.range (K + 1), branchMass p q K h i) = 1 := by
  have he : Weight.mass (counting p q K h) =
      ∑ i ∈ Finset.range (K + 1), counting p q K h i := by
    apply tsum_eq_sum
    intro i hi
    exact counting_above p q K i (by simp only [Finset.mem_range] at hi; omega) h
  simpa only [counting_eq_branchMass, counting_mass] using he.symm

/-- One finite outcome piece records its count and exact mass on both sides. -/
def countBranch (i : ℕ) (m : ℝ≥0∞) : RAssn ℕ ℕ :=
  fun μ ν => couple (fun x y => x = i ∧ y = i) μ ν ∧ massEq m m μ ν

/-- An additive quantitative contract, retaining zero-mass cases and the final
all-accepted case rather than replacing them by a disjunction. -/
def countSpec (p q : Model α) (K : ℕ) (h : List α) : RAssn ℕ ℕ :=
  finiteCases (fun i => countBranch i (branchMass p q K h i)) (K + 1)

private theorem countBranch_self (i : ℕ) (m : ℝ≥0∞) :
    countBranch i m (m • Weight.pure i) (m • Weight.pure i) := by
  refine ⟨(Coupled.pure (R := fun x y => x = i ∧ y = i) ⟨rfl, rfl⟩).smul m, ?_⟩
  simp [massEq, Weight.mass_smul]

/-- The eager sampler satisfies every finite first-rejection outcome clause. -/
theorem round_count_contract (p q : Model α) (K : ℕ) (h : List α) :
    countSpec p q K h (counting p q K h)
      (pushforward (fun out : List α × RoundTrace => out.2.accepted) (round p q K h)) := by
  rw [round_count, counting_decomposition]
  exact finiteCases_intro _ (K + 1) _ _ (fun i _ => countBranch_self i _)

theorem countSpec_mass_one (p q : Model α) (K : ℕ) (h : List α) :
    entail (countSpec p q K h) (massEq 1 1) := by
  have ht := finiteCases_massEq (P := fun i => countBranch i (branchMass p q K h i))
    (K + 1) (branchMass p q K h) (branchMass p q K h)
    (fun _ _ _ _ hb => hb.2)
  simpa only [branchMass_sum, countSpec] using ht

theorem countSpec_agreement (p q : Model α) (K : ℕ) (h : List α) :
    entail (countSpec p q K h) (couple Eq) := by
  apply finiteCases_couple
  intro i _ μ ν hb
  exact hb.1.mono (fun _ _ hxy => hxy.1.trans hxy.2.symm)

/-- Observable count transformations preserve the complete finite outcome split. -/
def mappedCountSpec (p q : Model α) (K : ℕ) (h : List α) (f : ℕ → ℕ) : RAssn ℕ ℕ :=
  finiteCases (fun i => countBranch (f i) (branchMass p q K h i)) (K + 1)

/-- A branchwise rule derivation transports the exact law through an observation.
Distinct source cases remain separate even when the observation merges their counts. -/
theorem countSpec_map (p q : Model α) (K : ℕ) (h : List α) (f : ℕ → ℕ) :
    quadSem (pushforward f) (pushforward f) (countSpec p q K h)
      (mappedCountSpec p q K h f) := by
  apply quadSem_finiteCases _ _ (pushforward_zero f) (pushforward_zero f)
    (pushforward_add f) (pushforward_add f)
  intro i _ μ ν hb
  refine ⟨hb.1.pushforward f f (fun x y hxy =>
    ⟨congrArg f hxy.1, congrArg f hxy.2⟩), ?_⟩
  simpa only [massEq, mass_pushforward] using hb.2

/-- A pRelOL judgment for the actual eager program and its finite outcome law. -/
theorem round_count_quad (p q : Model α) (K : ℕ) (h : List α) :
    quadSem (fun μ => Weight.bind μ (counting p q K))
      (fun μ => Weight.bind μ (fun h' =>
        pushforward (fun out : List α × RoundTrace => out.2.accepted) (round p q K h')))
      (exactly (Weight.pure h) (Weight.pure h)) (countSpec p q K h) := by
  rintro μ ν ⟨rfl, rfl⟩
  simpa only [Weight.pure_bind] using round_count_contract p q K h

end

end RelOL.Prob.Speculative.RoundLaw
