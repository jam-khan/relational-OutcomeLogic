import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.RoundExpectation

/-!
# Quantitative round laws at a finite remaining output budget

Budget zero performs no draft work. A positive-budget round samples its entire
draft buffer, and emission stops at the budget even if proposals remain. The
counting law therefore combines all longer survival paths at the clipped count.
-/

namespace RelOL.Prob.Speculative.RoundLaw

open scoped ENNReal

variable {α β : Type*}

noncomputable section

/-- A single actual eager round with an independently chosen remaining budget. -/
def roundWithBudget (p q : Model α) (K : ℕ) : ℕ → List α → Weight (List α × RoundTrace)
  | 0, h => Weight.pure (h, ⟨0, 0, false, false⟩)
  | n + 1, h => Weight.bind (draftBlock q h K) (fun buffer =>
      verifyBuffer p q (fun _ h' trace => Weight.pure (h', trace))
        (n + 1) h buffer K 0)

/-- Acceptance and emission accounting, preserving their correlation. -/
def stats (out : List α × RoundTrace) : ℕ × ℕ := (out.2.accepted, out.2.emitted)

private theorem bind_const_weight (μ : Weight α) (ν : Weight β) :
    Weight.bind μ (fun _ => ν) = Weight.mass μ • ν := by
  funext b
  exact ENNReal.tsum_mul_right

private theorem pushforward_comp (f : α → β) {γ : Type*} (g : β → γ) (μ : Weight α) :
    pushforward g (pushforward f μ) = pushforward (fun x => g (f x)) μ := by
  simp only [pushforward, Weight.bind_assoc, Weight.pure_bind]

/-- The complete joint count law, including exhaustion without a bonus token. -/
theorem delayed_stats_budget (p q : Model α) (n K : ℕ) (h : List α)
    (drafted accepted : ℕ) :
    pushforward stats
      (delayed p q (fun _ h' trace => Weight.pure (h', trace))
        n h K drafted accepted) =
      pushforward (fun i => (accepted + i, accepted + min (i + 1) n))
        (counting p q (min K n) h) := by
  induction n generalizing K h accepted with
  | zero => simp [delayed, stats, RoundTrace.emitted, counting]
  | succ n ih =>
    cases K with
    | zero =>
      simp only [delayed, pushforward_bind, pushforward_pure, zero_min, counting]
      simp only [stats, RoundTrace.emitted, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero, Nat.zero_add, Nat.min_eq_left (Nat.succ_le_succ (Nat.zero_le n))]
      exact Weight.bind_const_of_isProbability _ (p h).normalized _
    | succ K =>
      rw [delayed, step_decomposition, Weight.add_bind, pushforward_add]
      simp only [bind_pushforward, ↓reduceIte, Bool.false_eq_true,
        pushforward_bind, pushforward_pure]
      rw [min_add_add_right, counting, pushforward_add, pushforward_bind,
        pushforward_smul, pushforward_pure]
      simp only [ih, pushforward_comp, Nat.add_zero, stats, RoundTrace.emitted,
        Bool.false_eq_true, ↓reduceIte, Nat.min_eq_left (Nat.succ_le_succ (Nat.zero_le n))]
      congr 1
      · apply congrArg (Weight.bind (overlap (p h) (q h)))
        funext x
        congr 1
        funext i
        apply Prod.ext <;> omega
      · exact bind_const_weight _ _

theorem roundWithBudget_stats (p q : Model α) (K n : ℕ) (h : List α) :
    pushforward stats (roundWithBudget p q K n h) =
      pushforward (fun i => (i, min (i + 1) n)) (counting p q (min K n) h) := by
  cases n with
  | zero => simp [roundWithBudget, stats, RoundTrace.emitted, counting]
  | succ n =>
    rw [roundWithBudget, buffered_eq_delayed, delayed_stats_budget]
    simp only [Nat.zero_add]

theorem roundWithBudget_count (p q : Model α) (K n : ℕ) (h : List α) :
    pushforward (fun out : List α × RoundTrace => out.2.accepted)
      (roundWithBudget p q K n h) = counting p q (min K n) h := by
  have he := congrArg (pushforward Prod.fst) (roundWithBudget_stats p q K n h)
  simpa only [pushforward, Weight.bind_assoc, Weight.pure_bind, stats, Weight.bind_pure] using he

theorem roundWithBudget_emitted (p q : Model α) (K n : ℕ) (h : List α) :
    pushforward (fun out : List α × RoundTrace => out.2.emitted)
      (roundWithBudget p q K n h) =
      pushforward (fun i => min (i + 1) n) (counting p q (min K n) h) := by
  have he := congrArg (pushforward Prod.snd) (roundWithBudget_stats p q K n h)
  simpa only [pushforward_comp, stats] using he

theorem roundWithBudget_isProbability (p q : Model α) (K n : ℕ) (h : List α) :
    Weight.IsProbability (roundWithBudget p q K n h) := by
  have hm := congrArg Weight.mass (roundWithBudget_count p q K n h)
  simpa only [mass_pushforward, counting_mass, Weight.IsProbability] using hm

/-- Clipping preserves the complete finite first-rejection specification up to
the last accepted prefix that fits the output budget. -/
theorem roundWithBudget_count_contract (p q : Model α) (K n : ℕ) (h : List α) :
    countSpec p q (min K n) h (counting p q (min K n) h)
      (pushforward (fun out : List α × RoundTrace => out.2.accepted)
        (roundWithBudget p q K n h)) := by
  simpa only [round_count, roundWithBudget_count] using
    round_count_contract p q (min K n) h

/-- Derive the clipped emission contract by the finite additive composition
rule. Distinct acceptance cases remain distinct even when clipping merges emissions. -/
theorem roundWithBudget_emitted_contract (p q : Model α) (K n : ℕ) (h : List α) :
    mappedCountSpec p q (min K n) h (fun i => min (i + 1) n)
      (pushforward (fun i => min (i + 1) n) (counting p q (min K n) h))
      (pushforward (fun out : List α × RoundTrace => out.2.emitted)
        (roundWithBudget p q K n h)) := by
  have hc := countSpec_map p q (min K n) h (fun i => min (i + 1) n) _ _
    (roundWithBudget_count_contract p q K n h)
  simpa only [roundWithBudget_count, roundWithBudget_emitted] using hc

private theorem expectation_pushforward (μ : Weight α) (π : α → β) (f : β → ℝ≥0∞) :
    Weight.expectation (pushforward π μ) f = Weight.expectation μ (fun x => f (π x)) := by
  simp only [pushforward, Weight.expectation_bind, Weight.expectation_pure]

/-- The clipped sampler accepts only prefixes fitting within its remaining budget. -/
theorem expected_accepted_clipped (p q : Model α) (K n : ℕ) (h : List α) :
    Weight.expectation (roundWithBudget p q K n h)
      (fun out => (out.2.accepted : ℝ≥0∞)) =
      ∑ i ∈ Finset.range (min K n), survival p q (i + 1) h := by
  rw [← expectation_pushforward _ (fun out : List α × RoundTrace => out.2.accepted),
    roundWithBudget_count]
  exact counting_expected p q (min K n) h

private theorem counting_support_le (p q : Model α) (K i : ℕ) (h : List α)
    (hi : i ∈ Weight.support (counting p q K h)) : i ≤ K := by
  by_contra hgt
  exact hi (counting_above p q K i (by omega) h)

private theorem expectation_indicator (μ : Weight ℕ) (n : ℕ) :
    Weight.expectation μ (fun i => if i = n then 1 else 0) = μ n := by
  classical
  simp [Weight.expectation, mul_ite]

/-- When the remaining budget equals the number of possible acceptances, the
last survival case consumes the final slot and does not emit an extra bonus. -/
theorem counting_expected_at_budget (p q : Model α) (n : ℕ) (h : List α) :
    Weight.expectation (counting p q n h) (fun i => (min (i + 1) n : ℕ)) =
      ∑ i ∈ Finset.range n, survival p q i h := by
  have hs : Weight.expectation (counting p q n h)
      (fun i => ((min (i + 1) n : ℕ) : ℝ≥0∞) + if i = n then 1 else 0) =
      Weight.expectation (counting p q n h) (fun i => (i : ℝ≥0∞) + 1) := by
    apply Weight.expectation_congr_on_support
    intro i hi
    have hib := counting_support_le p q n i h hi
    by_cases he : i = n
    · subst i
      simp
    · have hil : i + 1 ≤ n := by omega
      simp only [he, if_false, add_zero, Nat.min_eq_left hil, Nat.cast_add, Nat.cast_one]
  rw [Weight.expectation_add_cost, expectation_indicator, counting_all_accepted,
    Weight.expectation_add_cost, counting_expected, Weight.expectation_const, counting_mass,
    mul_one] at hs
  have hsum : (∑ i ∈ Finset.range n, survival p q (i + 1) h) + 1 =
      (∑ i ∈ Finset.range n, survival p q i h) + survival p q n h := by
    calc
      _ = ∑ i ∈ Finset.range (n + 1), survival p q i h := by
        rw [Finset.sum_range_succ']; simp only [survival_zero]
      _ = _ := Finset.sum_range_succ _ _
  rw [hsum] at hs
  exact (ENNReal.add_left_inj (survival_ne_top p q n h)).mp hs

/-- The general clipped emission law includes zero budget and clipping away the
bonus token: the survival sum contains exactly `min (K+1) n` terms. -/
theorem expected_emitted_clipped (p q : Model α) (K n : ℕ) (h : List α) :
    Weight.expectation (roundWithBudget p q K n h)
      (fun out => (out.2.emitted : ℝ≥0∞)) =
      ∑ i ∈ Finset.range (min (K + 1) n), survival p q i h := by
  rw [← expectation_pushforward _ (fun out : List α × RoundTrace => out.2.emitted),
    roundWithBudget_emitted, expectation_pushforward]
  by_cases hkn : n ≤ K
  · rw [Nat.min_eq_right hkn, Nat.min_eq_right (by omega : n ≤ K + 1)]
    exact counting_expected_at_budget p q n h
  · have hkn' : K + 1 ≤ n := by omega
    rw [Nat.min_eq_left (by omega : K ≤ n), Nat.min_eq_left hkn']
    have he : Weight.expectation (counting p q K h) (fun i => ((min (i + 1) n : ℕ) : ℝ≥0∞)) =
        Weight.expectation (counting p q K h) (fun i => (i : ℝ≥0∞) + 1) := by
      apply Weight.expectation_congr_on_support
      intro i hi
      have hib := counting_support_le p q K i h hi
      simp only [Nat.min_eq_left (by omega : i + 1 ≤ n), Nat.cast_add, Nat.cast_one]
    rw [he, Weight.expectation_add_cost, counting_expected, Weight.expectation_const,
      counting_mass, mul_one, Finset.sum_range_succ']
    simp only [survival_zero]

theorem expected_emitted_clipped_geometric_sum (p q : Model α) (K n : ℕ) (h : List α)
    (a : ℝ≥0∞) (hc : ConstantConditionalOverlap p q K h a) :
    Weight.expectation (roundWithBudget p q K n h)
      (fun out => (out.2.emitted : ℝ≥0∞)) =
      ∑ i ∈ Finset.range (min (K + 1) n), a ^ i := by
  rw [expected_emitted_clipped]
  apply Finset.sum_congr rfl
  intro i hi
  apply survival_eq_pow p q K h a hc
  simp only [Finset.mem_range] at hi
  omega

theorem expected_emitted_clipped_rate_one (p q : Model α) (K n : ℕ) (h : List α)
    (hc : ConstantConditionalOverlap p q K h 1) :
    Weight.expectation (roundWithBudget p q K n h)
      (fun out => (out.2.emitted : ℝ≥0∞)) = (min (K + 1) n : ℕ) := by
  rw [expected_emitted_clipped_geometric_sum p q K n h 1 hc]
  simp

end

end RelOL.Prob.Speculative.RoundLaw
