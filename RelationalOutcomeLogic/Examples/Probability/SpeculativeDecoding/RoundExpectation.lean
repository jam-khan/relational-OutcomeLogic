import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.RoundLaw
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Expected accepted and emitted tokens of one eager speculative round

The tail sums use joint prefix-survival probabilities. Powers arise only under a
constant conditional overlap along accepted histories, never from an average rate.
-/

namespace RelOL.Prob.Speculative.RoundLaw

open scoped ENNReal NNReal

variable {α β : Type*}

noncomputable section

private theorem expectation_pushforward (μ : Weight α) (π : α → β) (f : β → ℝ≥0∞) :
    Weight.expectation (pushforward π μ) f = Weight.expectation μ (fun x => f (π x)) := by
  simp only [pushforward, Weight.expectation_bind, Weight.expectation_pure]

/-- Expected acceptance count in the exact first-rejection recurrence. -/
theorem counting_expected (p q : Model α) (K : ℕ) (h : List α) :
    Weight.expectation (counting p q K h) (fun i => (i : ℝ≥0∞)) =
      ∑ i ∈ Finset.range K, survival p q (i + 1) h := by
  induction K generalizing h with
  | zero => simp [counting]
  | succ K ih =>
    rw [counting, Weight.expectation_add, Weight.expectation_bind,
      Weight.expectation_smul, Weight.expectation_pure]
    simp only [Nat.cast_zero, mul_zero, add_zero, expectation_pushforward,
      Nat.cast_succ, Weight.expectation_add_cost, Weight.expectation_const,
      counting_mass, mul_one, ih]
    rw [Weight.expectation_finset_sum_cost]
    simp only [← survival_succ]
    rw [Finset.sum_range_succ']
    congr 1
    rw [survival_succ]
    simp only [survival_zero, Weight.expectation_const, mul_one]

/-- The actual eager sampler accepts the joint-survival tail sum in expectation. -/
theorem expected_accepted (p q : Model α) (K : ℕ) (h : List α) :
    Weight.expectation (round p q K h) (fun out => (out.2.accepted : ℝ≥0∞)) =
      ∑ i ∈ Finset.range K, survival p q (i + 1) h := by
  rw [← expectation_pushforward _ (fun out : List α × RoundTrace => out.2.accepted),
    round_count]
  exact counting_expected p q K h

/-- With space for the complete draft plus one token, every round finishes by
either correction or bonus. Thus emission is acceptance plus one. -/
theorem delayed_emitted_count (p q : Model α) (K : ℕ) (h : List α)
    (drafted accepted : ℕ) :
    pushforward (fun out : List α × RoundTrace => out.2.emitted)
      (delayed p q (fun _ h' trace => Weight.pure (h', trace))
        (K + 1) h K drafted accepted) =
    pushforward (fun out : List α × RoundTrace => out.2.accepted + 1)
      (delayed p q (fun _ h' trace => Weight.pure (h', trace))
        (K + 1) h K drafted accepted) := by
  induction K generalizing h accepted with
  | zero => simp [delayed, pushforward_bind, RoundTrace.emitted]
  | succ K ih =>
    rw [delayed, pushforward_bind, pushforward_bind]
    apply congrArg (Weight.bind (step (p h) (q h)))
    funext v
    cases hv : v.1 with
    | false => simp [RoundTrace.emitted]
    | true => simpa only [hv, ↓reduceIte] using ih (h ++ [v.2]) (accepted + 1)

theorem round_emitted_count (p q : Model α) (K : ℕ) (h : List α) :
    pushforward (fun out : List α × RoundTrace => out.2.emitted) (round p q K h) =
      pushforward Nat.succ (counting p q K h) := by
  rw [round_eq_delayed, delayed_emitted_count, ← round_eq_delayed]
  rw [← round_count p q K h]
  simp only [pushforward, Weight.bind_assoc, Weight.pure_bind]

/-- Emission counts inherit every first-rejection case by the finite additive
composition rule, retaining exact case masses rather than just their expected sum. -/
theorem round_emitted_contract (p q : Model α) (K : ℕ) (h : List α) :
    mappedCountSpec p q K h Nat.succ
      (pushforward Nat.succ (counting p q K h))
      (pushforward (fun out : List α × RoundTrace => out.2.emitted) (round p q K h)) := by
  have hc := countSpec_map p q K h Nat.succ _ _ (round_count_contract p q K h)
  simpa only [round_count, round_emitted_count] using hc

/-- Expected tokens emitted by the actual eager round: one terminal token plus
one token for each jointly accepted prefix. -/
theorem expected_emitted (p q : Model α) (K : ℕ) (h : List α) :
    Weight.expectation (round p q K h) (fun out => (out.2.emitted : ℝ≥0∞)) =
      ∑ i ∈ Finset.range (K + 1), survival p q i h := by
  rw [← expectation_pushforward _ (fun out : List α × RoundTrace => out.2.emitted),
    round_emitted_count, expectation_pushforward]
  simp only [Nat.cast_succ, Weight.expectation_add_cost, counting_expected,
    Weight.expectation_const, counting_mass, mul_one]
  rw [Finset.sum_range_succ']
  simp only [survival_zero]

theorem expected_emitted_geometric_sum (p q : Model α) (K : ℕ) (h : List α) (a : ℝ≥0∞)
    (hc : ConstantConditionalOverlap p q K h a) :
    Weight.expectation (round p q K h) (fun out => (out.2.emitted : ℝ≥0∞)) =
      ∑ i ∈ Finset.range (K + 1), a ^ i := by
  rw [expected_emitted]
  apply Finset.sum_congr rfl
  intro i hi
  exact survival_eq_pow p q K h a hc i (by simp only [Finset.mem_range] at hi; omega)

theorem expected_accepted_geometric_sum (p q : Model α) (K : ℕ) (h : List α) (a : ℝ≥0∞)
    (hc : ConstantConditionalOverlap p q K h a) :
    Weight.expectation (round p q K h) (fun out => (out.2.accepted : ℝ≥0∞)) =
      ∑ i ∈ Finset.range K, a ^ (i + 1) := by
  rw [expected_accepted]
  apply Finset.sum_congr rfl
  intro i hi
  exact survival_eq_pow p q K h a hc (i + 1) (by simp only [Finset.mem_range] at hi; omega)

/-- The rate-one boundary is finite and needs no division by zero. -/
theorem expected_emitted_rate_one (p q : Model α) (K : ℕ) (h : List α)
    (hc : ConstantConditionalOverlap p q K h 1) :
    Weight.expectation (round p q K h) (fun out => (out.2.emitted : ℝ≥0∞)) = K + 1 := by
  rw [expected_emitted_geometric_sum p q K h 1 hc]
  simp

private theorem ennreal_geometric_sum {a : ℝ≥0∞} (ha : a < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, a ^ i) = (1 - a ^ n) / (1 - a) := by
  lift a to ℝ≥0 using (ne_top_of_le_ne_top ENNReal.one_ne_top ha.le) with a
  have ha' : a < 1 := by exact_mod_cast ha
  have he := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (geom_sum_of_lt_one ha' n)
  simpa only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_pow,
    ENNReal.coe_div (ne_of_gt (tsub_pos_of_lt ha')), ENNReal.coe_sub, ENNReal.coe_one] using he

/-- The familiar ratio follows from conditional overlap invariance. It is not
valid when `a` denotes only an unconditional or empirical mean acceptance rate. -/
theorem expected_emitted_geometric (p q : Model α) (K : ℕ) (h : List α) (a : ℝ≥0∞)
    (hc : ConstantConditionalOverlap p q K h a) (ha : a < 1) :
    Weight.expectation (round p q K h) (fun out => (out.2.emitted : ℝ≥0∞)) =
      (1 - a ^ (K + 1)) / (1 - a) := by
  rw [expected_emitted_geometric_sum p q K h a hc]
  exact ennreal_geometric_sum ha (K + 1)

end

end RelOL.Prob.Speculative.RoundLaw
