import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Model
import RelationalOutcomeLogic.Prob.Coupling.Observation
import Mathlib.Tactic.NormNum

/-!
# A completion-order race with value-dependent durations

Every job is accepted. A true job takes one tick, a false job two ticks. Jobs
start simultaneously and ties are resolved by launch order. Thus the value of
the first completed job is the disjunction of the independently drawn values.
The program below samples the entire finite launch batch before observing it;
the biased output law is a theorem about that program, not its definition.
-/

namespace RelOL.Prob.ParallelSampling

open scoped ENNReal
noncomputable section

/-- A job's value law; callers establish `θ ≤ 1` when using probability laws. -/
def raceCoin (θ : ℝ≥0∞) : Weight Bool := fun b => if b then θ else 1 - θ

@[simp] theorem raceCoin_false (θ : ℝ≥0∞) : raceCoin θ false = 1 - θ := rfl
@[simp] theorem raceCoin_true (θ : ℝ≥0∞) : raceCoin θ true = θ := rfl

theorem raceCoin_isProbability {θ : ℝ≥0∞} (hθ : θ ≤ 1) :
    Weight.IsProbability (raceCoin θ) := by
  change (∑' b, raceCoin θ b) = 1
  simp only [tsum_bool, raceCoin_true, raceCoin_false]
  exact tsub_add_cancel_of_le hθ

/-- Draw exactly `P` independent jobs in launch order. -/
def raceDraws (θ : ℝ≥0∞) : Nat → Weight (List Bool)
  | 0 => Weight.pure []
  | P + 1 => Weight.bind (raceCoin θ) fun b =>
      pushforward (List.cons b) (raceDraws θ P)

theorem raceDraws_isProbability {θ : ℝ≥0∞} (hθ : θ ≤ 1) (P : Nat) :
    Weight.IsProbability (raceDraws θ P) := by
  induction P with
  | zero => exact Weight.isProbability_pure _
  | succ P ih =>
      apply (raceCoin_isProbability hθ).bind
      intro b
      simpa only [Weight.IsProbability, mass_pushforward] using ih

/-- Duration is dependent on the sampled value. -/
def raceDuration (b : Bool) : Nat := if b then 1 else 2

/-- Actual job encoding: all jobs pass the acceptance test. -/
def raceJob (b : Bool) : Job Bool := ⟨b, true, if b then 0 else 1⟩

def raceJobLaw (θ : ℝ≥0∞) : Weight (Job Bool) := pushforward raceJob (raceCoin θ)

theorem raceJobLaw_probability {θ : ℝ≥0∞} (hθ : θ ≤ 1) :
    Weight.IsProbability (raceJobLaw θ) := by
  simpa only [Weight.IsProbability, raceJobLaw, mass_pushforward] using
    raceCoin_isProbability hθ

/-- The race's finite launches are the common case-study job sampler. -/
theorem draws_raceJobLaw (θ : ℝ≥0∞) (P : Nat) :
    draws (raceJobLaw θ) P = pushforward (List.map raceJob) (raceDraws θ P) := by
  induction P with
  | zero => simp [draws, raceDraws]
  | succ P ih =>
      rw [draws, raceDraws, ih]
      simp only [raceJobLaw, pushforward, Weight.bind_assoc,
        Weight.pure_bind, List.map_cons]

/-- Compare completion timestamps, resolving ties in launch order. The empty
batch's sentinel has the slowest runtime present in this specialized model. -/
def earliestRaceJob : List (Job Bool) → Job Bool
  | [] => raceJob false
  | j :: js =>
      let rest := earliestRaceJob js
      if j.duration ≤ rest.duration then j else rest

/-- Run the first-completion selection on the sampled, timed launch batch. -/
def firstCompletion (bs : List Bool) : Bool :=
  (earliestRaceJob (bs.map raceJob)).value

private theorem earliestRaceJob_map (bs : List Bool) :
    earliestRaceJob (bs.map raceJob) = raceJob (bs.any id) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, earliestRaceJob, ih, List.any_cons]
      cases b <;> cases bs.any id <;> decide

theorem firstCompletion_eq_any (bs : List Bool) : firstCompletion bs = bs.any id := by
  simp only [firstCompletion, earliestRaceJob_map, raceJob]


/-- The faulty policy commits the first completed job and cancels the remainder. -/
def completionRace (θ : ℝ≥0∞) (P : Nat) : Weight Bool :=
  pushforward firstCompletion (raceDraws θ P)

@[simp] theorem firstCompletion_nil : firstCompletion [] = false := rfl

@[simp] theorem firstCompletion_cons (b : Bool) (bs : List Bool) :
    firstCompletion (b :: bs) = (b || firstCompletion bs) := by
  simp only [firstCompletion_eq_any, List.any_cons, id_eq]

/-- The selected value has minimal runtime whenever the batch is nonempty. -/
theorem firstCompletion_min_duration (bs : List Bool) (b : Bool) (hb : b ∈ bs) :
    raceDuration (firstCompletion bs) ≤ raceDuration b := by
  cases b with
  | false => cases firstCompletion bs <;> simp [raceDuration]
  | true =>
      have ht : firstCompletion bs = true := by
        simp only [firstCompletion_eq_any, List.any_eq_true]
        exact ⟨true, hb, rfl⟩
      simp [ht]

theorem completionRace_isProbability {θ : ℝ≥0∞} (hθ : θ ≤ 1) (P : Nat) :
    Weight.IsProbability (completionRace θ P) := by
  simpa only [Weight.IsProbability, completionRace, mass_pushforward] using
    raceDraws_isProbability hθ P

theorem completionRace_zero (θ : ℝ≥0∞) :
    completionRace θ 0 = Weight.pure false := by
  simp [completionRace, raceDraws]

/-- Unfold one independently sampled launch, then select the earliest completion. -/
theorem completionRace_succ (θ : ℝ≥0∞) (P : Nat) :
    completionRace θ (P + 1) = Weight.bind (raceCoin θ) fun b =>
      pushforward (fun c => b || c) (completionRace θ P) := by
  simp only [completionRace, raceDraws, pushforward,
    Weight.bind_assoc, Weight.pure_bind, firstCompletion_cons]

theorem completionRace_false (θ : ℝ≥0∞) (P : Nat) :
    completionRace θ P false = (1 - θ) ^ P := by
  induction P with
  | zero => simp [completionRace_zero, Weight.pure]
  | succ P ih =>
      rw [completionRace_succ]
      simp only [Weight.bind, pushforward, tsum_bool, raceCoin_true, raceCoin_false]
      simp [Weight.pure, ih, pow_succ, mul_comm]

theorem completionRace_true {θ : ℝ≥0∞} (hθ : θ ≤ 1) (P : Nat) :
    completionRace θ P true = 1 - (1 - θ) ^ P := by
  apply ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
  have h := completionRace_isProbability hθ P
  simpa only [Weight.IsProbability, Weight.mass, tsum_bool, completionRace_false, add_comm] using h

private theorem power_strict_drop {x : ℝ≥0∞} (h₀ : 0 < x) (h₁ : x < 1)
    {P : Nat} (hP : 1 < P) : x ^ P < x := by
  have hf : x ≠ ∞ := ne_top_of_lt (h₁.trans ENNReal.one_lt_top)
  have h₀' : 0 < x.toNNReal := by
    simpa using (ENNReal.toNNReal_lt_toNNReal ENNReal.zero_ne_top hf).2 h₀
  have h₁' : x.toNNReal < 1 := by
    simpa using (ENNReal.toNNReal_lt_toNNReal hf ENNReal.one_ne_top).2 h₁
  have hp := pow_lt_self_of_lt_one₀ h₀' h₁' hP
  apply (ENNReal.toNNReal_lt_toNNReal (ENNReal.pow_ne_top hf) hf).1
  simpa only [ENNReal.toNNReal_pow] using hp

/-- Every additional contender strictly amplifies the fast value, away from endpoints. -/
theorem completionRace_false_lt {θ : ℝ≥0∞} (h₀ : 0 < θ) (h₁ : θ < 1)
    {P : Nat} (hP : 1 < P) : completionRace θ P false < raceCoin θ false := by
  rw [completionRace_false, raceCoin_false]
  exact power_strict_drop (tsub_pos_iff_lt.mpr h₁)
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero h₀.ne') hP

theorem completionRace_true_gt {θ : ℝ≥0∞} (h₀ : 0 < θ) (h₁ : θ < 1)
    {P : Nat} (hP : 1 < P) : θ < completionRace θ P true := by
  have hg := completionRace_false_lt h₀ h₁ hP
  have hm := completionRace_isProbability h₁.le P
  have hc := raceCoin_isProbability h₁.le
  change Weight.mass _ = 1 at hm hc
  simp only [Weight.mass, tsum_bool, raceCoin_true, raceCoin_false] at hm hc
  by_contra hn
  have hle : completionRace θ P true ≤ θ := le_of_not_gt hn
  have hlt : completionRace θ P true + completionRace θ P false <
      θ + (1 - θ) := ENNReal.add_lt_add_of_le_of_lt
        (ne_top_of_le_ne_top ENNReal.one_ne_top (hle.trans h₁.le)) hle hg
  rw [add_comm (completionRace θ P true), hm, add_comm θ, hc] at hlt
  exact lt_irrefl _ hlt

theorem raceCoin_support {θ : ℝ≥0∞} (h₀ : 0 < θ) (h₁ : θ < 1) :
    Weight.support (raceCoin θ) = Set.univ := by
  ext b
  cases b <;> simp [Weight.support, h₀.ne', (tsub_pos_iff_lt.mpr h₁).ne']

theorem completionRace_same_support {θ : ℝ≥0∞} (h₀ : 0 < θ) (h₁ : θ < 1)
    {P : Nat} (hP : 1 < P) :
    Weight.support (completionRace θ P) = Weight.support (raceCoin θ) := by
  rw [raceCoin_support h₀ h₁]
  ext b
  cases b with
  | false => simp [Weight.support, completionRace_false, (tsub_pos_iff_lt.mpr h₁).ne']
  | true => simp [Weight.support, (h₀.trans (completionRace_true_gt h₀ h₁ hP)).ne']

end
end RelOL.Prob.ParallelSampling
