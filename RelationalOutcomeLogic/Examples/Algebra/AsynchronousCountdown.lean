import RelationalOutcomeLogic.Generic.Loops.Asynchronous
import RelationalOutcomeLogic.Examples.Algebra.Countdown
import RelationalOutcomeLogic.Algebra.Instances.Boolean
import RelationalOutcomeLogic.Algebra.Instances.Probability
import RelationalOutcomeLogic.Algebra.Instances.Counting
import RelationalOutcomeLogic.Algebra.Instances.Tropical

/-!
# One weighted asynchronous client in four scalar models

The fast machine performs one weighted countdown step. The slow machine separates
that step into a weighted transition and a unit-weight bookkeeping transition.
Joint steps contribute the arbitrary scalar `r`; the intervening left-only steps
decrease a phase rank. Counting and cost instances therefore exercise quantitative
behavior as well as scheduling, rather than only instantiating pure computations.
-/

open scoped ENNReal

namespace RelOL.Generic.AsyncExamples

open Algebra Algebra.Weighted WeightedPrograms

noncomputable section

abbrev SlowState := ℕ × Bool

def catchUp (s : SlowState) : SlowState := (s.1 - 1, false)
def draw (s : SlowState) : SlowState := (s.1, true)

def Related (s : SlowState) (n : ℕ) : Prop :=
  if s.2 = true then s.1 = n + 1 else s.1 = n

def mode (p : SlowState × ℕ) : AsyncMode :=
  if p.1.2 = true then .left else if 0 < p.1.1 then .both else .done

def phaseRank (p : SlowState × ℕ) : ℕ := if p.1.2 = true then 1 else 0

section Algebraic

variable {K : Type*} [Semiring K] [SummationSemiring.{0} K]

def slowStep (r : K) (s : SlowState) : Weighted.Weight K SlowState :=
  if s.2 = true then Weighted.pure (catchUp s) else scale r (Weighted.pure (draw s))

/-- The same schedule works whether joint weight denotes probability, traces, or cost. -/
def schedule (r : K) :
    AsyncSchedule Related (fun s => 0 < s.1) (fun n => 0 < n)
      (slowStep r) (countdownStep r) where
  mode := mode
  rank := phaseRank
  guards := by
    intro s n hrel
    simp only [mode]
    split_ifs with hp hn
    · simp only [Related, if_pos hp] at hrel
      omega
    · simp only [Related, if_neg hp] at hrel
      exact ⟨hn, by omega⟩
    · simp only [Related, if_neg hp] at hrel
      exact ⟨hn, by omega⟩
  left := by
    intro s n hrel hm
    have hp : s.2 = true := by
      by_cases hp : s.2 = true
      · exact hp
      · by_cases hn : 0 < s.1 <;> simp [mode, hp, hn] at hm
    rw [slowStep, if_pos hp]
    apply Coupled.pure
    simp only [Related, if_pos hp] at hrel
    constructor
    · simp only [Related, catchUp, Bool.false_eq_true, if_false]
      omega
    · simp [phaseRank, catchUp, hp]
  right := by
    intro s n _ hm
    by_cases hp : s.2 = true <;> by_cases hn : 0 < s.1 <;>
      simp [mode, hp, hn] at hm
  both := by
    intro s n hrel hm
    have hphase : s.2 ≠ true ∧ 0 < s.1 := by
      by_cases hp : s.2 = true
      · simp [mode, hp] at hm
      · by_cases hn : 0 < s.1
        · exact ⟨hp, hn⟩
        · simp [mode, hp, hn] at hm
    rw [slowStep, if_neg hphase.1]
    change Coupled Related (scale r (Weighted.pure (draw s)))
      (scale r (Weighted.pure (n - 1)))
    apply Coupled.scale
    apply Coupled.pure
    simp only [Related, if_neg hphase.1] at hrel
    simp only [Related, draw, if_true]
    omega

theorem schedule_joint_phase (r : K) (n : ℕ) :
    (schedule r).mode ((n + 1, false), n + 1) = .both := by simp [schedule, mode]

theorem schedule_left_phase (r : K) (n : ℕ) :
    (schedule r).mode ((n + 1, true), n) = .left := rfl

end Algebraic

section Ordered

variable {K : Type*} [Semiring K] [CompleteLattice K]
variable [SummationSemiring.{0} K] [OmegaSummationSemiring.{0} K]

def slowLoop (r : K) : SlowState → Weighted.Weight K SlowState :=
  Generic.loopSem (fun s => 0 < s.1) (slowStep r)

/-- The public mixed-loop rule proves the client for arbitrary scalar weights. -/
theorem async_spec (r : K) :
    prhl Related (slowLoop r) (countdown r)
      (fun s n => Related s n ∧ ¬ 0 < s.1 ∧ ¬ 0 < n) :=
  prhl_while_async (schedule r)

theorem initial_coupled (r : K) (n : ℕ) :
    Coupled (fun s i => Related s i ∧ ¬ 0 < s.1 ∧ ¬ 0 < i)
      (slowLoop r (n, false)) (countdown r n) :=
  async_spec r (n, false) n (by simp [Related])

/-- Forgetting the slow machine's phase preserves the complete weighted output. -/
theorem observed_equal (r : K) (n : ℕ) :
    pushforward Prod.fst (slowLoop r (n, false)) = countdown r n := by
  apply coupled_eq_iff.mp
  have h := (initial_coupled r n).bind
    (fun s => Weighted.pure s.1) Weighted.pure (fun s i hsi =>
      Coupled.pure (R := Eq) (by omega : s.1 = i))
  simpa only [Weighted.bind_pure, pushforward] using h

/-- The unit-weight bookkeeping leaves the product of joint weights unchanged. -/
theorem slow_mass (r : K) (n : ℕ) : mass (slowLoop r (n, false)) = r ^ n :=
  (initial_coupled r n).mass_eq.trans (countdown_mass r n)

end Ordered

/-- Boolean weights record that the common terminal outcome is reachable. -/
theorem boolean_observed (n : ℕ) :
    pushforward Prod.fst (slowLoop (1 : Reachability) (n, false)) = Weighted.pure 0 := by
  rw [observed_equal, countdown_sem]
  funext i
  simp

/-- Two distinguishable joint choices per round yield exactly `2^n` traces. -/
theorem counting_slow_mass (n : ℕ) : mass (slowLoop (2 : ℕ∞) (n, false)) = 2 ^ n :=
  slow_mass 2 n

/-- Counting weight two is exactly two additive unit-weight transitions. -/
theorem counting_joint_choices (n : ℕ) :
    slowStep (2 : ℕ∞) (n, false) =
      (Weighted.pure (n, true) : Weighted.Weight ℕ∞ SlowState) +
        Weighted.pure (n, true) := by
  funext s
  simp only [slowStep, Bool.false_eq_true, if_false, draw, scale_apply,
    Pi.add_apply, two_mul]

/-- A probabilistic test of weight `q` is multiplied once per joint round. -/
theorem probability_slow_mass (q : ℝ≥0∞) (n : ℕ) :
    mass (slowLoop q (n, false)) = q ^ n := slow_mass q n

theorem probability_slow_subprob (q : ℝ≥0∞) (hq : q ≤ 1) (n : ℕ) :
    mass (slowLoop q (n, false)) ≤ 1 := by
  rw [slow_mass]
  exact pow_le_one₀ zero_le hq

/-- Numerical tropical costs accumulate per joint round, with no bookkeeping cost. -/
theorem tropical_slow_mass (d : ℝ≥0∞) (n : ℕ) :
    Cost.value (mass (slowLoop (Cost.ofValue d) (n, false))) = n • d := by
  rw [slow_mass]
  exact Tropical.untrop_pow (Tropical.trop d) n

end
end RelOL.Generic.AsyncExamples
