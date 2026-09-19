import RelationalOutcomeLogic.Prob.Search
import RelationalOutcomeLogic.Prob.BugCert

/-!
# A cached-randomness bug in bounded search

The correct full scan takes a fresh independent trial at every iteration. The
faulty implementation takes one trial and drains the remaining budget without
changing its answer: repeatedly OR-ing a cached trial has exactly this behavior.
Both implementations terminate and, for nondegenerate trials, have the same
observable support. Their failure probabilities differ at every budget above one.
The certificates below concern the actual observed command semantics.
-/

namespace RelOL.Prob.Search

open scoped ENNReal

noncomputable section

/-- Consume the remaining budget without drawing fresh randomness. -/
def drain : Cmd State := .while fullGuard (.assign fun s => (s.1 - 1, s.2))

theorem drain_sem (n : ℕ) (b : Bool) : sem drain (n, b) = Weight.pure (0, b) := by
  induction n with
  | zero => exact sem_while_neg (g := fullGuard) (by simp [fullGuard]) _
  | succ n ih =>
      rw [drain, sem_while_pos (g := fullGuard) (by simp [fullGuard])]
      change Weight.bind (Weight.pure (n + 1 - 1, b)) (sem drain) = _
      simpa only [Weight.pure_bind, Nat.add_sub_cancel] using ih

/-- Incorrectly reuse the first trial instead of drawing a fresh trial at each step. -/
def cached (T : Trial) : Cmd State :=
  .ite fullGuard (.seq (body T) drain) .skip

@[simp] theorem cached_sem_zero (T : Trial) (b : Bool) :
    sem (cached T) (0, b) = Weight.pure (0, b) := by
  rw [cached, sem_ite_neg (g := fullGuard) (by simp [fullGuard]), sem_skip]

theorem cached_sem_succ (T : Trial) (n : ℕ) (b : Bool) :
    sem (cached T) (n + 1, b) =
      T.miss • Weight.pure (0, b) + T.hit • Weight.pure (0, true) := by
  rw [cached, sem_ite_pos (g := fullGuard) (by simp [fullGuard]), sem_seq]
  change Weight.bind (draw T (n + 1, b)) (sem drain) = _
  simp only [draw, Weight.add_bind, Weight.smul_bind, Weight.pure_bind, drain_sem]

/-- Missing fresh samples changes probabilities, rather than termination mass. -/
theorem cached_isProbability (T : Trial) (s : State) :
    Weight.IsProbability (sem (cached T) s) := by
  rcases s with ⟨n, b⟩
  cases n with
  | zero => rw [cached_sem_zero]; exact Weight.isProbability_pure _
  | succ n =>
      change Weight.mass (sem (cached T) (n + 1, b)) = 1
      rw [cached_sem_succ, Weight.mass_add, Weight.mass_smul, Weight.mass_smul,
        Weight.mass_pure, Weight.mass_pure, mul_one, mul_one]
      exact T.normalized

theorem observed_cached_isProbability (T : Trial) (n : ℕ) :
    Weight.IsProbability (observed (cached T) (seed n)) := by
  rw [observed_seed]
  exact (cached_isProbability T (n, false)).bind fun s => Weight.isProbability_pure s.2

/-- No trial is needed at budget zero. -/
theorem cached_zero_eq_full (T : Trial) (b : Bool) :
    sem (cached T) (0, b) = sem (full T) (0, b) := by simp

/-- Reusing a draw is harmless when there is only one trial. -/
theorem cached_one_eq_full (T : Trial) (b : Bool) :
    sem (cached T) (1, b) = sem (full T) (1, b) := by
  rw [cached_sem_succ T 0 b, full_sem_succ T 0 b, full_sem_zero, full_sem_zero]

theorem observe_cached_false (T : Trial) (n : ℕ) :
    observe (sem (cached T) (n + 1, false)) =
      T.miss • Weight.pure false + T.hit • Weight.pure true := by
  rw [cached_sem_succ, observe_add, observe_smul, observe_smul, observe_pure, observe_pure]

theorem observed_cached_seed (T : Trial) {n : ℕ} (hn : 0 < n) :
    observed (cached T) (seed n) =
      T.miss • Weight.pure false + T.hit • Weight.pure true := by
  cases n with
  | zero => cases Nat.not_lt_zero _ hn
  | succ n => rw [observed_seed, observe_cached_false]

theorem cached_false_event (T : Trial) {n : ℕ} (hn : 0 < n) :
    Weight.eventMass (observed (cached T) (seed n)) {false} = T.miss := by
  rw [observed_cached_seed T hn]
  simp [Weight.pure]

theorem full_false_event (T : Trial) (n : ℕ) :
    Weight.eventMass (observed (full T) (seed n)) {false} = T.miss ^ n := by
  rw [observed_full_seed]
  simp [Weight.pure]

/-- At least two independent nondegenerate trials fail less often than one cached trial. -/
theorem miss_pow_lt_miss (T : Trial) (hzero : 0 < T.miss) (hone : T.miss < 1)
    {n : ℕ} (hn : 1 < n) : T.miss ^ n < T.miss := by
  cases n with
  | zero => cases Nat.not_lt_zero _ hn
  | succ n =>
      have hnzero : n ≠ 0 := by omega
      have hpow : T.miss ^ n < 1 := by
        simpa only [one_pow] using ENNReal.pow_lt_pow_left hnzero hone
      calc
        T.miss ^ (n + 1) = T.miss * T.miss ^ n := pow_succ' _ _
        _ < T.miss * 1 := ENNReal.mul_lt_mul_right hzero.ne'
          (hone.trans ENNReal.one_lt_top).ne hpow
        _ = T.miss := mul_one _

/-- Even the complete set of possible observed values misses this correlation bug. -/
theorem cached_full_supports_equal (T : Trial) (hzero : 0 < T.miss)
    (hone : T.miss < 1) {n : ℕ} (hn : 0 < n) :
    Weight.support (observed (cached T) (seed n)) =
      Weight.support (observed (full T) (seed n)) := by
  have hhit : T.hit ≠ 0 := by
    intro h
    exact hone.ne (by simpa [h] using T.normalized)
  have hpow : T.miss ^ n ≠ 0 := ENNReal.pow_ne_zero hzero.ne' n
  have hsuccess : successMass T n ≠ 0 := by
    intro h
    have hlt : T.miss ^ n < 1 := by
      simpa only [one_pow] using ENNReal.pow_lt_pow_left (Nat.ne_of_gt hn) hone
    exact hlt.ne (by simpa [h] using failure_add_success T n)
  rw [observed_cached_seed T hn, observed_full_seed]
  ext b
  cases b <;> simp [Weight.support, Weight.pure, hzero.ne', hhit, hpow, hsuccess]

/-- The false-event gap certifies every nondegenerate trial and every budget above one. -/
def cached_mass_cert (T : Trial) (hzero : 0 < T.miss) (hone : T.miss < 1)
    {n : ℕ} (hn : 1 < n) :
    MassDeficitCert Eq (observed (cached T) (seed n)) (observed (full T) (seed n)) where
  left := {false}
  right := {false}
  cover := by
    intro a ha b hab
    simpa only [hab] using ha
  deficit := by
    rw [cached_false_event T (Nat.zero_lt_of_lt hn), full_false_event]
    exact miss_pow_lt_miss T hzero hone hn

/-- The defect is linked to the initial states of both actual command transformers. -/
def cached_bug (T : Trial) (hzero : 0 < T.miss) (hone : T.miss < 1)
    {n : ℕ} (hn : 1 < n) : BugCert (observed (cached T)) (observed (full T)) Eq where
  s₀ := (n, false)
  s₀' := (n, false)
  deficit := cached_mass_cert T hzero hone hn

theorem cached_spec_refuted (T : Trial) (hzero : 0 < T.miss) (hone : T.miss < 1)
    {n : ℕ} (hn : 1 < n) :
    ¬ quadSem (observed (cached T)) (observed (full T))
      (exactly (seed n) (seed n)) (couple Eq) :=
  (cached_bug T hzero hone hn).refutes (exactly_self _ _)

/-- A concrete two-trial witness: equal supports, failure probabilities one half and one quarter. -/
theorem fair_two_false_event_masses :
    Weight.eventMass (observed (cached Trial.fair) (seed 2)) {false} = 1 / 2 ∧
      Weight.eventMass (observed (full Trial.fair) (seed 2)) {false} = 1 / 4 := by
  rw [cached_false_event Trial.fair (by decide), full_false_event]
  constructor
  · rfl
  · change (1 / 2 : ℝ≥0∞) ^ 2 = 1 / 4
    rw [one_div, ← ENNReal.inv_pow]
    norm_num

theorem fair_two_supports_equal :
    Weight.support (observed (cached Trial.fair) (seed 2)) =
      Weight.support (observed (full Trial.fair) (seed 2)) :=
  cached_full_supports_equal Trial.fair (by norm_num [Trial.fair])
    (by norm_num [Trial.fair]) (by decide)

def fair_two_bug : BugCert (observed (cached Trial.fair)) (observed (full Trial.fair)) Eq :=
  cached_bug Trial.fair (by norm_num [Trial.fair]) (by norm_num [Trial.fair])
    (n := 2) (by decide)

theorem fair_two_spec_refuted :
    ¬ quadSem (observed (cached Trial.fair)) (observed (full Trial.fair))
      (exactly (seed 2) (seed 2)) (couple Eq) :=
  fair_two_bug.refutes (exactly_self _ _)

end

end RelOL.Prob.Search
