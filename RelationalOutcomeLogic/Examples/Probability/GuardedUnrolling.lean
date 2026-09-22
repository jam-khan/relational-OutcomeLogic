import RelationalOutcomeLogic.Prob.Transformations.GuardedUnroll
import RelationalOutcomeLogic.Subsumption.PRHL.Embedding
import RelationalOutcomeLogic.Examples.Probability.MassDeficit

/-!
# Guarded unrolling and a certified extra-sample bug

A countdown loop accumulates the Boolean OR of fresh fair samples. Guarded
two-iteration unrolling preserves its semantics for every initial count, including
zero and odd counts. Omitting the inner guard takes one extra sample at count one:
the observed false probability changes from one half to one quarter, although the
possible observed Boolean values are unchanged.
-/

namespace RelOL.Prob.UnrollExamples

open scoped ENNReal
open Examples

noncomputable section

/-- Remaining samples and the Boolean OR accumulated so far. -/
abbrev State := ℕ × Bool

def running (s : State) : Prop := s.1 ≠ 0

/-- Draw a fresh bit, accumulate its OR, and decrement the saturating counter. -/
def tossStep (s : State) : Weight State :=
  Weight.bind fair (fun b => Weight.pure (s.1 - 1, s.2 || b))

theorem tossStep_isProbability (s : State) : Weight.IsProbability (tossStep s) :=
  fair_isProbability.bind fun b => Weight.isProbability_pure (s.1 - 1, s.2 || b)

def body : Cmd State := .sample tossStep tossStep_isProbability

def source : Cmd State := .while running body

def guarded : Cmd State := .while running (.seq body (.ite running body .skip))

/-- The incorrect optimization executes the second sample even after the count reaches zero. -/
def faulty : Cmd State := .while running (.seq body body)

/-- The source proof uses the sampling and synchronous while rules. -/
theorem source_self_prhl :
    prhl Eq source source (fun s t => s = t ∧ ¬ running s ∧ ¬ running t) := by
  apply prhl_while
  · intro s t h
    subst t
    rfl
  · apply prhl_sample
    intro s t h
    exact coupled_eq_iff.mpr (congrArg tossStep h.1)

/-- Semantic replacement transports the rule-derived source proof to the guarded program. -/
theorem guarded_prhl : prhl Eq source guarded Eq := by
  have hsource : prhl Eq source source Eq :=
    prhl_consequence (fun _ _ h => h) source_self_prhl (fun _ _ h => h.1)
  exact (prhl_congr (c := source) (c' := source) (d := source) (d' := guarded)
    rfl (sem_guarded_unroll running body).symm).mp hsource

/-- No parity or positivity restriction is needed on the initial count. -/
theorem guarded_correct (n : ℕ) (b : Bool) : sem source (n, b) = sem guarded (n, b) :=
  coupled_eq_iff.mp (guarded_prhl (n, b) (n, b) rfl)

theorem source_zero (b : Bool) : sem source (0, b) = Weight.pure (0, b) :=
  sem_while_neg (g := running) (s := (0, b)) (by simp [running]) body

/-- The countdown establishes mass one for every finite initial number of samples. -/
theorem source_isProbability (n : ℕ) (b : Bool) : Weight.IsProbability (sem source (n, b)) := by
  induction n generalizing b with
  | zero =>
    rw [source_zero]
    exact Weight.isProbability_pure _
  | succ n ih =>
    rw [show sem source (n + 1, b) = semLift source (tossStep (n + 1, b)) from
      sem_while_pos (g := running) (s := (n + 1, b)) (by simp [running]) body]
    change Weight.IsProbability (Weight.bind (tossStep (n + 1, b)) (sem source))
    simp only [tossStep, Weight.bind_assoc, Weight.pure_bind, Nat.add_sub_cancel]
    exact fair_isProbability.bind fun bit => ih (b || bit)

theorem guarded_isProbability (n : ℕ) (b : Bool) : Weight.IsProbability (sem guarded (n, b)) := by
  rw [← guarded_correct]
  exact source_isProbability n b

theorem source_one (b : Bool) : sem source (1, b) = tossStep (1, b) := by
  rw [show sem source (1, b) = semLift source (tossStep (1, b)) from
    sem_while_pos (g := running) (s := (1, b)) (by simp [running]) body]
  change Weight.bind (tossStep (1, b)) (sem source) = tossStep (1, b)
  simp only [tossStep, Weight.bind_assoc, Weight.pure_bind, Nat.sub_self, source_zero]

theorem faulty_zero (b : Bool) : sem faulty (0, b) = Weight.pure (0, b) :=
  sem_while_neg (g := running) (s := (0, b)) (by simp [running]) (.seq body body)

theorem faulty_one (b : Bool) :
    sem faulty (1, b) = Weight.bind (tossStep (1, b)) tossStep := by
  rw [show sem faulty (1, b) =
      semLift faulty (Weight.bind (tossStep (1, b)) tossStep) from
    sem_while_pos (g := running) (s := (1, b)) (by simp [running]) (.seq body body)]
  change Weight.bind (Weight.bind (tossStep (1, b)) tossStep) (sem faulty) =
    Weight.bind (tossStep (1, b)) tossStep
  simp only [tossStep, Weight.bind_assoc, Weight.pure_bind, Nat.sub_self, Nat.zero_sub,
    faulty_zero]

/-- Forget the internal countdown and observe only the accumulated Boolean. -/
def observe (μ : Weight State) : Weight Bool := Weight.bind μ (fun s => Weight.pure s.2)

theorem guarded_observations (n : ℕ) (b : Bool) :
    observe (sem source (n, b)) = observe (sem guarded (n, b)) :=
  congrArg observe (guarded_correct n b)

theorem source_observed_one : observe (sem source (1, false)) = fair := by
  rw [source_one]
  simp only [observe, tossStep, Weight.bind_assoc, Weight.pure_bind, Bool.false_or,
    Weight.bind_pure]

/-- Two OR-ed fair bits produce the existing three-quarter-true distribution. -/
theorem faulty_observed_one : observe (sem faulty (1, false)) = biased := by
  rw [faulty_one]
  simp only [observe, tossStep, Weight.bind_assoc, Weight.pure_bind, Bool.false_or]
  have hquarter : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ = 4⁻¹ := by
    rw [← ENNReal.mul_inv (a := 2) (b := 2) (Or.inl (by norm_num))
      (Or.inl (by norm_num))]
    norm_num
  funext b
  cases b <;>
    norm_num [Weight.bind, fair, half, biased, Weight.pure,
      tsum_fintype, Fintype.sum_bool]
  · exact hquarter
  · rw [mul_add, hquarter]
    simp only [← one_div]
    rw [← ENNReal.add_div, ← ENNReal.add_div]
    norm_num

theorem observed_supports_equal :
    Weight.support (observe (sem source (1, false))) =
      Weight.support (observe (sem faulty (1, false))) := by
  rw [source_observed_one, faulty_observed_one]
  exact same_support

theorem false_event_masses :
    Weight.eventMass (observe (sem source (1, false))) {false} = 1 / 2 ∧
      Weight.eventMass (observe (sem faulty (1, false))) {false} = 1 / 4 := by
  rw [source_observed_one, faulty_observed_one]
  norm_num [Weight.eventMass, fair, half, biased, Weight.pure]

/-- The old fair/biased certificate applies to the actual projected loop outputs. -/
def faulty_mass_cert :
    MassDeficitCert Eq (observe (sem source (1, false)))
      (observe (sem faulty (1, false))) := by
  rw [source_observed_one, faulty_observed_one]
  exact CertificateExamples.fair_biased_cert

/-- A program transformer exposing only the observed Boolean result. -/
def observed (c : Cmd State) (μ : Weight State) : Weight Bool := observe (semLift c μ)

/-- The certificate is tied to both actual programs and their concrete initial states. -/
def faulty_bug : BugCert (observed source) (observed faulty) Eq where
  s₀ := (1, false)
  s₀' := (1, false)
  deficit := by
    simpa only [observed, semLift_pure] using faulty_mass_cert

theorem faulty_spec_refuted :
    ¬ quadSem (observed source) (observed faulty)
      (exactly (Weight.pure (1, false)) (Weight.pure (1, false))) (couple Eq) :=
  faulty_bug.refutes (exactly_self _ _)

end

end RelOL.Prob.UnrollExamples
