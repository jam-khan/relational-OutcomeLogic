import RelationalOutcomeLogic.Prob.Lang
import Mathlib.Tactic.NormNum

/-!
# Bounded randomized search

The full scan consumes all trials and records whether any trial succeeded. The
early-exit implementation stops after its first success. Trial probabilities are
parameters; the state records the remaining budget and the accumulated answer.
-/

namespace RelOL.Prob.Search

open scoped ENNReal

noncomputable section

abbrev State := ℕ × Bool

/-- A normalized Bernoulli trial, allowing deterministic boundary cases. -/
structure Trial where
  miss : ℝ≥0∞
  hit : ℝ≥0∞
  normalized : miss + hit = 1

/-- The found flag is sticky; each trial consumes one unit of budget. -/
def draw (T : Trial) (s : State) : Weight State :=
  T.miss • Weight.pure (s.1 - 1, s.2) + T.hit • Weight.pure (s.1 - 1, true)

theorem draw_isProbability (T : Trial) (s : State) : Weight.IsProbability (draw T s) := by
  change Weight.mass (draw T s) = 1
  simpa only [draw, Weight.mass_add, Weight.mass_smul, Weight.mass_pure, mul_one]
    using T.normalized

def body (T : Trial) : Cmd State := .sample (draw T) (draw_isProbability T)

def fullGuard (s : State) : Prop := 0 < s.1

def earlyGuard (s : State) : Prop := 0 < s.1 ∧ s.2 = false

def full (T : Trial) : Cmd State := .while fullGuard (body T)

def early (T : Trial) : Cmd State := .while earlyGuard (body T)

/-- A fresh search starts with no previously found success. -/
def seed (n : ℕ) : Weight State := Weight.pure (n, false)

/-- The externally visible result forgets how many trials remain. -/
def observe (μ : Weight State) : Weight Bool :=
  Weight.bind μ (fun s => Weight.pure s.2)

def observed (c : Cmd State) (μ : Weight State) : Weight Bool := observe (semLift c μ)

@[simp] theorem observe_zero : observe 0 = 0 := Weight.zero_bind _

@[simp] theorem observe_pure (s : State) : observe (Weight.pure s) = Weight.pure s.2 :=
  Weight.pure_bind _ _

theorem observe_add (μ ν : Weight State) : observe (μ + ν) = observe μ + observe ν :=
  Weight.add_bind _ _ _

theorem observe_smul (r : ℝ≥0∞) (μ : Weight State) : observe (r • μ) = r • observe μ :=
  Weight.smul_bind _ _ _

@[simp] theorem observed_seed (c : Cmd State) (n : ℕ) :
    observed c (seed n) = observe (sem c (n, false)) := by
  simp only [observed, seed, semLift_pure]

/-- Success probability, written recursively to include probability-zero boundaries. -/
def successMass (T : Trial) : ℕ → ℝ≥0∞
  | 0 => 0
  | n + 1 => T.miss * successMass T n + T.hit

@[simp] theorem successMass_zero (T : Trial) : successMass T 0 = 0 := rfl

theorem successMass_succ (T : Trial) (n : ℕ) :
    successMass T (n + 1) = T.miss * successMass T n + T.hit := rfl

theorem failure_add_success (T : Trial) (n : ℕ) :
    T.miss ^ n + successMass T n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', successMass_succ, ← add_assoc, ← mul_add, ih, mul_one, T.normalized]

@[simp] theorem full_sem_zero (T : Trial) (b : Bool) :
    sem (full T) (0, b) = Weight.pure (0, b) := by
  rw [full, sem_while_neg (g := fullGuard) (by simp [fullGuard])]

/-- Unfold one budgeted trial without changing the probability parameters. -/
theorem full_sem_succ (T : Trial) (n : ℕ) (b : Bool) :
    sem (full T) (n + 1, b) =
      T.miss • sem (full T) (n, b) + T.hit • sem (full T) (n, true) := by
  rw [full, sem_while_pos (g := fullGuard) (by simp [fullGuard])]
  change Weight.bind (draw T (n + 1, b)) (sem (full T)) = _
  simp only [draw, Weight.add_bind, Weight.smul_bind, Weight.pure_bind, Nat.add_sub_cancel]
  rfl

/-- Once success is found, the full scan only drains its budget. -/
theorem full_sem_true (T : Trial) (n : ℕ) :
    sem (full T) (n, true) = Weight.pure (0, true) := by
  induction n with
  | zero => exact full_sem_zero T true
  | succ n ih =>
      rw [full_sem_succ, ih, ← add_smul, T.normalized, one_smul]

/-- Exact output weights of a fresh full scan, including all deterministic boundary trials. -/
theorem full_sem_false (T : Trial) (n : ℕ) :
    sem (full T) (n, false) =
      T.miss ^ n • Weight.pure (0, false) + successMass T n • Weight.pure (0, true) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [full_sem_succ, ih, full_sem_true, smul_add, smul_smul, smul_smul,
        add_assoc, ← add_smul, successMass_succ, pow_succ']

/-- A finite full scan always returns a normalized distribution. -/
theorem full_isProbability (T : Trial) (s : State) : Weight.IsProbability (sem (full T) s) := by
  rcases s with ⟨n, b⟩
  cases b with
  | false =>
      change Weight.mass (sem (full T) (n, false)) = 1
      rw [full_sem_false, Weight.mass_add, Weight.mass_smul, Weight.mass_smul,
        Weight.mass_pure, Weight.mass_pure, mul_one, mul_one]
      exact failure_add_success T n
  | true =>
      rw [full_sem_true]
      exact Weight.isProbability_pure _

theorem observe_full_false (T : Trial) (n : ℕ) :
    observe (sem (full T) (n, false)) =
      T.miss ^ n • Weight.pure false + successMass T n • Weight.pure true := by
  rw [full_sem_false, observe_add, observe_smul, observe_smul, observe_pure, observe_pure]

theorem observed_full_seed (T : Trial) (n : ℕ) :
    observed (full T) (seed n) =
      T.miss ^ n • Weight.pure false + successMass T n • Weight.pure true := by
  rw [observed_seed, observe_full_false]

theorem observe_full_true (T : Trial) (n : ℕ) :
    observe (sem (full T) (n, true)) = Weight.pure true := by
  rw [full_sem_true, observe_pure]

/-- A fair trial for concrete quantitative certificates. -/
def Trial.fair : Trial where
  miss := 1 / 2
  hit := 1 / 2
  normalized := by
    rw [← ENNReal.add_div]
    norm_num only [one_add_one_eq_two]
    exact ENNReal.div_self (by norm_num) (by norm_num)

end

end RelOL.Prob.Search
