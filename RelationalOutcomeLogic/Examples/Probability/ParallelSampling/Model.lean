import RelationalOutcomeLogic.Algebra.ENNReal.Sequencing
import RelationalOutcomeLogic.Prob.Coupling.Observation

/-!
# Jobs and observable populations

A job jointly samples its value, acceptance decision, and runtime. No independence
between these fields is assumed. `ticks + 1` is its positive, finite duration;
the law need not have a common runtime bound. Launches in one generation use a
fixed law, independently. Exhaustion remains observable in the capped interface.
-/

namespace RelOL.Prob.ParallelSampling

universe u
variable {α : Type u}

structure Job (α : Type u) where
  value : α
  accepted : Bool
  ticks : Nat
  deriving DecidableEq

def Job.duration (j : Job α) : Nat := j.ticks + 1

@[simp] theorem Job.duration_pos (j : Job α) : 0 < j.duration := Nat.zero_lt_succ _

inductive Result (α : Type u) where
  | success (population : List α)
  | exhausted (population : List α)
  deriving DecidableEq

def Result.population : Result α → List α
  | .success xs | .exhausted xs => xs

def Result.prepend (a : α) : Result α → Result α
  | .success xs => .success (a :: xs)
  | .exhausted xs => .exhausted (a :: xs)

/-- Ordered selection, including the partial population on proposal exhaustion. -/
def select : Nat → List (Job α) → Result α
  | 0, _ => .success []
  | _ + 1, [] => .exhausted []
  | n + 1, j :: js =>
      if j.accepted then (select n js).prepend j.value else select (n + 1) js

/-- Number of prefix tickets required before success or proposal exhaustion. -/
def used : Nat → List (Job α) → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, j :: js => 1 + if j.accepted then used n js else used (n + 1) js

noncomputable section

/-- Finite ghost prefixes only: no distribution on an infinite random tape. -/
def draws (law : Weight (Job α)) : Nat → Weight (List (Job α))
  | 0 => Weight.pure []
  | m + 1 => Weight.bind law fun j =>
      Weight.bind (draws law m) fun js => Weight.pure (j :: js)

theorem draws_probability (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (m : Nat) : Weight.IsProbability (draws law m) := by
  induction m with
  | zero => exact Weight.isProbability_pure _
  | succ m ih =>
      exact Weight.IsProbability.bind hlaw (fun _ =>
        Weight.IsProbability.bind ih (fun _ => Weight.isProbability_pure _))

/-- A finite ghost sampler produces exactly the requested number of tickets. -/
theorem draws_support_length (law : Weight (Job α)) (m : Nat) (jobs : List (Job α))
    (h : jobs ∈ Weight.support (draws law m)) : jobs.length = m := by
  induction m generalizing jobs with
  | zero =>
      simp only [draws, Weight.support_pure, Set.mem_singleton_iff] at h
      subst jobs
      rfl
  | succ m ih =>
      obtain ⟨j, _, hj⟩ := (Weight.mem_support_bind_iff _ _ _).mp h
      obtain ⟨js, hjs, hcons⟩ := (Weight.mem_support_bind_iff _ _ _).mp hj
      simp only [Weight.support_pure, Set.mem_singleton_iff] at hcons
      subst jobs
      simp [ih js hjs]

end
end RelOL.Prob.ParallelSampling
