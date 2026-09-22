import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.State
import RelationalOutcomeLogic.Generic.Loops.Bounded
import RelationalOutcomeLogic.Bridges.Probability

/-!
# Rule derivation for ordered scheduling

The kernel layer is the monadic lifting of `poolLayer`: deterministic updates
map over an arbitrary verified continuation. The recursion rule consumes its
local obligation, indexed by the remaining event potential. No whole-program
scheduler equality is a premise of the derivation.
-/

namespace RelOL.Prob.ParallelSampling

universe u
variable {α : Type u}

structure PoolInput (α : Type u) where
  quota : Nat
  slots : List (Slot α)
  jobs : List (Job α)

abbrev PoolObservation (α : Type u) := Result α × Nat

def PoolInput.potential (s : PoolInput α) : Nat := poolPotential s.slots s.jobs

def PoolInput.expected (s : PoolInput α) : PoolObservation α :=
  (select s.quota (s.slots.map Slot.job ++ s.jobs),
    used s.quota (s.slots.map Slot.job ++ s.jobs))

def PoolResult.observe (r : PoolResult α) : PoolObservation α := (r.answer, r.committed)

def commitObservation (j : Job α) (o : PoolObservation α) : PoolObservation α :=
  (if j.accepted then o.1.prepend j.value else o.1, o.2 + 1)

noncomputable section

def poolKernelLayer (workers window : Nat)
    (resume : PoolInput α → Weight (PoolResult α)) (s : PoolInput α) :
    Weight (PoolResult α) :=
  match s.quota, s.slots, s.jobs with
  | 0, slots, _ => Weight.pure (poolStop 0 slots)
  | _ + 1, [], [] => Weight.pure (poolStop 1 [])
  | n + 1, slot :: slots, jobs =>
      if slot.remaining = 0 then
        pushforward (PoolResult.commit slot.job)
          (resume ⟨if slot.job.accepted then n else n + 1, slots, jobs⟩)
      else
        match jobs with
        | j :: rest =>
            if running (slot :: slots) < workers ∧ (slot :: slots).length < window then
              pushforward PoolResult.launch
                (resume ⟨n + 1, (slot :: slots) ++ [Slot.fresh j], rest⟩)
            else pushforward PoolResult.tick
              (resume ⟨n + 1, (slot :: slots).map Slot.tick, jobs⟩)
        | [] => pushforward PoolResult.tick
            (resume ⟨n + 1, (slot :: slots).map Slot.tick, []⟩)
  | n + 1, [], j :: jobs =>
      if 0 < workers ∧ 0 < window then
        pushforward PoolResult.launch (resume ⟨n + 1, [Slot.fresh j], jobs⟩)
      else Weight.pure (poolStop 1 [])

/-- The rule operates on the actual event interpreter's one-step unfolding. -/
theorem poolKernelLayer_pure (workers window : Nat)
    (resume : Nat → List (Slot α) → List (Job α) → PoolResult α) (s : PoolInput α) :
    poolKernelLayer workers window (fun s => Weight.pure (resume s.quota s.slots s.jobs)) s =
      Weight.pure (poolLayer workers window resume s.quota s.slots s.jobs) := by
  rcases s with ⟨quota, slots, jobs⟩
  cases quota with
  | zero => rfl
  | succ n =>
      cases slots with
      | nil =>
          cases jobs with
          | nil => rfl
          | cons j js =>
              by_cases h : 0 < workers ∧ 0 < window <;>
                simp [poolKernelLayer, poolLayer, h]
      | cons slot slots =>
          by_cases hs : slot.remaining = 0
          · simp [poolKernelLayer, poolLayer, hs]
          · cases jobs with
            | nil => simp [poolKernelLayer, poolLayer, hs]
            | cons j js =>
                by_cases hc : running (slot :: slots) < workers ∧ slots.length + 1 < window <;>
                  simp [poolKernelLayer, poolLayer, hs, hc]

private theorem observe_launch (μ : Weight (PoolResult α)) :
    pushforward PoolResult.observe (pushforward PoolResult.launch μ) =
      pushforward PoolResult.observe μ := by
  simp only [pushforward, Weight.bind_assoc, Weight.pure_bind,
    PoolResult.launch, PoolResult.observe]

private theorem observe_tick (μ : Weight (PoolResult α)) :
    pushforward PoolResult.observe (pushforward PoolResult.tick μ) =
      pushforward PoolResult.observe μ := by
  simp only [pushforward, Weight.bind_assoc, Weight.pure_bind,
    PoolResult.tick, PoolResult.observe]

private theorem observe_commit (j : Job α) (μ : Weight (PoolResult α)) :
    pushforward PoolResult.observe (pushforward (PoolResult.commit j) μ) =
      pushforward (commitObservation j) (pushforward PoolResult.observe μ) := by
  simp only [pushforward, Weight.bind_assoc, Weight.pure_bind,
    PoolResult.commit, PoolResult.observe, commitObservation]

/-- Local launch, completion and commitment contracts. The premise describes
arbitrary continuations; it does not refer to executing the recursive program. -/
theorem poolKernelLayer_contract (workers window : Nat) (hworkers : 0 < workers)
    (hwindow : 0 < window) (fuel : Nat) (resume : PoolInput α → Weight (PoolResult α))
    (hresume : ∀ s, s.potential ≤ fuel →
      pushforward PoolResult.observe (resume s) = Weight.pure s.expected)
    (s : PoolInput α) (hfuel : s.potential ≤ fuel + 1) :
    pushforward PoolResult.observe (poolKernelLayer workers window resume s) =
      Weight.pure s.expected := by
  rcases s with ⟨quota, slots, jobs⟩
  change poolPotential slots jobs ≤ fuel + 1 at hfuel
  cases quota with
  | zero => simp [poolKernelLayer, poolStop, PoolResult.observe, PoolInput.expected, select, used]
  | succ n =>
      cases slots with
      | nil =>
          cases jobs with
          | nil => simp [poolKernelLayer, poolStop, PoolResult.observe, PoolInput.expected,
              select, used]
          | cons j js =>
              have he := poolPotential_launch ([] : List (Slot α)) j js
              have hi := hresume ⟨n + 1, [Slot.fresh j], js⟩ (by
                change poolPotential [Slot.fresh j] js ≤ fuel
                simpa using (by omega : poolPotential ([] ++ [Slot.fresh j]) js ≤ fuel))
              simpa [poolKernelLayer, hworkers, hwindow, observe_launch,
                PoolInput.expected, Slot.fresh] using hi
      | cons slot slots =>
          by_cases hs : slot.remaining = 0
          · have he := poolPotential_commit slot slots jobs hs
            have hi := hresume ⟨if slot.job.accepted then n else n + 1, slots, jobs⟩
              (by change poolPotential slots jobs ≤ fuel; omega)
            simp only [poolKernelLayer, hs, ↓reduceIte, observe_commit, hi, pushforward_pure]
            congr 1
            cases ha : slot.job.accepted <;>
              simp [commitObservation, PoolInput.expected, select, used, ha, Nat.add_comm]
          · have he := poolPotential_tick_lt slot slots jobs hs
            cases jobs with
            | nil =>
                have hi := hresume ⟨n + 1, (slot :: slots).map Slot.tick, []⟩
                  (by change poolPotential ((slot :: slots).map Slot.tick) [] ≤ fuel; omega)
                simpa [poolKernelLayer, hs, observe_tick, PoolInput.expected,
                  Slot.tick, Function.comp_def] using hi
            | cons j js =>
                by_cases hc : running (slot :: slots) < workers ∧ slots.length + 1 < window
                · have he' := poolPotential_launch (slot :: slots) j js
                  have hi := hresume ⟨n + 1, (slot :: slots) ++ [Slot.fresh j], js⟩
                    (by change poolPotential ((slot :: slots) ++ [Slot.fresh j]) js ≤ fuel; omega)
                  simpa [poolKernelLayer, hs, hc, observe_launch, PoolInput.expected,
                    Slot.fresh] using hi
                · have hi := hresume ⟨n + 1, (slot :: slots).map Slot.tick, j :: js⟩
                    (by
                      change poolPotential ((slot :: slots).map Slot.tick) (j :: js) ≤ fuel
                      omega)
                  simpa [poolKernelLayer, hs, hc, observe_tick, PoolInput.expected,
                    Slot.tick, Function.comp_def] using hi

/-- The input family names the complete hidden tape and records available
potential. Exact input weights suffice here; probabilistic tape generation is
composed outside this deterministic scheduling derivation. -/
def poolPre (fuel : Nat) (s : PoolInput α) : Generic.RAssn Weight (PoolInput α) (PoolInput α) :=
  fun μ ν => μ = Weight.pure s ∧ ν = Weight.pure s ∧ s.potential ≤ fuel

def poolPost (s : PoolInput α) :
    Generic.RAssn Weight (PoolObservation α) (PoolResult α) :=
  fun μ ν => μ = Weight.pure s.expected ∧ pushforward PoolResult.observe ν = μ

def poolReference (_ : Nat) (s : PoolInput α) : Weight (PoolObservation α) :=
  Weight.pure s.expected

def poolKernel (workers window fuel : Nat) (s : PoolInput α) : Weight (PoolResult α) :=
  Weight.pure (poolFuel workers window fuel s.quota s.slots s.jobs)

/-- The complete event-loop contract is derived through the shared recursion
rule from the local continuation contract above. It proves the joint result and
stopping-ticket observation, including exhausted partial populations. -/
theorem poolFuel_quad (workers window : Nat) (hworkers : 0 < workers)
    (hwindow : 0 < window) (fuel : Nat) (s : PoolInput α) :
    Generic.quad (poolPre fuel s) (poolReference fuel) (poolKernel workers window fuel)
      (poolPost s) := by
  apply Generic.quad_recursion_family poolPre (fun _ => poolPost)
    poolReference (poolKernel workers window)
    (fun _ _ s => Weight.pure s.expected)
    (fun _ => poolKernelLayer workers window)
    (fun _ => rfl) ?_ ?_ ?_ fuel s
  · intro n
    funext s
    exact (poolKernelLayer_pure workers window (poolFuel workers window n) s).symm
  · intro s μ ν h
    rcases h with ⟨rfl, rfl, henergy⟩
    simp only [Generic.weight_bind_eq, Weight.pure_bind]
    constructor
    · rfl
    · rcases s with ⟨quota, slots, jobs⟩
      have hempty : slots = [] ∧ jobs = [] := by
        change poolPotential slots jobs ≤ 0 at henergy
        cases slots with
        | cons slot slots => simp [poolPotential] at henergy
        | nil =>
            constructor
            · rfl
            · cases jobs with
              | nil => rfl
              | cons j js => simp [poolPotential] at henergy
      rcases hempty with ⟨rfl, rfl⟩
      cases quota <;>
        simp [poolKernel, poolReference, poolFuel, poolStop, PoolResult.observe,
          PoolInput.expected, select, used]
  · intro n k l hkl s μ ν h
    rcases h with ⟨rfl, rfl, henergy⟩
    simp only [Generic.weight_bind_eq, Weight.pure_bind]
    constructor
    · rfl
    · apply poolKernelLayer_contract workers window hworkers hwindow n l ?_ s henergy
      intro next hnext
      have hc := hkl next (Weight.pure next) (Weight.pure next) ⟨rfl, rfl, hnext⟩
      simp only [Generic.weight_bind_eq, Weight.pure_bind, poolPost] at hc
      exact hc.2.trans hc.1

/-- Point-input consequence of the rule derivation, convenient for composing
with a probabilistic finite-tape sampler. -/
theorem poolFuel_observed (workers window : Nat) (hworkers : 0 < workers)
    (hwindow : 0 < window) (fuel : Nat) (s : PoolInput α)
    (hs : s.potential ≤ fuel) :
    pushforward PoolResult.observe (poolKernel workers window fuel s) =
      Weight.pure s.expected := by
  have h := poolFuel_quad workers window hworkers hwindow fuel s
    (Weight.pure s) (Weight.pure s) ⟨rfl, rfl, hs⟩
  simp only [Generic.weight_bind_eq, Weight.pure_bind, poolPost, poolReference] at h
  exact h.2

end
end RelOL.Prob.ParallelSampling
