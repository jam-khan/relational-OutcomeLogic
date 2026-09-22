import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.State
import RelationalOutcomeLogic.Prob.Logic.DistributionalLoop

/-!
# Fresh sampling at launch in the worker-pool event loop

The executable semantics draws a job only on a launch transition. A finite ghost
suffix is introduced by a reconstruction rule, never by the implementation.
Tick and commit retain the already sampled jobs, including the dependence of
their values on observed completion information. The same transition function
also defines the uncapped loop by disabling the proposal-budget check.
-/

namespace RelOL.Prob.ParallelSampling

universe u
variable {α : Type u}

structure EventState (α : Type u) where
  quota : Nat
  slots : List (Slot α)
  budget : Nat
  values : List α
  started : Nat
  committed : Nat
  elapsed : Nat
  deriving DecidableEq

inductive PoolAction where
  | stop | launch | commit | tick
  deriving DecidableEq

def eventAction (workers window : Nat) (limited : Bool) (s : EventState α) : PoolAction :=
  if s.quota = 0 then .stop else
  match s.slots with
  | [] => if (0 < s.budget ∨ limited = false) ∧ 0 < workers ∧ 0 < window
      then .launch else .stop
  | head :: _ => if head.remaining = 0 then .commit else
      if (0 < s.budget ∨ limited = false) ∧
          running s.slots < workers ∧ s.slots.length < window
      then .launch else .tick

def EventState.launch (s : EventState α) (j : Job α) : EventState α :=
  { s with slots := s.slots ++ [Slot.fresh j], budget := s.budget - 1,
           started := s.started + 1 }

def EventState.tick (s : EventState α) : EventState α :=
  { s with slots := s.slots.map Slot.tick, elapsed := s.elapsed + 1 }

def EventState.commit (s : EventState α) : EventState α :=
  match s.slots with
  | [] => s
  | head :: tail =>
      { s with
        slots := tail
        quota := if head.job.accepted then s.quota - 1 else s.quota
        values := if head.job.accepted then s.values ++ [head.job.value] else s.values
        committed := s.committed + 1 }

def EventState.initial (quota cap : Nat) : EventState α := ⟨quota, [], cap, [], 0, 0, 0⟩

def EventState.observe (s : EventState α) : PoolResult α :=
  ⟨if s.quota = 0 then .success s.values else .exhausted s.values,
   s.started, s.committed, s.slots.length, s.elapsed⟩

noncomputable section

/-- The implementation's random draw occurs exactly at launch. -/
def eventStep (law : Weight (Job α)) (workers window : Nat) (limited : Bool)
    (s : EventState α) : Weight (EventState α) :=
  match eventAction workers window limited s with
  | .stop => Weight.pure s
  | .launch => pushforward s.launch law
  | .commit => Weight.pure s.commit
  | .tick => Weight.pure s.tick

def eventActive (workers window : Nat) (limited : Bool) (s : EventState α) : Prop :=
  eventAction workers window limited s ≠ .stop

def eventRun (law : Weight (Job α)) (workers window : Nat) (limited : Bool) :
    EventState α → Weight (EventState α) :=
  loopSem (eventActive workers window limited) (eventStep law workers window limited)

/-- Both finite and uncapped interfaces use the actual same worker-pool loop. -/
def freshCollector (law : Weight (Job α)) (workers window quota cap : Nat) :
    Weight (PoolResult α) :=
  pushforward EventState.observe (eventRun law workers window true (EventState.initial quota cap))

def uncappedCollector (law : Weight (Job α)) (workers window quota : Nat) :
    Weight (PoolResult α) :=
  pushforward EventState.observe (eventRun law workers window false (EventState.initial quota 0))

def eventReconstruction (law : Weight (Job α)) (s : EventState α) :
    Weight (EventState α × List (Job α)) :=
  pushforward (fun jobs => (s, jobs)) (draws law s.budget)

def ghostEventStep (workers window : Nat) (s : EventState α × List (Job α)) :
    Weight (EventState α × List (Job α)) :=
  match eventAction workers window true s.1 with
  | .stop => Weight.pure s
  | .launch => match s.2 with
    | [] => 0
    | j :: js => Weight.pure (s.1.launch j, js)
  | .commit => Weight.pure (s.1.commit, s.2)
  | .tick => Weight.pure (s.1.tick, s.2)

theorem eventAction_launch_budget (workers window : Nat) (s : EventState α)
    (h : eventAction workers window true s = .launch) : 0 < s.budget := by
  unfold eventAction at h
  split at h
  · contradiction
  · split at h
    · split at h
      · simp_all
      · contradiction
    · split at h
      · contradiction
      · split at h
        · simp_all
        · contradiction

@[simp] theorem EventState.commit_budget (s : EventState α) : s.commit.budget = s.budget := by
  cases hs : s.slots <;> simp [EventState.commit, hs]

/-- The one-event reconstruction square. No assertion of posterior independence
of the active slots is used: only the unlaunched suffix is fresh. -/
theorem event_reconstruction_step (law : Weight (Job α)) (workers window : Nat)
    (s : EventState α) :
    Weight.bind (eventReconstruction law s) (ghostEventStep workers window) =
      Weight.bind (eventStep law workers window true s) (eventReconstruction law) := by
  rw [eventReconstruction, bind_pushforward]
  cases ha : eventAction workers window true s with
  | stop => simp [ghostEventStep, eventStep, ha, eventReconstruction, pushforward]
  | tick => simp [ghostEventStep, eventStep, ha, eventReconstruction, EventState.tick,
      pushforward]
  | commit => simp [ghostEventStep, eventStep, ha, eventReconstruction, pushforward]
  | launch =>
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (eventAction_launch_budget workers window s ha))
    simp only [hm, draws, Weight.bind_assoc, Weight.pure_bind, ghostEventStep, ha,
      eventStep, eventReconstruction, EventState.launch,
      Nat.succ_sub_one, pushforward]

theorem event_reconstruction_quad (law : Weight (Job α)) (workers window : Nat) :
    Generic.quad (Generic.lifted (eventReconstruction law))
      (eventStep law workers window true) (ghostEventStep workers window)
      (Generic.lifted (eventReconstruction law)) :=
  Generic.quad_lifted (event_reconstruction_step law workers window)

/-- Local reconstruction and guard compatibility prove the complete lazy loop,
including all finite-runtime bookkeeping and any possible divergence. -/
theorem event_loop_quad (law : Weight (Job α)) (workers window : Nat) :
    Generic.quad (Generic.lifted (eventReconstruction law))
      (eventRun law workers window true)
      (loopSem (fun s => eventActive workers window true s.1) (ghostEventStep workers window))
      (Generic.lifted (eventReconstruction law)) := by
  apply quad_lifted_while
  · intro s t ht
    obtain ⟨jobs, _, hpair⟩ := (Weight.mem_support_bind_iff _ _ _).mp ht
    simp only [Weight.support_pure, Set.mem_singleton_iff] at hpair
    subst t
    rfl
  · exact event_reconstruction_quad law workers window

theorem eventReconstruction_observe (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (s : EventState α) :
    pushforward (fun p => p.1.observe) (eventReconstruction law s) =
      Weight.pure s.observe := by
  rw [eventReconstruction, pushforward, bind_pushforward]
  change Weight.bind (draws law s.budget) (fun _ => Weight.pure s.observe) = Weight.pure s.observe
  exact Weight.bind_const_of_isProbability _ (draws_probability law hlaw _) _

/-- Erasing the finite ghost suffix preserves the actual collector's observations. -/
theorem event_loop_observed (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (workers window : Nat) (s : EventState α) :
    pushforward EventState.observe (eventRun law workers window true s) =
      Weight.bind (eventReconstruction law s) (fun t =>
        pushforward (fun p => p.1.observe)
          (loopSem (fun p => eventActive workers window true p.1)
            (ghostEventStep workers window) t)) := by
  have h := Generic.quad_lifted_iff.mp (event_loop_quad law workers window) s
  have ho := congrArg (pushforward (fun p => p.1.observe)) h
  simp only [Generic.weight_bind_eq, pushforward_bind, eventReconstruction_observe law hlaw] at ho
  exact ho.symm

end
end RelOL.Prob.ParallelSampling
