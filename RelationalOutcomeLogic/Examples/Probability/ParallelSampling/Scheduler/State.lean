import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Model

/-!
# An ordered, event-driven worker pool

The active list is in launch order. Its entries have ticket IDs `frontier + i`;
this representation makes duplicate IDs and reordering impossible. A zero
remaining duration is a completed result buffered until its predecessors commit.
Only positive remaining durations occupy worker slots. Launches respect both
worker capacity and a separate window of uncommitted tickets.

`poolFuel` executes actual launch, completion-tick, and commitment transitions.
The potential in `pool` supplies sufficient fuel for every finite input tape;
it is not an algorithmic runtime cutoff. The following invariant module proves
that the answer and accounting are independent of sufficient fuel.
-/

namespace RelOL.Prob.ParallelSampling

universe u
variable {α : Type u}

structure Slot (α : Type u) where
  job : Job α
  remaining : Nat
  deriving DecidableEq

def Slot.fresh (j : Job α) : Slot α := ⟨j, j.duration⟩
def Slot.tick (s : Slot α) : Slot α := { s with remaining := s.remaining - 1 }

/-- Each entry includes its eventual commitment transition. -/
def activePotential (slots : List (Slot α)) : Nat :=
  (slots.map fun s => s.remaining + 1).sum

/-- Unlaunched entries include launch, duration ticks, and commitment. -/
def waitingPotential (jobs : List (Job α)) : Nat :=
  (jobs.map fun j => j.duration + 2).sum

def poolPotential (slots : List (Slot α)) (jobs : List (Job α)) : Nat :=
  activePotential slots + waitingPotential jobs

def running (slots : List (Slot α)) : Nat :=
  (slots.filter fun s => 0 < s.remaining).length

/-- Observable answer and proposal accounting. `discarded` counts launched jobs
cancelled at success, including completed results that never committed. -/
structure PoolResult (α : Type u) where
  answer : Result α
  started : Nat
  committed : Nat
  discarded : Nat
  elapsed : Nat
  deriving DecidableEq

def PoolResult.launch (r : PoolResult α) : PoolResult α :=
  { r with started := r.started + 1 }

def PoolResult.tick (r : PoolResult α) : PoolResult α :=
  { r with elapsed := r.elapsed + 1 }

def PoolResult.commit (j : Job α) (r : PoolResult α) : PoolResult α :=
  { r with answer := if j.accepted then r.answer.prepend j.value else r.answer
           committed := r.committed + 1 }

def poolStop (quota : Nat) (slots : List (Slot α)) : PoolResult α :=
  ⟨if quota = 0 then .success [] else .exhausted [], 0, 0, slots.length, 0⟩

/-- One local transition layer. `resume` receives the remaining quota, ordered
launched window, and unlaunched suffix. A commit takes priority over new launches;
otherwise the pool fills free capacity before advancing time. -/
def poolLayer (workers window : Nat)
    (resume : Nat → List (Slot α) → List (Job α) → PoolResult α)
    (quota : Nat) (slots : List (Slot α)) (jobs : List (Job α)) : PoolResult α :=
  match quota, slots, jobs with
  | 0, _, _ => poolStop 0 slots
  | _ + 1, [], [] => poolStop 1 []
  | n + 1, s :: ss, js =>
      if s.remaining = 0 then
        (resume (if s.job.accepted then n else n + 1) ss js).commit s.job
      else
        match js with
        | j :: rest =>
            if running (s :: ss) < workers ∧ (s :: ss).length < window then
              (resume (n + 1) ((s :: ss) ++ [Slot.fresh j]) rest).launch
            else (resume (n + 1) ((s :: ss).map Slot.tick) js).tick
        | [] => (resume (n + 1) ((s :: ss).map Slot.tick) []).tick
  | n + 1, [], j :: js =>
      -- The public interface requires positive capacity and window.
      if 0 < workers ∧ 0 < window then
        (resume (n + 1) [Slot.fresh j] js).launch
      else poolStop 1 []

def poolFuel (workers window : Nat) :
    Nat → Nat → List (Slot α) → List (Job α) → PoolResult α
  | 0, quota, slots, _ => poolStop quota slots
  | fuel + 1, quota, slots, jobs =>
      poolLayer workers window (poolFuel workers window fuel) quota slots jobs

/-- Finite-tape execution. Positive capacities are hypotheses of the contracts. -/
def pool (workers window quota : Nat) (jobs : List (Job α)) : PoolResult α :=
  poolFuel workers window (waitingPotential jobs) quota [] jobs

@[simp] theorem activePotential_nil : activePotential ([] : List (Slot α)) = 0 := rfl
@[simp] theorem waitingPotential_nil : waitingPotential ([] : List (Job α)) = 0 := rfl
@[simp] theorem activePotential_cons (s : Slot α) (ss : List (Slot α)) :
    activePotential (s :: ss) = s.remaining + 1 + activePotential ss := by
  simp [activePotential]
@[simp] theorem waitingPotential_cons (j : Job α) (js : List (Job α)) :
    waitingPotential (j :: js) = j.duration + 2 + waitingPotential js := by
  simp [waitingPotential]
@[simp] theorem activePotential_append (xs ys : List (Slot α)) :
    activePotential (xs ++ ys) = activePotential xs + activePotential ys := by
  simp [activePotential]
@[simp] theorem activePotential_fresh (j : Job α) :
    activePotential [Slot.fresh j] = j.duration + 1 := by
  simp [Slot.fresh]

/-- Launching consumes one unit of potential, even for unbounded job durations. -/
theorem poolPotential_launch (slots : List (Slot α)) (j : Job α) (js : List (Job α)) :
    poolPotential (slots ++ [Slot.fresh j]) js + 1 =
      poolPotential slots (j :: js) := by
  simp [poolPotential, Slot.fresh]
  omega

/-- Buffered commitment consumes one unit of potential. -/
theorem poolPotential_commit (s : Slot α) (ss : List (Slot α))
    (js : List (Job α)) (hs : s.remaining = 0) :
    poolPotential ss js + 1 = poolPotential (s :: ss) js := by
  simp [poolPotential, hs]
  omega

theorem activePotential_tick_le (slots : List (Slot α)) :
    activePotential (slots.map Slot.tick) ≤ activePotential slots := by
  induction slots with
  | nil => simp
  | cons s ss ih =>
      simp only [List.map_cons, activePotential_cons, Slot.tick]
      omega

/-- Every completion-tick branch has a running head, so it makes progress even
when later jobs finish first. There is no required common duration bound. -/
theorem poolPotential_tick_lt (s : Slot α) (ss : List (Slot α))
    (js : List (Job α)) (hs : s.remaining ≠ 0) :
    poolPotential ((s :: ss).map Slot.tick) js < poolPotential (s :: ss) js := by
  have ht := activePotential_tick_le ss
  simp only [poolPotential, List.map_cons, activePotential_cons, Slot.tick]
  omega

@[simp] theorem jobs_tick (slots : List (Slot α)) :
    (slots.map Slot.tick).map Slot.job = slots.map Slot.job := by
  simp [List.map_map, Function.comp_def, Slot.tick]

@[simp] theorem jobs_launch (slots : List (Slot α)) (j : Job α)
    (js : List (Job α)) :
    (slots ++ [Slot.fresh j]).map Slot.job ++ js =
      slots.map Slot.job ++ j :: js := by
  simp [Slot.fresh, List.append_assoc]

end RelOL.Prob.ParallelSampling
