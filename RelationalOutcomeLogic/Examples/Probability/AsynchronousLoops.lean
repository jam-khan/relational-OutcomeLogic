import RelationalOutcomeLogic.Examples.Probability.Coins
import RelationalOutcomeLogic.Subsumption.PRHL.Asynchronous

/-!
# Mixed asynchronous schedules

The first schedule compares one-step and clamped two-step counter loops. The second
aligns random draws while one program performs additional deterministic control
iterations. Unilateral rank decreases are local proofs, not assumptions about the
final distributions.
-/

namespace RelOL.Prob.AsyncExamples

open Examples

noncomputable section

/-- One position per iteration. -/
def strideOne : Cmd ℕ := .assign (fun i => i + 1)

/-- Up to two positions per iteration, clamped at the common limit. -/
def strideTwo (n : ℕ) : Cmd ℕ := .assign (fun j => min (j + 2) n)

def strideRel (n i j : ℕ) : Prop := i ≤ j ∧ j ≤ i + 1 ∧ j ≤ n

def strideMode (n : ℕ) (p : ℕ × ℕ) : AsyncMode :=
  if p.1 < p.2 then .left else if p.1 < n then .both else .done

/-- A joint step may create a one-position gap; one left step then closes it. -/
def strideSchedule (n : ℕ) :
    AsyncSchedule (strideRel n) (fun i => i < n) (fun j => j < n)
      (sem strideOne) (sem (strideTwo n)) where
  mode := strideMode n
  rank p := p.2 - p.1
  guards := by
    intro i j hij
    rcases hij with ⟨hij, hgap, hjn⟩
    simp only [strideMode]
    split_ifs with hlt hn
    · omega
    · exact ⟨hn, by omega⟩
    · exact ⟨hn, by omega⟩
  left := by
    intro i j hij hm
    have hlt : i < j := by
      by_cases hlt : i < j
      · exact hlt
      · by_cases hn : i < n <;> simp [strideMode, hlt, hn] at hm
    apply Coupled.pure
    change strideRel n (i + 1) j ∧ j - (i + 1) < j - i
    rcases hij with ⟨hij, hgap, hjn⟩
    constructor
    · exact ⟨by omega, by omega, hjn⟩
    · omega
  right := by
    intro i j _ hm
    by_cases hlt : i < j <;> by_cases hn : i < n <;>
      simp [strideMode, hlt, hn] at hm
  both := by
    intro i j hij hm
    have hi : ¬ i < j ∧ i < n := by
      by_cases hlt : i < j
      · simp [strideMode, hlt] at hm
      · by_cases hn : i < n
        · exact ⟨hlt, hn⟩
        · simp [strideMode, hlt, hn] at hm
    apply Coupled.pure
    change strideRel n (i + 1) (min (j + 2) n)
    rcases hij with ⟨hij, hgap, hjn⟩
    simp only [strideRel]
    omega

/-- The loops may execute different numbers of iterations while keeping exact marginals. -/
theorem stride_async_spec (n : ℕ) :
    prhl (strideRel n) (.while (fun i => i < n) strideOne)
      (.while (fun j => j < n) (strideTwo n))
      (fun i j => strideRel n i j ∧ ¬ i < n ∧ ¬ j < n) :=
  prhl_while_async (strideSchedule n)

/-- Both terminal counters equal the bound, including odd bounds and the zero case. -/
theorem stride_terminal_coupling (n : ℕ) :
    Coupled (fun i j => i = n ∧ j = n)
      (sem (.while (fun i => i < n) strideOne) 0)
      (sem (.while (fun j => j < n) (strideTwo n)) 0) := by
  have hc := stride_async_spec n 0 0 (by simp [strideRel])
  apply hc.mono
  intro i j hij
  rcases hij with ⟨⟨hij, hgap, hjn⟩, hin, hjnot⟩
  exact ⟨by omega, by omega⟩

/-- The slow machine separates sampling from its countdown bookkeeping. -/
structure SlowState where
  remaining : ℕ
  catchUp : Bool
  total : ℕ
  deriving DecidableEq

/-- The fast machine samples and updates its countdown in one iteration. -/
structure FastState where
  remaining : ℕ
  total : ℕ
  deriving DecidableEq

def catchUpState (s : SlowState) : SlowState :=
  ⟨s.remaining - 1, false, s.total⟩

def slowDrawState (s : SlowState) (b : Bool) : SlowState :=
  ⟨s.remaining, true, s.total + b.toNat⟩

def fastDrawState (s : FastState) (b : Bool) : FastState :=
  ⟨s.remaining - 1, s.total + b.toNat⟩

def slowDraw (s : SlowState) : Weight SlowState :=
  Weight.bind fair (fun b => Weight.pure (slowDrawState s b))

def fastDraw (s : FastState) : Weight FastState :=
  Weight.bind fair (fun b => Weight.pure (fastDrawState s b))

theorem slowDraw_isProbability (s : SlowState) : Weight.IsProbability (slowDraw s) :=
  fair_isProbability.bind fun _ => Weight.isProbability_pure _

theorem fastDraw_isProbability (s : FastState) : Weight.IsProbability (fastDraw s) :=
  fair_isProbability.bind fun _ => Weight.isProbability_pure _

def slowBody : Cmd SlowState :=
  .ite (fun s => s.catchUp = true) (.assign catchUpState)
    (.sample slowDraw slowDraw_isProbability)

def fastBody : Cmd FastState := .sample fastDraw fastDraw_isProbability

def slowLoop : Cmd SlowState := .while (fun s => 0 < s.remaining) slowBody

def fastLoop : Cmd FastState := .while (fun s => 0 < s.remaining) fastBody

def samplingRel (s : SlowState) (t : FastState) : Prop :=
  s.total = t.total ∧
    if s.catchUp = true then s.remaining = t.remaining + 1 else s.remaining = t.remaining

def samplingMode (p : SlowState × FastState) : AsyncMode :=
  if p.1.catchUp = true then .left
  else if 0 < p.1.remaining then .both else .done

def samplingRank (p : SlowState × FastState) : ℕ := if p.1.catchUp = true then 1 else 0

/-- Every random draw is joint; the only unilateral phase is deterministic bookkeeping. -/
def samplingSchedule :
    AsyncSchedule samplingRel (fun s => 0 < s.remaining) (fun t => 0 < t.remaining)
      (sem slowBody) (sem fastBody) where
  mode := samplingMode
  rank := samplingRank
  guards := by
    intro s t hrel
    rcases hrel with ⟨hsum, hrem⟩
    simp only [samplingMode]
    split_ifs with hphase hn
    · simp only [if_pos hphase] at hrem
      omega
    · simp only [if_neg hphase] at hrem
      exact ⟨hn, by omega⟩
    · simp only [if_neg hphase] at hrem
      exact ⟨hn, by omega⟩
  left := by
    intro s t hrel hm
    have hphase : s.catchUp = true := by
      by_cases hp : s.catchUp = true
      · exact hp
      · by_cases hn : 0 < s.remaining <;> simp [samplingMode, hp, hn] at hm
    change Coupled _ (sem (.ite (fun s => s.catchUp = true)
      (.assign catchUpState) (.sample slowDraw slowDraw_isProbability)) s) _
    rw [sem_ite_pos (g := fun s : SlowState => s.catchUp = true) hphase]
    apply Coupled.pure
    rcases hrel with ⟨hsum, hrem⟩
    simp only [if_pos hphase] at hrem
    constructor
    · simp only [samplingRel, catchUpState, Bool.false_eq_true, if_false]
      exact ⟨hsum, by omega⟩
    · simp [samplingRank, catchUpState, hphase]
  right := by
    intro s t _ hm
    by_cases hp : s.catchUp = true <;> by_cases hn : 0 < s.remaining <;>
      simp [samplingMode, hp, hn] at hm
  both := by
    intro s t hrel hm
    have hphase : s.catchUp ≠ true ∧ 0 < s.remaining := by
      by_cases hp : s.catchUp = true
      · simp [samplingMode, hp] at hm
      · by_cases hn : 0 < s.remaining
        · exact ⟨hp, hn⟩
        · simp [samplingMode, hp, hn] at hm
    change Coupled samplingRel (sem (.ite (fun s => s.catchUp = true)
      (.assign catchUpState) (.sample slowDraw slowDraw_isProbability)) s) (fastDraw t)
    rw [sem_ite_neg (g := fun s : SlowState => s.catchUp = true) hphase.1]
    apply fair_equality_coupling.bind
    intro b b' hbb
    subst b'
    apply Coupled.pure
    rcases hrel with ⟨hsum, hrem⟩
    simp only [if_neg hphase.1] at hrem
    simp only [samplingRel, slowDrawState, fastDrawState, if_true]
    exact ⟨by rw [hsum], by omega⟩

/-- Aligned fair draws and additional left-only bookkeeping preserve the accumulated sum. -/
theorem sampling_async_spec :
    prhl samplingRel slowLoop fastLoop
      (fun s t => samplingRel s t ∧ ¬ 0 < s.remaining ∧ ¬ 0 < t.remaining) :=
  prhl_while_async samplingSchedule

/-- Mirroring the actual scheduler proves the corresponding right-only phases. -/
theorem sampling_async_right_spec :
    prhl (fun t s => samplingRel s t) fastLoop slowLoop
      (fun t s => samplingRel s t ∧ ¬ 0 < t.remaining ∧ ¬ 0 < s.remaining) :=
  prhl_while_async samplingSchedule.swap

theorem sampling_has_left_phase (n total : ℕ) :
    samplingSchedule.mode (⟨n + 1, true, total⟩, ⟨n, total⟩) = .left := rfl

theorem sampling_mirror_has_right_phase (n total : ℕ) :
    samplingSchedule.swap.mode (⟨n, total⟩, ⟨n + 1, true, total⟩) = .right := rfl

theorem sampling_initial_coupled (n total : ℕ) :
    Coupled (fun s t => samplingRel s t ∧ ¬ 0 < s.remaining ∧ ¬ 0 < t.remaining)
      (sem slowLoop ⟨n, false, total⟩) (sem fastLoop ⟨n, total⟩) :=
  sampling_async_spec _ _ (by simp [samplingRel])

/-- An independent countdown argument ensures the fast loop has an actual probability output. -/
theorem fastLoop_isProbability (s : FastState) : Weight.IsProbability (sem fastLoop s) := by
  rcases s with ⟨n, total⟩
  induction n generalizing total with
  | zero =>
      rw [fastLoop, sem_while_neg (g := fun s : FastState => 0 < s.remaining) (by simp)]
      exact Weight.isProbability_pure _
  | succ n ih =>
      rw [fastLoop, sem_while_pos (g := fun s : FastState => 0 < s.remaining) (by simp)]
      change Weight.IsProbability (Weight.bind
        (Weight.bind fair (fun b => Weight.pure (fastDrawState ⟨n + 1, total⟩ b)))
        (sem fastLoop))
      rw [Weight.bind_assoc]
      apply fair_isProbability.bind
      intro b
      rw [Weight.pure_bind]
      exact ih (total + b.toNat)

/-- Exact scheduler marginals transfer termination to the slower implementation. -/
theorem slowLoop_isProbability (n total : ℕ) :
    Weight.IsProbability (sem slowLoop ⟨n, false, total⟩) :=
  (sampling_initial_coupled n total).mass_eq.trans (fastLoop_isProbability ⟨n, total⟩)

/-- The complete distributions of the observed sums coincide for every sample count. -/
theorem sampling_observed_totals_eq (n total : ℕ) :
    Weight.bind (sem slowLoop ⟨n, false, total⟩) (fun s => Weight.pure s.total) =
      Weight.bind (sem fastLoop ⟨n, total⟩) (fun t => Weight.pure t.total) := by
  apply coupled_eq_iff.mp
  apply (sampling_initial_coupled n total).bind
  intro s t hst
  exact Coupled.pure hst.1.1

/-- Joint divergence is allowed: the progress condition applies only to unilateral steps. -/
def jointSpinSchedule :
    AsyncSchedule (Eq : Unit → Unit → Prop) (fun _ => True) (fun _ => True)
      (sem (.skip : Cmd Unit)) (sem (.skip : Cmd Unit)) where
  mode _ := .both
  rank _ := 0
  guards := fun _ _ _ => ⟨trivial, trivial⟩
  left := by intro _ _ _ hm; cases hm
  right := by intro _ _ _ hm; cases hm
  both := fun _ _ h _ => Coupled.pure h

theorem joint_divergence_async :
    prhl (Eq : Unit → Unit → Prop)
      (.while (fun _ => True) .skip) (.while (fun _ => True) .skip)
      (fun a b => a = b ∧ ¬ True ∧ ¬ True) :=
  prhl_while_async jointSpinSchedule

/-- All unilateral stutter steps here are individually lossless and preserve `True`. -/
theorem starving_steps_are_locally_valid :
    ∀ u : Unit, ∀ b : Bool,
      Coupled (fun _ _ => True) (sem (.skip : Cmd Unit) u) (Weight.pure b) :=
  fun _ _ => Coupled.pure trivial

/-- A terminating peer cannot be starved indefinitely just because each local step is valid. -/
theorem unranked_starvation_is_unsound :
    ¬ Coupled (fun _ _ => True)
      (sem (.while (fun _ => True) (.skip : Cmd Unit)) ())
      (sem (.while (fun b : Bool => b = true) (.assign (fun _ => false))) true) := by
  intro hc
  have hm := hc.mass_eq
  have hr : sem (.while (fun b : Bool => b = true) (.assign (fun _ => false))) true =
      Weight.pure false := by
    rw [sem_while_pos (g := fun b : Bool => b = true) rfl]
    change Weight.bind (Weight.pure false)
      (sem (.while (fun b : Bool => b = true) (.assign (fun _ => false)))) = _
    rw [Weight.pure_bind, sem_while_neg (by decide)]
  rw [sem_while_true, hr, Weight.mass_zero, Weight.mass_pure] at hm
  exact zero_ne_one hm

/-- No natural rank can decrease on the starved scheduler's self-loop. -/
theorem starving_step_has_no_rank (rank : Unit × Bool → ℕ) :
    ¬ Coupled (fun u b => rank (u, b) < rank ((), true))
      (Weight.pure ()) (Weight.pure true) := by
  intro h
  have hlt := (Coupled.pure_right_iff.mp h).2 () (by simp)
  exact Nat.lt_irrefl _ hlt

/-- A divergent advancing phase cannot preserve the passive side's point-mass marginal. -/
theorem divergent_advancing_phase_cannot_match_skip :
    ¬ Coupled (fun _ _ => True)
      (sem (.while (fun _ => True) (.skip : Cmd Unit)) ()) (Weight.pure ()) := by
  intro hc
  have hm := hc.mass_eq
  rw [sem_while_true, Weight.mass_zero, Weight.mass_pure] at hm
  exact zero_ne_one hm

end

end RelOL.Prob.AsyncExamples
