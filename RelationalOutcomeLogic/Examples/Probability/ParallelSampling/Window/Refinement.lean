import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Reference.Costs
import RelationalOutcomeLogic.Prob.Logic.DistributionalLoop

/-!
# A sliding window and its distributional loop invariant

The protocol retains `w` pending jobs and launches one fresh job before each
commit, so the launch window is `W = w + 1`. It commits the oldest launch ID.
This module abstracts the finite wait until that ticket completes; the event
scheduler separately realizes ordered commitment. Runtime and value can be
arbitrarily dependent within each job.

The proof uses a local queue-rotation square, `quad_lifted`, and the library's
full-loop reconstruction rule. It never assumes equality of complete runs.
-/
namespace RelOL.Prob.ParallelSampling

universe u
variable {α σ : Type u}
noncomputable section

/-- Sampling an iid finite prefix and appending one fresh draw gives the next prefix. -/
lemma draws_append_one (law : Weight (Job α)) (w : Nat)
    {γ : Type u} (f : List (Job α) → Weight γ) :
    Weight.bind (draws law w) (fun js => Weight.bind law (fun j => f (js ++ [j]))) =
      Weight.bind (draws law (w + 1)) f := by
  induction w generalizing f with
  | zero => simp [draws, Weight.bind_assoc]
  | succ w ih =>
      simp only [draws, Weight.bind_assoc, Weight.pure_bind, List.cons_append]
      congr 1
      funext j
      simpa only [draws, Weight.bind_assoc, Weight.pure_bind] using ih (fun js => f (j :: js))

/-- Hidden pending jobs are reconstructed from fresh iid draws. -/
def pending (law : Weight (Job α)) (w : Nat) (s : σ) : Weight (σ × List (Job α)) :=
  Weight.bind (draws law w) fun js => Weight.pure (s, js)

def consume (update : σ → Job α → σ) (s : σ) : List (Job α) → σ × List (Job α)
  | [] => (s, [])
  | j :: js => (update s j, js)

/-- One fresh proposal on the sequential side. -/
def proposalStep (law : Weight (Job α)) (update : σ → Job α → σ) (s : σ) : Weight σ :=
  Weight.bind law (fun j => Weight.pure (update s j))

/-- Replenish the window and commit its oldest ticket, keeping the suffix hidden. -/
def windowStep (law : Weight (Job α)) (update : σ → Job α → σ)
    (s : σ × List (Job α)) : Weight (σ × List (Job α)) :=
  Weight.bind law fun j => Weight.pure (consume update s.1 (s.2 ++ [j]))

/-- The crucial local square: the retained suffix remains iid jointly with the committed state. -/
lemma window_square (law : Weight (Job α)) (w : Nat) (update : σ → Job α → σ) (s : σ) :
    Weight.bind (pending law w s) (windowStep law update) =
      Weight.bind (proposalStep law update s) (pending law w) := by
  simp only [pending, proposalStep, Weight.bind_assoc, Weight.pure_bind]
  change Weight.bind (draws law w) (fun js => Weight.bind law
    (fun j => Weight.pure (consume update s (js ++ [j])))) = _
  rw [draws_append_one law w (fun js => Weight.pure (consume update s js))]
  simp only [draws, Weight.bind_assoc, Weight.pure_bind, consume]

/-- A local judgment, suitable for both bounded and unbounded sequencing rules. -/
theorem window_step_quad (law : Weight (Job α)) (w : Nat) (update : σ → Job α → σ) :
    Generic.quad (Generic.lifted (pending law w)) (proposalStep law update)
      (windowStep law update) (Generic.lifted (pending law w)) :=
  Generic.quad_lifted (window_square law w update)

lemma pending_support (law : Weight (Job α)) (w : Nat) (s : σ)
    (t : σ × List (Job α)) (ht : t ∈ Weight.support (pending law w s)) : t.1 = s := by
  obtain ⟨js, _, hjs⟩ := (Weight.mem_support_bind_iff _ _ _).mp ht
  rw [Weight.support_pure, Set.mem_singleton_iff] at hjs
  exact congrArg Prod.fst hjs

/-- The local judgment is lifted by the full-loop rule; divergent mass is preserved too. -/
theorem window_loop_quad (law : Weight (Job α)) (w : Nat)
    (update : σ → Job α → σ) (guard : σ → Prop) :
    Generic.quad (Generic.lifted (pending law w))
      (loopSem guard (proposalStep law update))
      (loopSem (fun s => guard s.1) (windowStep law update))
      (Generic.lifted (pending law w)) := by
  apply quad_lifted_while
  · intro s t ht
    rw [pending_support law w s t ht]
  · exact window_step_quad law w update

lemma pending_probability (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (w : Nat) (s : σ) : Weight.IsProbability (pending law w s) :=
  (draws_probability law hlaw w).bind (fun _ => Weight.isProbability_pure _)

lemma pending_observe (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (w : Nat) (s : σ) : pushforward Prod.fst (pending law w s) = Weight.pure s := by
  simp only [pending, pushforward_bind, pushforward_pure]
  exact Weight.bind_const_of_isProbability _ (draws_probability law hlaw w) _

/-- Erase the initial prefetch and hidden suffix after the rule-derived loop. -/
theorem window_loop_observe (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (w : Nat) (update : σ → Job α → σ) (guard : σ → Prop) (s : σ) :
    pushforward Prod.fst
      (Weight.bind (pending law w s)
        (loopSem (fun t => guard t.1) (windowStep law update))) =
      loopSem guard (proposalStep law update) s := by
  have h := window_loop_quad law w update guard (Weight.pure s) (pending law w s)
    (Generic.lifted_pure (pending law w) s)
  change Weight.bind (pending law w s) (loopSem (fun t => guard t.1) (windowStep law update)) =
    Weight.bind (Weight.bind (Weight.pure s) (loopSem guard (proposalStep law update)))
      (pending law w) at h
  rw [Weight.pure_bind] at h
  rw [h, pushforward_bind]
  simp only [pending_observe law hlaw, Weight.bind_pure]

end
end RelOL.Prob.ParallelSampling
