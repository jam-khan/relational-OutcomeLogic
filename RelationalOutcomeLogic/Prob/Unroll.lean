import RelationalOutcomeLogic.Prob.Lang

/-!
# Guarded two-iteration loop unrolling

The second body execution is guarded, so an exit after the first execution is
preserved. Finite approximants of the unrolled loop form a cofinal subsequence of
the original approximants. Their increasing limits therefore agree, without a
termination or normalization assumption.
-/

namespace RelOL.Prob

variable {α : Type*}

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Execute the body once, then again only if the resulting state still satisfies the guard. -/
def guardedDouble (g : α → Prop) (k : α → Weight α) (s : α) : Weight α :=
  Weight.bind (k s) (fun t => if g t then k t else Weight.pure t)

/-- A positive-fuel continuation already preserves states at which the guard is false. -/
theorem guardedDouble_bind_loopIter_succ (g : α → Prop) (k : α → Weight α)
    (n : ℕ) (s : α) :
    Weight.bind (guardedDouble g k s) (loopIter g k (n + 1)) =
      Weight.bind (k s) (loopIter g k (n + 2)) := by
  rw [guardedDouble, Weight.bind_assoc]
  apply congrArg (Weight.bind (k s))
  funext t
  by_cases ht : g t
  · rw [if_pos ht, loopIter_succ_pos ht]
  · rw [if_neg ht, Weight.pure_bind, loopIter_succ_neg ht, loopIter_succ_neg ht]

/-- Each positive-fuel unrolled approximation equals an odd-indexed original approximation. -/
theorem loopIter_guardedDouble_succ (g : α → Prop) (k : α → Weight α) (n : ℕ) :
    loopIter g (guardedDouble g k) (n + 1) = loopIter g k (2 * n + 1) := by
  induction n with
  | zero =>
    funext s
    simp only [loopIter, Weight.bind_zero]
  | succ n ih =>
    funext s
    have hn : 2 * (n + 1) + 1 = (2 * n + 2) + 1 := by omega
    rw [hn]
    by_cases hs : g s
    · rw [loopIter_succ_pos hs, ih, guardedDouble_bind_loopIter_succ,
        loopIter_succ_pos hs]
    · rw [loopIter_succ_neg hs, loopIter_succ_neg hs]

/-- Guarded unrolling preserves the complete loop semantics, including divergent mass. -/
theorem loopSem_guardedDouble (g : α → Prop) (k : α → Weight α) :
    loopSem g (guardedDouble g k) = loopSem g k := by
  funext s
  apply le_antisymm
  · apply iSup_le
    intro n
    cases n with
    | zero => exact bot_le
    | succ n =>
      rw [loopIter_guardedDouble_succ]
      exact loopIter_le_loopSem g k (2 * n + 1) s
  · apply iSup_le
    intro n
    calc
      loopIter g k n s ≤ loopIter g k (2 * n + 1) s :=
        loopIter_monotone g k (by omega) s
      _ = loopIter g (guardedDouble g k) (n + 1) s :=
        congrFun (loopIter_guardedDouble_succ g k n).symm s
      _ ≤ loopSem g (guardedDouble g k) s :=
        loopIter_le_loopSem g (guardedDouble g k) (n + 1) s

/-- The source-level guarded transformation preserves every state's output weights. -/
theorem sem_guarded_unroll (g : α → Prop) (c : Cmd α) :
    sem (.while g (.seq c (.ite g c .skip))) = sem (.while g c) :=
  loopSem_guardedDouble g (sem c)

theorem semLift_guarded_unroll (g : α → Prop) (c : Cmd α) (μ : Weight α) :
    semLift (.while g (.seq c (.ite g c .skip))) μ = semLift (.while g c) μ := by
  unfold semLift
  rw [sem_guarded_unroll]

end

end RelOL.Prob
