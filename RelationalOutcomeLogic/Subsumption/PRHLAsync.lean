import RelationalOutcomeLogic.Prob.AsyncLoop
import RelationalOutcomeLogic.Subsumption.PRHLOneSided

/-!
# Mixed asynchronous while rules

A schedule supplies local exact couplings and a decreasing rank for unilateral
steps. The scheduler theorem proves its final marginals; they are not assumptions
of these weighted and pRHL rules.
-/

namespace RelOL.Prob

variable {α β : Type*}

/-- Reverse a schedule, turning left-only phases into right-only phases. -/
def AsyncSchedule.swap {R : α → β → Prop} {g : α → Prop} {h : β → Prop}
    {k : α → Weight α} {l : β → Weight β} (S : AsyncSchedule R g h k l) :
    AsyncSchedule (fun b a => R a b) h g l k where
  mode p := (S.mode (p.2, p.1)).swap
  rank p := S.rank (p.2, p.1)
  guards := by
    intro b a hab
    have hs := S.guards a b hab
    cases hm : S.mode (a, b) <;> simp_all [AsyncMode.swap]
  left := by
    intro b a hab hm
    change (S.mode (a, b)).swap = .left at hm
    have hm' : S.mode (a, b) = .right := by
      have hs := congrArg AsyncMode.swap hm
      rw [AsyncMode.swap_swap] at hs
      simpa only [AsyncMode.swap] using hs
    exact (S.right a b hab hm').swap
  right := by
    intro b a hab hm
    change (S.mode (a, b)).swap = .right at hm
    have hm' : S.mode (a, b) = .left := by
      have hs := congrArg AsyncMode.swap hm
      rw [AsyncMode.swap_swap] at hs
      simpa only [AsyncMode.swap] using hs
    exact (S.left a b hab hm').swap
  both := by
    intro b a hab hm
    change (S.mode (a, b)).swap = .both at hm
    have hm' : S.mode (a, b) = .both := by
      have hs := congrArg AsyncMode.swap hm
      rw [AsyncMode.swap_swap] at hs
      simpa only [AsyncMode.swap] using hs
    exact (S.both a b hab hm').swap

/-- Lift a locally justified asynchronous schedule to arbitrary coupled input weights. -/
theorem quad_couple_while_async {R : α → β → Prop} {g : α → Prop} {h : β → Prop}
    {c : Cmd α} {d : Cmd β} (S : AsyncSchedule R g h (sem c) (sem d)) :
    quad (couple R) (.while g c) (.while h d)
      (couple (fun a b => R a b ∧ ¬g a ∧ ¬h b)) := by
  apply quad_couple_of_pointwise
  intro a b hab
  exact coupled_loop_async S hab

/-- Exact-coupling pRHL inherits the mixed scheduler's progress and marginal theorem. -/
theorem prhl_while_async {R : α → β → Prop} {g : α → Prop} {h : β → Prop}
    {c : Cmd α} {d : Cmd β} (S : AsyncSchedule R g h (sem c) (sem d)) :
    prhl R (.while g c) (.while h d) (fun a b => R a b ∧ ¬g a ∧ ¬h b) := by
  rw [prhl_iff_quad]
  exact quad_couple_while_async S

end RelOL.Prob
