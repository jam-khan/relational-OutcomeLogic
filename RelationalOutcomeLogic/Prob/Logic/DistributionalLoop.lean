import RelationalOutcomeLogic.Generic.Distributional
import RelationalOutcomeLogic.Bridges.Probability

/-!
# Reconstruction invariants for full probabilistic loops

The reconstruction kernel retains the joint law of hidden random state. A local
commuting square and support-wise agreement of guards lift to the increasing
limit of loop approximants. This rule does not assume termination, bounded
runtimes, or a probability bound. It synchronizes semantic body steps: internal
scheduler events must first be justified as one body, for example with the
ranked asynchronous rule. It is not an unrestricted asynchronous rule.
-/

namespace RelOL.Prob

universe u
variable {α β : Type u}
noncomputable section

theorem bind_loopIter_reconstruction
    (B : α → Weight β) (g : α → Prop) (h : β → Prop)
    (k : α → Weight α) (l : β → Weight β)
    (hguard : ∀ a b, b ∈ Weight.support (B a) → (g a ↔ h b))
    (hstep : ∀ a, g a → Weight.bind (B a) l = Weight.bind (k a) B)
    (n : Nat) (a : α) :
    Weight.bind (B a) (loopIter h l n) = Weight.bind (loopIter g k n a) B := by
  classical
  induction n generalizing a with
  | zero => simp only [loopIter, Weight.bind_zero, Weight.zero_bind]
  | succ n ih =>
    by_cases ha : g a
    · rw [loopIter_succ_pos ha]
      calc
        Weight.bind (B a) (loopIter h l (n + 1)) =
            Weight.bind (B a) (fun b => Weight.bind (l b) (loopIter h l n)) :=
          Weight.bind_congr_on_support _ fun b hb =>
            loopIter_succ_pos ((hguard a b hb).mp ha) l n
        _ = Weight.bind (Weight.bind (B a) l) (loopIter h l n) :=
          (Weight.bind_assoc _ _ _).symm
        _ = Weight.bind (Weight.bind (k a) B) (loopIter h l n) := by rw [hstep a ha]
        _ = Weight.bind (k a) (fun a' => Weight.bind (loopIter g k n a') B) := by
          rw [Weight.bind_assoc]
          congr 1
          funext a'
          exact ih a'
        _ = Weight.bind (Weight.bind (k a) (loopIter g k n)) B :=
          (Weight.bind_assoc _ _ _).symm
    · rw [loopIter_succ_neg ha, Weight.pure_bind]
      calc
        Weight.bind (B a) (loopIter h l (n + 1)) = Weight.bind (B a) Weight.pure :=
          Weight.bind_congr_on_support _ fun b hb =>
            loopIter_succ_neg (fun hb' => ha ((hguard a b hb).mpr hb')) l n
        _ = B a := Weight.bind_pure _

/-- The finite local obligations determine the full, possibly divergent loop. -/
theorem bind_loopSem_reconstruction
    (B : α → Weight β) (g : α → Prop) (h : β → Prop)
    (k : α → Weight α) (l : β → Weight β)
    (hguard : ∀ a b, b ∈ Weight.support (B a) → (g a ↔ h b))
    (hstep : ∀ a, g a → Weight.bind (B a) l = Weight.bind (k a) B)
    (a : α) :
    Weight.bind (B a) (loopSem h l) = Weight.bind (loopSem g k a) B := by
  rw [loopSem_eq_iSup, Weight.bind_iSup_right _ _ (loopIter_monotone h l)]
  rw [loopSem, Weight.bind_iSup_left _ (fun i j hij => loopIter_monotone g k hij a)]
  exact congrArg iSup (funext fun n => bind_loopIter_reconstruction B g h k l hguard hstep n a)

/-- A rule on arbitrary related input outcomes, consuming a local body judgment. -/
theorem quad_lifted_while
    (B : α → Weight β) (g : α → Prop) (h : β → Prop)
    (k : α → Weight α) (l : β → Weight β)
    (hguard : ∀ a b, b ∈ Weight.support (B a) → (g a ↔ h b))
    (hbody : Generic.quad (Generic.lifted B) k l (Generic.lifted B)) :
    Generic.quad (Generic.lifted B) (loopSem g k) (loopSem h l)
      (Generic.lifted B) := by
  apply Generic.quad_lifted
  exact bind_loopSem_reconstruction B g h k l hguard
    (fun a _ => Generic.quad_lifted_iff.mp hbody a)

end
end RelOL.Prob
