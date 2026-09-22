import RelationalOutcomeLogic.Algebra.IterationModel

/-!
# One least-fixed-point construction for outcome models

All results below are proved once for an ordered outcome model. The concrete Set
and semiring-weighted instances reuse the same approximants, unfolding law, and
least-fixed-point proof.
-/

universe u v

namespace RelOL.Generic

variable {M : Type u → Type v} [OutcomeModel M]
variable {α : Type u}

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Truncate after a bounded number of loop unfoldings. -/
def loopIter (g : α → Prop) (k : α → M α) : ℕ → α → M α
  | 0, _ => OutcomeModel.empty
  | n + 1, s => if g s then OutcomeModel.bind (k s) (loopIter g k n)
      else OutcomeModel.pure s

@[simp] theorem loopIter_zero (g : α → Prop) (k : α → M α) (s : α) :
    loopIter g k 0 s = OutcomeModel.empty := rfl

@[simp] theorem loopIter_succ_pos {g : α → Prop} {s : α} (hg : g s)
    (k : α → M α) (n : ℕ) :
    loopIter g k (n + 1) s = OutcomeModel.bind (k s) (loopIter g k n) := by
  simp only [loopIter, if_pos hg]

@[simp] theorem loopIter_succ_neg {g : α → Prop} {s : α} (hg : ¬ g s)
    (k : α → M α) (n : ℕ) : loopIter g k (n + 1) s = OutcomeModel.pure s := by
  simp only [loopIter, if_neg hg]

variable [∀ α, CompleteLattice (M α)] [IterationModel M]

theorem loopIter_mono_succ (g : α → Prop) (k : α → M α) (n : ℕ) :
    loopIter g k n ≤ loopIter g k (n + 1) := by
  induction n with
  | zero =>
      intro s
      rw [loopIter_zero, IterationModel.empty_eq_bot]
      exact bot_le
  | succ n ih =>
      intro s
      by_cases hg : g s
      · rw [loopIter_succ_pos hg, loopIter_succ_pos hg]
        exact IterationModel.bind_mono le_rfl ih
      · rw [loopIter_succ_neg hg, loopIter_succ_neg hg]

theorem loopIter_monotone (g : α → Prop) (k : α → M α) :
    Monotone (loopIter g k) := monotone_nat_of_le_succ (loopIter_mono_succ g k)

/-- All terminating outcomes are the increasing limit of finite approximations. -/
def loopSem (g : α → Prop) (k : α → M α) (s : α) : M α :=
  ⨆ n, loopIter g k n s

omit [IterationModel M] in
theorem loopIter_le_loopSem (g : α → Prop) (k : α → M α) (n : ℕ) (s : α) :
    loopIter g k n s ≤ loopSem g k s := le_iSup (fun m => loopIter g k m s) n

omit [IterationModel M] in
theorem loopSem_eq_iSup (g : α → Prop) (k : α → M α) :
    loopSem g k = ⨆ n, loopIter g k n := by
  funext s
  simp only [loopSem, iSup_apply]

theorem loopSem_eq_iSup_succ (g : α → Prop) (k : α → M α) (s : α) :
    loopSem g k s = ⨆ n, loopIter g k (n + 1) s := by
  apply le_antisymm
  · exact iSup_le fun n => le_iSup_of_le n (loopIter_mono_succ g k n s)
  · exact iSup_le fun n => loopIter_le_loopSem g k (n + 1) s

theorem loopSem_unfold (g : α → Prop) (k : α → M α) (s : α) :
    loopSem g k s = if g s then OutcomeModel.bind (k s) (loopSem g k)
      else OutcomeModel.pure s := by
  rw [loopSem_eq_iSup_succ]
  by_cases hg : g s
  · simp only [loopIter_succ_pos hg, if_pos hg]
    rw [loopSem_eq_iSup, IterationModel.bind_iSup_right _ _ (loopIter_monotone g k)]
  · simp only [loopIter_succ_neg hg, if_neg hg, iSup_const]

@[simp] theorem loopSem_pos {g : α → Prop} {s : α} (hg : g s) (k : α → M α) :
    loopSem g k s = OutcomeModel.bind (k s) (loopSem g k) := by
  rw [loopSem_unfold, if_pos hg]

@[simp] theorem loopSem_neg {g : α → Prop} {s : α} (hg : ¬ g s) (k : α → M α) :
    loopSem g k s = OutcomeModel.pure s := by
  rw [loopSem_unfold, if_neg hg]

def loopHom (g : α → Prop) (k : α → M α) : (α → M α) →o (α → M α) where
  toFun f s := if g s then OutcomeModel.bind (k s) f else OutcomeModel.pure s
  monotone' f f' h s := by
    by_cases hg : g s
    · simpa only [if_pos hg] using IterationModel.bind_mono (x := k s) le_rfl h
    · simp only [if_neg hg, le_refl]

theorem loopHom_apply (g : α → Prop) (k : α → M α) (f : α → M α) (s : α) :
    loopHom g k f s = if g s then OutcomeModel.bind (k s) f else OutcomeModel.pure s := rfl

theorem loopSem_le (g : α → Prop) (k : α → M α) (f : α → M α)
    (hf : loopHom g k f ≤ f) : loopSem g k ≤ f := by
  intro s
  apply iSup_le
  intro n
  induction n generalizing s with
  | zero =>
      rw [loopIter_zero, IterationModel.empty_eq_bot]
      exact bot_le
  | succ n ih =>
      change loopHom g k (loopIter g k n) s ≤ f s
      exact ((loopHom g k).monotone ih s).trans (hf s)

/-- The generic increasing-limit semantics is exactly the least fixed point. -/
theorem loopSem_eq_lfp (g : α → Prop) (k : α → M α) :
    loopSem g k = OrderHom.lfp (loopHom g k) := by
  apply le_antisymm
  · exact loopSem_le g k _ (le_of_eq (OrderHom.map_lfp _))
  · apply OrderHom.lfp_le
    intro s
    rw [loopHom_apply, ← loopSem_unfold g k s]

omit [∀ α, CompleteLattice (M α)] [IterationModel M] in
@[simp] theorem loopIter_true (k : α → M α) (n : ℕ) :
    loopIter (fun _ => True) k n = fun _ => OutcomeModel.empty := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext s
      rw [loopIter_succ_pos trivial, ih]
      exact OutcomeModel.bind_empty _

omit [IterationModel M] in
/-- Divergence is the empty outcome in every instance. -/
@[simp] theorem loopSem_true (k : α → M α) :
    loopSem (fun _ => True) k = fun _ => OutcomeModel.empty := by
  funext s
  simp only [loopSem, loopIter_true, iSup_const]

end

end RelOL.Generic
