import RelationalOutcomeLogic.Algebra.WeightOrder

/-!
# Least-fixed-point weighted loops

A finite approximation records only executions that exit within its fuel. The full
semantics is the increasing supremum of these approximations, so divergence loses
mass. Continuity of weighted bind is used only for this increasing chain.
-/

namespace RelOL.Prob

variable {α : Type*}

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Finite-fuel approximation of a weighted loop. -/
def loopIter (g : α → Prop) (k : α → Weight α) : ℕ → α → Weight α
  | 0, _ => 0
  | n + 1, s => if g s then Weight.bind (k s) (loopIter g k n) else Weight.pure s

@[simp] theorem loopIter_zero (g : α → Prop) (k : α → Weight α) (s : α) :
    loopIter g k 0 s = 0 := rfl

@[simp] theorem loopIter_succ_pos {g : α → Prop} {s : α} (hg : g s)
    (k : α → Weight α) (n : ℕ) :
    loopIter g k (n + 1) s = Weight.bind (k s) (loopIter g k n) := by
  simp only [loopIter, if_pos hg]

@[simp] theorem loopIter_succ_neg {g : α → Prop} {s : α} (hg : ¬g s)
    (k : α → Weight α) (n : ℕ) : loopIter g k (n + 1) s = Weight.pure s := by
  simp only [loopIter, if_neg hg]

theorem loopIter_mono_succ (g : α → Prop) (k : α → Weight α) (n : ℕ) :
    loopIter g k n ≤ loopIter g k (n + 1) := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    intro s
    by_cases hg : g s
    · rw [loopIter_succ_pos hg, loopIter_succ_pos hg]
      exact Weight.bind_mono_right (k s) ih
    · rw [loopIter_succ_neg hg, loopIter_succ_neg hg]

theorem loopIter_monotone (g : α → Prop) (k : α → Weight α) :
    Monotone (loopIter g k) := monotone_nat_of_le_succ (loopIter_mono_succ g k)

/-- The terminating-outcome semantics, as an increasing limit of finite approximations. -/
def loopSem (g : α → Prop) (k : α → Weight α) (s : α) : Weight α :=
  ⨆ n, loopIter g k n s

theorem loopIter_le_loopSem (g : α → Prop) (k : α → Weight α) (n : ℕ) (s : α) :
    loopIter g k n s ≤ loopSem g k s := le_iSup (fun m => loopIter g k m s) n

theorem loopSem_eq_iSup (g : α → Prop) (k : α → Weight α) :
    loopSem g k = ⨆ n, loopIter g k n := by
  funext s
  simp only [loopSem, iSup_apply]

theorem loopSem_eq_iSup_succ (g : α → Prop) (k : α → Weight α) (s : α) :
    loopSem g k s = ⨆ n, loopIter g k (n + 1) s := by
  apply le_antisymm
  · exact iSup_le fun n => le_iSup_of_le n (loopIter_mono_succ g k n s)
  · exact iSup_le fun n => loopIter_le_loopSem g k (n + 1) s

theorem loopSem_unfold (g : α → Prop) (k : α → Weight α) (s : α) :
    loopSem g k s = if g s then Weight.bind (k s) (loopSem g k) else Weight.pure s := by
  rw [loopSem_eq_iSup_succ]
  by_cases hg : g s
  · simp only [loopIter_succ_pos hg, if_pos hg]
    rw [loopSem_eq_iSup, Weight.bind_iSup_right _ _ (loopIter_monotone g k)]
  · simp only [loopIter_succ_neg hg, if_neg hg, iSup_const]

@[simp] theorem loopSem_pos {g : α → Prop} {s : α} (hg : g s) (k : α → Weight α) :
    loopSem g k s = Weight.bind (k s) (loopSem g k) := by
  rw [loopSem_unfold, if_pos hg]

@[simp] theorem loopSem_neg {g : α → Prop} {s : α} (hg : ¬g s) (k : α → Weight α) :
    loopSem g k s = Weight.pure s := by
  rw [loopSem_unfold, if_neg hg]

/-- The monotone characteristic functional of the loop. -/
def loopHom (g : α → Prop) (k : α → Weight α) :
    (α → Weight α) →o (α → Weight α) where
  toFun f s := if g s then Weight.bind (k s) f else Weight.pure s
  monotone' f f' h s := by
    by_cases hg : g s
    · simpa only [if_pos hg] using Weight.bind_mono_right (k s) h
    · simp only [if_neg hg, le_refl]

theorem loopHom_apply (g : α → Prop) (k : α → Weight α) (f : α → Weight α) (s : α) :
    loopHom g k f s = if g s then Weight.bind (k s) f else Weight.pure s := rfl

/-- Every pre-fixed point of the characteristic functional bounds the loop semantics. -/
theorem loopSem_le (g : α → Prop) (k : α → Weight α) (f : α → Weight α)
    (hf : loopHom g k f ≤ f) : loopSem g k ≤ f := by
  intro s
  apply iSup_le
  intro n
  induction n generalizing s with
  | zero => exact bot_le
  | succ n ih =>
    change loopHom g k (loopIter g k n) s ≤ f s
    exact ((loopHom g k).monotone ih s).trans (hf s)

/-- The increasing limit of approximations is the least fixed point. -/
theorem loopSem_eq_lfp (g : α → Prop) (k : α → Weight α) :
    loopSem g k = OrderHom.lfp (loopHom g k) := by
  apply le_antisymm
  · apply loopSem_le
    exact le_of_eq (OrderHom.map_lfp _)
  · apply OrderHom.lfp_le
    intro s
    rw [loopHom_apply, ← loopSem_unfold g k s]

theorem loopIter_isSubprob (g : α → Prop) (k : α → Weight α)
    (hk : ∀ s, Weight.IsSubprob (k s)) (n : ℕ) (s : α) :
    Weight.IsSubprob (loopIter g k n s) := by
  induction n generalizing s with
  | zero => exact Weight.isSubprob_zero
  | succ n ih =>
    by_cases hg : g s
    · rw [loopIter_succ_pos hg]
      exact (hk s).bind ih
    · rw [loopIter_succ_neg hg]
      exact Weight.isSubprob_pure s

theorem loopSem_isSubprob (g : α → Prop) (k : α → Weight α)
    (hk : ∀ s, Weight.IsSubprob (k s)) (s : α) : Weight.IsSubprob (loopSem g k s) :=
  Weight.IsSubprob.iSup (fun _ _ h => loopIter_monotone g k h s)
    (fun n => loopIter_isSubprob g k hk n s)

@[simp] theorem loopIter_true (k : α → Weight α) (n : ℕ) :
    loopIter (fun _ => True) k n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext s
    rw [loopIter_succ_pos trivial, ih]
    exact Weight.bind_zero _

/-- A loop whose guard never becomes false has no terminating mass. -/
@[simp] theorem loopSem_true (k : α → Weight α) : loopSem (fun _ => True) k = 0 := by
  funext s
  simp only [loopSem, loopIter_true, Pi.zero_apply, iSup_const]

/-- Finite approximations assign no mass to outputs at which the guard still holds. -/
theorem loopIter_apply_eq_zero_of_guard (g : α → Prop) (k : α → Weight α)
    (n : ℕ) (s : α) {t : α} (ht : g t) : loopIter g k n s t = 0 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases hs : g s
    · rw [loopIter_succ_pos hs]
      apply ENNReal.tsum_eq_zero.mpr
      intro a
      rw [ih a, mul_zero]
    · rw [loopIter_succ_neg hs]
      have hts : t ≠ s := fun h => hs (h ▸ ht)
      simp only [Weight.pure_apply, if_neg hts]

/-- Every output with nonzero terminating weight satisfies the exit condition. -/
theorem loopSem_apply_eq_zero_of_guard (g : α → Prop) (k : α → Weight α)
    (s : α) {t : α} (ht : g t) : loopSem g k s t = 0 := by
  simp only [loopSem, iSup_apply, loopIter_apply_eq_zero_of_guard g k _ _ ht, iSup_const]

end

end RelOL.Prob
