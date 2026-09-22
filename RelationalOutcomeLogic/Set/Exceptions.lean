import RelationalOutcomeLogic.Set.Semantics

/-! # Set-valued sequencing and loops with propagated exceptions -/

namespace RelOL

attribute [local instance] Classical.propDecidable

/-! ## The error-propagating Kleisli step -/

/-- Error-propagating continuation: errors propagate verbatim, `ok` states continue. -/
def errK {ε σ τ : Type*} (k : σ → Set (Except ε τ)) : Except ε σ → Set (Except ε τ)
  | .error e => {.error e}
  | .ok s => k s

@[simp] theorem errK_ok {ε σ τ : Type*} {k : σ → Set (Except ε τ)} {s : σ} :
    errK k (.ok s) = k s := rfl

@[simp] theorem errK_error {ε σ τ : Type*} {k : σ → Set (Except ε τ)} {e : ε} :
    errK k (.error e) = {Except.error e} := rfl

theorem errK_nonempty {ε σ τ : Type*} {k : σ → Set (Except ε τ)}
    (hk : ∀ s, (k s).Nonempty) (a : Except ε σ) : (errK k a).Nonempty := by
  cases a with
  | error e => exact ⟨.error e, rfl⟩
  | ok s => exact hk s

/-- The error-propagating bind is associative (fails if the two cases are swapped). -/
theorem errK_assoc {ε σ τ υ : Type*} (k₁ : σ → Set (Except ε τ))
    (k₂ : τ → Set (Except ε υ)) (m : Set (Except ε σ)) :
    kleisli (errK k₂) (kleisli (errK k₁) m)
      = kleisli (errK fun s => kleisli (errK k₂) (k₁ s)) m := by
  rw [kleisli_comp]
  congr 1
  funext x
  cases x with
  | error e => simp
  | ok s => rfl

theorem errK_mono {ε σ τ : Type*} {k₁ k₂ : σ → Set (Except ε τ)}
    (h : ∀ s, k₁ s ⊆ k₂ s) (a : Except ε σ) : errK k₁ a ⊆ errK k₂ a := by
  cases a with
  | error e => exact fun x hx => hx
  | ok s => exact h s

/-- `errK` commutes with inhabited indexed unions of continuations. -/
theorem errK_iUnion {ε σ τ : Type*} {ι : Sort*} [Nonempty ι]
    (k : ι → σ → Set (Except ε τ)) (a : Except ε σ) :
    errK (fun s => ⋃ i, k i s) a = ⋃ i, errK (k i) a := by
  cases a with
  | error e => simp [errK_error, Set.iUnion_const]
  | ok s => simp only [errK_ok]

/-! ## Error-propagating while-loops -/

/-- Fuel-indexed truncation of an error-propagating while-loop. -/
noncomputable def errLoopIter {ε σ : Type*} (b : σ → Prop)
    (step : σ → Set (Except ε σ)) : ℕ → σ → Set (Except ε σ)
  | 0, _ => ∅
  | n + 1, s =>
      if b s then kleisli (errK (errLoopIter b step n)) (step s) else {.ok s}

@[simp] theorem errLoopIter_zero {ε σ : Type*} (b : σ → Prop)
    (step : σ → Set (Except ε σ)) (s : σ) : errLoopIter b step 0 s = ∅ := rfl

theorem errLoopIter_succ_pos {ε σ : Type*} {b : σ → Prop} {s : σ} (h : b s)
    (step : σ → Set (Except ε σ)) (n : ℕ) :
    errLoopIter b step (n + 1) s
      = kleisli (errK (errLoopIter b step n)) (step s) := by
  simp only [errLoopIter, if_pos h]

theorem errLoopIter_succ_neg {ε σ : Type*} {b : σ → Prop} {s : σ} (h : ¬ b s)
    (step : σ → Set (Except ε σ)) (n : ℕ) :
    errLoopIter b step (n + 1) s = {.ok s} := by
  simp only [errLoopIter, if_neg h]

/-- Semantics of an error-propagating `while`. -/
noncomputable def errLoopSem {ε σ : Type*} (b : σ → Prop)
    (step : σ → Set (Except ε σ)) (s : σ) : Set (Except ε σ) :=
  ⋃ n, errLoopIter b step n s

theorem errLoopIter_subset_errLoopSem {ε σ : Type*} (b : σ → Prop)
    (step : σ → Set (Except ε σ)) (n : ℕ) (s : σ) :
    errLoopIter b step n s ⊆ errLoopSem b step s :=
  Set.subset_iUnion (fun n => errLoopIter b step n s) n

/-- The fixpoint unrolling equation for error-propagating loops. -/
theorem errLoopSem_unfold {ε σ : Type*} (b : σ → Prop)
    (step : σ → Set (Except ε σ)) (s : σ) :
    errLoopSem b step s
      = if b s then kleisli (errK (errLoopSem b step)) (step s) else {.ok s} := by
  by_cases h : b s
  · rw [if_pos h]
    unfold errLoopSem
    have : (errK fun t => ⋃ n, errLoopIter b step n t)
        = fun a => ⋃ n, errK (errLoopIter b step n) a := by
      funext a; exact errK_iUnion _ a
    rw [this, kleisli_iUnion_fun]
    ext t
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, ht⟩
      cases n with
      | zero => simp at ht
      | succ n => rw [errLoopIter_succ_pos h] at ht; exact ⟨n, ht⟩
    · rintro ⟨n, ht⟩
      exact ⟨n + 1, by rw [errLoopIter_succ_pos h]; exact ht⟩
  · rw [if_neg h]
    unfold errLoopSem
    ext t
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, ht⟩
      cases n with
      | zero => simp at ht
      | succ n => rwa [errLoopIter_succ_neg h] at ht
    · exact fun ht => ⟨1, by rwa [errLoopIter_succ_neg h]⟩

theorem errLoopSem_pos {ε σ : Type*} {b : σ → Prop} {s : σ} (h : b s)
    (step : σ → Set (Except ε σ)) :
    errLoopSem b step s = kleisli (errK (errLoopSem b step)) (step s) := by
  rw [errLoopSem_unfold, if_pos h]

theorem errLoopSem_neg {ε σ : Type*} {b : σ → Prop} {s : σ} (h : ¬ b s)
    (step : σ → Set (Except ε σ)) :
    errLoopSem b step s = {.ok s} := by
  rw [errLoopSem_unfold, if_neg h]

end RelOL
