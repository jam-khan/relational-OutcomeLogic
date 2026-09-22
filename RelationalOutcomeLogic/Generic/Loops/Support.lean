import RelationalOutcomeLogic.Algebra.Weighted.Iteration
import RelationalOutcomeLogic.Generic.Loops.Semantics

/-!
# Weighted loop unfolding and support invariants

The shared loop construction specializes to scalar weights. Every supported
terminal outcome satisfies a preserved state invariant and the negated guard;
the argument needs neither positive summation nor a nontrivial scalar.
-/

universe u v

namespace RelOL.Algebra.Weighted

variable {κ : Type v} [Semiring κ] [CompleteLattice κ]
variable [SummationSemiring.{u} κ] [OmegaSummationSemiring.{u} κ]
variable {α β σ τ : Type u}

open Generic (loopIter loopSem)

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
@[simp] theorem loopIter_zero (g : α → Prop) (k : α → Weight κ α) (s : α) :
    loopIter g k 0 s = 0 := rfl

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
theorem loopIter_succ_pos {g : α → Prop} {s : α} (hg : g s)
    (k : α → Weight κ α) (n : ℕ) :
    loopIter g k (n + 1) s = Weighted.bind (k s) (loopIter g k n) :=
  Generic.loopIter_succ_pos hg k n

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
theorem loopIter_succ_neg {g : α → Prop} {s : α} (hg : ¬ g s)
    (k : α → Weight κ α) (n : ℕ) : loopIter g k (n + 1) s = Weighted.pure s :=
  Generic.loopIter_succ_neg hg k n

theorem loopSem_pos {g : α → Prop} {s : α} (hg : g s) (k : α → Weight κ α) :
    loopSem g k s = Weighted.bind (k s) (loopSem g k) := Generic.loopSem_pos hg k

theorem loopSem_neg {g : α → Prop} {s : α} (hg : ¬ g s) (k : α → Weight κ α) :
    loopSem g k s = Weighted.pure s := Generic.loopSem_neg hg k

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
/-- One-way support preservation requires neither positivity nor a nontrivial scalar. -/
theorem loopIter_support_invariant (g : α → Prop) (k : α → Weight κ α) (P : α → Prop)
    (hbody : ∀ s, P s → g s → ∀ t ∈ support (k s), P t)
    (n : ℕ) (s : α) (hs : P s) (t : α)
    (ht : t ∈ support (loopIter g k n s)) : P t ∧ ¬ g t := by
  classical
  induction n generalizing s with
  | zero => exact (ht rfl).elim
  | succ n ih =>
      by_cases hg : g s
      · rw [loopIter_succ_pos hg] at ht
        obtain ⟨a, ha, hta⟩ := exists_support_of_bind_ne_zero (k s)
          (loopIter g k n) t ht
        exact ih a (hbody s hs hg a ha) hta
      · rw [loopIter_succ_neg hg] at ht
        have hts : t = s := by
          by_contra hne
          exact ht (by simp [Weighted.pure, hne])
        exact hts ▸ ⟨hs, hg⟩

omit [OmegaSummationSemiring κ] in
/-- A limit cannot add a supported outcome when every finite approximant is zero there. -/
theorem loopSem_support_invariant (g : α → Prop) (k : α → Weight κ α) (P : α → Prop)
    (hbody : ∀ s, P s → g s → ∀ t ∈ support (k s), P t)
    (s : α) (hs : P s) (t : α) (ht : t ∈ support (loopSem g k s)) :
    P t ∧ ¬ g t := by
  by_contra hout
  have hz : ∀ n, loopIter g k n s t = 0 := by
    intro n
    by_contra hn
    exact hout (loopIter_support_invariant g k P hbody n s hs t hn)
  exact ht (by simp only [Generic.loopSem, iSup_apply, hz, iSup_const])

end RelOL.Algebra.Weighted
