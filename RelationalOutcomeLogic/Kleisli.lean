import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints

namespace RelOL

-- `Type*` enables an implicit universe level
variable {α β γ : Type*}

/-
  Kleisli extension of `k : α → Set β` over the powerset monad.

  It means run `k` from every state in `m`, and
  collect all outcomes

  `k` is some non-deterministic program,
  state of type `α` to a set of outcomes of type `β`.

  `k†` : Set α → Set β
-/
def kleisli (k : α → Set β) (m : Set α) : Set β :=
  ⋃ x ∈ m, k x

/-
  It means that `y : β` is a possible outcome, given
  a program `k : α → Set β` and the set of input
  states `m : Set α`.
-/
@[simp] theorem mem_kleisli
  {k : α → Set β} {m : Set α} {y : β} :
    y ∈ kleisli k m ↔ ∃ x ∈ m, y ∈ k x := by
  unfold kleisli
  constructor
  repeat simp_all

-- k† ∅ = ∅
@[simp] theorem kleisli_empty
  (k : α → Set β) :
    kleisli k (∅ : Set α) = ∅ := by
  unfold kleisli
  simp

-- k† {x} = k x
@[simp] theorem kleisli_singleton
  (k : α → Set β) (x : α) :
    kleisli k {x} = k x := by
  unfold kleisli
  simp

/-
  The bind (·) compatibility law
  of the powerset execution model.

  `k† (m₁ ∪ m₂) = k† m₁ ∪ k† m₂`
-/
@[simp] theorem kleisli_union
  (k : α → Set β) (m₁ m₂ : Set α) :
    kleisli k (m₁ ∪ m₂) = kleisli k m₁ ∪ kleisli k m₂ := by
  unfold kleisli
  exact Set.biUnion_union m₁ m₂ k

/-
  Pointwise union for k†
  `(λx. k₁ x ∪ k₂ x)† m = k₁ m ∪ k₂ m`
-/
@[simp] theorem kleisli_pointwise_union
  (k₁ k₂ : α → Set β) (m : Set α) :
    kleisli (fun x => k₁ x ∪ k₂ x) m = kleisli k₁ m ∪ kleisli k₂ m := by
  ext y; simp; grind

/-
  Kleisli composition (associativity of bind).

  `k₂† (k₁† m) = (λ x. k₂ (k₁ x))† m`
-/
theorem kleisli_comp (k₁ : α → Set β) (k₂ : β → Set γ) (m : Set α) :
    kleisli k₂ (kleisli k₁ m) = kleisli (fun x => kleisli k₂ (k₁ x)) m := by
  ext z
  unfold kleisli
  simp

theorem kleisli_nonempty {k : α → Set β} {m : Set α} (hm : m.Nonempty)
    (h : ∀ x ∈ m, (k x).Nonempty) : (kleisli k m).Nonempty := by
  cases hm
  rename_i w h1
  unfold kleisli
  simp
  grind

-- Monotonicity and continuity, required by loops

theorem kleisli_mono {k : α → Set β} {m₁ m₂ : Set α} (h : m₁ ⊆ m₂) :
    kleisli k m₁ ⊆ kleisli k m₂ := by
  unfold kleisli
  exact Set.biUnion_mono h fun x a ⦃a_1⦄ a_2 ↦ a_2

theorem kleisli_mono_fun {k₁ k₂ : α → Set β} (h : ∀ x, k₁ x ⊆ k₂ x) (m : Set α) :
    kleisli k₁ m ⊆ kleisli k₂ m := by
  unfold kleisli
  exact Set.iUnion₂_mono fun i j ↦ h i

theorem kleisli_congr {k₁ k₂ : α → Set β} {m : Set α} (h : ∀ x ∈ m, k₁ x = k₂ x) :
    kleisli k₁ m = kleisli k₂ m := by
  ext y
  simp
  grind

theorem kleisli_iUnion {ℓ : Sort*} (k : α → Set β) (m : ℓ → Set α) :
    kleisli k (⋃ i, m i) = ⋃ i, kleisli k (m i) := by
  ext y
  simp
  grind

/- Continuity of `kleisli` in the continuation
  an indexed union of continuations can be made
  rewritten over the `kleisli`

  (λ x. `⋃ i`, k i x)† m = `⋃ i`, (k i)† m
-/
theorem kleisli_iUnion_fun {ℓ : Sort*} (k : ℓ → α → Set β) (m : Set α) :
    kleisli (fun x => ⋃ i, k i x) m = ⋃ i, kleisli (k i) m := by
  unfold kleisli
  ext y
  simp
  grind

-- Kleene iteration for while-loops

section Loops

attribute [local instance] Classical.propDecidable

/-- Fuel-indexed truncation of a while-loop body `step` under guard `b`. -/
noncomputable def loopIter (b : α → Prop) (step : α → Set α) : ℕ → α → Set α
  | 0, _      => ∅
  | n + 1, s  =>
    if b s
      then kleisli (loopIter b step n) (step s)
      else {s}

@[simp] theorem loopIter_zero
  (b : α → Prop) (step : α → Set α) (s : α) :
    loopIter b step 0 s = ∅ := by
  rfl

@[simp]
theorem loopIter_succ_pos
  {b : α → Prop} {s : α} (h : b s) (step : α → Set α) (n : ℕ) :
    loopIter b step (n + 1) s = kleisli (loopIter b step n) (step s) := by
  simp only [loopIter, if_pos h]

-- Given the guard is `false`,
-- loop iteration returns the `s`
@[simp] theorem loopIter_succ_neg
  {b : α → Prop} {s : α} (h : ¬ b s) (step : α → Set α) (n : ℕ) :
    loopIter b step (n + 1) s = {s} := by
  unfold loopIter
  simp; intro h'; grind


@[simp] theorem loopIter_mono_succ
  (b : α → Prop) (step : α → Set α) (n : ℕ) (s : α) :
    loopIter b step n s ⊆ loopIter b step (n + 1) s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    -- cases on the guard `b`
    by_cases h : b s
    · rw [loopIter_succ_pos h, loopIter_succ_pos h]
      exact kleisli_mono_fun ih (step s)
    · rw [loopIter_succ_neg h, loopIter_succ_neg h]

theorem loopIter_mono (b : α → Prop) (step : α → Set α) {n₁ n₂ : ℕ} (h : n₁ ≤ n₂)
    (s : α) : loopIter b step n₁ s ⊆ loopIter b step n₂ s := by
  induction h with
  | refl =>
      grind
  | step m' ih =>
      rename_i m''
      exact fun t ht => loopIter_mono_succ b step _ s (ih ht)

/-- Semantics of `while b do step`: union of all fuel-indexed truncations. -/
noncomputable def loopSem (b : α → Prop) (step : α → Set α) (s : α) : Set α :=
  ⋃ n, loopIter b step n s

@[simp] theorem loopIter_subset_loopSem
  (b : α → Prop) (step : α → Set α) (n : ℕ) (s : α) :
    loopIter b step n s ⊆ loopSem b step s :=
  Set.subset_iUnion (fun n => loopIter b step n s) n

/-- The fixpoint unrolling equation for loops. -/
theorem loopSem_unfold
  (b : α → Prop) (step : α → Set α) (s : α) :
    loopSem b step s
    = if b s
        then kleisli (loopSem b step) (step s)
        else {s} := by
  by_cases h : b s
  · rw [if_pos h]
    unfold loopSem
    rw [kleisli_iUnion_fun (fun n => loopIter b step n) (step s)]
    ext t
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, ht⟩
      cases n with
      | zero => simp at ht
      | succ n => rw [loopIter_succ_pos h] at ht; exact ⟨n, ht⟩
    · rintro ⟨n, ht⟩
      exact ⟨n + 1, by rw [loopIter_succ_pos h]; exact ht⟩
  · rw [if_neg h]
    unfold loopSem
    ext t
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, ht⟩
      cases n with
      | zero => simp at ht
      | succ n => rwa [loopIter_succ_neg h] at ht
    · exact fun ht => ⟨1, by rwa [loopIter_succ_neg h]⟩

/-- The characteristic functional of `while b do step`, as a monotone map. -/
noncomputable def loopHom (b : α → Prop) (step : α → Set α) :
    (α → Set α) →o (α → Set α) where
  toFun f s := if b s then kleisli f (step s) else {s}
  monotone' f g hfg s := by
    by_cases h : b s
    · simpa only [if_pos h] using kleisli_mono_fun (fun t => hfg t) (step s)
    · simp [if_neg h]

theorem loopHom_apply (b : α → Prop) (step : α → Set α) (f : α → Set α) (s : α) :
    loopHom b step f s = if b s then kleisli f (step s) else {s} := rfl

/-- Kleene: the union of iterates is the least fixed point of the loop
functional (the paper's Knaster–Tarski reading of `while`). -/
theorem loopSem_eq_lfp (b : α → Prop) (step : α → Set α) :
    loopSem b step = OrderHom.lfp (loopHom b step) := by
  have hlfp : ∀ s, loopHom b step (OrderHom.lfp (loopHom b step)) s
      = OrderHom.lfp (loopHom b step) s := fun s => by rw [OrderHom.map_lfp]
  apply le_antisymm
  · intro s
    unfold loopSem
    refine Set.iUnion_subset fun n => ?_
    induction n generalizing s with
    | zero => simp
    | succ n ih =>
      by_cases h : b s
      · rw [loopIter_succ_pos h, ← hlfp, loopHom_apply, if_pos h]
        exact kleisli_mono_fun (fun t => ih t) _
      · rw [loopIter_succ_neg h, ← hlfp, loopHom_apply, if_neg h]
  · apply OrderHom.lfp_le
    intro s
    rw [loopHom_apply, ← loopSem_unfold b step s]

end Loops

end RelOL
