import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints

/-!
# The powerset Kleisli engine

`kleisli k` is the Kleisli extension of `k : α → Set β` over the powerset monad.
This file is the single place where the execution-model structure of the
prototype lives: `kleisli_union` and `kleisli_empty` are exactly the two
PCM-compatibility laws of an Outcome-Logic execution model (Zilberstein et al.,
OOPSLA 2023, Def. 3.3) specialized to the powerset instance ⟨Set Σ, ∪, ∅⟩:

* `bind (m₁ ⋄ m₂) k = bind m₁ k ⋄ bind m₂ k`  ↝  `kleisli_union`
* `bind ∅ k = ∅`                              ↝  `kleisli_empty`

Every language semantics in this development defines its lift as `kleisli`
applied to a step function, and thereby inherits these laws for free.
-/

namespace RelOL

variable {α β γ : Type*}

/-- Kleisli extension of `k : α → Set β` over the powerset monad. -/
def kleisli (k : α → Set β) (m : Set α) : Set β := ⋃ x ∈ m, k x

@[simp] theorem mem_kleisli {k : α → Set β} {m : Set α} {y : β} :
    y ∈ kleisli k m ↔ ∃ x ∈ m, y ∈ k x := by
  simp [kleisli]

@[simp] theorem kleisli_empty (k : α → Set β) : kleisli k (∅ : Set α) = ∅ := by
  simp [kleisli]

@[simp] theorem kleisli_singleton (k : α → Set β) (x : α) : kleisli k {x} = k x := by
  simp [kleisli]

/-- The bind/⋄ compatibility law of the powerset execution model. -/
theorem kleisli_union (k : α → Set β) (m₁ m₂ : Set α) :
    kleisli k (m₁ ∪ m₂) = kleisli k m₁ ∪ kleisli k m₂ := by
  ext y; simp [mem_kleisli, or_and_right, exists_or]

/-- Kleisli extension distributes over pointwise union of continuations. -/
theorem kleisli_pointwise_union (k₁ k₂ : α → Set β) (m : Set α) :
    kleisli (fun x => k₁ x ∪ k₂ x) m = kleisli k₁ m ∪ kleisli k₂ m := by
  ext y
  simp only [mem_kleisli, Set.mem_union]
  constructor
  · rintro ⟨x, hx, hy | hy⟩
    · exact Or.inl ⟨x, hx, hy⟩
    · exact Or.inr ⟨x, hx, hy⟩
  · rintro (⟨x, hx, hy⟩ | ⟨x, hx, hy⟩)
    · exact ⟨x, hx, Or.inl hy⟩
    · exact ⟨x, hx, Or.inr hy⟩

/-- Kleisli composition (associativity of bind). -/
theorem kleisli_comp (k₁ : α → Set β) (k₂ : β → Set γ) (m : Set α) :
    kleisli k₂ (kleisli k₁ m) = kleisli (fun x => kleisli k₂ (k₁ x)) m := by
  ext z
  simp only [mem_kleisli]
  constructor
  · rintro ⟨y, ⟨x, hx, hy⟩, hz⟩
    exact ⟨x, hx, y, hy, hz⟩
  · rintro ⟨x, hx, y, hy, hz⟩
    exact ⟨y, ⟨x, hx, hy⟩, hz⟩

theorem kleisli_nonempty {k : α → Set β} {m : Set α} (hm : m.Nonempty)
    (h : ∀ x ∈ m, (k x).Nonempty) : (kleisli k m).Nonempty := by
  obtain ⟨x, hx⟩ := hm
  obtain ⟨y, hy⟩ := h x hx
  exact ⟨y, mem_kleisli.mpr ⟨x, hx, hy⟩⟩

/-! ## Monotonicity and continuity

Needed once loops enter: the characteristic functional of a `while` is built
from `kleisli`, and its monotonicity/continuity is what makes the Kleene
iterates converge to the least fixed point. -/

theorem kleisli_mono {k : α → Set β} {m₁ m₂ : Set α} (h : m₁ ⊆ m₂) :
    kleisli k m₁ ⊆ kleisli k m₂ := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_kleisli.mp hy
  exact mem_kleisli.mpr ⟨x, h hx, hxy⟩

theorem kleisli_mono_fun {k₁ k₂ : α → Set β} (h : ∀ x, k₁ x ⊆ k₂ x) (m : Set α) :
    kleisli k₁ m ⊆ kleisli k₂ m := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_kleisli.mp hy
  exact mem_kleisli.mpr ⟨x, hx, h x hxy⟩

theorem kleisli_congr {k₁ k₂ : α → Set β} {m : Set α} (h : ∀ x ∈ m, k₁ x = k₂ x) :
    kleisli k₁ m = kleisli k₂ m := by
  ext y
  simp only [mem_kleisli]
  exact ⟨fun ⟨x, hx, hy⟩ => ⟨x, hx, h x hx ▸ hy⟩, fun ⟨x, hx, hy⟩ => ⟨x, hx, (h x hx).symm ▸ hy⟩⟩

theorem kleisli_iUnion {ι : Sort*} (k : α → Set β) (m : ι → Set α) :
    kleisli k (⋃ i, m i) = ⋃ i, kleisli k (m i) := by
  ext y
  simp only [mem_kleisli, Set.mem_iUnion]
  constructor
  · rintro ⟨x, ⟨i, hx⟩, hy⟩
    exact ⟨i, x, hx, hy⟩
  · rintro ⟨i, x, hx, hy⟩
    exact ⟨x, ⟨i, hx⟩, hy⟩

/-- Continuity of `kleisli` in the continuation: an indexed union of
continuations can be pulled out. -/
theorem kleisli_iUnion_fun {ι : Sort*} (k : ι → α → Set β) (m : Set α) :
    kleisli (fun x => ⋃ i, k i x) m = ⋃ i, kleisli (k i) m := by
  ext y
  simp only [mem_kleisli, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx, i, hy⟩
    exact ⟨i, x, hx, hy⟩
  · rintro ⟨i, x, hx, hy⟩
    exact ⟨x, hx, i, hy⟩

/-! ## Kleene iterates for while-loops

`loopIter b step n` is the `n`-fuel truncation of `while b do step`: `∅` when
the fuel runs out mid-loop (the run is still going, so it contributes no
outcomes), `{s}` on guard failure. `loopSem` is the union over all fuels —
by `loopSem_eq_lfp` this is exactly the least fixed point of the loop's
characteristic functional, so divergence is modeled by the empty outcome set. -/

section Loops

attribute [local instance] Classical.propDecidable

/-- Fuel-indexed truncation of a while-loop body `step` under guard `b`. -/
noncomputable def loopIter (b : α → Prop) (step : α → Set α) : ℕ → α → Set α
  | 0, _ => ∅
  | n + 1, s => if b s then kleisli (loopIter b step n) (step s) else {s}

@[simp] theorem loopIter_zero (b : α → Prop) (step : α → Set α) (s : α) :
    loopIter b step 0 s = ∅ := rfl

theorem loopIter_succ_pos {b : α → Prop} {s : α} (h : b s) (step : α → Set α) (n : ℕ) :
    loopIter b step (n + 1) s = kleisli (loopIter b step n) (step s) := by
  simp only [loopIter, if_pos h]

theorem loopIter_succ_neg {b : α → Prop} {s : α} (h : ¬ b s) (step : α → Set α) (n : ℕ) :
    loopIter b step (n + 1) s = {s} := by
  simp only [loopIter, if_neg h]

theorem loopIter_mono_succ (b : α → Prop) (step : α → Set α) (n : ℕ) (s : α) :
    loopIter b step n s ⊆ loopIter b step (n + 1) s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    by_cases h : b s
    · rw [loopIter_succ_pos h, loopIter_succ_pos h]
      exact kleisli_mono_fun (fun t => ih t) _
    · rw [loopIter_succ_neg h, loopIter_succ_neg h]

theorem loopIter_mono (b : α → Prop) (step : α → Set α) {n₁ n₂ : ℕ} (h : n₁ ≤ n₂)
    (s : α) : loopIter b step n₁ s ⊆ loopIter b step n₂ s := by
  induction h with
  | refl => exact fun _ h => h
  | step _ ih => exact fun t ht => loopIter_mono_succ b step _ s (ih ht)

/-- Semantics of `while b do step`: union of all fuel-indexed truncations. -/
noncomputable def loopSem (b : α → Prop) (step : α → Set α) (s : α) : Set α :=
  ⋃ n, loopIter b step n s

theorem loopIter_subset_loopSem (b : α → Prop) (step : α → Set α) (n : ℕ) (s : α) :
    loopIter b step n s ⊆ loopSem b step s :=
  Set.subset_iUnion (fun n => loopIter b step n s) n

/-- The fixpoint unrolling equation for loops. -/
theorem loopSem_unfold (b : α → Prop) (step : α → Set α) (s : α) :
    loopSem b step s
      = if b s then kleisli (loopSem b step) (step s) else {s} := by
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
