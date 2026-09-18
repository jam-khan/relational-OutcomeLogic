import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Extended nonnegative outcome weights

`Weight α` is the ambient space of arbitrary extended nonnegative weights. Addition,
scalar multiplication, and order are pointwise. Probability and subprobability bounds
are predicates: unrestricted addition is available without claiming that it preserves
the bound on total mass.

This file supplies the concrete algebra for discrete weighted semantics. It does not
add probabilistic commands, coupling assertions, or a generic outcome-model interface.
-/

open scoped ENNReal

namespace RelOL

/-- Outcome weights, allowing arbitrary total mass, including infinity. -/
abbrev Weight (α : Type*) := α → ℝ≥0∞

namespace Weight

variable {α β γ : Type*}

noncomputable section

open scoped Classical in
/-- The weight concentrated at one outcome, with mass one. -/
def pure (a : α) : Weight α := fun b => if b = a then 1 else 0

/-- Discrete weighted sequencing. -/
def bind (μ : Weight α) (k : α → Weight β) : Weight β :=
  fun b => ∑' a, μ a * k a b

/-- Outcomes with nonzero weight. -/
def support (μ : Weight α) : Set α := {a | μ a ≠ 0}

/-- Total weight, which may be infinite. -/
def mass (μ : Weight α) : ℝ≥0∞ := ∑' a, μ a

/-- The total mass is at most one. -/
def IsSubprob (μ : Weight α) : Prop := mass μ ≤ 1

/-- The total mass is exactly one. -/
def IsProbability (μ : Weight α) : Prop := mass μ = 1

open scoped Classical in
@[simp] theorem pure_apply (a b : α) : pure a b = if b = a then 1 else 0 := rfl

@[simp] theorem bind_apply (μ : Weight α) (k : α → Weight β) (b : β) :
    bind μ k b = ∑' a, μ a * k a b := rfl

@[simp] theorem mem_support_iff (μ : Weight α) (a : α) :
    a ∈ support μ ↔ μ a ≠ 0 := Iff.rfl

@[simp] theorem pure_bind (a : α) (k : α → Weight β) : bind (pure a) k = k a := by
  classical
  funext b
  simp [bind, pure]

@[simp] theorem bind_pure (μ : Weight α) : bind μ pure = μ := by
  classical
  funext a
  simp [bind, pure, mul_ite]

theorem bind_assoc (μ : Weight α) (k : α → Weight β) (l : β → Weight γ) :
    bind (bind μ k) l = bind μ (fun a => bind (k a) l) := by
  funext c
  simp only [bind, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, mul_assoc]
  exact ENNReal.tsum_comm

@[simp] theorem zero_bind (k : α → Weight β) : bind 0 k = 0 := by
  funext b
  simp [bind]

@[simp] theorem bind_zero (μ : Weight α) : bind μ (fun _ => 0 : α → Weight β) = 0 := by
  funext b
  simp [bind]

theorem add_bind (μ ν : Weight α) (k : α → Weight β) :
    bind (μ + ν) k = bind μ k + bind ν k := by
  funext b
  simp only [bind, Pi.add_apply, add_mul, ENNReal.tsum_add]

theorem bind_add (μ : Weight α) (k l : α → Weight β) :
    bind μ (fun a => k a + l a) = bind μ k + bind μ l := by
  funext b
  simp only [bind, Pi.add_apply, mul_add, ENNReal.tsum_add]

theorem smul_bind (r : ℝ≥0∞) (μ : Weight α) (k : α → Weight β) :
    bind (r • μ) k = r • bind μ k := by
  funext b
  simp only [bind, Pi.smul_apply, smul_eq_mul, mul_assoc, ENNReal.tsum_mul_left]

theorem bind_smul (r : ℝ≥0∞) (μ : Weight α) (k : α → Weight β) :
    bind μ (fun a => r • k a) = r • bind μ k := by
  funext b
  change (∑' a, μ a * (r * k a b)) = r * ∑' a, μ a * k a b
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun a => mul_left_comm _ _ _

/-- Changing a continuation outside the input's support does not change sequencing. -/
theorem bind_congr_on_support (μ : Weight α) {k l : α → Weight β}
    (h : ∀ a ∈ support μ, k a = l a) : bind μ k = bind μ l := by
  funext b
  apply tsum_congr
  intro a
  by_cases ha : μ a = 0
  · simp [ha]
  · rw [h a ha]

@[simp] theorem support_zero : support (0 : Weight α) = ∅ := by
  ext a
  simp [support]

@[simp] theorem support_pure (a : α) : support (pure a) = {a} := by
  classical
  ext b
  simp [support, pure]

@[simp] theorem support_add (μ ν : Weight α) :
    support (μ + ν) = support μ ∪ support ν := by
  ext a
  simp only [support, Set.mem_setOf_eq, Pi.add_apply, ne_eq, add_eq_zero,
    not_and_or, Set.mem_union]

@[simp] theorem mem_support_smul_iff (r : ℝ≥0∞) (μ : Weight α) (a : α) :
    a ∈ support (r • μ) ↔ r ≠ 0 ∧ a ∈ support μ := by
  simp [support, not_or]

theorem support_smul_of_ne_zero {r : ℝ≥0∞} (hr : r ≠ 0) (μ : Weight α) :
    support (r • μ) = support μ := by
  ext a
  simp [hr]

@[simp] theorem mem_support_bind_iff (μ : Weight α) (k : α → Weight β) (b : β) :
    b ∈ support (bind μ k) ↔ ∃ a ∈ support μ, b ∈ support (k a) := by
  simp [support, bind, ENNReal.tsum_eq_zero, not_or]

theorem support_bind (μ : Weight α) (k : α → Weight β) :
    support (bind μ k) = ⋃ a ∈ support μ, support (k a) := by
  ext b
  simp only [mem_support_bind_iff, Set.mem_iUnion, exists_prop]

@[simp] theorem mass_zero : mass (0 : Weight α) = 0 := by simp [mass]

@[simp] theorem mass_pure (a : α) : mass (pure a) = 1 := by
  classical
  simp [mass, pure]

theorem mass_add (μ ν : Weight α) : mass (μ + ν) = mass μ + mass ν :=
  ENNReal.tsum_add

theorem mass_smul (r : ℝ≥0∞) (μ : Weight α) : mass (r • μ) = r * mass μ :=
  ENNReal.tsum_mul_left

theorem mass_bind (μ : Weight α) (k : α → Weight β) :
    mass (bind μ k) = ∑' a, μ a * mass (k a) := by
  simp only [mass, bind, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

@[simp] theorem mass_eq_zero_iff (μ : Weight α) : mass μ = 0 ↔ μ = 0 := by
  simp only [mass, ENNReal.tsum_eq_zero, funext_iff, Pi.zero_apply]

theorem mass_mono {μ ν : Weight α} (h : μ ≤ ν) : mass μ ≤ mass ν :=
  ENNReal.tsum_le_tsum h

theorem bind_mono {μ ν : Weight α} {k l : α → Weight β}
    (hμ : μ ≤ ν) (hk : k ≤ l) : bind μ k ≤ bind ν l := by
  intro b
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul' (hμ a) (hk a b)

theorem bind_mono_left {μ ν : Weight α} (h : μ ≤ ν) (k : α → Weight β) :
    bind μ k ≤ bind ν k := bind_mono h le_rfl

theorem bind_mono_right (μ : Weight α) {k l : α → Weight β} (h : k ≤ l) :
    bind μ k ≤ bind μ l := bind_mono le_rfl h

@[simp] theorem isSubprob_zero : IsSubprob (0 : Weight α) := by simp [IsSubprob]

@[simp] theorem isSubprob_pure (a : α) : IsSubprob (pure a) := by simp [IsSubprob]

@[simp] theorem isProbability_pure (a : α) : IsProbability (pure a) := mass_pure a

theorem IsProbability.isSubprob {μ : Weight α} (h : IsProbability μ) : IsSubprob μ :=
  le_of_eq h

/-- Sequencing by subprobability continuations cannot increase total mass. -/
theorem mass_bind_le_mass (μ : Weight α) (k : α → Weight β)
    (hk : ∀ a ∈ support μ, IsSubprob (k a)) : mass (bind μ k) ≤ mass μ := by
  rw [mass_bind]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : μ a = 0
  · simp [ha]
  · simpa using mul_le_mul_right (hk a ha) (μ a)

theorem IsSubprob.bind_of_support {μ : Weight α} {k : α → Weight β}
    (hμ : IsSubprob μ) (hk : ∀ a ∈ support μ, IsSubprob (k a)) :
    IsSubprob (bind μ k) :=
  (mass_bind_le_mass μ k hk).trans hμ

theorem IsSubprob.bind {μ : Weight α} {k : α → Weight β}
    (hμ : IsSubprob μ) (hk : ∀ a, IsSubprob (k a)) : IsSubprob (bind μ k) :=
  hμ.bind_of_support fun a _ => hk a

theorem mass_bind_of_isProbability (μ : Weight α) (k : α → Weight β)
    (hk : ∀ a ∈ support μ, IsProbability (k a)) : mass (bind μ k) = mass μ := by
  rw [mass_bind]
  apply tsum_congr
  intro a
  by_cases ha : μ a = 0
  · simp [ha]
  · rw [hk a ha, mul_one]

theorem IsProbability.bind {μ : Weight α} {k : α → Weight β}
    (hμ : IsProbability μ) (hk : ∀ a, IsProbability (k a)) : IsProbability (bind μ k) :=
  (mass_bind_of_isProbability μ k fun a _ => hk a).trans hμ

end

end Weight
end RelOL
