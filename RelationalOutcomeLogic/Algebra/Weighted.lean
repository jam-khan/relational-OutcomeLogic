import RelationalOutcomeLogic.Algebra.Scalar
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# Outcome weights over a summation semiring

The monad, additive choice, and left scaling laws are derived from scalar laws.
Multiplication need not commute: a scalar preceding a computation remains on
the left, and a scalar following it remains on the right.
-/

universe u v

namespace RelOL.Algebra.Weighted

abbrev Weight (K : Type v) (α : Type u) := α → K

variable {K : Type v} [Semiring K] [SummationSemiring.{u} K]
variable {α β γ : Type u}

open SummationSemiring

noncomputable section

open Classical in
def pure (a : α) : Weight K α := fun b => if b = a then 1 else 0
def bind (μ : Weight K α) (k : α → Weight K β) : Weight K β :=
  fun b => sum (fun a => μ a * k a b)
def mass (μ : Weight K α) : K := sum μ
def support (μ : Weight K α) : Set α := {a | μ a ≠ 0}
def scale (r : K) (μ : Weight K α) : Weight K α := fun a => r * μ a
def rscale (μ : Weight K α) (r : K) : Weight K α := fun a => μ a * r

omit [SummationSemiring.{u} K] in
open Classical in
@[simp] theorem pure_apply (a b : α) : (pure a : Weight K α) b = if b = a then 1 else 0 := rfl
@[simp] theorem bind_apply (μ : Weight K α) (k : α → Weight K β) (b : β) :
    bind μ k b = sum (fun a => μ a * k a b) := rfl
omit [SummationSemiring.{u} K] in
@[simp] theorem scale_apply (r : K) (μ : Weight K α) (a : α) : scale r μ a = r * μ a := rfl
omit [SummationSemiring.{u} K] in
@[simp] theorem rscale_apply (μ : Weight K α) (r : K) (a : α) : rscale μ r a = μ a * r := rfl
omit [SummationSemiring.{u} K] in
@[simp] theorem mem_support_iff (μ : Weight K α) (a : α) : a ∈ support μ ↔ μ a ≠ 0 := Iff.rfl

@[simp] theorem pure_bind (a : α) (k : α → Weight K β) : bind (pure a) k = k a := by
  classical
  funext b
  change sum (fun x => (if x = a then 1 else 0) * k x b) = k a b
  calc
    _ = sum (fun x => if x = a then k a b else 0) := by
      apply sum_congr
      intro x
      by_cases hx : x = a <;> simp [hx]
    _ = _ := sum_single a (k a b)

@[simp] theorem bind_pure (μ : Weight K α) : bind μ pure = μ := by
  classical
  funext a
  change sum (fun x => μ x * (if a = x then 1 else 0)) = μ a
  calc
    _ = sum (fun x => if x = a then μ a else 0) := by
      apply sum_congr
      intro x
      by_cases hx : x = a
      · simp [hx]
      · simp [hx, Ne.symm hx]
    _ = _ := sum_single a (μ a)

theorem bind_assoc (μ : Weight K α) (k : α → Weight K β) (l : β → Weight K γ) :
    bind (bind μ k) l = bind μ (fun a => bind (k a) l) := by
  funext c
  simp only [bind, ← sum_mul, ← mul_sum, mul_assoc]
  exact sum_comm _

@[simp] theorem zero_bind (k : α → Weight K β) : bind 0 k = 0 := by
  funext b
  simp only [bind, Pi.zero_apply, zero_mul, sum_zero]

@[simp] theorem bind_zero (μ : Weight K α) : bind μ (fun _ => 0 : α → Weight K β) = 0 := by
  funext b
  simp only [bind, Pi.zero_apply, mul_zero, sum_zero]

theorem add_bind (μ ν : Weight K α) (k : α → Weight K β) :
    bind (μ + ν) k = bind μ k + bind ν k := by
  funext b
  simp only [bind, Pi.add_apply, add_mul, sum_add]

theorem bind_add (μ : Weight K α) (k l : α → Weight K β) :
    bind μ (fun a => k a + l a) = bind μ k + bind μ l := by
  funext b
  simp only [bind, Pi.add_apply, mul_add, sum_add]

theorem scale_bind (r : K) (μ : Weight K α) (k : α → Weight K β) :
    bind (scale r μ) k = scale r (bind μ k) := by
  funext b
  simp only [bind, scale, mul_assoc, mul_sum]

theorem bind_rscale (μ : Weight K α) (k : α → Weight K β) (r : K) :
    bind μ (fun a => rscale (k a) r) = rscale (bind μ k) r := by
  funext b
  simp only [bind, rscale, ← mul_assoc, sum_mul]

/-- Moving a left scalar through a continuation needs commutation explicitly. -/
theorem bind_scale_of_commute (μ : Weight K α) (k : α → Weight K β) (r : K)
    (hc : ∀ a, Commute (μ a) r) :
    bind μ (fun a => scale r (k a)) = scale r (bind μ k) := by
  funext b
  change sum (fun a => μ a * (r * k a b)) = r * sum (fun a => μ a * k a b)
  rw [← mul_sum]
  apply sum_congr
  intro a
  rw [← mul_assoc, (hc a).eq, mul_assoc]

theorem bind_congr_on_support (μ : Weight K α) {k l : α → Weight K β}
    (h : ∀ a ∈ support μ, k a = l a) : bind μ k = bind μ l := by
  funext b
  apply sum_congr
  intro a
  by_cases ha : μ a = 0
  · simp [ha]
  · rw [h a ha]

/-- The direction required by coupling composition holds without positivity. -/
theorem exists_support_of_bind_ne_zero (μ : Weight K α) (k : α → Weight K β) (b : β)
    (hb : bind μ k b ≠ 0) : ∃ a ∈ support μ, b ∈ support (k a) := by
  obtain ⟨a, ha⟩ := exists_ne_zero_of_sum_ne_zero hb
  exact ⟨a, left_ne_zero_of_mul ha, right_ne_zero_of_mul ha⟩

@[simp] theorem mass_zero : mass (0 : Weight K α) = 0 := sum_zero
@[simp] theorem mass_pure (a : α) : mass (pure a : Weight K α) = 1 := sum_single a 1
theorem mass_add (μ ν : Weight K α) : mass (μ + ν) = mass μ + mass ν := sum_add μ ν
theorem mass_scale (r : K) (μ : Weight K α) : mass (scale r μ) = r * mass μ := mul_sum r μ
theorem mass_rscale (μ : Weight K α) (r : K) : mass (rscale μ r) = mass μ * r := sum_mul μ r
theorem mass_bind (μ : Weight K α) (k : α → Weight K β) :
    mass (bind μ k) = sum (fun a => μ a * mass (k a)) := by
  simp only [mass, ← mul_sum]
  exact sum_comm _

section Positive

variable [PositiveSummation.{u} K]

@[simp] theorem mass_eq_zero_iff (μ : Weight K α) : mass μ = 0 ↔ μ = 0 := by
  simp only [mass, PositiveSummation.sum_eq_zero, funext_iff, Pi.zero_apply]

@[simp] theorem mem_support_bind_iff [NoZeroDivisors K]
    (μ : Weight K α) (k : α → Weight K β) (b : β) :
    b ∈ support (bind μ k) ↔ ∃ a ∈ support μ, b ∈ support (k a) := by
  classical
  change sum (fun a => μ a * k a b) ≠ 0 ↔ ∃ a, μ a ≠ 0 ∧ k a b ≠ 0
  simp [PositiveSummation.sum_eq_zero, not_or]

end Positive

end

end RelOL.Algebra.Weighted
