import Mathlib.Algebra.Ring.Basic

/-!
# Semirings with arbitrary nonnegative-style summation

A plain semiring does not provide infinite sums. `SummationSemiring` records the
extra summation laws needed for unrestricted discrete outcome weights. The laws
do not assume that multiplication commutes. Order and continuity for iteration
are separate requirements; this interface alone supplies sequencing and choice.
-/

universe u v

namespace RelOL.Algebra

open Classical in
/-- An explicitly chosen complete summation operation on a semiring. The index
universe is fixed, so all state spaces in one model inhabit `Type u`. -/
class SummationSemiring (K : Type v) [Semiring K] where
  sum : {ι : Type u} → (ι → K) → K
  sum_zero {ι : Type u} : sum (fun _ : ι => 0) = 0
  sum_add {ι : Type u} (f g : ι → K) :
    sum (fun i => f i + g i) = sum f + sum g
  sum_single {ι : Type u} (j : ι) (x : K) :
    sum (fun i => if i = j then x else 0) = x
  sum_comm {ι κ : Type u} (f : ι → κ → K) :
    sum (fun i => sum (f i)) = sum (fun j => sum (fun i => f i j))
  sum_prod {ι κ : Type u} (f : ι × κ → K) :
    sum f = sum (fun i => sum (fun j => f (i, j)))
  mul_sum {ι : Type u} (r : K) (f : ι → K) :
    sum (fun i => r * f i) = r * sum f
  sum_mul {ι : Type u} (f : ι → K) (r : K) :
    sum (fun i => f i * r) = sum f * r

/-- No cancellation in an infinite sum. Exact support descriptions use this
additional hypothesis, while the monad and coupling-composition laws do not. -/
class PositiveSummation (K : Type v) [Semiring K] [SummationSemiring.{u} K] : Prop where
  sum_eq_zero {ι : Type u} (f : ι → K) :
    SummationSemiring.sum f = 0 ↔ ∀ i, f i = 0

namespace SummationSemiring

variable {K : Type v} [Semiring K] [SummationSemiring.{u} K]
variable {ι κ : Type u}

theorem sum_congr {f g : ι → K} (h : ∀ i, f i = g i) : sum f = sum g :=
  congrArg sum (funext h)

theorem sum_eq_single {f : ι → K} (j : ι) (h : ∀ i, i ≠ j → f i = 0) :
    sum f = f j := by
  classical
  calc
    _ = sum (fun i => if i = j then f j else 0) := by
      apply sum_congr
      intro i
      by_cases hi : i = j
      · simp [hi]
      · simp [hi, h i hi]
    _ = _ := sum_single j (f j)

/-- A nonzero sum contains a nonzero summand, without a positivity assumption. -/
theorem exists_ne_zero_of_sum_ne_zero {f : ι → K} (h : sum f ≠ 0) :
    ∃ i, f i ≠ 0 := by
  classical
  by_contra hn
  have hz : ∀ i, f i = 0 := fun i => Classical.byContradiction fun hi => hn ⟨i, hi⟩
  exact h ((sum_congr hz).trans sum_zero)

end SummationSemiring

end RelOL.Algebra
