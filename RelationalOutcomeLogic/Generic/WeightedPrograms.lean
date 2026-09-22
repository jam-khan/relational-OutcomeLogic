import RelationalOutcomeLogic.Algebra.WeightedOrder
import RelationalOutcomeLogic.Generic.Iteration

/-!
# Programs whose interpretation changes with the scalar model

The countdown proof is shared by reachability, trace counts, probability weights,
and tropical costs. Each guarded step multiplies its path weight by `r`; the
choice of scalar operations determines what that weight means.
-/

namespace RelOL.Generic.WeightedPrograms

open RelOL.Algebra

variable {K : Type*} [Semiring K] [CompleteLattice K]
variable [SummationSemiring.{0} K] [OmegaSummationSemiring.{0} K]

noncomputable section

/-- A weighted step consumes one unit of the natural-number counter. -/
def countdownStep (r : K) (n : ℕ) : Weighted.Weight K ℕ :=
  Weighted.scale r (Weighted.pure (n - 1))

/-- A loop program expressed using the common outcome semantics. -/
def countdown (r : K) (n : ℕ) : Weighted.Weight K ℕ :=
  Generic.loopSem (fun i : ℕ => 0 < i) (countdownStep r) n

/-- One loop proof works for every scalar instance, including noncommutative ones. -/
theorem countdown_sem (r : K) (n : ℕ) :
    countdown r n = Weighted.scale (r ^ n) (Weighted.pure 0) := by
  induction n with
  | zero =>
      rw [countdown, Generic.loopSem_neg (by decide)]
      change Weighted.pure 0 = Weighted.scale (r ^ 0) (Weighted.pure 0)
      funext i
      simp [Weighted.scale]
  | succ n ih =>
      rw [countdown, Generic.loopSem_pos (Nat.zero_lt_succ n)]
      change Weighted.bind (Weighted.scale r (Weighted.pure n))
        (countdown r) = Weighted.scale (r ^ (n + 1)) (Weighted.pure 0)
      rw [Weighted.scale_bind, Weighted.pure_bind, ih]
      funext i
      simp only [Weighted.scale_apply, pow_succ', mul_assoc]

/-- The loop's total outcome weight is the same scalar power. -/
theorem countdown_mass (r : K) (n : ℕ) : Weighted.mass (countdown r n) = r ^ n := by
  rw [countdown_sem, Weighted.mass_scale, Weighted.mass_pure, mul_one]

end

end RelOL.Generic.WeightedPrograms
