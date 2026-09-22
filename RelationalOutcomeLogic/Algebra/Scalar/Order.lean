import RelationalOutcomeLogic.Algebra.Scalar.Basic
import Mathlib.Order.FixedPoints

/-!
# Order and increasing limits for scalar weights

Infinite sequencing uses `SummationSemiring`; least-fixed-point loops additionally
need monotonicity and continuity along increasing sequences. These assumptions are
separate from idempotence, commutative multiplication, and exact support laws.
In particular, addition is not required to preserve arbitrary suprema.
-/

universe u v

namespace RelOL.Algebra

/-- The ordered laws used to construct increasing-limit weighted loop semantics. -/
class OmegaSummationSemiring (K : Type v) [Semiring K] [CompleteLattice K]
    [SummationSemiring.{u} K] : Prop where
  zero_eq_bot : (0 : K) = ⊥
  add_mono {a b c d : K} : a ≤ b → c ≤ d → a + c ≤ b + d
  mul_mono {a b c d : K} : a ≤ b → c ≤ d → a * c ≤ b * d
  sum_mono {ι : Type u} {f g : ι → K} :
    (∀ i, f i ≤ g i) → SummationSemiring.sum f ≤ SummationSemiring.sum g
  sum_iSup {ι : Type u} (f : ℕ → ι → K) (hf : Monotone f) :
    SummationSemiring.sum (fun i => ⨆ n, f n i) =
      ⨆ n, SummationSemiring.sum (f n)
  mul_iSup_left (a : K) (f : ℕ → K) (hf : Monotone f) :
    a * (⨆ n, f n) = ⨆ n, a * f n
  mul_iSup_right (f : ℕ → K) (hf : Monotone f) (a : K) :
    (⨆ n, f n) * a = ⨆ n, f n * a

end RelOL.Algebra
