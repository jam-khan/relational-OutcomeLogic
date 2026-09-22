import RelationalOutcomeLogic.Algebra.WeightedModel
import RelationalOutcomeLogic.Algebra.OrderedScalar
import RelationalOutcomeLogic.Algebra.IterationModel

/-!
# Ordered weighted outcome models

Scalar monotonicity and increasing-limit laws lift to the weighted monad. This
constructs the iteration-model instance, so the shared loop proof applies to every
admissible scalar instance without being reproved for each kind of computation.
-/

universe u v

namespace RelOL.Algebra.Weighted

variable {K : Type v} [Semiring K] [CompleteLattice K]
variable [SummationSemiring.{u} K] [OmegaSummationSemiring.{u} K]
variable {α β : Type u}

theorem bind_mono {μ ν : Weight K α} {k l : α → Weight K β}
    (hμ : μ ≤ ν) (hk : k ≤ l) : bind μ k ≤ bind ν l := by
  intro b
  exact OmegaSummationSemiring.sum_mono fun a =>
    OmegaSummationSemiring.mul_mono (hμ a) (hk a b)

theorem mass_mono {μ ν : Weight K α} (h : μ ≤ ν) : mass μ ≤ mass ν :=
  OmegaSummationSemiring.sum_mono h

theorem mass_iSup (μ : ℕ → Weight K α) (hμ : Monotone μ) :
    mass (⨆ n, μ n) = ⨆ n, mass (μ n) := by
  simpa only [mass, ← iSup_apply] using OmegaSummationSemiring.sum_iSup μ hμ

theorem bind_iSup_left (μ : ℕ → Weight K α) (hμ : Monotone μ) (k : α → Weight K β) :
    bind (⨆ n, μ n) k = ⨆ n, bind (μ n) k := by
  funext b
  simp only [bind, iSup_apply]
  calc
    _ = SummationSemiring.sum (fun a => ⨆ n, μ n a * k a b) :=
      SummationSemiring.sum_congr fun a =>
        OmegaSummationSemiring.mul_iSup_right _ (fun _ _ h => hμ h a) _
    _ = _ := OmegaSummationSemiring.sum_iSup _
      (fun _ _ h a => OmegaSummationSemiring.mul_mono (hμ h a) le_rfl)

theorem bind_iSup_right (μ : Weight K α) (k : ℕ → α → Weight K β) (hk : Monotone k) :
    bind μ (⨆ n, k n) = ⨆ n, bind μ (k n) := by
  funext b
  simp only [bind, iSup_apply]
  calc
    _ = SummationSemiring.sum (fun a => ⨆ n, μ a * k n a b) :=
      SummationSemiring.sum_congr fun a =>
        OmegaSummationSemiring.mul_iSup_left _ _ (fun _ _ h => hk h a b)
    _ = _ := OmegaSummationSemiring.sum_iSup _
      (fun _ _ h a => OmegaSummationSemiring.mul_mono le_rfl (hk h a b))

/-- Every admissible scalar supplies the common least-fixed-point loop interface. -/
instance (priority := 100) weightedIterationModel :
    IterationModel (Weight K : Type u → Type _) where
  empty_eq_bot := by
    intro α
    funext a
    exact OmegaSummationSemiring.zero_eq_bot
  bind_mono := bind_mono
  bind_iSup_right := bind_iSup_right

end RelOL.Algebra.Weighted
