import RelationalOutcomeLogic.Prob.Coupling.Assertions
import RelationalOutcomeLogic.Prob.Logic.Judgment

/-!
# Finite additive outcome cases

`finiteCases P n` retains every one of the first `n` outcome pieces, including
pieces of mass zero. It is an iterated additive conjunction, not a disjunction.
The composition rule transports all branches through additive outcome semantics.
-/

namespace RelOL.Prob

open scoped ENNReal

variable {α β γ δ : Type*}

/-- A finite additive decomposition with individually specified pieces. -/
def finiteCases (P : ℕ → RAssn α β) : ℕ → RAssn α β
  | 0 => emp
  | n + 1 => oplus (finiteCases P n) (P n)

theorem finiteCases_intro (P : ℕ → RAssn α β) (n : ℕ)
    (μ : ℕ → Weight α) (ν : ℕ → Weight β)
    (h : ∀ i < n, P i (μ i) (ν i)) :
    finiteCases P n (∑ i ∈ Finset.range n, μ i) (∑ i ∈ Finset.range n, ν i) := by
  induction n with
  | zero => simp [finiteCases, emp]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact oplus_intro (ih (fun i hi => h i (by omega))) (h n (by omega))

theorem finiteCases_mono {P Q : ℕ → RAssn α β} (n : ℕ)
    (h : ∀ i < n, entail (P i) (Q i)) : entail (finiteCases P n) (finiteCases Q n) := by
  induction n with
  | zero => exact entail_refl _
  | succ n ih =>
    exact oplus_mono (ih (fun i hi => h i (by omega))) (h n (by omega))

/-- Finite additive cases sum their masses without losing the branch specifications. -/
theorem finiteCases_massEq {P : ℕ → RAssn α β} (n : ℕ) (a b : ℕ → ℝ≥0∞)
    (h : ∀ i < n, entail (P i) (massEq (a i) (b i))) :
    entail (finiteCases P n)
      (massEq (∑ i ∈ Finset.range n, a i) (∑ i ∈ Finset.range n, b i)) := by
  induction n with
  | zero =>
    simpa only [finiteCases, Finset.sum_range_zero, massEq_zero_zero] using
      entail_refl (emp : RAssn α β)
  | succ n ih =>
    intro μ ν hμν
    have hsplit := oplus_mono (ih (fun i hi => h i (by omega))) (h n (by omega)) μ ν hμν
    simpa only [Finset.sum_range_succ] using
      oplus_massEq (∑ i ∈ Finset.range n, a i) (∑ i ∈ Finset.range n, b i)
        (a n) (b n) μ ν hsplit

/-- Forgetting quantitative case annotations preserves the common coupling relation. -/
theorem finiteCases_couple {P : ℕ → RAssn α β} (n : ℕ) (R : α → β → Prop)
    (h : ∀ i < n, entail (P i) (couple R)) : entail (finiteCases P n) (couple R) := by
  induction n with
  | zero =>
    rintro μ ν ⟨rfl, rfl⟩
    exact Coupled.zero R
  | succ n ih =>
    intro μ ν hμν
    exact oplus_couple_same μ ν
      (oplus_mono (ih (fun i hi => h i (by omega))) (h n (by omega)) μ ν hμν)

/-- Composition through additive transformers is proved for every branch. The
zero laws are needed for the empty decomposition; branches may overlap in support. -/
theorem quadSem_finiteCases (F : Weight α → Weight γ) (G : Weight β → Weight δ)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0)
    (hF : ∀ μ ν, F (μ + ν) = F μ + F ν)
    (hG : ∀ μ ν, G (μ + ν) = G μ + G ν)
    (P : ℕ → RAssn α β) (Q : ℕ → RAssn γ δ) (n : ℕ)
    (h : ∀ i < n, quadSem F G (P i) (Q i)) :
    quadSem F G (finiteCases P n) (finiteCases Q n) := by
  induction n with
  | zero =>
    rintro μ ν ⟨rfl, rfl⟩
    exact ⟨hF0, hG0⟩
  | succ n ih =>
    rintro μ ν ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁, h₂⟩
    rw [hF, hG]
    exact oplus_intro (ih (fun i hi => h i (by omega)) _ _ h₁) (h n (by omega) _ _ h₂)

end RelOL.Prob
