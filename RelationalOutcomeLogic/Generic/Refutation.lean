import RelationalOutcomeLogic.Algebra.Weighted.Events
import RelationalOutcomeLogic.Generic.Coupling

/-!
# Quantitative refutation over ordered summation semirings

The weights of finite events provide necessary bounds for an exact coupling.
A strict deficit refutes the coupling, and a concrete input lifts the certificate
to a refutation of the common relational judgment. The argument uses the chosen
semiring order, so for tropical costs its inequalities reverse numerical cost.
No normalization, subtraction, division, or commutative multiplication is needed.
-/

universe u v

namespace RelOL.Generic

open Algebra Algebra.Weighted

variable {K : Type v} [Semiring K] [CompleteLattice K]
variable [SummationSemiring.{u} K] [OmegaSummationSemiring.{u} K]
variable {α β γ δ : Type u}

/-- An imbalance of finite event weights ruling out every exact joint witness. -/
structure MassDeficitCert (R : α → β → Prop) (μ : Weighted.Weight K α)
    (ν : Weighted.Weight K β) where
  left : Finset α
  right : Finset β
  cover : ∀ a ∈ left, ∀ b, R a b → b ∈ right
  deficit : eventMass ν right < eventMass μ left

theorem MassDeficitCert.refutes {R : α → β → Prop}
    {μ : Weighted.Weight K α} {ν : Weighted.Weight K β}
    (C : MassDeficitCert R μ ν) : ¬ Weighted.Coupled R μ ν := by
  intro h
  exact (not_lt_of_ge (h.eventMass_le C.left C.right C.cover)) C.deficit

theorem no_massDeficitCert_of_coupled {R : α → β → Prop}
    {μ : Weighted.Weight K α} {ν : Weighted.Weight K β}
    (h : Weighted.Coupled R μ ν) : ¬ Nonempty (MassDeficitCert R μ ν) := by
  rintro ⟨C⟩
  exact C.refutes h

def MassDeficitCert.of_bounds {R : α → β → Prop}
    {μ : Weighted.Weight K α} {ν : Weighted.Weight K β}
    (A : Finset α) (B : Finset β) (hcover : ∀ a ∈ A, ∀ b, R a b → b ∈ B)
    {lower upper : K} (hleft : lower ≤ eventMass μ A)
    (hright : eventMass ν B ≤ upper) (hgap : upper < lower) : MassDeficitCert R μ ν where
  left := A
  right := B
  cover := hcover
  deficit := hright.trans_lt (hgap.trans_le hleft)

/-- A mismatch at one observation suffices to refute exact equality coupling. -/
def MassDeficitCert.singletonEq {μ ν : Weighted.Weight K α} (a : α) (h : ν a < μ a) :
    MassDeficitCert Eq μ ν where
  left := {a}
  right := {a}
  cover := by
    intro x hx y hxy
    simpa only [Finset.mem_singleton, ← hxy] using hx
  deficit := by simpa only [eventMass_singleton] using h

theorem MassDeficitCert.refutes_post {R : α → β → Prop}
    {μ : Weighted.Weight K α} {ν : Weighted.Weight K β}
    (C : MassDeficitCert R μ ν) {Q : RAssn (Weighted.Weight K) α β}
    (hQ : entail Q (couple R)) : ¬ Q μ ν := fun h => C.refutes (hQ μ ν h)

/-- A deficit for the union relation rules out every additive split into its pieces. -/
theorem MassDeficitCert.refutes_oplus {R S : α → β → Prop}
    {μ : Weighted.Weight K α} {ν : Weighted.Weight K β}
    (C : MassDeficitCert (fun a b => R a b ∨ S a b) μ ν) :
    ¬ oplus (couple R) (couple S) μ ν := by
  rintro ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁, h₂⟩
  exact C.refutes (Weighted.Coupled.add
    (Weighted.Coupled.mono h₁ fun _ _ h => Or.inl h)
    (Weighted.Coupled.mono h₂ fun _ _ h => Or.inr h))

/-- An imbalance in actual outputs at a concrete pair of initial states. -/
structure BugCert (F : Weighted.Weight K α → Weighted.Weight K γ)
    (G : Weighted.Weight K β → Weighted.Weight K δ) (R : γ → δ → Prop) where
  s₀ : α
  s₀' : β
  deficit : MassDeficitCert R (F (Weighted.pure s₀)) (G (Weighted.pure s₀'))

theorem BugCert.refutes {F : Weighted.Weight K α → Weighted.Weight K γ}
    {G : Weighted.Weight K β → Weighted.Weight K δ} {R : γ → δ → Prop}
    (C : BugCert F G R) {P : RAssn (Weighted.Weight K) α β}
    (hP : P (Weighted.pure C.s₀) (Weighted.pure C.s₀')) :
    ¬ quadSem F G P (couple R) := by
  intro h
  exact C.deficit.refutes (h _ _ hP)

theorem BugCert.refutes_of_entails {F : Weighted.Weight K α → Weighted.Weight K γ}
    {G : Weighted.Weight K β → Weighted.Weight K δ} {R : γ → δ → Prop}
    (C : BugCert F G R) {P : RAssn (Weighted.Weight K) α β}
    {Q : RAssn (Weighted.Weight K) γ δ}
    (hP : P (Weighted.pure C.s₀) (Weighted.pure C.s₀')) (hQ : entail Q (couple R)) :
    ¬ quadSem F G P Q := by
  intro h
  exact C.deficit.refutes_post hQ (h _ _ hP)

end RelOL.Generic
