import RelationalOutcomeLogic.Prob.Refutation.EventMass
import RelationalOutcomeLogic.Prob.Coupling.Assertions
import RelationalOutcomeLogic.Prob.Logic.Judgment

/-!
# Quantitative refutation certificates

If every permitted partner of a finite left event lies in a finite right event,
an exact coupling must put at least as much mass in the right event. A strict
deficit therefore rules out every joint witness, including when both supports match.

Only the events are required to be finite. Weights may have arbitrary or infinite
total mass. The certificate uses a strict inequality, not subtraction or division.
This is a sound refutation method; completeness and certificate discovery are not
claimed. In particular, an underapproximation on the right cannot replace the upper
bound required by `of_bounds`.
-/

namespace RelOL.Prob

open scoped ENNReal

variable {α β γ δ : Type*}

/-- A finite pair of events whose mass imbalance prevents an exact `R`-coupling. -/
structure MassDeficitCert (R : α → β → Prop) (μ : Weight α) (ν : Weight β) where
  left : Finset α
  right : Finset β
  cover : ∀ a ∈ left, ∀ b, R a b → b ∈ right
  deficit : Weight.eventMass ν right < Weight.eventMass μ left

/-- Soundness: the deficit contradicts the bound obeyed by every exact coupling. -/
theorem MassDeficitCert.refutes {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (C : MassDeficitCert R μ ν) : ¬ Coupled R μ ν := by
  intro h
  exact (not_lt_of_ge (h.eventMass_le C.left C.right C.cover)) C.deficit

/-- Any existing exact coupling rules out a sound deficit certificate. -/
theorem Coupled.no_massDeficitCert {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (h : Coupled R μ ν) : ¬ Nonempty (MassDeficitCert R μ ν) := by
  rintro ⟨C⟩
  exact C.refutes h

/-- Exact evaluation is unnecessary when certified lower/upper bounds already separate. -/
def MassDeficitCert.of_bounds {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (A : Finset α) (B : Finset β)
    (hcover : ∀ a ∈ A, ∀ b, R a b → b ∈ B)
    {lower upper : ℝ≥0∞}
    (hleft : lower ≤ Weight.eventMass μ A)
    (hright : Weight.eventMass ν B ≤ upper) (hgap : upper < lower) :
    MassDeficitCert R μ ν where
  left := A
  right := B
  cover := hcover
  deficit := hright.trans_lt (hgap.trans_le hleft)

/-- A deficient relation also refutes every stronger postcondition. -/
theorem MassDeficitCert.refutes_post {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (C : MassDeficitCert R μ ν) {Q : RAssn α β} (hQ : entail Q (couple R)) :
    ¬ Q μ ν := fun h => C.refutes (hQ μ ν h)

/-- A deficit for the union relation rules out any additive split between its relations. -/
theorem MassDeficitCert.refutes_oplus {R S : α → β → Prop}
    {μ : Weight α} {ν : Weight β}
    (C : MassDeficitCert (fun a b => R a b ∨ S a b) μ ν) :
    ¬ oplus (couple R) (couple S) μ ν :=
  C.refutes_post oplus_couple

/-- A concrete pair of initial states and a certified deficit in their actual outputs. -/
structure BugCert (F : Weight α → Weight γ) (G : Weight β → Weight δ)
    (R : γ → δ → Prop) where
  s₀ : α
  s₀' : β
  deficit : MassDeficitCert R (F (Weight.pure s₀)) (G (Weight.pure s₀'))

/-- The input must satisfy the specification's precondition before its deficit refutes it. -/
theorem BugCert.refutes {F : Weight α → Weight γ} {G : Weight β → Weight δ}
    {R : γ → δ → Prop} (C : BugCert F G R) {P : RAssn α β}
    (hP : P (Weight.pure C.s₀) (Weight.pure C.s₀')) :
    ¬ quadSem F G P (couple R) := by
  intro h
  exact C.deficit.refutes (h _ _ hP)

/-- The same concrete counterexample refutes any postcondition implying the coupling. -/
theorem BugCert.refutes_of_entails {F : Weight α → Weight γ} {G : Weight β → Weight δ}
    {R : γ → δ → Prop} (C : BugCert F G R) {P : RAssn α β} {Q : RAssn γ δ}
    (hP : P (Weight.pure C.s₀) (Weight.pure C.s₀')) (hQ : entail Q (couple R)) :
    ¬ quadSem F G P Q := by
  intro h
  exact C.deficit.refutes_post hQ (h _ _ hP)

end RelOL.Prob
