import Mathlib.Logic.Function.Basic
import RelationalOutcomeLogic.Basic
import RelationalOutcomeLogic.Kleisli

/-!
# The homogeneous language and its powerset semantics

A minimal nondeterministic imperative language (no loops — iteration is
deliberately out of scope for the prototype) with denotational semantics into
`Set State`, per the Outcome Logic powerset instance.

Guards are propositional (`State → Prop`) and `sem` is classical/`noncomputable`:
example proofs close by simp *rewriting* (`sem_ite_pos` with an `omega`-provable
guard), never by kernel computation, so decidability buys nothing here.
-/

namespace RelOL

/-- Commands of the homogeneous language. -/
inductive Cmd where
  | skip
  | assign (x : String) (e : State → Int)
  | seq (c₁ c₂ : Cmd)
  | ite (b : State → Prop) (c₁ c₂ : Cmd)
  | choice (c₁ c₂ : Cmd)

open Classical in
/-- Denotational semantics: the set of possible final states. -/
noncomputable def sem : Cmd → State → Set State
  | .skip, s => {s}
  | .assign x e, s => {Function.update s x (e s)}
  | .seq c₁ c₂, s => kleisli (sem c₂) (sem c₁ s)
  | .ite b c₁ c₂, s => if b s then sem c₁ s else sem c₂ s
  | .choice c₁ c₂, s => sem c₁ s ∪ sem c₂ s

/-- Lift of the semantics to sets of initial states (Kleisli extension). -/
noncomputable def semLift (c : Cmd) : Set State → Set State := kleisli (sem c)

/-! ## Computation kit -/

@[simp] theorem sem_skip (s : State) : sem .skip s = {s} := rfl

@[simp] theorem sem_assign (x : String) (e : State → Int) (s : State) :
    sem (.assign x e) s = {Function.update s x (e s)} := rfl

theorem sem_seq (c₁ c₂ : Cmd) (s : State) :
    sem (.seq c₁ c₂) s = kleisli (sem c₂) (sem c₁ s) := rfl

@[simp] theorem sem_choice (c₁ c₂ : Cmd) (s : State) :
    sem (.choice c₁ c₂) s = sem c₁ s ∪ sem c₂ s := rfl

theorem sem_ite_pos {b : State → Prop} {s : State} (h : b s) (c₁ c₂ : Cmd) :
    sem (.ite b c₁ c₂) s = sem c₁ s := by
  simp only [sem, if_pos h]

theorem sem_ite_neg {b : State → Prop} {s : State} (h : ¬ b s) (c₁ c₂ : Cmd) :
    sem (.ite b c₁ c₂) s = sem c₂ s := by
  simp only [sem, if_neg h]

/-- This loop-free fragment never diverges: every command has at least one outcome
from every state. -/
theorem sem_nonempty (c : Cmd) (s : State) : (sem c s).Nonempty := by
  induction c generalizing s with
  | skip => exact ⟨s, rfl⟩
  | assign x e => exact ⟨_, rfl⟩
  | seq c₁ c₂ ih₁ ih₂ => exact kleisli_nonempty (ih₁ s) fun t _ => ih₂ t
  | ite b c₁ c₂ ih₁ ih₂ =>
    by_cases h : b s
    · rw [sem_ite_pos h]; exact ih₁ s
    · rw [sem_ite_neg h]; exact ih₂ s
  | choice c₁ c₂ ih₁ ih₂ => exact (ih₁ s).inl

/-! ## Lift kit (the execution-model laws, inherited from `kleisli`) -/

@[simp] theorem mem_semLift {c : Cmd} {m : Set State} {t : State} :
    t ∈ semLift c m ↔ ∃ s ∈ m, t ∈ sem c s := mem_kleisli

@[simp] theorem semLift_empty (c : Cmd) : semLift c ∅ = ∅ := kleisli_empty _

@[simp] theorem semLift_singleton (c : Cmd) (s : State) : semLift c {s} = sem c s :=
  kleisli_singleton _ _

theorem semLift_union (c : Cmd) (m₁ m₂ : Set State) :
    semLift c (m₁ ∪ m₂) = semLift c m₁ ∪ semLift c m₂ :=
  kleisli_union _ m₁ m₂

theorem semLift_seq (c₁ c₂ : Cmd) (m : Set State) :
    semLift (.seq c₁ c₂) m = semLift c₂ (semLift c₁ m) :=
  (kleisli_comp (sem c₁) (sem c₂) m).symm

theorem semLift_choice (c₁ c₂ : Cmd) (m : Set State) :
    semLift (.choice c₁ c₂) m = semLift c₁ m ∪ semLift c₂ m :=
  kleisli_pointwise_union (sem c₁) (sem c₂) m

theorem semLift_nonempty (c : Cmd) {m : Set State} (hm : m.Nonempty) :
    (semLift c m).Nonempty :=
  kleisli_nonempty hm fun s _ => sem_nonempty c s

end RelOL
