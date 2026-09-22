import RelationalOutcomeLogic.Generic.Assertions

/-! # Shared relational judgments over outcome transformers and state kernels -/

namespace RelOL.Generic

universe u v
variable {M : Type u → Type v} [OutcomeModel M]
variable {α β γ δ : Type u}
open OutcomeModel

def quadSem (F : M α → M γ) (G : M β → M δ)
    (P : RAssn M α β) (Q : RAssn M γ δ) : Prop :=
  ∀ x y, P x y → Q (F x) (G y)

/-- A judgment over state kernels, lifted by the model's sequencing operation. -/
def quad (P : RAssn M α β) (k : α → M γ) (l : β → M δ)
    (Q : RAssn M γ δ) : Prop := quadSem (fun x => bind x k) (fun y => bind y l) P Q

end RelOL.Generic
