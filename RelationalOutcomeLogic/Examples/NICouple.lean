import RelationalOutcomeLogic.Examples.NI
import RelationalOutcomeLogic.Examples.GNI

/-! # Coupling noninterference: nondeterminism is not leakage -/

namespace RelOL

def CNI (c : Cmd) : Prop := ⦃couple L⦄ c ~ c ⦃couple L⦄

/-- Publishes `0` or `1`, independently of the secret. -/
def secProg : Cmd := (low ::= 0) + (low ::= 1)

/-- The product-model `NI` rejects the secure `secProg`: the rectangle demands that
all cross pairs agree. -/
theorem not_NI_secProg : ¬ NI secProg := by
  intro h
  have hpost := h {st 0 0} {st 0 0} (atom_singleton_iff.mpr rfl)
  rw [semLift_singleton] at hpost
  have h0 : Function.update (st 0 0) "low" (0 : Int) ∈ sem secProg (st 0 0) := by
    simp [secProg]
  have h1 : Function.update (st 0 0) "low" (1 : Int) ∈ sem secProg (st 0 0) := by
    simp [secProg]
  have hbad := atom_pair_elim hpost h0 h1
  simp [L] at hbad

/-- Coupling-NI accepts it, by C-Choice over C-Assign: branch `i` pairs with branch `i`. -/
theorem CNI_secProg : CNI secProg :=
  quad_choice_couple
    (quad_conseq (couple_mono fun _ _ _ => by simp [L]) (quad_assign_couple "low" "low" _ _)
      fun _ _ h => h)
    (quad_conseq (couple_mono fun _ _ _ => by simp [L]) (quad_assign_couple "low" "low" _ _)
      fun _ _ h => h)

/-- Coupling-NI still rejects the leaky `prog`. -/
theorem not_CNI_prog : ¬ CNI prog := by
  intro h
  have := h {st 1 0} {st 0 0} (couple_singleton_iff.mpr rfl)
  symexec [prog, L] at this

theorem GNI_iff_coupleL {c : Cmd} :
    GNI c ↔ ∀ s s' : State, coupleL (fun t t' => t "low" = t' "low") (sem c s) (sem c s') :=
  Iff.rfl

theorem GNI_secProg : GNI secProg := by
  intro s s' t ht
  simp only [secProg, Cmd.add_def, sem_choice, sem_assign, Set.mem_union,
    Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl
  · exact ⟨Function.update s' "low" 0, by simp [secProg], by simp⟩
  · exact ⟨Function.update s' "low" 1, by simp [secProg], by simp⟩

end RelOL
