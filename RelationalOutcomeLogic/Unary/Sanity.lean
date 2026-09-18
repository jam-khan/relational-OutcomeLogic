import RelationalOutcomeLogic.Unary.Triple

/-! # Unary sanity check: the malloc example of Outcome Logic -/

namespace OL

open RelOL

/-- Allocation succeeds (`p := 1`) or fails (`p := 0`). -/
def mallocProg : Cmd := (p ::= 1) + (p ::= 0)

theorem assign_const_spec (x : String) (v : Int) :
    ⦅⌜True⌝⦆ ↑x ::= ↑(fun _ => v) ⦅⌜fun s => s x = v⌝⦆ := by
  rintro m ⟨hne, -⟩
  rw [semLift_assign]
  exact ⟨hne.image _, by rintro _ ⟨s, -, rfl⟩; simp⟩

theorem malloc_spec : ⦅⌜True⌝⦆ mallocProg ⦅⌜p = 1⌝ ⊕ᵤ ⌜p = 0⌝⦆ :=
  triple_choice (assign_const_spec "p" 1) (assign_const_spec "p" 0)

/-- Success is genuinely reachable: under-approximation extracted from the OL spec. -/
theorem malloc_reaches_one (m : Set State) (hm : m.Nonempty) :
    ∃ t ∈ semLift mallocProg m, t "p" = 1 :=
  true_positivesU (oplusU_drop (malloc_spec m ⟨hm, fun _ _ => trivial⟩))

end OL
