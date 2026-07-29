import RelationalOutcomeLogic.Unary.Triple

/-!
# Unary sanity theorems

Phase-1 sanity checks that debug the outcome-set bookkeeping in isolation
before doubling it relationally:

* `malloc_spec` — the malloc-style example `⟨true⟩ C ⟨ok ⊕ er⟩`: nondeterministic
  choice yields *both* outcomes, each actually reachable.
* `malloc_reaches_one` — an IL-style subsumption instance (one direction of OL
  Thm. 4.5 for a concrete program): from the OL spec, dropping outcomes
  (Lemma B.1) plus reachability extraction yields an existential witness.
-/

namespace OL

open RelOL

/-- Malloc-style program: `p := 1` (allocation succeeds) or `p := 0` (fails). -/
def mallocProg : Cmd := .choice (.assign "p" fun _ => 1) (.assign "p" fun _ => 0)

theorem assign_const_spec (x : String) (v : Int) :
    triple (atomU fun _ => True) (.assign x fun _ => v) (atomU fun s => s x = v) := by
  rintro m ⟨hne, -⟩
  refine ⟨semLift_nonempty (by simp) hne, ?_⟩
  rintro t ht
  obtain ⟨s, -, ht⟩ := mem_semLift.mp ht
  simp only [sem_assign, Set.mem_singleton_iff] at ht
  subst ht
  simp

/-- `⟨true⟩ mallocProg ⟨p = 1 ⊕ p = 0⟩`: both outcomes exist and are reachable. -/
theorem malloc_spec :
    triple (atomU fun _ => True) mallocProg
      (oplusU (atomU fun s => s "p" = 1) (atomU fun s => s "p" = 0)) :=
  triple_choice (assign_const_spec "p" 1) (assign_const_spec "p" 0)

/-- IL-style consequence: success (`p = 1`) is genuinely reachable from any
nonempty initial set — under-approximation extracted from the OL spec. -/
theorem malloc_reaches_one (m : Set State) (hm : m.Nonempty) :
    ∃ t ∈ semLift mallocProg m, t "p" = 1 :=
  true_positivesU (oplusU_drop (malloc_spec m ⟨hm, fun _ _ => trivial⟩))

end OL
