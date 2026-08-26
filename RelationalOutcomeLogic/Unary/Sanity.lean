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

/-
  Malloc-style program:
  (allocation succeeds) `p := 1`
  (allocation fails)    `p := 0`
-/
def mallocProg : Cmd := (p ::= 1) + (p ::= 0)

/-
  Note the `↑`-escapes: `x` and `v` are Lean variables,
  so the program-variable and numeral sugar does not apply.
  Only concrete programs read as `p ::= 1`.
-/
theorem assign_const_spec (x : String) (v : Int) :
    ⦅⌜True⌝⦆ ↑x ::= ↑(fun _ => v) ⦅⌜fun s => s x = v⌝⦆ := by
  unfold triple
  intro m hm
  unfold atomU
  simp
  unfold atomU at hm
  grind

/-
  `⟨true⟩ mallocProg ⟨p = 1 ⊕ p = 0⟩`:
  both outcomes exist and are reachable.
-/
theorem malloc_spec : ⦅⌜True⌝⦆ mallocProg ⦅⌜p = 1⌝ ⊕ᵤ ⌜p = 0⌝⦆ :=
  triple_choice (assign_const_spec "p" 1) (assign_const_spec "p" 0)

/-
  IL-style consequence: success (`p = 1`) is genuinely
  reachable from any nonempty initial set — under-approximation
  extracted from the OL spec.
-/
theorem malloc_reaches_one (m : Set State) (hm : m.Nonempty) :
    ∃ t ∈ semLift mallocProg m, t "p" = 1 :=
  true_positivesU (oplusU_drop (malloc_spec m ⟨hm, fun _ _ => trivial⟩))

end OL
