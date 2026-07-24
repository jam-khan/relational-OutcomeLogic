import RelationalOutcomeLogic.Compiler.Lowering
import RelationalOutcomeLogic.Metatheory

/-!
# Case study 3: per-pass compiler correctness and a certified miscompilation

Translation validation for the exceptions-to-error-codes pass, per program
(this is deliberately *not* compiler verification — each theorem certifies one
program/pass pair):

* `lower_ok_correct` — the ok path: a non-throwing program is lowered correctly.
* `lower_thr_correct` — the exceptional path: for a program that throws
  mid-sequence, the correct pass sets the error flag and the guard stops
  execution; the target store matches the throw-point store.
* `miscompiled` — the **certified miscompilation witness**: under the buggy
  pass (dropped error guard) the target keeps executing after the exception,
  observably clobbering `y`. What fuzzers like Csmith observe empirically, as a
  kernel-checked theorem.
* `lowerBug_not_correct` — the certificate refutes the correctness quadruple
  via the relational Principle of Denial (same pattern as `not_NI_via_denial`
  and `not_refines`: the violation certificate *is* the disproof).
-/

namespace RelOL

/-- The all-zero initial store (in particular `err = 0`). -/
def zSt : State := fun _ => 0

/-- The store after `x := 1` — also the throw-point store of `thrProg`. -/
def sX : State := Function.update zSt "x" 1

/-- A non-throwing source program: `x := 1; y := 2`. -/
def okProg : CmdS := .seq (.assign "x" fun _ => 1) (.assign "y" fun _ => 2)

/-- A throwing source program: `x := 1; (throw; y := 2)` — the assignment to
`y` is dead code after the exception. -/
def thrProg : CmdS := .seq (.assign "x" fun _ => 1) (.seq .throw (.assign "y" fun _ => 2))

/-! ## Computation lemmas (each side reduces to a singleton) -/

theorem semS_okProg : semS okProg zSt = {Except.ok (Function.update sX "y" 2)} := by
  simp [okProg, semS, sX]

theorem sem_lower_okProg : sem (lower okProg) zSt = {Function.update sX "y" 2} := by
  simp [okProg, lower, sem, sX, zSt]

theorem semS_thrProg : semS thrProg zSt = {Except.error sX} := by
  simp [thrProg, semS, sX]

theorem sem_lower_thrProg :
    sem (lower thrProg) zSt = {Function.update sX "err" 1} := by
  simp [thrProg, lower, sem, sX, zSt]

theorem sem_lowerBug_thrProg :
    sem (lowerBug thrProg) zSt
      = {Function.update (Function.update sX "err" 1) "y" 2} := by
  simp [thrProg, lowerBug, sem, sX]

/-! ## Correctness certificates (translation validation, per program) -/

/-- The ok path: the correct pass validates on the non-throwing program. -/
theorem lower_ok_correct : lowered lower okProg zSt := by
  rintro m m' ⟨rfl, rfl⟩
  rw [semLiftS_singleton, errK_ok, semS_okProg, semLift_singleton, sem_lower_okProg]
  exact atom_singleton_iff.mpr rfl

/-- The exceptional path: the correct pass validates on the throwing program —
the target ends at the throw-point store with the error flag set, and the guard
prevents the dead code from running. -/
theorem lower_thr_correct : lowered lower thrProg zSt := by
  rintro m m' ⟨rfl, rfl⟩
  rw [semLiftS_singleton, errK_ok, semS_thrProg, semLift_singleton, sem_lower_thrProg]
  exact atom_singleton_iff.mpr rfl

/-! ## The certified miscompilation -/

/-- **The miscompilation certificate**: under the buggy pass, the source raises
at throw-point store `sX` (where `y = 0`), but the target's final store has
`y = 2` — the dead code ran. An observable, jointly reachable divergence,
stated as an exhaustive heterogeneous quadruple. -/
theorem miscompiled :
    quadSem (semLiftS thrProg) (semLift (lowerBug thrProg))
      (fun m m' => m = {Except.ok zSt} ∧ m' = {zSt})
      (atom fun a t' => a = Except.error sX ∧ t' "y" = 2 ∧ sX "y" = 0) := by
  rintro m m' ⟨rfl, rfl⟩
  rw [semLiftS_singleton, errK_ok, semS_thrProg, semLift_singleton, sem_lowerBug_thrProg]
  refine atom_singleton_iff.mpr ⟨rfl, ?_, ?_⟩
  · simp
  · simp [sX, zSt]

/-- **The certificate refutes the correctness quadruple** (relational Principle
of Denial): the buggy pass provably miscompiles `thrProg`. -/
theorem lowerBug_not_correct : ¬ lowered lowerBug thrProg zSt := by
  refine denial miscompiled ?_ ⟨_, _, rfl, rfl⟩
  rintro n n' hT hL
  obtain ⟨⟨a, ha⟩, ⟨t', ht'⟩, hall⟩ := hT
  obtain ⟨rfl, hy2, -⟩ := hall a ha t' ht'
  have hrel : t' = Function.update sX "err" 1 := atom_pair_elim hL ha ht'
  rw [hrel] at hy2
  simp [sX, zSt] at hy2

end RelOL
