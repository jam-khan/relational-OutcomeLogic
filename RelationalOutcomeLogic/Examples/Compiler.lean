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

/-! ## The loop miscompilation

The buggy pass also drops the error check from the *loop guard*: after an
in-body exception the target keeps looping. `thrLoop` throws in its first
iteration; the correct pass exits the loop at the throw-point store (and is
covered by the ∀-programs theorem `lower_correct`), while the buggy target
runs the rest of the iteration — observably bumping `i`. -/

/-- `while (i < 1) { throw; i := i + 1 }`. -/
def thrLoop : CmdS :=
  .while (fun s => s "i" < 1) (.seq .throw (.assign "i" fun s => s "i" + 1))

/-- The correct pass validates on the loop program — an instance of the
∀-programs theorem, not a bespoke proof. -/
theorem lower_thrLoop_correct : loweredW lower thrLoop zSt :=
  lower_correct _ (by simp [thrLoop]) _ rfl

theorem semS_thrLoop : semS thrLoop zSt = {Except.error zSt} := by
  rw [thrLoop, semS_while,
    errLoopSem_pos (b := fun s => s "i" < 1) (s := zSt) (by simp [zSt])]
  rw [semS_seq, semS_throw, kleisli_singleton, errK_error, kleisli_singleton,
    errK_error]

theorem sem_lowerBug_thrLoop :
    sem (lowerBug thrLoop) zSt
      = {Function.update (Function.update zSt "err" 1) "i" 1} := by
  change sem (.while (fun s => s "i" < 1)
    (.seq (.assign "err" fun _ => 1) (.assign "i" fun s => s "i" + 1))) zSt = _
  rw [sem_while_pos (b := fun s => s "i" < 1) (s := zSt) (by simp [zSt])]
  have hbody : sem (.seq (.assign "err" fun _ => (1 : Int))
      (.assign "i" fun s => s "i" + 1)) zSt
      = {Function.update (Function.update zSt "err" 1) "i" 1} := by
    rw [sem_seq, sem_assign, kleisli_singleton, sem_assign]
    simp [zSt]
  rw [hbody, semLift_singleton,
    sem_while_neg (b := fun s => s "i" < 1)
      (s := Function.update (Function.update zSt "err" 1) "i" 1) (by simp)]

/-- **The loop miscompilation certificate**: the source raises with `i = 0`;
the buggy target finishes the iteration and exits with `i = 1`. -/
theorem miscompiled_loop :
    quadSem (semLiftS thrLoop) (semLift (lowerBug thrLoop))
      (fun m m' => m = {Except.ok zSt} ∧ m' = {zSt})
      (atom fun a t' => a = Except.error zSt ∧ t' "i" = 1 ∧ zSt "i" = 0) := by
  rintro m m' ⟨rfl, rfl⟩
  rw [semLiftS_singleton, errK_ok, semS_thrLoop, semLift_singleton,
    sem_lowerBug_thrLoop]
  refine atom_singleton_iff.mpr ⟨rfl, ?_, rfl⟩
  simp

/-- The buggy pass provably miscompiles the loop program, by denial. -/
theorem lowerBug_loop_not_correct : ¬ lowered lowerBug thrLoop zSt := by
  refine denial miscompiled_loop ?_ ⟨_, _, rfl, rfl⟩
  rintro n n' hT hL
  obtain ⟨⟨a, ha⟩, ⟨t', ht'⟩, hall⟩ := hT
  obtain ⟨rfl, hi1, -⟩ := hall a ha t' ht'
  have hrel : t' = Function.update zSt "err" 1 := atom_pair_elim hL ha ht'
  rw [hrel] at hi1
  simp [zSt] at hi1

end RelOL
