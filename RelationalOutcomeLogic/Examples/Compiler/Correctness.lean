import RelationalOutcomeLogic.Examples.Compiler.Lowering
import RelationalOutcomeLogic.Set.Metatheory

/-! # Compiler correctness per pass, and a certified miscompilation -/

namespace RelOL

/-- The all-zero initial store (in particular `err = 0`). -/
def zSt : State := fun _ => 0

/-- The store after `x := 1` — also the throw-point store of `thrProg`. -/
def sX : State := Function.update zSt "x" 1

/-- A non-throwing source program. -/
def okProg : CmdS := .seq (.assign "x" fun _ => 1) (.assign "y" fun _ => 2)

/-- A throwing source program. -/
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

/-- The ok path. -/
theorem lower_ok_correct : lowered lower okProg zSt := by
  rintro m m' ⟨rfl, rfl⟩
  rw [semLiftS_singleton, errK_ok, semS_okProg, semLift_singleton, sem_lower_okProg]
  exact atom_singleton_iff.mpr rfl

/-- The exceptional path. -/
theorem lower_thr_correct : lowered lower thrProg zSt := by
  rintro m m' ⟨rfl, rfl⟩
  rw [semLiftS_singleton, errK_ok, semS_thrProg, semLift_singleton, sem_lower_thrProg]
  exact atom_singleton_iff.mpr rfl

/-! ## The certified miscompilation -/

/-- The miscompilation certificate. -/
theorem miscompiled :
    quadSem (semLiftS thrProg) (semLift (lowerBug thrProg))
      (fun m m' => m = {Except.ok zSt} ∧ m' = {zSt})
      (atom fun a t' => a = Except.error sX ∧ t' "y" = 2 ∧ sX "y" = 0) := by
  rintro m m' ⟨rfl, rfl⟩
  rw [semLiftS_singleton, errK_ok, semS_thrProg, semLift_singleton, sem_lowerBug_thrProg]
  refine atom_singleton_iff.mpr ⟨rfl, ?_, ?_⟩
  · simp
  · simp [sX, zSt]

/-- The certificate refutes the correctness quadruple (relational Principle of Denial). -/
theorem lowerBug_not_correct : ¬ lowered lowerBug thrProg zSt := by
  refine denial miscompiled ?_ ⟨_, _, rfl, rfl⟩
  rintro n n' hT hL
  obtain ⟨⟨a, ha⟩, ⟨t', ht'⟩, hall⟩ := hT
  obtain ⟨rfl, hy2, -⟩ := hall a ha t' ht'
  have hrel : t' = Function.update sX "err" 1 := atom_pair_elim hL ha ht'
  rw [hrel] at hy2
  simp [sX, zSt] at hy2

/-! ## The loop miscompilation -/

/-- `while (i < 1) { throw; i := i + 1 }`. -/
def thrLoop : CmdS :=
  .while (fun s => s "i" < 1) (.seq .throw (.assign "i" fun s => s "i" + 1))

/-- The correct pass validates the loop program, as an instance of the ∀-programs theorem. -/
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

/-- The loop miscompilation certificate. -/
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

/-! ## Bitotal pass, instantiated -/

theorem lower_okProg_couple : loweredC lower okProg :=
  lower_correct_couple _ (by simp [okProg])

theorem lower_thrProg_couple : loweredC lower thrProg :=
  lower_correct_couple _ (by simp [thrProg])

theorem lower_thrLoop_couple : loweredC lower thrLoop :=
  lower_correct_couple _ (by simp [thrLoop])

end RelOL
