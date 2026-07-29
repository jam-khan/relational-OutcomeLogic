import RelationalOutcomeLogic.Hetero.Refinement

/-!
# Case study 2b: a certified translation bug inside a loop

Both sides translate `i := 0; while (i < 2) { x += y; i := i + 1 }`. From
`x = 200, y = 100` the C side wraps at the first addition and finishes both
iterations (`x = 144`); the Rust side panics at the first addition and the
panic aborts the loop — `errK` absorbs the remaining iterations, so the
Rust-like outcome set is *exhaustively* the panic.

The certificate is exhaustive (no `⊤`), which is what refuting the ∀∃-shaped
`refines` requires; it needs genuine loop evaluation through the
error-propagating iterates on the Rust side.
-/

namespace RelOL

/-- The shared loop guard, `i < 2` (named so rewriting stays first-order). -/
def gLoop : StC → Prop := fun s => s "i" < 2

/-- Shared loop body: wrapping/checked `x += y`, then `i := i + 1`. -/
def loopBodyC : CmdC := .seq (.addAssign "x" "y") (.assign "i" fun s => s "i" + 1)

def loopBodyR : CmdR := .seq (.addAssign "x" "y") (.assign "i" fun s => s "i" + 1)

/-- C-like: `i := 0; while (i < 2) loopBodyC`. -/
def cLoopC : CmdC := .seq (.assign "i" fun _ => 0) (.while gLoop loopBodyC)

/-- Rust-like: the same program under checked arithmetic. -/
def cLoopR : CmdR := .seq (.assign "i" fun _ => 0) (.while gLoop loopBodyR)

/-- The overflowing initial store: `x = 200`, `y = 100`, everything else `0`. -/
def sL : StC := stv 200 100

/-- The Rust side's entire outcome set is the panic: the first checked
addition overflows, and the panic propagates through the remaining loop
iterations via `errK`. -/
theorem semR_cLoopR_eval : errK (semR cLoopR) (.ok sL) = {.error ()} := by
  rw [errK_ok]
  show semR (.seq _ _) sL = _
  rw [semR_seq, semR_assign, kleisli_singleton, errK_ok]
  rw [semR_while_pos (b := gLoop) (s := Function.update sL "i" 0)
    (by simp [gLoop]) loopBodyR]
  have hbody : semR loopBodyR (Function.update sL "i" 0) = {.error ()} := by
    show semR (.seq _ _) _ = _
    rw [semR_seq, semR_addAssign_err (by simp [sL, WORD]), kleisli_singleton,
      errK_error]
  rw [hbody, semLiftR_singleton, errK_error]

/-- The C side terminates normally: two iterations, wrapping at the first. -/
theorem semC_cLoopC_eval :
    semC cLoopC sL
      = {Function.update (Function.update (Function.update (Function.update
          (Function.update sL "i" 0) "x" 44) "i" 1) "x" 144) "i" 2} := by
  show semC (.seq _ _) sL = _
  rw [semC_seq, semC_assign, kleisli_singleton]
  set s1 := Function.update sL "i" 0 with hs1
  have hmod1 : (s1 "x" + s1 "y") % WORD = 44 := by
    have hx : s1 "x" = 200 := by simp [hs1, sL]
    have hy : s1 "y" = 100 := by simp [hs1, sL]
    rw [hx, hy]; decide
  rw [semC_while_pos (b := gLoop) (s := s1) (by simp [gLoop, hs1]) loopBodyC]
  have hb1 : semC loopBodyC s1
      = {Function.update (Function.update s1 "x" 44) "i" 1} := by
    show semC (.seq _ _) _ = _
    rw [semC_seq, semC_addAssign, kleisli_singleton, semC_assign, hmod1]
    simp [hs1]
  rw [hb1, semLiftC_singleton]
  set s2 := Function.update (Function.update s1 "x" 44) "i" 1 with hs2
  have hmod2 : (s2 "x" + s2 "y") % WORD = 144 := by
    have hx : s2 "x" = 44 := by simp [hs2]
    have hy : s2 "y" = 100 := by simp [hs2, hs1, sL]
    rw [hx, hy]; decide
  rw [semC_while_pos (b := gLoop) (s := s2) (by simp [gLoop, hs2]) loopBodyC]
  have hb2 : semC loopBodyC s2
      = {Function.update (Function.update s2 "x" 144) "i" 2} := by
    show semC (.seq _ _) _ = _
    rw [semC_seq, semC_addAssign, kleisli_singleton, semC_assign, hmod2]
    simp [hs2]
  rw [hb2, semLiftC_singleton]
  rw [semC_while_neg (b := gLoop)
    (s := Function.update (Function.update s2 "x" 144) "i" 2)
    (by simp [gLoop]) loopBodyC]

/-- **Exhaustive translation-bug certificate for the loop**: from the
overflowing store, the C side computes while the Rust side's entire outcome
set is the panic. -/
theorem translation_loop_bug :
    quadH (fun m m' => m = {sL} ∧ m' = {.ok sL}) cLoopC cLoopR
      (atom fun _ b => b = .error ()) := by
  rintro m m' ⟨rfl, rfl⟩
  rw [show semLiftC cLoopC {sL} = semC cLoopC sL from semLiftC_singleton _ _,
    semLiftR_singleton, semR_cLoopR_eval, semC_cLoopC_eval]
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, by simp⟩

/-- The loop translation does not refine: every Rust outcome is the panic, so
the C side's outcome has no `ok` counterpart. -/
theorem not_refines_loop : ¬ refines cLoopC cLoopR := by
  intro h
  have hin : InRange sL := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sL, WORD]
  have hR : semR cLoopR sL = {.error ()} := by
    have heval := semR_cLoopR_eval
    rwa [errK_ok] at heval
  have ht := h sL hin _ (by rw [semC_cLoopC_eval]; rfl)
  rw [hR, Set.mem_singleton_iff] at ht
  exact absurd ht (by simp)

end RelOL
