import RelationalOutcomeLogic.Examples.Translation.Overflow

/-! # The translation bug inside a loop: the panic aborts the Rust loop -/

namespace RelOL

def gLoop : StC → Prop := fun s => s "i" < 2

def loopBodyC : CmdC := .seq (.addAssign "x" "y") (.assign "i" fun s => s "i" + 1)

def loopBodyR : CmdR := .seq (.addAssign "x" "y") (.assign "i" fun s => s "i" + 1)

/-- `i := 0; while (i < 2) { x += y; i := i + 1 }`, with wrapping addition. -/
def cLoopC : CmdC := .seq (.assign "i" fun _ => 0) (.while gLoop loopBodyC)

/-- The same program with checked addition. -/
def cLoopR : CmdR := .seq (.assign "i" fun _ => 0) (.while gLoop loopBodyR)

/-- Exhaustive certificate: C runs both iterations (wrapping at the first), while the first
checked addition panics and the panic propagates through the rest of the Rust loop. -/
theorem translation_loop_bug :
    quadH (exactly {s₀} {.ok s₀}) cLoopC cLoopR (atom fun t b => t "x" = 144 ∧ b = .error ()) := by
  rintro m m' ⟨rfl, rfl⟩
  symexecH [cLoopC, cLoopR, loopBodyC, loopBodyR, gLoop, s₀]

def loopCert : OrphanCert (semLiftC cLoopC) (semLiftR cLoopR) (fun t b => b = .ok t) where
  s₀ := s₀
  s₀' := .ok s₀
  t := Function.update (Function.update (Function.update (Function.update
    (Function.update s₀ "i" 0) "x" 44) "i" 1) "x" 144) "i" 2
  reach := by symexecH [cLoopC, loopBodyC, gLoop, s₀]
  orphan := by symexecH [cLoopR, loopBodyR, gLoop, s₀]

theorem not_refines_loop : ¬ refines cLoopC cLoopR := fun h =>
  loopCert.refutes (coupleL_singleton_iff.mpr ⟨rfl, inRange_s₀⟩) (refines_iff_quadH.mp h)

end RelOL
