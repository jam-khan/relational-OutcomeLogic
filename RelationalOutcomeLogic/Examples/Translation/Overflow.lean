import RelationalOutcomeLogic.Examples.Translation.Refinement
import RelationalOutcomeLogic.Set.Refutation

/-! # A certified translation bug: `x += y` wraps in C and panics in Rust -/

namespace RelOL

def cProg : CmdC := .addAssign "x" "y"

def rProg : CmdR := .addAssign "x" "y"

/-- The same in-range store on both sides, with `x + y` overflowing the word. -/
def preOvf : RAssn StC (Except Unit StR) :=
  atom fun s b => b = .ok s ∧ s "x" + s "y" ≥ WORD ∧ InRange s

def s₀ : StC := stv 200 100

theorem inRange_s₀ : InRange s₀ := by
  simp [InRange, s₀, WORD]

theorem preOvf_sat : preOvf {s₀} {Except.ok s₀} := by
  rw [preOvf, atom_singleton_iff]
  exact ⟨rfl, by simp [s₀, WORD], inRange_s₀⟩

/-- Exhaustive certificate (Conseq + the panic axiom): the C side computes while
*every* Rust outcome is the panic. -/
theorem translation_bug_exhaustive :
    quadH preOvf cProg rProg (atom fun _ b => b = .error ()) :=
  quadSem_conseq (atom_mono fun _ _ h => ⟨h.1, h.2.1⟩) (quadH_addAssign_panic "x" "y")
    fun _ _ h => h

theorem translation_bug :
    quadH preOvf cProg rProg ((atom fun _ b => b = .error ()) ⊕ₒ ⊤ₒ) :=
  fun m m' h => oplus_left_top (translation_bug_exhaustive m m' h)

/-- The wrapped C outcome is an orphan: no Rust outcome is `ok`. -/
def ovfCert : OrphanCert (semLiftC cProg) (semLiftR rProg) (fun t b => b = .ok t) where
  s₀ := s₀
  s₀' := .ok s₀
  t := Function.update s₀ "x" 44
  reach := by symexecH [cProg, s₀]
  orphan := by symexecH [rProg, s₀]

theorem not_refines : ¬ refines cProg rProg := fun h =>
  ovfCert.refutes (coupleL_singleton_iff.mpr ⟨rfl, inRange_s₀⟩) (refines_iff_quadH.mp h)

/-- The contrast row: without overflow the translation is correct, over *all* such stores
at once (Conseq + the ok axiom, coupling tier). -/
theorem correct_translation :
    quadH (couple fun s a => a = .ok s ∧ InRange s ∧ s "x" + s "y" < WORD)
      cProg rProg (couple fun t b => b = .ok t) :=
  quadSem_conseq (couple_mono fun _ _ h => ⟨h.1, by have := h.2.1; unfold InRange at this; omega,
    h.2.2⟩) (quadH_addAssign_ok_couple "x" "y") fun _ _ h => h

end RelOL
