import RelationalOutcomeLogic.Examples.NI
import RelationalOutcomeLogic.Tactic.Symexec

/-! # A loop that leaks: the two sides run different numbers of iterations -/

namespace RelOL

def leakBody : Cmd := x ::= x - 1 ;; low ::= low + 1

/-- Copies the positive part of the secret `x` into `low`. -/
def leakLoop : Cmd := WHILE x > 0 DO leakBody END

/-- One iteration on the left, none on the right. -/
def preLoop : RAssn State State := ⌈x = 1 ∧ x' = 0 ∧ low = 0 ∧ low' = 0⌉

theorem preLoop_sat : preLoop {st 1 0} {st 0 0} := by
  rw [preLoop, atom_singleton_iff]
  simp

/-- The certificate, by the atom lifting rule and symbolic execution on a symbolic store. -/
theorem leak_insecure : ⦃preLoop⦄ leakLoop ~ leakLoop ⦃⌈low = 1 ∧ low' = 0⌉ ⊕ₒ ⊤ₒ⦄ :=
  quad_conseq (fun _ _ h => h)
    (quad_atom_iff.mpr fun s s' ⟨hx, hx', hl, hl'⟩ => by
      symexec [leakLoop, leakBody, hx, hx', hl, hl'])
    fun _ _ h => oplus_left_top h

theorem not_NI_leakLoop : ¬ NI leakLoop := by
  intro hNI
  have hNI' : ⦃preLoop⦄ leakLoop ~ leakLoop ⦃⌈L⌉⦄ :=
    quad_conseq (atom_mono fun s s' h => by simp [L, h.2.2.1, h.2.2.2]) hNI fun _ _ h => h
  refine denial leak_insecure ?_ ⟨{st 1 0}, {st 0 0}, preLoop_sat⟩ hNI'
  rintro n n' hT hL
  obtain ⟨t, ht, t', ht', h1, h0⟩ := rel_true_positives hT
  have heq : t "low" = t' "low" := atom_pair_elim hL ht ht'
  omega

end RelOL
