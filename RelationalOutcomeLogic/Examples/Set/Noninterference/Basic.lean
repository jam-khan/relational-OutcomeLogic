import RelationalOutcomeLogic.Set.Metatheory
import RelationalOutcomeLogic.Tactic.Symexec

/-! # Noninterference: a leak is certified, and the certificate refutes NI -/

namespace RelOL

/-- Concrete-state builder for the NI example. -/
def st (x low : Int) : State := fun v => if v = "x" then x else if v = "low" then low else 0

@[simp] theorem st_x (x low : Int) : st x low "x" = x := by simp [st]

@[simp] theorem st_low (x low : Int) : st x low "low" = low := by simp [st]


/-- Branches on the secret `x` and leaks it through `low`. -/
def prog : Cmd := IF x > 0 THEN low ::= 1 ELSE low ::= 0 END

def L : State → State → Prop := fun s s' => s "low" = s' "low"

def NI (c : Cmd) : Prop := ⦃⌈L⌉⦄ c ~ c ⦃⌈L⌉⦄

/-- Low-equal inputs on opposite sides of the branch. -/
def preIns : RAssn State State := ⌈↑L ∧ x > 0 ∧ x' ≤ 0⌉

theorem preIns_sat : preIns {st 1 0} {st 0 0} := by
  rw [preIns, atom_singleton_iff]
  refine ⟨rfl, ?_, ?_⟩ <;> simp

/-- The insecurity certificate: a leaking outcome pair is jointly reachable. -/
theorem insecure : ⦃preIns⦄ prog ~ prog ⦃⌈low = 1 ∧ low' = 0⌉ ⊕ₒ ⊤ₒ⦄ :=
  quad_conseq (fun _ _ h => h)
    (quad_atom_iff.mpr fun s s' ⟨_, hx, hx'⟩ => by symexec [prog, hx, hx'])
    fun _ _ h => oplus_left_top h

/-- The certificate is the disproof (Principle of Denial). -/
theorem not_NI : ¬ NI prog := by
  intro hNI
  have hNI' : ⦃preIns⦄ prog ~ prog ⦃⌈L⌉⦄ :=
    quad_conseq (atom_mono fun s s' h => h.1) hNI fun _ _ h => h
  refine denial insecure ?_ ⟨{st 1 0}, {st 0 0}, preIns_sat⟩ hNI'
  rintro n n' hT hL
  obtain ⟨t, ht, t', ht', h1, h0⟩ := rel_true_positives hT
  have heq : t "low" = t' "low" := atom_pair_elim hL ht ht'
  omega

end RelOL
