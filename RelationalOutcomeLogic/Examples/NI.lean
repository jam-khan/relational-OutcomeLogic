import RelationalOutcomeLogic.Metatheory

/-!
# Case study 1: noninterference and its certified violation

Murray's classic insecure program: `if x > 0 then low := 1 else low := 0`.

The same quadruple form does both jobs:
* `NI c` — the quadruple *without* `⊤` **states** noninterference;
* `insecure` — the quadruple *with* `⊕ ⊤` **certifies** its violation;
* `not_NI` — the violation refutes the property (relational Principle of
  Denial instance, proved via the principled chain in `Metatheory.lean` as
  `not_NI_via_denial`).

Murray's under-approximate logic can prove only the second; HHL handles both
but only for a single program over a single state space.
-/

namespace RelOL

/-- The insecure program: branches on the secret `x`, leaks through `low`. -/
def prog : Cmd :=
  .ite (fun s => s "x" > 0) (.assign "low" fun _ => 1) (.assign "low" fun _ => 0)

/-- Low-equivalence: the public variable `low` agrees. -/
def L : State → State → Prop := fun s s' => s "low" = s' "low"

/-- Noninterference as a RelOL quadruple — no `⊤`, exhaustive coverage. -/
def NI (c : Cmd) : Prop := ⦃atom L⦄ c ~ c ⦃atom L⦄

/-- The precondition of the insecurity certificate: low-equal initial states
that drive the two copies down different branches. -/
def preIns : RAssn State State :=
  atom fun s s' => L s s' ∧ s "x" > 0 ∧ s' "x" ≤ 0

theorem sem_prog_pos {s : State} (h : s "x" > 0) :
    sem prog s = {Function.update s "low" (1 : Int)} :=
  sem_ite_pos h _ _

theorem sem_prog_neg {s : State} (h : ¬ s "x" > 0) :
    sem prog s = {Function.update s "low" (0 : Int)} :=
  sem_ite_neg h _ _

/-- The precondition is satisfiable — the certificate is not vacuous. -/
theorem preIns_sat : preIns {st 1 0} {st 0 0} := by
  rw [preIns, atom_singleton_iff]
  refine ⟨rfl, ?_, ?_⟩ <;> simp

/-- **The insecurity certificate**: from any low-equal pre-models split across
the branch boundary, a leaking outcome pair (`low = 1` vs `low = 0`) is jointly
reachable. The `⊕ ⊤` makes this an under-approximate (violation-witnessing)
claim. -/
theorem insecure :
    ⦃preIns⦄ prog ~ prog ⦃(atom fun s s' => s "low" = 1 ∧ s' "low" = 0) ⊕ₒ rtop⦄ := by
  rintro m m' ⟨hm, hm', hall⟩
  apply oplus_left_top
  refine ⟨semLift_nonempty _ hm, semLift_nonempty _ hm', ?_⟩
  rintro t ht t' ht'
  obtain ⟨s, hs, ht⟩ := mem_semLift.mp ht
  obtain ⟨s', hs', ht'⟩ := mem_semLift.mp ht'
  obtain ⟨-, hx, hx'⟩ := hall s hs s' hs'
  rw [sem_prog_pos hx, Set.mem_singleton_iff] at ht
  rw [sem_prog_neg (by omega), Set.mem_singleton_iff] at ht'
  subst ht ht'
  simp

/-- The violation refutes noninterference: a direct counterexample instance. -/
theorem not_NI : ¬ NI prog := by
  intro h
  have hpost := h {st 1 0} {st 0 0} (by rw [atom_singleton_iff]; rfl)
  rw [semLift_singleton, semLift_singleton, sem_prog_pos (by simp),
    sem_prog_neg (by simp)] at hpost
  have hL := atom_pair_elim hpost (Set.mem_singleton _) (Set.mem_singleton _)
  simp [L] at hL

/-- The principled route: `insecure` + the relational Principle of Denial refute
noninterference. The insecurity certificate *is* the disproof — one logic, both
directions (the contrast with Murray's violation-only logic and with unary OL). -/
theorem not_NI_via_denial : ¬ NI prog := by
  intro hNI
  have hNI' : ⦃preIns⦄ prog ~ prog ⦃atom L⦄ :=
    quad_conseq (atom_mono fun s s' h => h.1) hNI (fun _ _ h => h)
  refine denial insecure ?_ ⟨{st 1 0}, {st 0 0}, preIns_sat⟩ hNI'
  rintro n n' hT hL
  obtain ⟨t, ht, t', ht', h1, h0⟩ := rel_true_positives hT
  have heq : t "low" = t' "low" := atom_pair_elim hL ht ht'
  omega

end RelOL
