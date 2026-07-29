import RelationalOutcomeLogic.Examples.NI

/-!
# Case study 1b: a loop that leaks, and its certified violation

`leakLoop ≡ while (x > 0) { x := x − 1; low := low + 1 }` copies the (positive
part of the) secret `x` into the public `low` — a noninterference violation
that needs *loop* reasoning: the two sides run different numbers of
iterations (1 vs 0 from the witness stores).

The certificate is established with the fuel rule `quad_while_fuel` (2 vs 1
units of fuel), and refutes `NI leakLoop` by the relational Principle of
Denial — the same certificate-plus-denial pattern as the loop-free case
study, now over a loop.
-/

namespace RelOL

/-- Loop body: `x := x − 1; low := low + 1`. -/
def leakBody : Cmd :=
  .seq (.assign "x" fun s => s "x" - 1) (.assign "low" fun s => s "low" + 1)

/-- The leaking loop: `while (x > 0) do leakBody`. -/
def leakLoop : Cmd := .while (fun s => s "x" > 0) leakBody

/-- Precondition of the certificate: low-equal (both `0`), secrets `1` vs `0`
— one iteration on the left, none on the right. -/
def preLoop : RAssn State State :=
  atom fun s s' => s "x" = 1 ∧ s' "x" = 0 ∧ s "low" = 0 ∧ s' "low" = 0

theorem preLoop_sat : preLoop {st 1 0} {st 0 0} := by
  rw [preLoop, atom_singleton_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem sem_leakBody (s : State) :
    sem leakBody s
      = {Function.update (Function.update s "x" (s "x" - 1)) "low"
          ((Function.update s "x" (s "x" - 1)) "low" + 1)} := by
  simp only [leakBody, sem_seq, sem_assign, kleisli_singleton]

/-- Zero iterations: guard already false. -/
theorem loopIter_leak_none {s : State} (hx : ¬ s "x" > 0) :
    loopIter (fun s => s "x" > 0) (sem leakBody) 1 s = {s} := by
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  apply loopIter_succ_neg
  exact hx

/-- One iteration from `x = 1`: ends with `x = 0` and `low` bumped. -/
theorem loopIter_leak_one {s : State} (hx : s "x" = 1) :
    loopIter (fun s => s "x" > 0) (sem leakBody) 2 s
      = {Function.update (Function.update s "x" 0) "low" (s "low" + 1)} := by
  rw [show (2 : ℕ) = 1 + 1 from rfl,
    loopIter_succ_pos (b := fun u => u "x" > 0) (s := s) (by omega),
    sem_leakBody, kleisli_singleton]
  have hstep : Function.update s "x" (s "x" - 1) = Function.update s "x" 0 := by
    rw [hx]; simp
  rw [hstep]
  have hlow : (Function.update s "x" 0) "low" = s "low" := by simp
  rw [hlow]
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  apply loopIter_succ_neg
  simp

/-- **The insecurity certificate for the loop**, via the fuel rule: with 2 vs 1
units of fuel the truncations already exhibit the leaking pair, and `⊕ ⊤`
absorbs the rest of the loop semantics. -/
theorem leak_insecure :
    ⦃preLoop⦄ leakLoop ~ leakLoop
      ⦃(atom fun t t' => t "low" = 1 ∧ t' "low" = 0) ⊕ₒ rtop⦄ := by
  unfold leakLoop
  apply quad_while_fuel 2 1
  rintro m m' ⟨hm, hm', hall⟩
  apply oplus_left_top
  obtain ⟨s₀, hs₀⟩ := hm
  obtain ⟨s₀', hs₀'⟩ := hm'
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hx, -, -, -⟩ := hall s₀ hs₀ s₀' hs₀'
    exact ⟨_, mem_kleisli.mpr ⟨s₀, hs₀, by rw [loopIter_leak_one hx]; rfl⟩⟩
  · obtain ⟨-, hx', -, -⟩ := hall s₀ hs₀ s₀' hs₀'
    exact ⟨_, mem_kleisli.mpr ⟨s₀', hs₀', by
      rw [loopIter_leak_none (by omega)]; rfl⟩⟩
  · rintro t ht t' ht'
    obtain ⟨s, hs, ht⟩ := mem_kleisli.mp ht
    obtain ⟨s', hs', ht'⟩ := mem_kleisli.mp ht'
    obtain ⟨hx, hx', hl, hl'⟩ := hall s hs s' hs'
    rw [loopIter_leak_one hx, Set.mem_singleton_iff] at ht
    rw [loopIter_leak_none (by omega), Set.mem_singleton_iff] at ht'
    subst ht ht'
    constructor
    · simp [hl]
    · exact hl'

/-- The loop violates noninterference — by denial from the certificate. -/
theorem not_NI_leakLoop : ¬ NI leakLoop := by
  intro hNI
  have hNI' : ⦃preLoop⦄ leakLoop ~ leakLoop ⦃atom L⦄ :=
    quad_conseq (atom_mono fun s s' h => by simp [L, h.2.2.1, h.2.2.2]) hNI
      (fun _ _ h => h)
  refine denial leak_insecure ?_ ⟨{st 1 0}, {st 0 0}, preLoop_sat⟩ hNI'
  rintro n n' hT hL
  obtain ⟨t, ht, t', ht', h1, h0⟩ := rel_true_positives hT
  have heq : t "low" = t' "low" := atom_pair_elim hL ht ht'
  omega

end RelOL
