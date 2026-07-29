import RelationalOutcomeLogic.Hetero.Refinement

/-!
# Case study 2: a certified translation bug across the semantic gap

The same source-level statement `x += y` translated to a C-like fragment
(silent wrap-around) and a Rust-like fragment (checked add, panics on
overflow). Under an overflowing in-range precondition:

* `translation_bug_exhaustive` — the *exhaustive* quadruple: the C side has
  outcomes while the Rust side's **entire** outcome set is the panic. This is
  the certificate strong enough to refute refinement.
* `translation_bug` — the same certificate in `⊕ ⊤` (outcome-dropping) form.
* `not_refines` — the certified counterexample to refinement, derived from the
  exhaustive certificate (not re-proved from scratch).
* `correct_translation` — the contrast row: under a non-overflowing
  precondition the same program pair satisfies the ok-matching quadruple
  (the singleton-pre pattern; see Notes.md on product-model vs couplings).
-/

namespace RelOL

/-- The C-like translation of `x += y`. -/
def cProg : CmdC := .addAssign "x" "y"

/-- The Rust-like translation of `x += y`. -/
def rProg : CmdR := .addAssign "x" "y"

/-- Overflowing precondition: same in-range store on both sides (Rust entered
via `.ok`), with `x + y` overflowing the word. -/
def preOvf : RAssn StC (Except Unit StR) := atom fun s b =>
  b = .ok s ∧ s "x" + s "y" ≥ WORD ∧ InRange s

/-- Witness store: `x = 200, y = 100` on the 8-bit machine. -/
def s₀ : StC := stv 200 100

/-- The precondition is satisfiable — the certificate is not vacuous. -/
theorem preOvf_sat : preOvf {s₀} {Except.ok s₀} := by
  rw [preOvf, atom_singleton_iff]
  refine ⟨rfl, ?_, ?_⟩
  · simp only [s₀, stv_x, stv_y, WORD]
    omega
  · simp only [InRange, s₀, stv_x, stv_y, WORD]
    omega

/-- **The exhaustive certificate**: under overflow, the C side computes (wraps)
while the Rust side's entire outcome set is the panic — no `⊤`, exhaustive
coverage of the Rust outcomes. -/
theorem translation_bug_exhaustive :
    quadH preOvf cProg rProg (atom fun _ b => b = .error ()) := by
  rintro m m' ⟨hm, hm', hall⟩
  refine ⟨semLiftC_nonempty (by simp [cProg]) hm, semLiftR_nonempty (by simp [rProg]) hm', ?_⟩
  rintro t ht b hb
  obtain ⟨s, hs, -⟩ := mem_semLiftC.mp ht
  obtain ⟨a, ha, hb⟩ := mem_semLiftR.mp hb
  obtain ⟨rfl, hovf, -⟩ := hall s hs a ha
  rw [errK_ok,
    show semR rProg s = {Except.error ()} from semR_addAssign_err (by omega)] at hb
  simpa using hb

/-- The certificate in outcome-dropping (`⊕ ⊤`) form. -/
theorem translation_bug :
    quadH preOvf cProg rProg ((atom fun _ b => b = .error ()) ⊕ₒ rtop) :=
  fun m m' h => oplus_left_top (translation_bug_exhaustive m m' h)

/-- **The certified counterexample to refinement**, derived from the exhaustive
certificate: refinement would match some C outcome with an ok Rust outcome, but
the certificate says every Rust outcome is the panic. -/
theorem not_refines : ¬ refines cProg rProg := by
  intro h
  have hpost := translation_bug_exhaustive {s₀} {Except.ok s₀} preOvf_sat
  obtain ⟨t, ht⟩ := hpost.1
  obtain ⟨s, hs, htC⟩ := mem_semLiftC.mp ht
  rw [Set.mem_singleton_iff] at hs
  subst hs
  have hok : Except.ok t ∈ semR rProg s₀ :=
    h s₀ (by simp only [InRange, s₀, stv_x, stv_y, WORD]; omega) t htC
  have hmem : (Except.ok t : Except Unit StR) ∈ semLiftR rProg {Except.ok s₀} :=
    mem_semLiftR.mpr ⟨.ok s₀, rfl, by rwa [errK_ok]⟩
  have hbad := atom_pair_elim hpost ht hmem
  simp at hbad

/-- **The contrast row**: under a non-overflowing precondition, the same
program pair satisfies the ok-matching quadruple — the two sides compute the
same store. (Singleton-pre pattern: `atom`'s cross-product semantics requires
functional posts to be stated per initial store.) -/
theorem correct_translation {s : StC} (hrange : InRange s)
    (hno : s "x" + s "y" < WORD) :
    quadSem (semLiftC cProg) (semLiftR rProg)
      (fun m m' => m = {s} ∧ m' = {Except.ok s})
      (atom fun t b => b = Except.ok t) := by
  rintro m m' ⟨rfl, rfl⟩
  have h0 : (0 : Int) ≤ s "x" + s "y" := by
    obtain ⟨h1, -, h3, -⟩ := hrange
    omega
  rw [semLiftC_singleton, semLiftR_singleton, errK_ok,
    show semR rProg s = {Except.ok (Function.update s "x" (s "x" + s "y"))} from
      semR_addAssign_ok hno,
    show semC cProg s = {Function.update s "x" ((s "x" + s "y") % WORD)} from rfl,
    Int.emod_eq_of_lt h0 hno]
  exact atom_singleton_iff.mpr rfl

end RelOL
