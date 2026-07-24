# Relational Outcome Logic — Project Handoff Document

Context: this document summarizes a design discussion for a new research project, **Relational Outcome Logic (RelOL)**, intended to produce (1) a Lean 4 mechanization and (2) an extended abstract with two mechanized examples.

---

## 1. Background: Outcome Logic (OL)

Base paper: *Outcome Logic: A Unifying Foundation for Correctness and Incorrectness Reasoning*, Zilberstein, Dreyer, Silva, OOPSLA 2023.

Key concepts the project builds on:

- **Outcome monoid / execution model**: a monad M on Set (sequencing via bind/unit) plus a partial commutative monoid (PCM) structure ⟨MΣ, ⋄, ∅⟩ on MΣ (branching via ⋄, divergence via ∅), with compatibility laws: `bind(m₁ ⋄ m₂, k) = bind(m₁,k) ⋄ bind(m₂,k)` and `bind(∅,k) = ∅`. Instances: powerset (Set Σ, ∪, ∅) for nondeterminism; subdistributions (DΣ, +, zero-dist, partial when mass > 1) for probability; `Set (E + Σ)` for nondeterminism + errors (OL §6.3).
- **Assertions are predicates over MΣ**, not over single states. Atomic satisfaction in the powerset instance: `S ⊨ P ⟺ S ≠ ∅ ∧ ∀σ ∈ S. σ ⊨ P`. The nonemptiness clause bakes **reachability** into satisfaction.
- **Outcome conjunction ⊕**: `m ⊨ P ⊕ Q ⟺ ∃m₁ m₂. m = m₁ ⋄ m₂ ∧ m₁ ⊨ P ∧ m₂ ⊨ Q`. Unlike ∨, ⊕ forces both outcomes to actually exist (nonempty pieces). Without a trailing ⊤ the split is exhaustive (Hoare-style total coverage); with `⊕ ⊤` you get under-approximation (IL-style dropping of outcomes).
- **OL triple** keeps Hoare's forward shape: `⊨ ⟨P⟩ C ⟨Q⟩ ⟺ ∀m. m ⊨ P ⟹ ⟦C⟧†(m) ⊨ Q`, where ⟦C⟧† is the Kleisli extension (semLift). Reachability comes from the assertion logic, not from IL's backward quantifier flip. Key separation: reachability and under-approximation are independent, composable mechanisms.
- **Falsification (Thm 5.1) / Principle of Denial**: any untrue OL spec is disprovable by another OL triple → correctness and incorrectness in one logic.

## 2. The Gap RelOL Fills

- **Hyper Hoare Logic (HHL, Dardinier & Müller)** already covers hyperproperties and relational reasoning over the *homogeneous* powerset instance (second-order assertions over sets of states; relational-two-programs handled by self-composition/renaming encoding). Do NOT pitch "relational hyperproperties" — that space is used up, plausibly why the OL authors never did relational OL.
- **Genuinely open** (the project's claims):
  1. **Heterogeneous semantics**: the two sides of a relational judgment running under *different monads/execution models* (e.g., C-like: `Set (Except UB Σ_C)` vs Rust-like: deterministic with panic). HHL's encoding requires one language, one semantic domain; heterogeneity there needs an ad-hoc unverified superlanguage embedding. RelOL is native and compositional.
  2. **Monadic generality**: relational OL over distributions → relational probabilistic incorrectness (toward certified DP-violation witnesses). Neither HHL nor unary OL reaches this.
  3. **Structured assertions**: ⊕-based quadruples are weaker than HHL's second-order logic but structured (BI-style), better suited to eventual automation/symbolic execution.
- **Murray's under-approximate relational logic** (insecurity quadruples): IL-shaped, under-approximate-only, cannot state noninterference itself. RelOL states both NI (no ⊤) and its violation (⊕ ⊤) in one quadruple form.
- Positioning sentence: "the homogeneous relational case is settled by HHL; the heterogeneous and probabilistic cases are not — here is a prototype showing the heterogeneous one is cheap to set up and immediately useful."

## 3. The Core Definitions (product model, homogeneous first)

Model: pairs of outcome-monoid elements. Quadruple keeps Hoare's forward shape:

```
⊨ ⟨R⟩ c, c' ⟨S⟩  ⟺  ∀(m, m'). (m,m') ⊨ R ⟹ (⟦c⟧†(m), ⟦c'⟧†(m')) ⊨ S
```

Relational atomic assertions (powerset instance, doubled nonemptiness = joint reachability):

```
(S, S') ⊨ r  ⟺  S ≠ ∅ ∧ S' ≠ ∅ ∧ ∀σ ∈ S, σ' ∈ S'. r(σ, σ')
```

Pairwise outcome conjunction (both sides split in sync):

```
(m, m') ⊨ P ⊕ Q  ⟺  ∃ m₁ m₂ m₁' m₂'. m = m₁ ⋄ m₂ ∧ m' = m₁' ⋄ m₂' ∧ (m₁,m₁') ⊨ P ∧ (m₂,m₂') ⊨ Q
```

Design decisions (all "smallest viable"):
- **Product model**, not coupling model — sufficient for the examples; couplings are future work.
- **Shallow assertion embedding** (`RAssn := Set State → Set State → Prop`) for the prototype. Deep embedding (BI syntax + satisfaction) is required later for syntactic falsification theorems (structural induction on assertion syntax, cf. OL Lemma D.3), but not for the abstract.
- **Homogeneous first, heterogeneous as a Phase-4 refactor** (two state types, two `Outc`/`semLift`s). Premature generalization adds typeclass noise before knowing which lemmas matter.
- **No loops initially** (bounded/no iteration); lfp machinery deferred.
- ⊕ uses overlapping-friendly ∪ (no disjointness side condition) — matches OL and simplifies proofs.

## 4. Lean 4 Skeleton — Homogeneous (Phase 2)

```lean
abbrev State := String → Int

inductive Cmd where
  | skip
  | assign (x : String) (e : State → Int)
  | seq (c₁ c₂ : Cmd)
  | ite (b : State → Bool) (c₁ c₂ : Cmd)
  | choice (c₁ c₂ : Cmd)

def sem : Cmd → State → Set State
  | .skip,        s => {s}
  | .assign x e,  s => {Function.update s x (e s)}
  | .seq c₁ c₂,   s => ⋃ t ∈ sem c₁ s, sem c₂ t
  | .ite b c₁ c₂, s => if b s then sem c₁ s else sem c₂ s
  | .choice c₁ c₂, s => sem c₁ s ∪ sem c₂ s

def semLift (c : Cmd) (m : Set State) : Set State := ⋃ s ∈ m, sem c s

abbrev RAssn := Set State → Set State → Prop

def atom (r : State → State → Prop) : RAssn := fun m m' =>
  m.Nonempty ∧ m'.Nonempty ∧ ∀ s ∈ m, ∀ s' ∈ m', r s s'

def oplus (P Q : RAssn) : RAssn := fun m m' =>
  ∃ m₁ m₂ m₁' m₂', m = m₁ ∪ m₂ ∧ m' = m₁' ∪ m₂' ∧ P m₁ m₁' ∧ Q m₂ m₂'

def top : RAssn := fun _ _ => True

def quad (R : RAssn) (c c' : Cmd) (S : RAssn) : Prop :=
  ∀ m m', R m m' → S (semLift c m) (semLift c' m')

notation:50 "⦃" R "⦄ " c ", " c' " ⦃" S "⦄" => quad R c c' S
```

### Case study 1: Noninterference violation (Murray's example)

```lean
def prog : Cmd := .ite (fun s => s "x" > 0)
  (.assign "low" fun _ => 1) (.assign "low" fun _ => 0)

def L : State → State → Prop := fun s s' => s "low" = s' "low"

theorem insecure :
    ⦃ atom (fun s s' => L s s' ∧ s "x" > 0 ∧ s' "x" ≤ 0) ⦄
    prog, prog
    ⦃ oplus (atom fun s s' => s "low" = 1 ∧ s' "low" = 0) top ⦄ := by
  -- precondition forces each side down a different branch;
  -- semLift computes to singletons; pick trivial split m ∪ ∅.
  sorry
```

Plus corollary `insecurity_implies_not_NI` (the quadruple + `(low=1 ∧ low'=0) → ¬L` refutes noninterference) — a relational Principle of Denial instance. Contrast: same quadruple form without ⊤, `⦃L⦄ c, c ⦃L⦄`, *states* NI — one logic, both directions (Murray's logic cannot state NI).

## 5. Lean 4 Skeleton — Heterogeneous (Phase 4)

Key move: the two sides carry different state types AND different monads. C-like wraps on overflow silently; Rust-like panics.

```lean
abbrev Val := Int
def WORD : Int := 256  -- tiny 8-bit machine keeps examples computable

abbrev Outc (σ : Type) := Set (Except Unit σ)  -- powerset ∘ error monad (OL §6.3)

def liftE {σ : Type} (f : σ → Outc σ) (m : Outc σ) : Outc σ :=
  ⋃ x ∈ m, match x with
    | .error e => {.error e}   -- error propagation
    | .ok s    => f s

-- C-like: addAssign wraps: x := (x + y) % WORD, always ok. Has nondet `choice`.
-- Rust-like: addAssign checked: ok if x + y < WORD else {.error ()} (panic). Deterministic (no choice — deliberate asymmetry).
-- Both: skip, assign, seq. Semantics semC : CmdC → StC → Outc StC, semR : CmdR → StR → Outc StR.

abbrev RAssn := Outc StC → Outc StR → Prop  -- heterogeneous relational assertions

def atom (r : Except Unit StC → Except Unit StR → Prop) : RAssn :=
  fun m m' => m.Nonempty ∧ m'.Nonempty ∧ ∀ x ∈ m, ∀ y ∈ m', r x y

def quad (R : RAssn) (c : CmdC) (c' : CmdR) (S : RAssn) : Prop :=
  ∀ m m', R m m' → S (semLiftC c m) (semLiftR c' m')
```

### Case study 2: Certified translation bug (overflow)

```lean
def cProg : CmdC := .addAssign "x" "y"
def rProg : CmdR := .addAssign "x" "y"

def preOvf : RAssn := atom fun a b =>
  ∃ s, a = .ok s ∧ b = .ok s ∧ s "x" + s "y" ≥ WORD
       ∧ 0 ≤ s "x" ∧ s "x" < WORD ∧ 0 ≤ s "y" ∧ s "y" < WORD

theorem translation_bug :
    ⦃ preOvf ⦄ cProg ~ rProg
    ⦃ oplus (atom fun a b => (∃ s, a = .ok s) ∧ b = .error ()) rtop ⦄ := by
  sorry  -- C side computes to ok-singleton (wrapped), Rust side to {.error ()}; split (m, ∅)
```

Plus: define refinement as the correctness quadruple (every C `ok` outcome matched by a Rust `ok` with related states), prove `translation_bug → ¬refines cProg rProg` — certified counterexample to refinement. Also verify one *correct* translation with the same definitions (two-row contrast table for the paper).

### Case study 3 (future work, one sentence in abstract): compiler-pass incorrectness

Target = subset of source (lowering passes) ⇒ one syntax/semantics mechanized, quadruple relates program to its lowered form. Correctness direction = per-pass translation validation, composable via Seq. Incorrectness direction = certified miscompilation witness (what Csmith produces empirically, as a theorem). Best pass choice: exceptions-to-error-codes (effect-changing, so monad-crossing, demonstrating heterogeneity; classical; realistic bug mode = dropped/misrouted error). Pitch as "certified translation bugs per-pass," NOT "compiler verification" (avoid CompCert comparison; nearest neighbor is Alive2 — differentiate via compositionality + kernel-checked certificates vs whole-function SMT).

## 6. Rules / Metatheory Plan

Rules to prove sound (as lemmas about `quad`): **Conseq, Seq** (via `semLift (seq c₁ c₂) m = semLift c₂ (semLift c₁ m)`), **Sym** (flip the pair — trivial in symmetric product model), **Choice** (yields ⊕), **Split** (⊕ on both sides), derived **UnderApprox** (`quad R c c' S → quad R (choice c d) c' (oplus S top)` — the OL-vs-IL selling point).

**Split is the load-bearing wall**: `quad R₁ c c' S₁ → quad R₂ c c' S₂ → quad (oplus R₁ R₂) c c' (oplus S₁ S₂)`. The relational analogue of OL Lemma D.3 must split two elements simultaneously; the cross-product in atoms (∀σ,σ') makes Split/Frame interaction subtler. **Attempt Split's statement immediately after defining oplus, before examples** — if it fights, the fix is in how the two sides' splits correlate, and that fight IS the research content. Record what breaks.

Metatheory probes, in order:
1. **Relational Principle of Denial** (semantic falsification, easy direction) — ~10 lines, Thm 5.1's argument verbatim. If hard, `quad` is misdefined.
2. Rule soundness (order above).
3. **Relational falsifying-assertion lemma** (analogue of OL Lemma 5.5): characterize exactly how `(S,S') ⊭ Q₁ ⊕ … ⊕ Qₙ`. Expect MORE failure modes than unary OL's three (each side fails independently). Clean enumeration = theorem for abstract; ugly = finding anyway.

Note precedent: OL's own Thm 5.1 is purely semantic (no rules/syntax needed) — semantic-level results are a respectable abstract-level contribution. Rules become non-optional only if claiming *compositional* reasoning.

## 7. Phased Execution Plan

- **Phase 0** (half day): Lake project + Mathlib. Files: `Semantics.lean, Assertions.lean, Quadruple.lean, Rules.lean, Examples/NI.lean, Examples/Translation.lean`. Rule: no `sorry` survives a commit to Semantics/Assertions.
- **Phase 1** (2–3 days): **unary** OL first (powerset instance, exactly per the paper). Sanity theorems: malloc-style `⟨true⟩ C ⟨ok ⊕ er⟩`; dropping-outcomes lemma (`oplus P Q → oplus P top`, OL Lemma B.1); one direction of Thm 4.5 subsumption for a concrete program. Debugs the bookkeeping in isolation before doubling it.
- **Phase 2** (1 week): relational product model (homogeneous), probe Split immediately, close NI example + `¬NI` corollary. **This is the first complete artifact.**
- **Phase 3** (1–2 weeks): metatheory probes (Denial → rules → falsification enumeration).
- **Phase 4** (1 week): heterogeneous refactor (parametrize over two execution models — Lean structure `ExecModel` = OL Def 3.3), translation example + `¬refines`. Generalize LAST, not first.
- Total: 4–6 weeks part-time. Working style: statement-first (typecheck with sorry, then prove); keep `Notes.md` of every design choice and every proof that fought back (becomes the abstract's technical section almost verbatim); `simp`/`aesop` for example computations, hand proofs for metatheory; no custom tactics yet (defer the proof-producing-executor direction until the metatheory is stable).

## 8. Extended Abstract Plan

Target: 2.5–3 pages, semantic-level (no full rule system needed; optionally prove Seq+Split quietly and say "compositional proof system under development; core rules verified").

Structure:
1. **Problem**: under-approximate logics are unary (OL) or IL-shaped/single-effect (Murray); relational properties (security, refinement) need execution pairs; translation validation needs pairs across *different semantics*.
2. **Quadruple** (half page): definitions; the carrying sentence: *the same quadruple form states the property (no ⊤) and certifies its violation (with ⊕ ⊤)*. One line on heterogeneity.
3. **Example 1**: insecurity quadruple + `¬NI` corollary; one-sentence contrast with Murray.
4. **Example 2**: translation bug + `¬refines`; one sentence on why existing translation validation can't produce this artifact.
5. **Status & roadmap** (3 sentences): mechanized in Lean 4, LOC, sorry-free (make true first); future: coupling model, probabilistic instance (→ DP violations), syntactic falsification, proof-producing tactic. Explicitly name open problems.
6. **Related work**: OL, Murray, HHL (spend the sentences here — state the self-composition encoding explicitly and why it fails for heterogeneity: per-pair encodings, no errors, no probabilities, encoding in TCB), Alive2/translation validation, relational refinement types (rF*, Fuzz — they prove DP, none refute with certified witness; RelOL over distributions is that line's refutation-side complement).

Venues for the abstract: LOLA, HOPE, POPL/ETAPS SRC, Dutch FM community events. Do NOT claim "mechanized" until both example theorems are sorry-free.

## 9. Adjacent Research Directions (secondary to the anchor project)

1. **Relational Outcome Logic** (this project — the anchor).
2. **OL for higher-order programs** — one sentence only; VERIFY novelty first (OL follow-up literature moves fast; Zilberstein successors + Iris-adjacent work may have claimed it).
3. **Outcome types** — type-level analogue of ⊕: refinement types are Hoare-shaped (over-approximate, can't express reachability — a type `{v | v>0 ∨ v=-1}` never guarantees −1 occurs); "outcome-structured / incorrectness typing" appears open but VERIFY ("incorrectness typing", "under-approximate types" literature search before naming it).

Long-term architecture (not for the abstract): proof-producing RelOL symbolic executor whose entailment side conditions are discharged via Flex-style certified CHC solving — same Lean host, kernel-only TCB, no SMT trust.

## 10. Open Verification Items (technical due diligence before any document)

- Re-verify HHL's published claims (expressiveness scope, whether any heterogeneous or probabilistic extension has since appeared).
- Check the recent OL follow-up literature (Zilberstein successors, demonic/weighted OL, Iris-adjacent work) for any relational or higher-order OL development.
- Accumulated framing warnings: don't fight HHL on homogeneous relational hyperproperties; don't claim "C and Rust" (say "modeling the semantic gap" with ~5-construct fragments); don't say "compiler verification" (say "certified translation bugs, per-pass"); flag the refinement-types vs program-refinement terminology collision once; scope case study 3 to a single effect-changing pass.