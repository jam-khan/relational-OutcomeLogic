import RelationalOutcomeLogic.Quadruple
import RelationalOutcomeLogic.Coupling

/-!
# Heterogeneous execution models: a C-like and a Rust-like fragment

The two sides of the relational judgment run under **different** execution
models — different carrier shapes and different effect repertoires:

* **C-like** (`CmdC`): plain powerset carrier `Set StC`; `addAssign` silently
  wraps modulo `WORD`; has nondeterministic `choice`.
* **Rust-like** (`CmdR`): powerset over an error carrier `Set (Except Unit StR)`;
  `addAssign` is checked and panics (`.error ()`) on overflow; deterministic
  (no `choice` — deliberate asymmetry).

Error propagation is confined to `errK`, mechanizing the **monad-law-consistent**
orientation of OL Def. 6.3 / Example 6.4 (the printed Def. 6.3 has the ok/error
cases apparently swapped): errors propagate verbatim, ok-states get the
continuation. `errK_assoc` is the regression lemma — it fails if the cases are
swapped.

Because the assertion/quadruple layer (`RAssn`, `atom`, `oplus`, `quadSem`) is
carrier-polymorphic, this file only supplies semantics; no assertion or rule
definitions are duplicated.
-/

namespace RelOL

attribute [local instance] Classical.propDecidable

/-- C-like program states. -/
abbrev StC := String → Int

/-- Rust-like program states. -/
abbrev StR := String → Int

/-- Machine word bound of the tiny 8-bit machine (keeps examples computable). -/
def WORD : Int := 256

/-- In-range stores for the translation examples. -/
def InRange (s : StC) : Prop :=
  0 ≤ s "x" ∧ s "x" < WORD ∧ 0 ≤ s "y" ∧ s "y" < WORD

/-- Two-variable concrete-state builder for translation counterexamples. -/
def stv (x y : Int) : StC := fun v => if v = "x" then x else if v = "y" then y else 0

@[simp] theorem stv_x (x y : Int) : stv x y "x" = x := by simp [stv]

@[simp] theorem stv_y (x y : Int) : stv x y "y" = y := by simp [stv]

/-! ## The C-like side -/

/-- C-like commands: silent wrap-around addition, nondeterministic choice. -/
inductive CmdC where
  | skip
  | assign (x : String) (e : StC → Int)
  | seq (c₁ c₂ : CmdC)
  | choice (c₁ c₂ : CmdC)
  | ite (b : StC → Prop) (c₁ c₂ : CmdC)
  | while (b : StC → Prop) (c : CmdC)
  | addAssign (x y : String)

/-- C-like semantics: plain powerset; `addAssign` wraps modulo `WORD`, always ok. -/
noncomputable def semC : CmdC → StC → Set StC
  | .skip, s => {s}
  | .assign x e, s => {Function.update s x (e s)}
  | .seq c₁ c₂, s => kleisli (semC c₂) (semC c₁ s)
  | .choice c₁ c₂, s => semC c₁ s ∪ semC c₂ s
  | .ite b c₁ c₂, s => if b s then semC c₁ s else semC c₂ s
  | .while b c, s => loopSem b (semC c) s
  | .addAssign x y, s => {Function.update s x ((s x + s y) % WORD)}

noncomputable def semLiftC (c : CmdC) : Set StC → Set StC := kleisli (semC c)

@[simp] theorem semC_addAssign (x y : String) (s : StC) :
    semC (.addAssign x y) s = {Function.update s x ((s x + s y) % WORD)} := rfl

theorem semC_seq (c₁ c₂ : CmdC) (s : StC) :
    semC (.seq c₁ c₂) s = kleisli (semC c₂) (semC c₁ s) := rfl

theorem semC_choice (c₁ c₂ : CmdC) (s : StC) :
    semC (.choice c₁ c₂) s = semC c₁ s ∪ semC c₂ s := rfl

theorem semC_ite_pos {b : StC → Prop} {s : StC} (h : b s) (c₁ c₂ : CmdC) :
    semC (.ite b c₁ c₂) s = semC c₁ s := by
  simp only [semC, if_pos h]

theorem semC_ite_neg {b : StC → Prop} {s : StC} (h : ¬ b s) (c₁ c₂ : CmdC) :
    semC (.ite b c₁ c₂) s = semC c₂ s := by
  simp only [semC, if_neg h]

theorem semC_while (b : StC → Prop) (c : CmdC) (s : StC) :
    semC (.while b c) s = loopSem b (semC c) s := rfl

/-- The fixpoint unrolling equation for C-like `while`. -/
theorem semC_while_unfold (b : StC → Prop) (c : CmdC) (s : StC) :
    semC (.while b c) s
      = if b s then semLiftC (.while b c) (semC c s) else {s} :=
  loopSem_unfold b (semC c) s

theorem semC_while_pos {b : StC → Prop} {s : StC} (h : b s) (c : CmdC) :
    semC (.while b c) s = semLiftC (.while b c) (semC c s) := by
  rw [semC_while_unfold, if_pos h]

theorem semC_while_neg {b : StC → Prop} {s : StC} (h : ¬ b s) (c : CmdC) :
    semC (.while b c) s = {s} := by
  rw [semC_while_unfold, if_neg h]

theorem loopIter_subset_semC (b : StC → Prop) (c : CmdC) (n : ℕ) (s : StC) :
    loopIter b (semC c) n s ⊆ semC (.while b c) s :=
  loopIter_subset_loopSem b (semC c) n s

/-- Structurally loop-free C-like commands. -/
@[simp] def LoopFreeC : CmdC → Prop
  | .skip => True
  | .assign _ _ => True
  | .seq c₁ c₂ => LoopFreeC c₁ ∧ LoopFreeC c₂
  | .choice c₁ c₂ => LoopFreeC c₁ ∧ LoopFreeC c₂
  | .ite _ c₁ c₂ => LoopFreeC c₁ ∧ LoopFreeC c₂
  | .while _ _ => False
  | .addAssign _ _ => True

theorem semC_nonempty {c : CmdC} (hc : LoopFreeC c) (s : StC) : (semC c s).Nonempty := by
  induction c generalizing s with
  | skip => exact ⟨s, rfl⟩
  | assign x e => exact ⟨_, rfl⟩
  | seq c₁ c₂ ih₁ ih₂ => exact kleisli_nonempty (ih₁ hc.1 s) fun t _ => ih₂ hc.2 t
  | choice c₁ c₂ ih₁ ih₂ => exact (ih₁ hc.1 s).inl
  | ite b c₁ c₂ ih₁ ih₂ =>
    by_cases h : b s
    · rw [semC_ite_pos h]; exact ih₁ hc.1 s
    · rw [semC_ite_neg h]; exact ih₂ hc.2 s
  | «while» b c ih => exact hc.elim
  | addAssign x y => exact ⟨_, rfl⟩

@[simp] theorem mem_semLiftC {c : CmdC} {m : Set StC} {t : StC} :
    t ∈ semLiftC c m ↔ ∃ s ∈ m, t ∈ semC c s := mem_kleisli

@[simp] theorem semLiftC_singleton (c : CmdC) (s : StC) : semLiftC c {s} = semC c s :=
  kleisli_singleton _ _

theorem semLiftC_nonempty {c : CmdC} (hc : LoopFreeC c) {m : Set StC} (hm : m.Nonempty) :
    (semLiftC c m).Nonempty :=
  kleisli_nonempty hm fun s _ => semC_nonempty hc s

/-! ## The error-propagating Kleisli step -/

/-- Error-propagating continuation lift (OL Def. 6.3 in the monad-law-consistent
orientation of Example 6.4): errors propagate verbatim, ok-states continue.
Polymorphic in the error type `ε` (the Rust-like side uses `ε := Unit`; the
compiler case study uses state-carrying exceptions, `ε := State`). -/
def errK {ε σ τ : Type*} (k : σ → Set (Except ε τ)) : Except ε σ → Set (Except ε τ)
  | .error e => {.error e}
  | .ok s => k s

@[simp] theorem errK_ok {ε σ τ : Type*} {k : σ → Set (Except ε τ)} {s : σ} :
    errK k (.ok s) = k s := rfl

@[simp] theorem errK_error {ε σ τ : Type*} {k : σ → Set (Except ε τ)} {e : ε} :
    errK k (.error e) = {Except.error e} := rfl

theorem errK_nonempty {ε σ τ : Type*} {k : σ → Set (Except ε τ)}
    (hk : ∀ s, (k s).Nonempty) (a : Except ε σ) : (errK k a).Nonempty := by
  cases a with
  | error e => exact ⟨.error e, rfl⟩
  | ok s => exact hk s

/-- **Regression lemma for the Def. 6.3 orientation**: the error-propagating
bind is associative. With the printed (swapped) case-split this is false. -/
theorem errK_assoc {ε σ τ υ : Type*} (k₁ : σ → Set (Except ε τ))
    (k₂ : τ → Set (Except ε υ)) (m : Set (Except ε σ)) :
    kleisli (errK k₂) (kleisli (errK k₁) m)
      = kleisli (errK fun s => kleisli (errK k₂) (k₁ s)) m := by
  rw [kleisli_comp]
  congr 1
  funext x
  cases x with
  | error e => simp
  | ok s => rfl

theorem errK_mono {ε σ τ : Type*} {k₁ k₂ : σ → Set (Except ε τ)}
    (h : ∀ s, k₁ s ⊆ k₂ s) (a : Except ε σ) : errK k₁ a ⊆ errK k₂ a := by
  cases a with
  | error e => exact fun x hx => hx
  | ok s => exact h s

/-- `errK` commutes with indexed unions of continuations (the index must be
inhabited so the error case's constant `{.error e}` survives). -/
theorem errK_iUnion {ε σ τ : Type*} {ι : Sort*} [Nonempty ι]
    (k : ι → σ → Set (Except ε τ)) (a : Except ε σ) :
    errK (fun s => ⋃ i, k i s) a = ⋃ i, errK (k i) a := by
  cases a with
  | error e => simp [errK_error, Set.iUnion_const]
  | ok s => simp only [errK_ok]

/-! ## Error-propagating while-loops

The Kleene iterator for loops over an error carrier: the body's outcomes are
`Except`-valued, the continuation re-enters the loop through `errK` (panics
propagate, ok-states iterate), and guard failure exits with `.ok s`. -/

/-- Fuel-indexed truncation of an error-propagating while-loop. -/
noncomputable def errLoopIter {ε σ : Type*} (b : σ → Prop)
    (step : σ → Set (Except ε σ)) : ℕ → σ → Set (Except ε σ)
  | 0, _ => ∅
  | n + 1, s =>
      if b s then kleisli (errK (errLoopIter b step n)) (step s) else {.ok s}

@[simp] theorem errLoopIter_zero {ε σ : Type*} (b : σ → Prop)
    (step : σ → Set (Except ε σ)) (s : σ) : errLoopIter b step 0 s = ∅ := rfl

theorem errLoopIter_succ_pos {ε σ : Type*} {b : σ → Prop} {s : σ} (h : b s)
    (step : σ → Set (Except ε σ)) (n : ℕ) :
    errLoopIter b step (n + 1) s
      = kleisli (errK (errLoopIter b step n)) (step s) := by
  simp only [errLoopIter, if_pos h]

theorem errLoopIter_succ_neg {ε σ : Type*} {b : σ → Prop} {s : σ} (h : ¬ b s)
    (step : σ → Set (Except ε σ)) (n : ℕ) :
    errLoopIter b step (n + 1) s = {.ok s} := by
  simp only [errLoopIter, if_neg h]

/-- Semantics of an error-propagating `while`: union over all fuels. -/
noncomputable def errLoopSem {ε σ : Type*} (b : σ → Prop)
    (step : σ → Set (Except ε σ)) (s : σ) : Set (Except ε σ) :=
  ⋃ n, errLoopIter b step n s

theorem errLoopIter_subset_errLoopSem {ε σ : Type*} (b : σ → Prop)
    (step : σ → Set (Except ε σ)) (n : ℕ) (s : σ) :
    errLoopIter b step n s ⊆ errLoopSem b step s :=
  Set.subset_iUnion (fun n => errLoopIter b step n s) n

/-- The fixpoint unrolling equation for error-propagating loops. -/
theorem errLoopSem_unfold {ε σ : Type*} (b : σ → Prop)
    (step : σ → Set (Except ε σ)) (s : σ) :
    errLoopSem b step s
      = if b s then kleisli (errK (errLoopSem b step)) (step s) else {.ok s} := by
  by_cases h : b s
  · rw [if_pos h]
    unfold errLoopSem
    have : (errK fun t => ⋃ n, errLoopIter b step n t)
        = fun a => ⋃ n, errK (errLoopIter b step n) a := by
      funext a; exact errK_iUnion _ a
    rw [this, kleisli_iUnion_fun]
    ext t
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, ht⟩
      cases n with
      | zero => simp at ht
      | succ n => rw [errLoopIter_succ_pos h] at ht; exact ⟨n, ht⟩
    · rintro ⟨n, ht⟩
      exact ⟨n + 1, by rw [errLoopIter_succ_pos h]; exact ht⟩
  · rw [if_neg h]
    unfold errLoopSem
    ext t
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, ht⟩
      cases n with
      | zero => simp at ht
      | succ n => rwa [errLoopIter_succ_neg h] at ht
    · exact fun ht => ⟨1, by rwa [errLoopIter_succ_neg h]⟩

theorem errLoopSem_pos {ε σ : Type*} {b : σ → Prop} {s : σ} (h : b s)
    (step : σ → Set (Except ε σ)) :
    errLoopSem b step s = kleisli (errK (errLoopSem b step)) (step s) := by
  rw [errLoopSem_unfold, if_pos h]

theorem errLoopSem_neg {ε σ : Type*} {b : σ → Prop} {s : σ} (h : ¬ b s)
    (step : σ → Set (Except ε σ)) :
    errLoopSem b step s = {.ok s} := by
  rw [errLoopSem_unfold, if_neg h]

/-! ## The Rust-like side -/

/-- Rust-like commands: checked addition, deterministic (no choice). -/
inductive CmdR where
  | skip
  | assign (x : String) (e : StR → Int)
  | seq (c₁ c₂ : CmdR)
  | ite (b : StR → Prop) (c₁ c₂ : CmdR)
  | while (b : StR → Prop) (c : CmdR)
  | addAssign (x y : String)

/-- Rust-like semantics into the error carrier: checked `addAssign` panics on
overflow; loops iterate through `errK`, so a panic mid-loop aborts the loop. -/
noncomputable def semR : CmdR → StR → Set (Except Unit StR)
  | .skip, s => {.ok s}
  | .assign x e, s => {.ok (Function.update s x (e s))}
  | .seq c₁ c₂, s => kleisli (errK (semR c₂)) (semR c₁ s)
  | .ite b c₁ c₂, s => if b s then semR c₁ s else semR c₂ s
  | .while b c, s => errLoopSem b (semR c) s
  | .addAssign x y, s =>
      if s x + s y < WORD then {.ok (Function.update s x (s x + s y))} else {.error ()}

noncomputable def semLiftR (c : CmdR) : Set (Except Unit StR) → Set (Except Unit StR) :=
  kleisli (errK (semR c))

theorem semR_addAssign_ok {x y : String} {s : StR} (h : s x + s y < WORD) :
    semR (.addAssign x y) s = {.ok (Function.update s x (s x + s y))} := by
  simp only [semR, if_pos h]

theorem semR_addAssign_err {x y : String} {s : StR} (h : ¬ s x + s y < WORD) :
    semR (.addAssign x y) s = {.error ()} := by
  simp only [semR, if_neg h]

theorem semR_seq (c₁ c₂ : CmdR) (s : StR) :
    semR (.seq c₁ c₂) s = kleisli (errK (semR c₂)) (semR c₁ s) := rfl

theorem semR_ite_pos {b : StR → Prop} {s : StR} (h : b s) (c₁ c₂ : CmdR) :
    semR (.ite b c₁ c₂) s = semR c₁ s := by
  simp only [semR, if_pos h]

theorem semR_ite_neg {b : StR → Prop} {s : StR} (h : ¬ b s) (c₁ c₂ : CmdR) :
    semR (.ite b c₁ c₂) s = semR c₂ s := by
  simp only [semR, if_neg h]

theorem semR_while (b : StR → Prop) (c : CmdR) (s : StR) :
    semR (.while b c) s = errLoopSem b (semR c) s := rfl

/-- The fixpoint unrolling equation for Rust-like `while`. -/
theorem semR_while_unfold (b : StR → Prop) (c : CmdR) (s : StR) :
    semR (.while b c) s
      = if b s then semLiftR (.while b c) (semR c s) else {.ok s} :=
  errLoopSem_unfold b (semR c) s

theorem semR_while_pos {b : StR → Prop} {s : StR} (h : b s) (c : CmdR) :
    semR (.while b c) s = semLiftR (.while b c) (semR c s) := by
  rw [semR_while_unfold, if_pos h]

theorem semR_while_neg {b : StR → Prop} {s : StR} (h : ¬ b s) (c : CmdR) :
    semR (.while b c) s = {.ok s} := by
  rw [semR_while_unfold, if_neg h]

theorem errLoopIter_subset_semR (b : StR → Prop) (c : CmdR) (n : ℕ) (s : StR) :
    errLoopIter b (semR c) n s ⊆ semR (.while b c) s :=
  errLoopIter_subset_errLoopSem b (semR c) n s

/-- Structurally loop-free Rust-like commands. -/
@[simp] def LoopFreeR : CmdR → Prop
  | .skip => True
  | .assign _ _ => True
  | .seq c₁ c₂ => LoopFreeR c₁ ∧ LoopFreeR c₂
  | .ite _ c₁ c₂ => LoopFreeR c₁ ∧ LoopFreeR c₂
  | .while _ _ => False
  | .addAssign _ _ => True

theorem semR_nonempty {c : CmdR} (hc : LoopFreeR c) (s : StR) : (semR c s).Nonempty := by
  induction c generalizing s with
  | skip => exact ⟨_, rfl⟩
  | assign x e => exact ⟨_, rfl⟩
  | seq c₁ c₂ ih₁ ih₂ =>
    exact kleisli_nonempty (ih₁ hc.1 s) fun a _ => errK_nonempty (ih₂ hc.2) a
  | ite b c₁ c₂ ih₁ ih₂ =>
    by_cases h : b s
    · rw [semR_ite_pos h]; exact ih₁ hc.1 s
    · rw [semR_ite_neg h]; exact ih₂ hc.2 s
  | «while» b c ih => exact hc.elim
  | addAssign x y =>
    by_cases h : s x + s y < WORD
    · rw [semR_addAssign_ok h]; exact ⟨_, rfl⟩
    · rw [semR_addAssign_err h]; exact ⟨_, rfl⟩

@[simp] theorem mem_semLiftR {c : CmdR} {m : Set (Except Unit StR)} {b : Except Unit StR} :
    b ∈ semLiftR c m ↔ ∃ a ∈ m, b ∈ errK (semR c) a := mem_kleisli

@[simp] theorem semLiftR_singleton (c : CmdR) (a : Except Unit StR) :
    semLiftR c {a} = errK (semR c) a :=
  kleisli_singleton _ _

theorem semLiftR_nonempty {c : CmdR} (hc : LoopFreeR c) {m : Set (Except Unit StR)}
    (hm : m.Nonempty) : (semLiftR c m).Nonempty :=
  kleisli_nonempty hm fun a _ => errK_nonempty (semR_nonempty hc) a

/-! ## The heterogeneous quadruple -/

/-- The heterogeneous RelOL quadruple: C-like on the left, Rust-like on the
right — an *instantiation* of the polymorphic `quadSem`, not a new definition. -/
def quadH (R : RAssn StC (Except Unit StR)) (c : CmdC) (c' : CmdR)
    (S : RAssn StC (Except Unit StR)) : Prop :=
  quadSem (semLiftC c) (semLiftR c') R S

/-! ## Heterogeneous atomic axioms

The named rules for the primitive statements both sides share. The
`ok`-correspondence precondition `a = .ok s` couples each Rust-like outcome to
the C-like state it mirrors; the postconditions certify the correspondence
(ok case), or its collapse into the panic (overflow case). -/

@[simp] theorem semC_skip (s : StC) : semC .skip s = {s} := rfl

@[simp] theorem semC_assign (x : String) (e : StC → Int) (s : StC) :
    semC (.assign x e) s = {Function.update s x (e s)} := rfl

@[simp] theorem semR_skip (s : StR) : semR .skip s = {.ok s} := rfl

@[simp] theorem semR_assign (x : String) (e : StR → Int) (s : StR) :
    semR (.assign x e) s = {.ok (Function.update s x (e s))} := rfl

theorem quadH_skip :
    quadH (atom fun s a => a = .ok s) .skip .skip (atom fun t b => b = .ok t) := by
  rintro m m' ⟨hm, hm', hall⟩
  refine ⟨semLiftC_nonempty (by simp) hm, semLiftR_nonempty (by simp) hm', ?_⟩
  rintro t ht b hb
  obtain ⟨s, hs, ht⟩ := mem_semLiftC.mp ht
  obtain ⟨a, ha, hb⟩ := mem_semLiftR.mp hb
  obtain rfl := hall s hs a ha
  simp only [errK_ok, semR_skip, Set.mem_singleton_iff] at hb
  simp only [semC_skip, Set.mem_singleton_iff] at ht
  simp [hb, ht]

/-- Synchronized assignment across the two execution models. -/
theorem quadH_assign (x : String) (e : StC → Int) :
    quadH (atom fun s a => a = .ok s) (.assign x e) (.assign x e)
      (atom fun t b => b = .ok t) := by
  rintro m m' ⟨hm, hm', hall⟩
  refine ⟨semLiftC_nonempty (by simp) hm, semLiftR_nonempty (by simp) hm', ?_⟩
  rintro t ht b hb
  obtain ⟨s, hs, ht⟩ := mem_semLiftC.mp ht
  obtain ⟨a, ha, hb⟩ := mem_semLiftR.mp hb
  obtain rfl := hall s hs a ha
  simp only [errK_ok, semR_assign, Set.mem_singleton_iff] at hb
  simp only [semC_assign, Set.mem_singleton_iff] at ht
  simp [hb, ht]

/-- Checked and wrapping addition agree below the word bound: the wrap is the
identity, so the ok-correspondence is preserved. -/
theorem quadH_addAssign_ok (x y : String) :
    quadH (atom fun s a => a = .ok s ∧ 0 ≤ s x + s y ∧ s x + s y < WORD)
      (.addAssign x y) (.addAssign x y) (atom fun t b => b = .ok t) := by
  rintro m m' ⟨hm, hm', hall⟩
  refine ⟨semLiftC_nonempty (by simp) hm, semLiftR_nonempty (by simp) hm', ?_⟩
  rintro t ht b hb
  obtain ⟨s, hs, ht⟩ := mem_semLiftC.mp ht
  obtain ⟨a, ha, hb⟩ := mem_semLiftR.mp hb
  obtain ⟨rfl, h0, hlt⟩ := hall s hs a ha
  rw [errK_ok, semR_addAssign_ok hlt, Set.mem_singleton_iff] at hb
  rw [semC_addAssign, Set.mem_singleton_iff, Int.emod_eq_of_lt h0 hlt] at ht
  simp [hb, ht]

/-- On overflow the Rust-like side's entire outcome set is the panic, whatever
the C-like side wraps to. -/
theorem quadH_addAssign_panic (x y : String) :
    quadH (atom fun s a => a = .ok s ∧ WORD ≤ s x + s y)
      (.addAssign x y) (.addAssign x y) (atom fun _ b => b = .error ()) := by
  rintro m m' ⟨hm, hm', hall⟩
  refine ⟨semLiftC_nonempty (by simp) hm, semLiftR_nonempty (by simp) hm', ?_⟩
  rintro t _ b hb
  obtain ⟨a, ha, hb⟩ := mem_semLiftR.mp hb
  obtain ⟨s, hs⟩ := hm
  obtain ⟨rfl, hge⟩ := hall s hs a ha
  rw [errK_ok, semR_addAssign_err (by omega), Set.mem_singleton_iff] at hb
  exact hb

/-! ## Coupling layer

The heterogeneous coupling axioms ride on `couple_bind` exactly like the
homogeneous rules — and get *shorter* than their `atom` counterparts, because
the pairing replaces the separate nonemptiness bookkeeping. The `a = .ok s`
conjunct of the `atom` preconditions was always a hand-rolled coupling; here
it becomes the coupling relation itself. -/

/-- Per-state couplings lift to heterogeneous quadruples over arbitrary
`couple` preconditions. -/
theorem quadH_couple_lift {r r' : StC → Except Unit StR → Prop}
    {c : CmdC} {c' : CmdR}
    (h : ∀ s a, r s a → couple r' (semC c s) (errK (semR c') a)) :
    quadH (couple r) c c' (couple r') :=
  fun _ _ hm => couple_bind hm h

theorem quadH_skip_couple :
    quadH (couple fun s a => a = .ok s) .skip .skip
      (couple fun t b => b = .ok t) :=
  quadH_couple_lift fun s a ha => by
    subst ha
    rw [errK_ok]
    exact couple_singleton_iff.mpr rfl

theorem quadH_assign_couple (x : String) (e : StC → Int) :
    quadH (couple fun s a => a = .ok s) (.assign x e) (.assign x e)
      (couple fun t b => b = .ok t) :=
  quadH_couple_lift fun s a ha => by
    subst ha
    rw [errK_ok]
    exact couple_singleton_iff.mpr rfl

theorem quadH_addAssign_ok_couple (x y : String) :
    quadH (couple fun s a => a = .ok s ∧ 0 ≤ s x + s y ∧ s x + s y < WORD)
      (.addAssign x y) (.addAssign x y) (couple fun t b => b = .ok t) :=
  quadH_couple_lift fun s a ⟨ha, h0, hlt⟩ => by
    subst ha
    rw [errK_ok, semR_addAssign_ok hlt, semC_addAssign, Int.emod_eq_of_lt h0 hlt]
    exact couple_singleton_iff.mpr rfl

theorem quadH_addAssign_panic_couple (x y : String) :
    quadH (couple fun s a => a = .ok s ∧ WORD ≤ s x + s y)
      (.addAssign x y) (.addAssign x y) (couple fun _ b => b = .error ()) :=
  quadH_couple_lift fun s a ⟨ha, hge⟩ => by
    subst ha
    rw [errK_ok, semR_addAssign_err (by omega), semC_addAssign]
    exact couple_singleton_iff.mpr rfl

/-- **Coupled heterogeneous loops** (ok-preserving case): a plain loop on the
C-like side couples with an error-propagating loop on the Rust-like side,
provided the coupled body never panics. Panic-crossing loops are handled by
exhaustive certificates instead (`translation_loop_bug`). -/
theorem loopSem_errLoopSem_couple {ε σ : Type*} {r : StC → σ → Prop}
    {b : StC → Prop} {b' : σ → Prop}
    {step : StC → Set StC} {step' : σ → Set (Except ε σ)}
    (hguard : ∀ x u, r x u → (b x ↔ b' u))
    (hbody : ∀ x u, r x u → b x → b' u →
      couple (fun t a => ∃ v, a = .ok v ∧ r t v) (step x) (step' u)) :
    ∀ x u, r x u →
      couple (fun t a => ∃ v, a = .ok v ∧ r t v ∧ ¬ b t ∧ ¬ b' v)
        (loopSem b step x) (errLoopSem b' step' u) := by
  have auxL : ∀ n x u, r x u → ∀ t ∈ loopIter b step n x,
      ∃ a ∈ errLoopSem b' step' u, ∃ v, a = .ok v ∧ r t v ∧ ¬ b t ∧ ¬ b' v := by
    intro n
    induction n with
    | zero =>
      intro x u _ t ht
      rw [loopIter_zero] at ht
      exact absurd ht (Set.notMem_empty t)
    | succ n ih =>
      intro x u hr t ht
      by_cases hb : b x
      · have hb' : b' u := (hguard x u hr).mp hb
        rw [loopIter_succ_pos hb] at ht
        obtain ⟨w, hw, ht⟩ := mem_kleisli.mp ht
        obtain ⟨a₁, ha₁, v, rfl, hrv⟩ := (hbody x u hr hb hb').1 w hw
        obtain ⟨a, ha, hprop⟩ := ih w v hrv t ht
        refine ⟨a, ?_, hprop⟩
        rw [errLoopSem_pos hb']
        exact mem_kleisli.mpr ⟨.ok v, ha₁, by rwa [errK_ok]⟩
      · have hb' : ¬ b' u := fun h => hb ((hguard x u hr).mpr h)
        rw [loopIter_succ_neg hb, Set.mem_singleton_iff] at ht
        subst ht
        refine ⟨.ok u, ?_, u, rfl, hr, hb, hb'⟩
        rw [errLoopSem_neg hb']
        exact Set.mem_singleton _
  have auxR : ∀ n x u, r x u → ∀ a ∈ errLoopIter b' step' n u,
      ∃ t ∈ loopSem b step x, ∃ v, a = .ok v ∧ r t v ∧ ¬ b t ∧ ¬ b' v := by
    intro n
    induction n with
    | zero =>
      intro x u _ a ha
      rw [errLoopIter_zero] at ha
      exact absurd ha (Set.notMem_empty a)
    | succ n ih =>
      intro x u hr a ha
      by_cases hb' : b' u
      · have hb : b x := (hguard x u hr).mpr hb'
        rw [errLoopIter_succ_pos hb'] at ha
        obtain ⟨a₁, ha₁, ha⟩ := mem_kleisli.mp ha
        obtain ⟨w, hw, v, rfl, hrv⟩ := (hbody x u hr hb hb').2 a₁ ha₁
        rw [errK_ok] at ha
        obtain ⟨t, ht, hprop⟩ := ih w v hrv a ha
        refine ⟨t, ?_, hprop⟩
        rw [loopSem_unfold, if_pos hb]
        exact mem_kleisli.mpr ⟨w, hw, ht⟩
      · have hb : ¬ b x := fun h => hb' ((hguard x u hr).mp h)
        rw [errLoopIter_succ_neg hb', Set.mem_singleton_iff] at ha
        subst ha
        refine ⟨x, ?_, u, rfl, hr, hb, hb'⟩
        rw [loopSem_unfold, if_neg hb]
        exact Set.mem_singleton x
  intro x u hr
  constructor
  · intro t ht
    obtain ⟨n, ht⟩ := Set.mem_iUnion.mp ht
    obtain ⟨a, ha, hprop⟩ := auxL n x u hr t ht
    exact ⟨a, ha, hprop⟩
  · intro a ha
    obtain ⟨n, ha⟩ := Set.mem_iUnion.mp ha
    obtain ⟨t, ht, hprop⟩ := auxR n x u hr a ha
    exact ⟨t, ht, hprop⟩

/-- Coupled While across the two execution models, entered via `ok`. -/
theorem quadH_while_couple {r : StC → StR → Prop} {b : StC → Prop}
    {b' : StR → Prop} {c : CmdC} {c' : CmdR}
    (hguard : ∀ s u, r s u → (b s ↔ b' u))
    (hbody : ∀ s u, r s u → b s → b' u →
      couple (fun t a => ∃ v, a = .ok v ∧ r t v) (semC c s) (semR c' u)) :
    quadH (couple fun s a => ∃ u, a = .ok u ∧ r s u) (.while b c) (.while b' c')
      (couple fun t a => ∃ v, a = .ok v ∧ r t v ∧ ¬ b t ∧ ¬ b' v) :=
  quadH_couple_lift fun s a ⟨u, ha, hr⟩ => by
    subst ha
    rw [errK_ok, semC_while, semR_while]
    exact loopSem_errLoopSem_couple hguard hbody s u hr

end RelOL
