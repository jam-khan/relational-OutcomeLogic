import RelationalOutcomeLogic.Quadruple

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
  | addAssign (x y : String)

/-- C-like semantics: plain powerset; `addAssign` wraps modulo `WORD`, always ok. -/
def semC : CmdC → StC → Set StC
  | .skip, s => {s}
  | .assign x e, s => {Function.update s x (e s)}
  | .seq c₁ c₂, s => kleisli (semC c₂) (semC c₁ s)
  | .choice c₁ c₂, s => semC c₁ s ∪ semC c₂ s
  | .addAssign x y, s => {Function.update s x ((s x + s y) % WORD)}

def semLiftC (c : CmdC) : Set StC → Set StC := kleisli (semC c)

@[simp] theorem semC_addAssign (x y : String) (s : StC) :
    semC (.addAssign x y) s = {Function.update s x ((s x + s y) % WORD)} := rfl

theorem semC_nonempty (c : CmdC) (s : StC) : (semC c s).Nonempty := by
  induction c generalizing s with
  | skip => exact ⟨s, rfl⟩
  | assign x e => exact ⟨_, rfl⟩
  | seq c₁ c₂ ih₁ ih₂ => exact kleisli_nonempty (ih₁ s) fun t _ => ih₂ t
  | choice c₁ c₂ ih₁ ih₂ => exact (ih₁ s).inl
  | addAssign x y => exact ⟨_, rfl⟩

@[simp] theorem mem_semLiftC {c : CmdC} {m : Set StC} {t : StC} :
    t ∈ semLiftC c m ↔ ∃ s ∈ m, t ∈ semC c s := mem_kleisli

@[simp] theorem semLiftC_singleton (c : CmdC) (s : StC) : semLiftC c {s} = semC c s :=
  kleisli_singleton _ _

theorem semLiftC_nonempty (c : CmdC) {m : Set StC} (hm : m.Nonempty) :
    (semLiftC c m).Nonempty :=
  kleisli_nonempty hm fun s _ => semC_nonempty c s

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

/-! ## The Rust-like side -/

/-- Rust-like commands: checked addition, deterministic (no choice). -/
inductive CmdR where
  | skip
  | assign (x : String) (e : StR → Int)
  | seq (c₁ c₂ : CmdR)
  | addAssign (x y : String)

/-- Rust-like semantics into the error carrier: checked `addAssign` panics on
overflow. -/
def semR : CmdR → StR → Set (Except Unit StR)
  | .skip, s => {.ok s}
  | .assign x e, s => {.ok (Function.update s x (e s))}
  | .seq c₁ c₂, s => kleisli (errK (semR c₂)) (semR c₁ s)
  | .addAssign x y, s =>
      if s x + s y < WORD then {.ok (Function.update s x (s x + s y))} else {.error ()}

def semLiftR (c : CmdR) : Set (Except Unit StR) → Set (Except Unit StR) :=
  kleisli (errK (semR c))

theorem semR_addAssign_ok {x y : String} {s : StR} (h : s x + s y < WORD) :
    semR (.addAssign x y) s = {.ok (Function.update s x (s x + s y))} := by
  simp only [semR, if_pos h]

theorem semR_addAssign_err {x y : String} {s : StR} (h : ¬ s x + s y < WORD) :
    semR (.addAssign x y) s = {.error ()} := by
  simp only [semR, if_neg h]

theorem semR_nonempty (c : CmdR) (s : StR) : (semR c s).Nonempty := by
  induction c generalizing s with
  | skip => exact ⟨_, rfl⟩
  | assign x e => exact ⟨_, rfl⟩
  | seq c₁ c₂ ih₁ ih₂ => exact kleisli_nonempty (ih₁ s) fun a _ => errK_nonempty ih₂ a
  | addAssign x y =>
    by_cases h : s x + s y < WORD
    · rw [semR_addAssign_ok h]; exact ⟨_, rfl⟩
    · rw [semR_addAssign_err h]; exact ⟨_, rfl⟩

@[simp] theorem mem_semLiftR {c : CmdR} {m : Set (Except Unit StR)} {b : Except Unit StR} :
    b ∈ semLiftR c m ↔ ∃ a ∈ m, b ∈ errK (semR c) a := mem_kleisli

@[simp] theorem semLiftR_singleton (c : CmdR) (a : Except Unit StR) :
    semLiftR c {a} = errK (semR c) a :=
  kleisli_singleton _ _

theorem semLiftR_nonempty (c : CmdR) {m : Set (Except Unit StR)} (hm : m.Nonempty) :
    (semLiftR c m).Nonempty :=
  kleisli_nonempty hm fun a _ => errK_nonempty (semR_nonempty c) a

/-! ## The heterogeneous quadruple -/

/-- The heterogeneous RelOL quadruple: C-like on the left, Rust-like on the
right — an *instantiation* of the polymorphic `quadSem`, not a new definition. -/
def quadH (R : RAssn StC (Except Unit StR)) (c : CmdC) (c' : CmdR)
    (S : RAssn StC (Except Unit StR)) : Prop :=
  quadSem (semLiftC c) (semLiftR c') R S

end RelOL
