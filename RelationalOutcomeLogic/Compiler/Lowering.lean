import RelationalOutcomeLogic.Lang
import RelationalOutcomeLogic.Quadruple
import RelationalOutcomeLogic.Hetero.Lang

/-!
# The exceptions-to-error-codes lowering pass

A source language `CmdS` with structured exceptions (`throw`), whose semantics
lands in `Set (Except State State)` — the exception **carries the state at the
throw point** — is lowered to the *ite-fragment of the already-mechanized core
language* `Cmd` (a genuine subset of core: no `choice`). This is the
effect-changing pass singled out in the project plan: source and target live
under different monads, so the pass is a heterogeneous relational judgment by
construction.

* `lower` — the correct pass: `throw` becomes `err := 1`, and sequencing guards
  the continuation with `err = 0`.
* `lowerBug` — the classic miscompilation mode: the error guard on sequencing
  is dropped, so the target keeps executing after an exception.
* `lowRel` — the compilation correspondence: an ok source outcome matches the
  identical target store; an exceptional outcome `error te` matches the
  throw-point store with the error flag set, `update te "err" 1`.

Convention: source programs do not mention the reserved variable `"err"` and
target execution starts from a store with `err = 0` (both facts hold for the
concrete example programs; a well-formedness predicate is future work).
-/

namespace RelOL

/-- Source commands: the core sequential fragment plus `throw`. -/
inductive CmdS where
  | skip
  | assign (x : String) (e : State → Int)
  | seq (c₁ c₂ : CmdS)
  | throw

/-- Source semantics: exceptions carry the state at the throw point and
propagate through sequencing via `errK`. -/
def semS : CmdS → State → Set (Except State State)
  | .skip, s => {.ok s}
  | .assign x e, s => {.ok (Function.update s x (e s))}
  | .seq c₁ c₂, s => kleisli (errK (semS c₂)) (semS c₁ s)
  | .throw, s => {.error s}

def semLiftS (c : CmdS) : Set (Except State State) → Set (Except State State) :=
  kleisli (errK (semS c))

@[simp] theorem semLiftS_singleton (c : CmdS) (a : Except State State) :
    semLiftS c {a} = errK (semS c) a :=
  kleisli_singleton _ _

/-- The correct lowering: error codes plus guarded sequencing. The image is the
deterministic ite-fragment of the core language. -/
def lower : CmdS → Cmd
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq c₁ c₂ => .seq (lower c₁) (.ite (fun s => s "err" = 0) (lower c₂) .skip)
  | .throw => .assign "err" fun _ => 1

/-- The buggy lowering: the error guard on sequencing is **dropped** — the
target continues executing after an exception (a dropped-error miscompilation). -/
def lowerBug : CmdS → Cmd
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq c₁ c₂ => .seq (lowerBug c₁) (lowerBug c₂)
  | .throw => .assign "err" fun _ => 1

/-- Compilation correspondence between source outcomes and target stores. -/
def lowRel : Except State State → State → Prop
  | .ok t, t' => t' = t
  | .error te, t' => t' = Function.update te "err" 1

/-- The compilation-correctness quadruple for a source program `c` under a pass
`comp`, at initial store `s`: heterogeneous pre (source entered via `.ok`),
post = the correspondence, exhaustively (no `⊤`). -/
def lowered (comp : CmdS → Cmd) (c : CmdS) (s : State) : Prop :=
  quadSem (semLiftS c) (semLift (comp c))
    (fun m m' => m = {Except.ok s} ∧ m' = {s}) (atom lowRel)

end RelOL
