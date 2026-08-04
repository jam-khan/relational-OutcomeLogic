import Mathlib.Logic.Function.Basic
import RelationalOutcomeLogic.Basic
import RelationalOutcomeLogic.Kleisli

/-!
  Simple `cwhile` like language and its powerset
  semantics.

  - `nondeterministic`
  - `while` loops
  - `power set` semantics

  Note: this is an instance of OL semantics,
  ideally we want generality beyond `power set`
  semantics. For Relational Outcome Logic,
  we begin with the `power set` for now.

  Note: this is for `homogenous` setting,
  `relOL` shall be capable of reasoning in
  `heterogenous` language setting (two languages
  with different semantics).
-/

namespace RelOL

-- This allows for `State -> Prop` semantics
-- at the cost of assuming decidability deriving
-- from `classical axiom of choice`.
attribute [local instance] Classical.propDecidable

-- Commands of the homogeneous language.
inductive Cmd where
  | skip
  | assign (x : String) (e : State → Int)
  | seq (c₁ c₂ : Cmd)
  | ite (b : State → Prop) (c₁ c₂ : Cmd)
  | choice (c₁ c₂ : Cmd)
  | while (b : State → Prop) (c : Cmd)

/-! ## Program notation (scoped to `RelOL`)

  `SKIP`                        no-op
  `x ::= e`                     assignment (e is a program expression, see below)
  `c₁ ;; c₂`                    sequencing
  `c₁ + c₂`                     nondeterministic choice
  `IF b THEN c₁ ELSE c₂ END`    conditional (b is a program guard, see below)
  `WHILE b DO c END`            loop

Assignment RHSs and guards are *program expressions*, not Lean lambdas: bare
identifiers are program variables (`x` means `fun s => s "x"`), numerals are
constants, and `+ - *` / `= ≠ < ≤ > ≥ ∧ ∨ ¬` mean the obvious things. So

  `x ::= 1`,  `y ::= x + 1`,  `WHILE i < n DO i ::= i + 1 END`

all elaborate to the plain `Cmd.assign`/`Cmd.while` terms with the usual
`fun s => …` functions inside — the sugar is macro-only, nothing new in the
semantics. Escapes, for when a piece of the program is a Lean variable:

  `↑x ::= ↑e`      assignment with `x : String`, `e : State → Int` in scope
  `WHILE ↑b DO …`  guard from a Lean term `b : State → Prop`
  `"x" ::= e`      the variable name as a string literal also works

`⟦e⟧` / `⟦b⟧` turn a program expression / guard into a standalone
`State → Int` / `State → Prop` term.

Precedence: `::=` (70) > `+` (65) > `;;` (50), so
`(x ::= e) + (x ::= e') ;; c` reads as `((x ::= e) + (x ::= e')) ;; c`.
One trap: the RHS of `::=` is greedy, so choice branches need parens —
`x ::= 1 + x ::= 2` is a parse error, write `(x ::= 1) + (x ::= 2)`. -/

scoped notation "SKIP" => Cmd.skip
scoped infixr:50 " ;; " => Cmd.seq
scoped instance : Add Cmd := ⟨Cmd.choice⟩

@[simp] theorem Cmd.add_def (c₁ c₂ : Cmd) : c₁ + c₂ = Cmd.choice c₁ c₂ := rfl

/-- Program expressions (`Int`-valued): numerals, program variables, `+ - *`,
and `↑t` to splice a Lean term `t : State → Int`. -/
declare_syntax_cat rexp

/-- Program guards (`Prop`-valued): comparisons of program expressions,
`∧ ∨ ¬`, and `↑t` to splice a Lean term `t : State → Prop`. -/
declare_syntax_cat rbexp

syntax num : rexp
syntax "-" num : rexp
syntax ident : rexp
syntax str : rexp
syntax:65 rexp:65 " + " rexp:66 : rexp
syntax:65 rexp:65 " - " rexp:66 : rexp
syntax:70 rexp:70 " * " rexp:71 : rexp
syntax "(" rexp ")" : rexp
syntax "↑" term:max : rexp

syntax:50 rexp:51 " = " rexp:51 : rbexp
syntax:50 rexp:51 " ≠ " rexp:51 : rbexp
syntax:50 rexp:51 " < " rexp:51 : rbexp
syntax:50 rexp:51 " ≤ " rexp:51 : rbexp
syntax:50 rexp:51 " > " rexp:51 : rbexp
syntax:50 rexp:51 " ≥ " rexp:51 : rbexp
syntax:35 rbexp:36 " ∧ " rbexp:35 : rbexp
syntax:30 rbexp:31 " ∨ " rbexp:30 : rbexp
syntax:40 "¬" rbexp:40 : rbexp
syntax "(" rbexp ")" : rbexp
syntax "↑" term:max : rbexp

/-- (internal) value of the program expression in state `s`. -/
syntax "rexp% " ident rexp : term
/-- (internal) truth of the program guard in state `s`. -/
syntax "rbexp% " ident rbexp : term

macro_rules
  | `(rexp% $_ $n:num)              => `(($n : Int))
  | `(rexp% $_ -$n:num)             => `((-$n : Int))
  | `(rexp% $s $x:ident)            => `($s $(Lean.quote x.getId.toString))
  | `(rexp% $s $x:str)              => `($s $x)
  | `(rexp% $s $a:rexp + $b:rexp)   => `((rexp% $s $a) + (rexp% $s $b))
  | `(rexp% $s $a:rexp - $b:rexp)   => `((rexp% $s $a) - (rexp% $s $b))
  | `(rexp% $s $a:rexp * $b:rexp)   => `((rexp% $s $a) * (rexp% $s $b))
  | `(rexp% $s ($a:rexp))           => `(rexp% $s $a)
  | `(rexp% $s ↑$t)                 => `(($t : State → Int) $s)

macro_rules
  | `(rbexp% $s $a:rexp = $b:rexp)  => `((rexp% $s $a) = (rexp% $s $b))
  | `(rbexp% $s $a:rexp ≠ $b:rexp)  => `((rexp% $s $a) ≠ (rexp% $s $b))
  | `(rbexp% $s $a:rexp < $b:rexp)  => `((rexp% $s $a) < (rexp% $s $b))
  | `(rbexp% $s $a:rexp ≤ $b:rexp)  => `((rexp% $s $a) ≤ (rexp% $s $b))
  | `(rbexp% $s $a:rexp > $b:rexp)  => `((rexp% $s $a) > (rexp% $s $b))
  | `(rbexp% $s $a:rexp ≥ $b:rexp)  => `((rexp% $s $a) ≥ (rexp% $s $b))
  | `(rbexp% $s $a:rbexp ∧ $b:rbexp) => `((rbexp% $s $a) ∧ (rbexp% $s $b))
  | `(rbexp% $s $a:rbexp ∨ $b:rbexp) => `((rbexp% $s $a) ∨ (rbexp% $s $b))
  | `(rbexp% $s ¬$a:rbexp)          => `(¬ (rbexp% $s $a))
  | `(rbexp% $s ($a:rbexp))         => `(rbexp% $s $a)
  | `(rbexp% $s ↑$t)                => `(($t : State → Prop) $s)

scoped syntax "⟦" rexp "⟧" : term
scoped syntax "⟦" rbexp "⟧" : term

macro_rules
  | `(⟦$e:rexp⟧)  => `((fun s => rexp% s $e : State → Int))
  | `(⟦$b:rbexp⟧) => `((fun s => rbexp% s $b : State → Prop))

scoped syntax:70 ident " ::= " rexp : term
scoped syntax:70 str " ::= " rexp : term
scoped syntax:70 "↑" term:max " ::= " rexp : term

macro_rules
  | `($x:ident ::= $e:rexp) => `(Cmd.assign $(Lean.quote x.getId.toString) ⟦$e:rexp⟧)
  | `($x:str ::= $e:rexp)   => `(Cmd.assign $x ⟦$e:rexp⟧)
  | `(↑$x ::= $e:rexp)      => `(Cmd.assign $x ⟦$e:rexp⟧)

scoped syntax "IF " rbexp " THEN " term " ELSE " term " END" : term
scoped syntax "WHILE " rbexp " DO " term " END" : term

macro_rules
  | `(IF $b:rbexp THEN $c₁ ELSE $c₂ END) => `(Cmd.ite ⟦$b:rbexp⟧ $c₁ $c₂)
  | `(WHILE $b:rbexp DO $c END)          => `(Cmd.while ⟦$b:rbexp⟧ $c)

open Classical in
-- Denotational semantics: the set of possible final states.
noncomputable def sem : Cmd → State → Set State
  | .skip, s          => {s}
  | .assign x e, s    => {Function.update s x (e s)}
  | .seq c₁ c₂, s     => kleisli (sem c₂) (sem c₁ s)
  | .ite b c₁ c₂, s   => if b s then sem c₁ s else sem c₂ s
  | .choice c₁ c₂, s  => sem c₁ s ∪ sem c₂ s
  | .while b c, s     => loopSem b (sem c) s

-- lifting of semantics from `State to Set of States`
-- to `Set of States → Set of States` (Kleisli extension)
noncomputable def semLift (c : Cmd) : Set State → Set State :=
  kleisli (sem c)

-- Some helper lemmas for `simplification`
-- Note: semantics are defined as `noncomputable`
-- so, below lemmas can help with proofs by `simplication`
-- instead of `computation`/`fixpoint`.
@[simp] theorem sem_skip
  (s : State) :
    sem .skip s = {s} := by
  rfl

@[simp] theorem sem_assign
  (x : String) (e : State → Int) (s : State) :
    sem (.assign x e) s = {Function.update s x (e s)} := by
  rfl

@[simp] theorem sem_seq
  (c₁ c₂ : Cmd) (s : State) :
    sem (.seq c₁ c₂) s = kleisli (sem c₂) (sem c₁ s) := by
  rfl

@[simp] theorem sem_choice
  (c₁ c₂ : Cmd) (s : State) :
    sem (.choice c₁ c₂) s = sem c₁ s ∪ sem c₂ s := by
  rfl

@[simp] theorem sem_ite_pos
  {b : State → Prop} {s : State} (h : b s) (c₁ c₂ : Cmd) :
    sem (.ite b c₁ c₂) s = sem c₁ s := by
  simp only [sem, if_pos h]

@[simp] theorem sem_ite_neg
  {b : State → Prop} {s : State} (h : ¬ b s) (c₁ c₂ : Cmd) :
    sem (.ite b c₁ c₂) s = sem c₂ s := by
  simp only [sem, if_neg h]

-- Loops
@[simp] theorem sem_while
  (b : State → Prop) (c : Cmd) (s : State) :
    sem (.while b c) s = loopSem b (sem c) s := rfl

@[simp] theorem sem_while_unfold
  (b : State → Prop) (c : Cmd) (s : State) :
    sem (.while b c) s
      = if b s then semLift (.while b c) (sem c s) else {s} := by
  apply loopSem_unfold b (sem c) s

@[simp] theorem sem_while_pos
  {b : State → Prop} {s : State} (h : b s) (c : Cmd) :
    sem (.while b c) s = semLift (.while b c) (sem c s) := by
  rw [sem_while_unfold, if_pos]
  assumption

@[simp] theorem sem_while_neg
  {b : State → Prop} {s : State} (h : ¬ b s) (c : Cmd) :
    sem (.while b c) s = {s} := by
  rw [sem_while_unfold, if_neg h]

/-
  Fuel based lemmas for `while` loop
-/
@[simp] theorem loopIter_subset_sem
  (b : State → Prop) (c : Cmd) (n : ℕ) (s : State) :
    loopIter b (sem c) n s ⊆ sem (.while b c) s :=
  loopIter_subset_loopSem b (sem c) n s

/-
  `while` is the least fixed point of its characteristic functional
  (Knaster–Tarski reading; regression pin for the loop semantics).
-/
@[simp] theorem sem_while_eq_lfp
  (b : State → Prop) (c : Cmd) :
    sem (.while b c) = OrderHom.lfp (loopHom b (sem c)) := by
  funext s
  simp only [sem_while]
  rw [loopSem_eq_lfp]

-- Divergence is the empty outcome set.
theorem sem_while_true_skip (s : State) :
    sem (.while (fun _ => True) .skip) s = ∅ := by
  rw [sem_while]
  unfold loopSem
  refine Set.eq_empty_of_subset_empty (Set.iUnion_subset fun n => ?_)
  induction n generalizing s with
  | zero      => simp
  | succ n ih =>
      rw [loopIter_succ_pos, sem_skip, kleisli_singleton]
      · exact ih s
      · grind

-- Loop-free fragment
-- This reserves the Cmd to loopfree fragment
-- allows for more properties to be stated
-- ideally all things possible with the loop fragment
@[simp] def LoopFree : Cmd → Prop
  | .skip         => True
  | .assign _ _   => True
  | .seq c₁ c₂    => LoopFree c₁ ∧ LoopFree c₂
  | .ite _ c₁ c₂  => LoopFree c₁ ∧ LoopFree c₂
  | .choice c₁ c₂ => LoopFree c₁ ∧ LoopFree c₂
  | .while _ _    => False

-- `Loop-free` fragment shall not diverge
-- as main cause of divergence appears
-- due to `loops`
-- This means every `command` must have
-- atleast one outcome from every state.
theorem sem_nonempty
  {c : Cmd} (hc : LoopFree c) (s : State) :
    (sem c s).Nonempty := by
  induction c generalizing s with
  | skip       => exact Set.nonempty_of_mem rfl
  | assign x e => exact Set.nonempty_of_mem rfl
  | seq c₁ c₂ ih₁ ih₂ =>
      rw [sem_seq]
      cases hc
      apply kleisli_nonempty <;> grind
  | ite b c₁ c₂ ih₁ ih₂ =>
      by_cases h : b s
      · rw [sem_ite_pos h c₁ c₂]
        apply ih₁ hc.1
      · rw [sem_ite_neg h c₁ c₂]
        apply ih₂ hc.2
  | choice c₁ c₂ ih₁ ih₂ =>
      rw [sem_choice]
      rw [@Set.union_nonempty]
      left
      apply ih₁ hc.1
  | «while» b c ih =>
      by_cases h : b s
      · rw [sem_while_pos h c]
        exact Set.nonempty_iff_ne_empty.mpr fun a ↦ hc
      · rw [sem_while_neg h c]
        exact Set.singleton_nonempty s

/-
lifting lemmas, derived from `kleisli`

Why do we need these?
  kleisli based semantics are not used by the logic
  directly, rather `lifting : Power set → Power set`
  is used, hence we need below lemmas for the `semLift`

sem c     : State → Set State   -- program semantics (`Kleisli` arrow)
semLift c : Set State → Set State -- = kleisli (sem c), `lifting`
quad (logic) : assertions over the semantic lifting

Hence, we derive below for the `lifting` based on the `sem`
-/
@[simp] theorem mem_semLift
  {c : Cmd} {m : Set State} {t : State} :
    t ∈ semLift c m ↔ ∃ s ∈ m, t ∈ sem c s :=
  mem_kleisli

@[simp] theorem semLift_empty
  (c : Cmd) :
    semLift c ∅ = ∅ := kleisli_empty _

@[simp] theorem semLift_singleton
  (c : Cmd) (s : State) :
    semLift c {s} = sem c s :=
  kleisli_singleton _ _

@[simp] theorem semLift_skip
  (m : Set State) :
    semLift .skip m = m := by
  ext t; simp

@[simp] theorem semLift_union
  (c : Cmd) (m₁ m₂ : Set State) :
    semLift c (m₁ ∪ m₂) = semLift c m₁ ∪ semLift c m₂ := by
  ext t; simp [semLift]

@[simp] theorem semLift_seq
  (c₁ c₂ : Cmd) (m : Set State) :
    semLift (.seq c₁ c₂) m = semLift c₂ (semLift c₁ m) :=
  (kleisli_comp (sem c₁) (sem c₂) m).symm

@[simp] theorem semLift_choice
  (c₁ c₂ : Cmd) (m : Set State) :
    semLift (.choice c₁ c₂) m = semLift c₁ m ∪ semLift c₂ m :=
  kleisli_pointwise_union (sem c₁) (sem c₂) m

@[simp] theorem semLift_nonempty
  {c : Cmd} (hc : LoopFree c) {m : Set State} (hm : m.Nonempty) :
    (semLift c m).Nonempty := by
  unfold semLift
  refine kleisli_nonempty hm ?_
  exact fun x a ↦ sem_nonempty hc x

/-
  Set-level computation lemmas for the structured rules

  These are used for the structural rules later.
-/

-- `⟦x := e⟧†(m) = { s[x ↦ e(s)] | s ∈ m}`
@[simp] theorem semLift_assign
  (x : String) (e : State → Int) (m : Set State) :
    semLift (.assign x e) m = (fun s => Function.update s x (e s)) '' m := by
  ext t
  simp [Set.mem_image, eq_comm]

-- `(∀ s ∈ m, b(s)) → ⟦if b then c₁ else c₂⟧†(m) = ⟦c₁⟧†(m)`
@[simp] theorem semLift_ite_pos
  {b : State → Prop} {m : Set State} (h : ∀ s ∈ m, b s) (c₁ c₂ : Cmd) :
    semLift (.ite b c₁ c₂) m = semLift c₁ m := by
  unfold semLift
  refine kleisli_congr ?_
  intro x hx
  by_cases h' : b x
  · exact sem_ite_pos (h x hx) c₁ c₂
  · exact sem_ite_pos (h x hx) c₁ c₂

-- `(∀ s ∈ m, ¬ b(s)) → ⟦if b then c₁ else c₂⟧†(m) = ⟦c₂⟧†(m)`
@[simp] theorem semLift_ite_neg
  {b : State → Prop} {m : Set State} (h : ∀ s ∈ m, ¬ b s) (c₁ c₂ : Cmd) :
    semLift (.ite b c₁ c₂) m = semLift c₂ m := by
  unfold semLift
  refine kleisli_congr ?_
  intro x hx
  by_cases h' : b x
  · exact sem_ite_neg (h x hx) c₁ c₂
  · exact sem_ite_neg (h x hx) c₁ c₂

-- On a set where the guard fails uniformly, the loop is the identity.
@[simp] theorem semLift_while_neg
  {b : State → Prop} {m : Set State} (h : ∀ s ∈ m, ¬ b s) (c : Cmd) :
    semLift (.while b c) m = m := by
  rw [semLift, kleisli_congr fun s hs => sem_while_neg (h s hs) c]
  ext t
  simp [mem_kleisli]

@[simp] theorem semLift_while_pos
  {b : State → Prop} {m : Set State} (h : ∀ s ∈ m, b s) (c : Cmd) :
    semLift (.while b c) m = semLift (.while b c) (semLift c m) := by
  rw [semLift, kleisli_congr fun s hs => sem_while_pos (h s hs) c]
  rw [semLift, semLift, kleisli_comp]

-- `while b c` and it's one step un-roll are equivalent
@[simp] theorem sem_while_eq_unroll
  (b : State → Prop) (c : Cmd) :
    sem (.while b c) = sem (.ite b (.seq c (.while b c)) .skip) := by
  funext s -- f ~> f s
  by_cases h' : b s
  · rw [sem_while_pos h' c, semLift, sem]
    simp; grind
  · rw [sem_while_neg h' c]
    rw [sem]
    simp; grind

end RelOL
