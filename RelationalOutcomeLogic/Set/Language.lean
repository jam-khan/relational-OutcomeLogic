import Mathlib.Logic.Function.Basic
import RelationalOutcomeLogic.Set.State
import RelationalOutcomeLogic.Set.Semantics

/-!
# A nondeterministic while-language with powerset semantics

Notation (scoped): `SKIP`, `x ::= e`, `c₁ ;; c₂`, `c₁ + c₂`, `IF b THEN c₁ ELSE c₂ END`,
`WHILE b DO c END`. Expressions and guards are program expressions: identifiers are
program variables, `↑t` splices a Lean term, `⟦e⟧` is the denoted function.
Precedence: `::=` (70) > `+` (65) > `;;` (50); parenthesise choice branches.
-/

namespace RelOL

attribute [local instance] Classical.propDecidable

inductive Cmd where
  | skip
  | assign (x : String) (e : State → Int)
  | seq (c₁ c₂ : Cmd)
  | ite (b : State → Prop) (c₁ c₂ : Cmd)
  | choice (c₁ c₂ : Cmd)
  | while (b : State → Prop) (c : Cmd)

scoped notation "SKIP" => Cmd.skip
scoped infixr:50 " ;; " => Cmd.seq
scoped instance : Add Cmd := ⟨Cmd.choice⟩

@[simp] theorem Cmd.add_def (c₁ c₂ : Cmd) : c₁ + c₂ = Cmd.choice c₁ c₂ := rfl

/-- Program expressions (`Int`-valued). -/
declare_syntax_cat rexp

/-- Program guards (`Prop`-valued). -/
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
-- constant guards `True`/`False` (as `ident`: string literals would become global keywords)
syntax ident : rbexp

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
  | `(rbexp% $_ $x:ident)           => do
      if x.getId.eraseMacroScopes == `True then `(True)
      else if x.getId.eraseMacroScopes == `False then `(False)
      else Lean.Macro.throwUnsupported

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

-- fully-escaped forms elaborate straight to the constructors (tried first)
macro_rules
  | `($x:ident ::= ↑$t) => `(Cmd.assign $(Lean.quote x.getId.toString) ($t : State → Int))
  | `($x:str ::= ↑$t)   => `(Cmd.assign $x ($t : State → Int))
  | `(↑$x ::= ↑$t)      => `(Cmd.assign $x ($t : State → Int))

macro_rules
  | `(IF ↑$t THEN $c₁ ELSE $c₂ END) => `(Cmd.ite ($t : State → Prop) $c₁ $c₂)
  | `(WHILE ↑$t DO $c END)          => `(Cmd.while ($t : State → Prop) $c)

/-- Denotational semantics: the set of possible final states (`∅` is divergence). -/
noncomputable def sem : Cmd → State → Set State
  | .skip, s => {s}
  | .assign x e, s => {Function.update s x (e s)}
  | .seq c₁ c₂, s => kleisli (sem c₂) (sem c₁ s)
  | .ite b c₁ c₂, s => if b s then sem c₁ s else sem c₂ s
  | .choice c₁ c₂, s => sem c₁ s ∪ sem c₂ s
  | .while b c, s => loopSem b (sem c) s

/-- The lifted semantics the logic speaks about. -/
noncomputable def semLift (c : Cmd) : Set State → Set State :=
  kleisli (sem c)

@[simp] theorem sem_skip (s : State) : sem .skip s = {s} := rfl

@[simp] theorem sem_assign (x : String) (e : State → Int) (s : State) :
    sem (.assign x e) s = {Function.update s x (e s)} := rfl

@[simp] theorem sem_seq (c₁ c₂ : Cmd) (s : State) :
    sem (.seq c₁ c₂) s = kleisli (sem c₂) (sem c₁ s) := rfl

@[simp] theorem sem_choice (c₁ c₂ : Cmd) (s : State) :
    sem (.choice c₁ c₂) s = sem c₁ s ∪ sem c₂ s := rfl

@[simp] theorem sem_ite_pos {b : State → Prop} {s : State} (h : b s) (c₁ c₂ : Cmd) :
    sem (.ite b c₁ c₂) s = sem c₁ s := by
  simp only [sem, if_pos h]

@[simp] theorem sem_ite_neg {b : State → Prop} {s : State} (h : ¬ b s) (c₁ c₂ : Cmd) :
    sem (.ite b c₁ c₂) s = sem c₂ s := by
  simp only [sem, if_neg h]

@[simp] theorem sem_while (b : State → Prop) (c : Cmd) (s : State) :
    sem (.while b c) s = loopSem b (sem c) s := rfl

theorem sem_while_unfold (b : State → Prop) (c : Cmd) (s : State) :
    sem (.while b c) s = if b s then semLift (.while b c) (sem c s) else {s} :=
  loopSem_unfold b (sem c) s

theorem sem_while_pos {b : State → Prop} {s : State} (h : b s) (c : Cmd) :
    sem (.while b c) s = semLift (.while b c) (sem c s) := by
  rw [sem_while_unfold, if_pos h]

theorem sem_while_neg {b : State → Prop} {s : State} (h : ¬ b s) (c : Cmd) :
    sem (.while b c) s = {s} := by
  rw [sem_while_unfold, if_neg h]

theorem loopIter_subset_sem (b : State → Prop) (c : Cmd) (n : ℕ) (s : State) :
    loopIter b (sem c) n s ⊆ sem (.while b c) s :=
  loopIter_subset_loopSem b (sem c) n s

theorem sem_while_eq_lfp (b : State → Prop) (c : Cmd) :
    sem (.while b c) = OrderHom.lfp (loopHom b (sem c)) := by
  funext s
  rw [sem_while, loopSem_eq_lfp]

/-- Divergence is the empty outcome set. -/
theorem sem_while_true (c : Cmd) (s : State) : sem (.while (fun _ => True) c) s = ∅ := by
  rw [sem_while]
  refine Set.eq_empty_of_subset_empty (Set.iUnion_subset fun n => ?_)
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [loopIter_succ_pos trivial]
    intro t ht
    obtain ⟨u, -, hu⟩ := mem_kleisli.mp ht
    exact ih u hu

theorem sem_while_true_skip (s : State) : sem (.while (fun _ => True) .skip) s = ∅ :=
  sem_while_true .skip s

@[simp] def LoopFree : Cmd → Prop
  | .skip => True
  | .assign _ _ => True
  | .seq c₁ c₂ => LoopFree c₁ ∧ LoopFree c₂
  | .ite _ c₁ c₂ => LoopFree c₁ ∧ LoopFree c₂
  | .choice c₁ c₂ => LoopFree c₁ ∧ LoopFree c₂
  | .while _ _ => False

/-- Loop-free commands never diverge. -/
theorem sem_nonempty {c : Cmd} (hc : LoopFree c) (s : State) : (sem c s).Nonempty := by
  induction c generalizing s with
  | skip => exact ⟨s, rfl⟩
  | assign x e => exact ⟨_, rfl⟩
  | seq c₁ c₂ ih₁ ih₂ => exact kleisli_nonempty (ih₁ hc.1 s) fun t _ => ih₂ hc.2 t
  | ite b c₁ c₂ ih₁ ih₂ =>
    by_cases h : b s
    · rw [sem_ite_pos h]; exact ih₁ hc.1 s
    · rw [sem_ite_neg h]; exact ih₂ hc.2 s
  | choice c₁ c₂ ih₁ ih₂ => exact (ih₁ hc.1 s).inl
  | «while» b c ih => exact hc.elim

/-! ## Lifted semantics -/

@[simp] theorem mem_semLift {c : Cmd} {m : Set State} {t : State} :
    t ∈ semLift c m ↔ ∃ s ∈ m, t ∈ sem c s := mem_kleisli

@[simp] theorem semLift_empty (c : Cmd) : semLift c ∅ = ∅ := kleisli_empty _

@[simp] theorem semLift_singleton (c : Cmd) (s : State) : semLift c {s} = sem c s :=
  kleisli_singleton _ _

@[simp] theorem semLift_skip (m : Set State) : semLift .skip m = m := by
  ext t; simp

@[simp] theorem semLift_union (c : Cmd) (m₁ m₂ : Set State) :
    semLift c (m₁ ∪ m₂) = semLift c m₁ ∪ semLift c m₂ :=
  kleisli_union _ _ _

@[simp] theorem semLift_seq (c₁ c₂ : Cmd) (m : Set State) :
    semLift (.seq c₁ c₂) m = semLift c₂ (semLift c₁ m) :=
  (kleisli_comp (sem c₁) (sem c₂) m).symm

@[simp] theorem semLift_choice (c₁ c₂ : Cmd) (m : Set State) :
    semLift (.choice c₁ c₂) m = semLift c₁ m ∪ semLift c₂ m :=
  kleisli_pointwise_union (sem c₁) (sem c₂) m

theorem semLift_nonempty {c : Cmd} (hc : LoopFree c) {m : Set State} (hm : m.Nonempty) :
    (semLift c m).Nonempty :=
  kleisli_nonempty hm fun s _ => sem_nonempty hc s

@[simp] theorem semLift_assign (x : String) (e : State → Int) (m : Set State) :
    semLift (.assign x e) m = (fun s => Function.update s x (e s)) '' m := by
  ext t
  simp [Set.mem_image, eq_comm]

theorem semLift_ite_pos {b : State → Prop} {m : Set State} (h : ∀ s ∈ m, b s) (c₁ c₂ : Cmd) :
    semLift (.ite b c₁ c₂) m = semLift c₁ m :=
  kleisli_congr fun s hs => sem_ite_pos (h s hs) c₁ c₂

theorem semLift_ite_neg {b : State → Prop} {m : Set State} (h : ∀ s ∈ m, ¬ b s) (c₁ c₂ : Cmd) :
    semLift (.ite b c₁ c₂) m = semLift c₂ m :=
  kleisli_congr fun s hs => sem_ite_neg (h s hs) c₁ c₂

theorem semLift_while_neg {b : State → Prop} {m : Set State} (h : ∀ s ∈ m, ¬ b s) (c : Cmd) :
    semLift (.while b c) m = m := by
  rw [semLift, kleisli_congr fun s hs => sem_while_neg (h s hs) c]
  ext t
  simp

theorem semLift_while_pos {b : State → Prop} {m : Set State} (h : ∀ s ∈ m, b s) (c : Cmd) :
    semLift (.while b c) m = semLift (.while b c) (semLift c m) := by
  rw [semLift, kleisli_congr fun s hs => sem_while_pos (h s hs) c, semLift, semLift, kleisli_comp]

/-- A loop is its one-step unrolling. -/
theorem sem_while_eq_unroll (b : State → Prop) (c : Cmd) :
    sem (.while b c) = sem (.ite b (.seq c (.while b c)) .skip) := by
  funext s
  by_cases h : b s
  · rw [sem_while_pos h, sem_ite_pos h, sem_seq, semLift]
  · rw [sem_while_neg h, sem_ite_neg h, sem_skip]

theorem semLift_while_eq_unroll (b : State → Prop) (c : Cmd) :
    semLift (.while b c) = semLift (.ite b (.seq c (.while b c)) .skip) := by
  unfold semLift
  rw [← sem_while_eq_unroll]

end RelOL
