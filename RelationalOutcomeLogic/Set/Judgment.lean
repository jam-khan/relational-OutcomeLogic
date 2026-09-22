import RelationalOutcomeLogic.Set.Language
import RelationalOutcomeLogic.Set.Assertions

/-!
# The quadruple `⦃R⦄ c ~ c' ⦃S⦄`

`⟪R⟫ F , G ⟪S⟫` is the semantic judgment over arbitrary lifts (language-independent).
`⌈…⌉` and `⌈…⌉ʷ` also accept two-state program assertions: unprimed variables read the
left state, primed ones the right, e.g. `⌈y = 1 ∧ y' = 1⌉`.
-/

namespace RelOL

variable {α β γ δ : Type*}

def quadSem (F : Set α → Set γ) (G : Set β → Set δ) (R : RAssn α β) (S : RAssn γ δ) : Prop :=
  ∀ m m', R m m' → S (F m) (G m')

def quad (R : RAssn State State) (c c' : Cmd) (S : RAssn State State) : Prop :=
  quadSem (semLift c) (semLift c') R S

scoped notation:50 "⦃" R "⦄ " c:50 " ~ " c':50 " ⦃" S "⦄" => quad R c c' S
scoped notation:50 "⟪" R "⟫ " F:51 " , " G:51 " ⟪" S "⟫" => quadSem F G R S

/-- Two-state program expressions: `x` reads the left state, `x'` the right. -/
declare_syntax_cat rrexp

/-- Two-state assertions on program expressions (the `⌈…⌉` sugar). -/
declare_syntax_cat rassn

syntax num : rrexp
syntax "-" num : rrexp
syntax ident : rrexp
syntax str : rrexp
syntax:65 rrexp:65 " + " rrexp:66 : rrexp
syntax:65 rrexp:65 " - " rrexp:66 : rrexp
syntax:70 rrexp:70 " * " rrexp:71 : rrexp
syntax "(" rrexp ")" : rrexp
syntax "↑" term:max : rrexp

syntax:50 rrexp:51 " = " rrexp:51 : rassn
syntax:50 rrexp:51 " ≠ " rrexp:51 : rassn
syntax:50 rrexp:51 " < " rrexp:51 : rassn
syntax:50 rrexp:51 " ≤ " rrexp:51 : rassn
syntax:50 rrexp:51 " > " rrexp:51 : rassn
syntax:50 rrexp:51 " ≥ " rrexp:51 : rassn
syntax:35 rassn:36 " ∧ " rassn:35 : rassn
syntax:30 rassn:31 " ∨ " rassn:30 : rassn
syntax:40 "¬" rassn:40 : rassn
syntax "(" rassn ")" : rassn
syntax ident : rassn
syntax "↑" term:max : rassn

/-- (internal) value of a two-state expression in states `s`, `s'`. -/
syntax "rrexp% " ident ident rrexp : term
/-- (internal) truth of a two-state assertion in states `s`, `s'`. -/
syntax "rassn% " ident ident rassn : term

macro_rules
  | `(rrexp% $_ $_ $n:num)  => `(($n : Int))
  | `(rrexp% $_ $_ -$n:num) => `((-$n : Int))
  | `(rrexp% $s $s' $x:ident) => do
      let n := x.getId.toString
      if n.endsWith "'" then `($s' $(Lean.quote (String.ofList n.toList.dropLast)))
      else `($s $(Lean.quote n))
  | `(rrexp% $s $_ $x:str)  => `($s $x)
  | `(rrexp% $s $s' $a:rrexp + $b:rrexp) => `((rrexp% $s $s' $a) + (rrexp% $s $s' $b))
  | `(rrexp% $s $s' $a:rrexp - $b:rrexp) => `((rrexp% $s $s' $a) - (rrexp% $s $s' $b))
  | `(rrexp% $s $s' $a:rrexp * $b:rrexp) => `((rrexp% $s $s' $a) * (rrexp% $s $s' $b))
  | `(rrexp% $s $s' ($a:rrexp)) => `(rrexp% $s $s' $a)
  | `(rrexp% $s $s' ↑$t)    => `(($t : State → State → Int) $s $s')

macro_rules
  | `(rassn% $s $s' $a:rrexp = $b:rrexp) => `((rrexp% $s $s' $a) = (rrexp% $s $s' $b))
  | `(rassn% $s $s' $a:rrexp ≠ $b:rrexp) => `((rrexp% $s $s' $a) ≠ (rrexp% $s $s' $b))
  | `(rassn% $s $s' $a:rrexp < $b:rrexp) => `((rrexp% $s $s' $a) < (rrexp% $s $s' $b))
  | `(rassn% $s $s' $a:rrexp ≤ $b:rrexp) => `((rrexp% $s $s' $a) ≤ (rrexp% $s $s' $b))
  | `(rassn% $s $s' $a:rrexp > $b:rrexp) => `((rrexp% $s $s' $a) > (rrexp% $s $s' $b))
  | `(rassn% $s $s' $a:rrexp ≥ $b:rrexp) => `((rrexp% $s $s' $a) ≥ (rrexp% $s $s' $b))
  | `(rassn% $s $s' $a:rassn ∧ $b:rassn) => `((rassn% $s $s' $a) ∧ (rassn% $s $s' $b))
  | `(rassn% $s $s' $a:rassn ∨ $b:rassn) => `((rassn% $s $s' $a) ∨ (rassn% $s $s' $b))
  | `(rassn% $s $s' ¬$a:rassn) => `(¬ (rassn% $s $s' $a))
  | `(rassn% $s $s' ($a:rassn)) => `(rassn% $s $s' $a)
  | `(rassn% $_ $_ $x:ident) => do
      -- only the constants; anything else falls back to the term form `⌈r⌉`
      if x.getId.eraseMacroScopes == `True then `(True)
      else if x.getId.eraseMacroScopes == `False then `(False)
      else Lean.Macro.throwUnsupported
  | `(rassn% $s $s' ↑$t)    => `(($t : State → State → Prop) $s $s')

scoped syntax "⌈" rassn "⌉" : term
scoped syntax "⌈" rassn "⌉ʷ" : term

macro_rules
  | `(⌈$a:rassn⌉)  => `(atom (fun s s' => rassn% s s' $a))
  | `(⌈$a:rassn⌉ʷ) => `(atomW (fun s s' => rassn% s s' $a))

end RelOL
