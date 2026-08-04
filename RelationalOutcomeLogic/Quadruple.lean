import RelationalOutcomeLogic.Lang
import RelationalOutcomeLogic.Assertions

/-!
  # Relational Outcome Logic Quadruple `⟨P⟩ c ~ c' ⟨S⟩`
-/

namespace RelOL

variable {α β γ δ : Type*}

-- Semantic relational quadruple over abstract lift functions.
def quadSem (F : Set α → Set γ) (G : Set β → Set δ) (R : RAssn α β) (S : RAssn γ δ) : Prop :=
  ∀ m m', R m m' → S (F m) (G m')

/-- Homogeneous (same-language) Relational Outcome Logic quadruple. -/
def quad (R : RAssn State State) (c c' : Cmd) (S : RAssn State State) : Prop :=
  quadSem (semLift c) (semLift c') R S

-- Program slots parse at level 50 so `;;`-chains (infixr:50) fit without parens:
-- `⦃R⦄ c₁ ;; c₂ ~ c' ⦃S⦄` works.
@[inherit_doc] scoped notation:50 "⦃" R "⦄ " c:50 " ~ " c':50 " ⦃" S "⦄" => quad R c c' S

/-- Semantic quadruple, displayed with the lifts between the brackets:
`⟪R⟫ F , G ⟪S⟫` is `quadSem F G R S`. -/
scoped notation:50 "⟪" R "⟫ " F:51 " , " G:51 " ⟪" S "⟫" => quadSem F G R S

/-! ## Relational assertion sugar

`⌈…⌉` (and `⌈…⌉ʷ`) also accept a *two-state* program expression, with the
prime convention from the paper: an unprimed variable reads the LEFT state, a
primed one the RIGHT. So

  `⌈y = 1 ∧ y' = 1⌉`   is   `atom (fun s s' => s "y" = 1 ∧ s' "y" = 1)`
  `⌈True⌉`             is   `atom (fun _ _ => True)`

Same grammar as guards otherwise (numerals, `+ - *`, comparisons, `∧ ∨ ¬`),
plus `↑r` to splice a Lean term `r : State → State → Prop` (or, inside an
expression, `↑e` with `e : State → State → Int`). The term forms
`⌈fun s s' => …⌉` keep working — anything the sugar can't parse falls back to
the plain notation from `Assertions.lean`. -/

/-- Two-state program expressions: like `rexp`, but `x` reads the left state
and `x'` the right. -/
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
      -- bare idents are only the constant assertions; anything else falls back
      -- to the term form of `⌈…⌉` (e.g. `⌈r⌉` with `r` a Lean relation).
      if x.getId.eraseMacroScopes == `True then `(True)
      else if x.getId.eraseMacroScopes == `False then `(False)
      else Lean.Macro.throwUnsupported
  | `(rassn% $s $s' ↑$t)    => `(($t : State → State → Prop) $s $s')

scoped syntax "⌈" rassn "⌉" : term
scoped syntax "⌈" rassn "⌉ʷ" : term

macro_rules
  | `(⌈$a:rassn⌉)  => `(atom (fun s s' => rassn% s s' $a))
  | `(⌈$a:rassn⌉ʷ) => `(atomW (fun s s' => rassn% s s' $a))

-- Example
theorem quad_skip (R : RAssn State State) : ⦃R⦄ SKIP ~ SKIP ⦃R⦄ := by
  rw [quad, quadSem]; simp

end RelOL
