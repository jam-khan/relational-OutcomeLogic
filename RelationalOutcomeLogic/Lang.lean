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
  simp
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
      exact ih s
      grind

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
