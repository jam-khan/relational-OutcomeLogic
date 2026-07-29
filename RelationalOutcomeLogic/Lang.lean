import Mathlib.Logic.Function.Basic
import RelationalOutcomeLogic.Basic
import RelationalOutcomeLogic.Kleisli

/-!
# The homogeneous language and its powerset semantics

A nondeterministic imperative language with while-loops, with denotational
semantics into `Set State`, per the Outcome Logic powerset instance. Loops are
Kleene unions of fuel-indexed iterates (`loopSem` from the Kleisli engine),
provably the least fixed point of the loop functional (`sem_while_eq_lfp`);
divergence is the empty outcome set.

Guards are propositional (`State → Prop`) and `sem` is classical/`noncomputable`:
example proofs close by simp *rewriting* (`sem_ite_pos` with an `omega`-provable
guard), never by kernel computation, so decidability buys nothing here.
-/

namespace RelOL

attribute [local instance] Classical.propDecidable

/-- Commands of the homogeneous language. -/
inductive Cmd where
  | skip
  | assign (x : String) (e : State → Int)
  | seq (c₁ c₂ : Cmd)
  | ite (b : State → Prop) (c₁ c₂ : Cmd)
  | choice (c₁ c₂ : Cmd)
  | while (b : State → Prop) (c : Cmd)

open Classical in
/-- Denotational semantics: the set of possible final states. -/
noncomputable def sem : Cmd → State → Set State
  | .skip, s => {s}
  | .assign x e, s => {Function.update s x (e s)}
  | .seq c₁ c₂, s => kleisli (sem c₂) (sem c₁ s)
  | .ite b c₁ c₂, s => if b s then sem c₁ s else sem c₂ s
  | .choice c₁ c₂, s => sem c₁ s ∪ sem c₂ s
  | .while b c, s => loopSem b (sem c) s

/-- Lift of the semantics to sets of initial states (Kleisli extension). -/
noncomputable def semLift (c : Cmd) : Set State → Set State := kleisli (sem c)

/-! ## Computation kit -/

@[simp] theorem sem_skip (s : State) : sem .skip s = {s} := rfl

@[simp] theorem sem_assign (x : String) (e : State → Int) (s : State) :
    sem (.assign x e) s = {Function.update s x (e s)} := rfl

theorem sem_seq (c₁ c₂ : Cmd) (s : State) :
    sem (.seq c₁ c₂) s = kleisli (sem c₂) (sem c₁ s) := rfl

@[simp] theorem sem_choice (c₁ c₂ : Cmd) (s : State) :
    sem (.choice c₁ c₂) s = sem c₁ s ∪ sem c₂ s := rfl

theorem sem_ite_pos {b : State → Prop} {s : State} (h : b s) (c₁ c₂ : Cmd) :
    sem (.ite b c₁ c₂) s = sem c₁ s := by
  simp only [sem, if_pos h]

theorem sem_ite_neg {b : State → Prop} {s : State} (h : ¬ b s) (c₁ c₂ : Cmd) :
    sem (.ite b c₁ c₂) s = sem c₂ s := by
  simp only [sem, if_neg h]

/-! ## Loops -/

theorem sem_while (b : State → Prop) (c : Cmd) (s : State) :
    sem (.while b c) s = loopSem b (sem c) s := rfl

/-- The fixpoint unrolling equation for `while`. -/
theorem sem_while_unfold (b : State → Prop) (c : Cmd) (s : State) :
    sem (.while b c) s
      = if b s then semLift (.while b c) (sem c s) else {s} :=
  loopSem_unfold b (sem c) s

theorem sem_while_pos {b : State → Prop} {s : State} (h : b s) (c : Cmd) :
    sem (.while b c) s = semLift (.while b c) (sem c s) := by
  rw [sem_while_unfold, if_pos h]

theorem sem_while_neg {b : State → Prop} {s : State} (h : ¬ b s) (c : Cmd) :
    sem (.while b c) s = {s} := by
  rw [sem_while_unfold, if_neg h]

/-- Every fuel-indexed truncation under-approximates the loop: the engine of
the fuel-based While rules. -/
theorem loopIter_subset_sem (b : State → Prop) (c : Cmd) (n : ℕ) (s : State) :
    loopIter b (sem c) n s ⊆ sem (.while b c) s :=
  loopIter_subset_loopSem b (sem c) n s

/-- `while` is the least fixed point of its characteristic functional
(Knaster–Tarski reading; regression pin for the loop semantics). -/
theorem sem_while_eq_lfp (b : State → Prop) (c : Cmd) :
    sem (.while b c) = OrderHom.lfp (loopHom b (sem c)) := by
  funext s
  rw [sem_while, loopSem_eq_lfp]

/-- Divergence is the empty outcome set. -/
theorem sem_while_true_skip (s : State) :
    sem (.while (fun _ => True) .skip) s = ∅ := by
  rw [sem_while]
  refine Set.eq_empty_of_subset_empty (Set.iUnion_subset fun n => ?_)
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [loopIter_succ_pos trivial, sem_skip, kleisli_singleton]
    exact ih s

/-! ## Loop-free fragment -/

/-- Structurally loop-free commands: the fragment where every command is total. -/
@[simp] def LoopFree : Cmd → Prop
  | .skip => True
  | .assign _ _ => True
  | .seq c₁ c₂ => LoopFree c₁ ∧ LoopFree c₂
  | .ite _ c₁ c₂ => LoopFree c₁ ∧ LoopFree c₂
  | .choice c₁ c₂ => LoopFree c₁ ∧ LoopFree c₂
  | .while _ _ => False

/-- The loop-free fragment never diverges: every command has at least one
outcome from every state. -/
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

/-! ## Lift kit (the execution-model laws, inherited from `kleisli`) -/

@[simp] theorem mem_semLift {c : Cmd} {m : Set State} {t : State} :
    t ∈ semLift c m ↔ ∃ s ∈ m, t ∈ sem c s := mem_kleisli

@[simp] theorem semLift_empty (c : Cmd) : semLift c ∅ = ∅ := kleisli_empty _

@[simp] theorem semLift_singleton (c : Cmd) (s : State) : semLift c {s} = sem c s :=
  kleisli_singleton _ _

@[simp] theorem semLift_skip (m : Set State) : semLift .skip m = m := by
  ext t; simp [semLift]

theorem semLift_union (c : Cmd) (m₁ m₂ : Set State) :
    semLift c (m₁ ∪ m₂) = semLift c m₁ ∪ semLift c m₂ :=
  kleisli_union _ m₁ m₂

theorem semLift_seq (c₁ c₂ : Cmd) (m : Set State) :
    semLift (.seq c₁ c₂) m = semLift c₂ (semLift c₁ m) :=
  (kleisli_comp (sem c₁) (sem c₂) m).symm

theorem semLift_choice (c₁ c₂ : Cmd) (m : Set State) :
    semLift (.choice c₁ c₂) m = semLift c₁ m ∪ semLift c₂ m :=
  kleisli_pointwise_union (sem c₁) (sem c₂) m

theorem semLift_nonempty {c : Cmd} (hc : LoopFree c) {m : Set State} (hm : m.Nonempty) :
    (semLift c m).Nonempty :=
  kleisli_nonempty hm fun s _ => sem_nonempty hc s

/-! ## Set-level computation lemmas for the structured rules

Conditionals and loops act uniformly on an outcome set once the guard is
decided uniformly on it; these are the semantic facts behind the `If` and
`While` proof rules. -/

theorem semLift_assign (x : String) (e : State → Int) (m : Set State) :
    semLift (.assign x e) m = (fun s => Function.update s x (e s)) '' m := by
  ext t
  simp [Set.mem_image, eq_comm]

theorem semLift_ite_pos {b : State → Prop} {m : Set State} (h : ∀ s ∈ m, b s)
    (c₁ c₂ : Cmd) : semLift (.ite b c₁ c₂) m = semLift c₁ m :=
  kleisli_congr fun s hs => sem_ite_pos (h s hs) c₁ c₂

theorem semLift_ite_neg {b : State → Prop} {m : Set State} (h : ∀ s ∈ m, ¬ b s)
    (c₁ c₂ : Cmd) : semLift (.ite b c₁ c₂) m = semLift c₂ m :=
  kleisli_congr fun s hs => sem_ite_neg (h s hs) c₁ c₂

/-- On a set where the guard fails uniformly, the loop is the identity. -/
theorem semLift_while_neg {b : State → Prop} {m : Set State} (h : ∀ s ∈ m, ¬ b s)
    (c : Cmd) : semLift (.while b c) m = m := by
  rw [semLift, kleisli_congr fun s hs => sem_while_neg (h s hs) c]
  ext t
  simp [mem_kleisli]

/-- On a set where the guard holds uniformly, the loop runs its body once and
re-enters. -/
theorem semLift_while_pos {b : State → Prop} {m : Set State} (h : ∀ s ∈ m, b s)
    (c : Cmd) : semLift (.while b c) m = semLift (.while b c) (semLift c m) := by
  rw [semLift, kleisli_congr fun s hs => sem_while_pos (h s hs) c]
  rw [semLift, semLift, kleisli_comp]

/-- `while b c` and its one-step unrolling are semantically equal — the
command-level fixpoint equation. -/
theorem sem_while_eq_unroll (b : State → Prop) (c : Cmd) :
    sem (.while b c) = sem (.ite b (.seq c (.while b c)) .skip) := by
  funext s
  by_cases h : b s
  · rw [sem_while_pos h, sem_ite_pos h, sem_seq]; rfl
  · rw [sem_while_neg h, sem_ite_neg h, sem_skip]

end RelOL
