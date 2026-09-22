import RelationalOutcomeLogic.Prob.Semantics.Loop
import RelationalOutcomeLogic.Prob.Logic.Judgment

/-!
# A probabilistic while-language

Commands act on a generic state type. Sampling primitives carry a proof that each
sample distribution has mass one. Sequencing and loops can lose mass only through
nontermination. The lifted semantics also accepts arbitrary raw input weights;
subprobability bounds are preserved rather than built into the carrier.

There is no unrestricted additive choice command. Probabilistic choice can be
expressed through a normalized sampling primitive.
-/

namespace RelOL.Prob

open scoped ENNReal

attribute [local instance] Classical.propDecidable

inductive Cmd (α : Type*) where
  | skip
  | assign (f : α → α)
  | sample (k : α → Weight α) (normalized : ∀ a, Weight.IsProbability (k a))
  | seq (c d : Cmd α)
  | ite (g : α → Prop) (c d : Cmd α)
  | while (g : α → Prop) (c : Cmd α)

variable {α β : Type*}

noncomputable section

/-- A distribution of terminating final states; missing mass represents divergence. -/
def sem : Cmd α → α → Weight α
  | .skip, s => Weight.pure s
  | .assign f, s => Weight.pure (f s)
  | .sample k _, s => k s
  | .seq c d, s => Weight.bind (sem c s) (sem d)
  | .ite g c d, s => if g s then sem c s else sem d s
  | .while g c, s => loopSem g (sem c) s

/-- Execute a command on a weighted input distribution. -/
def semLift (c : Cmd α) (μ : Weight α) : Weight α := Weight.bind μ (sem c)

/-- A relational judgment, permitting different state types on the two sides. -/
def quad (P : RAssn α β) (c : Cmd α) (d : Cmd β) (Q : RAssn α β) : Prop :=
  quadSem (semLift c) (semLift d) P Q

@[simp] theorem sem_skip (s : α) : sem .skip s = Weight.pure s := rfl

@[simp] theorem sem_assign (f : α → α) (s : α) :
    sem (.assign f) s = Weight.pure (f s) := rfl

@[simp] theorem sem_sample (k : α → Weight α) (hk : ∀ s, Weight.IsProbability (k s))
    (s : α) : sem (.sample k hk) s = k s := rfl

@[simp] theorem sem_seq (c d : Cmd α) (s : α) :
    sem (.seq c d) s = Weight.bind (sem c s) (sem d) := rfl

@[simp] theorem sem_ite_pos {g : α → Prop} {s : α} (h : g s) (c d : Cmd α) :
    sem (.ite g c d) s = sem c s := by
  simp only [sem, if_pos h]

@[simp] theorem sem_ite_neg {g : α → Prop} {s : α} (h : ¬ g s) (c d : Cmd α) :
    sem (.ite g c d) s = sem d s := by
  simp only [sem, if_neg h]

@[simp] theorem sem_while (g : α → Prop) (c : Cmd α) (s : α) :
    sem (.while g c) s = loopSem g (sem c) s := rfl

@[simp] theorem semLift_pure (c : Cmd α) (s : α) :
    semLift c (Weight.pure s) = sem c s := Weight.pure_bind s (sem c)

@[simp] theorem semLift_skip (μ : Weight α) : semLift .skip μ = μ := Weight.bind_pure μ

@[simp] theorem semLift_seq (c d : Cmd α) (μ : Weight α) :
    semLift (.seq c d) μ = semLift d (semLift c μ) :=
  (Weight.bind_assoc μ (sem c) (sem d)).symm

@[simp] theorem semLift_zero (c : Cmd α) : semLift c 0 = 0 := Weight.zero_bind (sem c)

theorem semLift_add (c : Cmd α) (μ ν : Weight α) :
    semLift c (μ + ν) = semLift c μ + semLift c ν := Weight.add_bind μ ν (sem c)

theorem semLift_smul (c : Cmd α) (r : ℝ≥0∞) (μ : Weight α) :
    semLift c (r • μ) = r • semLift c μ := Weight.smul_bind r μ (sem c)

/-- Every command produces a subprobability from a single starting state. -/
theorem sem_isSubprob (c : Cmd α) (s : α) : Weight.IsSubprob (sem c s) := by
  induction c generalizing s with
  | skip => exact Weight.isSubprob_pure s
  | assign f => exact Weight.isSubprob_pure (f s)
  | sample k hk => exact (hk s).isSubprob
  | seq c d ihc ihd => exact (ihc s).bind ihd
  | ite g c d ihc ihd =>
    by_cases h : g s
    · simpa only [sem_ite_pos h] using ihc s
    · simpa only [sem_ite_neg h] using ihd s
  | «while» g c ih => exact loopSem_isSubprob g (sem c) ih s

/-- A program cannot create additional total mass from arbitrary input weights. -/
theorem semLift_mass_le (c : Cmd α) (μ : Weight α) :
    Weight.mass (semLift c μ) ≤ Weight.mass μ :=
  Weight.mass_bind_le_mass μ (sem c) fun s _ => sem_isSubprob c s

theorem semLift_isSubprob (c : Cmd α) {μ : Weight α} (hμ : Weight.IsSubprob μ) :
    Weight.IsSubprob (semLift c μ) := hμ.bind (sem_isSubprob c)

/-- The syntactic fragment whose commands contain no while-loop. -/
@[simp] def LoopFree : Cmd α → Prop
  | .skip => True
  | .assign _ => True
  | .sample _ _ => True
  | .seq c d => LoopFree c ∧ LoopFree d
  | .ite _ c d => LoopFree c ∧ LoopFree d
  | .while _ _ => False

/-- Normalized primitives ensure that loop-free commands preserve all mass. -/
theorem sem_isProbability {c : Cmd α} (hc : LoopFree c) (s : α) :
    Weight.IsProbability (sem c s) := by
  induction c generalizing s with
  | skip => exact Weight.isProbability_pure s
  | assign f => exact Weight.isProbability_pure (f s)
  | sample k hk => exact hk s
  | seq c d ihc ihd => exact (ihc hc.1 s).bind (ihd hc.2)
  | ite g c d ihc ihd =>
    by_cases h : g s
    · simpa only [sem_ite_pos h] using ihc hc.1 s
    · simpa only [sem_ite_neg h] using ihd hc.2 s
  | «while» _ _ _ => exact hc.elim

theorem semLift_mass_eq {c : Cmd α} (hc : LoopFree c) (μ : Weight α) :
    Weight.mass (semLift c μ) = Weight.mass μ :=
  Weight.mass_bind_of_isProbability μ (sem c) fun s _ => sem_isProbability hc s

theorem semLift_isProbability {c : Cmd α} (hc : LoopFree c) {μ : Weight α}
    (hμ : Weight.IsProbability μ) : Weight.IsProbability (semLift c μ) :=
  hμ.bind (sem_isProbability hc)

/-- Unfolding executes the body once when the guard holds. -/
theorem sem_while_unfold (g : α → Prop) (c : Cmd α) (s : α) :
    sem (.while g c) s =
      if g s then semLift (.while g c) (sem c s) else Weight.pure s :=
  loopSem_unfold g (sem c) s

theorem sem_while_pos {g : α → Prop} {s : α} (h : g s) (c : Cmd α) :
    sem (.while g c) s = semLift (.while g c) (sem c s) := by
  rw [sem_while_unfold, if_pos h]

theorem sem_while_neg {g : α → Prop} {s : α} (h : ¬ g s) (c : Cmd α) :
    sem (.while g c) s = Weight.pure s := by
  rw [sem_while_unfold, if_neg h]

@[simp] theorem sem_while_false (c : Cmd α) (s : α) :
    sem (.while (fun _ => False) c) s = Weight.pure s :=
  sem_while_neg (fun h => h) c

@[simp] theorem sem_while_true (c : Cmd α) (s : α) :
    sem (.while (fun _ => True) c) s = 0 := congrFun (loopSem_true (sem c)) s

end

end RelOL.Prob
