import RelationalOutcomeLogic.Prob.Rules
import RelationalOutcomeLogic.Prob.Support

/-!
# One-sided exact relational reasoning

Coupling against a point mass requires total mass one on the advancing side.
The one-sided loop rules therefore require losslessness of the whole loop on the
states covered by the precondition. Losslessness of its body alone is insufficient.
-/

namespace RelOL.Prob

variable {α β : Type*}

theorem IsCoupling.swap {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    {J : Weight (α × β)} (h : IsCoupling R μ ν J) :
    IsCoupling (fun b a => R a b) ν μ (fun p => J (p.2, p.1)) where
  margL_eq := h.margR_eq
  margR_eq := h.margL_eq
  supported := fun b a hab => h.supported a b hab

theorem Coupled.swap {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (h : Coupled R μ ν) : Coupled (fun b a => R a b) ν μ := by
  obtain ⟨J, hJ⟩ := h
  exact ⟨fun p => J (p.2, p.1), hJ.swap⟩

/-- Exact coupling against a point mass requires both losslessness and support preservation. -/
theorem Coupled.pure_right_iff {R : α → β → Prop} {μ : Weight α} {b : β} :
    Coupled R μ (Weight.pure b) ↔
      Weight.IsProbability μ ∧ ∀ a ∈ Weight.support μ, R a b := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · change Weight.mass μ = 1
      simpa only [Weight.mass_pure] using h.mass_eq
    · intro a ha
      obtain ⟨b', hb', hab'⟩ := h.support_couple.1 a ha
      rw [Weight.support_pure, Set.mem_singleton_iff] at hb'
      exact hb' ▸ hab'
  · rintro ⟨hprob, hrel⟩
    let J : Weight (α × β) := fun p => if p.2 = b then μ p.1 else 0
    refine ⟨J, ?_, ?_, ?_⟩
    · funext a
      simp [margL, J]
    · funext b'
      by_cases hb : b' = b
      · subst b'
        simpa only [Weight.IsProbability, Weight.mass, margR, J, if_true,
          Weight.pure_apply] using hprob
      · simp [margR, J, Weight.pure, hb]
    · intro a b' hab
      by_cases hb : b' = b
      · subst b'
        exact hrel a (by simpa only [Weight.mem_support_iff, J, if_true] using hab)
      · exact (hab (by simp [J, hb])).elim

theorem Coupled.pure_left_iff {R : α → β → Prop} {a : α} {ν : Weight β} :
    Coupled R (Weight.pure a) ν ↔
      Weight.IsProbability ν ∧ ∀ b ∈ Weight.support ν, R a b := by
  constructor
  · intro h
    exact Coupled.pure_right_iff.mp h.swap
  · intro h
    exact (Coupled.pure_right_iff.mpr h).swap

/-- The command terminates with total mass one on the specified starting states. -/
def LosslessOn (P : α → Prop) (c : Cmd α) : Prop :=
  ∀ a, P a → Weight.IsProbability (sem c a)

/-- A body-preserved predicate holds at every supported finite-loop exit. -/
theorem loopIter_support_invariant (g : α → Prop) (k : α → Weight α) (P : α → Prop)
    (hbody : ∀ s, P s → g s → ∀ t ∈ Weight.support (k s), P t)
    (n : ℕ) (s : α) (hs : P s) (t : α)
    (ht : t ∈ Weight.support (loopIter g k n s)) : P t ∧ ¬g t := by
  induction n generalizing s with
  | zero => simp only [loopIter_zero, Weight.support_zero, Set.mem_empty_iff_false] at ht
  | succ n ih =>
    by_cases hg : g s
    · rw [loopIter_succ_pos hg] at ht
      obtain ⟨u, hu, htu⟩ := (Weight.mem_support_bind_iff _ _ _).mp ht
      exact ih u (hbody s hs hg u hu) htu
    · rw [loopIter_succ_neg hg, Weight.support_pure, Set.mem_singleton_iff] at ht
      exact ht ▸ ⟨hs, hg⟩

/-- Increasing limits introduce no positive-weight output outside the invariant and exit set. -/
theorem loopSem_support_invariant (g : α → Prop) (k : α → Weight α) (P : α → Prop)
    (hbody : ∀ s, P s → g s → ∀ t ∈ Weight.support (k s), P t)
    (s : α) (hs : P s) (t : α) (ht : t ∈ Weight.support (loopSem g k s)) :
    P t ∧ ¬g t := by
  have hpos : 0 < ⨆ n, loopIter g k n s t := by
    simpa only [loopSem, iSup_apply] using (pos_iff_ne_zero.mpr ht)
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hpos
  exact loopIter_support_invariant g k P hbody n s hs t (ne_of_gt hn)

/-- Swapping the programs swaps the relation on both sides of the judgment. -/
theorem quad_couple_symm {R S : α → β → Prop} {c : Cmd α} {d : Cmd β}
    (h : quad (couple R) c d (couple S)) :
    quad (couple (fun b a => R a b)) d c (couple (fun b a => S a b)) :=
  fun μ ν hμν => (h ν μ hμν.swap).swap

/-- A left-only loop must preserve the relation and be lossless on relevant starts. -/
theorem quad_couple_while_left {R : α → β → Prop} (g : α → Prop) {c : Cmd α}
    (hbody : quad (couple (fun a b => R a b ∧ g a)) c .skip (couple R))
    (hloss : LosslessOn (fun a => ∃ b, R a b) (.while g c)) :
    quad (couple R) (.while g c) .skip (couple (fun a b => R a b ∧ ¬g a)) := by
  apply quad_couple_of_pointwise
  intro a b hab
  apply Coupled.pure_right_iff.mpr
  refine ⟨hloss a ⟨b, hab⟩, ?_⟩
  intro t ht
  apply loopSem_support_invariant g (sem c) (fun x => R x b) ?_ a hab t ht
  intro x hxb hg y hy
  have hc : Coupled R (sem c x) (Weight.pure b) := by
    simpa only [semLift_pure, sem_skip, couple] using
      hbody (Weight.pure x) (Weight.pure b) (Coupled.pure ⟨hxb, hg⟩)
  exact (Coupled.pure_right_iff.mp hc).2 y hy

/-- The symmetric one-sided loop rule, with losslessness only on its relevant starts. -/
theorem quad_couple_while_right {R : α → β → Prop} (g : β → Prop) {d : Cmd β}
    (hbody : quad (couple (fun a b => R a b ∧ g b)) .skip d (couple R))
    (hloss : LosslessOn (fun b => ∃ a, R a b) (.while g d)) :
    quad (couple R) .skip (.while g d) (couple (fun a b => R a b ∧ ¬g b)) :=
  quad_couple_symm (quad_couple_while_left g (quad_couple_symm hbody) hloss)

end RelOL.Prob
