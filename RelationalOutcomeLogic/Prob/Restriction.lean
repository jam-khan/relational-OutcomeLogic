import RelationalOutcomeLogic.Prob.CouplingAssertions

/-!
# Restricting and splitting weighted couplings

An observable that agrees at related states partitions a coupling into two actual
joint weights. Each piece retains its exact restricted marginals and its own mass.
Empty pieces are allowed, so impossible branches do not require positive mass.
-/

namespace RelOL.Weight

open scoped ENNReal

variable {α : Type*}

/-- Retain exactly the weight satisfying the predicate, without renormalizing. -/
noncomputable def restrict (μ : Weight α) (P : α → Prop) : Weight α := by
  classical
  exact fun a => if P a then μ a else 0

@[simp] theorem restrict_apply_pos {μ : Weight α} {P : α → Prop} {a : α}
    (ha : P a) : restrict μ P a = μ a := by
  classical
  simp only [restrict, if_pos ha]

@[simp] theorem restrict_apply_neg {μ : Weight α} {P : α → Prop} {a : α}
    (ha : ¬ P a) : restrict μ P a = 0 := by
  classical
  simp only [restrict, if_neg ha]

/-- The two complementary parts add back to the original weight. -/
theorem restrict_add_compl (μ : Weight α) (P : α → Prop) :
    restrict μ P + restrict μ (fun a => ¬ P a) = μ := by
  classical
  funext a
  by_cases ha : P a <;> simp [restrict, ha]

theorem restrict_add (μ ν : Weight α) (P : α → Prop) :
    restrict (μ + ν) P = restrict μ P + restrict ν P := by
  classical
  funext a
  by_cases ha : P a <;> simp [restrict, ha]

theorem restrict_smul (r : ℝ≥0∞) (μ : Weight α) (P : α → Prop) :
    restrict (r • μ) P = r • restrict μ P := by
  classical
  funext a
  by_cases ha : P a <;> simp [restrict, ha]

@[simp] theorem restrict_pure_pos (a : α) {P : α → Prop} (ha : P a) :
    restrict (pure a) P = pure a := by
  classical
  funext b
  by_cases hb : b = a
  · subst b
    exact restrict_apply_pos ha
  · simp [restrict, pure, hb]

@[simp] theorem restrict_pure_neg (a : α) {P : α → Prop} (ha : ¬ P a) :
    restrict (pure a) P = 0 := by
  classical
  funext b
  by_cases hb : b = a
  · subst b
    exact restrict_apply_neg ha
  · simp [restrict, pure, hb]

end RelOL.Weight

namespace RelOL.Prob

variable {α β : Type*}

/-- Restrict an exact joint along predicates that agree on its supporting relation. -/
theorem IsCoupling.restrict {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    {J : Weight (α × β)} (hJ : IsCoupling R μ ν J)
    (P : α → Prop) (Q : β → Prop) (hsync : ∀ a b, R a b → (P a ↔ Q b)) :
    IsCoupling (fun a b => R a b ∧ P a ∧ Q b)
      (Weight.restrict μ P) (Weight.restrict ν Q)
      (Weight.restrict J (fun p => P p.1)) := by
  classical
  have hshift : ∀ a b,
      (if P a then J (a, b) else 0) = if Q b then J (a, b) else 0 := by
    intro a b
    by_cases hzero : J (a, b) = 0
    · simp [hzero]
    · rw [hsync a b (hJ.supported a b hzero)]
  refine ⟨?_, ?_, ?_⟩
  · funext a
    by_cases ha : P a
    · simpa only [margL, Weight.restrict, if_pos ha] using congrFun hJ.margL_eq a
    · simp [margL, Weight.restrict, ha]
  · funext b
    change (∑' a, if P a then J (a, b) else 0) = if Q b then ν b else 0
    simp_rw [hshift]
    by_cases hb : Q b
    · simpa only [if_pos hb, margR] using congrFun hJ.margR_eq b
    · simp [hb]
  · intro a b hab
    have hp : P a := by
      by_contra hn
      simp only [Weight.restrict, if_neg hn, ne_eq, not_true_eq_false] at hab
    have hj : J (a, b) ≠ 0 := by
      simpa only [Weight.restrict, if_pos hp] using hab
    exact ⟨hJ.supported a b hj, hp, (hsync a b (hJ.supported a b hj)).mp hp⟩

theorem Coupled.restrict {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (h : Coupled R μ ν) (P : α → Prop) (Q : β → Prop)
    (hsync : ∀ a b, R a b → (P a ↔ Q b)) :
    Coupled (fun a b => R a b ∧ P a ∧ Q b)
      (Weight.restrict μ P) (Weight.restrict ν Q) := by
  obtain ⟨J, hJ⟩ := h
  exact ⟨_, hJ.restrict P Q hsync⟩

/-- Split a coupling by a shared observable while retaining the exact mass of each piece. -/
theorem Coupled.split_mass {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (h : Coupled R μ ν) (P : α → Prop) (Q : β → Prop)
    (hsync : ∀ a b, R a b → (P a ↔ Q b)) :
    oplus
      (fun μ₁ ν₁ => couple (fun a b => R a b ∧ P a ∧ Q b) μ₁ ν₁ ∧
        massEq (Weight.mass (Weight.restrict μ P))
          (Weight.mass (Weight.restrict μ P)) μ₁ ν₁)
      (fun μ₂ ν₂ => couple (fun a b => R a b ∧ ¬ P a ∧ ¬ Q b) μ₂ ν₂ ∧
        massEq (Weight.mass (Weight.restrict μ (fun a => ¬ P a)))
          (Weight.mass (Weight.restrict μ (fun a => ¬ P a))) μ₂ ν₂) μ ν := by
  obtain ⟨J, hJ⟩ := h
  have hpos : Coupled (fun a b => R a b ∧ P a ∧ Q b)
      (Weight.restrict μ P) (Weight.restrict ν Q) := ⟨_, hJ.restrict P Q hsync⟩
  have hneg : Coupled (fun a b => R a b ∧ ¬ P a ∧ ¬ Q b)
      (Weight.restrict μ (fun a => ¬ P a)) (Weight.restrict ν (fun b => ¬ Q b)) :=
    ⟨_, hJ.restrict (fun a => ¬ P a) (fun b => ¬ Q b)
      (fun a b hab => not_congr (hsync a b hab))⟩
  refine ⟨Weight.restrict μ P, Weight.restrict μ (fun a => ¬ P a),
    Weight.restrict ν Q, Weight.restrict ν (fun b => ¬ Q b),
    (Weight.restrict_add_compl μ P).symm, (Weight.restrict_add_compl ν Q).symm,
    ⟨hpos, rfl, hpos.mass_eq.symm⟩, ⟨hneg, rfl, hneg.mass_eq.symm⟩⟩

end RelOL.Prob
