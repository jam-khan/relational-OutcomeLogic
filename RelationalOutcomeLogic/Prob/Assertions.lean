import RelationalOutcomeLogic.Algebra.Weight

/-!
# Assertions over pairs of weighted outcomes

Outcome splitting uses pointwise addition, so overlapping pieces contribute their
weights separately. Product atoms constrain supports; mass assertions record the
quantitative information that support alone loses. These are assertions over raw
weights and do not impose a subprobability bound implicitly.
-/

namespace RelOL.Prob

open scoped ENNReal

variable {α β : Type*}

/-- A predicate over a pair of weighted outcomes. -/
abbrev RAssn (α β : Type*) := Weight α → Weight β → Prop

def entail (P Q : RAssn α β) : Prop := ∀ μ ν, P μ ν → Q μ ν

def rtop : RAssn α β := fun _ _ => True

def rbot : RAssn α β := fun _ _ => False

/-- The additive unit: neither side has a terminating outcome. -/
def emp : RAssn α β := fun μ ν => μ = 0 ∧ ν = 0

/-- Exactly this pair of weights, including their quantitative information. -/
def exactly (μ₀ : Weight α) (ν₀ : Weight β) : RAssn α β :=
  fun μ ν => μ = μ₀ ∧ ν = ν₀

/-- Both sides have positive total weight. -/
def positive : RAssn α β := fun μ ν => 0 < Weight.mass μ ∧ 0 < Weight.mass ν

/-- Prescribed total weights, with no implicit normalization assumption. -/
def massEq (p q : ℝ≥0∞) : RAssn α β :=
  fun μ ν => Weight.mass μ = p ∧ Weight.mass ν = q

/-- Every pair of supported outcomes is related; either zero side makes this vacuous. -/
def atomW (R : α → β → Prop) : RAssn α β :=
  fun μ ν => ∀ a ∈ Weight.support μ, ∀ b ∈ Weight.support ν, R a b

/-- A product atom requiring a positive weight on each side. This is not a coupling. -/
def atom (R : α → β → Prop) : RAssn α β :=
  fun μ ν => positive μ ν ∧ atomW R μ ν

/-- Additive outcome splitting; each branch receives its own weight on both sides. -/
def oplus (P Q : RAssn α β) : RAssn α β :=
  fun μ ν => ∃ μ₁ μ₂ ν₁ ν₂,
    μ = μ₁ + μ₂ ∧ ν = ν₁ + ν₂ ∧ P μ₁ ν₁ ∧ Q μ₂ ν₂

def disj (P Q : RAssn α β) : RAssn α β := fun μ ν => P μ ν ∨ Q μ ν

/-- The image of an assertion under a common scalar on both sides. -/
def scale (r : ℝ≥0∞) (P : RAssn α β) : RAssn α β :=
  fun μ ν => ∃ μ₀ ν₀, μ = r • μ₀ ∧ ν = r • ν₀ ∧ P μ₀ ν₀

theorem entail_refl (P : RAssn α β) : entail P P := fun _ _ h => h

theorem entail_trans {P Q S : RAssn α β} (hPQ : entail P Q) (hQS : entail Q S) :
    entail P S := fun μ ν h => hQS μ ν (hPQ μ ν h)

theorem entail_rtop (P : RAssn α β) : entail P rtop := fun _ _ _ => trivial

theorem rbot_entail (P : RAssn α β) : entail rbot P := fun _ _ h => h.elim

@[simp] theorem exactly_self (μ : Weight α) (ν : Weight β) : exactly μ ν μ ν :=
  ⟨rfl, rfl⟩

@[simp] theorem emp_zero : emp (0 : Weight α) (0 : Weight β) := ⟨rfl, rfl⟩

@[simp] theorem positive_iff_ne_zero (μ : Weight α) (ν : Weight β) :
    positive μ ν ↔ μ ≠ 0 ∧ ν ≠ 0 := by
  simp [positive, pos_iff_ne_zero]

@[simp] theorem massEq_zero_zero : (massEq 0 0 : RAssn α β) = emp := by
  funext μ ν
  apply propext
  simp [massEq, emp]

theorem massEq_positive {p q : ℝ≥0∞} (hp : 0 < p) (hq : 0 < q) :
    entail (massEq p q : RAssn α β) positive := by
  rintro μ ν ⟨hμ, hν⟩
  exact ⟨hμ.symm ▸ hp, hν.symm ▸ hq⟩

@[simp] theorem atomW_zero_left (R : α → β → Prop) (ν : Weight β) :
    atomW R 0 ν := by
  simp [atomW]

@[simp] theorem atomW_zero_right (R : α → β → Prop) (μ : Weight α) :
    atomW R μ 0 := by
  simp [atomW]

@[simp] theorem not_atom_zero_left (R : α → β → Prop) (ν : Weight β) :
    ¬ atom R 0 ν := by
  simp [atom, positive]

@[simp] theorem not_atom_zero_right (R : α → β → Prop) (μ : Weight α) :
    ¬ atom R μ 0 := by
  simp [atom, positive]

@[simp] theorem atomW_pure_iff (R : α → β → Prop) (a : α) (b : β) :
    atomW R (Weight.pure a) (Weight.pure b) ↔ R a b := by
  simp [atomW]

@[simp] theorem atom_pure_iff (R : α → β → Prop) (a : α) (b : β) :
    atom R (Weight.pure a) (Weight.pure b) ↔ R a b := by
  simp [atom, positive]

theorem atomW_of_atom (R : α → β → Prop) : entail (atom R) (atomW R) :=
  fun _ _ h => h.2

theorem atomW_mono {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) :
    entail (atomW R) (atomW S) :=
  fun _ _ h a ha b hb => hRS a b (h a ha b hb)

theorem atom_mono {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) :
    entail (atom R) (atom S) :=
  fun μ ν h => ⟨h.1, atomW_mono hRS μ ν h.2⟩

theorem oplus_intro {P Q : RAssn α β} {μ₁ μ₂ : Weight α} {ν₁ ν₂ : Weight β}
    (hP : P μ₁ ν₁) (hQ : Q μ₂ ν₂) : oplus P Q (μ₁ + μ₂) (ν₁ + ν₂) :=
  ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, hP, hQ⟩

theorem oplus_mono {P P' Q Q' : RAssn α β} (hP : entail P P') (hQ : entail Q Q') :
    entail (oplus P Q) (oplus P' Q') := by
  rintro _ _ ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁, h₂⟩
  exact oplus_intro (hP _ _ h₁) (hQ _ _ h₂)

theorem oplus_comm (P Q : RAssn α β) : oplus P Q = oplus Q P := by
  funext μ ν
  apply propext
  constructor <;> rintro ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁, h₂⟩ <;>
    exact ⟨μ₂, μ₁, ν₂, ν₁, add_comm _ _, add_comm _ _, h₂, h₁⟩

theorem oplus_assoc (P Q S : RAssn α β) :
    oplus (oplus P Q) S = oplus P (oplus Q S) := by
  funext μ ν
  apply propext
  constructor
  · rintro ⟨μ₁₂, μ₃, ν₁₂, ν₃, rfl, rfl,
      ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁, h₂⟩, h₃⟩
    exact ⟨μ₁, μ₂ + μ₃, ν₁, ν₂ + ν₃, add_assoc _ _ _, add_assoc _ _ _, h₁,
      oplus_intro h₂ h₃⟩
  · rintro ⟨μ₁, μ₂₃, ν₁, ν₂₃, rfl, rfl, h₁,
      ⟨μ₂, μ₃, ν₂, ν₃, rfl, rfl, h₂, h₃⟩⟩
    exact ⟨μ₁ + μ₂, μ₃, ν₁ + ν₂, ν₃, (add_assoc _ _ _).symm,
      (add_assoc _ _ _).symm, oplus_intro h₁ h₂, h₃⟩

@[simp] theorem oplus_emp (P : RAssn α β) : oplus P emp = P := by
  funext μ ν
  apply propext
  constructor
  · rintro ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, hP, rfl, rfl⟩
    simpa using hP
  · intro hP
    exact ⟨μ, 0, ν, 0, (add_zero _).symm, (add_zero _).symm, hP, rfl, rfl⟩

@[simp] theorem emp_oplus (P : RAssn α β) : oplus emp P = P := by
  rw [oplus_comm, oplus_emp]

@[simp] theorem oplus_rbot (P : RAssn α β) : oplus P rbot = rbot := by
  funext μ ν
  apply propext
  simp [oplus, rbot]

@[simp] theorem rbot_oplus (P : RAssn α β) : oplus rbot P = rbot := by
  rw [oplus_comm, oplus_rbot]

theorem oplus_left_top {P : RAssn α β} {μ : Weight α} {ν : Weight β}
    (hP : P μ ν) : oplus P rtop μ ν :=
  ⟨μ, 0, ν, 0, (add_zero _).symm, (add_zero _).symm, hP, trivial⟩

theorem oplus_exactly (μ₁ μ₂ : Weight α) (ν₁ ν₂ : Weight β) :
    oplus (exactly μ₁ ν₁) (exactly μ₂ ν₂) = exactly (μ₁ + μ₂) (ν₁ + ν₂) := by
  funext μ ν
  apply propext
  constructor
  · rintro ⟨_, _, _, _, rfl, rfl, h₁, h₂⟩
    rcases h₁ with ⟨rfl, rfl⟩
    rcases h₂ with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact oplus_intro (exactly_self _ _) (exactly_self _ _)

/-- Splitting adds the prescribed masses; it does not duplicate them for free. -/
theorem oplus_massEq (p q p' q' : ℝ≥0∞) :
    entail (oplus (massEq p q) (massEq p' q') : RAssn α β)
      (massEq (p + p') (q + q')) := by
  rintro _ _ ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁, h₂⟩
  exact ⟨(Weight.mass_add _ _).trans (congrArg₂ (· + ·) h₁.1 h₂.1),
    (Weight.mass_add _ _).trans (congrArg₂ (· + ·) h₁.2 h₂.2)⟩

theorem oplus_disj_left (P Q S : RAssn α β) :
    oplus (disj P Q) S = disj (oplus P S) (oplus Q S) := by
  funext μ ν
  apply propext
  constructor
  · rintro ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁ | h₁, h₂⟩
    · exact Or.inl (oplus_intro h₁ h₂)
    · exact Or.inr (oplus_intro h₁ h₂)
  · rintro (⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁, h₂⟩ |
      ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁, h₂⟩)
    · exact oplus_intro (Or.inl h₁) h₂
    · exact oplus_intro (Or.inr h₁) h₂

theorem oplus_disj_right (P Q S : RAssn α β) :
    oplus P (disj Q S) = disj (oplus P Q) (oplus P S) := by
  rw [oplus_comm P, oplus_disj_left, oplus_comm Q, oplus_comm S]

theorem scale_intro (r : ℝ≥0∞) {P : RAssn α β} {μ : Weight α} {ν : Weight β}
    (hP : P μ ν) : scale r P (r • μ) (r • ν) := ⟨μ, ν, rfl, rfl, hP⟩

theorem scale_mono (r : ℝ≥0∞) {P Q : RAssn α β} (h : entail P Q) :
    entail (scale r P) (scale r Q) := by
  rintro _ _ ⟨μ, ν, rfl, rfl, hP⟩
  exact scale_intro r (h μ ν hP)

@[simp] theorem scale_one (P : RAssn α β) : scale 1 P = P := by
  funext μ ν
  apply propext
  simp [scale]

theorem scale_massEq (r p q : ℝ≥0∞) :
    entail (scale r (massEq p q) : RAssn α β) (massEq (r * p) (r * q)) := by
  rintro _ _ ⟨μ, ν, rfl, rfl, hμ, hν⟩
  exact ⟨(Weight.mass_smul _ _).trans (congrArg (r * ·) hμ),
    (Weight.mass_smul _ _).trans (congrArg (r * ·) hν)⟩

end RelOL.Prob
