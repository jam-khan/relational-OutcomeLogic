import RelationalOutcomeLogic.Algebra.Weight

/-!
# Exact weighted couplings

A coupling is a joint outcome weight with the two specified marginals and support
contained in a relation. The definition applies to arbitrary nonnegative weights;
normalization and finite total mass are not required for the algebra in this file.

Sequencing chooses continuation joints only on the support of the input joint.
It consequently requires related continuations only at related input outcomes.
-/

open scoped ENNReal

namespace RelOL.Prob

variable {α β γ δ : Type*}

noncomputable section

/-- The first marginal of a joint weight. -/
def margL (J : Weight (α × β)) : Weight α := fun a => ∑' b, J (a, b)

/-- The second marginal of a joint weight. -/
def margR (J : Weight (α × β)) : Weight β := fun b => ∑' a, J (a, b)

/-- A particular joint weight witnesses an exact coupling supported in `R`. -/
structure IsCoupling (R : α → β → Prop) (μ : Weight α) (ν : Weight β)
    (J : Weight (α × β)) : Prop where
  margL_eq : margL J = μ
  margR_eq : margR J = ν
  supported : ∀ a b, J (a, b) ≠ 0 → R a b

/-- There exists an exact coupling supported in `R`. -/
def Coupled (R : α → β → Prop) (μ : Weight α) (ν : Weight β) : Prop :=
  ∃ J, IsCoupling R μ ν J

@[simp] theorem margL_zero : margL (0 : Weight (α × β)) = 0 := by
  funext a
  simp [margL]

@[simp] theorem margR_zero : margR (0 : Weight (α × β)) = 0 := by
  funext b
  simp [margR]

theorem margL_add (J K : Weight (α × β)) : margL (J + K) = margL J + margL K := by
  funext a
  exact ENNReal.tsum_add

theorem margR_add (J K : Weight (α × β)) : margR (J + K) = margR J + margR K := by
  funext b
  exact ENNReal.tsum_add

theorem margL_smul (r : ℝ≥0∞) (J : Weight (α × β)) : margL (r • J) = r • margL J := by
  funext a
  exact ENNReal.tsum_mul_left

theorem margR_smul (r : ℝ≥0∞) (J : Weight (α × β)) : margR (r • J) = r • margR J := by
  funext b
  exact ENNReal.tsum_mul_left

@[simp] theorem margL_pure (a : α) (b : β) : margL (Weight.pure (a, b)) = Weight.pure a := by
  classical
  funext a'
  by_cases ha : a' = a <;> simp [margL, Weight.pure, Prod.mk.injEq, ha]

@[simp] theorem margR_pure (a : α) (b : β) : margR (Weight.pure (a, b)) = Weight.pure b := by
  classical
  funext b'
  by_cases hb : b' = b <;> simp [margR, Weight.pure, Prod.mk.injEq, hb]

@[simp] theorem mass_margL (J : Weight (α × β)) : Weight.mass (margL J) = Weight.mass J :=
  ENNReal.tsum_prod'.symm

@[simp] theorem mass_margR (J : Weight (α × β)) : Weight.mass (margR J) = Weight.mass J :=
  ENNReal.tsum_comm.trans ENNReal.tsum_prod'.symm

theorem IsCoupling.mass_eq {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    {J : Weight (α × β)} (h : IsCoupling R μ ν J) : Weight.mass μ = Weight.mass ν := by
  rw [← h.margL_eq, ← h.margR_eq, mass_margL, mass_margR]

theorem Coupled.mass_eq {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (h : Coupled R μ ν) : Weight.mass μ = Weight.mass ν := by
  obtain ⟨J, hJ⟩ := h
  exact hJ.mass_eq

theorem IsCoupling.zero (R : α → β → Prop) : IsCoupling R 0 0 0 where
  margL_eq := margL_zero
  margR_eq := margR_zero
  supported := by simp

theorem Coupled.zero (R : α → β → Prop) : Coupled R 0 0 := ⟨0, IsCoupling.zero R⟩

theorem IsCoupling.pure {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    IsCoupling R (Weight.pure a) (Weight.pure b) (Weight.pure (a, b)) where
  margL_eq := margL_pure a b
  margR_eq := margR_pure a b
  supported := by
    intro a' b' hab
    have hmem : (a', b') ∈ Weight.support (Weight.pure (a, b)) := hab
    rw [Weight.support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    exact h

theorem Coupled.pure {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Coupled R (Weight.pure a) (Weight.pure b) := ⟨_, IsCoupling.pure h⟩

theorem IsCoupling.mono {R S : α → β → Prop} {μ : Weight α} {ν : Weight β}
    {J : Weight (α × β)} (h : IsCoupling R μ ν J) (hRS : ∀ a b, R a b → S a b) :
    IsCoupling S μ ν J where
  margL_eq := h.margL_eq
  margR_eq := h.margR_eq
  supported := fun a b hab => hRS a b (h.supported a b hab)

theorem Coupled.mono {R S : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (h : Coupled R μ ν) (hRS : ∀ a b, R a b → S a b) : Coupled S μ ν := by
  obtain ⟨J, hJ⟩ := h
  exact ⟨J, hJ.mono hRS⟩

theorem IsCoupling.apply_eq_zero_of_not_rel {R : α → β → Prop} {μ : Weight α}
    {ν : Weight β} {J : Weight (α × β)} (h : IsCoupling R μ ν J)
    {a : α} {b : β} (hab : ¬R a b) : J (a, b) = 0 := by
  by_contra hne
  exact hab (h.supported a b hne)

theorem IsCoupling.add {R : α → β → Prop} {μ μ' : Weight α} {ν ν' : Weight β}
    {J K : Weight (α × β)} (hJ : IsCoupling R μ ν J) (hK : IsCoupling R μ' ν' K) :
    IsCoupling R (μ + μ') (ν + ν') (J + K) where
  margL_eq := by rw [margL_add, hJ.margL_eq, hK.margL_eq]
  margR_eq := by rw [margR_add, hJ.margR_eq, hK.margR_eq]
  supported := by
    intro a b hab
    have hmem : (a, b) ∈ Weight.support J ∪ Weight.support K := by
      rw [← Weight.support_add]
      exact hab
    exact hmem.elim (hJ.supported a b) (hK.supported a b)

theorem Coupled.add {R : α → β → Prop} {μ μ' : Weight α} {ν ν' : Weight β}
    (h : Coupled R μ ν) (h' : Coupled R μ' ν') : Coupled R (μ + μ') (ν + ν') := by
  obtain ⟨J, hJ⟩ := h
  obtain ⟨K, hK⟩ := h'
  exact ⟨J + K, hJ.add hK⟩

theorem IsCoupling.smul {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    {J : Weight (α × β)} (h : IsCoupling R μ ν J) (r : ℝ≥0∞) :
    IsCoupling R (r • μ) (r • ν) (r • J) where
  margL_eq := by rw [margL_smul, h.margL_eq]
  margR_eq := by rw [margR_smul, h.margR_eq]
  supported := fun a b hab =>
    h.supported a b ((Weight.mem_support_smul_iff r J (a, b)).mp hab).2

theorem Coupled.smul {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (h : Coupled R μ ν) (r : ℝ≥0∞) : Coupled R (r • μ) (r • ν) := by
  obtain ⟨J, hJ⟩ := h
  exact ⟨r • J, hJ.smul r⟩

open scoped Classical in
/-- The diagonal joint weight, witnessing equality of a weight with itself. -/
def diag (μ : Weight α) : Weight (α × α) := fun p => if p.1 = p.2 then μ p.1 else 0

@[simp] theorem margL_diag (μ : Weight α) : margL (diag μ) = μ := by
  classical
  funext a
  simp [margL, diag]

@[simp] theorem margR_diag (μ : Weight α) : margR (diag μ) = μ := by
  classical
  funext a
  simp [margR, diag]

theorem isCoupling_diag (μ : Weight α) : IsCoupling Eq μ μ (diag μ) where
  margL_eq := margL_diag μ
  margR_eq := margR_diag μ
  supported := by
    intro a b hab
    by_contra hne
    exact hab (by simp [diag, hne])

theorem IsCoupling.eq {μ ν : Weight α} {J : Weight (α × α)}
    (h : IsCoupling Eq μ ν J) : μ = ν := by
  funext a
  have hL : margL J a = J (a, a) :=
    tsum_eq_single a fun b hb => h.apply_eq_zero_of_not_rel hb.symm
  have hR : margR J a = J (a, a) :=
    tsum_eq_single a fun b hb => h.apply_eq_zero_of_not_rel hb
  rw [← h.margL_eq, ← h.margR_eq, hL, hR]

@[simp] theorem coupled_eq_iff {μ ν : Weight α} : Coupled Eq μ ν ↔ μ = ν := by
  constructor
  · rintro ⟨J, hJ⟩
    exact hJ.eq
  · rintro rfl
    exact ⟨diag μ, isCoupling_diag μ⟩

/-- Marginalization commutes with sequencing a joint weight. -/
theorem margL_bind (J : Weight (α × β)) (K : α × β → Weight (γ × δ)) :
    margL (Weight.bind J K) = Weight.bind J (fun p => margL (K p)) := by
  funext c
  change (∑' d, ∑' p, J p * K p (c, d)) = ∑' p, J p * ∑' d, K p (c, d)
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

/-- Marginalization commutes with sequencing a joint weight. -/
theorem margR_bind (J : Weight (α × β)) (K : α × β → Weight (γ × δ)) :
    margR (Weight.bind J K) = Weight.bind J (fun p => margR (K p)) := by
  funext d
  change (∑' c, ∑' p, J p * K p (c, d)) = ∑' p, J p * ∑' c, K p (c, d)
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

theorem bind_fst (J : Weight (α × β)) (k : α → Weight γ) :
    Weight.bind J (fun p => k p.1) = Weight.bind (margL J) k := by
  funext c
  simp only [Weight.bind, margL, ENNReal.tsum_prod', ENNReal.tsum_mul_right]

theorem bind_snd (J : Weight (α × β)) (k : β → Weight γ) :
    Weight.bind J (fun p => k p.2) = Weight.bind (margR J) k := by
  funext c
  simp only [Weight.bind, margR, ENNReal.tsum_prod']
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_right]

/-- Joint sequencing needs continuation couplings only on the input joint's support. -/
theorem IsCoupling.bind {R : α → β → Prop} {S : γ → δ → Prop}
    {μ : Weight α} {ν : Weight β} {J : Weight (α × β)}
    (hJ : IsCoupling R μ ν J) (k : α → Weight γ) (l : β → Weight δ)
    (K : α × β → Weight (γ × δ))
    (hK : ∀ p ∈ Weight.support J, IsCoupling S (k p.1) (l p.2) (K p)) :
    IsCoupling S (Weight.bind μ k) (Weight.bind ν l) (Weight.bind J K) where
  margL_eq := by
    calc
      margL (Weight.bind J K) = Weight.bind J (fun p => margL (K p)) := margL_bind J K
      _ = Weight.bind J (fun p => k p.1) :=
        Weight.bind_congr_on_support J fun p hp => (hK p hp).margL_eq
      _ = Weight.bind (margL J) k := bind_fst J k
      _ = Weight.bind μ k := by rw [hJ.margL_eq]
  margR_eq := by
    calc
      margR (Weight.bind J K) = Weight.bind J (fun p => margR (K p)) := margR_bind J K
      _ = Weight.bind J (fun p => l p.2) :=
        Weight.bind_congr_on_support J fun p hp => (hK p hp).margR_eq
      _ = Weight.bind (margR J) l := bind_snd J l
      _ = Weight.bind ν l := by rw [hJ.margR_eq]
  supported := by
    intro c d hcd
    obtain ⟨p, hp, hKp⟩ := (Weight.mem_support_bind_iff J K (c, d)).mp hcd
    exact (hK p hp).supported c d hKp

/-- Exact couplings compose along related continuation programs. -/
theorem Coupled.bind {R : α → β → Prop} {S : γ → δ → Prop}
    {μ : Weight α} {ν : Weight β} (h : Coupled R μ ν)
    (k : α → Weight γ) (l : β → Weight δ)
    (hkl : ∀ a b, R a b → Coupled S (k a) (l b)) :
    Coupled S (Weight.bind μ k) (Weight.bind ν l) := by
  classical
  obtain ⟨J, hJ⟩ := h
  let K : α × β → Weight (γ × δ) := fun p =>
    if hp : R p.1 p.2 then (hkl p.1 p.2 hp).choose else 0
  refine ⟨Weight.bind J K, hJ.bind k l K ?_⟩
  intro p hp
  have hR : R p.1 p.2 := hJ.supported p.1 p.2 hp
  dsimp only [K]
  rw [dif_pos hR]
  exact (hkl p.1 p.2 hR).choose_spec

end

end RelOL.Prob
