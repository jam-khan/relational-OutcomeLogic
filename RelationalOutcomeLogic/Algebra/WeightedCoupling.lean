import RelationalOutcomeLogic.Algebra.Weighted

/-!
# Exact couplings over a summation semiring

Marginals sum out one component of a joint weight. Their exact equations and
the supported sequencing rule are proved uniformly, without positivity or
commutative multiplication assumptions.
-/

universe u v

namespace RelOL.Algebra.Weighted

variable {K : Type v} [Semiring K] [SummationSemiring.{u} K]
variable {α β γ δ : Type u}

open SummationSemiring

noncomputable section

def margL (J : Weight K (α × β)) : Weight K α := fun a => sum (fun b => J (a, b))
def margR (J : Weight K (α × β)) : Weight K β := fun b => sum (fun a => J (a, b))

structure IsCoupling (R : α → β → Prop) (μ : Weight K α) (ν : Weight K β)
    (J : Weight K (α × β)) : Prop where
  margL_eq : margL J = μ
  margR_eq : margR J = ν
  supported : ∀ a b, J (a, b) ≠ 0 → R a b

def Coupled (R : α → β → Prop) (μ : Weight K α) (ν : Weight K β) : Prop :=
  ∃ J, IsCoupling R μ ν J

@[simp] theorem margL_zero : margL (0 : Weight K (α × β)) = 0 := by
  funext a
  exact sum_zero

@[simp] theorem margR_zero : margR (0 : Weight K (α × β)) = 0 := by
  funext b
  exact sum_zero

theorem margL_add (J H : Weight K (α × β)) : margL (J + H) = margL J + margL H := by
  funext a
  exact sum_add _ _

theorem margR_add (J H : Weight K (α × β)) : margR (J + H) = margR J + margR H := by
  funext b
  exact sum_add _ _

theorem margL_scale (r : K) (J : Weight K (α × β)) : margL (scale r J) = scale r (margL J) := by
  funext a
  exact mul_sum r _

theorem margR_scale (r : K) (J : Weight K (α × β)) : margR (scale r J) = scale r (margR J) := by
  funext b
  exact mul_sum r _

@[simp] theorem margL_pure (a : α) (b : β) :
    margL (pure (a, b) : Weight K (α × β)) = pure a := by
  classical
  funext a'
  by_cases ha : a' = a
  · subst a'
    simp only [margL, pure, Prod.mk.injEq, true_and, ite_true]
    exact sum_single b 1
  · simp only [margL, pure, Prod.mk.injEq, ha, false_and, ite_false, sum_zero]

@[simp] theorem margR_pure (a : α) (b : β) :
    margR (pure (a, b) : Weight K (α × β)) = pure b := by
  classical
  funext b'
  by_cases hb : b' = b
  · subst b'
    simp only [margR, pure, Prod.mk.injEq, and_true, ite_true]
    exact sum_single a 1
  · simp only [margR, pure, Prod.mk.injEq, hb, and_false, ite_false, sum_zero]

@[simp] theorem mass_margL (J : Weight K (α × β)) : mass (margL J) = mass J :=
  (sum_prod J).symm

@[simp] theorem mass_margR (J : Weight K (α × β)) : mass (margR J) = mass J :=
  (sum_comm fun b a => J (a, b)).trans (sum_prod J).symm

theorem IsCoupling.mass_eq {R : α → β → Prop} {μ : Weight K α} {ν : Weight K β}
    {J : Weight K (α × β)} (h : IsCoupling R μ ν J) : mass μ = mass ν := by
  rw [← h.margL_eq, ← h.margR_eq, mass_margL, mass_margR]

theorem Coupled.mass_eq {R : α → β → Prop} {μ : Weight K α} {ν : Weight K β}
    (h : Coupled R μ ν) : mass μ = mass ν := by
  obtain ⟨J, hJ⟩ := h
  exact hJ.mass_eq

theorem IsCoupling.zero (R : α → β → Prop) :
    IsCoupling R (0 : Weight K α) 0 0 where
  margL_eq := margL_zero
  margR_eq := margR_zero
  supported := by simp

theorem Coupled.zero (R : α → β → Prop) : Coupled R (0 : Weight K α) 0 :=
  ⟨0, IsCoupling.zero R⟩

theorem IsCoupling.pure {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    IsCoupling R (pure a : Weight K α) (pure b) (pure (a, b)) where
  margL_eq := margL_pure a b
  margR_eq := margR_pure a b
  supported := by
    classical
    intro a' b' hab
    have hp : (a', b') = (a, b) := by
      by_contra hn
      exact hab (by simp [Weighted.pure, hn])
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    exact h

theorem Coupled.pure {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Coupled R (pure a : Weight K α) (pure b) := ⟨_, IsCoupling.pure h⟩

theorem IsCoupling.mono {R S : α → β → Prop} {μ : Weight K α} {ν : Weight K β}
    {J : Weight K (α × β)} (h : IsCoupling R μ ν J) (hRS : ∀ a b, R a b → S a b) :
    IsCoupling S μ ν J where
  margL_eq := h.margL_eq
  margR_eq := h.margR_eq
  supported := fun a b hab => hRS a b (h.supported a b hab)

theorem Coupled.mono {R S : α → β → Prop} {μ : Weight K α} {ν : Weight K β}
    (h : Coupled R μ ν) (hRS : ∀ a b, R a b → S a b) : Coupled S μ ν := by
  obtain ⟨J, hJ⟩ := h
  exact ⟨J, hJ.mono hRS⟩

theorem IsCoupling.add {R : α → β → Prop} {μ μ' : Weight K α} {ν ν' : Weight K β}
    {J H : Weight K (α × β)} (hJ : IsCoupling R μ ν J) (hH : IsCoupling R μ' ν' H) :
    IsCoupling R (μ + μ') (ν + ν') (J + H) where
  margL_eq := by rw [margL_add, hJ.margL_eq, hH.margL_eq]
  margR_eq := by rw [margR_add, hJ.margR_eq, hH.margR_eq]
  supported := by
    intro a b hab
    by_cases hja : J (a, b) = 0
    · apply hH.supported a b
      simpa only [Pi.add_apply, hja, zero_add] using hab
    · exact hJ.supported a b hja

theorem Coupled.add {R : α → β → Prop} {μ μ' : Weight K α} {ν ν' : Weight K β}
    (h : Coupled R μ ν) (h' : Coupled R μ' ν') : Coupled R (μ + μ') (ν + ν') := by
  obtain ⟨J, hJ⟩ := h
  obtain ⟨H, hH⟩ := h'
  exact ⟨J + H, hJ.add hH⟩

theorem IsCoupling.scale {R : α → β → Prop} {μ : Weight K α} {ν : Weight K β}
    {J : Weight K (α × β)} (h : IsCoupling R μ ν J) (r : K) :
    IsCoupling R (scale r μ) (scale r ν) (scale r J) where
  margL_eq := by rw [margL_scale, h.margL_eq]
  margR_eq := by rw [margR_scale, h.margR_eq]
  supported := fun a b hab => h.supported a b (right_ne_zero_of_mul hab)

theorem Coupled.scale {R : α → β → Prop} {μ : Weight K α} {ν : Weight K β}
    (h : Coupled R μ ν) (r : K) : Coupled R (scale r μ) (scale r ν) := by
  obtain ⟨J, hJ⟩ := h
  exact ⟨_, hJ.scale r⟩

open Classical in
def diag (μ : Weight K α) : Weight K (α × α) := fun p => if p.1 = p.2 then μ p.1 else 0

@[simp] theorem margL_diag (μ : Weight K α) : margL (diag μ) = μ := by
  classical
  funext a
  change sum (fun b => if a = b then μ a else 0) = μ a
  simpa only [eq_comm] using sum_single a (μ a)

@[simp] theorem margR_diag (μ : Weight K α) : margR (diag μ) = μ := by
  classical
  funext b
  change sum (fun a => if a = b then μ a else 0) = μ b
  calc
    _ = sum (fun a => if a = b then μ b else 0) := by
      apply sum_congr
      intro a
      by_cases h : a = b <;> simp [h]
    _ = _ := sum_single b (μ b)

theorem isCoupling_diag (μ : Weight K α) : IsCoupling Eq μ μ (diag μ) where
  margL_eq := margL_diag μ
  margR_eq := margR_diag μ
  supported := by
    classical
    intro a b hab
    by_contra hne
    exact hab (by simp [diag, hne])

theorem Coupled.refl (μ : Weight K α) : Coupled Eq μ μ := ⟨_, isCoupling_diag μ⟩

theorem IsCoupling.eq {μ ν : Weight K α} {J : Weight K (α × α)}
    (h : IsCoupling Eq μ ν J) : μ = ν := by
  rw [← h.margL_eq, ← h.margR_eq]
  funext a
  change sum (fun b => J (a, b)) = sum (fun b => J (b, a))
  have hl : sum (fun b => J (a, b)) = J (a, a) := by
    apply sum_eq_single a
    intro b hb
    by_contra hj
    exact hb (h.supported a b hj).symm
  have hr : sum (fun b => J (b, a)) = J (a, a) := by
    apply sum_eq_single a
    intro b hb
    by_contra hj
    exact hb (h.supported b a hj)
  exact hl.trans hr.symm

theorem coupled_eq_iff {μ ν : Weight K α} : Coupled Eq μ ν ↔ μ = ν := by
  constructor
  · rintro ⟨J, hJ⟩
    exact hJ.eq
  · rintro rfl
    exact Coupled.refl μ

theorem margL_bind (J : Weight K (α × β)) (H : α × β → Weight K (γ × δ)) :
    margL (bind J H) = bind J (fun p => margL (H p)) := by
  funext c
  change sum (fun d => sum (fun p => J p * H p (c, d))) =
    sum (fun p => J p * sum (fun d => H p (c, d)))
  rw [sum_comm]
  apply sum_congr
  intro p
  exact mul_sum _ _

theorem margR_bind (J : Weight K (α × β)) (H : α × β → Weight K (γ × δ)) :
    margR (bind J H) = bind J (fun p => margR (H p)) := by
  funext d
  change sum (fun c => sum (fun p => J p * H p (c, d))) =
    sum (fun p => J p * sum (fun c => H p (c, d)))
  rw [sum_comm]
  apply sum_congr
  intro p
  exact mul_sum _ _

theorem bind_fst (J : Weight K (α × β)) (k : α → Weight K γ) :
    bind J (fun p => k p.1) = bind (margL J) k := by
  funext c
  simp only [bind, margL, sum_prod, sum_mul]

theorem bind_snd (J : Weight K (α × β)) (k : β → Weight K γ) :
    bind J (fun p => k p.2) = bind (margR J) k := by
  funext c
  simp only [bind, margR, sum_prod]
  rw [sum_comm]
  apply sum_congr
  intro b
  exact sum_mul _ _

theorem IsCoupling.bind {R : α → β → Prop} {S : γ → δ → Prop}
    {μ : Weight K α} {ν : Weight K β} {J : Weight K (α × β)}
    (hJ : IsCoupling R μ ν J) (k : α → Weight K γ) (l : β → Weight K δ)
    (H : α × β → Weight K (γ × δ))
    (hH : ∀ p ∈ support J, IsCoupling S (k p.1) (l p.2) (H p)) :
    IsCoupling S (bind μ k) (bind ν l) (bind J H) where
  margL_eq := by
    calc
      margL (Weighted.bind J H) = Weighted.bind J (fun p => margL (H p)) := margL_bind J H
      _ = Weighted.bind J (fun p => k p.1) :=
        bind_congr_on_support J fun p hp => (hH p hp).margL_eq
      _ = Weighted.bind (margL J) k := bind_fst J k
      _ = Weighted.bind μ k := by rw [hJ.margL_eq]
  margR_eq := by
    calc
      margR (Weighted.bind J H) = Weighted.bind J (fun p => margR (H p)) := margR_bind J H
      _ = Weighted.bind J (fun p => l p.2) :=
        bind_congr_on_support J fun p hp => (hH p hp).margR_eq
      _ = Weighted.bind (margR J) l := bind_snd J l
      _ = Weighted.bind ν l := by rw [hJ.margR_eq]
  supported := by
    intro c d hcd
    obtain ⟨p, hp, hHp⟩ := exists_support_of_bind_ne_zero J H (c, d) hcd
    exact (hH p hp).supported c d hHp

theorem Coupled.bind {R : α → β → Prop} {S : γ → δ → Prop}
    {μ : Weight K α} {ν : Weight K β} (h : Coupled R μ ν)
    (k : α → Weight K γ) (l : β → Weight K δ)
    (hkl : ∀ a b, R a b → Coupled S (k a) (l b)) :
    Coupled S (bind μ k) (bind ν l) := by
  classical
  obtain ⟨J, hJ⟩ := h
  let H : α × β → Weight K (γ × δ) := fun p =>
    if hp : R p.1 p.2 then (hkl p.1 p.2 hp).choose else 0
  refine ⟨Weighted.bind J H, hJ.bind k l H ?_⟩
  intro p hp
  have hR : R p.1 p.2 := hJ.supported p.1 p.2 hp
  dsimp only [H]
  rw [dif_pos hR]
  exact (hkl p.1 p.2 hR).choose_spec

end

end RelOL.Algebra.Weighted
