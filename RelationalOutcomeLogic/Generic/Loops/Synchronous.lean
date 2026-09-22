import RelationalOutcomeLogic.Generic.Coupling
import RelationalOutcomeLogic.Algebra.Weighted.Iteration
import RelationalOutcomeLogic.Generic.Loops.Semantics

/-!
# Synchronous loop couplings from a coherent joint execution

One joint body kernel defines a product loop whose finite approximants increase.
Each approximant has exactly the corresponding two program marginals. Taking the
limit preserves both marginals and the exit relation. No independently chosen
finite witnesses, normalization, or losslessness assumption is used.
-/

universe u v

namespace RelOL.Algebra.Weighted

variable {σ : Type v} [Semiring σ] [CompleteLattice σ]
variable [SummationSemiring.{u} σ] [OmegaSummationSemiring.{u} σ]
variable {α β : Type u}

/-- The first marginal preserves increasing sequential limits of joint weights. -/
theorem margL_iSup (J : ℕ → Weight σ (α × β)) (hJ : Monotone J) :
    margL (⨆ n, J n) = ⨆ n, margL (J n) := by
  funext a
  simp only [margL, iSup_apply]
  exact OmegaSummationSemiring.sum_iSup _ (fun i j hij b => hJ hij (a, b))

/-- The second marginal preserves increasing sequential limits of joint weights. -/
theorem margR_iSup (J : ℕ → Weight σ (α × β)) (hJ : Monotone J) :
    margR (⨆ n, J n) = ⨆ n, margR (J n) := by
  funext b
  simp only [margR, iSup_apply]
  exact OmegaSummationSemiring.sum_iSup _ (fun i j hij a => hJ hij (a, b))

/-- The limit of a coherent increasing family of joints retains its exact marginals.
Existence of unrelated witnesses for each index alone is not this hypothesis. -/
theorem IsCoupling.iSup {R : α → β → Prop} {μ : ℕ → Weight σ α}
    {ν : ℕ → Weight σ β} {J : ℕ → Weight σ (α × β)}
    (hJ : Monotone J) (h : ∀ n, IsCoupling R (μ n) (ν n) (J n)) :
    IsCoupling R (⨆ n, μ n) (⨆ n, ν n) (⨆ n, J n) where
  margL_eq := by
    rw [margL_iSup J hJ]
    exact iSup_congr fun n => (h n).margL_eq
  margR_eq := by
    rw [margR_iSup J hJ]
    exact iSup_congr fun n => (h n).margR_eq
  supported := by
    intro a b hab
    by_contra hR
    have hzero : ∀ n, J n (a, b) = 0 :=
      fun n => by
        by_contra hn
        exact hR ((h n).supported a b hn)
    exact hab (by simp only [iSup_apply, hzero, iSup_const])

omit [CompleteLattice σ] [OmegaSummationSemiring σ] in
/-- A fixed joint body kernel couples every finite pair of synchronous loop approximants. -/
theorem IsCoupling.loopIter {R : α → β → Prop}
    (g : α → Prop) (h : β → Prop) (k : α → Weight σ α) (l : β → Weight σ β)
    (K : α × β → Weight σ (α × β))
    (hsync : ∀ a b, R a b → (g a ↔ h b))
    (hK : ∀ a b, R a b → g a → IsCoupling R (k a) (l b) (K (a, b)))
    (n : ℕ) {a : α} {b : β} (hab : R a b) :
    IsCoupling (fun x y => R x y ∧ ¬ g x ∧ ¬ h y)
      (Generic.loopIter g k n a) (Generic.loopIter h l n b)
      (Generic.loopIter (fun p => g p.1) K n (a, b)) := by
  classical
  induction n generalizing a b with
  | zero =>
      simpa only [Generic.loopIter, OutcomeModel.empty, outcomeModel] using
        IsCoupling.zero (fun x y => R x y ∧ ¬ g x ∧ ¬ h y)
  | succ n ih =>
      by_cases ha : g a
      · have hb : h b := (hsync a b hab).mp ha
        simp only [Generic.loopIter, if_pos ha, if_pos hb]
        change IsCoupling _ (Weighted.bind (k a) (Generic.loopIter g k n))
          (Weighted.bind (l b) (Generic.loopIter h l n))
          (Weighted.bind (K (a, b)) (Generic.loopIter (fun p => g p.1) K n))
        apply (hK a b hab ha).bind (Generic.loopIter g k n) (Generic.loopIter h l n)
          (Generic.loopIter (fun p => g p.1) K n)
        intro p hp
        exact ih ((hK a b hab ha).supported p.1 p.2 hp)
      · have hb : ¬ h b := fun hb => ha ((hsync a b hab).mpr hb)
        simpa only [Generic.loopIter, if_neg ha, if_neg hb, OutcomeModel.pure, outcomeModel] using
          IsCoupling.pure (R := fun x y => R x y ∧ ¬ g x ∧ ¬ h y) ⟨hab, ha, hb⟩

/-- The product loop's increasing joint approximants give an exact coupling of full loops. -/
theorem IsCoupling.loopSem {R : α → β → Prop}
    (g : α → Prop) (h : β → Prop) (k : α → Weight σ α) (l : β → Weight σ β)
    (K : α × β → Weight σ (α × β))
    (hsync : ∀ a b, R a b → (g a ↔ h b))
    (hK : ∀ a b, R a b → g a → IsCoupling R (k a) (l b) (K (a, b)))
    {a : α} {b : β} (hab : R a b) :
    IsCoupling (fun x y => R x y ∧ ¬ g x ∧ ¬ h y)
      (Generic.loopSem g k a) (Generic.loopSem h l b)
      (Generic.loopSem (fun p => g p.1) K (a, b)) := by
  have hmono : Monotone (fun n => Generic.loopIter (fun p => g p.1) K n (a, b)) :=
    fun _ _ hij => Generic.loopIter_monotone (fun p => g p.1) K hij (a, b)
  simpa only [Generic.loopSem] using
    IsCoupling.iSup hmono (fun n => IsCoupling.loopIter g h k l K hsync hK n hab)

/-- Synchronous relational loop soundness, allowing divergence and arbitrary raw weights. -/
theorem coupled_loop {R : α → β → Prop}
    (g : α → Prop) (h : β → Prop) (k : α → Weight σ α) (l : β → Weight σ β)
    (hsync : ∀ a b, R a b → (g a ↔ h b))
    (hbody : ∀ a b, R a b → g a → Coupled R (k a) (l b))
    {a : α} {b : β} (hab : R a b) :
    Coupled (fun x y => R x y ∧ ¬ g x ∧ ¬ h y) (Generic.loopSem g k a) (Generic.loopSem h l b) := by
  classical
  let K : α × β → Weight σ (α × β) := fun p =>
    if hp : R p.1 p.2 ∧ g p.1 then (hbody p.1 p.2 hp.1 hp.2).choose else 0
  have hK : ∀ a b, R a b → g a → IsCoupling R (k a) (l b) (K (a, b)) := by
    intro a b hab ha
    dsimp only [K]
    rw [dif_pos ⟨hab, ha⟩]
    exact (hbody a b hab ha).choose_spec
  exact ⟨Generic.loopSem (fun p => g p.1) K (a, b),
    IsCoupling.loopSem g h k l K hsync hK hab⟩

end RelOL.Algebra.Weighted

namespace RelOL.Generic

open Algebra

variable {K : Type v} [Semiring K] [CompleteLattice K]
variable [SummationSemiring.{u} K] [OmegaSummationSemiring.{u} K]
variable {α β : Type u}

/-- The synchronous pRHL while rule over every ordered summation-semiring instance. -/
theorem prhl_while {R : α → β → Prop}
    (g : α → Prop) (h : β → Prop)
    (k : α → Weighted.Weight K α) (l : β → Weighted.Weight K β)
    (hsync : ∀ a b, R a b → (g a ↔ h b))
    (hbody : prhl (fun a b => R a b ∧ g a) k l R) :
    prhl R (loopSem g k) (loopSem h l) (fun a b => R a b ∧ ¬ g a ∧ ¬ h b) := by
  intro a b hab
  exact Weighted.coupled_loop g h k l hsync (fun a b hr hg => hbody a b ⟨hr, hg⟩) hab

/-- An outcome-level body derivation yields an outcome-level relational while rule. -/
theorem quad_couple_while {R : α → β → Prop}
    (g : α → Prop) (h : β → Prop)
    (k : α → Weighted.Weight K α) (l : β → Weighted.Weight K β)
    (hsync : ∀ a b, R a b → (g a ↔ h b))
    (hbody : quad (couple (fun a b => R a b ∧ g a)) k l (couple R)) :
    quad (couple R) (loopSem g k) (loopSem h l)
      (couple (fun a b => R a b ∧ ¬ g a ∧ ¬ h b)) :=
  prhl_iff_quad.mp (prhl_while g h k l hsync (prhl_iff_quad.mpr hbody))

end RelOL.Generic
