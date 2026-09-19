import RelationalOutcomeLogic.Prob.Loop
import RelationalOutcomeLogic.Prob.Coupling
import RelationalOutcomeLogic.Algebra.WeightOrder

/-!
# Synchronous loop couplings from a coherent joint execution

One joint body kernel defines a product loop whose finite approximants increase.
Each approximant has exactly the corresponding two program marginals. Taking the
limit preserves both marginals and the exit relation. No independently chosen
finite witnesses, normalization, or losslessness assumption is used.
-/

namespace RelOL.Prob

variable {α β : Type*}

/-- The first marginal preserves increasing sequential limits of joint weights. -/
theorem margL_iSup (J : ℕ → Weight (α × β)) (hJ : Monotone J) :
    margL (⨆ n, J n) = ⨆ n, margL (J n) := by
  funext a
  simp only [margL, iSup_apply]
  exact Weight.tsum_iSup_of_monotone _ (fun i j hij b => hJ hij (a, b))

/-- The second marginal preserves increasing sequential limits of joint weights. -/
theorem margR_iSup (J : ℕ → Weight (α × β)) (hJ : Monotone J) :
    margR (⨆ n, J n) = ⨆ n, margR (J n) := by
  funext b
  simp only [margR, iSup_apply]
  exact Weight.tsum_iSup_of_monotone _ (fun i j hij a => hJ hij (a, b))

/-- The limit of a coherent increasing family of joints retains its exact marginals.
Existence of unrelated witnesses for each index alone is not this hypothesis. -/
theorem IsCoupling.iSup {R : α → β → Prop} {μ : ℕ → Weight α}
    {ν : ℕ → Weight β} {J : ℕ → Weight (α × β)}
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
      fun n => (h n).apply_eq_zero_of_not_rel hR
    exact hab (by simp only [iSup_apply, hzero, iSup_const])

/-- A fixed joint body kernel couples every finite pair of synchronous loop approximants. -/
theorem IsCoupling.loopIter {R : α → β → Prop}
    (g : α → Prop) (h : β → Prop) (k : α → Weight α) (l : β → Weight β)
    (K : α × β → Weight (α × β))
    (hsync : ∀ a b, R a b → (g a ↔ h b))
    (hK : ∀ a b, R a b → g a → IsCoupling R (k a) (l b) (K (a, b)))
    (n : ℕ) {a : α} {b : β} (hab : R a b) :
    IsCoupling (fun x y => R x y ∧ ¬ g x ∧ ¬ h y)
      (Prob.loopIter g k n a) (Prob.loopIter h l n b)
      (Prob.loopIter (fun p => g p.1) K n (a, b)) := by
  classical
  induction n generalizing a b with
  | zero =>
      simpa only [Prob.loopIter] using
        IsCoupling.zero (fun x y => R x y ∧ ¬ g x ∧ ¬ h y)
  | succ n ih =>
      by_cases ha : g a
      · have hb : h b := (hsync a b hab).mp ha
        simp only [Prob.loopIter, if_pos ha, if_pos hb]
        apply (hK a b hab ha).bind (Prob.loopIter g k n) (Prob.loopIter h l n)
          (Prob.loopIter (fun p => g p.1) K n)
        intro p hp
        exact ih ((hK a b hab ha).supported p.1 p.2 hp)
      · have hb : ¬ h b := fun hb => ha ((hsync a b hab).mpr hb)
        simpa only [Prob.loopIter, if_neg ha, if_neg hb] using
          IsCoupling.pure (R := fun x y => R x y ∧ ¬ g x ∧ ¬ h y) ⟨hab, ha, hb⟩

/-- The product loop's increasing joint approximants give an exact coupling of full loops. -/
theorem IsCoupling.loopSem {R : α → β → Prop}
    (g : α → Prop) (h : β → Prop) (k : α → Weight α) (l : β → Weight β)
    (K : α × β → Weight (α × β))
    (hsync : ∀ a b, R a b → (g a ↔ h b))
    (hK : ∀ a b, R a b → g a → IsCoupling R (k a) (l b) (K (a, b)))
    {a : α} {b : β} (hab : R a b) :
    IsCoupling (fun x y => R x y ∧ ¬ g x ∧ ¬ h y)
      (Prob.loopSem g k a) (Prob.loopSem h l b)
      (Prob.loopSem (fun p => g p.1) K (a, b)) := by
  have hmono : Monotone (fun n => Prob.loopIter (fun p => g p.1) K n (a, b)) :=
    fun _ _ hij => loopIter_monotone (fun p => g p.1) K hij (a, b)
  simpa only [Prob.loopSem] using
    IsCoupling.iSup hmono (fun n => IsCoupling.loopIter g h k l K hsync hK n hab)

/-- Synchronous relational loop soundness, allowing divergence and arbitrary raw weights. -/
theorem coupled_loop {R : α → β → Prop}
    (g : α → Prop) (h : β → Prop) (k : α → Weight α) (l : β → Weight β)
    (hsync : ∀ a b, R a b → (g a ↔ h b))
    (hbody : ∀ a b, R a b → g a → Coupled R (k a) (l b))
    {a : α} {b : β} (hab : R a b) :
    Coupled (fun x y => R x y ∧ ¬ g x ∧ ¬ h y) (loopSem g k a) (loopSem h l b) := by
  classical
  let K : α × β → Weight (α × β) := fun p =>
    if hp : R p.1 p.2 ∧ g p.1 then (hbody p.1 p.2 hp.1 hp.2).choose else 0
  have hK : ∀ a b, R a b → g a → IsCoupling R (k a) (l b) (K (a, b)) := by
    intro a b hab ha
    dsimp only [K]
    rw [dif_pos ⟨hab, ha⟩]
    exact (hbody a b hab ha).choose_spec
  exact ⟨loopSem (fun p => g p.1) K (a, b),
    IsCoupling.loopSem g h k l K hsync hK hab⟩

end RelOL.Prob
