import RelationalOutcomeLogic.Algebra.Weighted.Coupling
import RelationalOutcomeLogic.Algebra.Weighted.Iteration

/-!
# Observations of weighted outcomes

Pushforward transports each outcome through a deterministic observation while
preserving its weight. These laws concern the weighted algebra itself and can be
used without importing loop alignment or the relational logic.
-/

universe u v

namespace RelOL.Algebra.Weighted

variable {κ : Type v} [Semiring κ] [CompleteLattice κ]
variable [SummationSemiring.{u} κ] [OmegaSummationSemiring.{u} κ]
variable {α β σ τ : Type u}

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
/-- Observe an outcome without changing its scalar weight. -/
noncomputable def pushforward (π : σ → τ) (μ : Weight κ σ) : Weight κ τ :=
  Weighted.bind μ (fun s => Weighted.pure (π s))

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
@[simp] theorem pushforward_zero (π : σ → τ) : pushforward (κ := κ) π 0 = 0 :=
  Weighted.zero_bind _

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
@[simp] theorem pushforward_pure (π : σ → τ) (s : σ) :
    pushforward (κ := κ) π (Weighted.pure s) = Weighted.pure (π s) :=
  Weighted.pure_bind _ _

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
theorem pushforward_bind (π : σ → τ) (μ : Weight κ α) (K : α → Weight κ σ) :
    pushforward π (Weighted.bind μ K) =
      Weighted.bind μ (fun s => pushforward π (K s)) := Weighted.bind_assoc _ _ _

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
theorem bind_pushforward (π : σ → τ) (μ : Weight κ σ) (f : τ → Weight κ β) :
    Weighted.bind (pushforward π μ) f = Weighted.bind μ (fun s => f (π s)) := by
  simp only [pushforward, Weighted.bind_assoc, Weighted.pure_bind]

theorem pushforward_iSup (π : σ → τ) (μ : ℕ → Weight κ σ) (hμ : Monotone μ) :
    pushforward π (⨆ n, μ n) = ⨆ n, pushforward π (μ n) :=
  Weighted.bind_iSup_left μ hμ _

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
@[simp] theorem pushforward_fst (J : Weight κ (α × β)) :
    pushforward Prod.fst J = margL J := by
  rw [pushforward, bind_fst, Weighted.bind_pure]

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
@[simp] theorem pushforward_snd (J : Weight κ (α × β)) :
    pushforward Prod.snd J = margR J := by
  rw [pushforward, bind_snd, Weighted.bind_pure]

end RelOL.Algebra.Weighted
