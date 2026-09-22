import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Correction
import RelationalOutcomeLogic.Prob.Coupling.Assertions
import RelationalOutcomeLogic.Bridges.Probability

/-!
# Deriving the accept/correct sampler's quantitative outcome contract

Primitive sampling and deterministic tagging judgments are sequenced and joined
with the additive choice rule. The resulting contract retains accepted/corrected
branch masses and token agreement for arbitrary coupled input weights. Its token
projection supplies the local sampler obligation in the complete decoder proof.
The primitive algebraic boundary is the accepted/corrected decomposition of one
verification step; no completed decoder correctness theorem is used here.
-/

namespace RelOL.Prob.Speculative

universe u
open scoped ENNReal
variable {α : Type u}

noncomputable section

/-- Agreement on the token and a specified verification outcome. -/
def branchSpec (accepted : Bool) (mass : ℝ≥0∞) : RAssn α (Bool × α) :=
  fun μ ν => couple (fun x v => x = v.2 ∧ v.1 = accepted) μ ν ∧ massEq mass mass μ ν

/-- The accepted overlap and corrected residual keep their individual masses. -/
def stepSpec (p q : Distribution α) : RAssn α (Bool × α) :=
  oplus (branchSpec true (acceptanceMass p q)) (branchSpec false (rejectionMass p q))

private def coupledMass {σ : Type*} (r : ℝ≥0∞) : RAssn σ σ :=
  fun μ ν => couple Eq μ ν ∧ massEq r r μ ν

/-- Primitive sampling preserves agreement and scales the incoming mass by the
branch's mass. Inputs need not be normalized or concentrated at one state. -/
private theorem sample_mass_quad {σ : Type u} (w : Weight α) (r : ℝ≥0∞) :
    Generic.quad (coupledMass (σ := σ) r) (fun _ => w) (fun _ => w)
      (coupledMass (r * Weight.mass w)) := by
  rintro μ ν ⟨hc, hμ, hν⟩
  refine ⟨hc.bind (fun _ => w) (fun _ => w)
    (fun _ _ _ => coupled_eq_iff.mpr rfl), ?_, ?_⟩
  · change Weight.mass (Weight.bind μ (fun _ => w)) = r * Weight.mass w
    rw [Weight.mass_bind, ENNReal.tsum_mul_right]
    change Weight.mass μ * Weight.mass w = r * Weight.mass w
    rw [hμ]
  · change Weight.mass (Weight.bind ν (fun _ => w)) = r * Weight.mass w
    rw [Weight.mass_bind, ENNReal.tsum_mul_right]
    change Weight.mass ν * Weight.mass w = r * Weight.mass w
    rw [hν]

/-- The deterministic tagging command records a branch without changing mass. -/
private theorem tag_mass_quad (b : Bool) (r : ℝ≥0∞) :
    Generic.quad (coupledMass (σ := α) r) Weight.pure
      (fun x => Weight.pure (b, x)) (branchSpec b r) := by
  rintro μ ν ⟨hc, hμ, hν⟩
  refine ⟨hc.bind Weight.pure (fun x => Weight.pure (b, x))
    (fun a c hac => Coupled.pure (show a = c ∧ b = b from ⟨hac, rfl⟩)), ?_, ?_⟩
  · simpa only [Generic.weight_bind_eq, Weight.bind_pure] using hμ
  · change Weight.mass (pushforward (fun x => (b, x)) ν) = r
    rw [mass_pushforward, hν]

/-- A branch proof is obtained by sequencing sampling and deterministic tagging. -/
private theorem tagged_sampler_quad {σ : Type u} (w : Weight α) (b : Bool)
    (r : ℝ≥0∞) :
    Generic.quad (coupledMass (σ := σ) r) (fun _ => w)
      (fun _ => pushforward (fun x => (b, x)) w)
      (branchSpec b (r * Weight.mass w)) := by
  simpa only [Generic.weight_bind_eq, Weight.bind_pure, pushforward] using
    Generic.quad_seq (sample_mass_quad (σ := σ) w r)
      (tag_mass_quad b (r * Weight.mass w))

theorem step_decomposition (p q : Distribution α) :
    step p q = pushforward (fun x => (true, x)) (overlap p q) +
      pushforward (fun x => (false, x)) (residual p q) := by
  classical
  funext v
  rcases v with ⟨b, x⟩
  cases b <;> simp [step_apply_true, step_apply_false, pushforward,
    Weight.bind, Weight.pure, mul_ite]

/-- The choice rule combines accepted and corrected branch derivations. This
judgment applies to arbitrary coupled inputs of equal prescribed mass. The only
sampler rewrite is its local accepted/corrected decomposition. -/
theorem step_outcome_quad_mass {σ : Type u} (p q : Distribution α) (r : ℝ≥0∞) :
    Generic.quad (fun μ ν : Weight σ => couple Eq μ ν ∧ massEq r r μ ν)
      (fun _ => p.weight) (fun _ => step p q)
      (oplus (branchSpec true (r * acceptanceMass p q))
        (branchSpec false (r * rejectionMass p q))) := by
  change Generic.quad (coupledMass r) _ _ _
  simpa only [Generic.weight_add_eq, Generic.weight_oplus_eq,
    overlap_add_residual, ← step_decomposition, acceptanceMass, rejectionMass] using
    Generic.quad_choice (tagged_sampler_quad (σ := σ) (overlap p q) true r)
      (tagged_sampler_quad (σ := σ) (residual p q) false r)

/-- The actual sampler's contract follows by specializing its derived judgment. -/
theorem step_outcome_contract (p q : Distribution α) :
    stepSpec p q p.weight (step p q) := by
  have h := step_outcome_quad_mass (σ := PUnit.{u + 1}) p q 1
    (Weight.pure PUnit.unit) (Weight.pure PUnit.unit)
    ⟨Coupled.pure rfl, by simp [massEq]⟩
  simpa only [Generic.weight_bind_eq, Weight.pure_bind, one_mul, stepSpec] using h

theorem stepSpec_mass_one (p q : Distribution α) :
    entail (stepSpec p q) (massEq 1 1) := by
  intro μ ν h
  have hm := oplus_mono (fun _ _ h => h.2) (fun _ _ h => h.2) μ ν h
  have hs := oplus_massEq (acceptanceMass p q) (acceptanceMass p q)
    (rejectionMass p q) (rejectionMass p q) μ ν hm
  simpa only [acceptance_add_rejection] using hs

theorem stepSpec_token_agreement (p q : Distribution α) :
    entail (stepSpec p q) (couple (fun x v => x = v.2)) := by
  intro μ ν h
  apply oplus_couple_same μ ν
  exact oplus_mono (fun _ _ hb => hb.1.mono (fun _ _ hv => hv.1))
    (fun _ _ hb => hb.1.mono (fun _ _ hv => hv.1)) μ ν h

theorem stepSpec_observed_eq (p q : Distribution α) {μ : Weight α}
    {ν : Weight (Bool × α)} (h : stepSpec p q μ ν) :
    μ = pushforward Prod.snd ν := by
  have hc := (stepSpec_token_agreement p q μ ν h).pushforward id Prod.snd
    (S := Eq) (fun _ _ h => h)
  have he := coupled_eq_iff.mp hc
  simpa only [pushforward, id_eq, Weight.bind_pure] using he

/-- Consequence specializes the derived arbitrary-input judgment to an explicit
initial input. The proof does not assume the sampler's completed contract. -/
theorem step_outcome_quad (p q : Distribution α) :
    quadSem (fun μ : Weight Unit => Weight.bind μ (fun _ => p.weight))
      (fun μ : Weight Unit => Weight.bind μ (fun _ => step p q))
      (exactly (Weight.pure ()) (Weight.pure ())) (stepSpec p q) := by
  have derived : Generic.quad
      (exactly (Weight.pure (PUnit.unit : PUnit.{u + 1}))
        (Weight.pure (PUnit.unit : PUnit.{u + 1})))
      (fun _ : PUnit.{u + 1} => p.weight) (fun _ => step p q) (stepSpec p q) := by
    apply Generic.quad_consequence (M := Weight)
      (P' := exactly (Weight.pure (PUnit.unit : PUnit.{u + 1}))
        (Weight.pure (PUnit.unit : PUnit.{u + 1}))) (Q' := stepSpec p q)
      (P := fun μ ν : Weight PUnit.{u + 1} =>
      couple Eq μ ν ∧ massEq 1 1 μ ν)
      (Q := oplus (branchSpec true (1 * acceptanceMass p q))
        (branchSpec false (1 * rejectionMass p q)))
      ?_ (step_outcome_quad_mass (σ := PUnit.{u + 1}) p q 1) ?_
    · rintro _ _ ⟨rfl, rfl⟩
      exact ⟨Coupled.pure rfl, by simp [massEq]⟩
    · intro μ ν h
      simpa only [one_mul, stepSpec] using h
  -- `PUnit` keeps the generic derivation universe-polymorphic; the public
  -- interface uses ordinary `Unit` and has the same deterministic entry point.
  rintro _ _ ⟨rfl, rfl⟩
  simpa only [Generic.weight_bind_eq, Weight.pure_bind] using
    derived _ _ (exactly_self _ _)

end
end RelOL.Prob.Speculative
