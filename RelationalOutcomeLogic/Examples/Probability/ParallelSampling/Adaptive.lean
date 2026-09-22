import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Correctness
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Versioning

/-!
# Adaptive generations by relational sequencing

The next generation may choose its whole joint job law, quota, and proposal cap
from the committed history. Each generation finishes before that choice changes;
outstanding work is not silently reused under a different law. `Versioning`
provides a separate reconstruction contract for validated look-ahead.
-/

namespace RelOL.Prob.ParallelSampling
universe u
variable {α : Type u}
noncomputable section

abbrev GenerationHistory (α : Type u) := List (Result α)

def referenceGeneration (law : GenerationHistory α → Weight (Job α))
    (quota cap : GenerationHistory α → Nat) (h : GenerationHistory α) :
    Weight (GenerationHistory α) :=
  pushforward (fun r => h ++ [r]) (capped (law h) (cap h) (quota h))

def parallelGeneration (law : GenerationHistory α → Weight (Job α))
    (quota cap : GenerationHistory α → Nat) (workers window : Nat)
    (h : GenerationHistory α) : Weight (GenerationHistory α) :=
  pushforward (fun r => h ++ [r.answer])
    (freshCollector (law h) workers window (quota h) (cap h))

theorem generation_quad (law : GenerationHistory α → Weight (Job α))
    (hlaw : ∀ h, Weight.IsProbability (law h)) (quota cap : GenerationHistory α → Nat)
    (workers window : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    Generic.quad (Generic.lifted Weight.pure) (referenceGeneration law quota cap)
      (parallelGeneration law quota cap workers window) (Generic.lifted Weight.pure) := by
  apply Generic.quad_lifted
  intro h
  simp only [Generic.weight_bind_eq, Weight.pure_bind, Weight.bind_pure]
  have ho := freshCollector_answer (law h) (hlaw h) workers window (quota h) (cap h)
    hworkers hwindow
  rw [parallelGeneration, referenceGeneration, ← ho]
  simp only [pushforward, Weight.bind_assoc, Weight.pure_bind]

def adaptiveReference (law : GenerationHistory α → Weight (Job α))
    (quota cap : GenerationHistory α → Nat) (generations : Nat) :
    GenerationHistory α → Weight (GenerationHistory α) :=
  Generic.boundedSteps (fun _ => referenceGeneration law quota cap) generations

def adaptiveParallel (law : GenerationHistory α → Weight (Job α))
    (quota cap : GenerationHistory α → Nat) (workers window generations : Nat) :
    GenerationHistory α → Weight (GenerationHistory α) :=
  Generic.boundedSteps (fun _ => parallelGeneration law quota cap workers window) generations

/-- Every generation's rule consumes the previous generation's whole history law. -/
theorem adaptive_quad (law : GenerationHistory α → Weight (Job α))
    (hlaw : ∀ h, Weight.IsProbability (law h)) (quota cap : GenerationHistory α → Nat)
    (workers window generations : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    Generic.quad (Generic.lifted Weight.pure) (adaptiveReference law quota cap generations)
      (adaptiveParallel law quota cap workers window generations) (Generic.lifted Weight.pure) :=
  Generic.quad_boundedSteps_invariant _ _ _
    (fun _ => generation_quad law hlaw quota cap workers window hworkers hwindow) generations

theorem adaptive_equal (law : GenerationHistory α → Weight (Job α))
    (hlaw : ∀ h, Weight.IsProbability (law h)) (quota cap : GenerationHistory α → Nat)
    (workers window generations : Nat) (hworkers : 0 < workers) (hwindow : 0 < window)
    (h : GenerationHistory α) :
    adaptiveParallel law quota cap workers window generations h =
      adaptiveReference law quota cap generations h := by
  have he := Generic.quad_lifted_iff.mp
    (adaptive_quad law hlaw quota cap workers window generations hworkers hwindow) h
  simpa only [Generic.weight_bind_eq, Weight.pure_bind, Weight.bind_pure] using he

/-- Kernel-validated look-ahead can be substituted into any complete generation.
The validation context must carry the stipulated conditional generating law. -/
theorem validated_generation {ι : Type u} (law : ι → Weight (Job α))
    (hlaw : ∀ v, Weight.IsProbability (law v)) (valid : ι → ι → Bool)
    (hsound : ∀ old current, valid old current = true → law old = law current)
    (context : VersionContext ι) (workers window quota cap : Nat)
    (hworkers : 0 < workers) (hwindow : 0 < window) :
    pushforward PoolResult.answer
      (freshCollector (validatedSample law valid context) workers window quota cap) =
      capped (law context.required) cap quota := by
  rw [validatedSample_eq law hlaw valid hsound context]
  exact freshCollector_answer _ (hlaw _) workers window quota cap hworkers hwindow

end
end RelOL.Prob.ParallelSampling
