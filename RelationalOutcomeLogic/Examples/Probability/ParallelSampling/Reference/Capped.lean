import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Model
import RelationalOutcomeLogic.Generic.Distributional
import RelationalOutcomeLogic.Generic.Loops.Bounded
import RelationalOutcomeLogic.Bridges.Probability

/-!
# Deferred sampling and the capped reference

The reference samples only proposals it needs. The ghost execution samples a
finite prefix before scheduling. Their equality is derived by the reconstruction
and recursion rules: one draw exposes the next ticket, and an unused normalized
suffix can be discarded. Exhausted partial populations are retained.
-/

namespace RelOL.Prob.ParallelSampling

universe u
variable {α : Type u}
noncomputable section

def capped (law : Weight (Job α)) : Nat → Nat → Weight (Result α)
  | _, 0 => Weight.pure (.success [])
  | 0, _ + 1 => Weight.pure (.exhausted [])
  | m + 1, n + 1 => Weight.bind law fun j =>
      if j.accepted then pushforward (Result.prepend j.value) (capped law m n)
      else capped law m (n + 1)

private abbrev Budget := ULift.{u} Nat
private abbrev Ghost (α : Type u) := Budget × List (Job α)

/-- The unobserved suffix is fresh; previously observed runtimes are not resampled. -/
def prefixReconstruction (law : Weight (Job α)) (m : Nat)
    (b : ULift.{u} Nat) : Weight (ULift.{u} Nat × List (Job α)) :=
  pushforward (fun js => (b, js)) (draws law m)

private def referenceLayer (law : Weight (Job α))
    (k : Budget → Weight (Result α)) (b : Budget) : Weight (Result α) :=
  match b.down with
  | 0 => Weight.pure (.success [])
  | n + 1 => Weight.bind law fun j =>
      if j.accepted then pushforward (Result.prepend j.value) (k ⟨n⟩) else k b

private def ghostLayer (k : Ghost α → Weight (Result α))
    (s : Ghost α) : Weight (Result α) :=
  match s.1.down, s.2 with
  | 0, _ => Weight.pure (.success [])
  | _ + 1, [] => Weight.pure (.exhausted [])
  | n + 1, j :: js =>
      if j.accepted then pushforward (Result.prepend j.value) (k (⟨n⟩, js))
      else k (s.1, js)

private theorem reconstruction_layer (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (m : Nat)
    (k : Budget → Weight (Result α)) (l : Ghost α → Weight (Result α))
    (h : Generic.quad (Generic.lifted (prefixReconstruction law m)) k l
      (Generic.lifted Weight.pure)) :
    Generic.quad (Generic.lifted (prefixReconstruction law (m + 1)))
      (referenceLayer law k) (ghostLayer l) (Generic.lifted Weight.pure) := by
  apply Generic.quad_lifted
  intro b
  have hc (b' : Budget) :
      Weight.bind (draws law m) (fun js => l (b', js)) = k b' := by
    have hh := Generic.quad_lifted_iff.mp h b'
    simpa only [prefixReconstruction, bind_pushforward, Generic.weight_bind_eq,
      Weight.bind_pure] using hh
  change Weight.bind (prefixReconstruction law (m + 1) b) (ghostLayer l) =
    Weight.bind (referenceLayer law k b) Weight.pure
  rw [Weight.bind_pure, prefixReconstruction, bind_pushforward]
  rcases b with ⟨b⟩
  cases b with
  | zero =>
      change Weight.bind (draws law (m + 1))
        (fun _ => Weight.pure (Result.success ([] : List α))) = _
      exact Weight.bind_const_of_isProbability _ (draws_probability law hlaw _) _
  | succ n =>
      simp only [draws, Weight.bind_assoc, Weight.pure_bind, ghostLayer, referenceLayer]
      congr 1
      funext j
      cases hj : j.accepted
      · simpa only [hj, Bool.false_eq_true, ↓reduceIte] using hc ⟨n + 1⟩
      · simp only [↓reduceIte, pushforward, ← Weight.bind_assoc, hc ⟨n⟩]

/-- A rule-derived eager/lazy sampling correspondence, including early stopping. -/
theorem capped_reconstruction_quad (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (m : Nat) :
    Generic.quad (Generic.lifted (prefixReconstruction law m))
      (fun b : ULift.{u} Nat => capped law m b.down)
      (fun s : ULift.{u} Nat × List (Job α) => Weight.pure (select s.1.down s.2))
      (Generic.lifted Weight.pure) := by
  apply Generic.quad_recursion
    (fun i => Generic.lifted (prefixReconstruction law i))
    (Generic.lifted Weight.pure)
    (fun i b => capped law i b.down)
    (fun _ s => Weight.pure (select s.1.down s.2))
    (fun _ => referenceLayer law) (fun _ => ghostLayer)
  · intro i
    funext b
    rcases b with ⟨b⟩
    cases b <;> rfl
  · intro i
    funext s
    rcases s with ⟨⟨b⟩, js⟩
    cases b with
    | zero => cases js <;> rfl
    | succ n =>
      cases js with
      | nil => rfl
      | cons j js =>
        cases hj : j.accepted <;>
          simp [ghostLayer, select, hj]
  · apply Generic.quad_lifted
    intro b
    change Weight.bind (prefixReconstruction law 0 b)
      (fun s => Weight.pure (select s.1.down s.2)) =
      Weight.bind (capped law 0 b.down) Weight.pure
    simp only [prefixReconstruction, draws, pushforward_pure, Weight.pure_bind,
      Weight.bind_pure]
    cases b.down <;> rfl
  · exact reconstruction_layer law hlaw

theorem capped_eq_prefix (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (m n : Nat) : capped law m n = pushforward (select n) (draws law m) := by
  have h := Generic.quad_lifted_iff.mp (capped_reconstruction_quad law hlaw m) ⟨n⟩
  simpa only [prefixReconstruction, bind_pushforward, Generic.weight_bind_eq,
    Weight.bind_pure, pushforward, Weight.bind_assoc, Weight.pure_bind] using h.symm

theorem capped_probability (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (m n : Nat) : Weight.IsProbability (capped law m n) := by
  rw [capped_eq_prefix law hlaw]
  exact (draws_probability law hlaw m).bind (fun _ => Weight.isProbability_pure _)

end
end RelOL.Prob.ParallelSampling
