import RelationalOutcomeLogic.Rules

/-!
# Case study 1c: refuting Generalized Noninterference (a ∀∃ hyperproperty)

`GNI` (McLean/McCullough-style, specialized to stores): every outcome from one
initial state is low-matched by *some* outcome from any other initial state —
a ∀∃ hyperproperty, unlike NI's ∀∀ shape.

Refuting a ∀∃ specification needs more than an `⊕ ⊤` certificate: the dropped
outcomes could hide the matching run. The certificate below therefore pairs an
under-approximate left claim (a reachable `low = 1` outcome, the `atom`
component) with an *exhaustive* right claim (every right outcome has
`low = 0`, a bespoke shallow assertion) — the same certificate-strength
asymmetry as refuting `refines` in the translation case study, now on a
hyperproperty from the security literature.
-/

namespace RelOL

/-- Concrete state builder: a secret `h` and a public `low`. -/
def sth (h low : Int) : State :=
  fun v => if v = "h" then h else if v = "low" then low else 0

@[simp] theorem sth_h (h low : Int) : sth h low "h" = h := by simp [sth]

@[simp] theorem sth_low (h low : Int) : sth h low "low" = low := by simp [sth]

/-- Either publish the secret or publish `0` — nondeterministically. -/
def gniProg : Cmd :=
  .choice (.assign "low" fun s => s "h") (.assign "low" fun _ => 0)

/-- Generalized noninterference (∀∃): every outcome is low-matched by some
outcome from any other initial state. -/
def GNI (c : Cmd) : Prop :=
  ∀ s s' : State, ∀ t ∈ sem c s, ∃ t' ∈ sem c s', t "low" = t' "low"

/-- Certificate precondition: secrets `1` vs `0`. -/
def preGNI : RAssn State State := atom fun s s' => s "h" = 1 ∧ s' "h" = 0

theorem preGNI_sat : preGNI {sth 1 0} {sth 0 0} := by
  rw [preGNI, atom_singleton_iff]
  simp

/-- Every right-side outcome publishes `0`: both branches do, since the
right secret is `0`. -/
theorem gni_right_low {s' : State} (hh' : s' "h" = 0) :
    ∀ t' ∈ sem gniProg s', t' "low" = 0 := by
  intro t' ht'
  simp only [gniProg, sem_choice, sem_assign, Set.mem_union,
    Set.mem_singleton_iff] at ht'
  rcases ht' with rfl | rfl
  · simp [hh']
  · simp

/-- **The GNI-refuting certificate**: the `atom` component exhibits a jointly
reachable `(low = 1, low = 0)` pair; the second component covers the right
side *exhaustively* with `low = 0`. The second component is a bespoke shallow
assertion — the assertion language is closed under arbitrary predicates. -/
theorem gni_cert :
    ⦃preGNI⦄ gniProg ~ gniProg
      ⦃(atom fun t t' => t "low" = 1 ∧ t' "low" = 0) ⊕ₒ
        (fun _ n' => ∀ t' ∈ n', t' "low" = 0)⦄ := by
  rintro m m' ⟨⟨s₀, hs₀⟩, ⟨s₀', hs₀'⟩, hall⟩
  have hright : ∀ t' ∈ semLift gniProg m', t' "low" = 0 := by
    intro t' ht'
    obtain ⟨s', hs', ht'⟩ := mem_semLift.mp ht'
    exact gni_right_low (hall s₀ hs₀ s' hs').2 t' ht'
  refine ⟨(fun s => Function.update s "low" (s "h")) '' m, semLift gniProg m,
    semLift gniProg m', semLift gniProg m', ?_, (Set.union_self _).symm, ?_, ?_⟩
  · refine (Set.union_eq_self_of_subset_left ?_).symm
    rintro t ⟨s, hs, rfl⟩
    refine mem_semLift.mpr ⟨s, hs, ?_⟩
    simp only [gniProg, sem_choice, sem_assign]
    exact Set.mem_union_left _ rfl
  · refine ⟨⟨_, Set.mem_image_of_mem _ hs₀⟩,
      semLift_nonempty (by simp [gniProg]) ⟨s₀', hs₀'⟩, ?_⟩
    rintro t ⟨s, hs, rfl⟩ t' ht'
    obtain ⟨hh, -⟩ := hall s hs s₀' hs₀'
    exact ⟨by simp [hh], hright t' ht'⟩
  · exact hright

/-- The certificate refutes GNI: the reachable `low = 1` outcome on the left
has no low-match on the right, whose outcomes are exhaustively `low = 0`. -/
theorem not_GNI : ¬ GNI gniProg := by
  intro hGNI
  have hc := gni_cert {sth 1 0} {sth 0 0} preGNI_sat
  rw [semLift_singleton, semLift_singleton] at hc
  obtain ⟨n₁, n₂, n₁', n₂', he, he', hatom, hQ⟩ := hc
  obtain ⟨⟨t, ht⟩, ⟨u', hu'⟩, hcross⟩ := hatom
  have ht1 : t "low" = 1 := (hcross t ht u' hu').1
  have htmem : t ∈ sem gniProg (sth 1 0) := by
    rw [he]; exact Set.mem_union_left _ ht
  obtain ⟨t', ht', heq⟩ := hGNI (sth 1 0) (sth 0 0) t htmem
  have ht0 : t' "low" = 0 := by
    have : t' ∈ n₁' ∪ n₂' := he' ▸ ht'
    rcases this with h | h
    · exact (hcross t ht t' h).2
    · exact hQ t' h
  omega

end RelOL
