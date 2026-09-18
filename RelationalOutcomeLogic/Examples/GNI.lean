import RelationalOutcomeLogic.Rules

/-! # Generalised noninterference (∀∃), refuted by a certificate with an exhaustive component -/

namespace RelOL

def sth (h low : Int) : State :=
  fun v => if v = "h" then h else if v = "low" then low else 0

@[simp] theorem sth_h (h low : Int) : sth h low "h" = h := by simp [sth]

@[simp] theorem sth_low (h low : Int) : sth h low "low" = low := by simp [sth]

/-- Publishes the secret `h`, or `0`. -/
def gniProg : Cmd := (low ::= h) + (low ::= 0)

/-- Every outcome is low-matched by some outcome from any other initial state. -/
def GNI (c : Cmd) : Prop :=
  ∀ s s' : State, ∀ t ∈ sem c s, ∃ t' ∈ sem c s', t "low" = t' "low"

def preGNI : RAssn State State := ⌈h = 1 ∧ h' = 0⌉

theorem preGNI_sat : preGNI {sth 1 0} {sth 0 0} := by
  rw [preGNI, atom_singleton_iff]
  simp

theorem gni_right_low {s' : State} (hh' : s' "h" = 0) :
    ∀ t' ∈ sem gniProg s', t' "low" = 0 := by
  intro t' ht'
  simp only [gniProg, Cmd.add_def, sem_choice, sem_assign, Set.mem_union,
    Set.mem_singleton_iff] at ht'
  rcases ht' with rfl | rfl
  · simp [hh']
  · simp

/-- A reachable `(low = 1, low = 0)` pair, and the right side is exhaustively `low = 0`. -/
theorem gni_cert :
    ⦃preGNI⦄ gniProg ~ gniProg
      ⦃⌈low = 1 ∧ low' = 0⌉ ⊕ₒ fun _ n' => ∀ t' ∈ n', t' "low" = 0⦄ := by
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
    simp only [gniProg, Cmd.add_def, sem_choice, sem_assign]
    exact Set.mem_union_left _ rfl
  · refine ⟨⟨_, Set.mem_image_of_mem _ hs₀⟩,
      semLift_nonempty (by simp [gniProg]) ⟨s₀', hs₀'⟩, ?_⟩
    rintro t ⟨s, hs, rfl⟩ t' ht'
    obtain ⟨hh, -⟩ := hall s hs s₀' hs₀'
    exact ⟨by simp [hh], hright t' ht'⟩
  · exact hright

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
