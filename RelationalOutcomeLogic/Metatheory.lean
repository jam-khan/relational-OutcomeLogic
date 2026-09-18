import RelationalOutcomeLogic.Rules

/-! # Metatheory: falsification, denial, failure modes, and the (in)completeness of Seq -/

namespace RelOL

variable {α β γ δ : Type*}

/-! ## Falsification and denial -/

/-- Falsification: an untrue quadruple is disproved by a true one from an exact pre-model. -/
theorem falsification {F : Set α → Set γ} {G : Set β → Set δ}
    {R : RAssn α β} {S : RAssn γ δ} :
    ¬ quadSem F G R S ↔
      ∃ m₀ m₀', R m₀ m₀' ∧
        quadSem F G (fun m m' => m = m₀ ∧ m' = m₀') (fun n n' => ¬ S n n') := by
  constructor
  · intro h
    unfold quadSem at h
    push Not at h
    obtain ⟨m₀, m₀', hR, hnS⟩ := h
    exact ⟨m₀, m₀', hR, by rintro m m' ⟨rfl, rfl⟩; exact hnS⟩
  · rintro ⟨m₀, m₀', hR, hq⟩ h
    exact hq m₀ m₀' ⟨rfl, rfl⟩ (h m₀ m₀' hR)

/-- Principle of Denial: a true quadruple with a satisfiable pre and an incompatible post
refutes the specification. -/
theorem denial {F : Set α → Set γ} {G : Set β → Set δ}
    {R : RAssn α β} {S T : RAssn γ δ} (h : quadSem F G R T)
    (hTS : ∀ n n', T n n' → ¬ S n n') (hsat : ∃ m m', R m m') :
    ¬ quadSem F G R S := by
  intro hq
  obtain ⟨m, m', hm⟩ := hsat
  exact hTS _ _ (h m m' hm) (hq m m' hm)

/-! ## Failure modes, n = 1 (complete enumeration) -/

/-- One atom fails by left divergence, right divergence, or a reachable bad pair. -/
theorem not_atom_iff {r : α → β → Prop} {m : Set α} {m' : Set β} :
    ¬ atom r m m' ↔ m = ∅ ∨ m' = ∅ ∨ ∃ x ∈ m, ∃ y ∈ m', ¬ r x y := by
  unfold atom
  push Not
  constructor
  · intro h
    by_cases hm : m = ∅
    · exact Or.inl hm
    by_cases hm' : m' = ∅
    · exact Or.inr (Or.inl hm')
    · exact Or.inr (Or.inr (h (Set.nonempty_iff_ne_empty.mpr hm)
        (Set.nonempty_iff_ne_empty.mpr hm')))
  · rintro (rfl | rfl | ⟨x, hx, y, hy, hr⟩) hne hne'
    · exact absurd hne (by simp)
    · exact absurd hne' (by simp)
    · exact ⟨x, hx, y, hy, hr⟩

/-- The bad-pair mode is itself a certificate. -/
theorem bad_pair_oplus {r : α → β → Prop} {m : Set α} {m' : Set β} :
    (∃ x ∈ m, ∃ y ∈ m', ¬ r x y) ↔ ((atom fun x y => ¬ r x y) ⊕ₒ ⊤ₒ) m m' :=
  atom_oplus_top_iff.symm

theorem not_atom_enum {r : α → β → Prop} {m : Set α} {m' : Set β} :
    ¬ atom r m m' ↔ m = ∅ ∨ m' = ∅ ∨ ((atom fun x y => ¬ r x y) ⊕ₒ rtop) m m' := by
  rw [not_atom_iff, bad_pair_oplus]

/-! ## Failure modes, n ≥ 2: sound modes -/

/-- Left divergence refutes any `⊕` of atoms. -/
theorem not_oplus_atoms_left_empty {r₁ r₂ : α → β → Prop} {m' : Set β} :
    ¬ (atom r₁ ⊕ₒ atom r₂) (∅ : Set α) m' := by
  rintro ⟨m₁, m₂, m₁', m₂', hm, -, ⟨⟨x, hx⟩, -, -⟩, -⟩
  have hx' : x ∈ m₁ ∪ m₂ := Set.mem_union_left _ hx
  rw [← hm] at hx'
  simp at hx'

/-- Right divergence refutes any `⊕` of atoms. -/
theorem not_oplus_atoms_right_empty {r₁ r₂ : α → β → Prop} {m : Set α} :
    ¬ (atom r₁ ⊕ₒ atom r₂) m (∅ : Set β) := by
  rintro ⟨m₁, m₂, m₁', m₂', -, hm', ⟨-, ⟨y, hy⟩, -⟩, -⟩
  have hy' : y ∈ m₁' ∪ m₂' := Set.mem_union_left _ hy
  rw [← hm'] at hy'
  simp at hy'

/-- If `r₁` relates no reachable pair, the `⊕`-spec fails. -/
theorem not_oplus_atoms_of_rel_empty_left {r₁ r₂ : α → β → Prop} {m : Set α} {m' : Set β}
    (h : ∀ x ∈ m, ∀ y ∈ m', ¬ r₁ x y) : ¬ (atom r₁ ⊕ₒ atom r₂) m m' := by
  rintro ⟨m₁, m₂, m₁', m₂', hm, hm', ⟨⟨x, hx⟩, ⟨y, hy⟩, hall⟩, -⟩
  exact h x (hm.symm ▸ Set.mem_union_left _ hx) y (hm'.symm ▸ Set.mem_union_left _ hy)
    (hall x hx y hy)

theorem not_oplus_atoms_of_rel_empty_right {r₁ r₂ : α → β → Prop} {m : Set α} {m' : Set β}
    (h : ∀ x ∈ m, ∀ y ∈ m', ¬ r₂ x y) : ¬ (atom r₁ ⊕ₒ atom r₂) m m' :=
  fun hc => not_oplus_atoms_of_rel_empty_left h (oplus_comm _ _ hc)

/-- Orphan: a left outcome with no partner under either relation refutes the spec. -/
theorem not_oplus_atoms_of_left_orphan {r₁ r₂ : α → β → Prop} {m : Set α} {m' : Set β}
    (x : α) (hx : x ∈ m) (h : ∀ y ∈ m', ¬ r₁ x y ∧ ¬ r₂ x y) :
    ¬ (atom r₁ ⊕ₒ atom r₂) m m' := by
  rintro ⟨m₁, m₂, m₁', m₂', hm, hm', ⟨-, ⟨y₁, hy₁⟩, hall₁⟩, ⟨-, ⟨y₂, hy₂⟩, hall₂⟩⟩
  have hxm : x ∈ m₁ ∪ m₂ := hm ▸ hx
  rcases hxm with hx₁ | hx₂
  · exact (h y₁ (hm'.symm ▸ Set.mem_union_left _ hy₁)).1 (hall₁ x hx₁ y₁ hy₁)
  · exact (h y₂ (hm'.symm ▸ Set.mem_union_right _ hy₂)).2 (hall₂ x hx₂ y₂ hy₂)

/-! ## Failure modes, n ≥ 2: where the unary story breaks -/

/-- For `n ≥ 2` a reachable bad pair does *not* refute: the split can separate it. -/
theorem bad_pair_does_not_refute :
    ∃ (r₁ r₂ : Bool → Bool → Prop) (m m' : Set Bool),
      (∃ x ∈ m, ∃ y ∈ m', ¬ r₁ x y ∧ ¬ r₂ x y) ∧ (atom r₁ ⊕ₒ atom r₂) m m' := by
  refine ⟨fun a b => a = true ∧ b = true, fun a b => a = false ∧ b = false,
    Set.univ, Set.univ,
    ⟨true, Set.mem_univ _, false, Set.mem_univ _, by simp, by simp⟩, ?_⟩
  refine ⟨{true}, {false}, {true}, {false}, ?_, ?_, ?_, ?_⟩
  · ext b; cases b <;> simp
  · ext b; cases b <;> simp
  · exact ⟨⟨true, rfl⟩, ⟨true, rfl⟩, by simp⟩
  · exact ⟨⟨false, rfl⟩, ⟨false, rfl⟩, by simp⟩

/-- No unary-style enumeration is complete: every local failure mode is absent, yet the
spec is unsatisfiable. Satisfaction is a rectangle-cover problem (`oplus_atom_iff_cover`). -/
theorem enumeration_incomplete :
    ∃ (r₁ r₂ : Bool → Bool → Prop) (m m' : Set Bool),
      m.Nonempty ∧ m'.Nonempty ∧
      (∃ x ∈ m, ∃ y ∈ m', r₁ x y) ∧
      (∃ x ∈ m, ∃ y ∈ m', r₂ x y) ∧
      (∀ x ∈ m, ∃ y ∈ m', r₁ x y ∨ r₂ x y) ∧
      (∀ y ∈ m', ∃ x ∈ m, r₁ x y ∨ r₂ x y) ∧
      ¬ (atom r₁ ⊕ₒ atom r₂) m m' := by
  refine ⟨(· = ·), (· ≠ ·), Set.univ, Set.univ, ⟨true, Set.mem_univ _⟩,
    ⟨true, Set.mem_univ _⟩,
    ⟨true, Set.mem_univ _, true, Set.mem_univ _, rfl⟩,
    ⟨true, Set.mem_univ _, false, Set.mem_univ _, by simp⟩,
    fun x _ => ⟨x, Set.mem_univ _, Or.inl rfl⟩,
    fun y _ => ⟨y, Set.mem_univ _, Or.inl rfl⟩, ?_⟩
  rintro ⟨m₁, m₂, m₁', m₂', hm, hm', ⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩, hall₁⟩,
    ⟨-, -, hall₂⟩⟩
  have hx₁y₁ : x₁ = y₁ := hall₁ x₁ hx₁ y₁ hy₁
  have hnb₂ : (!x₁) ∈ m₂ := by
    have hmem : (!x₁) ∈ m₁ ∪ m₂ := by rw [← hm]; exact Set.mem_univ _
    rcases hmem with h | h
    · have := hall₁ _ h _ hy₁
      rw [← hx₁y₁] at this
      simp at this
    · exact h
  have hnb₂' : (!x₁) ∈ m₂' := by
    have hmem : (!x₁) ∈ m₁' ∪ m₂' := by rw [← hm']; exact Set.mem_univ _
    rcases hmem with h | h
    · have := hall₁ _ hx₁ _ h
      simp at this
    · exact h
  exact hall₂ _ hnb₂ _ hnb₂' rfl

/-- `atom r₁ ⊕ atom r₂` is a cover of both sides by an `r₁`- and an `r₂`-rectangle. -/
theorem oplus_atom_iff_cover {r₁ r₂ : α → β → Prop} {m : Set α} {m' : Set β} :
    (atom r₁ ⊕ₒ atom r₂) m m' ↔
      ∃ A B A' B', A ∪ B = m ∧ A' ∪ B' = m' ∧
        A.Nonempty ∧ A'.Nonempty ∧ B.Nonempty ∧ B'.Nonempty ∧
        A ×ˢ A' ⊆ {p | r₁ p.1 p.2} ∧ B ×ˢ B' ⊆ {p | r₂ p.1 p.2} := by
  constructor
  · rintro ⟨A, B, A', B', rfl, rfl, ⟨hA, hA', h₁⟩, ⟨hB, hB', h₂⟩⟩
    exact ⟨A, B, A', B', rfl, rfl, hA, hA', hB, hB',
      fun p hp => h₁ p.1 hp.1 p.2 hp.2, fun p hp => h₂ p.1 hp.1 p.2 hp.2⟩
  · rintro ⟨A, B, A', B', rfl, rfl, hA, hA', hB, hB', h₁, h₂⟩
    exact ⟨A, B, A', B', rfl, rfl, ⟨hA, hA', fun x hx y hy => h₁ (Set.mk_mem_prod hx hy)⟩,
      ⟨hB, hB', fun x hx y hy => h₂ (Set.mk_mem_prod hx hy)⟩⟩

/-! ## Strongest posts, and the (in)completeness of Seq -/

def spost (F : Set α → Set γ) (G : Set β → Set δ) (R : RAssn α β) : RAssn γ δ :=
  fun n n' => ∃ m m', R m m' ∧ n = F m ∧ n' = G m'

theorem quadSem_iff_spost_entail {F : Set α → Set γ} {G : Set β → Set δ}
    {R : RAssn α β} {S : RAssn γ δ} : ⟪R⟫ F , G ⟪S⟫ ↔ (spost F G R ⟹ₒ S) :=
  ⟨by rintro h n n' ⟨m, m', hm, rfl, rfl⟩; exact h m m' hm,
   fun h m m' hm => h _ _ ⟨m, m', hm, rfl, rfl⟩⟩

/-- Seq is complete for arbitrary mid-conditions. -/
theorem quadSem_comp_complete {ε ζ : Type*} {F : Set α → Set γ} {G : Set β → Set δ}
    {F' : Set γ → Set ε} {G' : Set δ → Set ζ} {R : RAssn α β} {T : RAssn ε ζ}
    (h : ⟪R⟫ F' ∘ F , G' ∘ G ⟪T⟫) : ∃ S, ⟪R⟫ F , G ⟪S⟫ ∧ ⟪S⟫ F' , G' ⟪T⟫ :=
  ⟨spost F G R, fun m m' hm => ⟨m, m', hm, rfl, rfl⟩,
   by rintro n n' ⟨m, m', hm, rfl, rfl⟩; exact h m m' hm⟩

/-- ... but not for coupling mid-conditions: the possibilistic shadow of pRHL's asynchrony
wall. Repair: `quad_couple_of_LR`, with one mid-relation per direction. -/
theorem seq_couple_incomplete :
    ∃ (c₁ c₂ c₁' c₂' : Cmd) (r r' : State → State → Prop),
      (⦃couple r⦄ c₁ ;; c₂ ~ c₁' ;; c₂' ⦃couple r'⦄) ∧
      ¬ ∃ rm, (⦃couple r⦄ c₁ ~ c₁' ⦃couple rm⦄) ∧ (⦃couple rm⦄ c₂ ~ c₂' ⦃couple r'⦄) := by
  refine ⟨(x ::= 0) + (x ::= 1), SKIP, x ::= 0, (x ::= 0) + (x ::= 1), (· = ·), (· = ·), ?_, ?_⟩
  · rw [quad_couple_lift_iff]
    rintro s s' rfl
    simp only [Cmd.add_def, sem_seq, sem_choice, sem_assign, sem_skip, kleisli_union,
      kleisli_singleton, Function.update_idem]
    exact ⟨fun t ht => ⟨t, ht, rfl⟩, fun t ht => ⟨t, ht, rfl⟩⟩
  · rintro ⟨rm, h₁, h₂⟩
    rw [quad_couple_lift_iff] at h₁ h₂
    have hmid := h₁ (fun _ => 0) (fun _ => 0) rfl
    simp only [Cmd.add_def, sem_choice, sem_assign] at hmid
    obtain ⟨y, hy, hrm⟩ := hmid.1 _ (Or.inr rfl)
    obtain rfl := Set.mem_singleton_iff.mp hy
    have hpost := h₂ _ _ hrm
    simp only [Cmd.add_def, sem_skip, sem_choice, sem_assign, Function.update_idem] at hpost
    obtain ⟨u, hu, hu'⟩ := hpost.2 _ (Or.inl rfl)
    obtain rfl := Set.mem_singleton_iff.mp hu
    simpa using congrFun hu' "x"

end RelOL
