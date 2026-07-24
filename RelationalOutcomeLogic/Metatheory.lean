import RelationalOutcomeLogic.Rules

/-!
# RelOL metatheory: falsification, denial, and failure-mode analysis

Semantic-level results, in the tradition of OL Thm. 5.1 (whose proof is purely
semantic and instance-independent):

* `falsification` — every untrue relational quadruple is disprovable by a true
  one (relational Thm. 5.1; the witness is the exact-pair assertion).
* `denial` — the relational Principle of Denial (Thm. 5.2's easy direction).
* `not_atom_iff` / `not_atom_enum` — the **complete** failure-mode enumeration
  for a single relational atom (n = 1): left divergence, right divergence, or a
  reachable bad pair — the latter itself a positive RelOL certificate (`⊕ ⊤`),
  via an *overlapping* split. Four primitives where unary OL (Lemma 5.5) has three.
* For `⊕`-lists (n ≥ 2) the story genuinely diverges from unary OL:
  - "bad pair reachable" is **no longer sound** as a refutation (the two sides
    of a split need not co-locate a given pair) — see
    `bad_pair_does_not_refute`;
  - the sound generalizations are the *orphan* modes
    (`not_oplus_atoms_of_left_orphan`) and per-relation joint unreachability
    (`not_oplus_atoms_of_rel_empty_left`);
  - and **no unary-style enumeration is complete**: `enumeration_incomplete`
    exhibits a 2×2 Boolean instance where both sides are nonempty, both
    relations are witnessed, no outcome is an orphan — yet the spec is
    unsatisfiable. Satisfying `atom r₁ ⊕ atom r₂` is a *rectangle-cover*
    condition, and the cover can fail for irreducibly global reasons.
-/

namespace RelOL

variable {α β γ δ : Type*}

/-! ## Falsification and denial -/

/-- **Relational semantic falsification** (Thm. 5.1 analogue): an untrue
quadruple is always disprovable by a *true* quadruple whose precondition is a
satisfiable strengthening (here: the exact falsifying pair) and whose
postcondition is the negation. Purely semantic — holds for any lifts. -/
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

/-- **Relational Principle of Denial** (Thm. 5.2 analogue, easy direction):
a true quadruple with a satisfiable precondition and a postcondition
incompatible with `S` refutes `⟨R⟩ … ⟨S⟩`. -/
theorem denial {F : Set α → Set γ} {G : Set β → Set δ}
    {R : RAssn α β} {S T : RAssn γ δ} (h : quadSem F G R T)
    (hTS : ∀ n n', T n n' → ¬ S n n') (hsat : ∃ m m', R m m') :
    ¬ quadSem F G R S := by
  intro hq
  obtain ⟨m, m', hm⟩ := hsat
  exact hTS _ _ (h m m' hm) (hq m m' hm)

/-! ## Failure modes, n = 1 (complete enumeration) -/

/-- Complete failure-mode enumeration for one relational atom: left divergence,
right divergence, or a reachable bad pair. -/
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

/-- The bad-pair mode in *positive* form: a reachable bad pair is itself a RelOL
certificate `(atom ¬r) ⊕ ⊤`, via the overlapping splits `m = {x} ∪ m`,
`m' = {y} ∪ m'`. -/
theorem bad_pair_oplus {r : α → β → Prop} {m : Set α} {m' : Set β} :
    (∃ x ∈ m, ∃ y ∈ m', ¬ r x y) ↔ ((atom fun x y => ¬ r x y) ⊕ₒ rtop) m m' := by
  constructor
  · rintro ⟨x, hx, y, hy, hr⟩
    refine ⟨{x}, m, {y}, m', ?_, ?_, atom_singleton_iff.mpr hr, trivial⟩
    · ext z
      simp only [Set.mem_union, Set.mem_singleton_iff]
      exact ⟨Or.inr, fun h => h.elim (fun hz => hz ▸ hx) id⟩
    · ext z
      simp only [Set.mem_union, Set.mem_singleton_iff]
      exact ⟨Or.inr, fun h => h.elim (fun hz => hz ▸ hy) id⟩
  · exact rel_true_positives

/-- The n = 1 enumeration with the bad-pair mode as a positive certificate:
a relational atomic spec fails in exactly one of **four** ways (unary OL has
three, Lemma 5.5): left divergence, right divergence, or a certified bad pair. -/
theorem not_atom_enum {r : α → β → Prop} {m : Set α} {m' : Set β} :
    ¬ atom r m m' ↔ m = ∅ ∨ m' = ∅ ∨ ((atom fun x y => ¬ r x y) ⊕ₒ rtop) m m' := by
  rw [not_atom_iff, bad_pair_oplus]

/-! ## Failure modes, n ≥ 2: sound modes -/

/-- Sound mode: left divergence refutes any `⊕` of atoms. -/
theorem not_oplus_atoms_left_empty {r₁ r₂ : α → β → Prop} {m' : Set β} :
    ¬ (atom r₁ ⊕ₒ atom r₂) (∅ : Set α) m' := by
  rintro ⟨m₁, m₂, m₁', m₂', hm, -, ⟨⟨x, hx⟩, -, -⟩, -⟩
  have hx' : x ∈ m₁ ∪ m₂ := Set.mem_union_left _ hx
  rw [← hm] at hx'
  simp at hx'

/-- Sound mode: right divergence refutes any `⊕` of atoms. -/
theorem not_oplus_atoms_right_empty {r₁ r₂ : α → β → Prop} {m : Set α} :
    ¬ (atom r₁ ⊕ₒ atom r₂) m (∅ : Set β) := by
  rintro ⟨m₁, m₂, m₁', m₂', -, hm', ⟨-, ⟨y, hy⟩, -⟩, -⟩
  have hy' : y ∈ m₁' ∪ m₂' := Set.mem_union_left _ hy
  rw [← hm'] at hy'
  simp at hy'

/-- Sound mode: if `r₁` relates *no* reachable pair, the `⊕`-spec fails
(the relational analogue of unary OL's "outcome `Qᵢ` never reached"). -/
theorem not_oplus_atoms_of_rel_empty_left {r₁ r₂ : α → β → Prop} {m : Set α} {m' : Set β}
    (h : ∀ x ∈ m, ∀ y ∈ m', ¬ r₁ x y) : ¬ (atom r₁ ⊕ₒ atom r₂) m m' := by
  rintro ⟨m₁, m₂, m₁', m₂', hm, hm', ⟨⟨x, hx⟩, ⟨y, hy⟩, hall⟩, -⟩
  exact h x (hm.symm ▸ Set.mem_union_left _ hx) y (hm'.symm ▸ Set.mem_union_left _ hy)
    (hall x hx y hy)

theorem not_oplus_atoms_of_rel_empty_right {r₁ r₂ : α → β → Prop} {m : Set α} {m' : Set β}
    (h : ∀ x ∈ m, ∀ y ∈ m', ¬ r₂ x y) : ¬ (atom r₁ ⊕ₒ atom r₂) m m' :=
  fun hc => not_oplus_atoms_of_rel_empty_left h (oplus_comm _ _ hc)

/-- Sound mode (**orphan**, the correct relational generalization of unary OL's
"bad state reachable"): a left outcome with no partner under *either* relation
refutes the spec. Note the ∃∀ shape — unlike the n = 1 bad-pair mode, this is
*not* expressible as a `⊕ ⊤` certificate over a sub-rectangle. -/
theorem not_oplus_atoms_of_left_orphan {r₁ r₂ : α → β → Prop} {m : Set α} {m' : Set β}
    (x : α) (hx : x ∈ m) (h : ∀ y ∈ m', ¬ r₁ x y ∧ ¬ r₂ x y) :
    ¬ (atom r₁ ⊕ₒ atom r₂) m m' := by
  rintro ⟨m₁, m₂, m₁', m₂', hm, hm', ⟨-, ⟨y₁, hy₁⟩, hall₁⟩, ⟨-, ⟨y₂, hy₂⟩, hall₂⟩⟩
  have hxm : x ∈ m₁ ∪ m₂ := hm ▸ hx
  rcases hxm with hx₁ | hx₂
  · exact (h y₁ (hm'.symm ▸ Set.mem_union_left _ hy₁)).1 (hall₁ x hx₁ y₁ hy₁)
  · exact (h y₂ (hm'.symm ▸ Set.mem_union_right _ hy₂)).2 (hall₂ x hx₂ y₂ hy₂)

/-! ## Failure modes, n ≥ 2: where the unary story breaks -/

/-- **The unary bad-pair mode is unsound for n ≥ 2**: a reachable pair
satisfying neither relation does *not* refute `atom r₁ ⊕ atom r₂` — the split
can separate the two outcomes so they are never co-located. Witness: `m = {x, u}`,
`m' = {y, v}` with the bad pair `(x, y)` absorbed by the cross split
`({x}, {v}) / ({u}, {y})`. -/
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

/-- **Incompleteness of any unary-style enumeration** (the relational
Lemma 5.5 / D.3 obstruction, mechanized): a 2×2 Boolean instance where every
unary-style failure mode is absent — both sides nonempty, both relations
jointly witnessed, no orphans on either side — and yet `atom r₁ ⊕ atom r₂` is
unsatisfiable. The obstruction is global: satisfaction demands a *rectangle
cover* (`A×A' ⊆ r₁`, `B×B' ⊆ r₂`, `A ∪ B = m`, `A' ∪ B' = m'`), and with
`r₁ = (· = ·)`, `r₂ = (· ≠ ·)` any `r₁`-rectangle is a diagonal singleton,
forcing the complementary `r₂`-rectangle to contain a reflexive (equal) pair. -/
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

end RelOL
