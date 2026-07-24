import RelationalOutcomeLogic.Kleisli

/-!
# Relational outcome assertions

The core of RelOL: assertions over *pairs* of outcome sets, polymorphic in the
carrier types `α β` from day one. Since the PCM is `(∪, ∅)` at every carrier,
nothing here is specific to a language or state type — the heterogeneous
instantiation (`α := StC`, `β := Except Unit StR`) reuses this file verbatim.

* `atom r` — doubled nonemptiness (joint reachability) + the cross-product
  lifting of the state relation `r` (relational analogue of OL Def. 5.4).
* `oplus` (`⊕ₒ`) — the pairwise outcome conjunction: both sides split in sync,
  overlap-friendly.
* The helper kit (`oplus_intro`, `oplus_left_top`, `rel_true_positives`, …)
  keeps example proofs away from raw 4-existential splits.
-/

namespace RelOL

variable {α β : Type*}

/-- Relational outcome assertions: predicates over pairs of outcome sets. -/
def RAssn (α β : Type*) := Set α → Set β → Prop

/-- Relational atomic satisfaction: both sides reachable (nonempty), and every
cross pair of outcomes related by `r`. -/
def atom (r : α → β → Prop) : RAssn α β := fun m m' =>
  m.Nonempty ∧ m'.Nonempty ∧ ∀ x ∈ m, ∀ y ∈ m', r x y

/-- Pairwise outcome conjunction: both sides split simultaneously (overlap-friendly). -/
def oplus (P Q : RAssn α β) : RAssn α β := fun m m' =>
  ∃ m₁ m₂ m₁' m₂', m = m₁ ∪ m₂ ∧ m' = m₁' ∪ m₂' ∧ P m₁ m₁' ∧ Q m₂ m₂'

/-- The trivial relational assertion (holds of anything, including empty sides). -/
def rtop : RAssn α β := fun _ _ => True

/-- Relational `⊤^⊕`: joint divergence — no outcomes on either side. -/
def rempty : RAssn α β := fun m m' => m = ∅ ∧ m' = ∅

/-- Entailment of relational assertions. -/
def entail (P Q : RAssn α β) : Prop := ∀ m m', P m m' → Q m m'

/-- Swap the two sides (used by the `Sym` rule; swaps the carriers, so it stays
well-typed heterogeneously). -/
def RAssn.swap (R : RAssn α β) : RAssn β α := fun m m' => R m' m

@[inherit_doc] scoped infixr:60 " ⊕ₒ " => oplus

/-! ## Helper kit -/

@[simp] theorem atom_singleton_iff {r : α → β → Prop} {a : α} {b : β} :
    atom r {a} {b} ↔ r a b := by
  simp [atom]

theorem atom_pair_elim {r : α → β → Prop} {m m'} (h : atom r m m') {x y}
    (hx : x ∈ m) (hy : y ∈ m') : r x y := h.2.2 x hx y hy

theorem atom_mono {r r' : α → β → Prop} (h : ∀ x y, r x y → r' x y) :
    entail (atom r) (atom r') :=
  fun _ _ ⟨hne, hne', hall⟩ => ⟨hne, hne', fun x hx y hy => h x y (hall x hx y hy)⟩

theorem oplus_intro {P Q : RAssn α β} {m₁ m₂ m₁' m₂'} (h₁ : P m₁ m₁') (h₂ : Q m₂ m₂') :
    (P ⊕ₒ Q) (m₁ ∪ m₂) (m₁' ∪ m₂') := ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩

/-- `P ⟹ P ⊕ ⊤` via the trivial split `(m ∪ ∅, m' ∪ ∅)`. -/
theorem oplus_left_top {P : RAssn α β} {m m'} (h : P m m') : (P ⊕ₒ rtop) m m' :=
  ⟨m, ∅, m', ∅, (Set.union_empty m).symm, (Set.union_empty m').symm, h, trivial⟩

/-- Dropping outcomes (relational Lemma B.1): `P ⊕ Q ⟹ P ⊕ ⊤`. -/
theorem oplus_drop {P Q : RAssn α β} : entail (P ⊕ₒ Q) (P ⊕ₒ rtop) := by
  rintro m m' ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, -⟩
  exact ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, trivial⟩

theorem oplus_mono {P P' Q Q' : RAssn α β} (hP : entail P P') (hQ : entail Q Q') :
    entail (P ⊕ₒ Q) (P' ⊕ₒ Q') := by
  rintro m m' ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩
  exact ⟨m₁, m₂, m₁', m₂', rfl, rfl, hP _ _ h₁, hQ _ _ h₂⟩

theorem oplus_comm {P Q : RAssn α β} : entail (P ⊕ₒ Q) (Q ⊕ₒ P) := by
  rintro m m' ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩
  exact ⟨m₂, m₁, m₂', m₁', Set.union_comm .., Set.union_comm .., h₂, h₁⟩

theorem oplus_assoc {P Q R : RAssn α β} : entail ((P ⊕ₒ Q) ⊕ₒ R) (P ⊕ₒ (Q ⊕ₒ R)) := by
  rintro m m' ⟨m₁₂, m₃, m₁₂', m₃', rfl, rfl, ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩, h₃⟩
  exact ⟨m₁, m₂ ∪ m₃, m₁', m₂' ∪ m₃', Set.union_assoc .., Set.union_assoc .., h₁,
    oplus_intro h₂ h₃⟩

/-- Reachability extraction: an under-approximate relational atomic claim
`atom r ⊕ ⊤` guarantees a *witness pair* of jointly reachable outcomes related
by `r`. This is the engine behind the relational Principle of Denial. -/
theorem rel_true_positives {r : α → β → Prop} {m m'} (h : (atom r ⊕ₒ rtop) m m') :
    ∃ x ∈ m, ∃ y ∈ m', r x y := by
  obtain ⟨m₁, m₂, m₁', m₂', rfl, rfl, ⟨⟨x, hx⟩, ⟨y, hy⟩, hall⟩, -⟩ := h
  exact ⟨x, Set.mem_union_left _ hx, y, Set.mem_union_left _ hy, hall x hx y hy⟩

end RelOL
