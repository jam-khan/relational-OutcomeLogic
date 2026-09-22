import RelationalOutcomeLogic.Set.Semantics

/-!
# Relational outcome assertions

Predicates over pairs of outcome sets, polymorphic in the two carriers (so the two
programs may live in different languages). The outcome monoid is `(∪, ∅)`.

Notation (scoped): `⌈r⌉` atom, `⌈r⌉ʷ` weak atom, `P ⊕ₒ Q`, `⊤ₒ`, `P ⟹ₒ Q`, `Rᵀ`.
-/

namespace RelOL

variable {α β : Type*}

def RAssn (α β : Type*) := Set α → Set β → Prop

/-- Product atom: both sides reachable, and every pair of outcomes is related. -/
def atom (r : α → β → Prop) : RAssn α β :=
  fun m m' => m.Nonempty ∧ m'.Nonempty ∧ ∀ x ∈ m, ∀ y ∈ m', r x y

/-- Weak atom: every pair of outcomes is related (divergence-tolerant, the RHL shape). -/
def atomW (r : α → β → Prop) : RAssn α β :=
  fun m m' => ∀ x ∈ m, ∀ y ∈ m', r x y

/-- Outcome conjunction: both sides split in sync; pieces may overlap. -/
def oplus (P Q : RAssn α β) : RAssn α β :=
  fun m m' => ∃ m₁ m₂ m₁' m₂', m = m₁ ∪ m₂ ∧ m' = m₁' ∪ m₂' ∧ P m₁ m₁' ∧ Q m₂ m₂'

/-- Infinitary outcome conjunction. -/
def oplusFam {ι : Type*} (φ : ι → RAssn α β) : RAssn α β :=
  fun m m' => ∃ (f : ι → Set α) (g : ι → Set β),
    m = ⋃ i, f i ∧ m' = ⋃ i, g i ∧ ∀ i, φ i (f i) (g i)

def rtop : RAssn α β := fun _ _ => True

/-- Joint divergence. -/
def rempty : RAssn α β := fun m m' => m = ∅ ∧ m' = ∅

/-- Exactly this pair of outcome sets. -/
def exactly (m₀ : Set α) (m₀' : Set β) : RAssn α β := fun m m' => m = m₀ ∧ m' = m₀'

def entail (P Q : RAssn α β) : Prop := ∀ m m', P m m' → Q m m'

def RAssn.swap (R : RAssn α β) : RAssn β α := fun m m' => R m' m

@[inherit_doc] scoped infixr:60 " ⊕ₒ " => oplus
scoped notation "⌈" r "⌉" => atom r
scoped notation "⌈" r "⌉ʷ" => atomW r
scoped notation "⊤ₒ" => rtop
scoped infixr:25 " ⟹ₒ " => entail
scoped postfix:max "ᵀ" => RAssn.swap

/-! ## Atoms -/

@[simp] theorem atom_singleton_iff {r : α → β → Prop} {a : α} {b : β} :
    atom r {a} {b} ↔ r a b := by
  simp [atom]

theorem atom_pair_elim {r : α → β → Prop} {m m'} (h : atom r m m') {x y}
    (hx : x ∈ m) (hy : y ∈ m') : r x y :=
  h.2.2 x hx y hy

theorem atom_mono {r r' : α → β → Prop} (h : ∀ x y, r x y → r' x y) :
    atom r ⟹ₒ atom r' :=
  fun _ _ ⟨hne, hne', hall⟩ => ⟨hne, hne', fun x hx y hy => h x y (hall x hx y hy)⟩

theorem atom_iff_atomW {r : α → β → Prop} {m : Set α} {m' : Set β} :
    atom r m m' ↔ m.Nonempty ∧ m'.Nonempty ∧ atomW r m m' := Iff.rfl

theorem atomW_of_atom {r : α → β → Prop} : atom r ⟹ₒ atomW r :=
  fun _ _ h => h.2.2

@[simp] theorem atomW_singleton_iff {r : α → β → Prop} {a : α} {b : β} :
    atomW r {a} {b} ↔ r a b := by
  simp [atomW]

theorem atomW_mono {r r' : α → β → Prop} (h : ∀ x y, r x y → r' x y) :
    atomW r ⟹ₒ atomW r' :=
  fun _ _ h1 x hx y hy => h x y (h1 x hx y hy)

@[simp] theorem atomW_empty_left (r : α → β → Prop) (m' : Set β) : atomW r ∅ m' := by
  simp [atomW]

@[simp] theorem atomW_empty_right (r : α → β → Prop) (m : Set α) : atomW r m ∅ := by
  simp [atomW]

/-! ## Outcome conjunction -/

theorem oplus_intro {P Q : RAssn α β} {m₁ m₂ m₁' m₂'} (h₁ : P m₁ m₁') (h₂ : Q m₂ m₂') :
    (P ⊕ₒ Q) (m₁ ∪ m₂) (m₁' ∪ m₂') :=
  ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩

theorem oplus_left_top {P : RAssn α β} {m m'} (h : P m m') : (P ⊕ₒ ⊤ₒ) m m' :=
  ⟨m, ∅, m', ∅, (Set.union_empty m).symm, (Set.union_empty m').symm, h, trivial⟩

theorem oplus_mono {P P' Q Q' : RAssn α β} (hP : P ⟹ₒ P') (hQ : Q ⟹ₒ Q') :
    P ⊕ₒ Q ⟹ₒ P' ⊕ₒ Q' := by
  rintro m m' ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩
  exact oplus_intro (hP _ _ h₁) (hQ _ _ h₂)

theorem oplus_drop {P Q : RAssn α β} : P ⊕ₒ Q ⟹ₒ P ⊕ₒ ⊤ₒ :=
  oplus_mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem oplus_comm {P Q : RAssn α β} : P ⊕ₒ Q ⟹ₒ Q ⊕ₒ P := by
  rintro m m' ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩
  exact ⟨m₂, m₁, m₂', m₁', Set.union_comm .., Set.union_comm .., h₂, h₁⟩

theorem oplus_assoc {P Q R : RAssn α β} : (P ⊕ₒ Q) ⊕ₒ R ⟹ₒ P ⊕ₒ (Q ⊕ₒ R) := by
  rintro m m' ⟨m₁₂, m₃, m₁₂', m₃', rfl, rfl, ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩, h₃⟩
  exact ⟨m₁, m₂ ∪ m₃, m₁', m₂' ∪ m₃', Set.union_assoc .., Set.union_assoc .., h₁,
    oplus_intro h₂ h₃⟩

/-- `⊕ ⊤` certificates survive enlarging the outcome sets (new outcomes go into `⊤`). -/
theorem oplus_top_mono {S : RAssn α β} {m₀ m : Set α} {m₀' m' : Set β}
    (h : (S ⊕ₒ ⊤ₒ) m₀ m₀') (hm : m₀ ⊆ m) (hm' : m₀' ⊆ m') : (S ⊕ₒ ⊤ₒ) m m' := by
  obtain ⟨m₁, m₂, m₁', m₂', rfl, rfl, hS, -⟩ := h
  exact ⟨m₁, m, m₁', m',
    (Set.union_eq_self_of_subset_left (Set.subset_union_left.trans hm)).symm,
    (Set.union_eq_self_of_subset_left (Set.subset_union_left.trans hm')).symm, hS, trivial⟩

/-- An under-approximate atom is exactly a jointly reachable related pair. -/
theorem atom_oplus_top_iff {r : α → β → Prop} {m : Set α} {m' : Set β} :
    (atom r ⊕ₒ ⊤ₒ) m m' ↔ ∃ x ∈ m, ∃ y ∈ m', r x y := by
  constructor
  · rintro ⟨m₁, m₂, m₁', m₂', rfl, rfl, ⟨⟨x, hx⟩, ⟨y, hy⟩, hall⟩, -⟩
    exact ⟨x, Set.mem_union_left _ hx, y, Set.mem_union_left _ hy, hall x hx y hy⟩
  · rintro ⟨x, hx, y, hy, hr⟩
    exact oplus_top_mono (oplus_left_top (atom_singleton_iff.mpr hr))
      (Set.singleton_subset_iff.mpr hx) (Set.singleton_subset_iff.mpr hy)

/-- True positives: an `atom r ⊕ ⊤` certificate yields a reachable `r`-pair. -/
theorem rel_true_positives {r : α → β → Prop} {m m'} (h : (atom r ⊕ₒ ⊤ₒ) m m') :
    ∃ x ∈ m, ∃ y ∈ m', r x y :=
  atom_oplus_top_iff.mp h

/-! ## Swap -/

@[simp] theorem RAssn.swap_swap (R : RAssn α β) : R.swap.swap = R := rfl

theorem RAssn.swap_oplus (P Q : RAssn α β) : (P ⊕ₒ Q).swap = (P.swap ⊕ₒ Q.swap) := by
  funext m' m
  unfold RAssn.swap oplus
  grind

end RelOL
