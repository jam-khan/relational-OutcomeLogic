import RelationalOutcomeLogic.Set.Assertions

/-!
# Couplings

`couple r` pairs every outcome with an `r`-partner on the other side (bitotal);
`coupleL` / `coupleR` are its two halves (the ∀∃ shape of refinement and GNI);
`coupleNE` adds reachability and is the refutation-grade form.
-/

namespace RelOL

variable {α β γ δ : Type*}

def coupleL (r : α → β → Prop) : RAssn α β := fun m m' => ∀ x ∈ m, ∃ y ∈ m', r x y

def coupleR (r : α → β → Prop) : RAssn α β := fun m m' => ∀ y ∈ m', ∃ x ∈ m, r x y

def couple (r : α → β → Prop) : RAssn α β := fun m m' =>
  (∀ x ∈ m, ∃ y ∈ m', r x y) ∧ (∀ y ∈ m', ∃ x ∈ m, r x y)

def coupleNE (r : α → β → Prop) : RAssn α β := fun m m' => m.Nonempty ∧ couple r m m'

theorem couple_iff_LR {r : α → β → Prop} {m : Set α} {m' : Set β} :
    couple r m m' ↔ coupleL r m m' ∧ coupleR r m m' := Iff.rfl

/-- A coupling is a witness set of `r`-pairs whose projections are the two outcome sets. -/
theorem couple_iff_witness {r : α → β → Prop} {m : Set α} {m' : Set β} :
    couple r m m' ↔
      ∃ W : Set (α × β), (∀ p ∈ W, r p.1 p.2) ∧ Prod.fst '' W = m ∧ Prod.snd '' W = m' := by
  constructor
  · rintro ⟨hLR, hRL⟩
    refine ⟨{p | p.1 ∈ m ∧ p.2 ∈ m' ∧ r p.1 p.2}, fun p hp => hp.2.2, ?_, ?_⟩
    · ext x
      constructor
      · rintro ⟨p, hp, rfl⟩; exact hp.1
      · intro hx
        obtain ⟨y, hy, hr⟩ := hLR x hx
        exact ⟨(x, y), ⟨hx, hy, hr⟩, rfl⟩
    · ext y
      constructor
      · rintro ⟨p, hp, rfl⟩; exact hp.2.1
      · intro hy
        obtain ⟨x, hx, hr⟩ := hRL y hy
        exact ⟨(x, y), ⟨hx, hy, hr⟩, rfl⟩
  · rintro ⟨W, hr, rfl, rfl⟩
    exact ⟨by rintro x ⟨p, hp, rfl⟩; exact ⟨p.2, ⟨p, hp, rfl⟩, hr p hp⟩,
      by rintro y ⟨p, hp, rfl⟩; exact ⟨p.1, ⟨p, hp, rfl⟩, hr p hp⟩⟩

/-! ## Basic kit -/

@[simp] theorem couple_singleton_iff {r : α → β → Prop} {a : α} {b : β} :
    couple r {a} {b} ↔ r a b := by
  simp only [couple, Set.mem_singleton_iff, forall_eq, exists_eq_left, and_self]

@[simp] theorem coupleL_singleton_iff {r : α → β → Prop} {a : α} {b : β} :
    coupleL r {a} {b} ↔ r a b := by
  simp only [coupleL, Set.mem_singleton_iff, forall_eq, exists_eq_left]

@[simp] theorem coupleNE_singleton_iff {r : α → β → Prop} {a : α} {b : β} :
    coupleNE r {a} {b} ↔ r a b := by
  simp [coupleNE]

@[simp] theorem couple_empty (r : α → β → Prop) : couple r ∅ ∅ := by
  simp [couple]

/-- The two sides of a coupling are jointly inhabited or jointly empty. -/
theorem couple_nonempty_iff {r : α → β → Prop} {m : Set α} {m' : Set β}
    (h : couple r m m') : m.Nonempty ↔ m'.Nonempty :=
  ⟨fun ⟨x, hx⟩ => let ⟨y, hy, _⟩ := h.1 x hx; ⟨y, hy⟩,
   fun ⟨y, hy⟩ => let ⟨x, hx, _⟩ := h.2 y hy; ⟨x, hx⟩⟩

theorem couple_mono {r r' : α → β → Prop} (h : ∀ x y, r x y → r' x y) :
    couple r ⟹ₒ couple r' := fun _ _ hc =>
  ⟨fun x hx => let ⟨y, hy, hr⟩ := hc.1 x hx; ⟨y, hy, h x y hr⟩,
   fun y hy => let ⟨x, hx, hr⟩ := hc.2 y hy; ⟨x, hx, h x y hr⟩⟩

theorem coupleL_mono {r r' : α → β → Prop} (h : ∀ x y, r x y → r' x y) :
    coupleL r ⟹ₒ coupleL r' := fun _ _ hc x hx =>
  let ⟨y, hy, hr⟩ := hc x hx; ⟨y, hy, h x y hr⟩

theorem coupleL_of_couple {r : α → β → Prop} : couple r ⟹ₒ coupleL r :=
  fun _ _ h => h.1

theorem couple_swap (r : α → β → Prop) : (couple r).swap = couple fun y x => r x y := by
  funext m' m
  exact propext and_comm

theorem coupleL_union {r : α → β → Prop} {m₁ m₂ : Set α} {m₁' m₂' : Set β}
    (h₁ : coupleL r m₁ m₁') (h₂ : coupleL r m₂ m₂') : coupleL r (m₁ ∪ m₂) (m₁' ∪ m₂') := by
  rintro x (hx | hx)
  · obtain ⟨y, hy, hr⟩ := h₁ x hx
    exact ⟨y, Set.mem_union_left _ hy, hr⟩
  · obtain ⟨y, hy, hr⟩ := h₂ x hx
    exact ⟨y, Set.mem_union_right _ hy, hr⟩

theorem couple_union {r : α → β → Prop} {m₁ m₂ : Set α} {m₁' m₂' : Set β}
    (h₁ : couple r m₁ m₁') (h₂ : couple r m₂ m₂') : couple r (m₁ ∪ m₂) (m₁' ∪ m₂') :=
  ⟨coupleL_union h₁.1 h₂.1, coupleL_union (r := fun y x => r x y) h₁.2 h₂.2⟩

theorem couple_iUnion {ι : Sort*} {r : α → β → Prop} {f : ι → Set α} {g : ι → Set β}
    (h : ∀ i, couple r (f i) (g i)) : couple r (⋃ i, f i) (⋃ i, g i) := by
  constructor
  · intro x hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨y, hy, hr⟩ := (h i).1 x hx
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, hr⟩
  · intro y hy
    obtain ⟨i, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨x, hx, hr⟩ := (h i).2 y hy
    exact ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩, hr⟩

theorem couple_comp {r : α → β → Prop} {s : β → γ → Prop}
    {m : Set α} {m' : Set β} {m'' : Set γ} (h₁ : couple r m m') (h₂ : couple s m' m'') :
    couple (fun x z => ∃ y, r x y ∧ s y z) m m'' := by
  constructor
  · intro x hx
    obtain ⟨y, hy, hr⟩ := h₁.1 x hx
    obtain ⟨z, hz, hs⟩ := h₂.1 y hy
    exact ⟨z, hz, y, hr, hs⟩
  · intro z hz
    obtain ⟨y, hy, hs⟩ := h₂.2 z hz
    obtain ⟨x, hx, hr⟩ := h₁.2 y hy
    exact ⟨x, hx, y, hr, hs⟩

/-! ## Relation to the product atoms -/

theorem couple_of_atom {r : α → β → Prop} : atom r ⟹ₒ couple r := by
  rintro m m' ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩, hall⟩
  exact ⟨fun x hx => ⟨y₀, hy₀, hall x hx y₀ hy₀⟩, fun y hy => ⟨x₀, hx₀, hall x₀ hx₀ y hy⟩⟩

/-- A ∀∀ rectangle over jointly inhabited (or jointly empty) sides is a coupling. -/
theorem couple_of_atomW_nonempty {r : α → β → Prop} {m : Set α} {m' : Set β}
    (h : atomW r m m') (hiff : m.Nonempty ↔ m'.Nonempty) : couple r m m' := by
  constructor
  · intro x hx
    obtain ⟨y, hy⟩ := hiff.mp ⟨x, hx⟩
    exact ⟨y, hy, h x hx y hy⟩
  · intro y hy
    obtain ⟨x, hx⟩ := hiff.mpr ⟨y, hy⟩
    exact ⟨x, hx, h x hx y hy⟩

/-- Couplings are strictly weaker than rectangles beyond singletons. -/
theorem couple_strict :
    ∃ (r : Bool → Bool → Prop) (m : Set Bool) (m' : Set Bool),
      couple r m m' ∧ ¬ atom r m m' := by
  refine ⟨(· = ·), Set.univ, Set.univ,
    ⟨fun x _ => ⟨x, Set.mem_univ x, rfl⟩, fun y _ => ⟨y, Set.mem_univ y, rfl⟩⟩, ?_⟩
  rintro ⟨-, -, hall⟩
  exact absurd (hall true (Set.mem_univ _) false (Set.mem_univ _)) (by decide)

/-! ## Falsification -/

/-- Orphan-completeness: a coupling fails exactly when some outcome has no partner. -/
theorem not_couple_iff {r : α → β → Prop} {m : Set α} {m' : Set β} :
    ¬ couple r m m' ↔
      (∃ x ∈ m, ∀ y ∈ m', ¬ r x y) ∨ (∃ y ∈ m', ∀ x ∈ m, ¬ r x y) := by
  unfold couple
  rw [not_and_or]
  push Not
  rfl

/-- An under-approximate reachable coupling is exactly a jointly reachable related pair. -/
theorem coupleNE_oplus_top_iff {r : α → β → Prop} {m : Set α} {m' : Set β} :
    (coupleNE r ⊕ₒ ⊤ₒ) m m' ↔ ∃ x ∈ m, ∃ y ∈ m', r x y := by
  constructor
  · rintro ⟨m₁, m₂, m₁', m₂', rfl, rfl, ⟨⟨x, hx⟩, hc⟩, -⟩
    obtain ⟨y, hy, hr⟩ := hc.1 x hx
    exact ⟨x, Set.mem_union_left _ hx, y, Set.mem_union_left _ hy, hr⟩
  · rintro ⟨x, hx, y, hy, hr⟩
    exact oplus_top_mono (oplus_left_top (coupleNE_singleton_iff.mpr hr))
      (Set.singleton_subset_iff.mpr hx) (Set.singleton_subset_iff.mpr hy)

theorem coupleNE_true_positives {r : α → β → Prop} {m : Set α} {m' : Set β}
    (h : (coupleNE r ⊕ₒ ⊤ₒ) m m') : ∃ x ∈ m, ∃ y ∈ m', r x y :=
  coupleNE_oplus_top_iff.mp h

/-- Without reachability, `⊕ ⊤` carries no information. -/
theorem couple_oplus_top (r : α → β → Prop) (m : Set α) (m' : Set β) :
    (couple r ⊕ₒ ⊤ₒ) m m' :=
  ⟨∅, m, ∅, m', (Set.empty_union m).symm, (Set.empty_union m').symm, couple_empty r, trivial⟩

/-! ## `⊕` collapses over couplings -/

theorem couple_restrict (r : α → β → Prop) (m : Set α) (m' : Set β) :
    couple r {x ∈ m | ∃ y ∈ m', r x y} {y ∈ m' | ∃ x ∈ m, r x y} :=
  ⟨fun x ⟨hx, y, hy, h⟩ => ⟨y, ⟨hy, x, hx, h⟩, h⟩, fun y ⟨hy, x, hx, h⟩ => ⟨x, ⟨hx, y, hy, h⟩, h⟩⟩

private theorem cover_of_coupleL {r₁ r₂ : α → β → Prop} {m : Set α} {m' : Set β}
    (h : coupleL (fun x y => r₁ x y ∨ r₂ x y) m m') :
    m = {x ∈ m | ∃ y ∈ m', r₁ x y} ∪ {x ∈ m | ∃ y ∈ m', r₂ x y} := by
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  · intro hx
    obtain ⟨y, hy, h | h⟩ := h x hx
    · exact Or.inl ⟨hx, y, hy, h⟩
    · exact Or.inr ⟨hx, y, hy, h⟩
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx

theorem oplus_couple_eq (r₁ r₂ : α → β → Prop) :
    (couple r₁ ⊕ₒ couple r₂) = couple fun x y => r₁ x y ∨ r₂ x y := by
  funext m m'
  refine propext ⟨?_, fun h => ⟨_, _, _, _, cover_of_coupleL h.1,
    cover_of_coupleL (r₁ := fun y x => r₁ x y) (r₂ := fun y x => r₂ x y) h.2,
    couple_restrict r₁ m m', couple_restrict r₂ m m'⟩⟩
  rintro ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩
  exact couple_union (couple_mono (fun _ _ h => Or.inl h) _ _ h₁)
    (couple_mono (fun _ _ h => Or.inr h) _ _ h₂)

theorem oplus_coupleL_eq (r₁ r₂ : α → β → Prop) :
    (coupleL r₁ ⊕ₒ coupleL r₂) = coupleL fun x y => r₁ x y ∨ r₂ x y := by
  funext m m'
  refine propext ⟨?_, fun h => ⟨_, _, m', m', cover_of_coupleL h, (Set.union_self m').symm,
    fun x ⟨_, y, hy, hr⟩ => ⟨y, hy, hr⟩, fun x ⟨_, y, hy, hr⟩ => ⟨y, hy, hr⟩⟩⟩
  rintro ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩
  exact coupleL_union (coupleL_mono (fun _ _ h => Or.inl h) _ _ h₁)
    (coupleL_mono (fun _ _ h => Or.inr h) _ _ h₂)

/-- First-order falsification for `⊕`-lists of reachable couplings. -/
theorem oplus_coupleNE_iff {r₁ r₂ : α → β → Prop} {m : Set α} {m' : Set β} :
    (coupleNE r₁ ⊕ₒ coupleNE r₂) m m' ↔
      couple (fun x y => r₁ x y ∨ r₂ x y) m m' ∧
        (∃ x ∈ m, ∃ y ∈ m', r₁ x y) ∧ (∃ x ∈ m, ∃ y ∈ m', r₂ x y) := by
  constructor
  · intro h
    refine ⟨oplus_couple_eq r₁ r₂ ▸ oplus_mono (fun _ _ h => h.2) (fun _ _ h => h.2) _ _ h,
      coupleNE_true_positives (oplus_drop _ _ h),
      coupleNE_true_positives (oplus_drop _ _ (oplus_comm _ _ h))⟩
  · rintro ⟨h, ⟨x₁, hx₁, y₁, hy₁, h₁⟩, ⟨x₂, hx₂, y₂, hy₂, h₂⟩⟩
    exact ⟨_, _, _, _, cover_of_coupleL h.1,
      cover_of_coupleL (r₁ := fun y x => r₁ x y) (r₂ := fun y x => r₂ x y) h.2,
      ⟨⟨x₁, hx₁, y₁, hy₁, h₁⟩, couple_restrict r₁ m m'⟩,
      ⟨⟨x₂, hx₂, y₂, hy₂, h₂⟩, couple_restrict r₂ m m'⟩⟩

/-- The 2×2 instance defeating the product-model enumeration is coupling-satisfiable. -/
theorem coupling_dissolves_incompleteness :
    (couple (· = ·) ⊕ₒ couple (· ≠ ·)) (Set.univ : Set Bool) Set.univ := by
  rw [oplus_couple_eq]
  exact ⟨fun x _ => ⟨x, Set.mem_univ x, Or.inl rfl⟩, fun y _ => ⟨y, Set.mem_univ y, Or.inl rfl⟩⟩

/-- Couplings are definable from infinitary `⊕` over exact singleton pairs. -/
theorem couple_iff_oplusFam {r : α → β → Prop} {m : Set α} {m' : Set β} :
    couple r m m' ↔
      ∃ W : Set (α × β), (∀ p ∈ W, r p.1 p.2) ∧
        oplusFam (fun p : W => exactly {p.1.1} {p.1.2}) m m' := by
  rw [couple_iff_witness]
  refine exists_congr fun W => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨rfl, rfl⟩
    refine ⟨fun p => {p.1.1}, fun p => {p.1.2}, ?_, ?_, fun p => ⟨rfl, rfl⟩⟩ <;>
    · ext z
      simp [eq_comm]
  · rintro ⟨f, g, rfl, rfl, hfg⟩
    constructor <;>
    · ext z
      simp only [Set.mem_image, Set.mem_iUnion, Prod.exists, Subtype.exists]
      constructor
      · rintro ⟨a, b, hab, rfl⟩
        exact ⟨a, b, hab, by simp [(hfg ⟨(a, b), hab⟩).1, (hfg ⟨(a, b), hab⟩).2]⟩
      · rintro ⟨a, b, hab, hz⟩
        simp only [(hfg ⟨(a, b), hab⟩).1, (hfg ⟨(a, b), hab⟩).2,
          Set.mem_singleton_iff] at hz
        exact ⟨a, b, hab, hz.symm⟩

/-! ## Lifting through Kleisli extension and loops -/

theorem coupleL_bind {r : α → β → Prop} {r' : γ → δ → Prop}
    {k : α → Set γ} {k' : β → Set δ} {m : Set α} {m' : Set β}
    (hm : coupleL r m m') (h : ∀ x y, r x y → coupleL r' (k x) (k' y)) :
    coupleL r' (kleisli k m) (kleisli k' m') := by
  intro u hu
  obtain ⟨x, hx, hu⟩ := mem_kleisli.mp hu
  obtain ⟨y, hy, hr⟩ := hm x hx
  obtain ⟨v, hv, hr'⟩ := h x y hr u hu
  exact ⟨v, mem_kleisli.mpr ⟨y, hy, hv⟩, hr'⟩

/-- Per-pair couplings of the continuations lift through Kleisli extension. -/
theorem couple_bind {r : α → β → Prop} {r' : γ → δ → Prop}
    {k : α → Set γ} {k' : β → Set δ} {m : Set α} {m' : Set β}
    (hm : couple r m m') (h : ∀ x y, r x y → couple r' (k x) (k' y)) :
    couple r' (kleisli k m) (kleisli k' m') :=
  ⟨coupleL_bind hm.1 fun x y hr => (h x y hr).1,
   coupleL_bind (r := fun y x => r x y) (r' := fun v u => r' u v) hm.2 fun y x hr => (h x y hr).2⟩

/-- ∀∃ simulation through guard-synchronised loops; no termination premise. -/
theorem loopSem_coupleL {r : α → β → Prop} {b : α → Prop} {b' : β → Prop}
    {step : α → Set α} {step' : β → Set β}
    (hguard : ∀ x y, r x y → (b x ↔ b' y))
    (hbody : ∀ x y, r x y → b x → b' y → coupleL r (step x) (step' y)) :
    ∀ x y, r x y →
      coupleL (fun t t' => r t t' ∧ ¬ b t ∧ ¬ b' t') (loopSem b step x) (loopSem b' step' y) := by
  have aux : ∀ n x y, r x y → ∀ t ∈ loopIter b step n x,
      ∃ t' ∈ loopSem b' step' y, r t t' ∧ ¬ b t ∧ ¬ b' t' := by
    intro n
    induction n with
    | zero => intro x y _ t ht; simp at ht
    | succ n ih =>
      intro x y hr t ht
      by_cases hb : b x
      · have hb' : b' y := (hguard x y hr).mp hb
        rw [loopIter_succ_pos hb] at ht
        obtain ⟨u, hu, ht⟩ := mem_kleisli.mp ht
        obtain ⟨v, hv, hruv⟩ := hbody x y hr hb hb' u hu
        obtain ⟨t', ht', hprop⟩ := ih u v hruv t ht
        refine ⟨t', ?_, hprop⟩
        rw [loopSem_unfold, if_pos hb']
        exact mem_kleisli.mpr ⟨v, hv, ht'⟩
      · have hb' : ¬ b' y := fun h => hb ((hguard x y hr).mpr h)
        rw [loopIter_succ_neg hb, Set.mem_singleton_iff] at ht
        subst ht
        refine ⟨y, ?_, hr, hb, hb'⟩
        rw [loopSem_unfold, if_neg hb']
        rfl
  intro x y hr t ht
  obtain ⟨n, ht⟩ := Set.mem_iUnion.mp ht
  exact aux n x y hr t ht

/-- Coupled loops: no fuel, no `⊕ ⊤`, no termination premise. -/
theorem loopSem_couple {r : α → β → Prop} {b : α → Prop} {b' : β → Prop}
    {step : α → Set α} {step' : β → Set β}
    (hguard : ∀ x y, r x y → (b x ↔ b' y))
    (hbody : ∀ x y, r x y → b x → b' y → couple r (step x) (step' y)) :
    ∀ x y, r x y →
      couple (fun t t' => r t t' ∧ ¬ b t ∧ ¬ b' t') (loopSem b step x) (loopSem b' step' y) := by
  intro x y hr
  refine ⟨loopSem_coupleL hguard (fun x y h hb hb' => (hbody x y h hb hb').1) x y hr, ?_⟩
  intro t' ht'
  obtain ⟨t, ht, h, hb', hb⟩ := loopSem_coupleL (r := fun y x => r x y)
    (fun y x h => (hguard x y h).symm) (fun y x h hb' hb => (hbody x y h hb hb').2) y x hr t' ht'
  exact ⟨t, ht, h, hb, hb'⟩

end RelOL
