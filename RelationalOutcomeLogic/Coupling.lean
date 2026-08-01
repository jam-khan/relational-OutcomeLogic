import RelationalOutcomeLogic.Assertions

/-!
# Couplings: the pairing model of relational outcome assertions

The product-model atom `atom r` demands the full rectangle `m × m' ⊆ r`, which
cannot express ∀∃ properties (refinement, GNI) and forces functional posts into
singleton preconditions. A **coupling** instead demands a *pairing*: every left
outcome has a related right partner and vice versa (bitotal), or one direction
only (`coupleL`, forward-simulation shape).

* `couple r` — bitotal coupling; on singletons it agrees with `atom r`
  (`couple_singleton_iff`), and `atom r` entails it (`couple_of_atom`), but it
  is strictly weaker on larger sets (`couple_strict`).
* `coupleL r` — left-total coupling (∀∃), the shape of `refines` and GNI.
* `coupleNE r` — jointly-reachable coupling, the refutation-grade form: its
  `⊕ ⊤` certificates yield genuine witness pairs (`coupleNE_true_positives`).
* `couple_bind` — the possibilistic pRHL bind: per-state couplings lift
  through Kleisli extension. This kills the singleton-precondition pattern.
* `loopSem_couple` — couplings of loop bodies lift to loops, with **no**
  termination side condition: divergent paths contribute no outcomes to
  either side, so bitotality survives divergence.
* `not_couple_iff` — falsification of couplings is **orphan-complete** and
  first-order, in contrast to the rectangle-cover problem for `atom`
  (`Metatheory.enumeration_incomplete`); indeed the Boolean witness that
  defeats the product-model enumeration is coupling-satisfiable
  (`coupling_dissolves_incompleteness`).
-/

namespace RelOL

variable {α β γ δ : Type*}

/-- Bitotal coupling: every left outcome has a related right partner and vice
versa. Equivalently, some witness set `W ⊆ r` projects onto both sides
(`couple_iff_witness`). -/
def couple (r : α → β → Prop) : RAssn α β := fun m m' =>
  (∀ x ∈ m, ∃ y ∈ m', r x y) ∧ (∀ y ∈ m', ∃ x ∈ m, r x y)

/-- Left-total coupling: every left outcome has a related right partner
(forward simulation / ∀∃ shape). -/
def coupleL (r : α → β → Prop) : RAssn α β := fun m m' =>
  ∀ x ∈ m, ∃ y ∈ m', r x y

/-- Jointly-reachable coupling: the refutation-grade form (`atom`'s analogue).
One nonemptiness conjunct suffices — bitotality carries it to the other side
(`couple_nonempty_iff`). -/
def coupleNE (r : α → β → Prop) : RAssn α β := fun m m' =>
  m.Nonempty ∧ couple r m m'

/-- The pRHL-style reading: a coupling is a witness set of pairs inside `r`
whose projections cover both outcome sets. The canonical witness is
`{p ∈ m ×ˢ m' | r p.1 p.2}`. -/
theorem couple_iff_witness {r : α → β → Prop} {m : Set α} {m' : Set β} :
    couple r m m' ↔
      ∃ W : Set (α × β), (∀ p ∈ W, r p.1 p.2) ∧
        Prod.fst '' W = m ∧ Prod.snd '' W = m' := by
  constructor
  · rintro ⟨hLR, hRL⟩
    refine ⟨{p | p.1 ∈ m ∧ p.2 ∈ m' ∧ r p.1 p.2}, fun p hp => hp.2.2, ?_, ?_⟩
    · ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact hp.1
      · intro hx
        obtain ⟨y, hy, hr⟩ := hLR x hx
        exact ⟨(x, y), ⟨hx, hy, hr⟩, rfl⟩
    · ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact hp.2.1
      · intro hy
        obtain ⟨x, hx, hr⟩ := hRL y hy
        exact ⟨(x, y), ⟨hx, hy, hr⟩, rfl⟩
  · rintro ⟨W, hr, rfl, rfl⟩
    constructor
    · rintro x ⟨p, hp, rfl⟩
      exact ⟨p.2, ⟨p, hp, rfl⟩, hr p hp⟩
    · rintro y ⟨p, hp, rfl⟩
      exact ⟨p.1, ⟨p, hp, rfl⟩, hr p hp⟩

/-! ## Basic kit -/

@[simp] theorem couple_singleton_iff {r : α → β → Prop} {a : α} {b : β} :
    couple r {a} {b} ↔ r a b := by
  simp only [couple, Set.mem_singleton_iff, forall_eq, exists_eq_left, and_self]

@[simp] theorem couple_empty (r : α → β → Prop) : couple r ∅ ∅ :=
  ⟨fun x hx => absurd hx (Set.notMem_empty x),
   fun y hy => absurd hy (Set.notMem_empty y)⟩

/-- Bitotality: the two sides of a coupling are jointly inhabited or jointly
empty. -/
theorem couple_nonempty_iff {r : α → β → Prop} {m : Set α} {m' : Set β}
    (h : couple r m m') : m.Nonempty ↔ m'.Nonempty :=
  ⟨fun ⟨x, hx⟩ => let ⟨y, hy, _⟩ := h.1 x hx; ⟨y, hy⟩,
   fun ⟨y, hy⟩ => let ⟨x, hx, _⟩ := h.2 y hy; ⟨x, hx⟩⟩

theorem couple_mono {r r' : α → β → Prop} (h : ∀ x y, r x y → r' x y) :
    entail (couple r) (couple r') := fun _ _ hc =>
  ⟨fun x hx => let ⟨y, hy, hr⟩ := hc.1 x hx; ⟨y, hy, h x y hr⟩,
   fun y hy => let ⟨x, hx, hr⟩ := hc.2 y hy; ⟨x, hx, h x y hr⟩⟩

theorem coupleL_mono {r r' : α → β → Prop} (h : ∀ x y, r x y → r' x y) :
    entail (coupleL r) (coupleL r') := fun _ _ hc x hx =>
  let ⟨y, hy, hr⟩ := hc x hx; ⟨y, hy, h x y hr⟩

theorem coupleL_of_couple {r : α → β → Prop} : entail (couple r) (coupleL r) :=
  fun _ _ h => h.1

/-- The swap of a coupling is the coupling of the flipped relation — like
`Sym`, couplings survive heterogeneity. -/
theorem couple_swap (r : α → β → Prop) :
    (couple r).swap = couple fun y x => r x y := by
  funext m' m
  exact propext and_comm

theorem couple_union {r : α → β → Prop} {m₁ m₂ : Set α} {m₁' m₂' : Set β}
    (h₁ : couple r m₁ m₁') (h₂ : couple r m₂ m₂') :
    couple r (m₁ ∪ m₂) (m₁' ∪ m₂') := by
  constructor
  · rintro x (hx | hx)
    · obtain ⟨y, hy, hr⟩ := h₁.1 x hx
      exact ⟨y, Set.mem_union_left _ hy, hr⟩
    · obtain ⟨y, hy, hr⟩ := h₂.1 x hx
      exact ⟨y, Set.mem_union_right _ hy, hr⟩
  · rintro y (hy | hy)
    · obtain ⟨x, hx, hr⟩ := h₁.2 y hy
      exact ⟨x, Set.mem_union_left _ hx, hr⟩
    · obtain ⟨x, hx, hr⟩ := h₂.2 y hy
      exact ⟨x, Set.mem_union_right _ hx, hr⟩

theorem couple_iUnion {ι : Sort*} {r : α → β → Prop} {f : ι → Set α}
    {g : ι → Set β} (h : ∀ i, couple r (f i) (g i)) :
    couple r (⋃ i, f i) (⋃ i, g i) := by
  constructor
  · intro x hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨y, hy, hr⟩ := (h i).1 x hx
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, hr⟩
  · intro y hy
    obtain ⟨i, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨x, hx, hr⟩ := (h i).2 y hy
    exact ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩, hr⟩

/-- Couplings compose relationally (transitivity through a middle set). -/
theorem couple_comp {r : α → β → Prop} {s : β → γ → Prop}
    {m : Set α} {m' : Set β} {m'' : Set γ}
    (h₁ : couple r m m') (h₂ : couple s m' m'') :
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

/-! ## Bridges to the product model -/

/-- A nonempty rectangle is a coupling: `atom` entails `couple`. -/
theorem couple_of_atom {r : α → β → Prop} : entail (atom r) (couple r) := by
  rintro m m' ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩, hall⟩
  exact ⟨fun x hx => ⟨y₀, hy₀, hall x hx y₀ hy₀⟩,
         fun y hy => ⟨x₀, hx₀, hall x₀ hx₀ y hy⟩⟩

/-- A ∀∀ rectangle over jointly inhabited (or jointly empty) sides is a
coupling — the bridge that turns a pointwise simulation plus equitermination
into a bitotal coupling (used by the verified compiler pass). -/
theorem couple_of_atomW_nonempty {r : α → β → Prop} {m : Set α} {m' : Set β}
    (h : atomW r m m') (hiff : m.Nonempty ↔ m'.Nonempty) : couple r m m' := by
  constructor
  · intro x hx
    obtain ⟨y, hy⟩ := hiff.mp ⟨x, hx⟩
    exact ⟨y, hy, h x hx y hy⟩
  · intro y hy
    obtain ⟨x, hx⟩ := hiff.mpr ⟨y, hy⟩
    exact ⟨x, hx, h x hx y hy⟩

/-- Strictness: couplings are weaker than rectangles beyond singletons. The
diagonal couples `univ` with `univ` over `Bool`, but is no rectangle. -/
theorem couple_strict :
    ∃ (r : Bool → Bool → Prop) (m : Set Bool) (m' : Set Bool),
      couple r m m' ∧ ¬ atom r m m' := by
  refine ⟨(· = ·), Set.univ, Set.univ,
    ⟨fun x _ => ⟨x, Set.mem_univ x, rfl⟩, fun y _ => ⟨y, Set.mem_univ y, rfl⟩⟩, ?_⟩
  rintro ⟨-, -, hall⟩
  exact absurd (hall true (Set.mem_univ _) false (Set.mem_univ _)) (by decide)

/-! ## The refutation engine -/

/-- Under-approximate coupling claims yield genuine witness pairs, no matter
which outcomes `⊤` absorbs — the coupling analogue of `rel_true_positives`. -/
theorem coupleNE_true_positives {r : α → β → Prop} {m : Set α} {m' : Set β}
    (h : (coupleNE r ⊕ₒ rtop) m m') : ∃ x ∈ m, ∃ y ∈ m', r x y := by
  obtain ⟨m₁, m₂, m₁', m₂', rfl, rfl, ⟨⟨x, hx⟩, hc⟩, -⟩ := h
  obtain ⟨y, hy, hr⟩ := hc.1 x hx
  exact ⟨x, Set.mem_union_left _ hx, y, Set.mem_union_left _ hy, hr⟩

/-- **Orphan-completeness**: a coupling fails exactly when some outcome on one
side has no `r`-partner on the other. Coupling falsification is therefore
first-order — in contrast to the product model, whose falsification is a
rectangle-cover problem (`enumeration_incomplete`). -/
theorem not_couple_iff {r : α → β → Prop} {m : Set α} {m' : Set β} :
    ¬ couple r m m' ↔
      (∃ x ∈ m, ∀ y ∈ m', ¬ r x y) ∨ (∃ y ∈ m', ∀ x ∈ m, ¬ r x y) := by
  unfold couple
  rw [not_and_or]
  push Not
  rfl

/-- The Boolean instance that defeats the product-model enumeration
(`r₁ = (·=·)`, `r₂ = (·≠·)`, both sides `univ`) is coupling-satisfiable: the
diagonal and the anti-diagonal are the two couplings. The rectangle-cover
obstruction is a product-model artifact. -/
theorem coupling_dissolves_incompleteness :
    (couple (· = ·) ⊕ₒ couple (· ≠ ·)) (Set.univ : Set Bool) Set.univ := by
  refine ⟨Set.univ, Set.univ, Set.univ, Set.univ,
    (Set.union_self _).symm, (Set.union_self _).symm, ?_, ?_⟩
  · exact ⟨fun x _ => ⟨x, Set.mem_univ x, rfl⟩, fun y _ => ⟨y, Set.mem_univ y, rfl⟩⟩
  · exact ⟨fun x _ => ⟨!x, Set.mem_univ _, by cases x <;> simp⟩,
           fun y _ => ⟨!y, Set.mem_univ _, by cases y <;> simp⟩⟩

/-! ## The lifting engine -/

/-- **Possibilistic pRHL bind**: a coupling of inputs and per-pair couplings of
continuations lift to a coupling of Kleisli extensions. This is what frees
functional postconditions from singleton preconditions. -/
theorem couple_bind {r : α → β → Prop} {r' : γ → δ → Prop}
    {k : α → Set γ} {k' : β → Set δ} {m : Set α} {m' : Set β}
    (hm : couple r m m') (h : ∀ x y, r x y → couple r' (k x) (k' y)) :
    couple r' (kleisli k m) (kleisli k' m') := by
  constructor
  · intro u hu
    obtain ⟨x, hx, hu⟩ := mem_kleisli.mp hu
    obtain ⟨y, hy, hr⟩ := hm.1 x hx
    obtain ⟨v, hv, hr'⟩ := (h x y hr).1 u hu
    exact ⟨v, mem_kleisli.mpr ⟨y, hy, hv⟩, hr'⟩
  · intro v hv
    obtain ⟨y, hy, hv⟩ := mem_kleisli.mp hv
    obtain ⟨x, hx, hr⟩ := hm.2 y hy
    obtain ⟨u, hu, hr'⟩ := (h x y hr).2 v hv
    exact ⟨u, mem_kleisli.mpr ⟨x, hx, hu⟩, hr'⟩

/-- One-directional bind for left-total couplings (forward simulation). -/
theorem coupleL_bind {r : α → β → Prop} {r' : γ → δ → Prop}
    {k : α → Set γ} {k' : β → Set δ} {m : Set α} {m' : Set β}
    (hm : coupleL r m m') (h : ∀ x y, r x y → coupleL r' (k x) (k' y)) :
    coupleL r' (kleisli k m) (kleisli k' m') := by
  intro u hu
  obtain ⟨x, hx, hu⟩ := mem_kleisli.mp hu
  obtain ⟨y, hy, hr⟩ := hm x hx
  obtain ⟨v, hv, hr'⟩ := h x y hr u hu
  exact ⟨v, mem_kleisli.mpr ⟨y, hy, hv⟩, hr'⟩

/-! ## Loops -/

/-- **Coupled loops**: guard-synchronized, per-pair-coupled bodies yield a
coupling of the loop semantics — with no fuel in the statement, no `⊕ ⊤`, and
no termination side condition. Divergent paths contribute no outcomes to
either side, so bitotality survives divergence. -/
theorem loopSem_couple {r : α → β → Prop} {b : α → Prop} {b' : β → Prop}
    {step : α → Set α} {step' : β → Set β}
    (hguard : ∀ x y, r x y → (b x ↔ b' y))
    (hbody : ∀ x y, r x y → b x → b' y → couple r (step x) (step' y)) :
    ∀ x y, r x y →
      couple (fun t t' => r t t' ∧ ¬ b t ∧ ¬ b' t')
        (loopSem b step x) (loopSem b' step' y) := by
  have auxL : ∀ n x y, r x y → ∀ t ∈ loopIter b step n x,
      ∃ t' ∈ loopSem b' step' y, r t t' ∧ ¬ b t ∧ ¬ b' t' := by
    intro n
    induction n with
    | zero =>
      intro x y _ t ht
      rw [loopIter_zero] at ht
      exact absurd ht (Set.notMem_empty t)
    | succ n ih =>
      intro x y hr t ht
      by_cases hb : b x
      · have hb' : b' y := (hguard x y hr).mp hb
        rw [loopIter_succ_pos hb] at ht
        obtain ⟨u, hu, ht⟩ := mem_kleisli.mp ht
        obtain ⟨v, hv, hruv⟩ := (hbody x y hr hb hb').1 u hu
        obtain ⟨t', ht', hprop⟩ := ih u v hruv t ht
        refine ⟨t', ?_, hprop⟩
        rw [loopSem_unfold, if_pos hb']
        exact mem_kleisli.mpr ⟨v, hv, ht'⟩
      · have hb' : ¬ b' y := fun h => hb ((hguard x y hr).mpr h)
        rw [loopIter_succ_neg hb, Set.mem_singleton_iff] at ht
        subst ht
        refine ⟨y, ?_, hr, hb, hb'⟩
        rw [loopSem_unfold, if_neg hb']
        exact Set.mem_singleton y
  have auxR : ∀ n x y, r x y → ∀ t' ∈ loopIter b' step' n y,
      ∃ t ∈ loopSem b step x, r t t' ∧ ¬ b t ∧ ¬ b' t' := by
    intro n
    induction n with
    | zero =>
      intro x y _ t' ht'
      rw [loopIter_zero] at ht'
      exact absurd ht' (Set.notMem_empty t')
    | succ n ih =>
      intro x y hr t' ht'
      by_cases hb' : b' y
      · have hb : b x := (hguard x y hr).mpr hb'
        rw [loopIter_succ_pos hb'] at ht'
        obtain ⟨v, hv, ht'⟩ := mem_kleisli.mp ht'
        obtain ⟨u, hu, hruv⟩ := (hbody x y hr hb hb').2 v hv
        obtain ⟨t, ht, hprop⟩ := ih u v hruv t' ht'
        refine ⟨t, ?_, hprop⟩
        rw [loopSem_unfold, if_pos hb]
        exact mem_kleisli.mpr ⟨u, hu, ht⟩
      · have hb : ¬ b x := fun h => hb' ((hguard x y hr).mp h)
        rw [loopIter_succ_neg hb', Set.mem_singleton_iff] at ht'
        subst ht'
        refine ⟨x, ?_, hr, hb, hb'⟩
        rw [loopSem_unfold, if_neg hb]
        exact Set.mem_singleton x
  intro x y hr
  constructor
  · intro t ht
    obtain ⟨n, ht⟩ := Set.mem_iUnion.mp ht
    exact auxL n x y hr t ht
  · intro t' ht'
    obtain ⟨n, ht'⟩ := Set.mem_iUnion.mp ht'
    exact auxR n x y hr t' ht'

end RelOL
