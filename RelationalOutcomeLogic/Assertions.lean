import RelationalOutcomeLogic.Kleisli

/-!
# Relational Outcome Assertions

RAssn α β := Set α → Set β → Prop

- Assertions over `pairs` of outcome sets.
- Polymorphic in the carrier types `α β`.
- Partial commutative monoid for each
carrier is `(∪, ∅)`, so nothing assumes
a specific language or state type.

This allows for heterogeneous instantiation,
where `α` can be `state` and `β` can `state with errors`.


## Preliminaries/Jargon (Outcome carriers, outcome sets, and PCM)

1. What is an `outcome`, and what is a `carrier`?

Evaluation of a program (single) leads to X,
here `X` is the `outcome`.

Outcome `carrier` is type of one such `X`.

So, outcome `carrier` defines the kind of
`outcomes` we care about.

Examples:
  1. A plain imperative program `c` leads to store `s = [x ↦ 44]`.
  Carrier type is `State`.
  2. Rust-like with panic exception, leads to either `ok s` or panic `err`
  Carrier type is `Except Unit State`
  3. A language with exceptions can lead to either `ok s` or `throw` carrying store `s`
  Carrier type is `Except State State`

2. How do we go from `one` outcome to an outcome `set`?

Outcome set is simply the set of possible outcomes.

For a non-deterministic program, this leads to a set of outcomes.
Otherwise, it will be a singleton set with a single outcome.

Example:
  Assignment with `choice/+` operator:
  ⟦x := 1 + x := 2⟧(s) = { s[x ↦ 1], s[x ↦ 2] }

`SPECIAL CASES`
- `singleton` = exactly one possible ending (the program itself need not be
  syntactically deterministic)
- `∅` = `divergence`, program never finished

Key insight of `outcome logic`:
  `assertions` over the whole `outcome set` at once,
  instead of `one` per program.

Insight for `relational outcome logic`
  `assertions` over the pair `(m, m')` of outcome
  sets, one per program, and the carrier for the
  left and right program may diff.

3. What operations are required on the `outcome sets`?

Outcome sets `form` a `PCM` (Partial commutative monoid) under `(∪, ∅)`.

This is the standard for splitting `X` into two parts. For example,
`separation logic` uses it for memory: `h₁ · h₂ = union of disjoint heaps`,
`disjointness` leads to `partiality`.

PCM (`Partial Commutative Monoid`)
  - `a · b = b · a`             (commutative)
  - `(a · b) · c = a · (b · c)` (associative)
  - `a · 0 = a`                 (unit)
  - `some pairs` don't combine  (partial)

`Partiality` can show up with probabilities for example.

Our PCM `(∪, ∅)` is `total` (every pair combines) and `idempotent`
(`m ∪ m = m`). Idempotence permits `overlapping` splits — a set may serve
as both parts at once — which is exactly what makes the one-sided
`Choice-L` rule sound. The probabilistic PCM (`+` on distributions) is
neither, so that rule dies there.

4. What does the `PCM` gives to `relational OL`?

  **Pairwise** outcome conjunction `⊕` is enabled.

  `Unary` OL conjunction is stated as following:
    m ⊨ P ⊕ Q   iff   ∃ m₁ m₂,  m = m₁ ∪ m₂  ∧  m₁ ⊨ P  ∧  m₂ ⊨ Q

  `Relational` OL conjunction is stated as below:
    (m, m') ⊨ P ⊕ Q
      iff ∃ m₁ m₂ m₁' m₂',
              m = m₁ ∪ m₂   ∧ m' = m₁' ∪ m₂'
            ∧ (m₁, m₁') ⊨ P ∧ (m₂, m₂') ⊨ Q

  Both sides split `in sync`: piece `i` of the left is paired with piece
  `i` of the right, so `⊕` carries the `alignment` between the two
  programs' nondeterminism (e.g. branch 1 ↔ branch 1 after `Choice`).

  PCM laws become `⊕` laws:
    commutative → `P ⊕ Q ⇒ Q ⊕ P`
    associative → `(P ⊕ Q) ⊕ R ⇒ P ⊕ (Q ⊕ R)`
    unit        → `P ⇒ P ⊕ ⊤` (trivial split `(m ∪ ∅, m' ∪ ∅)`, "dropping")
-/

namespace RelOL

variable {α β : Type*}

-- Relational outcome assertions: predicates over pairs of outcome sets.
def RAssn (α β : Type*) := Set α → Set β → Prop

/-
  `Relational` atom

  Basic way to state a relation between
  two program's outcomes

  Note: non-emptyness is added to avoid
    vacuous proof when either `program` diverges
    and gives a `∅` outcome, as `∀ x ∈ ∅, ..` holds vacuously.
-/
def atom (r : α → β → Prop) : RAssn α β :=
  fun m m' =>
    -- 1) `Joint reachability` both programs
    -- actually produce atleast `one` outcome.
      m.Nonempty ∧ m'.Nonempty
    -- 2) `Cross-product` condition: every
    -- left outcome relates to every right outcome.
    ∧ ∀ x ∈ m, ∀ y ∈ m', r x y

/-
  `Weak relational atom`

  Why do we need this even though it has no `reachability` guarantees?

  1. `atom` is used for `certificates (under-approximate)`, it must not be vacuous.
  2. Partial-correctness specs (over-approximate) must **not** be falsified by divergence,
  so here `atomW` is going to be used.

  This is analogous to `Partial correctness`.

  This is the assertion we can use when relating
  two `diverging` programs, just using `atom`
  will not allow for reasoning/relating two
  diverging program as it holds reachability.

  This is not going to be used for some `existential`
  statement, where we state some `buggy` state is reachable
  because it can be used to state `vacuous` proof, so `atom`
  shall be used instead.

  Below is mainly used for embedding/subsumption of `Benton's RHL`
  and compiler correctness (E.g., divering program compiles to divering program).
-/
def atomW (r : α → β → Prop) : RAssn α β :=
  fun m m' =>
    ∀ x ∈ m, ∀ y ∈ m', r x y

/-- Pairwise `outcome conjunction/⊕` : both sides split simultaneously (overlap-friendly)

  This allows for splitting two sets at once.

  Concrete example:
    Both programs flip a coin:

    m  = ⟦x := 1 + x := 2⟧(s)  = {s[x ↦ 1],  s[x ↦ 2]}   (Program 1)
    m' = ⟦y := 1 + y := 2⟧(s') = {s'[y ↦ 1], s'[y ↦ 2]}  (Program 2)

  Plain atom `⌈x = y⌉` FAILS on (m, m').

  - Why? It demands both cross pair agree, so (x ↦ 1, y ↦ 2) fails.

    m₁ = {s[x ↦ 1]}, m₂ = {s[x ↦ 2]}, m₁' = {s'[y ↦ 1]}, m₂' = {s'[y ↦ 2]}

  gives (m₁, m₁') ⊨ ⌈x = y⌉
  and   (m₂, m₂') ⊨ ⌈x = y⌉

  Hence, `(m, m') ⊨ ⌈x = y⌉ ⊕ ⌈x = y⌉`

  Note: PIECES NEED NOT BE DISJOINT

  - We can write set of outcomes as union
  of itself and then, do the split `m' = m' ∪ m'`.

  Later, this fact will come in handly for `Choice-L` rule
  which allows for left program to branch, and right program
  to just self-split to pair with both branches. Pretty cool!

  If we had disjointness ingrained, then this will rule will
  not be false, as between two programs where only one branches,
  we won't be able to reason.

  Difference from unary OL outcome conjunction `⊕` splits one
  set into part where `P` holds and the part where `Q` holds,
  but relational outcome conjunction needs to decide which one
  is the correct right-`piece` for each left-`piece` to correspond.

  `Synchronization` needs to be taken care of.
-/
def oplus (P Q : RAssn α β) : RAssn α β :=
  fun m m' =>
    ∃ m₁ m₂ m₁' m₂',
      m = m₁ ∪ m₂ ∧ m' = m₁' ∪ m₂' ∧ P m₁ m₁' ∧ Q m₂ m₂'

-- Trivial relational assertion (holds for anything)
def rtop : RAssn α β := fun _ _ => True

-- Relational `⊤ ⊕ ⊤`: joint divergence - no outcomes on either side.
def rempty : RAssn α β := fun m m' => m = ∅ ∧ m' = ∅

-- Entailment of relational assertion
def entail (P Q : RAssn α β) : Prop := ∀ m m', P m m' → Q m m'

/-
  Swap the two sides (used by the `Sym` rule, swaps the carriers
  ,so it stays well-typed heterogeneously).
-/
def RAssn.swap (R : RAssn α β) : RAssn β α := fun m m' => R m' m

@[inherit_doc] scoped infixr:60 " ⊕ₒ " => oplus

/-! ## Notation

Reading kit, matching the paper:
  `⌈r⌉`      product atom (joint reachability + ∀∀)
  `⌈r⌉ʷ`     weak atom (∀∀ only, divergence-tolerant)
  `⊤ₒ`       trivial assertion
  `P ⟹ₒ Q`   entailment
  `Rᵀ`       swap (exchanges the carriers)
All scoped to `RelOL`, so they never leak into importing files. -/

scoped notation "⌈" r "⌉" => atom r
scoped notation "⌈" r "⌉ʷ" => atomW r
scoped notation "⊤ₒ" => rtop
scoped infixr:25 " ⟹ₒ " => entail
scoped postfix:max "ᵀ" => RAssn.swap

-- Helper lemmas

@[simp] theorem atom_singleton_iff
  {r : α → β → Prop} {a : α} {b : β} :
    atom r {a} {b} ↔ r a b := by
  simp [atom]

theorem atom_pair_elim
  {r : α → β → Prop} {m m'} (h : atom r m m') {x y} (hx : x ∈ m) (hy : y ∈ m') :
    r x y := by
  unfold atom at h
  apply h.2.2 <;> assumption

theorem oplus_intro
  {P Q : RAssn α β} {m₁ m₂ m₁' m₂'} (h₁ : P m₁ m₁') (h₂ : Q m₂ m₂') :
    (P ⊕ₒ Q) (m₁ ∪ m₂) (m₁' ∪ m₂') := by
  unfold oplus
  exists m₁
  exists m₂
  exists m₁'
  exists m₂'

-- `P ⟹ P ⊕  ⊤` via trivial split `(m ∪ ∅, m' ∪ ∅)`.
theorem oplus_left_top
  {P : RAssn α β} {m m'} (h : P m m') :
    (P ⊕ₒ rtop) m m' := by
  unfold oplus
  exists m
  exists ∅
  exists m'
  exists ∅
  constructor <;> try simp only [Set.union_empty, true_and]
  · constructor <;> try simp
    · assumption
    · unfold rtop; grind

-- `(P ⟹ P') → (Q ⟹ Q') → (P ⊕ₒ Q ⟹ P' ⊕ₒ Q')`
theorem oplus_mono {P P' Q Q' : RAssn α β} (hP : entail P P') (hQ : entail Q Q') :
    entail (P ⊕ₒ Q) (P' ⊕ₒ Q') := by
  unfold entail
  rintro m m' ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩
  unfold oplus
  unfold entail at hQ
  exists m₁
  exists m₂
  exists m₁'
  exists m₂'
  simp only [true_and]
  constructor
  · apply hP
    assumption
  · apply hQ
    assumption

theorem oplus_comm {P Q : RAssn α β} : entail (P ⊕ₒ Q) (Q ⊕ₒ P) := by
  rintro m m' ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩
  exact ⟨m₂, m₁, m₂', m₁', Set.union_comm .., Set.union_comm .., h₂, h₁⟩

theorem oplus_assoc {P Q R : RAssn α β} : entail ((P ⊕ₒ Q) ⊕ₒ R) (P ⊕ₒ (Q ⊕ₒ R)) := by
  rintro m m' ⟨m₁₂, m₃, m₁₂', m₃', rfl, rfl, ⟨m₁, m₂, m₁', m₂', rfl, rfl, h₁, h₂⟩, h₃⟩
  exact ⟨m₁, m₂ ∪ m₃, m₁', m₂' ∪ m₃', Set.union_assoc .., Set.union_assoc .., h₁,
    oplus_intro h₂ h₃⟩

/-
  Reachability extraction: an under-approximate relational atomic claim
`atom r ⊕ ⊤` guarantees a *witness pair* of jointly reachable outcomes related
by `r`. This is the engine behind the relational Principle of Denial.

It is essentially saying:
```
  If you can prove f you can prove ⌈r⌉ ⊕ ⊤
  about a pair of programs' outcomes,
  then a real, reachable pair of outcomes
  satisfying r actually exists.
```

The refutation pipeline:
  1. prove a TRUE quadruple  ⟨pre⟩ c ~ c' ⟨⌈bad⌉ ⊕ ⊤⟩   (the certificate)
  2. rel_true_positives extracts a jointly reachable pair satisfying `bad`
  3. `bad` contradicts the spec's post, and `pre` is satisfiable
  ⟹ denial: the spec's quadruple is FALSE.

Correctness denied by exhibiting a proof, not by failing to find one.
-/
theorem rel_true_positives
  {r : α → β → Prop} {m m'} (h : (atom r ⊕ₒ rtop) m m') :
    ∃ x ∈ m, ∃ y ∈ m', r x y := by
  obtain ⟨m₁, m₂, m₁', m₂', rfl, rfl, ⟨⟨x, hx⟩, ⟨y, hy⟩, hall⟩, -⟩ := h
  exact ⟨x, Set.mem_union_left _ hx, y, Set.mem_union_left _ hy, hall x hx y hy⟩

/-- `⊕ ⊤` certificates are monotone under enlarging the outcome sets: the new
outcomes go into the `⊤` part. This is what lets a certificate proved on a
fuel-truncated loop transfer to the full loop. -/
theorem oplus_top_mono
  {S : RAssn α β} {m₀ m : Set α} {m₀' m' : Set β}
  (h : (S ⊕ₒ rtop) m₀ m₀') (hm : m₀ ⊆ m) (hm' : m₀' ⊆ m') :
    (S ⊕ₒ rtop) m m' := by
  obtain ⟨m₁, m₂, m₁', m₂', rfl, rfl, hS, -⟩ := h
  exact ⟨m₁, m, m₁', m',
    (Set.union_eq_self_of_subset_left (Set.subset_union_left.trans hm)).symm,
    (Set.union_eq_self_of_subset_left (Set.subset_union_left.trans hm')).symm,
    hS, trivial⟩

-- `Weak-atom` (`atomW`) helper lemmas

-- `atom` is essentially `atomW` plus joint reachability
theorem atom_iff_atomW
  {r : α → β → Prop} {m : Set α} {m' : Set β} :
    atom r m m' ↔ m.Nonempty ∧ m'.Nonempty ∧ atomW r m m' := by
  exact Eq.to_iff rfl

-- `atom` entails `atomW`
theorem atomW_of_atom
  {r : α → β → Prop} :
    entail (atom r) (atomW r) := by
  unfold entail
  intro m m' h1
  unfold atom at h1
  unfold atomW
  grind

@[simp] theorem atomW_singleton_iff
  {r : α → β → Prop} {a : α} {b : β} :
    atomW r {a} {b} ↔ r a b := by
  simp [atomW]

-- `atomW r ⟹ atomW r'`
theorem atomW_mono
  {r r' : α → β → Prop} (h : ∀ x y, r x y → r' x y) :
    entail (atomW r) (atomW r') := by
  unfold atomW
  unfold entail
  intro m m' h1 x hx y hy
  exact h x y (h1 x hx y hy)

@[simp] theorem atomW_empty_left
  (r : α → β → Prop) (m' : Set β) :
    atomW r ∅ m' := by
  simp [atomW]

@[simp] theorem atomW_empty_right
  (r : α → β → Prop) (m : Set α) :
    atomW r m ∅ := by
  simp [atomW]

-- Swap helper lemmas

@[simp] theorem RAssn.swap_swap
  (R : RAssn α β) :
    R.swap.swap = R := rfl

theorem RAssn.swap_oplus
  (P Q : RAssn α β) :
    (P ⊕ₒ Q).swap = (P.swap ⊕ₒ Q.swap) := by
  funext m' m
  unfold RAssn.swap oplus
  grind

end RelOL
