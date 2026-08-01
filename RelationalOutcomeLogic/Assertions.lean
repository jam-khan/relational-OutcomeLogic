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

-- `Relational` atom
-- basic way to state a relation between
-- two program's outcomes
--
-- note: non-emptyness is added to avoid
-- vacuous proof when either `program` diverges
-- and gives a `∅` outcome, as `∀ x ∈ ∅, ..` holds vacuously.
def atom (r : α → β → Prop) : RAssn α β :=
  fun m m' =>
    -- 1) `Joint reachability` both programs
    -- actually produce atleast `one` outcome.
      m.Nonempty ∧ m'.Nonempty
    -- 2) `Cross-product` condition: every
    -- left outcome relates to every right outcome.
    ∧ ∀ x ∈ m, ∀ y ∈ m', r x y
