/-
## Outcome Logic (TOPLAS25)

## 1 Introduction notes

- `Demonic` nondeterminism

Post-condition `Φ` must hold in **all**
possible outcomes -- assume the **worst-case**
branch is taken.

- `Angelic` nondeterminism

Post-condition `Φ` must hold in some **reachable**
outcome -- assume a favorable branch is taken.

In `Outcome Logic`, `demonic` means all outcomes satisfy Q
and `angelic` means all outcomes satisfy Q.

- `Manifest` errors: Bugs that occur regardless of context.

- What is a `Semiring`?

An algebraic structure `⟨U, +, ·, 0, 1⟩` where
  - `+` is associative and commutative with identity `0`
  - `·` is associative with identity `1`
  - `·` distributes over `+`
  - `0` annihilates `0 · u = 0`

In `Outcome Logic`, elements of `semiring` acts as
**weights** on program outcomes.

## 2 Overview notes

# 2.1 Unified Denotational Semantics

# 2.2 Unified Program Logic

# 2.3 Applications to Correctness and Incorrectness

## 3 Weighted Program Semantics

# 3.1 Algebraic Preliminaries

# 3.2 Weighting Functions

# 3.3 Denotational Semantics

# 3.4 Syntactic Sugar for Total Programs


# While language (Guarded Command Language GCL)

-/
