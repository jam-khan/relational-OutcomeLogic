# Relational Outcome Logic — `prototype-2`: the coupling model

Extends `prototype` (product model) with the **coupling model**: assertions
that pair outcomes across the two sides instead of relating them wholesale.
Both models coexist; couplings are primary, the product atom and its
rectangle-cover metatheory remain as the contrast layer.

## What the coupling model buys (all mechanized, sorry-free)

- `Coupling.lean` — `couple` (bitotal), `coupleL` (∀∃ / forward simulation),
  `coupleNE` (refutation-grade); `couple_bind` (possibilistic pRHL bind);
  `not_couple_iff` (falsification is **orphan-complete**, first-order — vs.
  the product model's rectangle-cover problem, whose Boolean witness is
  coupling-satisfiable: `coupling_dissolves_incompleteness`).
- `Rules.lean` — coupling rule tier: `quad_couple_lift`, If/Choice rules, and
  `quad_while_couple`: **no fuel, no `⊕ ⊤`, no termination side condition**.
- `Hetero/Lang.lean` — coupling axioms + coupled heterogeneous While
  (`loopSem_errLoopSem_couple`, ok-preserving).
- `Examples/NICouple.lean` — the model-choice contrast: product-NI rejects
  the secure `secProg` (`low := 0 + low := 1`), coupling-NI accepts it and
  still rejects the leaky `prog`; `GNI_secProg` is the first positively
  proved ∀∃ property in the library.
- `Examples/Translation.lean` — `correct_translation_general`: the
  singleton-precondition pattern dissolved by `couple_bind`.
- `Compiler/Lowering.lean` — **bitotal verified pass**: `lower_terminates`
  (equi-termination, double fuel transfer) + `lower_sim` (∀∀ simulation)
  assemble into `lower_couple`; `lower_correct_couple` states correctness
  over arbitrary preconditions (`loweredC`), superseding the singleton-pre
  `loweredW`.

Future work note: `couple` is definable from any execution model's `mem`
(see `typeclass-plan.md` on `main`) — the probabilistic instance recovers
genuine pRHL couplings.

Gate: `./scripts/check.sh` (build + sorry scan); axioms of all coupling
results: `propext`, `Classical.choice`, `Quot.sound` only.
