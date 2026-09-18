# Relational Outcome Logic

A Lean 4 mechanization of Relational Outcome Logic: quadruples `⦃R⦄ c ~ c' ⦃S⦄` over pairs of
outcome sets, for two programs that may live in different languages.

```
./scripts/check.sh    # build, no sorry, standard axioms only
```

| File | Content |
| --- | --- |
| `Kleisli.lean` | Kleisli extension over the powerset monad; Kleene iteration for loops |
| `Lang.lean` | the while-language, its semantics, program notation |
| `Assertions.lean` | `atom`, `atomW`, `⊕`, infinitary `⊕`, entailment |
| `Coupling.lean` | `couple`, `coupleL`, `coupleNE`; the `⊕`-collapse; lifting through bind and loops |
| `Quadruple.lean` | `quadSem`, `quad`, assertion notation |
| `Rules.lean` | the proof rules: structural, product tier, While-Fam, coupling tier |
| `Metatheory.lean` | falsification, denial, failure modes, strongest posts, Seq (in)completeness |
| `BugCert.lean`, `Tactic/Symexec.lean` | certificate objects; the `symexec` tactic |
| `Unary/`, `Subsumption/` | unary OL and RHL as fragments |
| `Hetero/` | a C-like and a Rust-like language under one judgment; refinement |
| `Compiler/` | a verified exceptions-to-error-codes pass |
| `Examples/` | NI, GNI, coupling NI, translation bugs, miscompilation certificates |

Branches `prototype` and `prototype-2` are frozen references.
