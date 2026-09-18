# Relational Outcome Logic

A Lean 4 mechanization of Relational Outcome Logic: quadruples `⦃R⦄ c ~ c' ⦃S⦄` over pairs of
outcome sets, for two programs that may live in different languages.

```
./scripts/check.sh    # build, no sorry, standard axioms only
```

| File | Content |
| --- | --- |
| `Algebra/Weight.lean` | Raw nonnegative weights; sequencing, support, scaling, mass bounds |
| `Algebra/WeightOrder.lean` | Increasing-limit laws and omega-continuity of weighted sequencing |
| `Algebra/WeightBoundary.lean` | Counterexamples to set-specific algebraic and arbitrary-supremum laws |
| `Prob/Assertions.lean` | Weighted assertions, additive splitting, scaling, and mass constraints |
| `Prob/Coupling.lean` | Joint weights with exact marginals; equality, addition, scaling, and sequencing |
| `Prob/CouplingAssertions.lean` | Coupling assertions and additive structural rules |
| `Prob/Support.lean` | Exact weighted couplings imply the existing Set support coupling |
| `Prob/Examples.lean` | Fair/biased coins, termination mass, splitting, and coupling composition |
| `Prob/EventMass.lean` | Finite-event mass and the necessary mass bound for exact couplings |
| `Prob/Quadruple.lean` | Language-independent judgments over weighted outcome transformers |
| `Prob/BugCert.lean` | Quantitative deficit certificates and sound refutation of coupling specifications |
| `Prob/CertificateExamples.lean` | Coin-bias certificates, additive specifications, and sampling counterexamples |
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

The concrete weighted foundation, assertions, exact-marginal couplings, and quantitative
refutation certificates are implemented alongside the Set logic. Their mass and
nontermination conventions are fixed in the [semantic contract](docs/weighted-semantics.md).
Probabilistic commands and loops, followed by pRHL subsumption, are next in the
[current roadmap](typeclass-plan.md).
