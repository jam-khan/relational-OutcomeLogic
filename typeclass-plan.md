# Typeclass restructuring of RelOL (post-redo abstraction phase)

## Context

The concrete mechanization instantiates everything at `Set` and passes execution-model laws as explicit hypotheses (`quadSem_split` takes union-preservation; `errK_assoc` is a bespoke lemma). Target: the TOPLAS25-style architecture — an **execution-model typeclass** whose instances are powerset nondeterminism, the error model, and (stretch) weighted/probabilistic outcomes — with assertions, quadruples, structural rules, and metatheory stated once, generically. Decisions: **concrete redo first** (README checklist unchanged), then this abstraction as a follow-on phase; **full depth**: `ExecModel` + `IterModel` (loops generic) + probabilistic instance as stretch. Subsumption results stay theorems (they relate judgments, not models) but get restated uniformly in the model.

Execute on a branch off the completed redo (or off `prototype` to abstract before finishing the redo by hand).

## Target architecture (new files under `RelationalOutcomeLogic/Algebra/`)

**`Algebra/ExecModel.lean`** — the core class (TOPLAS25 execution model = monad + outcome monoid + membership):
```lean
class ExecModel (W : Type u → Type v) where
  pure  : α → W α
  bind  : W α → (α → W β) → W β
  -- monad laws (3)
  oadd  : W α → W α → W α            -- ⋄
  ozero : W α                         -- 𝟘
  -- (⋄, 𝟘) commutative monoid laws
  bind_oadd  : bind (oadd m₁ m₂) k = oadd (bind m₁ k) (bind m₂ k)  -- OL Def 3.3(1)
  bind_ozero : bind ozero k = ozero                                 -- OL Def 3.3(2)
  mem : α → W α → Prop                -- "is a possible outcome of"
  mem_pure : mem x (pure y) ↔ x = y
  mem_oadd : mem x (oadd m₁ m₂) ↔ mem x m₁ ∨ mem x m₂
  not_mem_ozero : ¬ mem x ozero
  mem_bind : mem y (bind m k) ↔ ∃ x, mem x m ∧ mem y (k x)
```
Plus: Kleisli extension `ext k := (bind · k)` (the generic `kleisli`), derived laws (`ext_oadd`, `ext_ozero`, `ext_comp`, `ext_mono` where ordered).

**`Algebra/Idem.lean`** — `class IdemModel (W) extends ExecModel W` adding `oadd_self : oadd m m = m`. This is the *overlap-friendliness boundary*: `Choice-L`, `UnderApprox`, and `embedU_oplus`'s iff direction live here; everything else does not. (Set: instance. Weights: provably not — record as a counterexample lemma.)

**`Algebra/IterModel.lean`** — `class IterModel (W) extends ExecModel W` adding per-carrier `OmegaCompletePartialOrder (W α)` (Mathlib), `ozero` least, and ω-continuity of `bind` in both arguments. Generic `loopIter`/`loopSem` (fuel iterates, ωSup of the chain), `loopSem_unfold`, `loopSem_eq_lfp`, `loopIter_subset_loopSem`. The concrete `Kleisli.lean` loop block becomes the `Set` instantiation.

**`Algebra/Instances/`**
- `SetModel.lean` — `instance : ExecModel Set` (`pure := ({·})`, `bind := flip kleisli`, `⋄ := ∪`, `𝟘 := ∅`, `mem := ∈`); `IdemModel Set`; `IterModel Set` (CompleteLattice → ωCPO for free). All current `kleisli_*` lemmas become instance-law corollaries.
- `ErrorModel.lean` — for `[ExecModel W]`, `instance : ExecModel (fun α => W (Except ε α))` with `pure := pure ∘ .ok`, bind routing errors through untouched. **`errK` becomes this instance's bind and `errK_assoc` becomes its associativity law** — the bespoke lemma disappears into the class. `IterModel` inherits likewise (`errLoopSem` = generic `loopSem` at this instance).
- `WeightModel.lean` (stretch) — weighting functions `Weight α := α → ℝ≥0∞` (pin the semiring to `ℝ≥0∞`: `tsum` always defined, `tsum_ne_zero_iff` gives `mem_bind`): `pure := Dirac`, `bind μ k := fun y => ∑' x, μ x * k x y`, `⋄ := +` (total, no mass cap — the semiring-weighted reading, avoiding PCM partiality), `mem x μ := μ x ≠ 0`. `IterModel` via monotone convergence. NOT `IdemModel` — prove `¬ (⋄ idempotent)` as the boundary witness.

**Generic ports** (each shadows a concrete file; concrete file becomes instantiation + language-specific content only):
- `Algebra/Assertions.lean` — `RAssn W α β := W α → W β → Prop`; `atom`/`atomW` via `mem`; `oplus` via `∃ m₁ m₂, m = oadd m₁ m₂ ∧ …`; helper kit (`oplus_drop`, `rel_true_positives`, `oplus_top_mono`, swap) re-proved from the `mem_*` laws alone.
- `Algebra/Quadruple.lean` — `quadSem` unchanged in shape (bare functions; it never used laws).
- `Algebra/Rules.lean` — structural tier over `[ExecModel]` (Split's hypotheses discharged by `ext_oadd`); `Choice-L`/`UnderApprox` under `[IdemModel]`; While tiers under `[IterModel]`.
- `Algebra/Metatheory.lean` — `falsification`/`denial` carrier-free (unchanged); enumeration/orphan/rectangle-cover results generic in `mem`; the Bool incompleteness witness stays at the `Set` instance.
- `Subsumption/` — restate OL subsumption with the left side generic in `W` (right side stays the trivial `Set Unit` identity lift); RHL bridge generic in `W` for the judgment shape, `Set`-instantiated for the language.

Languages (`Lang.lean`, `Hetero/Lang.lean`, `Compiler/Lowering.lean`) keep their syntax and step functions; their lifts become `ext (sem c)` at the right instance, and `semLift_*`/`semC_*`/`semR_*` collapse to instance corollaries. Case studies should re-run with near-zero diff — that is the acceptance test of the abstraction.

## Steps (ordered)

1. `Algebra/ExecModel.lean` + `Instances/SetModel.lean`; port `Assertions` generically; make `Set` case studies compile against the generic assertions (aliasing old names).
2. `Algebra/Rules.lean` structural tier + `Idem.lean`; re-derive command rules for `Cmd` from the generic tier.
3. `Instances/ErrorModel.lean`; delete `errK` in favor of the instance bind; re-prove `Hetero/` and `Compiler/` on top (this is the step that proves the abstraction is right — the hetero side should get *shorter*).
4. `Algebra/IterModel.lean` + Set/Error iteration instances; retire the concrete loop blocks; While rules generic.
5. `Algebra/Metatheory.lean` generic port; subsumption restated in `W`.
6. Stretch: `Instances/WeightModel.lean` + the non-idempotence boundary lemma + one toy probabilistic quadruple (e.g. a fair-coin assignment satisfying an `oplus`-split post) as proof of life.
7. README: append a "Phase A: abstraction" block to the checklist (6 items mirroring steps 1–6).

## Known hazards (hit these deliberately, they're the learning content)

- **Universe discipline**: `W : Type u → Type v` — pin with `Type*` consistently; the `PUnit` universe-metavariable failure from the concrete build will recur (use `Unit`).
- **`mem_bind` for weights** needs `ℝ≥0∞`-specific `tsum` facts — this is why the semiring is pinned, not abstract.
- **Idempotence stratification**: resist putting `oadd_self` in `ExecModel`; the whole point is that `Choice-L` fails probabilistically.
- **ωCPO vs CompleteLattice**: Mathlib's `OmegaCompletePartialOrder` is the right generality (weights are not a complete lattice under the mass reading); Set gets it from its lattice.
- **Instance-resolution noise** in case studies: keep old lemma names as `abbrev`/aliases during migration so examples don't churn.

## Verification

- After each step: `./scripts/check.sh` (build + sorry gate).
- Acceptance test of the abstraction: `Examples/` and `Compiler/` compile with only import/name changes — no proof rewrites.
- `#print axioms` on `lower_correct`, `rhl_iff_quad`, and the toy probabilistic quadruple: only `propext`, `Classical.choice`, `Quot.sound`.
- Boundary witnesses compile: `errK_assoc` retired (instance law), `Weight` non-idempotence lemma present.
