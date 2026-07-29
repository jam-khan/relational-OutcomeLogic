# Relational Outcome Logic

Redo-from-scratch of the mechanization. Reference implementation lives on the
`prototype` branch. Method: state the theorem → write the informal proof in
the draft notes → formalize → compare with `prototype` only when stuck.

## Redo checklist

- [ ] 1. Kleisli engine (`Kleisli.lean`): `kleisli` + union/empty/comp laws; `loopIter`, `loopSem`, `loopSem_unfold`, `loopSem_eq_lfp`
- [ ] 2. Languages (`Lang.lean`, `Hetero/Lang.lean`): `sem`/`semLift` + computation kit; `LoopFree`; `semLift_ite/while` lemmas; `errK`, `errK_assoc`, `errLoopSem`
- [ ] 3. Assertions (`Assertions.lean`): `atom`, `atomW`, `oplus` (+ drop, left_top, true_positives, top_mono); swap kit
- [ ] 4. Quadruples + rules (`Quadruple.lean`, `Rules.lean`): `quadSem`/`quad`; structural rules; Asgn/If; While unroll + fuel + ranked invariant; derive Choice-R yourself
- [ ] 5. Metatheory (`Metatheory.lean`): falsification, denial, n=1 enumeration, bad-pair unsoundness, rectangle-cover incompleteness
- [ ] 6. Subsumption (`Subsumption/OL.lean`, `Subsumption/RHL.lean`): `triple_iff_quadSem` + `embedU_oplus`; `rhl_iff_quad` + Benton rules incl. partial While
- [ ] 7. Hetero axioms (`Hetero/Lang.lean`): `quadH` + skip/assign/addAssign ok/panic axioms
- [ ] 8. Case studies (`Examples/`, `Compiler/`): NI + loop NI (fuel rule); GNI; translation bug + loop version; lowering, miscompilation certificates, `lower_sim`/`lower_correct`
- [ ] Gate each step: `./scripts/check.sh` + `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`)
