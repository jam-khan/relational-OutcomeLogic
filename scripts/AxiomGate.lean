import RelationalOutcomeLogic

-- Fails unless every declaration of the library rests on the standard axioms only.
open Lean in
run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let ours := env.constants.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some i =>
      if (`RelationalOutcomeLogic).isPrefixOf env.header.moduleNames[i.toNat]! then acc.push n
      else acc
    | none => acc
  let mut bad : Array (Name × Array Name) := #[]
  for n in ours do
    let extra := (← collectAxioms n).filter (!allowed.contains ·)
    unless extra.isEmpty do bad := bad.push (n, extra)
  unless bad.isEmpty do
    throwError "non-standard axioms:{bad.foldl (fun m (n, a) => m ++ m!"\n  {n}: {a}") m!""}"
  logInfo m!"axiom gate: {ours.size} declarations, standard axioms only"
