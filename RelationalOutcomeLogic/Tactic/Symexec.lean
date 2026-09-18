import RelationalOutcomeLogic.Rules

/-!
# `symexec`: forward execution on concrete stores

A closed `simp only` bundle (never `sem_while_unfold`, which loops): it evaluates
`semLift c {s}` to an explicit outcome set, deciding guards on the concrete store, and
reduces singleton atoms/couplings to their relation. `symexec [defs]` adds program
definitions, store lemmas, or the lemmas of another language to the bundle.
-/

namespace RelOL

open Lean.Parser.Tactic in
syntax "symexec" (" [" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic

macro_rules
  -- the splice below needs a nonempty list; `and_true` is already in the bundle
  | `(tactic| symexec $[$loc:location]?) => `(tactic| symexec [and_true] $[$loc]?)
  | `(tactic| symexec [$ts,*] $[$loc:location]?) =>
    `(tactic| simp only [$ts,*, semLift_singleton, sem_seq, sem_assign, sem_skip, sem_choice,
        Cmd.add_def, kleisli_singleton, kleisli_union, kleisli_insert, kleisli_empty,
        sem_ite_pos, sem_ite_neg, sem_while_pos, sem_while_neg, st_x, st_low,
        Function.update_self, Function.update_of_ne, ne_eq, String.reduceEq,
        Int.reduceLT, Int.reduceLE, Int.reduceGT, Int.reduceGE, Int.reduceAdd, Int.reduceSub,
        Int.reduceMul, Int.reduceEq, Int.reduceNeg, Int.reduceMod,
        gt_iff_lt, ge_iff_le, not_lt, not_le, Set.union_singleton, Set.singleton_union,
        Set.union_insert, Set.insert_union, Set.union_empty, Set.empty_union,
        Set.mem_singleton_iff, Set.mem_insert_iff, atom_singleton_iff, atomW_singleton_iff,
        couple_singleton_iff, coupleL_singleton_iff, coupleNE_singleton_iff,
        true_and, and_true, and_self, not_true_eq_false, not_false_eq_true,
        if_true, if_false, ite_true, ite_false, forall_eq, reduceCtorEq] $[$loc]?)

end RelOL
