import RelationalOutcomeLogic.Lang
import RelationalOutcomeLogic.Quadruple
import RelationalOutcomeLogic.Hetero.Lang

/-!
# The exceptions-to-error-codes lowering pass

A source language `CmdS` with structured exceptions (`throw`), whose semantics
lands in `Set (Except State State)` — the exception **carries the state at the
throw point** — is lowered to the *ite-fragment of the already-mechanized core
language* `Cmd` (a genuine subset of core: no `choice`). This is the
effect-changing pass singled out in the project plan: source and target live
under different monads, so the pass is a heterogeneous relational judgment by
construction.

* `lower` — the correct pass: `throw` becomes `err := 1`, and sequencing guards
  the continuation with `err = 0`.
* `lowerBug` — the classic miscompilation mode: the error guard on sequencing
  is dropped, so the target keeps executing after an exception.
* `lowRel` — the compilation correspondence: an ok source outcome matches the
  identical target store; an exceptional outcome `error te` matches the
  throw-point store with the error flag set, `update te "err" 1`.

Convention: source programs do not mention the reserved variable `"err"` and
target execution starts from a store with `err = 0` (both facts hold for the
concrete example programs; a well-formedness predicate is future work).
-/

namespace RelOL

/-- Source commands: the core sequential fragment plus `throw` and `while`. -/
inductive CmdS where
  | skip
  | assign (x : String) (e : State → Int)
  | seq (c₁ c₂ : CmdS)
  | throw
  | while (b : State → Prop) (c : CmdS)

/-- Source semantics: exceptions carry the state at the throw point and
propagate through sequencing and loop iteration via `errK`. -/
noncomputable def semS : CmdS → State → Set (Except State State)
  | .skip, s => {.ok s}
  | .assign x e, s => {.ok (Function.update s x (e s))}
  | .seq c₁ c₂, s => kleisli (errK (semS c₂)) (semS c₁ s)
  | .throw, s => {.error s}
  | .while b c, s => errLoopSem b (semS c) s

@[simp] theorem semS_skip (s : State) : semS .skip s = {.ok s} := rfl

@[simp] theorem semS_assign (x : String) (e : State → Int) (s : State) :
    semS (.assign x e) s = {.ok (Function.update s x (e s))} := rfl

@[simp] theorem semS_throw (s : State) : semS .throw s = {.error s} := rfl

theorem semS_seq (c₁ c₂ : CmdS) (s : State) :
    semS (.seq c₁ c₂) s = kleisli (errK (semS c₂)) (semS c₁ s) := rfl

theorem semS_while (b : State → Prop) (c : CmdS) (s : State) :
    semS (.while b c) s = errLoopSem b (semS c) s := rfl

noncomputable def semLiftS (c : CmdS) : Set (Except State State) → Set (Except State State) :=
  kleisli (errK (semS c))

@[simp] theorem semLiftS_singleton (c : CmdS) (a : Except State State) :
    semLiftS c {a} = errK (semS c) a :=
  kleisli_singleton _ _

/-- The correct lowering: error codes plus guarded sequencing, and the loop
guard strengthened with the error check so an exception exits the loop. The
image is the deterministic ite-fragment of the core language. -/
def lower : CmdS → Cmd
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq c₁ c₂ => .seq (lower c₁) (.ite (fun s => s "err" = 0) (lower c₂) .skip)
  | .throw => .assign "err" fun _ => 1
  | .while b c => .while (fun s => b s ∧ s "err" = 0) (lower c)

/-- The buggy lowering: the error guard is **dropped**, on sequencing and on
the loop guard — the target keeps executing (and keeps looping) after an
exception (a dropped-error miscompilation). -/
def lowerBug : CmdS → Cmd
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq c₁ c₂ => .seq (lowerBug c₁) (lowerBug c₂)
  | .throw => .assign "err" fun _ => 1
  | .while b c => .while b (lowerBug c)

/-- Compilation correspondence between source outcomes and target stores. -/
def lowRel : Except State State → State → Prop
  | .ok t, t' => t' = t
  | .error te, t' => t' = Function.update te "err" 1

/-- The compilation-correctness quadruple for a source program `c` under a pass
`comp`, at initial store `s`: heterogeneous pre (source entered via `.ok`),
post = the correspondence, exhaustively (no `⊤`). -/
def lowered (comp : CmdS → Cmd) (c : CmdS) (s : State) : Prop :=
  quadSem (semLiftS c) (semLift (comp c))
    (fun m m' => m = {Except.ok s} ∧ m' = {s}) (atom lowRel)

/-- Divergence-tolerant variant of `lowered`: the weak-atom post claims the
correspondence for whatever outcomes exist, so a diverging (well-formed)
source program does not falsify the pass. This is the post the ∀-programs
theorem `lower_correct` establishes. -/
def loweredW (comp : CmdS → Cmd) (c : CmdS) (s : State) : Prop :=
  quadSem (semLiftS c) (semLift (comp c))
    (fun m m' => m = {Except.ok s} ∧ m' = {s}) (atomW lowRel)

/-! ## The verified pass -/

/-- Well-formed source programs: never write the reserved `err` variable. -/
@[simp] def Wf : CmdS → Prop
  | .skip => True
  | .assign x _ => x ≠ "err"
  | .seq c₁ c₂ => Wf c₁ ∧ Wf c₂
  | .throw => True
  | .while _ c => Wf c

/-- Simulation invariant, strengthening `lowRel` with error-flag tracking:
ok-runs keep the stores literally equal with a clear flag; exceptional
outcomes carry a clear-flag throw-point store, matched by the target with the
flag set. -/
def lowInv : Except State State → State → Prop
  | .ok t, t' => t' = t ∧ t "err" = 0
  | .error te, t' => t' = Function.update te "err" 1 ∧ te "err" = 0

theorem lowRel_of_lowInv : ∀ a t', lowInv a t' → lowRel a t'
  | .ok _, _, h => h.1
  | .error _, _, h => h.1

/-- **The simulation**: for well-formed programs from a clear-flag store,
every source outcome and every target outcome are `lowInv`-related. Pointwise
(∀∀) form, so divergence on either side is absorbed; the loop case is a fuel
induction nested inside the structural one. -/
theorem lower_sim (c : CmdS) (hwf : Wf c) : ∀ s : State, s "err" = 0 →
    ∀ a ∈ semS c s, ∀ u' ∈ sem (lower c) s, lowInv a u' := by
  induction c with
  | skip =>
    intro s hs a ha u' hu'
    simp only [semS_skip, Set.mem_singleton_iff] at ha
    simp only [lower, sem_skip, Set.mem_singleton_iff] at hu'
    subst ha hu'
    exact ⟨rfl, hs⟩
  | assign x e =>
    intro s hs a ha u' hu'
    simp only [semS_assign, Set.mem_singleton_iff] at ha
    simp only [lower, sem_assign, Set.mem_singleton_iff] at hu'
    subst ha hu'
    refine ⟨rfl, ?_⟩
    rw [Function.update_apply, if_neg (Ne.symm hwf)]
    exact hs
  | seq c₁ c₂ ih₁ ih₂ =>
    intro s hs a ha u' hu'
    rw [semS_seq] at ha
    obtain ⟨a₁, ha₁, ha⟩ := mem_kleisli.mp ha
    simp only [lower] at hu'
    rw [sem_seq] at hu'
    obtain ⟨v, hv, hu'⟩ := mem_kleisli.mp hu'
    have hinv₁ := ih₁ hwf.1 s hs a₁ ha₁ v hv
    cases a₁ with
    | ok u =>
      obtain ⟨rfl, hu⟩ := hinv₁
      rw [errK_ok] at ha
      rw [sem_ite_pos (b := fun t => t "err" = 0) (s := v) hu] at hu'
      exact ih₂ hwf.2 v hu a ha u' hu'
    | error te =>
      obtain ⟨rfl, hte⟩ := hinv₁
      rw [errK_error, Set.mem_singleton_iff] at ha
      subst ha
      rw [sem_ite_neg (b := fun t => t "err" = 0)
        (s := Function.update te "err" 1) (by simp)] at hu'
      rw [sem_skip, Set.mem_singleton_iff] at hu'
      subst hu'
      exact ⟨rfl, hte⟩
  | throw =>
    intro s hs a ha u' hu'
    simp only [semS_throw, Set.mem_singleton_iff] at ha
    simp only [lower, sem_assign, Set.mem_singleton_iff] at hu'
    subst ha hu'
    exact ⟨rfl, hs⟩
  | «while» b c ih =>
    have aux : ∀ n k (s : State), s "err" = 0 →
        ∀ a ∈ errLoopIter b (semS c) n s,
        ∀ u' ∈ loopIter (fun t => b t ∧ t "err" = 0) (sem (lower c)) k s,
          lowInv a u' := by
      intro n
      induction n with
      | zero => intro k s _ a ha; simp at ha
      | succ n ihn =>
        intro k s hs a ha u' hu'
        by_cases hb : b s
        · rw [errLoopIter_succ_pos hb] at ha
          obtain ⟨a₁, ha₁, ha⟩ := mem_kleisli.mp ha
          cases k with
          | zero => simp at hu'
          | succ k =>
            rw [loopIter_succ_pos (b := fun t => b t ∧ t "err" = 0) (s := s)
              ⟨hb, hs⟩] at hu'
            obtain ⟨v, hv, hu'⟩ := mem_kleisli.mp hu'
            have hinv₁ := ih hwf s hs a₁ ha₁ v hv
            cases a₁ with
            | ok u =>
              obtain ⟨rfl, hu⟩ := hinv₁
              rw [errK_ok] at ha
              exact ihn k v hu a ha u' hu'
            | error te =>
              obtain ⟨rfl, hte⟩ := hinv₁
              rw [errK_error, Set.mem_singleton_iff] at ha
              subst ha
              cases k with
              | zero => simp at hu'
              | succ k =>
                rw [loopIter_succ_neg (b := fun t => b t ∧ t "err" = 0)
                  (s := Function.update te "err" 1) (by simp)] at hu'
                rw [Set.mem_singleton_iff] at hu'
                subst hu'
                exact ⟨rfl, hte⟩
        · rw [errLoopIter_succ_neg hb, Set.mem_singleton_iff] at ha
          subst ha
          cases k with
          | zero => simp at hu'
          | succ k =>
            rw [loopIter_succ_neg (b := fun t => b t ∧ t "err" = 0) (s := s)
              (fun h => hb h.1)] at hu'
            rw [Set.mem_singleton_iff] at hu'
            subst hu'
            exact ⟨rfl, hs⟩
    intro s hs a ha u' hu'
    rw [semS_while] at ha
    obtain ⟨n, ha⟩ := Set.mem_iUnion.mp ha
    simp only [lower] at hu'
    rw [sem_while] at hu'
    obtain ⟨k, hu'⟩ := Set.mem_iUnion.mp hu'
    exact aux n k s hs a ha u' hu'

/-- **The verified pass**: the guarded lowering is correct for *every*
well-formed source program and every clear-flag initial store — compiler
verification, not just translation validation. -/
theorem lower_correct (c : CmdS) (hc : Wf c) (s : State) (hs : s "err" = 0) :
    loweredW lower c s := by
  rintro m m' ⟨rfl, rfl⟩
  rw [semLiftS_singleton, errK_ok, semLift_singleton]
  intro a ha u' hu'
  exact lowRel_of_lowInv a u' (lower_sim c hc s hs a ha u' hu')

/-! ## The bitotal pass (coupling model)

`lower_sim` is a ∀∀ simulation; upgrading it to a bitotal coupling needs
exactly one more ingredient: **equi-termination** — source and target
produce outcomes from the same initial stores. Since `CmdS` and the
`lower`-image are deterministic, outcome sets are `∅`-or-inhabited together,
and `couple_of_atomW_nonempty` assembles the coupling from the ∀∀ simulation
plus the termination transfer. -/

/-- **Equi-termination**: from a clear-flag store, a well-formed source
program has an outcome iff its lowering does. The while case transfers fuel
in both directions: an in-body exception makes the source exit with `error`
while the guarded target exits its loop with the flag set. -/
theorem lower_terminates (c : CmdS) (hwf : Wf c) : ∀ s : State, s "err" = 0 →
    ((semS c s).Nonempty ↔ (sem (lower c) s).Nonempty) := by
  induction c with
  | skip => exact fun s _ => ⟨fun _ => ⟨s, rfl⟩, fun _ => ⟨.ok s, rfl⟩⟩
  | assign x e =>
    exact fun s _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  | throw =>
    exact fun s _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  | seq c₁ c₂ ih₁ ih₂ =>
    intro s hs
    constructor
    · rintro ⟨a, ha⟩
      rw [semS_seq] at ha
      obtain ⟨a₁, ha₁, ha⟩ := mem_kleisli.mp ha
      obtain ⟨v, hv⟩ := (ih₁ hwf.1 s hs).mp ⟨a₁, ha₁⟩
      have hinv₁ := lower_sim c₁ hwf.1 s hs a₁ ha₁ v hv
      cases a₁ with
      | ok u =>
        obtain ⟨rfl, hu⟩ := hinv₁
        rw [errK_ok] at ha
        obtain ⟨u₂, hu₂⟩ := (ih₂ hwf.2 v hu).mp ⟨a, ha⟩
        refine ⟨u₂, ?_⟩
        simp only [lower]
        rw [sem_seq]
        refine mem_kleisli.mpr ⟨v, hv, ?_⟩
        rw [sem_ite_pos (b := fun t => t "err" = 0) (s := v) hu]
        exact hu₂
      | error te =>
        obtain ⟨rfl, hte⟩ := hinv₁
        refine ⟨Function.update te "err" 1, ?_⟩
        simp only [lower]
        rw [sem_seq]
        refine mem_kleisli.mpr ⟨_, hv, ?_⟩
        rw [sem_ite_neg (b := fun t => t "err" = 0)
          (s := Function.update te "err" 1) (by simp)]
        rw [sem_skip]
        exact rfl
    · rintro ⟨u', hu'⟩
      simp only [lower] at hu'
      rw [sem_seq] at hu'
      obtain ⟨v, hv, hu'⟩ := mem_kleisli.mp hu'
      obtain ⟨a₁, ha₁⟩ := (ih₁ hwf.1 s hs).mpr ⟨v, hv⟩
      have hinv₁ := lower_sim c₁ hwf.1 s hs a₁ ha₁ v hv
      cases a₁ with
      | ok u =>
        obtain ⟨rfl, hu⟩ := hinv₁
        rw [sem_ite_pos (b := fun t => t "err" = 0) (s := v) hu] at hu'
        obtain ⟨a₂, ha₂⟩ := (ih₂ hwf.2 v hu).mpr ⟨u', hu'⟩
        refine ⟨a₂, ?_⟩
        rw [semS_seq]
        exact mem_kleisli.mpr ⟨.ok v, ha₁, by rwa [errK_ok]⟩
      | error te =>
        refine ⟨.error te, ?_⟩
        rw [semS_seq]
        exact mem_kleisli.mpr ⟨.error te, ha₁, by rw [errK_error]; exact rfl⟩
  | «while» b c ih =>
    have auxA : ∀ n (s : State), s "err" = 0 →
        (errLoopIter b (semS c) n s).Nonempty →
        (loopSem (fun t => b t ∧ t "err" = 0) (sem (lower c)) s).Nonempty := by
      intro n
      induction n with
      | zero =>
        intro s _ h
        rw [errLoopIter_zero] at h
        exact absurd h Set.not_nonempty_empty
      | succ n ihn =>
        intro s hs h
        by_cases hb : b s
        · rw [errLoopIter_succ_pos hb] at h
          obtain ⟨a, ha⟩ := h
          obtain ⟨a₁, ha₁, ha⟩ := mem_kleisli.mp ha
          obtain ⟨v, hv⟩ := (ih hwf s hs).mp ⟨a₁, ha₁⟩
          have hinv₁ := lower_sim c hwf s hs a₁ ha₁ v hv
          cases a₁ with
          | ok u =>
            obtain ⟨rfl, hu⟩ := hinv₁
            rw [errK_ok] at ha
            obtain ⟨w, hw⟩ := ihn v hu ⟨a, ha⟩
            refine ⟨w, ?_⟩
            rw [loopSem_unfold, if_pos ⟨hb, hs⟩]
            exact mem_kleisli.mpr ⟨v, hv, hw⟩
          | error te =>
            obtain ⟨rfl, hte⟩ := hinv₁
            refine ⟨Function.update te "err" 1, ?_⟩
            rw [loopSem_unfold, if_pos ⟨hb, hs⟩]
            refine mem_kleisli.mpr ⟨_, hv, ?_⟩
            rw [loopSem_unfold, if_neg (by simp)]
            exact rfl
        · refine ⟨s, ?_⟩
          rw [loopSem_unfold, if_neg (fun hcon => hb hcon.1)]
          exact rfl
    have auxB : ∀ k (s : State), s "err" = 0 →
        (loopIter (fun t => b t ∧ t "err" = 0) (sem (lower c)) k s).Nonempty →
        (errLoopSem b (semS c) s).Nonempty := by
      intro k
      induction k with
      | zero =>
        intro s _ h
        rw [loopIter_zero] at h
        exact absurd h Set.not_nonempty_empty
      | succ k ihk =>
        intro s hs h
        by_cases hb : b s
        · rw [loopIter_succ_pos (b := fun t => b t ∧ t "err" = 0) (s := s)
            ⟨hb, hs⟩] at h
          obtain ⟨w, hw⟩ := h
          obtain ⟨v, hv, hw⟩ := mem_kleisli.mp hw
          obtain ⟨a₁, ha₁⟩ := (ih hwf s hs).mpr ⟨v, hv⟩
          have hinv₁ := lower_sim c hwf s hs a₁ ha₁ v hv
          cases a₁ with
          | ok u =>
            obtain ⟨rfl, hu⟩ := hinv₁
            obtain ⟨a, ha⟩ := ihk v hu ⟨w, hw⟩
            refine ⟨a, ?_⟩
            rw [errLoopSem_pos hb]
            exact mem_kleisli.mpr ⟨.ok v, ha₁, by rwa [errK_ok]⟩
          | error te =>
            refine ⟨.error te, ?_⟩
            rw [errLoopSem_pos hb]
            exact mem_kleisli.mpr ⟨.error te, ha₁, by rw [errK_error]; exact rfl⟩
        · refine ⟨.ok s, ?_⟩
          rw [errLoopSem_neg hb]
          exact rfl
    intro s hs
    constructor
    · rintro ⟨a, ha⟩
      rw [semS_while] at ha
      obtain ⟨n, ha⟩ := Set.mem_iUnion.mp ha
      have hres := auxA n s hs ⟨a, ha⟩
      simpa only [lower, sem_while] using hres
    · rintro ⟨u', hu'⟩
      simp only [lower] at hu'
      rw [sem_while] at hu'
      obtain ⟨k, hu'⟩ := Set.mem_iUnion.mp hu'
      have hres := auxB k s hs ⟨u', hu'⟩
      rwa [semS_while]

/-- **Bitotal correspondence per initial store**: the ∀∀ simulation
(`lower_sim`) plus equi-termination (`lower_terminates`) assemble into a
coupling — every source outcome has a matching target outcome and vice
versa, and jointly divergent runs couple trivially. -/
theorem lower_couple (c : CmdS) (hwf : Wf c) (s : State) (hs : s "err" = 0) :
    couple lowInv (semS c s) (sem (lower c) s) := by
  rcases Set.eq_empty_or_nonempty (semS c s) with hemp | hne
  · have hemp' : sem (lower c) s = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      intro hne'
      have hcon := (lower_terminates c hwf s hs).mpr hne'
      rw [hemp] at hcon
      exact Set.not_nonempty_empty hcon
    rw [hemp, hemp']
    exact couple_empty _
  · exact couple_of_atomW_nonempty
      (fun a ha u' hu' => lower_sim c hwf s hs a ha u' hu')
      ⟨fun _ => (lower_terminates c hwf s hs).mp hne, fun _ => hne⟩

/-- Coupling-strength compilation correctness, with a **general
precondition**: any coupling pairing source entries `.ok t'` with clear-flag
target stores `t'` — no singleton anywhere in the statement. -/
def loweredC (comp : CmdS → Cmd) (c : CmdS) : Prop :=
  quadSem (semLiftS c) (semLift (comp c))
    (couple fun a t' => a = .ok t' ∧ t' "err" = 0) (couple lowRel)

/-- **The bitotal verified pass**: for every well-formed source program, the
guarded lowering satisfies the coupling-strength correctness statement over
arbitrary preconditions — `couple_bind` lifts the per-store bitotal
correspondence `lower_couple`. -/
theorem lower_correct_couple (c : CmdS) (hwf : Wf c) : loweredC lower c :=
  fun _ _ hm => couple_bind hm fun a t' ⟨ha, ht'⟩ => by
    subst ha
    rw [errK_ok]
    exact couple_mono lowRel_of_lowInv _ _ (lower_couple c hwf t' ht')

end RelOL
