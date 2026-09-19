import RelationalOutcomeLogic.Algebra.Alignment
import RelationalOutcomeLogic.Rules

/-!
# Mixed asynchronous coupling for Set outcomes

Projection of a joint loop is proved from local image equations and a decreasing
natural rank on passive steps. The rank prevents starvation and supplies finite
catch-up when a projected loop has exited. Joint divergence remains permitted.
-/

namespace RelOL

variable {σ α β : Type*}

/-- Local conditions for erasing stuttering from a Set-valued loop. -/
structure SetLoopProjection (I : σ → Prop) (active advance : σ → Prop)
    (K : σ → Set σ) (π : σ → α) (g : α → Prop) (k : α → Set α) where
  rank : σ → ℕ
  preserve : ∀ p, I p → active p → ∀ q ∈ K p, I q
  done_guard : ∀ p, I p → ¬ active p → ¬ g (π p)
  step : ∀ p, I p → active p → advance p → g (π p) ∧ π '' K p = k (π p)
  stay : ∀ p, I p → active p → ¬ advance p →
    π '' K p = {π p} ∧ ∀ q ∈ K p, rank q < rank p

namespace SetLoopProjection

variable {I : σ → Prop} {active advance : σ → Prop} {K : σ → Set σ}
    {π : σ → α} {g : α → Prop} {k : α → Set α}

/-- A terminating joint run projects to a terminating original run. -/
theorem image_iter_subset (P : SetLoopProjection I active advance K π g k)
    (n : ℕ) (p : σ) (hp : I p) :
    π '' loopIter active K n p ⊆ loopSem g k (π p) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rintro t ⟨q, hq, rfl⟩
    by_cases ha : active p
    · rw [loopIter_succ_pos ha] at hq
      obtain ⟨u, hu, hq⟩ := mem_kleisli.mp hq
      have ht := ih u (P.preserve p hp ha u hu) ⟨q, hq, rfl⟩
      by_cases hadv : advance p
      · obtain ⟨hg, hmap⟩ := P.step p hp ha hadv
        rw [loopSem_unfold, if_pos hg]
        exact mem_kleisli.mpr ⟨π u, hmap ▸ Set.mem_image_of_mem π hu, ht⟩
      · have heq : π u = π p := by
          have hm := Set.mem_image_of_mem π hu
          rw [(P.stay p hp ha hadv).1, Set.mem_singleton_iff] at hm
          exact hm
        simpa only [heq] using ht
    · rw [loopIter_succ_neg ha, Set.mem_singleton_iff] at hq
      subst q
      rw [loopSem_unfold, if_neg (P.done_guard p hp ha)]
      rfl

/-- Every finite original run is covered by the full joint loop, including final catch-up. -/
theorem iter_subset_image (P : SetLoopProjection I active advance K π g k)
    (n : ℕ) (p : σ) (hp : I p) :
    loopIter g k n (π p) ⊆ π '' loopSem active K p := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    have aux : ∀ r p, P.rank p = r → I p →
        loopIter g k (n + 1) (π p) ⊆ π '' loopSem active K p := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ihr =>
        intro p hr hp t ht
        by_cases ha : active p
        · by_cases hadv : advance p
          · obtain ⟨hg, hmap⟩ := P.step p hp ha hadv
            rw [loopIter_succ_pos hg] at ht
            obtain ⟨a, ha', ht⟩ := mem_kleisli.mp ht
            rw [← hmap] at ha'
            obtain ⟨u, hu, rfl⟩ := ha'
            obtain ⟨q, hq, heq⟩ := ih u (P.preserve p hp ha u hu) ht
            refine ⟨q, ?_, heq⟩
            rw [loopSem_unfold, if_pos ha]
            exact mem_kleisli.mpr ⟨u, hu, hq⟩
          · obtain ⟨hmap, hdec⟩ := P.stay p hp ha hadv
            have hmem : π p ∈ π '' K p := hmap.symm ▸ Set.mem_singleton (π p)
            obtain ⟨u, hu, heq⟩ := hmem
            have hlt : P.rank u < r := hr ▸ hdec u hu
            obtain ⟨q, hq, hqt⟩ := ihr (P.rank u) hlt u rfl
              (P.preserve p hp ha u hu) (by simpa only [heq] using ht)
            refine ⟨q, ?_, hqt⟩
            rw [loopSem_unfold, if_pos ha]
            exact mem_kleisli.mpr ⟨u, hu, hq⟩
        · rw [loopIter_succ_neg (P.done_guard p hp ha), Set.mem_singleton_iff] at ht
          refine ⟨p, ?_, ht.symm⟩
          rw [loopSem_unfold, if_neg ha]
          rfl
    exact aux (P.rank p) p rfl hp

/-- Stuttering preserves the complete terminating outcome set, with both inclusions proved. -/
theorem image_loopSem (P : SetLoopProjection I active advance K π g k)
    (p : σ) (hp : I p) : π '' loopSem active K p = loopSem g k (π p) := by
  apply Set.Subset.antisymm
  · rintro t ⟨q, hq, rfl⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hq
    exact P.image_iter_subset n p hp ⟨q, hn, rfl⟩
  · intro t ht
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ht
    exact P.iter_subset_image n p hp hn

end SetLoopProjection

/-- A mixed Set scheduler supplies local joint witnesses, not final loop projections. -/
structure SetAsyncSchedule (R : α → β → Prop) (g : α → Prop) (h : β → Prop)
    (k : α → Set α) (l : β → Set β) where
  mode : α × β → AsyncMode
  rank : α × β → ℕ
  joint : α × β → Set (α × β)
  preserve : ∀ p, R p.1 p.2 → mode p ≠ .done → ∀ q ∈ joint p, R q.1 q.2
  done_guard : ∀ p, R p.1 p.2 → mode p = .done → ¬ g p.1 ∧ ¬ h p.2
  left_step : ∀ p, R p.1 p.2 → mode p = .left →
    g p.1 ∧ Prod.fst '' joint p = k p.1 ∧ Prod.snd '' joint p = {p.2} ∧
      ∀ q ∈ joint p, rank q < rank p
  right_step : ∀ p, R p.1 p.2 → mode p = .right →
    h p.2 ∧ Prod.fst '' joint p = {p.1} ∧ Prod.snd '' joint p = l p.2 ∧
      ∀ q ∈ joint p, rank q < rank p
  both_step : ∀ p, R p.1 p.2 → mode p = .both →
    g p.1 ∧ h p.2 ∧ Prod.fst '' joint p = k p.1 ∧ Prod.snd '' joint p = l p.2

namespace SetAsyncSchedule

variable {R : α → β → Prop} {g : α → Prop} {h : β → Prop}
    {k : α → Set α} {l : β → Set β}

def leftProjection (S : SetAsyncSchedule R g h k l) :
    SetLoopProjection (fun p => R p.1 p.2) (fun p => S.mode p ≠ .done)
      (fun p => S.mode p = .left ∨ S.mode p = .both) S.joint Prod.fst g k where
  rank := S.rank
  preserve := S.preserve
  done_guard := fun p hp hd => (S.done_guard p hp (not_not.mp hd)).1
  step := by
    rintro p hp _ (hm | hm)
    · exact ⟨(S.left_step p hp hm).1, (S.left_step p hp hm).2.1⟩
    · exact ⟨(S.both_step p hp hm).1, (S.both_step p hp hm).2.2.1⟩
  stay := by
    intro p hp ha hn
    have hm : S.mode p = .right := by
      cases heq : S.mode p <;> simp_all
    exact ⟨(S.right_step p hp hm).2.1, (S.right_step p hp hm).2.2.2⟩

def rightProjection (S : SetAsyncSchedule R g h k l) :
    SetLoopProjection (fun p => R p.1 p.2) (fun p => S.mode p ≠ .done)
      (fun p => S.mode p = .right ∨ S.mode p = .both) S.joint Prod.snd h l where
  rank := S.rank
  preserve := S.preserve
  done_guard := fun p hp hd => (S.done_guard p hp (not_not.mp hd)).2
  step := by
    rintro p hp _ (hm | hm)
    · exact ⟨(S.right_step p hp hm).1, (S.right_step p hp hm).2.2.1⟩
    · exact ⟨(S.both_step p hp hm).2.1, (S.both_step p hp hm).2.2.2⟩
  stay := by
    intro p hp ha hn
    have hm : S.mode p = .left := by
      cases heq : S.mode p <;> simp_all
    exact ⟨(S.left_step p hp hm).2.2.1, (S.left_step p hp hm).2.2.2⟩

private theorem exit_invariant (S : SetAsyncSchedule R g h k l)
    (n : ℕ) (p : α × β) (hp : R p.1 p.2) (q : α × β)
    (hq : q ∈ loopIter (fun p => S.mode p ≠ .done) S.joint n p) :
    R q.1 q.2 ∧ S.mode q = .done := by
  induction n generalizing p with
  | zero => simp at hq
  | succ n ih =>
    by_cases ha : S.mode p ≠ .done
    · rw [loopIter_succ_pos (b := fun p => S.mode p ≠ .done) ha] at hq
      obtain ⟨u, hu, hq⟩ := mem_kleisli.mp hq
      exact ih u (S.preserve p hp ha u hu) hq
    · rw [loopIter_succ_neg (b := fun p => S.mode p ≠ .done) ha,
        Set.mem_singleton_iff] at hq
      subst q
      exact ⟨hp, not_not.mp ha⟩

/-- The mixed product loop is a witness for bitotal coupling of the separate loops. -/
theorem couples (S : SetAsyncSchedule R g h k l) {a : α} {b : β} (hab : R a b) :
    couple (fun x y => R x y ∧ ¬ g x ∧ ¬ h y) (loopSem g k a) (loopSem h l b) := by
  apply couple_iff_witness.mpr
  refine ⟨loopSem (fun p => S.mode p ≠ .done) S.joint (a, b), ?_,
    S.leftProjection.image_loopSem (a, b) hab,
    S.rightProjection.image_loopSem (a, b) hab⟩
  intro q hq
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hq
  obtain ⟨hR, hd⟩ := S.exit_invariant n (a, b) hab q hn
  exact ⟨hR, S.done_guard q hR hd⟩

end SetAsyncSchedule

/-- Mixed bitotal coupling rule for the Set command language. -/
theorem quad_while_async_couple {R : State → State → Prop}
    {g h : State → Prop} {c d : Cmd}
    (S : SetAsyncSchedule R g h (sem c) (sem d)) :
    quad (couple R) (.while g c) (.while h d)
      (couple (fun a b => R a b ∧ ¬ g a ∧ ¬ h b)) :=
  quad_couple_lift_iff.mpr fun _ _ hab => S.couples hab

end RelOL
