import RelationalOutcomeLogic.Async

/-!
# A Set client with different iteration counts

The first loop counts down by one, the second by two. Joint steps create at most
one unit of lag, which a left-only step removes. This uses the mixed bitotal rule.
-/

namespace RelOL.SetAsyncExamples

def aligned (a b : ℕ) : Prop := b ≤ a ∧ a ≤ b + 1

def mode (p : ℕ × ℕ) : AsyncMode :=
  if p.1 = 0 then .done else if p.1 = p.2 then .both else .left

def joint (p : ℕ × ℕ) : Set (ℕ × ℕ) :=
  if p.1 = p.2 then {(p.1 - 1, p.2 - 2)} else {(p.1 - 1, p.2)}

/-- A local mixed schedule; its fields mention only one-step outcomes. -/
def schedule : SetAsyncSchedule aligned (fun n => 0 < n) (fun n => 0 < n)
    (fun n => {n - 1}) (fun n => {n - 2}) where
  mode := mode
  rank := fun p => p.1 - p.2
  joint := joint
  preserve := by
    rintro ⟨a, b⟩ hp ha ⟨x, y⟩ hxy
    simp only [aligned] at hp ⊢
    by_cases heq : a = b
    · simp only [joint, heq, if_true, Set.mem_singleton_iff, Prod.mk.injEq] at hxy
      omega
    · simp only [joint, heq, if_false, Set.mem_singleton_iff, Prod.mk.injEq] at hxy
      omega
  done_guard := by
    rintro ⟨a, b⟩ hp hm
    simp only [aligned] at hp
    simp only [mode] at hm
    split_ifs at hm
    simp_all
  left_step := by
    rintro ⟨a, b⟩ hp hm
    have hab : a ≠ b := by
      intro heq
      simp [mode, heq] at hm
      split_ifs at hm
    have ha : a ≠ 0 := by
      intro hz
      simp [mode, hz] at hm
    refine ⟨by omega, ?_, ?_, ?_⟩
    · simp [joint, hab]
    · simp [joint, hab]
    · rintro ⟨x, y⟩ hxy
      simp only [joint, hab, if_false, Set.mem_singleton_iff, Prod.mk.injEq] at hxy
      simp only [aligned] at hp
      dsimp
      omega
  right_step := by
    rintro ⟨a, b⟩ _ hm
    simp only [mode] at hm
    split_ifs at hm
  both_step := by
    rintro ⟨a, b⟩ hp hm
    have ha : a ≠ 0 := by
      intro hz
      simp [mode, hz] at hm
    have hab : a = b := by
      simp only [mode, if_neg ha] at hm
      split_ifs at hm with heq
      · exact heq
    refine ⟨by omega, by omega, ?_, ?_⟩ <;> simp [joint, hab]

/-- All natural starting counts, including odd bounds, are related by the mixed rule. -/
theorem countdown_different_strides (n : ℕ) :
    couple (fun a b => a = 0 ∧ b = 0)
      (loopSem (fun a => 0 < a) (fun a => {a - 1}) n)
      (loopSem (fun b => 0 < b) (fun b => {b - 2}) n) := by
  have hc := schedule.couples (a := n) (b := n) (show aligned n n by constructor <;> omega)
  apply couple_mono (fun a b hp => ?_) _ _ hc
  exact ⟨by omega, by omega⟩

/-- The selector really uses joint, one-sided, and exit modes on reachable pairs. -/
theorem three_modes : mode (2, 2) = .both ∧ mode (1, 0) = .left ∧ mode (0, 0) = .done := by
  decide

end RelOL.SetAsyncExamples
