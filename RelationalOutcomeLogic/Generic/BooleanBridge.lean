import RelationalOutcomeLogic.Algebra.Instances.Boolean
import RelationalOutcomeLogic.Algebra.WeightedCoupling
import RelationalOutcomeLogic.Algebra.WeightedOrder
import RelationalOutcomeLogic.Generic.Iteration
import RelationalOutcomeLogic.Coupling

/-!
# Boolean-weighted outcomes recover Set semantics

The equivalence preserves outcome union, Kleisli sequencing, full loops, and exact
supported couplings. Thus the Boolean instance has the existing bitotal Set
interpretation, not just analogous operations.
-/

namespace RelOL.Generic.BooleanBridge

universe u

open Algebra

variable {α β : Type u}

def encode (m : Set α) : Weighted.Weight Reachability α := fun a => a ∈ m

def decode (μ : Weighted.Weight Reachability α) : Set α :=
  fun a => Reachability.holds (μ a)

@[simp] theorem decode_encode (m : Set α) : decode (encode m) = m := rfl
@[simp] theorem encode_decode (μ : Weighted.Weight Reachability α) : encode (decode μ) = μ := rfl

/-- Boolean weights and sets have the same information order. -/
def orderIso : Set α ≃o Weighted.Weight Reachability α where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode
  map_rel_iff' := Iff.rfl

theorem encode_iSup {ι : Sort*} (m : ι → Set α) : encode (⨆ i, m i) = ⨆ i, encode (m i) :=
  orderIso.map_iSup m

@[simp] theorem encode_empty : encode (∅ : Set α) = 0 := rfl
@[simp] theorem encode_union (m n : Set α) : encode (m ∪ n) = encode m + encode n := rfl

@[simp] theorem encode_ne_zero_iff (m : Set α) (a : α) : encode m a ≠ 0 ↔ a ∈ m := by
  change ¬ ((a ∈ m) = False) ↔ a ∈ m
  simp

theorem encode_singleton (a : α) : encode {a} = Weighted.pure a := by
  classical
  funext b
  apply propext
  change (b = a) ↔ Reachability.holds (if b = a then 1 else 0)
  by_cases h : b = a <;> simp [h]

theorem encode_kleisli (m : Set α) (k : α → Set β) :
    encode (kleisli k m) = Weighted.bind (encode m) (fun a => encode (k a)) := by
  funext b
  apply propext
  change b ∈ kleisli k m ↔ ∃ a ∈ m, b ∈ k a
  exact mem_kleisli

theorem encode_loopIter (g : α → Prop) (k : α → Set α) (n : ℕ) (s : α) :
    encode (RelOL.loopIter g k n s) =
      Generic.loopIter g (fun a => encode (k a)) n s := by
  classical
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases hs : g s
    · simp only [RelOL.loopIter, Generic.loopIter, hs, ite_true]
      rw [encode_kleisli]
      change Weighted.bind (encode (k s)) (fun a => encode (RelOL.loopIter g k n a)) =
        Weighted.bind (encode (k s)) (Generic.loopIter g (fun a => encode (k a)) n)
      exact congrArg (Weighted.bind (encode (k s))) (funext ih)
    · simp only [RelOL.loopIter, Generic.loopIter, hs, ite_false]
      change encode {s} = Weighted.pure s
      exact encode_singleton s

/-- The Boolean scalar's full loop denotes exactly the original set of terminating outcomes. -/
theorem encode_loopSem (g : α → Prop) (k : α → Set α) (s : α) :
    encode (RelOL.loopSem g k s) = Generic.loopSem g (fun a => encode (k a)) s := by
  change encode (⨆ n, RelOL.loopIter g k n s) =
    ⨆ n, Generic.loopIter g (fun a => encode (k a)) n s
  rw [encode_iSup]
  simp only [encode_loopIter]

theorem margL_encode (J : Set (α × β)) :
    Weighted.margL (encode J) = encode (Prod.fst '' J) := by
  funext a
  apply propext
  change (∃ b, (a, b) ∈ J) ↔ ∃ p, p ∈ J ∧ p.1 = a
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨(a, b), hb, rfl⟩
  · rintro ⟨⟨a', b⟩, hb, rfl⟩
    exact ⟨b, hb⟩

theorem margR_encode (J : Set (α × β)) :
    Weighted.margR (encode J) = encode (Prod.snd '' J) := by
  funext b
  apply propext
  change (∃ a, (a, b) ∈ J) ↔ ∃ p, p ∈ J ∧ p.2 = b
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(a, b), ha, rfl⟩
  · rintro ⟨⟨a, b'⟩, ha, rfl⟩
    exact ⟨a, ha⟩

/-- Exact Boolean marginals are precisely bitotal Set matching. -/
theorem coupled_iff (R : α → β → Prop) (m : Set α) (n : Set β) :
    Weighted.Coupled R (encode m) (encode n) ↔ RelOL.couple R m n := by
  rw [RelOL.couple_iff_witness]
  constructor
  · rintro ⟨J, hJ⟩
    refine ⟨decode J, ?_, ?_, ?_⟩
    · intro p hp
      apply hJ.supported
      exact (encode_ne_zero_iff (decode J) p).mpr hp
    · have h := hJ.margL_eq
      rw [← encode_decode J, margL_encode] at h
      exact congrArg decode h
    · have h := hJ.margR_eq
      rw [← encode_decode J, margR_encode] at h
      exact congrArg decode h
  · rintro ⟨J, hR, hL, hN⟩
    refine ⟨encode J, ?_, ?_, ?_⟩
    · rw [margL_encode, hL]
    · rw [margR_encode, hN]
    · intro a b hab
      exact hR (a, b) ((encode_ne_zero_iff J (a, b)).mp hab)

end RelOL.Generic.BooleanBridge
