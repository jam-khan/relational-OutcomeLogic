import RelationalOutcomeLogic.Set.Metatheory

/-!
# Bug certificates

The object is the bug report: a concrete input pair, the reachable evidence, and why it
contradicts the specification. `refutes` is the Principle of Denial, packaged.
-/

namespace RelOL

variable {α β γ δ : Type*}

/-- A jointly reachable `bad` pair, incompatible with the postcondition `S`. -/
structure BugCert (F : Set α → Set γ) (G : Set β → Set δ) (S : RAssn γ δ) where
  s₀ : α
  s₀' : β
  bad : γ → δ → Prop
  cert : ⟪exactly {s₀} {s₀'}⟫ F , G ⟪atom bad ⊕ₒ ⊤ₒ⟫
  incompat : ∀ t t', bad t t' → ∀ n n', t ∈ n → t' ∈ n' → ¬ S n n'

theorem BugCert.refutes {F : Set α → Set γ} {G : Set β → Set δ} {S : RAssn γ δ}
    (B : BugCert F G S) {R : RAssn α β} (hR : R {B.s₀} {B.s₀'}) : ¬ ⟪R⟫ F , G ⟪S⟫ := by
  intro h
  refine denial B.cert ?_ ⟨_, _, rfl, rfl⟩ fun m m' ⟨hm, hm'⟩ => hm ▸ hm' ▸ h _ _ hR
  intro n n' hT hS
  obtain ⟨t, ht, t', ht', hb⟩ := rel_true_positives hT
  exact B.incompat t t' hb n n' ht ht' hS

/-- For ∀∃ specifications: a reachable left outcome with no partner among *all* right
outcomes (exhaustive on the right, so not an `⊕ ⊤` certificate). -/
structure OrphanCert (F : Set α → Set γ) (G : Set β → Set δ) (r : γ → δ → Prop) where
  s₀ : α
  s₀' : β
  t : γ
  reach : t ∈ F {s₀}
  orphan : ∀ t' ∈ G {s₀'}, ¬ r t t'

theorem OrphanCert.refutes {F : Set α → Set γ} {G : Set β → Set δ} {r : γ → δ → Prop}
    (B : OrphanCert F G r) {R : RAssn α β} (hR : R {B.s₀} {B.s₀'}) :
    ¬ ⟪R⟫ F , G ⟪coupleL r⟫ := by
  intro h
  obtain ⟨t', ht', hr⟩ := h _ _ hR B.t B.reach
  exact B.orphan t' ht' hr

end RelOL
