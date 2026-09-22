import RelationalOutcomeLogic.Generic.Judgment

/-!
# Structural rules over any additive outcome model

These proofs are shared by the set, probability, and semiring instances. The
splitting rule depends only on additive sequencing; it does not assume that a
state-level relation is closed under merging or that outcomes are idempotent.
-/

namespace RelOL.Generic

universe u v
variable {M : Type u → Type v} [OutcomeModel M]
variable {α β γ δ ε ζ : Type u}
open OutcomeModel

omit [OutcomeModel M] in
@[simp] theorem quadSem_exactly_iff (F : M α → M γ) (G : M β → M δ)
    (x : M α) (y : M β) (Q : RAssn M γ δ) :
    quadSem F G (exactly x y) Q ↔ Q (F x) (G y) := by
  constructor
  · intro h
    exact h x y ⟨rfl, rfl⟩
  · rintro h _ _ ⟨rfl, rfl⟩
    exact h

omit [OutcomeModel M] in
theorem quadSem_consequence {F : M α → M γ} {G : M β → M δ}
    {P P' : RAssn M α β} {Q Q' : RAssn M γ δ}
    (hP : entail P' P) (h : quadSem F G P Q) (hQ : entail Q Q') :
    quadSem F G P' Q' := fun x y hx => hQ _ _ (h x y (hP x y hx))

omit [OutcomeModel M] in
theorem quadSem_seq {F : M α → M γ} {G : M β → M δ}
    {H : M γ → M ε} {I : M δ → M ζ}
    {P : RAssn M α β} {Q : RAssn M γ δ} {S : RAssn M ε ζ}
    (h : quadSem F G P Q) (h' : quadSem H I Q S) :
    quadSem (H ∘ F) (I ∘ G) P S := fun x y hx => h' _ _ (h x y hx)

omit [OutcomeModel M] in
theorem quadSem_swap {F : M α → M γ} {G : M β → M δ}
    {P : RAssn M α β} {Q : RAssn M γ δ} (h : quadSem F G P Q) :
    quadSem G F P.swap Q.swap := fun y x hxy => h x y hxy

theorem quadSem_split {F : M α → M γ} {G : M β → M δ}
    (hF : ∀ x y, F (add x y) = add (F x) (F y))
    (hG : ∀ x y, G (add x y) = add (G x) (G y))
    {P P' : RAssn M α β} {Q Q' : RAssn M γ δ}
    (h : quadSem F G P Q) (h' : quadSem F G P' Q') :
    quadSem F G (oplus P P') (oplus Q Q') := by
  rintro _ _ ⟨x₁, x₂, y₁, y₂, rfl, rfl, h₁, h₂⟩
  rw [hF, hG]
  exact oplus_intro (h _ _ h₁) (h' _ _ h₂)

theorem quad_consequence {k : α → M γ} {l : β → M δ}
    {P P' : RAssn M α β} {Q Q' : RAssn M γ δ}
    (hP : entail P' P) (h : quad P k l Q) (hQ : entail Q Q') :
    quad P' k l Q' := quadSem_consequence hP h hQ

theorem quad_skip (P : RAssn M α β) : quad P pure pure P := by
  intro x y h
  simpa using h

theorem quad_seq {k : α → M γ} {l : β → M δ}
    {k' : γ → M ε} {l' : δ → M ζ}
    {P : RAssn M α β} {Q : RAssn M γ δ} {S : RAssn M ε ζ}
    (h : quad P k l Q) (h' : quad Q k' l' S) :
    quad P (fun a => bind (k a) k') (fun b => bind (l b) l') S := by
  intro x y hx
  simpa only [OutcomeModel.bind_assoc] using h' _ _ (h x y hx)

theorem quad_swap {k : α → M γ} {l : β → M δ}
    {P : RAssn M α β} {Q : RAssn M γ δ} (h : quad P k l Q) :
    quad P.swap l k Q.swap := quadSem_swap h

theorem quad_split {k : α → M γ} {l : β → M δ}
    {P P' : RAssn M α β} {Q Q' : RAssn M γ δ}
    (h : quad P k l Q) (h' : quad P' k l Q') :
    quad (oplus P P') k l (oplus Q Q') :=
  quadSem_split (fun x y => add_bind x y k) (fun x y => add_bind x y l) h h'

theorem quad_empty (k : α → M γ) (l : β → M δ) : quad emp k l emp := by
  rintro _ _ ⟨rfl, rfl⟩
  simp [emp]

theorem quad_abort (P : RAssn M α β) :
    quad P (fun _ => (empty : M γ)) (fun _ => (empty : M δ)) emp := by
  intro x y _
  simp [emp]

/-- Combining kernels adds output pieces without duplicating the input assertion. -/
theorem quad_choice {k k' : α → M γ} {l l' : β → M δ}
    {P : RAssn M α β} {Q Q' : RAssn M γ δ}
    (h : quad P k l Q) (h' : quad P k' l' Q') :
    quad P (fun a => add (k a) (k' a)) (fun b => add (l b) (l' b)) (oplus Q Q') := by
  intro x y hx
  dsimp
  rw [bind_add, bind_add]
  exact oplus_intro (h _ _ hx) (h' _ _ hx)

theorem quad_disj {k : α → M γ} {l : β → M δ}
    {P P' : RAssn M α β} {Q : RAssn M γ δ}
    (h : quad P k l Q) (h' : quad P' k l Q) :
    quad (disj P P') k l Q := by
  rintro x y (hx | hx)
  · exact h x y hx
  · exact h' x y hx

/-- A concrete violating input refutes a universal judgment in every instance. -/
theorem refute_quad {k : α → M γ} {l : β → M δ}
    {P : RAssn M α β} {Q : RAssn M γ δ} {x : M α} {y : M β}
    (hP : P x y) (hQ : ¬ Q (bind x k) (bind y l)) : ¬ quad P k l Q :=
  fun h => hQ (h x y hP)

end RelOL.Generic
