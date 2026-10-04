module

public import RequestProject.Sec2_CoreCalculus.Typing

/-!
# Section 2: renaming (structural) lemma for GrCore

Typing is preserved by injective renamings of de Bruijn indices; the variables that are not in
the image of the renaming carry no assumption.  This gives exchange and weakening by unused
variables.
-/

@[expose] public section

namespace LinExp

namespace Ctx

variable {E : Type}

lemma push_cases {n m : ℕ} (ρ : Fin n → Fin m) (j : Fin m) :
    (∃ i, ρ i = j) ∨ (∀ i, ρ i ≠ j) := by
  by_cases h : ∃ i, ρ i = j
  · exact Or.inl h
  · push_neg at h; exact Or.inr h

lemma push_update {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (Γ : Ctx E n)
    (i : Fin n) (e : Option E) :
    push ρ (Function.update Γ i e) = Function.update (push ρ Γ) (ρ i) e := by
  funext j
  rcases push_cases ρ j with ⟨i', rfl⟩ | h
  · rw [push_apply hρ]
    by_cases hi : i' = i
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne (fun h => hi (hρ h)),
        push_apply hρ]
  · rw [push_off _ _ _ h, Function.update_of_ne (fun h' => h i h'.symm), push_off _ _ _ h]

lemma liftN_one_zero {n m : ℕ} (ρ : Fin n → Fin m) : liftN 1 ρ 0 = 0 := by
  simp [liftN]

lemma liftN_one_succ {n m : ℕ} (ρ : Fin n → Fin m) (i : Fin n) :
    liftN 1 ρ i.succ = (ρ i).succ := by
  simp [liftN, Fin.ext_iff]

lemma cons_liftN_one {n m : ℕ} (ρ : Fin n → Fin m) (e : Option E) (Γ' : Ctx E m)
    (Γ : Ctx E n) (h1 : ∀ i, Γ' (ρ i) = Γ i) (i : Fin (n + 1)) :
    cons e Γ' (liftN 1 ρ i) = cons e Γ i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [liftN_one_zero]
  · simp [liftN_one_succ, h1]

lemma cons_liftN_one_off {n m : ℕ} (ρ : Fin n → Fin m) (e : Option E) (Γ' : Ctx E m)
    (h2 : ∀ j, (∀ i, ρ i ≠ j) → Γ' j = none) (j : Fin (m + 1))
    (hj : ∀ i, liftN 1 ρ i ≠ j) : cons e Γ' j = none := by
  refine Fin.cases ?_ (fun j => ?_) j hj
  · intro hj; exact absurd (liftN_one_zero ρ) (hj 0)
  · intro hj
    simp only [cons_succ]
    exact h2 j (fun i hi => hj i.succ (by rw [liftN_one_succ, hi]))

end Ctx

variable {R : Type} [Semiring R]

lemma CtxAdd.push {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    {Γ₁ Γ₂ Γ : GCtx R n} (h : CtxAdd Γ₁ Γ₂ Γ) :
    CtxAdd (Ctx.push ρ Γ₁) (Ctx.push ρ Γ₂) (Ctx.push ρ Γ) := by
  intro j
  rcases Ctx.push_cases ρ j with ⟨i, rfl⟩ | hj
  · simp only [Ctx.push_apply hρ]; exact h i
  · simp only [Ctx.push_off _ _ _ hj]; exact EntryAdd.noneLeft none

lemma IsZeroCtx.push {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    {Δ : GCtx R n} (h : IsZeroCtx Δ) : IsZeroCtx (Ctx.push ρ Δ) := by
  intro j
  rcases Ctx.push_cases ρ j with ⟨i, rfl⟩ | hj
  · rw [Ctx.push_apply hρ]; exact h i
  · exact Or.inl (Ctx.push_off _ _ _ hj)

omit [Semiring R] in
lemma IsGraded.push {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    {Γ : GCtx R n} (h : IsGraded Γ) : IsGraded (Ctx.push ρ Γ) := by
  intro j A
  rcases Ctx.push_cases ρ j with ⟨i, rfl⟩ | hj
  · rw [Ctx.push_apply hρ]; exact h i A
  · rw [Ctx.push_off _ _ _ hj]; simp

lemma scale_push {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (r : R)
    (Γ : GCtx R n) : Ctx.push ρ (scale r Γ) = scale r (Ctx.push ρ Γ) := by
  funext j
  rcases Ctx.push_cases ρ j with ⟨i, rfl⟩ | hj
  · simp only [scale, Ctx.push_apply hρ]
  · simp only [scale, Ctx.push_off _ _ _ hj, Option.map_none]

variable [Preorder R]

/-- **Renaming lemma** for GrCore: typing is preserved by injective renamings, provided the
new context agrees with the old one along the renaming and is empty elsewhere. -/
theorem Typed.rename {hs : R → R → Option R} {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R}
    (h : Typed hs Γ t A) {m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    {Γ' : GCtx R m} (h1 : ∀ i, Γ' (ρ i) = Γ i) (h2 : ∀ j, (∀ i, ρ i ≠ j) → Γ' j = none) :
    Typed hs Γ' (t.rename ρ) A := by
  induction h generalizing m with
  | @var n Γ i A hi hj =>
    refine Typed.var (by rw [h1, hi]) (fun j hne => ?_)
    rcases Ctx.push_cases ρ j with ⟨i', rfl⟩ | hoff
    · rw [h1]; exact hj i' (fun h => hne (h ▸ rfl))
    · exact h2 j hoff
  | @lam n Γ t A B _ ih =>
    exact Typed.lam (ih (Ctx.liftN_injective 1 ρ hρ)
      (Ctx.cons_liftN_one ρ _ Γ' Γ h1) (Ctx.cons_liftN_one_off ρ _ Γ' h2))
  | @app n Γ₁ Γ₂ Γ t₁ t₂ A B _ _ hadd ih1 ih2 =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    exact Typed.app (ih1 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _))
      (ih2 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _)) (hadd.push hρ)
  | @der n Γ t A B i _ hi ih =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    rw [Ctx.push_update hρ]
    exact Typed.der (ih hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _))
      (by rw [Ctx.push_apply hρ, hi])
  | @weak n Γ Δ Γ'' t A _ hz hadd ih =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    exact Typed.weak (ih hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _)) (hz.push hρ)
      (hadd.push hρ)
  | @approx n Γ t A B i r s _ hi hrs ih =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    rw [Ctx.push_update hρ]
    exact Typed.approx (ih hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _))
      (by rw [Ctx.push_apply hρ, hi]) hrs
  | @pr n Γ t A r _ hg ih =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    rw [scale_push hρ]
    exact Typed.pr r (ih hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _)) (hg.push hρ)
  | @unit n Γ hΓ =>
    refine Typed.unit (fun j => ?_)
    rcases Ctx.push_cases ρ j with ⟨i', rfl⟩ | hoff
    · rw [h1, hΓ]
    · exact h2 j hoff
  | @pair n Γ₁ Γ₂ Γ t₁ t₂ A B _ _ hadd ih1 ih2 =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    exact Typed.pair (ih1 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _))
      (ih2 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _)) (hadd.push hρ)
  | @letPat n k Γ₁ Γ₂ Γ Δ p t₁ t₂ A B _ hp _ hadd ih1 ih2 =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    refine Typed.letPat (ih1 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _)) hp
      (ih2 (Ctx.liftN_injective k ρ hρ) (fun i => ?_) (fun j hj => ?_)) (hadd.push hρ)
    · rw [Ctx.liftN_append_apply]
      congr 1
      funext j; exact Ctx.push_apply hρ _ j
    · exact Ctx.liftN_off ρ _ Δ (Ctx.push_off _ _) j hj

/-- Weakening by one unused variable. -/
theorem Typed.shift {hs : R → R → Option R} {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R}
    (h : Typed hs Γ t A) : Typed hs (Ctx.cons none Γ) t.shift A :=
  h.rename (Fin.succ_injective n) (fun _ => rfl)
    (fun j hj => by
      refine Fin.cases (fun _ => rfl) (fun j hj => absurd rfl (hj j)) j hj)

end LinExp

end
