module

public import RequestProject.Sec4_Solution.IMELL.Typing
public import RequestProject.Sec2_CoreCalculus.Renaming

/-!
# Section 4: renaming lemma for IMELL

Typing is preserved by injective renamings of de Bruijn indices (exchange and weakening by
unused variables).
-/

@[expose] public section

namespace LinExp

lemma ISplit.push {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    {Γ₁ Γ₂ Γ : ICtx n} (h : ISplit Γ₁ Γ₂ Γ) :
    ISplit (Ctx.push ρ Γ₁) (Ctx.push ρ Γ₂) (Ctx.push ρ Γ) := by
  intro j
  rcases Ctx.push_cases ρ j with ⟨i, rfl⟩ | hj
  · simp only [Ctx.push_apply hρ]; exact h i
  · simp [Ctx.push_off _ _ _ hj]

lemma ISplitN.push {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) :
    ∀ (k : ℕ) (Γs : Fin k → ICtx n) (Γ : ICtx n), ISplitN k Γs Γ →
      ISplitN k (fun j => Ctx.push ρ (Γs j)) (Ctx.push ρ Γ)
  | 0, _, Γ, h => fun j => by
    rcases Ctx.push_cases ρ j with ⟨i, rfl⟩ | hj
    · rw [Ctx.push_apply hρ]; exact h i
    · exact Ctx.push_off _ _ _ hj
  | k + 1, Γs, Γ, ⟨Γ', h1, h2⟩ => ⟨Ctx.push ρ Γ', ISplitN.push hρ k _ Γ' h1, h2.push hρ⟩

/-- **Renaming lemma** for IMELL. -/
theorem IHasType.rename {n : ℕ} {Γ : ICtx n} {M : ITerm n} {A : ITy} (h : IHasType Γ M A)
    {m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) {Γ' : ICtx m}
    (h1 : ∀ i, Γ' (ρ i) = Γ i) (h2 : ∀ j, (∀ i, ρ i ≠ j) → Γ' j = none) :
    IHasType Γ' (M.rename ρ) A := by
  induction h generalizing m with
  | @var n Γ i A hi hj =>
    refine IHasType.var (by rw [h1, hi]) (fun j hne => ?_)
    rcases Ctx.push_cases ρ j with ⟨i', rfl⟩ | hoff
    · rw [h1]; exact hj i' (fun h => hne (h ▸ rfl))
    · exact h2 j hoff
  | @lam n Γ M A B _ ih =>
    exact IHasType.lam (ih (Ctx.liftN_injective 1 ρ hρ)
      (Ctx.cons_liftN_one ρ _ Γ' Γ h1) (Ctx.cons_liftN_one_off ρ _ Γ' h2))
  | app _ _ hs ih1 ih2 =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    exact IHasType.app (ih1 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _))
      (ih2 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _)) (hs.push hρ)
  | @star n Γ hΓ =>
    refine IHasType.star (fun j => ?_)
    rcases Ctx.push_cases ρ j with ⟨i', rfl⟩ | hoff
    · rw [h1, hΓ]
    · exact h2 j hoff
  | letStar _ _ hs ih1 ih2 =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    exact IHasType.letStar (ih1 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _))
      (ih2 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _)) (hs.push hρ)
  | pair _ _ hs ih1 ih2 =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    exact IHasType.pair (ih1 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _))
      (ih2 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _)) (hs.push hρ)
  | @letPair n Γ₁ Γ₂ Γ M N A B C _ _ hs ih1 ih2 =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    refine IHasType.letPair (ih1 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _))
      (ih2 (Ctx.liftN_injective 2 ρ hρ) (fun i => ?_) (fun j hj => ?_)) (hs.push hρ)
    · rw [Ctx.liftN_append_apply]
      congr 1
      funext j; exact Ctx.push_apply hρ _ j
    · exact Ctx.liftN_off ρ _ _ (Ctx.push_off _ _) j hj
  | @promote n k Γs Γ Ms N As B hsplit _ hN ihs _ =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    exact IHasType.promote (ISplitN.push hρ k Γs Γ hsplit)
      (fun j => ihs j hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _)) hN
  | derelict _ ih => exact IHasType.derelict (ih hρ h1 h2)
  | discard _ _ hs ih1 ih2 =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    exact IHasType.discard (ih1 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _))
      (ih2 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _)) (hs.push hρ)
  | @copy n Γ₁ Γ₂ Γ M N A B _ _ hs ih1 ih2 =>
    obtain rfl := Ctx.eq_push hρ h1 h2
    refine IHasType.copy (ih1 hρ (Ctx.push_apply hρ _) (Ctx.push_off _ _))
      (ih2 (Ctx.liftN_injective 2 ρ hρ) (fun i => ?_) (fun j hj => ?_)) (hs.push hρ)
    · rw [Ctx.liftN_append_apply]
      congr 1
      funext j; exact Ctx.push_apply hρ _ j
    · exact Ctx.liftN_off ρ _ _ (Ctx.push_off _ _) j hj

/-- Derivability is preserved by injective renamings. -/
theorem IDeriv.rename {n : ℕ} {Γ : ICtx n} {A : ITy} (h : IDeriv Γ A) {m : ℕ}
    {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) {Γ' : ICtx m}
    (h1 : ∀ i, Γ' (ρ i) = Γ i) (h2 : ∀ j, (∀ i, ρ i ≠ j) → Γ' j = none) : IDeriv Γ' A :=
  let ⟨M, hM⟩ := h
  ⟨M.rename ρ, hM.rename hρ h1 h2⟩

end LinExp

end
