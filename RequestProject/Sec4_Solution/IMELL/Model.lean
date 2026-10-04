module

public import RequestProject.Sec4_Solution.IMELL.Typing
public import RequestProject.Sec4_Solution.Model.Value

/-!
# Section 4 (proof tool): soundness of IMELL in the resource-counting model

Every derivable IMELL sequent `Γ ⊢ M : A` satisfies `⟦A⟧ ≤ Σ ⟦Γ⟧` in `Val`
(with `⟦!A⟧ = !⟦A⟧`).  This is used to show that certain formulas are not provable.
-/

@[expose] public section

namespace LinExp

namespace IModel

open Val

/-- Interpretation of IMELL formulas, given a valuation of the atoms. -/
def interp (ν : ℕ → ℤ) : ITy → Val
  | .atom i => fin (ν i)
  | .unit => 0
  | .lolli A B => res (interp ν A) (interp ν B)
  | .tensor A B => interp ν A + interp ν B
  | .bang A => bang (interp ν A)

/-- Interpretation of an optional assumption. -/
def entry (ν : ℕ → ℤ) : Option ITy → Val
  | none => 0
  | some A => interp ν A

/-- Interpretation of a context. -/
def ctxVal (ν : ℕ → ℤ) {n : ℕ} (Γ : ICtx n) : Val := ∑ i, entry ν (Γ i)

variable (ν : ℕ → ℤ)

lemma ctxVal_split {n : ℕ} {Γ₁ Γ₂ Γ : ICtx n} (h : ISplit Γ₁ Γ₂ Γ) :
    ctxVal ν Γ = ctxVal ν Γ₁ + ctxVal ν Γ₂ := by
  unfold ctxVal
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases h i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; simp [entry]
  · rw [h1, h2]; simp [entry]

lemma ctxVal_none {n : ℕ} (Γ : ICtx n) (h : ∀ i, Γ i = none) : ctxVal ν Γ = 0 := by
  unfold ctxVal
  exact Finset.sum_eq_zero (fun i _ => by rw [h i]; rfl)

lemma ctxVal_splitN {n : ℕ} : ∀ (k : ℕ) (Γs : Fin k → ICtx n) (Γ : ICtx n),
    ISplitN k Γs Γ → ctxVal ν Γ = ∑ j, ctxVal ν (Γs j)
  | 0, _, Γ, h => by simp [ctxVal_none ν Γ h]
  | k + 1, Γs, Γ, ⟨Γ', h1, h2⟩ => by
    rw [ctxVal_split ν h2, ctxVal_splitN k _ Γ' h1, Fin.sum_univ_succ]

lemma ctxVal_single {n : ℕ} (Γ : ICtx n) (i : Fin n) (hj : ∀ j, j ≠ i → Γ j = none) :
    ctxVal ν Γ = entry ν (Γ i) := by
  unfold ctxVal
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [hj j hji]; rfl) (by simp)]

lemma ctxVal_append {n k : ℕ} (Γ : ICtx n) (Δ : ICtx k) :
    ctxVal ν (Ctx.append Γ Δ) = ctxVal ν Γ + ctxVal ν Δ :=
  Ctx.sum_append (entry ν) Γ Δ

lemma ctxVal_ctx2 (A B : ITy) : ctxVal ν (ctx2 A B) = interp ν A + interp ν B := by
  simp [ctxVal, Fin.sum_univ_two, ctx2, entry, add_comm]

/-- **Soundness** of IMELL in the model. -/
theorem sound {n : ℕ} {Γ : ICtx n} {M : ITerm n} {A : ITy} (h : IHasType Γ M A) :
    interp ν A ≤ ctxVal ν Γ := by
  induction h with
  | var hi hj => rw [ctxVal_single ν _ _ hj, hi]; rfl
  | @lam n Γ M A B _ ih =>
    show res _ _ ≤ _
    rw [res_le_iff]
    have : ctxVal ν (Ctx.cons (some A) Γ) = ctxVal ν Γ + interp ν A := by
      unfold ctxVal
      rw [Fin.sum_univ_succ, add_comm]; rfl
    rwa [this] at ih
  | app _ _ hs ih1 ih2 =>
    rw [ctxVal_split ν hs]
    exact le_trans ((res_le_iff _ _ _).mp ih1) (add_le_add le_rfl ih2)
  | star hΓ => rw [ctxVal_none ν _ hΓ]; exact le_rfl
  | letStar _ _ hs ih1 ih2 =>
    rw [ctxVal_split ν hs]
    calc _ ≤ _ := ih2
      _ = 0 + _ := (zero_add _).symm
      _ ≤ _ := add_le_add ih1 le_rfl
  | pair _ _ hs ih1 ih2 =>
    rw [ctxVal_split ν hs]; exact add_le_add ih1 ih2
  | letPair _ _ hs ih1 ih2 =>
    rw [ctxVal_split ν hs]
    rw [ctxVal_append, ctxVal_ctx2] at ih2
    refine le_trans ih2 ?_
    rw [add_comm (ctxVal ν _)]
    exact add_le_add ih1 le_rfl
  | @promote n k Γs Γ Ms N As B hsplit _ _ ihs ihN =>
    show bang _ ≤ _
    rw [ctxVal_splitN ν k Γs Γ hsplit]
    have hN : ctxVal ν (fun j => some (ITy.bang (As j))) = ∑ j, bang (interp ν (As j)) := rfl
    rw [hN] at ihN
    have hidem : IsIdem (∑ j, bang (interp ν (As j))) :=
      IsIdem.sum _ _ (fun j _ => bang_isIdem _)
    exact le_trans (bang_le_of_le hidem ihN) (Finset.sum_le_sum (fun j _ => ihs j))
  | derelict _ ih => exact le_trans (le_bang _) ih
  | discard _ _ hs ih1 ih2 =>
    rw [ctxVal_split ν hs]
    calc _ ≤ _ := ih2
      _ = 0 + _ := (zero_add _).symm
      _ ≤ _ := add_le_add (le_trans (zero_le_bang _) ih1) le_rfl
  | copy _ _ hs ih1 ih2 =>
    rw [ctxVal_split ν hs]
    rw [ctxVal_append, ctxVal_ctx2] at ih2
    refine le_trans ih2 ?_
    show _ + (bang _ + bang _) ≤ _
    rw [bang_add_bang, add_comm (ctxVal ν _)]
    exact add_le_add ih1 le_rfl

end IModel

end LinExp

end
