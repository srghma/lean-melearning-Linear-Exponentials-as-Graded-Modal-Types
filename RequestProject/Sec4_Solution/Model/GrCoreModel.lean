module

public import RequestProject.Sec4_Solution.NoneOneTons
public import RequestProject.Sec4_Solution.Model.Value

/-!
# Section 4 (proof tool): soundness of the adjusted GrCore over `{0, 1, ω}` in the model

Types are interpreted in `Val` with `⟦□_0 A⟧ = 0`, `⟦□_1 A⟧ = ⟦A⟧` and `⟦□_ω A⟧ = !⟦A⟧`.
Every derivable judgement `Γ ⊢ t : A` of the *adjusted* calculus (with `hsup` given by
equation (1)) is valid: `⟦A⟧ ≤ Σ ⟦Γ⟧`.
-/

@[expose] public section

namespace LinExp

namespace GrModel

open Val

/-- Action of a grade on a value. -/
def gact : LNL → Val → Val
  | .zero, _ => 0
  | .one, x => x
  | .many, x => bang x

/-- Interpretation of types, given a valuation `ν` of the atoms. -/
def interp (ν : ℕ → ℤ) : Ty LNL → Val
  | .atom i => fin (ν i)
  | .unit => 0
  | .lolli A B => res (interp ν A) (interp ν B)
  | .tensor A B => interp ν A + interp ν B
  | .box r A => gact r (interp ν A)

/-- Interpretation of an assumption. -/
def entry (ν : ℕ → ℤ) : Option (Assm LNL) → Val
  | none => 0
  | some (.lin A) => interp ν A
  | some (.grad A r) => gact r (interp ν A)

/-- Interpretation of a context: the sum of its assumptions. -/
def ctxVal (ν : ℕ → ℤ) {n : ℕ} (Γ : GCtx LNL n) : Val := ∑ i, entry ν (Γ i)

/-- Interpretation of an optional grade `?r` acting on a value. -/
def optAct : Option LNL → Val → Val
  | none, x => x
  | some r, x => gact r x

variable (ν : ℕ → ℤ)

lemma gact_add_le (r s : LNL) (x : Val) : gact r x + gact s x ≤ gact (r + s) x := by
  cases r <;> cases s <;>
    simp [gact, LNL.add_def, LNL.add, add_le_bang, bang_add_le, bang_add_bang]
  rw [add_comm]; exact bang_add_le x

lemma gact_mono {r s : LNL} (h : r ≤ s) (x : Val) : gact r x ≤ gact s x := by
  rcases h with rfl | rfl
  · exact le_rfl
  · cases r <;> simp [gact, zero_le_bang, le_bang]

lemma entryAdd_le {e₁ e₂ e : Option (Assm LNL)} (h : EntryAdd e₁ e₂ e) :
    entry ν e₁ + entry ν e₂ ≤ entry ν e := by
  cases h with
  | noneLeft e => simp [entry]
  | noneRight a => simp [entry]
  | grad A r s => exact gact_add_le r s _

lemma ctxAdd_le {n : ℕ} {Γ₁ Γ₂ Γ : GCtx LNL n} (h : CtxAdd Γ₁ Γ₂ Γ) :
    ctxVal ν Γ₁ + ctxVal ν Γ₂ ≤ ctxVal ν Γ := by
  unfold ctxVal
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => entryAdd_le ν (h i))

lemma ctxVal_append {n k : ℕ} (Γ : GCtx LNL n) (Δ : GCtx LNL k) :
    ctxVal ν (Ctx.append Γ Δ) = ctxVal ν Γ + ctxVal ν Δ :=
  Ctx.sum_append (entry ν) Γ Δ

lemma ctxVal_update_le {n : ℕ} (Γ : GCtx LNL n) (i : Fin n) (e : Option (Assm LNL))
    (h : entry ν (Γ i) ≤ entry ν e) : ctxVal ν Γ ≤ ctxVal ν (Function.update Γ i e) := by
  unfold ctxVal
  refine Finset.sum_le_sum (fun j _ => ?_)
  by_cases hj : j = i
  · subst hj; simpa using h
  · rw [Function.update_of_ne hj]

lemma ctxVal_single {n : ℕ} (Γ : GCtx LNL n) (i : Fin n) (hj : ∀ j, j ≠ i → Γ j = none) :
    ctxVal ν Γ = entry ν (Γ i) := by
  unfold ctxVal
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [hj j hji]; rfl) (by simp)]

lemma ctxVal_none {n : ℕ} (Γ : GCtx LNL n) (h : ∀ i, Γ i = none) : ctxVal ν Γ = 0 := by
  unfold ctxVal
  exact Finset.sum_eq_zero (fun i _ => by rw [h i]; rfl)

lemma ctxVal_zero_ctx {n : ℕ} (Δ : GCtx LNL n) (h : IsZeroCtx Δ) : ctxVal ν Δ = 0 := by
  unfold ctxVal
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rcases h i with h | ⟨A, h⟩ <;> rw [h] <;> rfl

/-- Soundness of pattern typing: the bound context is bounded by the matched type. -/
lemma patTy_sound {k : ℕ} {o : Option LNL} {p : Pat k} {A : Ty LNL} {Δ : GCtx LNL k}
    (h : PatTy HSup.hsup o p A Δ) : ctxVal ν Δ ≤ optAct o (interp ν A) := by
  induction h with
  | var A => simp [ctxVal_single ν _ 0 (fun j hj => absurd (Subsingleton.elim j 0) hj),
      entry, optAct]
  | pair _ _ ih1 ih2 =>
    rw [ctxVal_append]; exact add_le_add ih1 ih2
  | box r _ ih => exact ih
  | gvar r A => simp [ctxVal_single ν _ 0 (fun j hj => absurd (Subsingleton.elim j 0) hj),
      entry, optAct]
  | gpair _ _ hst ih1 ih2 =>
    obtain ⟨rfl, rfl, rfl⟩ := LNL.hsup_eq_some.mp hst
    rw [ctxVal_append]
    exact add_le_add ih1 ih2
  | unit o =>
    rw [ctxVal_none ν _ (fun i => Fin.elim0 i)]
    cases o with
    | none => exact le_rfl
    | some r => cases r <;> simp [optAct, gact, interp, bang_zero]

lemma scale_entry_le {n : ℕ} (Γ : GCtx LNL n) (hg : IsGraded Γ) (i : Fin n) :
    entry ν (Γ i) ≤ entry ν (scale LNL.many Γ i) ∧ IsIdem (entry ν (scale LNL.many Γ i)) := by
  rcases h : Γ i with _ | ⟨A⟩ | ⟨A, s⟩
  · simp [scale, h, entry, IsIdem.zero]
  · exact absurd h (hg i A)
  · simp only [scale, h, Option.map_some, Assm.scale, entry]
    cases s <;> simp [LNL.mul_def, LNL.mul, gact, le_bang, bang_isIdem, IsIdem.zero]

/-- **Soundness** of the adjusted GrCore over `{0, 1, ω}` in the model. -/
theorem sound {n : ℕ} {Γ : GCtx LNL n} {t : Term n} {A : Ty LNL} (h : AdjTyped Γ t A) :
    interp ν A ≤ ctxVal ν Γ := by
  induction h with
  | var hi hj => rw [ctxVal_single ν _ _ hj, hi]; rfl
  | @lam n Γ t A B _ ih =>
    show res _ _ ≤ _
    rw [res_le_iff]
    have : ctxVal ν (Ctx.cons (some (.lin A)) Γ) = ctxVal ν Γ + interp ν A := by
      unfold ctxVal
      rw [Fin.sum_univ_succ, add_comm]; rfl
    rwa [this] at ih
  | app _ _ hadd ih1 ih2 =>
    refine le_trans ?_ (ctxAdd_le ν hadd)
    exact le_trans ((res_le_iff _ _ _).mp ih1) (add_le_add le_rfl ih2)
  | @der n Γ t A B i _ hi ih =>
    exact le_trans ih (ctxVal_update_le ν Γ i _ (by rw [hi]; rfl))
  | weak _ hz hadd ih =>
    refine le_trans ?_ (ctxAdd_le ν hadd)
    rw [ctxVal_zero_ctx ν _ hz, add_zero]; exact ih
  | @approx n Γ t A B i r s _ hi hrs ih =>
    exact le_trans ih (ctxVal_update_le ν Γ i _ (by rw [hi]; exact gact_mono hrs _))
  | @pr n Γ t A r _ hg ih =>
    cases r with
    | zero =>
      show (0 : Val) ≤ _
      rw [ctxVal_zero_ctx]
      intro i
      rcases h : Γ i with _ | ⟨B⟩ | ⟨B, s⟩
      · simp [scale, h]
      · exact absurd h (hg i B)
      · right; exact ⟨B, by simp only [scale, h, Option.map_some, Assm.scale]; cases s <;> rfl⟩
    | one =>
      have : scale (1 : LNL) Γ = Γ := by
        funext i
        rcases h : Γ i with _ | ⟨B⟩ | ⟨B, s⟩ <;> simp [scale, Assm.scale, h]
        cases s <;> rfl
      show interp ν A ≤ _
      rw [show LNL.one = 1 from rfl, this]; exact ih
    | many =>
      show bang _ ≤ _
      have hidem : IsIdem (ctxVal ν (scale LNL.many Γ)) :=
        IsIdem.sum _ _ (fun i _ => (scale_entry_le ν Γ hg i).2)
      refine bang_le_of_le hidem (le_trans ih ?_)
      exact Finset.sum_le_sum (fun i _ => (scale_entry_le ν Γ hg i).1)
  | unit hΓ => rw [ctxVal_none ν _ hΓ]; exact le_rfl
  | pair _ _ hadd ih1 ih2 =>
    exact le_trans (add_le_add ih1 ih2) (ctxAdd_le ν hadd)
  | letPat _ hp _ hadd ih1 ih2 =>
    rw [ctxVal_append] at ih2
    refine le_trans ih2 (le_trans ?_ (ctxAdd_le ν hadd))
    rw [add_comm (ctxVal ν _)]
    exact add_le_add (le_trans (patTy_sound ν hp) ih1) le_rfl

end GrModel

end LinExp

end
