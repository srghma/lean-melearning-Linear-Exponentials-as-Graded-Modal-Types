module

public import RequestProject.Sec4_Solution.Theorem1.Admissible

/-!
# Section 4 (Theorem 1, auxiliary): promotion of `!`-contexts in IMELL

If every assumption of `Γ` has the form `!A`, then `Γ ⊢ B` implies `Γ ⊢ !B` (using Benton et
al.'s `promote` with one argument per variable in scope).
-/

@[expose] public section

namespace LinExp

/-- A pointwise criterion for `ISplitN`. -/
theorem ISplitN.of_pointwise {n : ℕ} : ∀ (k : ℕ) (Γs : Fin k → ICtx n) (Γ : ICtx n),
    (∀ x, (Γ x = none ∧ ∀ j, Γs j x = none) ∨
      ∃ j, Γs j x = Γ x ∧ ∀ j', j' ≠ j → Γs j' x = none) → ISplitN k Γs Γ
  | 0, Γs, Γ, h => fun x => by
    rcases h x with ⟨hx, _⟩ | ⟨j, _⟩
    · exact hx
    · exact Fin.elim0 j
  | k + 1, Γs, Γ, h => by
    refine ⟨fun x => if Γs 0 x = none then Γ x else none, ISplitN.of_pointwise k _ _ ?_, ?_⟩
    · intro x
      rcases h x with ⟨hx, hall⟩ | ⟨j, hj, hothers⟩
      · left; simp [hx, hall]
      · by_cases hj0 : j = 0
        · subst hj0
          left
          refine ⟨?_, fun j' => hothers _ (Fin.succ_ne_zero _)⟩
          split_ifs with h0
          · rw [← hj, h0]
          · rfl
        · obtain ⟨j₀, rfl⟩ := Fin.exists_succ_eq.mpr hj0
          right
          refine ⟨j₀, ?_, fun j' hj' => hothers _ (fun e => hj' (Fin.succ_injective _ e))⟩
          rw [if_pos (hothers 0 (Ne.symm hj0)), hj]
    · intro x
      by_cases h0 : Γs 0 x = none
      · left; simp [h0]
      · right
        simp only [h0, ↓reduceIte, true_and]
        rcases h x with ⟨_, hall⟩ | ⟨j, hj, hothers⟩
        · exact absurd (hall 0) h0
        · by_cases hj0 : j = 0
          · subst hj0; exact hj
          · exact absurd (hothers 0 (Ne.symm hj0)) h0

/-- The argument of a `!`-formula (and `I` otherwise). -/
def bangArg : Option ITy → ITy
  | some (.bang A) => A
  | _ => .unit

/-- `promote` with no arguments: `⊢ promote for in * : !I`. -/
lemma promote_unit {n : ℕ} :
    IHasType (Ctx.empty n) (.promote (k := 0) Fin.elim0 .star) (.bang .unit) :=
  IHasType.promote (Γs := Fin.elim0) (As := Fin.elim0) (fun _ => rfl) (fun j => Fin.elim0 j)
    (IHasType.star (fun j => Fin.elim0 j))

/-- **Promotion** of a context consisting only of `!`-assumptions. -/
theorem IDeriv.promote_all {n : ℕ} (Γ : ICtx n)
    (h : ∀ i, Γ i = none ∨ ∃ A, Γ i = some (.bang A)) {B : ITy} (hd : IDeriv Γ B) :
    IDeriv Γ (.bang B) := by
  classical
  let As : Fin n → ITy := fun i => bangArg (Γ i)
  have hfill : IDeriv (fun i => some (.bang (As i))) B := by
    refine IDeriv.ctxwise (fun i => ?_) hd
    rcases h i with hi | ⟨A, hi⟩
    · rw [hi]; exact PosEnt.addBang _
    · simp only [As, hi, bangArg]; exact PosEnt.refl _
  obtain ⟨N, hN⟩ := hfill
  let Γs : Fin n → ICtx n := fun i x => if x = i then Γ x else none
  let Ms : Fin n → ITerm n := fun i => if (Γ i).isSome then .var i else
    .promote (k := 0) Fin.elim0 .star
  refine ⟨.promote Ms N, IHasType.promote (Γs := Γs) (As := As) ?_ (fun i => ?_) hN⟩
  · refine ISplitN.of_pointwise n Γs Γ (fun x => ?_)
    by_cases hx : Γ x = none
    · left; exact ⟨hx, fun j => by simp only [Γs]; split_ifs <;> simp_all⟩
    · right; exact ⟨x, by simp [Γs], fun j hj => by simp [Γs, Ne.symm hj]⟩
  · rcases h i with hi | ⟨A, hi⟩
    · have hΓs : Γs i = Ctx.empty n := by
        funext x; simp only [Γs, Ctx.empty]; split_ifs with hx
        · rw [hx, hi]
        · rfl
      simp only [Ms, hi, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hΓs, As, bangArg]
      exact promote_unit
    · simp only [Ms, hi, Option.isSome_some, ↓reduceIte, As, bangArg]
      exact IHasType.var (by simp [Γs, hi]) (fun j hj => by simp [Γs, hj])

end LinExp

end
