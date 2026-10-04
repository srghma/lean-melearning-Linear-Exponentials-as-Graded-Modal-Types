module

public import RequestProject.Sec4_Solution.Theorem1.Theorem1
public import RequestProject.Sec4_Solution.PushNotDerivable

/-!
# Section 6: conclusions

The `hsup` operation lets one calculus retain *both* the power of `push` and that of `!`,
depending on the grade structure:

* with `hsup = diagHsup` (`r ⊔ s = r` iff `r = s`), `push` is derivable at every grade
  (this is the calculus of Section 2);
* with the none-one-tons semiring and equation (1), `push` is not derivable at grade `ω`,
  and `□_ω` behaves as IMELL's `!` (Theorem 1).
-/

@[expose] public section

namespace LinExp

open LNL

/-- Summary of the paper's main claims, as formalized. -/
theorem both_push_and_bang :
    (∀ (R : Type) [Semiring R] [Preorder R] [DecidableEq R] (r : R) (A B : Ty R),
      @AdjTyped R _ _ (HSup.diag R) 0 (Ctx.empty 0) pushTerm (pushTy r A B)) ∧
    (¬ ∃ t : Term 0, AdjTyped (Ctx.empty 0) t (pushTy ω (.atom 0) (.atom 1))) ∧
    (∀ (n : ℕ) (Γ : GCtx LNL n) (t : Term n) (A : Ty LNL),
      AdjTyped Γ t A → ∃ M, IHasType (trCtx Γ) M (trTy A)) ∧
    (∀ (n : ℕ) (Γ : ICtx n) (M : ITerm n) (T : ITy),
      IHasType Γ M T → AdjTyped (trCtxI Γ) (trTerm M) (trTyI T)) :=
  ⟨fun _ _ _ _ r A B => grcore_push r A B, adj_push_many_not_derivable (by decide),
    theorem1.1, theorem1.2⟩

end LinExp

end
