module

public import RequestProject.Sec4_Solution.Theorem1.GrCoreToIMELL
public import RequestProject.Sec4_Solution.Theorem1.IMELLToGrCore
public import RequestProject.Sec4_Solution.Theorem1.AsStated

/-!
# Section 4: Theorem 1 (equivalent expressivity)

*The adjusted GrCore calculus, for the none-one-tons semiring with `!A = □_ω A`, has the same
expressive power as IMELL.*

* (GrCore into IMELL) `Γ ⊢ t : A ⟹ ∃ M. ⟦Γ⟧ ⊢_IMELL M : ⟦A⟧` — proved for the translation
  with `⟦□_0 A⟧ = I` (`theorem1_grcore_to_imell`).  With the translation described in the
  paper (`⟦□_0 A⟧ = !⟦A⟧`) the statement is false (`theorem1_grcore_to_imell_as_stated_false`).
* (IMELL into GrCore) `Γ ⊢_IMELL M : T ⟹ ⟦Γ⟧ ⊢ ⟦M⟧ : ⟦T⟧` (`theorem1_imell_to_grcore`).
-/

@[expose] public section

namespace LinExp

/-- **Theorem 1** (with the corrected translation of `□_0`). -/
theorem theorem1 :
    (∀ (n : ℕ) (Γ : GCtx LNL n) (t : Term n) (A : Ty LNL),
      AdjTyped Γ t A → ∃ M, IHasType (trCtx Γ) M (trTy A)) ∧
    (∀ (n : ℕ) (Γ : ICtx n) (M : ITerm n) (T : ITy),
      IHasType Γ M T → AdjTyped (trCtxI Γ) (trTerm M) (trTyI T)) :=
  ⟨fun _ _ _ _ h => theorem1_grcore_to_imell h, fun _ _ _ _ h => theorem1_imell_to_grcore h⟩

/-- The two type translations are compatible: translating an IMELL formula into GrCore and
back gives the original formula (in particular `!A ↦ □_ω A ↦ !A`). -/
theorem trTy_trTyI (T : ITy) : trTy (trTyI T) = T := by
  induction T with
  | atom i => rfl
  | unit => rfl
  | lolli A B ihA ihB => simp [trTyI, trTy, ihA, ihB]
  | tensor A B ihA ihB => simp [trTyI, trTy, ihA, ihB]
  | bang A ih => simp [trTyI, trTy, ih]

end LinExp

end
