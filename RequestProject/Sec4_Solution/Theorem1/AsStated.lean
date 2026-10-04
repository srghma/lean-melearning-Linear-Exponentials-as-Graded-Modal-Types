module

public import RequestProject.Sec4_Solution.Theorem1.Translations
public import RequestProject.Sec4_Solution.IMELL.Facts
public import RequestProject.Sec2_CoreCalculus.Derived
public import RequestProject.Sec2_CoreCalculus.Notation

/-!
# Section 4: the GrCore → IMELL half of Theorem 1, *as stated*, fails

The paper states (Theorem 1, GrCore into IMELL):
`Γ ⊢ t : A ⟹ ∃ M. ⟦Γ⟧ ⊢_IMELL M : ⟦A⟧`, where the translation "maps both `□_0 A` and
`□_ω A` to `!⟦A⟧` and `□_1 A` to just `⟦A⟧`".

With that translation the statement is false as soon as there are atomic types: the closed
term `λz. let [y] = z in (y, [y])` has type `□_1 α ⊸ α ⊗ □_0 α` in the adjusted calculus
(the variable `y : [α]_1` is used once linearly and once under a `0`-box, and `1 + 0 = 1`),
but its translation `α ⊸ α ⊗ !α` is not provable in IMELL.

The corrected statement (with `□_0 A ↦ I`) is proved in
`RequestProject/Sec4_Solution/Theorem1/GrCoreToIMELL.lean`.
-/

@[expose] public section

namespace LinExp

/-- The counterexample term `λz. let [y] = z in (y, [y])`. -/
def dupZeroTerm : Term 0 := [grcore| λ z. let [y] = z in (y, [y]) ]

/-- `λz. let [y] = z in (y, [y]) : □_1 α ⊸ α ⊗ □_0 α` (in the adjusted calculus). -/
theorem dupZeroTerm_typed (i : ℕ) :
    AdjTyped (Ctx.empty 0) dupZeroTerm (□[(1 : LNL)] (.atom i) ⊸ .atom i ⊗ □[(0 : LNL)] (.atom i)) := by
  refine Typed.lam (Typed.letPat (Γ₁ := Ctx.cons (some (.lin (□[(1 : LNL)] (.atom i)))) (Ctx.empty 0))
    (Γ₂ := Ctx.empty 1) (Typed.var rfl (fun j hj => ?_)) (PatTy.box 1 (PatTy.gvar 1 _)) ?_ ?_)
  · fin_cases j; simp at hj
  · refine Typed.pair (Γ₁ := fun k => if k.val = 0 then some (.grad (.atom i) 1) else none)
      (Γ₂ := fun k => if k.val = 0 then some (.grad (.atom i) 0) else none)
      (Typed.var_one (by simp) (fun j hj => if_neg (fun h => hj (Fin.ext h))))
      (Typed.box_var (by simp) (fun j hj => if_neg (fun h => hj (Fin.ext h)))) ?_
    intro k
    fin_cases k
    · exact EntryAdd.grad _ 1 0
    · simp [Ctx.append, Ctx.empty]; exact EntryAdd.noneLeft none
  · intro k; fin_cases k; exact EntryAdd.noneRight _

/-- **Theorem 1 (GrCore into IMELL), as stated in the paper, is false** (in the presence of
atomic types): there is a derivable judgement of the adjusted calculus over `{0, 1, ω}` whose
translation (with `□_0 A ↦ !⟦A⟧`) is not derivable in IMELL. -/
theorem theorem1_grcore_to_imell_as_stated_false :
    ¬ ∀ (n : ℕ) (Γ : GCtx LNL n) (t : Term n) (A : Ty LNL),
      AdjTyped Γ t A → ∃ M, IHasType (trCtxPaper Γ) M (trTyPaper A) := by
  intro h
  obtain ⟨M, hM⟩ := h 0 _ _ _ (dupZeroTerm_typed 0)
  have e : trCtxPaper (Ctx.empty 0 : GCtx LNL 0) = Ctx.empty 0 := funext (fun k => Fin.elim0 k)
  rw [e] at hM
  exact imell_not_derivable_atom_tensor_bang 0 ⟨M, hM⟩

end LinExp

end
