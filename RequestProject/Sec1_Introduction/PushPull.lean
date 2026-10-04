module

public import RequestProject.Sec3_DissectingTheProblem.Push
public import RequestProject.Sec4_Solution.IMELL.Facts

/-!
# Section 1: introduction — `pull` and `push` in graded type theory (GR) and in linear logic (LL)

```
⊢_GR pull_□ : □_r A ⊗ □_r B ⊸ □_r (A ⊗ B)        ⊢_GR push_□ : □_r (A ⊗ B) ⊸ □_r A ⊗ □_r B
⊢_LL pull_! : !A ⊗ !B ⊸ !(A ⊗ B)                  ⊬_LL push_! : !(A ⊗ B) ⊸ !A ⊗ !B
```

Here GR is GrCore (Section 2), and LL is IMELL with Benton et al.'s term assignment
(Section 4).  `⊬_LL push_!` is stated for distinct atomic formulas `A`, `B`.
-/

@[expose] public section

namespace LinExp

variable {R : Type} [Semiring R] [Preorder R]

/-- `pull_□` is derivable at every grade, whatever the operation used by `[PPROD]` (it only
uses `[PBOX]` and `[PVAR]` patterns). -/
theorem pull_typed (hs : R → R → Option R) (r : R) (A B : Ty R) :
    Typed hs (Ctx.empty 0) pullTerm (pullTy r A B) := by
  refine Typed.lam (Typed.letPat (Γ₁ := Ctx.cons (some (.lin (□[r] A ⊗ □[r] B))) (Ctx.empty 0))
    (Γ₂ := Ctx.empty 1) (Typed.var rfl (fun j hj => ?_))
    (PatTy.pair (PatTy.box r (PatTy.gvar r A)) (PatTy.box r (PatTy.gvar r B))) ?_ ?_)
  · fin_cases j; simp at hj
  · let Γ0 : GCtx R (0 + 1 + (1 + 1)) := fun i =>
      if i.val = 0 then some (.grad B 1) else if i.val = 1 then some (.grad A 1) else none
    have h0 : Typed hs Γ0 (.pair (.var ⟨1, by decide⟩) (.var ⟨0, by decide⟩)) (A ⊗ B) := by
      refine Typed.pair (Γ₁ := fun i => if i.val = 1 then some (.grad A 1) else none)
        (Γ₂ := fun i => if i.val = 0 then some (.grad B 1) else none)
        (Typed.var_one (by simp) (fun j hj => if_neg (fun h => hj (Fin.ext h))))
        (Typed.var_one (by simp) (fun j hj => if_neg (fun h => hj (Fin.ext h)))) ?_
      intro i
      fin_cases i <;> simp [Γ0] <;> constructor
    refine (h0.pr r (fun i C => ?_)).of_eq ?_
    · simp only [Γ0]; split_ifs <;> simp
    · funext i
      fin_cases i <;> simp [Γ0, scale, Assm.scale, Ctx.append, Ctx.empty]
  · intro i; fin_cases i; simp [Ctx.empty]; constructor

/-- **`⊢_GR pull_□`** (in GrCore, Section 2). -/
theorem gr_pull [DecidableEq R] (r : R) (A B : Ty R) :
    GrCore (Ctx.empty 0) pullTerm (pullTy r A B) :=
  pull_typed diagHsup r A B

/-- **`⊢_GR push_□`** (in GrCore, Section 2; see Section 3). -/
theorem gr_push [DecidableEq R] (r : R) (A B : Ty R) :
    GrCore (Ctx.empty 0) pushTerm (pushTy r A B) :=
  grcore_push r A B

/-- **`⊢_LL pull_!`**. -/
theorem ll_pull (A B : ITy) : IDeriv (Ctx.empty 0) (pullBangTy A B) :=
  ⟨_, imell_pull A B⟩

/-- **`⊬_LL push_!`** (for distinct atomic formulas). -/
theorem ll_push_not_derivable {i j : ℕ} (hij : i ≠ j) :
    ¬ IDeriv (Ctx.empty 0) (pushBangTy (.atom i) (.atom j)) :=
  imell_push_not_derivable hij

end LinExp

end
