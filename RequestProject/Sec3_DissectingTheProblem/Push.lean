module

public import RequestProject.Sec2_CoreCalculus.Derived
public import RequestProject.Sec1_Introduction.Terms

/-!
# Section 3: dissecting the problem

In GrCore one may nest a tensor pattern inside an unboxing pattern:

```
Γ₁ ⊢ t₁ : □_r (A ⊗ B)    · ⊢ [(x, y)] : □_r (A ⊗ B) ▷ x : [A]_r, y : [B]_r    Γ₂, x : [A]_r, y : [B]_r ⊢ t₂ : C
───────────────────────────────────────────────────────────────────────────────────── (LET)
                      Γ₁ + Γ₂ ⊢ let [(x, y)] = t₁ in t₂ : C
```

With `t₂ = ([x], [y])` this derives `push_□ : □_r (A ⊗ B) ⊸ □_r A ⊗ □_r B` for *every* grade
`r`, so no `□_r` of GrCore can be linear logic's `!`.
-/

@[expose] public section

namespace LinExp

variable {R : Type} [Semiring R] [Preorder R]

/-- The derivation displayed at the start of Section 3, as a derived rule: it is available
whenever the operation used by `[PPROD]` satisfies `r ⊔ r = r` (which is the case for the
calculus of Section 2). -/
theorem Typed.letBoxPair {hs : R → R → Option R} {r : R} (hrr : hs r r = some r) {n : ℕ}
    {Γ₁ Γ₂ Γ : GCtx R n} {t₁ : Term n} {t₂ : Term (n + (1 + 1))} {A B C : Ty R}
    (h₁ : Typed hs Γ₁ t₁ (□[r] (A ⊗ B)))
    (h₂ : Typed hs (Ctx.append Γ₂ (Ctx.append (fun _ => some (.grad A r))
      (fun _ => some (.grad B r)))) t₂ C)
    (hadd : CtxAdd Γ₁ Γ₂ Γ) :
    Typed hs Γ (.letPat (.box (.pair .var .var)) t₁ t₂) C :=
  Typed.letPat h₁ (PatTy.box r (PatTy.gpair (PatTy.gvar r A) (PatTy.gvar r B) hrr)) h₂ hadd

/-- `push_□` is derivable at every grade `r` whenever `r ⊔ r = r`. -/
theorem push_typed {hs : R → R → Option R} {r : R} (hrr : hs r r = some r) (A B : Ty R) :
    Typed hs (Ctx.empty 0) pushTerm (pushTy r A B) := by
  refine Typed.lam (Typed.letBoxPair (Γ₁ := Ctx.cons (some (.lin (□[r] (A ⊗ B)))) (Ctx.empty 0))
    (Γ₂ := Ctx.empty 1) hrr (Typed.var rfl (fun j hj => ?_)) ?_ ?_)
  · fin_cases j; simp at hj
  · refine Typed.pair (Γ₁ := fun i => if i.val = 1 then some (.grad A r) else none)
      (Γ₂ := fun i => if i.val = 0 then some (.grad B r) else none)
      (Typed.box_var (by simp) (fun j hj => if_neg (fun h => hj (Fin.ext h))))
      (Typed.box_var (by simp) (fun j hj => if_neg (fun h => hj (Fin.ext h)))) ?_
    intro i
    fin_cases i <;> simp [Ctx.append, Ctx.empty] <;> constructor
  · intro i
    fin_cases i
    simp [Ctx.empty]
    constructor

/-- **Section 3.** In GrCore (Section 2), `push_□ : □_r (A ⊗ B) ⊸ □_r A ⊗ □_r B` is
derivable for every grade `r` and all types `A`, `B`. -/
theorem grcore_push [DecidableEq R] (r : R) (A B : Ty R) :
    GrCore (Ctx.empty 0) pushTerm (pushTy r A B) :=
  push_typed (by simp [diagHsup]) A B

end LinExp

end
