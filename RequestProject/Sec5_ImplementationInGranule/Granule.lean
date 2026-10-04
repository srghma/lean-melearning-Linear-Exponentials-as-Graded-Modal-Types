module

public import RequestProject.Sec4_Solution.PushNotDerivable

/-!
# Section 5: implementation in Granule

In Granule the grades `r` and `s` in `r ⊔ s` are necessarily the same (`r ⊔ r`), and for the
`LNL` semiring (`0`, `1`, `Many`) `r ⊔ r` is defined only when `r = 1`.  Hence the
(previously type-checkable) program

```granule
push : ∀ {a b : Type} . (a, b) [Many] → (a [Many], b [Many])
push [(x, y)] = ([x], [y])
```

is now ill-typed.  We model the type variables `a`, `b` by two distinct atomic types.
-/

@[expose] public section

namespace LinExp

open LNL

/-- For `LNL`, `r ⊔ r` is defined exactly when `r = 1`. -/
theorem lnl_hsup_self_defined_iff (r : LNL) : (∃ t, HSup.hsup r r = some t) ↔ r = 1 := by
  cases r <;> simp [HSup.hsup, LNL.hsup]

/-- The Granule program `push [(x, y)] = ([x], [y])` at type
`(a, b) [Many] → (a [Many], b [Many])` is ill-typed in the adjusted calculus. -/
theorem granule_push_many_ill_typed :
    ¬ AdjTyped (Ctx.empty 0) pushTerm (pushTy ω (.atom 0) (.atom 1)) :=
  fun h => adj_push_many_not_derivable (by decide) ⟨_, h⟩

/-- … whereas it was type-checkable before the adjustment (Section 3). -/
theorem granule_push_many_typed_before :
    GrCore (Ctx.empty 0) pushTerm (pushTy ω (.atom 0) (.atom 1)) :=
  grcore_push ω _ _

end LinExp

end
