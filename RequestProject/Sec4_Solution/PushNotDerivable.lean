module

public import RequestProject.Sec4_Solution.Model.GrCoreModel
public import RequestProject.Sec3_DissectingTheProblem.Push

/-!
# Section 4: the adjusted calculus disallows `!(A ⊗ B) → !A ⊗ !B`

With `hsup` given by equation (1) on `{0, 1, ω}`, the `[PPROD]` rule can no longer be applied
under an `ω`-box, and `push : □_ω (A ⊗ B) ⊸ □_ω A ⊗ □_ω B` is not derivable (by *any* closed
term) for distinct atomic types `A`, `B`.  The proof is semantic: the type is not valid in the
model of `RequestProject/Sec4_Solution/Model`.

On the other hand `push` remains derivable at grade `1` (where `1 ⊔ 1 = 1`), and in the
unadjusted calculus of Section 2 it is derivable at every grade (Section 3).
-/

@[expose] public section

namespace LinExp

open LNL

/-- **Section 4.** In the adjusted calculus over `{0, 1, ω}` there is no closed term of type
`□_ω (α ⊗ β) ⊸ □_ω α ⊗ □_ω β` for distinct atoms `α`, `β`. -/
theorem adj_push_many_not_derivable {i j : ℕ} (hij : i ≠ j) :
    ¬ ∃ t : Term 0, AdjTyped (Ctx.empty 0) t (pushTy ω (.atom i) (.atom j)) := by
  rintro ⟨t, ht⟩
  let ν : ℕ → ℤ := fun k => if k = i then 1 else if k = j then -1 else 0
  have h := GrModel.sound ν ht
  rw [GrModel.ctxVal_none ν _ (fun k => Fin.elim0 k)] at h
  have hj : ν j = -1 := by simp [ν, Ne.symm hij]
  have hi : ν i = 1 := by simp [ν]
  simp [pushTy, GrModel.interp, GrModel.gact, hi, hj, Val.bang, Val.res, Val.zero_eq] at h

/-- In the adjusted calculus over `{0, 1, ω}`, `push` is still derivable at grade `1`. -/
theorem adj_push_one (A B : Ty LNL) : AdjTyped (Ctx.empty 0) pushTerm (pushTy 1 A B) :=
  push_typed rfl A B

/-- The same type *is* derivable in the unadjusted calculus of Section 2 (cf. Section 3). -/
theorem grcore_push_many (A B : Ty LNL) : GrCore (Ctx.empty 0) pushTerm (pushTy ω A B) :=
  grcore_push ω A B

end LinExp

end
