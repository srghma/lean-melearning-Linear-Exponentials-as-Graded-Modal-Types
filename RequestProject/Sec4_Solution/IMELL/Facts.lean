module

public import RequestProject.Sec4_Solution.IMELL.Model

/-!
# Section 1/4: `pull_!` and `push_!` in IMELL

* `⊢_LL pull_! : !A ⊗ !B ⊸ !(A ⊗ B)`
* `⊬_LL push_! : !(A ⊗ B) ⊸ !A ⊗ !B`  (for distinct atoms `A`, `B`)

We also record that `α ⊸ α ⊗ !α` is not provable; this is used in
`RequestProject/Sec4_Solution/Theorem1` to refute the first half of Theorem 1 as stated.
-/

@[expose] public section

namespace LinExp

/-- `!(A ⊗ B) ⊸ !A ⊗ !B` -/
def pushBangTy (A B : ITy) : ITy := .lolli (.bang (.tensor A B)) (.tensor (.bang A) (.bang B))

/-- `!A ⊗ !B ⊸ !(A ⊗ B)` -/
def pullBangTy (A B : ITy) : ITy := .lolli (.tensor (.bang A) (.bang B)) (.bang (.tensor A B))

/-- `pull_! = λz. let z be x ⊗ y in promote x, y for a, b in (derelict a ⊗ derelict b)`. -/
def pullBangTerm : ITerm 0 :=
  .lam (.letPair (.var 0)
    (.promote (k := 2) (fun j => if j.val = 0 then .var 1 else .var 0)
      (.pair (.derelict (.var 0)) (.derelict (.var 1)))))

/-- **`⊢_LL pull_!`**: `!A ⊗ !B ⊸ !(A ⊗ B)` is provable in IMELL. -/
theorem imell_pull (A B : ITy) : IHasType (Ctx.empty 0) pullBangTerm (pullBangTy A B) := by
  refine IHasType.lam (IHasType.letPair (Γ₁ := Ctx.cons (some (.tensor (.bang A) (.bang B)))
    (Ctx.empty 0)) (Γ₂ := Ctx.empty 1) (IHasType.var rfl (fun j hj => ?_)) ?_ ?_)
  · fin_cases j; simp at hj
  · refine IHasType.promote (As := fun j => if j.val = 0 then A else B)
      (Γs := fun j => if j.val = 0 then (fun i => if i.val = 1 then some (.bang A) else none)
        else (fun i => if i.val = 0 then some (.bang B) else none)) ?_ ?_ ?_
    · refine ⟨fun i => if i.val = 0 then some (.bang B) else none, ⟨fun i => if i.val = 3 then
        some (.bang B) else none, fun i => ?_, fun i => ?_⟩, fun i => ?_⟩
      · fin_cases i <;> simp
      · fin_cases i <;> simp
      · fin_cases i <;> simp [Ctx.append, ctx2, Ctx.empty]
    · intro j
      fin_cases j
      · exact IHasType.var (by simp) (fun i hi => by
          simp only [↓reduceIte]
          exact if_neg (fun h => hi (Fin.ext h)))
      · exact IHasType.var (by simp) (fun i hi => by
          simp only [one_ne_zero, ↓reduceIte]
          exact if_neg (fun h => hi (Fin.ext h)))
    · refine IHasType.pair (Γ₁ := fun i => if i.val = 0 then some (.bang A) else none)
        (Γ₂ := fun i => if i.val = 1 then some (.bang B) else none)
        (IHasType.derelict (IHasType.var (by simp) (fun i hi => if_neg (fun h => hi (Fin.ext h)))))
        (IHasType.derelict (IHasType.var (by simp) (fun i hi => if_neg (fun h => hi (Fin.ext h)))))
        (fun i => ?_)
      fin_cases i <;> simp
  · intro i; fin_cases i; simp [Ctx.empty]

/-- **`⊬_LL push_!`**: `!(α ⊗ β) ⊸ !α ⊗ !β` is not provable in IMELL for distinct atoms. -/
theorem imell_push_not_derivable {i j : ℕ} (hij : i ≠ j) :
    ¬ IDeriv (Ctx.empty 0) (pushBangTy (.atom i) (.atom j)) := by
  rintro ⟨M, hM⟩
  let ν : ℕ → ℤ := fun k => if k = i then 1 else if k = j then -1 else 0
  have h := IModel.sound ν hM
  rw [IModel.ctxVal_none ν _ (fun k => Fin.elim0 k)] at h
  have hj : ν j = -1 := by simp [ν, Ne.symm hij]
  have hi : ν i = 1 := by simp [ν]
  simp [pushBangTy, IModel.interp, hi, hj, Val.bang, Val.res, Val.zero_eq] at h

/-- `α ⊸ α ⊗ !α` is not provable in IMELL. -/
theorem imell_not_derivable_atom_tensor_bang (i : ℕ) :
    ¬ IDeriv (Ctx.empty 0) (.lolli (.atom i) (.tensor (.atom i) (.bang (.atom i)))) := by
  rintro ⟨M, hM⟩
  have h := IModel.sound (fun _ => 1) hM
  rw [IModel.ctxVal_none _ _ (fun k => Fin.elim0 k)] at h
  simp [IModel.interp, Val.bang, Val.res, Val.zero_eq] at h

end LinExp

end
