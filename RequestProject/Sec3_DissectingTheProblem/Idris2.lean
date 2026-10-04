module

public import RequestProject.Sec3_DissectingTheProblem.QTT
public import RequestProject.Sec4_Solution.IMELL.Facts

/-!
# Section 3: Idris 2

Every Idris 2 variable has a quantity `0`, `1` or `ω`, i.e. a grade of the none-one-tons
semiring `{0, 1, ω}` of Section 4.  Idris 2 cannot abstract over quantities, so the graded
modality is only available at `ω`, through the data type

```idris
data Unrestricted : Type -> Type where Box : a -> Unrestricted a

push : Unrestricted (a, b) -> (Unrestricted a, Unrestricted b)
push (Box (x, y)) = (Box x, Box y)
```

(the field of `Box` has the default quantity `ω`).  As in Linear Haskell, Idris 2 accepts the
nested pattern `Box (x, y)`, so its pattern matching is GrCore's (Section 2) and
`Unrestricted a` is `□_ω a`.

Results:

* `idris2_push`: `push` type-checks;
* `idris2_unrestricted_not_bang`: its type translates to linear logic's `push_!`, which is not
  derivable, so `Unrestricted a` is not `!a`;
* `idris2_vs_qtt`: Idris 2 accepts `push`, but QTT, on which Idris 2 is based, does not (see
  `RequestProject/Sec3_DissectingTheProblem/QTT.lean`).
-/

@[expose] public section

namespace LinExp

open LNL

/-- The Idris 2 data type `Unrestricted a`, i.e. `□_ω a`. -/
def idrisUnrestricted (A : Ty LNL) : Ty LNL := □[ω] A

/-- The type of Idris 2's `push : Unrestricted (a, b) -> (Unrestricted a, Unrestricted b)`
(the outer arrow is used linearly). -/
def idrisPushTy (A B : Ty LNL) : Ty LNL :=
  idrisUnrestricted (A ⊗ B) ⊸ idrisUnrestricted A ⊗ idrisUnrestricted B

/-- **Idris 2 admits `push`**: `push (Box (x, y)) = (Box x, Box y)` type-checks. -/
theorem idris2_push (A B : Ty LNL) : GrCore (Ctx.empty 0) pushTerm (idrisPushTy A B) :=
  grcore_push ω A B

/-- **`Unrestricted a` is not `!a`.**  For distinct atoms the type of `push` is derivable in
Idris 2, while its translation `!(α ⊗ β) ⊸ !α ⊗ !β` is not derivable in linear logic. -/
theorem idris2_unrestricted_not_bang {i j : ℕ} (hij : i ≠ j) :
    GrCore (Ctx.empty 0) pushTerm (idrisPushTy (.atom i) (.atom j)) ∧
      ¬ IDeriv (Ctx.empty 0) (trTy (idrisPushTy (.atom i) (.atom j))) :=
  ⟨idris2_push _ _, imell_push_not_derivable hij⟩

/-- **Idris 2 versus QTT.**  For distinct atoms, Idris 2 derives `push` at `Unrestricted`,
but in QTT the term `push` has no type at all, and no closed term has the type of `push`. -/
theorem idris2_vs_qtt {i j : ℕ} (hij : i ≠ j) :
    GrCore (Ctx.empty 0) pushTerm (idrisPushTy (.atom i) (.atom j)) ∧
      (∀ T : Ty LNL, ¬ QTTTyped (Ctx.empty 0) pushTerm T) ∧
      ¬ ∃ t : Term 0, QTTTyped (Ctx.empty 0) t (idrisPushTy (.atom i) (.atom j)) :=
  ⟨idris2_push _ _, qtt_push_ill_typed, qtt_push_many_not_derivable hij⟩

end LinExp

end
