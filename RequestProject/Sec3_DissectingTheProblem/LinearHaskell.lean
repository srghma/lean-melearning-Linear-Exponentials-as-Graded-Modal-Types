module

public import RequestProject.Sec3_DissectingTheProblem.Push
public import RequestProject.Sec4_Solution.Theorem1.Theorem1
public import RequestProject.Sec4_Solution.IMELL.Facts

/-!
# Section 3: Linear Haskell

Linear Haskell function types `a %r -> b` carry a multiplicity `r ∈ {'One, 'Many}`, and a
graded modality is defined as a data type with one field of multiplicity `r`:

```haskell
data Box r a where { Box :: a %r -> Box r a }

push :: Box r (a, b) %1 -> (Box r a, Box r b)
push (Box (x, y)) = (Box x, Box y)
```

Matching on `Box p` binds the variables of `p` with multiplicity `r`, and Haskell allows the
nested pattern `Box (x, y)`, which binds *both* `x` and `y` with multiplicity `r`.  This is
GrCore's `[PPROD]` rule under a box with the same grade on both sides.  So the typing of this
fragment of Linear Haskell is GrCore (Section 2) over `{0, 1, ω}` with `'One = 1` and
`'Many = ω`, where `Box r a` is `□_r a` and `Unrestricted a = Box 'Many a` is `□_ω a`.  The
grade `0` is not a user-facing multiplicity of Linear Haskell; it only plays a role in the
usage of variables.

Results:

* `linearHaskell_push`: `push` type-checks at both multiplicities;
* `linearHaskell_unrestricted_not_bang`: the type of `push` at `Unrestricted` is derivable,
  but its image under the translation of Theorem 1 (with `□_ω = !`), namely
  `!(α ⊗ β) ⊸ !α ⊗ !β`, is not derivable in linear logic.  So `Unrestricted a` behaves
  differently from `!a`.

The `{0, 1, ω}` semiring, IMELL and the translation are defined in Section 4; like Section 1,
this file refers forward to that section.
-/

@[expose] public section

namespace LinExp

open LNL

/-- The multiplicities of Linear Haskell. -/
inductive HsMultiplicity : Type where
  /-- `'One`: linear use -/
  | One
  /-- `'Many`: unrestricted use -/
  | Many
  deriving DecidableEq, Repr

/-- A Linear Haskell multiplicity as a grade of `{0, 1, ω}`. -/
def HsMultiplicity.toGrade : HsMultiplicity → LNL
  | .One => 1
  | .Many => ω

/-- The Linear Haskell data type `Box r a`, i.e. `□_r a`. -/
def hsBox (r : HsMultiplicity) (A : Ty LNL) : Ty LNL := □[r.toGrade] A

/-- `Unrestricted a = Box 'Many a`. -/
def hsUnrestricted (A : Ty LNL) : Ty LNL := hsBox .Many A

/-- The type of Linear Haskell's `push :: Box r (a, b) %1 -> (Box r a, Box r b)`. -/
def hsPushTy (r : HsMultiplicity) (A B : Ty LNL) : Ty LNL :=
  hsBox r (A ⊗ B) ⊸ hsBox r A ⊗ hsBox r B

/-- **Linear Haskell admits `push`**, at both multiplicities: the definition
`push (Box (x, y)) = (Box x, Box y)` type-checks. -/
theorem linearHaskell_push (r : HsMultiplicity) (A B : Ty LNL) :
    GrCore (Ctx.empty 0) pushTerm (hsPushTy r A B) :=
  grcore_push r.toGrade A B

/-- The type of `push` at `Unrestricted` translates to linear logic's `push_!`. -/
theorem trTy_hsPushTy_many (A B : Ty LNL) :
    trTy (hsPushTy .Many A B) = pushBangTy (trTy A) (trTy B) := rfl

/-- **`Unrestricted a` is not `!a`.**  For distinct atoms `α`, `β`, Linear Haskell derives
`push : Unrestricted (α, β) %1 -> (Unrestricted α, Unrestricted β)`, but the translated type
`!(α ⊗ β) ⊸ !α ⊗ !β` is not derivable in linear logic. -/
theorem linearHaskell_unrestricted_not_bang {i j : ℕ} (hij : i ≠ j) :
    GrCore (Ctx.empty 0) pushTerm (hsPushTy .Many (.atom i) (.atom j)) ∧
      ¬ IDeriv (Ctx.empty 0) (trTy (hsPushTy .Many (.atom i) (.atom j))) :=
  ⟨linearHaskell_push _ _ _, imell_push_not_derivable hij⟩

end LinExp

end
