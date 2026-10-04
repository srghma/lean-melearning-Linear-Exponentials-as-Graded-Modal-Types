module

public import RequestProject.Sec2_CoreCalculus.Notation

/-!
# Section 1: the distributive laws `push` and `pull`

The two distributive laws between the graded modality and the tensor discussed in the
introduction, written in GrCore:

* `pull_□ : □_r A ⊗ □_r B ⊸ □_r (A ⊗ B)`
* `push_□ : □_r (A ⊗ B) ⊸ □_r A ⊗ □_r B`   (Granule: `push [(x, y)] = ([x], [y])`)
-/

@[expose] public section

namespace LinExp

/-- `push = λ z. let [(x, y)] = z in ([x], [y])`. -/
def pushTerm : Term 0 := [grcore| λ z. let [(x, y)] = z in ([x], [y]) ]

/-- `pull = λ z. let ([x], [y]) = z in [(x, y)]`. -/
def pullTerm : Term 0 := [grcore| λ z. let ([x], [y]) = z in [(x, y)] ]

/-- The type `□_r (A ⊗ B) ⊸ □_r A ⊗ □_r B` of `push`. -/
def pushTy {R : Type} (r : R) (A B : Ty R) : Ty R := □[r] (A ⊗ B) ⊸ □[r] A ⊗ □[r] B

/-- The type `□_r A ⊗ □_r B ⊸ □_r (A ⊗ B)` of `pull`. -/
def pullTy {R : Type} (r : R) (A B : Ty R) : Ty R := □[r] A ⊗ □[r] B ⊸ □[r] (A ⊗ B)

end LinExp

end
