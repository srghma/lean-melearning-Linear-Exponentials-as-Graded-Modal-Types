module

public import RequestProject.Sec3_DissectingTheProblem.Push

/-!
# Section 3: Dissecting the problem

1. `Sec3_DissectingTheProblem/Push.lean` — nesting a tensor pattern inside an unboxing
   pattern derives `push : □_r (A ⊗ B) ⊸ □_r A ⊗ □_r B` in GrCore at every grade
   (`grcore_push`).

The informal comparisons with Linear Haskell, Idris 2, QTT and `Λ^p` are not formalized.
-/
