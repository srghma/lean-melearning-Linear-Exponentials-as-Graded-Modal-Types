module

public import RequestProject.Sec3_DissectingTheProblem.Push
public import RequestProject.Sec3_DissectingTheProblem.LinearHaskell
public import RequestProject.Sec3_DissectingTheProblem.QTT
public import RequestProject.Sec3_DissectingTheProblem.Idris2
public import RequestProject.Sec3_DissectingTheProblem.LambdaP

/-!
# Section 3: Dissecting the problem

1. `Sec3_DissectingTheProblem/Push.lean` — nesting a tensor pattern inside an unboxing
   pattern derives `push : □_r (A ⊗ B) ⊸ □_r A ⊗ □_r B` in GrCore at every grade
   (`grcore_push`).
2. `Sec3_DissectingTheProblem/LinearHaskell.lean` — Linear Haskell's `Box r a` is `□_r a`;
   `push` type-checks (`linearHaskell_push`), so `Unrestricted a` is not `!a`
   (`linearHaskell_unrestricted_not_bang`).
3. `Sec3_DissectingTheProblem/QTT.lean` — QTT as the variant of GrCore without `[PPROD]`
   (`QTTTyped`), with its tensor rules (`QTTTyped.letPair`, `QTTTyped.letGradedPair`).  QTT does
   not admit `push` (`qtt_push_ill_typed`, `qtt_push_many_not_derivable`) and is conservative
   over linear logic (`qtt_conservative_over_imell`).
4. `Sec3_DissectingTheProblem/Idris2.lean` — Idris 2's `Unrestricted a` is `□_ω a`; `push`
   type-checks (`idris2_push`, `idris2_unrestricted_not_bang`), unlike in QTT
   (`idris2_vs_qtt`).
5. `Sec3_DissectingTheProblem/LambdaP.lean` — Abel and Bernardy's `Λ^p` (`LamP.LTyped`), with
   its graded product elimination `let (x, y) =^q t in u`.  `Λ^p` admits `push` (`lamP_push`),
   its rule is derivable in GrCore (`grcore_lamP_letPair`), and its `q = 1` instance is the QTT
   rule (`LamP.LTyped.letPair_one`); `lamP_vs_qtt` compares the two.

Files 2–5 use the `{0, 1, ω}` semiring, IMELL, the model and Theorem 1 of Section 4; like
Section 1, they refer forward to that section.
-/
