module

public import RequestProject.Sec4_Solution.Hsup
public import RequestProject.Sec4_Solution.HsupLub
public import RequestProject.Sec4_Solution.NoneOneTons
public import RequestProject.Sec4_Solution.Model.Value
public import RequestProject.Sec4_Solution.Model.GrCoreModel
public import RequestProject.Sec4_Solution.PushNotDerivable
public import RequestProject.Sec4_Solution.IMELL.Syntax
public import RequestProject.Sec4_Solution.IMELL.Typing
public import RequestProject.Sec4_Solution.IMELL.Renaming
public import RequestProject.Sec4_Solution.IMELL.Model
public import RequestProject.Sec4_Solution.IMELL.Facts
public import RequestProject.Sec4_Solution.Theorem1.Translations
public import RequestProject.Sec4_Solution.Theorem1.Admissible
public import RequestProject.Sec4_Solution.Theorem1.Sharing
public import RequestProject.Sec4_Solution.Theorem1.Promotion
public import RequestProject.Sec4_Solution.Theorem1.GrCoreToIMELL
public import RequestProject.Sec4_Solution.Theorem1.IMELLToGrCore
public import RequestProject.Sec4_Solution.Theorem1.AsStated
public import RequestProject.Sec4_Solution.Theorem1.Theorem1

/-!
# Section 4: Solution

Reading order:

1. `Sec4_Solution/Hsup.lean` — the partial operation `hsup` and the adjusted calculus
   (`AdjTyped`); the calculus of Section 2 is the instance `HSup.diag`.
2. `Sec4_Solution/HsupLub.lean` — taking `hsup` to be the partial least upper bound of the
   order recovers the calculus of Section 2 (`adjTyped_lub_iff_grcore`); for a discrete
   order (exact usage) this is `diagHsup` (`isPartialLub_diagHsup`).
3. `Sec4_Solution/NoneOneTons.lean` — the semiring `{0, 1, ω}` and equation (1).
4. `Sec4_Solution/Model/` — `Value`, `GrCoreModel`: a resource-counting model, used only as
   a proof tool for underivability results.
5. `Sec4_Solution/PushNotDerivable.lean` — `!(A ⊗ B) ⊸ !A ⊗ !B` is no longer derivable
   (`adj_push_many_not_derivable`), while `push` at grade `1` still is (`adj_push_one`).
6. `Sec4_Solution/IMELL/` — IMELL with the term assignment of Benton et al.:
   `Syntax`, `Typing`, `Renaming`, `Model`, `Facts` (`pull_!` derivable, `push_!` not).
7. `Sec4_Solution/Theorem1/` — Theorem 1: `Translations`; the auxiliary admissible rules of
   IMELL `Admissible`, `Sharing`, `Promotion`; the two directions `GrCoreToIMELL` and
   `IMELLToGrCore`; `AsStated` (the translation of the original paper is refuted); and
   finally `Theorem1`.
-/
