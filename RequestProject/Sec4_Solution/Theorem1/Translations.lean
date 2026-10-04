module

public import RequestProject.Sec4_Solution.NoneOneTons
public import RequestProject.Sec4_Solution.IMELL.Typing

/-!
# Section 4 (Theorem 1): translations between GrCore over `{0, 1, ω}` and IMELL

* GrCore → IMELL, as described in the paper: `□_0 A` and `□_ω A` are mapped to `!⟦A⟧`,
  `□_1 A` to `⟦A⟧`, and similarly for graded assumptions (`x : [A]_ω` to `x : !⟦A⟧`).
  (`trTyPaper`, `trCtxPaper`.)
* GrCore → IMELL, corrected: `□_0 A` is mapped to the unit `I` instead.
  (`trTy`, `trCtx`.)  The paper source shipped with this project
  (`Linear Exponentials as Graded Modal Types.typ`) has been corrected to state this
  translation.  See `RequestProject/Sec4_Solution/Theorem1/AsStated.lean` for why the
  paper's mapping of `□_0` does not work.
* IMELL → GrCore: `!A` is mapped to `□_ω ⟦A⟧` and assumptions to linear assumptions.
  (`trTyI`, `trCtxI`.)
-/

@[expose] public section

namespace LinExp

/-- The paper's translation of GrCore types into IMELL formulas. -/
def trTyPaper : Ty LNL → ITy
  | .atom i => .atom i
  | .unit => .unit
  | .lolli A B => .lolli (trTyPaper A) (trTyPaper B)
  | .tensor A B => .tensor (trTyPaper A) (trTyPaper B)
  | .box .zero A => .bang (trTyPaper A)
  | .box .one A => trTyPaper A
  | .box .many A => .bang (trTyPaper A)

/-- The paper's translation of assumptions. -/
def trAssmPaper : Assm LNL → ITy
  | .lin A => trTyPaper A
  | .grad A r => trTyPaper (.box r A)

/-- The paper's translation of contexts. -/
def trCtxPaper {n : ℕ} (Γ : GCtx LNL n) : ICtx n := fun i => (Γ i).map trAssmPaper

/-- The corrected translation of GrCore types into IMELL formulas (`□_0 A ↦ I`). -/
def trTy : Ty LNL → ITy
  | .atom i => .atom i
  | .unit => .unit
  | .lolli A B => .lolli (trTy A) (trTy B)
  | .tensor A B => .tensor (trTy A) (trTy B)
  | .box .zero _ => .unit
  | .box .one A => trTy A
  | .box .many A => .bang (trTy A)

/-- The corrected translation of assumptions. -/
def trAssm : Assm LNL → ITy
  | .lin A => trTy A
  | .grad A r => trTy (.box r A)

/-- The corrected translation of contexts. -/
def trCtx {n : ℕ} (Γ : GCtx LNL n) : ICtx n := fun i => (Γ i).map trAssm

/-- Translation of IMELL formulas into GrCore types: `!A ↦ □_ω ⟦A⟧`. -/
def trTyI : ITy → Ty LNL
  | .atom i => .atom i
  | .unit => .unit
  | .lolli A B => .lolli (trTyI A) (trTyI B)
  | .tensor A B => .tensor (trTyI A) (trTyI B)
  | .bang A => .box .many (trTyI A)

/-- Translation of IMELL contexts into GrCore contexts (all assumptions linear). -/
def trCtxI {n : ℕ} (Γ : ICtx n) : GCtx LNL n := fun i => (Γ i).map (fun A => .lin (trTyI A))

end LinExp

end
