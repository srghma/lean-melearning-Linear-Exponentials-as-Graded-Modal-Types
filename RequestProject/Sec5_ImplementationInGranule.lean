module

public import RequestProject.Sec5_ImplementationInGranule.Granule
public import RequestProject.Sec5_ImplementationInGranule.DataTypes.Syntax
public import RequestProject.Sec5_ImplementationInGranule.DataTypes.Typing
public import RequestProject.Sec5_ImplementationInGranule.DataTypes.Embedding
public import RequestProject.Sec5_ImplementationInGranule.DataTypes.Inversion
public import RequestProject.Sec5_ImplementationInGranule.Constraints.PatCheck
public import RequestProject.Sec5_ImplementationInGranule.Constraints.Correctness
public import RequestProject.Sec5_ImplementationInGranule.Constraints.Instantiate
public import RequestProject.Sec5_ImplementationInGranule.Constraints.Solver
public import RequestProject.Sec5_ImplementationInGranule.Examples

/-!
# Section 5: Implementation in Granule

1. `Sec5_ImplementationInGranule/Granule.lean` — for `LNL`, `r ⊔ r` is defined only at
   `r = 1`; the Granule `push` at `[Many]` is ill-typed after the adjustment, and was typable
   before it.

Data types (ADTs and GADTs):

2. `DataTypes/Syntax.lean` — types with data types `data d i` (name `d`, GADT index `i`),
   signatures of constructors (`GSig`), constructor patterns, constructor terms and `case`.
3. `DataTypes/Typing.lean` — the typing judgement `GTyped`, with Granule-style pattern typing
   `GPatTy`: under a box of grade `r`, all sub-patterns of a constructor (or pair) pattern are
   checked at `r`, and if there is at least one sub-pattern, `r ⋉ r` must be defined.
4. `DataTypes/Embedding.lean` — GrCore embeds into this calculus (`grcore_embeds`), for every
   `⋉` defined only on the diagonal (Section 2's and equation (1)).
5. `DataTypes/Inversion.lean` — if a pattern cannot be matched against `A`, no program
   `λz. let p = z in u` has a type `A ⊸ B` (`lam_letPat_var_ill_typed`).

Constraint solving:

6. `Constraints/PatCheck.lean` — the constraint language `GFormula` and the constraint
   generator `patCheck` for patterns.
7. `Constraints/Correctness.lean` — `patCheck_iff`: pattern typing holds iff `patCheck`
   succeeds and its constraint holds.
8. `Constraints/Instantiate.lean` — constraint generation commutes with instantiating grades.
9. `Constraints/Solver.lean` — grade variables, satisfiability and validity of constraints,
   their correctness for grade-polymorphic types, and executable decision procedures over
   finite grade structures (standing in for the SMT solver).

10. `Examples.lean` — `push`, `Maybe`, `Vec`, `case`, and grade-polymorphic `push`, over
    `LNL`.
-/
