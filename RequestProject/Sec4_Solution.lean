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
public import RequestProject.Sec4_Solution.Theorem1.Explicit.Combinators
public import RequestProject.Sec4_Solution.Theorem1.Explicit.Pattern
public import RequestProject.Sec4_Solution.Theorem1.Explicit.Translation
public import RequestProject.Sec4_Solution.Theorem1.Theorem1
public import RequestProject.Sec4_Solution.Coeffect.GradedComonad
public import RequestProject.Sec4_Solution.Coeffect.ResourceModel
public import RequestProject.Sec4_Solution.Semantics.CatModel
public import RequestProject.Sec4_Solution.Semantics.Interp
public import RequestProject.Sec4_Solution.Semantics.CountingModel
public import RequestProject.Sec4_Solution.Semantics.ErasureModel
public import RequestProject.Sec4_Solution.Atoms.Substitution
public import RequestProject.Sec4_Solution.Atoms.AtomFree

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
   a proof tool for underivability results (item 9 shows it is an instance of the categorical
   semantics).
5. `Sec4_Solution/PushNotDerivable.lean` — `!(A ⊗ B) ⊸ !A ⊗ !B` is no longer derivable
   (`adj_push_many_not_derivable`), while `push` at grade `1` still is (`adj_push_one`).
6. `Sec4_Solution/IMELL/` — IMELL with the term assignment of Benton et al.:
   `Syntax`, `Typing`, `Renaming`, `Model`, `Facts` (`pull_!` derivable, `push_!` not).
7. `Sec4_Solution/Theorem1/` — Theorem 1: `Translations`; the auxiliary admissible rules of
   IMELL `Admissible`, `Sharing`, `Promotion`; the two directions `GrCoreToIMELL` and
   `IMELLToGrCore`; `AsStated` (the translation of the original paper is refuted);
   `Explicit/` (the GrCore → IMELL term translation written out as a function `trDeriv` on
   typing derivations: IMELL term combinators `Combinators`, pattern elimination `Pattern`,
   and the translation with its correctness proof `Translation`); and finally `Theorem1`.
8. `Sec4_Solution/Coeffect/` — the coeffect remark at the end of Section 4: `⋉` is modelled by
   colax monoidality of a graded comonad. `GradedComonad` defines graded comonads, the graded
   exponential structure and the partial colax structure `HSupColax` indexed by `⋉`;
   `ResourceModel` builds a model over `{0, 1, ω}` that has the colax map for equation (1) but
   none for any `⋉` with `ω ⋉ ω` defined (`res_colax_exactly_eq1`), so the adjusted `[PPROD]`
   has strictly more models than GrCore's (`adjusted_colax_strictly_more_models`).
9. `Sec4_Solution/Semantics/` — a categorical semantics of the typing judgement `Typed hs`
   (not in the paper), for every pre-ordered semiring and every `⋉`, so for GrCore and for the
   adjusted calculus. `CatModel` defines models (symmetric monoidal closed category, graded
   exponential comonad, colax structure for `⋉`) and interprets types and contexts;
   `Interp` interprets every derivation as a morphism `⟦Γ⟧ ⟶ ⟦A⟧` (`CatModel.interp`,
   soundness `CatModel.sound`); `CountingModel` shows the resource-counting model of item 4 is
   an instance (`grModel_sound_from_catModel`, `adj_push_many_not_derivable_sem`);
   `ErasureModel` is the set-theoretic model with `D_r A = A`, valid for every `⋉`
   (`no_closed_term_of_atom`).
10. `Sec4_Solution/Atoms/` — the role of the atomic types added to both calculi (not in the
   paper). `Substitution`: atoms are type variables — substituting types for atoms preserves
   typing in GrCore (every `⋉`) and IMELL (`Typed.substAtoms`, `IHasType.substAtoms`), so a
   closed term has a type with atoms iff it has all its instances
   (`typed_atoms_iff_schematic`, `ihasType_atoms_iff_schematic`). `AtomFree`: without atoms
   every type is inhabited (`atomFree_inhabited`, `iatomFree_inhabited`, `ideriv_atomFree`),
   so the paper's underivability results are statements about schemas
   (`adj_push_many_schema`, `imell_push_schema`, `imell_dup_bang_schema`), and Theorem 1 with
   the paper's translation holds on atom-free judgements (`theorem1_as_stated_atomFree`).
-/
