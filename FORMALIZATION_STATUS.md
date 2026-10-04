# Formalization status: "Linear Exponentials as Graded Modal Types"

## Layout and reading order

| Directory | Paper section | Index file |
|---|---|---|
| `RequestProject/Sec1_Introduction/` | 1 Introduction | `RequestProject/Sec1_Introduction.lean` |
| `RequestProject/Sec2_CoreCalculus/` | 2 Core calculus | `RequestProject/Sec2_CoreCalculus.lean` |
| `RequestProject/Sec3_DissectingTheProblem/` | 3 Dissecting the problem | `RequestProject/Sec3_DissectingTheProblem.lean` |
| `RequestProject/Sec4_Solution/` | 4 Solution | `RequestProject/Sec4_Solution.lean` |
| `RequestProject/Sec5_ImplementationInGranule/` | 5 Implementation in Granule | `RequestProject/Sec5_ImplementationInGranule.lean` |
| `RequestProject/Sec6_Conclusions/` | 6 Conclusions | `RequestProject/Sec6_Conclusions.lean` |

Each index file lists the files of its section in reading order. `RequestProject.lean`
imports all six sections.

Sections 2 to 6 import only earlier sections, so they can be read in numerical order, with two
exceptions. The Section 3 comparison files (Linear Haskell, QTT, Idris 2, `Λ^p`) use the
`{0, 1, ω}` semiring, IMELL, the model and Theorem 1 from Section 4. Section 1 is the other
exception. Like the paper's introduction, it states results that are only made
precise later: its terms are GrCore terms (Section 2), `⊢ push_□` is the derivation of
Section 3, and LL is IMELL (Section 4). Skim it first for the statements, and come back to it
after Section 4 for the proofs.

## What is formalized

* Section 1: `gr_pull`, `gr_push`, `ll_pull`, `ll_push_not_derivable`.
* Section 2: syntax (de Bruijn, `Term n`), `[grcore| … ]` notation, all typing rules, renaming.
* Section 3: `grcore_push` (push is derivable at every grade), and the comparisons with other
  systems:
  * **Linear Haskell** (`LinearHaskell.lean`): `Box r a` is `□_r a` with `'One = 1`,
    `'Many = ω`. `linearHaskell_push` shows `push` type-checks at both multiplicities;
    `linearHaskell_unrestricted_not_bang` shows that the type of `push` at `Unrestricted` is
    derivable while its translation `!(α ⊗ β) ⊸ !α ⊗ !β` is not derivable in IMELL.
  * **QTT** (`QTT.lean`): a variant of the calculus, `QTTTyped = Typed qttHsup`, in which
    `[PPROD]` never applies (`qttHsup` is always undefined). The simplified QTT rule and QTT's
    graded-pair rule are rules of the variant (`QTTTyped.letPair`, `QTTTyped.letGradedPair`).
    No product pattern can be typed under a box (`qtt_no_pair_under_box`). Results:
    `qtt_push_ill_typed` (over any semiring the term `push` has no type), `qttTyped_to_grcore`
    and `qttTyped_to_adjTyped` (QTT is a fragment of both calculi),
    `qtt_push_many_not_derivable` (over `{0, 1, ω}`, no closed term has the type of `push` at
    `ω`) and `qtt_conservative_over_imell` (every QTT judgement translates into IMELL).
  * **Idris 2** (`Idris2.lean`): `Unrestricted a` is `□_ω a`. `idris2_push`,
    `idris2_unrestricted_not_bang`, and `idris2_vs_qtt` (Idris 2 accepts `push`, QTT does not).
  * **Abel & Bernardy's `Λ^p`** (`LambdaP.lean`): a separate calculus `LamP.LTyped` with
    grade-vector contexts and the graded eliminator `let (x, y) =^q t in u`. Results:
    `lamP_push` (push at every grade, over every semiring), `LamP.LTyped.letPair_one` (the
    `q = 1` instance is the QTT rule), `grcore_lamP_letPair` (the `Λ^p` rule is derivable in
    GrCore as `let [(x, y)] = [t] in u`), and `lamP_vs_qtt` (over `{0, 1, ω}`, `Λ^p` derives
    push at `ω`, while QTT and IMELL do not).
* Section 4:
  * the `hsup` extension (`HSup`, `AdjTyped`);
  * **new:** `adjTyped_lub_iff_grcore`: taking `hsup` to be the partial least upper bound
    recovers the calculus of Section 2. Also `isPartialLub_diagHsup`: for the exact-usage
    (discrete) order, `hsup` is defined only when `r = s`;
  * none-one-tons and equation (1);
  * `adj_push_many_not_derivable`, `adj_push_one`;
  * Theorem 1, corrected (`theorem1`), and the refutation of the translation in the original
    paper (`theorem1_grcore_to_imell_as_stated_false`).
  * **new (coeffect remark):** `Sec4_Solution/Coeffect/GradedComonad.lean` defines graded
    comonads (`GradedComonad`), the extra structure used for graded contexts
    (`GradedExponential`), and partial colax monoidality indexed by `⋉`
    (`HSupColax hs G`: a map `n_{r,s,A,B} : D_{r⋉s}(A ⊗ B) → D_r A ⊗ D_s B` exactly when
    `r ⋉ s` is defined). General results: `HSupColax.push` (semantic `push` from
    `r ⋉ r = r`), `diag_colax_push` (models of GrCore's `[PPROD]` have `push` at every grade),
    `HSupColax.restrict`, `no_colax_of_no_split`. `Sec4_Solution/Coeffect/ResourceModel.lean`
    gives a concrete thin symmetric monoidal model over `{0, 1, ω}` (sets of resource vectors,
    `D_ω A` = generated submonoid): it is a graded exponential comonad (`resExp`) with the
    colax structure of equation (1) (`resColax`), but has no morphism
    `D_t(a ⊗ b) → D_ω a ⊗ D_ω b` for any `t` (`res_no_split_many`), hence no colax structure
    for any `⋉` with `ω ⋉ ω` defined (`res_no_colax_of_many_defined`,
    `res_not_grcore_colax`, `res_colax_exactly_eq1`); so the adjusted `[PPROD]` has strictly
    more models than GrCore's (`adjusted_colax_strictly_more_models`).
* **Semantics (not in the paper)** (`Sec4_Solution/Semantics/`): a categorical semantics of the
  typing judgement `Typed hs`, for every pre-ordered semiring and every partial `⋉` (so both for
  Section 2's GrCore and for the adjusted calculus).
  * A model `CatModel R hs C` is a symmetric monoidal closed category `C` with a graded
    exponential comonad (`GradedExponential`), a colax structure `HSupColax hs` for `[PPROD]`,
    maps `D_r I ⟶ I` (the unit pattern under a box) and objects for the atoms.
  * Types, assumptions and contexts are interpreted as objects (`tyObj`, `entryObj`, `ctxObj`).
  * `Deriv hs Γ t A` is the type of derivations (same rules as `Typed`, valued in `Type`);
    `typed_iff_nonempty_deriv`. Every derivation denotes a morphism
    `CatModel.interp d : ⟦Γ⟧ ⟶ ⟦A⟧` (and every pattern derivation `?r⟦A⟧ ⟶ ⟦Δ⟧`).
  * Soundness: `CatModel.sound` (derivable ⇒ a morphism `⟦Γ⟧ ⟶ ⟦A⟧` exists in every model),
    and `CatModel.not_typed_of_isEmpty` (no global element of `⟦A⟧` in some model ⇒ no closed
    term of type `A`).
  * Instances: the resource-counting model (`countingModel`, a thin model of the adjusted
    calculus over `{0, 1, ω}`): its interpretation agrees with `GrModel`
    (`countingModel_hom_iff`), so `GrModel.sound` is a special case
    (`grModel_sound_from_catModel`) and `adj_push_many_not_derivable` gets a second proof
    (`adj_push_many_not_derivable_sem`). The erasure model in `Type` (`erasureModel`, `D_r A = A`)
    is a model for every `hs`; it shows no closed term has an atomic type
    (`no_closed_term_of_atom`).
* Section 5: `granule_push_many_ill_typed`, `granule_push_many_typed_before`,
  `lnl_hsup_self_defined_iff`, and Granule's data types and constraint solving:
  * **Data types** (`DataTypes/`): types gain `data d i` (data type `d` at GADT index `i`); a
    signature `GSig` gives the field types of each constructor at each index (`none` when the
    constructor cannot build that index, which is how GADT index refinement is modelled).
    Constructors are first-class terms, patterns gain `c p₁ ⋯ pₘ`, and there is an `m`-way
    `case`. Pattern typing `GPatTy` follows Section 5's description of Granule: under a box of
    grade `r`, all sub-patterns of a constructor or pair pattern are checked at `r`, and if
    there is at least one sub-pattern, `r ⋉ r` must be defined. GrCore embeds into the
    extended calculus for every `⋉` defined only on the diagonal (`grcore_embeds`; covers
    Section 2 and equation (1)). Inversion: if a pattern cannot be matched against `A`, no
    program `λz. let p = z in u` has a type `A ⊸ B` (`lam_letPat_var_ill_typed`).
  * **Constraints** (`Constraints/`): a constraint language `GFormula` (connectives, `=`, `⊑`,
    "`g ⋉ g` is defined") and a constraint generator `patCheck` for patterns, generic in the
    grades. `patCheck_iff`: pattern typing holds iff `patCheck` succeeds and its constraint
    holds. `patCheck_map`: generation commutes with instantiating grades. With grade
    variables (`GExp R V`), `patTy_some_instance_iff` / `patTy_all_instances_iff`: the pattern
    can be typed at some / every instantiation iff the symbolic constraint is satisfiable /
    valid. Over finite grades both are decidable; `checkPatSat` and `checkPatValid` are
    executable checkers with correctness theorems (`checkPatSat_iff`, `checkPatValid_iff`).
    General consequences: `GPatTy.con_requires_hsup`, `GPatTy.pair_requires_hsup`,
    `GPatTy.con_nullary`.
  * **Examples** (`Examples.lean`, over `LNL` with equation (1)): `push`'s pattern `[(x, y)]`
    is rejected at `[Many]` and the whole program is ill-typed
    (`granule_push_many_ill_typed_dt`, `granule_push_many_ill_typed_dt'`), accepted at `[1]`
    (`granule_push_one_typed_dt`); `[Just x]` rejected at `Many` but `[Nothing]` accepted;
    `Nil` does not match `Vec 1 a`; `[Cons x Nil]` accepted at `[1]`, rejected at `[Many]`;
    `unwrap_typed` and `maybeId_typed` (constructors and `case`); grade-polymorphic `push`:
    constraint satisfiable but not valid (`pushPat_poly_satisfiable`,
    `pushPat_poly_not_valid`).
* Section 6: `both_push_and_bang`.

## What is still missing (not formalized)

1. **Section 3, scope of the comparisons.** Linear Haskell and Idris 2 are modelled only
   through their `Box`/`Unrestricted` data types and nested pattern matching, i.e. as GrCore
   over `{0, 1, ω}`. Type dependency in QTT, and graded function types `q A → B` in `Λ^p`, are
   not modelled (only linear functions are). The remark that `Λ^p`'s models include the one
   showing every linear term is a permutation is not formalized. There is no full translation
   of `Λ^p` into GrCore; only its product rule is shown to be derivable.
2. **Section 4, the coeffect remark: scope.** The remark is formalized in
   `Sec4_Solution/Coeffect/` (see above). `GradedComonad`, `GradedExponential` and
   `HSupColax` impose the graded comonad laws, naturality, and the colax counit, symmetry and
   associativity laws, but not every coherence law between the different pieces of structure
   (e.g. between approximation and comultiplication, or between contraction and the colax map).
3. **Semantics of GrCore: what is still missing.** A categorical semantics of derivations now
   exists (`Sec4_Solution/Semantics/`, see above). Not covered: an equational theory or
   operational semantics (β/η reduction, substitution lemma, cut elimination) and its soundness
   in the models; coherence (that different derivations of the same judgement have the same
   denotation; this would need the full set of coherence laws of item 2); completeness. The
   paper does not claim any of these.
4. **Section 5, scope of the data-type model.** Data types are modelled with ℕ-valued GADT
   indices and monomorphised type parameters (each instance of `Maybe a` is its own data-type
   name); there is no type-level polymorphism or index unification, and impossible `case`
   branches are simply untypable. Exhaustiveness of `case` is not checked. Constraint
   generation is formalized for patterns only (term typing stays declarative), and the SMT
   solver is replaced by a decision procedure that enumerates valuations, so it only applies to
   finite grade types. The reading of "`r ⋉ r` defined at `r`" is: `r ⋉ r` is defined; for
   Section 2's `⋉` and equation (1), whenever it is defined it equals `r`.
5. **Theorem 1, the exact shape of the translations.** GrCore → IMELL is proved in the form the
   paper states it (`∃ M`). The type-directed term translation itself is not given as a
   function. IMELL → GrCore uses an explicit term translation (`trTerm`).
6. **Design assumption, now justified formally** (`Sec4_Solution/Atoms/`). Both calculi have
   atomic types added. They act exactly as the paper's type metavariables: substituting types
   for atoms preserves typing in GrCore (for every `⋉`) and in IMELL (`Typed.substAtoms`,
   `IHasType.substAtoms`), so a closed term has a type with atoms iff it has every instance
   (`typed_atoms_iff_schematic`, `ihasType_atoms_iff_schematic`). Without atoms every type is
   inhabited — GrCore/adjusted calculus over any semiring where each grade is `⊒ 0` or `⊒ 1`
   (`atomFree_inhabited`, in particular `{0, 1, ω}`), and every IMELL sequent
   (`ideriv_atomFree`). So `⊬ push_!`, `⊬ □_ω(A ⊗ B) ⊸ □_ω A ⊗ □_ω B` and `⊬ A ⊸ A ⊗ !A` are
   statements about schemas: no single term works for all `A`, `B`, yet each atom-free
   instance is derivable (`imell_push_schema`, `adj_push_many_schema`,
   `imell_dup_bang_schema`). Likewise Theorem 1 with the paper's original translation holds on
   all atom-free judgements (`theorem1_as_stated_atomFree`); its refutation needs atoms.
   Not covered: the GrCore case for semirings with grades above neither `0` nor `1` (e.g.
   exact usage `ℕ` with grade `2`).

## Review of the Typst source (`Linear Exponentials as Graded Modal Types.typ`)

The file compiles with Typst 0.15 and produces no warnings. Compared with the original PDF:

Fixed in this revision:

* **Equation (1)** was rendered inline, in small type and without its number "(1)". It is now
  a numbered display equation.
* **QTT rule:** `U[(x, y)/z]` and `U[M/z]` were typeset as fractions. The slash is now
  escaped.
* **(APPROX):** the rule used `A` both for the type of `x` and for the type of `t`. That forces
  the two to be equal, which is not intended. The original PDF has the same slip. The term's
  type is now `B`, which matches the Lean rule `Typed.approx`.
* **Code blocks** could split across a page break, which left their label ("Granule",
  "Idris 2") alone at the top of the next page. They are now unbreakable.
* The colax map was renamed to `⋉_{r,s,A,B}`. It is `n_{r,s,A,B}` again, as in the original.
* Removed a stray space in "Theorem 1 (Equivalent expressivity) .".

Changed in the earlier revision, and still correct:

* Theorem 1's translation: `□_0 A ↦ 1`, not `!⟦A⟧`, with the counterexample.
* Equation (1): the missing first case was restored.

Not changed: the PDF itself. It is the original paper.
