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
* Section 5: `granule_push_many_ill_typed`, `granule_push_many_typed_before`,
  `lnl_hsup_self_defined_iff`.
* Section 6: `both_push_and_bang`.

## What is still missing (not formalized)

1. **Section 3, scope of the comparisons.** Linear Haskell and Idris 2 are modelled only
   through their `Box`/`Unrestricted` data types and nested pattern matching, i.e. as GrCore
   over `{0, 1, ω}`. Type dependency in QTT, and graded function types `q A → B` in `Λ^p`, are
   not modelled (only linear functions are). The remark that `Λ^p`'s models include the one
   showing every linear term is a permutation is not formalized. There is no full translation
   of `Λ^p` into GrCore; only its product rule is shown to be derivable.
2. **Section 4, the coeffect remark.** The colax-monoidality reading
   `n_{r,s,A,B} : D_{r ⋉ s}(A ⊗ B) → D_r A ⊗ D_s B` (Petricek et al.) needs a categorical
   semantics, which is not formalized.
3. **Section 4, a semantics for GrCore in general.** The only model is a resource-counting
   model for `{0, 1, ω}`, and it serves only to prove underivability. There is no
   denotational or operational semantics, and no cut elimination or substitution lemma for
   GrCore, but the paper does not claim any of these.
4. **Section 5, the Granule specifics.** User-defined ADTs/GADTs, `hsup` applied to arbitrary
   constructors, and discharging the constraints with an SMT solver are not modelled. Only the
   `r ⊔ r` restriction for `LNL` and the `push` example are formalized.
5. **Theorem 1, the exact shape of the translations.** GrCore → IMELL is proved in the form the
   paper states it (`∃ M`). The type-directed term translation itself is not given as a
   function. IMELL → GrCore uses an explicit term translation (`trTerm`).
6. **Design assumption.** Both calculi have atomic types added. Without atoms every type is
   inhabited and the underivability statements would be trivial.

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
