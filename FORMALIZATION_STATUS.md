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

Sections 2 to 6 import only earlier sections, so they can be read in numerical order. Section 1
is the one exception. Like the paper's introduction, it states results that are only made
precise later: its terms are GrCore terms (Section 2), `⊢ push_□` is the derivation of
Section 3, and LL is IMELL (Section 4). Skim it first for the statements, and come back to it
after Section 4 for the proofs.

## What is formalized

* Section 1: `gr_pull`, `gr_push`, `ll_pull`, `ll_push_not_derivable`.
* Section 2: syntax (de Bruijn, `Term n`), `[grcore| … ]` notation, all typing rules, renaming.
* Section 3: `grcore_push` (push is derivable at every grade).
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

1. **Section 3, the other languages.** Linear Haskell, Idris 2, QTT and Abel & Bernardy's
   `Λ^p` are only discussed informally in the paper. The two rules the paper shows (the
   simplified QTT tensor elimination and the `Λ^p` graded `let`) could be added as variants of
   the calculus. Then one could prove "QTT does not admit push" and "`Λ^p` admits push". These
   claims are not stated precisely in the paper.
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
