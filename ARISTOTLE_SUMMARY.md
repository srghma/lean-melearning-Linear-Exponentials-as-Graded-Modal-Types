# Summary of changes for run 8ffe1f8e-6369-4d00-889f-6f72bccc12a8
I took "implement" to mean: prove in Lean the two claims behind the "Atomic types" note, which until now were only stated in comments. First, the atoms added to both calculi act exactly like the paper's metavariables `A`, `B`. Second, without atoms every type has a closed term, so the paper's "cannot be derived" results only make sense when `A`, `B` are read as type variables. Both are now proved. The project builds with no errors and no `sorry`, and the new theorems use only the standard axioms.

**New folder `RequestProject/Sec4_Solution/Atoms/`**

`Substitution.lean`: atoms behave as type variables
- `Ty.substAtoms` and `ITy.substAtoms` replace each atom with a given type.
- `Typed.substAtoms`: substituting types for atoms keeps a GrCore term typed, with the same term. This holds for every pair rule `⋉`, so for both Section 2's calculus and the adjusted calculus. `IHasType.substAtoms` is the same result for IMELL.
- Consequence (`typed_atoms_iff_schematic`, `ihasType_atoms_iff_schematic`): a closed term has a type containing atoms exactly when it has every instance of that type.

`AtomFree.lean`: without atoms everything is inhabited
- `Ty.AtomFree` and `ITy.AtomFree` describe the paper's own types, which have no atoms.
- `atomFree_inhabited`: every atom-free type has a closed term \(t : A\) and a closed term \(A ⊸ 1\). This holds for GrCore and the adjusted calculus, for every `⋉`, over any semiring where each grade \(r\) satisfies \(0 ⊑ r\) or \(1 ⊑ r\); this includes \(\{0,1,\omega\}\). `adj_atomFree_inhabited` and `grcore_atomFree_inhabited` are the \(\{0,1,\omega\}\) instances.
- `iatomFree_inhabited` and `ideriv_atomFree`: in IMELL, every sequent built from atom-free formulas is provable.
- The paper's negative results only hold as statements about schemas. In each case below, no single term works for all `A`, `B`, but every atom-free instance can be derived:
  - `imell_push_schema` for \(!(A⊗B) ⊸ !A ⊗ !B\);
  - `adj_push_many_schema` for \(\square_\omega(A⊗B) ⊸ \square_\omega A ⊗ \square_\omega B\) in the adjusted calculus;
  - `imell_dup_bang_schema` for \(A ⊸ A ⊗ !A\).
- `theorem1_as_stated_atomFree`: with the paper's original translation (\(\square_0 A \mapsto !⟦A⟧\)), every atom-free judgement translates to a derivable IMELL sequent. So the earlier refutation of Theorem 1 as stated depends on having atoms.

**Limitation:** the GrCore inhabitation result does not cover semirings with a grade above neither \(0\) nor \(1\), for example exact-usage \(\mathbb N\) at grade \(2\).

I also updated the Section 4 index (`RequestProject/Sec4_Solution.lean`, new item 10), the comment in `RequestProject/Sec2_CoreCalculus/Syntax.lean`, and item 6 of `FORMALIZATION_STATUS.md`. The Properties table has eight new proved properties and two new definitions (`Ty.AtomFree`, `Ty.substAtoms`).

# Summary of changes for run df905e8a-6a5c-4957-83eb-624927ef1bdd
The GrCore → IMELL translation of Theorem 1 is now a function, `trDeriv`, and its correctness is proved. The full project builds with no errors, warnings or `sorry`, and the new theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Design choice: the translation takes a typing derivation, not a bare term.** GrCore terms carry no type annotations. The IMELL term depends on grades that only the derivation records, such as the grade of a promotion `[t]` or of an unboxing pattern. So no function of the bare term would work. The paper also calls this a "type-directed translation". The typing judgement is a proposition, so I added derivations as data:
- **`RequestProject/Sec2_CoreCalculus/Derivation.lean`:** `Derivation hs Γ t A` has the same rules as `Typed`, as data. `typed_iff_nonempty_derivation` shows a judgement is derivable exactly when it has a derivation.

**The translation (`RequestProject/Sec4_Solution/Theorem1/Explicit/`)**
- **`Combinators.lean`** builds explicit IMELL terms for the rules the earlier proof only showed were derivable, each with a typing lemma:
  - `cutAt`: substitution as a β-redex.
  - `adjustAt` / `adjustAll`: change the assumption at one position or at every position (dereliction, adding or removing an `I`, discarding a `!A`, `I` to `!A`).
  - `splitTm r s`: the colax maps \(⟦\square_{r+s}A⟧ ⊸ ⟦\square_r A⟧ ⊗ ⟦\square_s A⟧\).
  - `shareL`: combines two premises that share graded variables by splitting each shared variable with `splitTm`.
  - `promoteTm`: Benton et al.'s `promote` for a context of `!`-assumptions.
- **`Pattern.lean`:** `patElim` eliminates a pattern. Product patterns become `let _ be x ⊗ y in _`; a unit pattern becomes `let _ be * in _` or `discard` (when its assumption has type `!I`). `patElim_typed` proves it correct.
- **`Translation.lean`:** `trDeriv` is defined by recursion on derivations and is computable.
  - Variables and λ map to themselves.
  - Application, pair and `let` use `shareL`.
  - DER is the identity.
  - WEAK consumes the new `[A]_0` variables.
  - APPROX uses `discard` (from 0 to ω) or `derelict` (from 1 to ω).
  - PR at grade 0 builds `*`, at grade 1 is the identity, and at grade ω uses `promote`.
  - `trDeriv_typed` proves \(⟦Γ⟧ ⊢ \mathsf{trDeriv}\ d : ⟦A⟧\) for every derivation `d`. It uses the corrected type translation (\(\square_0 A ↦ I\)).
  - The file ends with one checked example: the derivation of `λx. x` translates to `λx. x`. That is the only computed example; the others would have needed derivations that are awkward to build by hand.

**Theorem 1 (`Theorem1/Theorem1.lean`)**
- `theorem1_explicit` states both directions with explicit term translations: `trDeriv` for GrCore → IMELL and the existing `trTerm` for IMELL → GrCore.
- `theorem1_grcore_to_imell_explicit` gives the paper's form ("there exists a term M"), with `trDeriv` supplying the term.
- The earlier `theorem1` and its proofs are unchanged.

I updated the section index files and added four entries to the Properties table: `Derivation`, `trDeriv`, and the two proved properties `trDeriv_typed` and `theorem1_explicit`. I did not check whether the older Theorem 1 entries still say the translation is not written out; their notes may need a small update. All work is committed.

# Summary of changes for run 1949e5e4-3906-47de-adb0-73f7c3946b33
I added Granule's data types (ADTs and GADTs) and its constraint-based pattern checking to the Section 5 folder. The full project builds with no errors, warnings or `sorry`, and the new theorems use only the standard axioms. Two simplifications: a decision procedure that tries every grade assignment stands in for the SMT solver, and constraints are generated for patterns only.

**Data types (`RequestProject/Sec5_ImplementationInGranule/DataTypes/`)**
- **Syntax:** types now include `data d i` (data type `d` at GADT index `i`). A signature `GSig` lists each constructor's field types at each index. A constructor that can't build a given index has no entry there; that is how GADT index refinement works here. Constructors are first-class terms, patterns gain `c p₁ ⋯ pₘ`, and there is an `m`-way `case`. Terms stay de Bruijn-indexed (`GTerm 0` is the closed terms).
- **Typing (`GTyped`, with pattern typing `GPatTy`):** this follows the paper's description. Under a box of grade \(r\), every sub-pattern of a constructor or pair pattern is checked at \(r\). If there is at least one sub-pattern, \(r ⋉ r\) must be defined.
- **`grcore_embeds`:** every GrCore derivation is also a derivation of the new calculus, for any `⋉` that is only defined when both grades are equal (Section 2's `⋉` and equation (1)).
- **`lam_letPat_var_ill_typed`:** if a pattern can't be matched against \(A\), then no program `λz. let p = z in u` has type \(A ⊸ B\).

**Constraint solving (`Constraints/`)**
- `patCheck` turns a pattern and a type into either a failure or the bound variables plus a constraint on the grades.
- `patCheck_iff`: a pattern can be typed exactly when `patCheck` succeeds and its constraint holds.
- `patCheck_map`: generating constraints and then instantiating the grades gives the same result as instantiating first.
- With grade variables, `patTy_some_instance_iff` and `patTy_all_instances_iff` show that the pattern types at some (or every) instantiation exactly when the constraint is satisfiable (or valid).
- The executable checkers `checkPatSat` and `checkPatValid` come with correctness proofs. They only work when the grades and grade variables are finite, as for `LNL`.
- `GPatTy.con_requires_hsup`, `GPatTy.pair_requires_hsup` and `GPatTy.con_nullary` state the "at least one sub-pattern" rule directly.

**Examples (`Examples.lean`, `LNL` with equation (1))**
- The paper's `push` is rejected at `[Many]`: every program of the form `push [(x, y)] = u` is ill-typed (`granule_push_many_ill_typed_dt`). It is accepted at `[1]`.
- `[Just x]` is rejected under `Many`, but the nullary `[Nothing]` is accepted.
- `Nil` doesn't match `Vec 1 a`. `[Cons x Nil]` is accepted at `[1]` and rejected at `[Many]`.
- `unwrap_typed` and `maybeId_typed` show constructors and `case` working.
- For grade-polymorphic `push`, the constraint is satisfiable but not valid.

**Limits**
- Type parameters are handled by monomorphisation: `Maybe a` for each `a` is a separate data type. There is no type-level polymorphism or index unification.
- `case` is not checked for exhaustiveness.
- I read "\(r ⋉ r\) defined at \(r\)" as "\(r ⋉ r\) is defined". For both of the paper's choices of `⋉`, it then equals \(r\).

The Section 5 index file and `FORMALIZATION_STATUS.md` are updated. The Properties table has two new definitions and five new proved properties.

# Summary of changes for run c05d06d2-08c8-471e-89c4-cb4892c9a284
I added a semantics for GrCore: every typing derivation is now interpreted as a morphism in a categorical model. It works for any pre-ordered semiring and any partial `⋉`, so it covers both Section 2's GrCore and the adjusted calculus of Section 4. The full project builds with no errors, warnings or `sorry`, and the new theorems use only the standard axioms. The paper has no such semantics; this is new material.

There are four new files in `RequestProject/Sec4_Solution/Semantics/`:

- **`CatModel.lean` – what a model is.** `CatModel R hs C` reuses the structures from the earlier coeffect work:
  - a symmetric monoidal closed category, where \(⊸\) is the internal hom;
  - a graded exponential comonad for \(\square_r\);
  - the partial colax maps \(D_{r⋉s}(A⊗B) \to D_rA ⊗ D_sB\) for `[PPROD]`;
  - a map \(D_r I \to I\), needed for the unit pattern under a box;
  - objects for the atoms.

  The file interprets types, assumptions and contexts as objects. It also builds the maps for the context operations: context addition (contraction on shared graded variables), weakening, dereliction, approximation, promotion, and joining a pattern's bindings onto the context.
- **`Interp.lean` – interpreting derivations.**
  - `Typed` is a proposition, so a function can't take its proofs apart. I added `Deriv`, a data-valued copy with exactly the same rules, and proved `typed_iff_nonempty_deriv`.
  - `CatModel.interp` sends each derivation \(Γ ⊢ t : A\) to a morphism \(⟦Γ⟧ \to ⟦A⟧\), by recursion on the derivation.
  - `CatModel.sound`: if a judgement is derivable, every model has a morphism \(⟦Γ⟧ \to ⟦A⟧\). As a corollary, `not_typed_of_isEmpty`: if some model has no global element of \(⟦A⟧\), no closed term has type \(A\).
- **`CountingModel.lean` – the old counting model is an instance.**
  - `countingModel ν` turns the existing \(\{0,1,ω\}\) counting model into a model of the adjusted calculus: there is a morphism \(x \to y\) iff \(y ≤ x\), the internal hom is the existing implication, and the colax map exists only for \(1⋉1\).
  - `countingModel_hom_iff`: its interpretation agrees with the original one. So the earlier soundness theorem follows from the general one (`grModel_sound_from_catModel`).
  - `adj_push_many_not_derivable_sem` re-proves that `push` at \(ω\) has no derivation, this time through the general semantics.
- **`ErasureModel.lean` – a model for every `⋉`.** `erasureModel` uses ordinary types and functions, with \(D_r A = A\). As an application, `no_closed_term_of_atom` shows that no closed term has an atomic type, in GrCore and in every variant.

**What is still not covered:**
- **No equations:** there is no reduction relation, substitution lemma or cut elimination, and no proof that the models respect them.
- **Coherence:** it isn't shown that different derivations of the same judgement get the same morphism. That would need more coherence laws than the structures currently require.
- **Completeness** is not addressed.
- **Models of GrCore itself:** the only model given for Section 2's GrCore (not the adjusted calculus) is the erasure model, which ignores grades.

I updated the index file `RequestProject/Sec4_Solution.lean` and `FORMALIZATION_STATUS.md` to match. The Properties table has two new definitions (the model structure and the interpretation of derivations) and three new proved properties (general soundness, the counting model as an instance, and no closed term of atomic type).

# Summary of changes for run d123beee-4927-4b71-b46f-bb8753217e57
I formalized the coeffect remark at the end of Section 4: the paper's `⋉` is modelled by colax monoidality of a graded comonad, \(n_{r,s,A,B} : D_{r⋉s}(A⊗B) \to D_r A ⊗ D_s B\). I also built a concrete model showing that, there, the restriction to \(1 ⋉ 1 = 1\) in equation (1) cannot be relaxed to allow \(ω ⋉ ω\). The whole project builds with no errors, warnings or `sorry`, and the new theorems use only the standard axioms. One limit: this gives a categorical semantics for the graded modality and `⋉`, but there is no theorem interpreting every typing derivation in it, so it isn't a semantics for the full typing judgement.

There are two new files in `RequestProject/Sec4_Solution/Coeffect/`. The project builds them through `Sec4_Solution.lean`, which also lists them in the section's reading order.

**`GradedComonad.lean` (definitions, using Mathlib's monoidal categories)**
- `GradedComonad R C`: a graded comonad \(D_r\) with counit, comultiplication \(D_{r*s} \to D_r D_s\), and approximation maps \(D_s \to D_r\) for \(r ⊑ s\) (the semantic version of `(APPROX)`). The graded comonad laws are included.
- `GradedExponential`: adds weakening, contraction \(D_{r+s}A \to D_rA ⊗ D_sA\), and the lax monoidal maps that promotion needs. Only their naturality is required.
- `HSupColax hs G`: the remark itself. It is a partial colax structure that supplies \(n_{r,s,A,B}\) exactly when \(r ⋉ s\) is defined, with naturality, counit, symmetry and associativity laws.
- General results:
  - `HSupColax.push`: whenever \(r ⋉ r = r\), the colax map gives a semantic `push`.
  - `diag_colax_push`: with Section 2's `⋉` (defined iff \(r = s\)), any model of `[PPROD]` has `push` at every grade.
  - `HSupColax.restrict`: making `⋉` less defined removes requirements on a model.
  - `no_colax_of_no_split`: if a model has no morphism of the colax map's type at \(ω ⋉ ω\), it has no colax structure at all for any `⋉` that defines it.

**`ResourceModel.lean` (a concrete model over \(\{0,1,ω\}\))**
- Objects are sets of resource vectors, and there is a morphism \(A \to B\) exactly when \(B ⊆ A\). Tensor is pointwise sum, \(D_0A = \{0\}\), \(D_1A = A\), and \(D_ωA\) is the submonoid generated by \(A\).
- It is a graded comonad with weakening, contraction and the lax monoidal maps (`resExp`), and it has the colax structure for equation (1) (`resColax`).
- `res_no_split_many`: for the independent resources \(a = (1,0)\) and \(b = (0,1)\), there is no morphism \(D_t(a⊗b) \to D_ωa ⊗ D_ωb\) for any grade \(t\).
- `res_colax_exactly_eq1`: the model has a colax structure for equation (1), but none for any `⋉` in which \(ω ⋉ ω\) is defined, whatever its value. In particular it is not a model of GrCore's `[PPROD]` (`res_not_grcore_colax`).
- `adjusted_colax_strictly_more_models`: every model of GrCore's `[PPROD]` is also a model of the adjusted rule, but not the other way round.

**What is still not covered**
- The structures require the laws listed above, but not every coherence law between their parts (for example, between approximation and comultiplication).

`FORMALIZATION_STATUS.md` has been updated to match. The Properties table has one new definition (`HSupColax`) and three new proved properties (`res_colax_exactly_eq1`, `adjusted_colax_strictly_more_models`, `diag_colax_push`).

# Summary of changes for run 9481bb5d-a41e-46c9-a35e-0573342937d7
I formalized Section 3's comparisons with Linear Haskell, Idris 2, QTT and Λ^p. QTT is now a variant of GrCore, and Λ^p is a new calculus with its own terms and typing rules. The full project builds with no errors, no warnings and no `sorry`, and the new theorems use only the standard axioms.

There are four new files in `RequestProject/Sec3_DissectingTheProblem/`, and the section's index file and `FORMALIZATION_STATUS.md` are updated to match.

**QTT (`QTT.lean`)**
- **The variant:** `QTTTyped` is GrCore with the `[PPROD]` rule switched off, so a pair can never be taken apart underneath a box. Everything else, including pattern matching on unboxed pairs, is unchanged. The paper's simplified QTT tensor rule and QTT's graded-pair rule \((x^\pi : S) \otimes T\) (read as \(\square_\pi S \otimes T\)) both hold in it (`QTTTyped.letPair`, `QTTTyped.letGradedPair`).
- **No pairs under a box:** `qtt_no_pair_under_box` shows a product pattern cannot be typed underneath a box.
- **`push` is ill-typed:** `qtt_push_ill_typed` shows that, over any semiring, the term `push` has no type at all.
- **QTT is a fragment of the earlier calculi:** every QTT derivation is also a derivation in GrCore and in the adjusted calculus, for any `hsup` (`qttTyped_to_grcore`, `qttTyped_to_adjTyped`).
- **No term of the `push` type:** `qtt_push_many_not_derivable` shows that, over \(\{0,1,\omega\}\), no closed term has type \(\square_\omega(\alpha\otimes\beta) \multimap \square_\omega\alpha\otimes\square_\omega\beta\).
- **Conservative over linear logic:** `qtt_conservative_over_imell` shows every QTT judgement translates, using Theorem 1, into a derivable IMELL judgement.

**Linear Haskell (`LinearHaskell.lean`)**
- `Box r a` is modelled as \(\square_r a\), with `'One` = 1 and `'Many` = ω.
- `linearHaskell_push`: `push` type-checks at both multiplicities.
- `linearHaskell_unrestricted_not_bang`: at `Unrestricted`, `push` type-checks, but the translated type \(!(\alpha\otimes\beta) \multimap\, !\alpha \otimes !\beta\) cannot be derived in linear logic. So `Unrestricted a` is not `!a`.

**Idris 2 (`Idris2.lean`)**
- `Unrestricted a` is modelled as \(\square_\omega a\).
- `idris2_push` and `idris2_unrestricted_not_bang` are the analogues of the Linear Haskell results.
- `idris2_vs_qtt`: Idris 2 accepts `push`, while QTT, which Idris 2 is based on, does not.

**Λ^p (`LambdaP.lean`)**
- **The calculus:** `LamP.LTerm R n` uses de Bruijn indices, so `LTerm R 0` is the closed terms. Eliminators carry a grade, as in `let (x, y) =^q t in u`. The typing judgement `LamP.LTyped` uses grade-vector contexts, and its product rule gives \((q\gamma+\delta)\Gamma\) in the conclusion.
- **`push`:** `lamP_push` shows Λ^p admits `push` at every grade, over every semiring.
- **Relation to QTT:** `LTyped.letPair_one` shows the q = 1 case of the Λ^p rule is the simplified QTT rule.
- **Relation to GrCore:** `grcore_lamP_letPair` shows the Λ^p rule can be derived in GrCore as `let [(x, y)] = [t] in u`. This makes precise the paper's remark that it is "akin to the elimination behaviour underneath a graded modality in GrCore".
- **Comparison:** `lamP_vs_qtt` shows that over \(\{0,1,\omega\}\), Λ^p derives `push` at ω, while QTT and IMELL do not.

**Limits of what is modelled**
- Linear Haskell and Idris 2 are covered only through their `Box`/`Unrestricted` data types and nested pattern matching.
- QTT's type dependency is not modelled.
- Λ^p includes only linear functions, not graded functions \(q\,A \to B\).
- There is no full translation of Λ^p into GrCore; only its product rule is shown to be derivable.
- The paper's remark about Λ^p's models (that they include the one showing every linear term is a permutation) is not formalized.
- **Section order:** the four new files use the \(\{0,1,\omega\}\) semiring, IMELL, the counting model and Theorem 1 from Section 4. This is a forward reference, like the one Section 1 already makes, and is noted in the section's index file.

The Properties table has two new definitions (the QTT variant and the Λ^p calculus) and eight new properties, all proved.

# Summary of changes for run da1f2aab-d633-44a4-bad9-e1904ee00d28
I reorganised the Lean files by paper section, fixed the Typst source, added one result from Section 4 that hadn't been formalized, and listed what is still missing. The project builds with no `sorry`, and the new theorem uses only the standard axioms.

**1. Folder layout (one folder per section)**
The folders are now `RequestProject/Sec1_Introduction/`, `Sec2_CoreCalculus/`, `Sec3_DissectingTheProblem/`, `Sec4_Solution/`, `Sec5_ImplementationInGranule/` and `Sec6_Conclusions/`. The number prefix gives the reading order.
- Each folder has an index file next to it (for example `RequestProject/Sec4_Solution.lean`) that imports that section's files in reading order and describes each one.
- A new root file, `RequestProject.lean`, imports all six sections. I added it to the `globs` in `lakefile.toml` so the default build compiles it.
- Sections 2–6 only import earlier sections. Section 1 is the one exception: like the paper's introduction, it states results that are defined later (GrCore in Section 2, `push` in Section 3, IMELL in Section 4). Read it first for the statements, then again after Section 4 for the proofs.

**2. Is the `.typ` file correct?**
It now compiles with Typst 0.15 with no warnings. The two fixes from the earlier run (Theorem 1's translation and equation (1)) are still correct. Comparing it page by page against the original PDF turned up more problems, which I fixed:
- **Equation (1)** was rendered inline, in small type, with no "(1)". It is now a numbered display equation.
- **QTT rule:** `U[(x,y)/z]` and `U[M/z]` were typeset as fractions. The slash is now escaped.
- **(APPROX):** the term's type was written `A`, the same letter as the type of `x`, which forces the two to be equal. The original paper has the same slip. I changed it to `B`, which matches the Lean rule.
- **Code blocks** could split across pages, leaving the label ("Granule", "Idris 2") alone on the next page. They now stay on one page.
- **Two small changes:** the colax map's name is `n_{r,s,A,B}` again, as in the original, and I removed a stray space in "Theorem 1 (…) .".

**3. New result**
Section 4 says that taking `hsup` to be the partial least upper bound "recovers the existing pattern matching typing". Previously only the exact-usage (discrete) case was covered. It is now proved in general in `RequestProject/Sec4_Solution/HsupLub.lean`:
- `adjTyped_lub_iff_grcore`: if `hsup` is the partial least upper bound of a partially ordered semiring, the adjusted calculus derives exactly the same judgements as Section 2's GrCore. It needs a partial order, not just a preorder, so that the least upper bound of `r` and `r` is `r` itself.
- `isPartialLub_diagHsup`: for an exact-usage (discrete) order, `hsup` is defined only when `r = s`.

**4. What is still missing**
Full details are in `FORMALIZATION_STATUS.md`.
- **Section 3:** the comparisons with Linear Haskell, Idris 2, QTT and Λ^p. The paper states these only informally; the QTT and Λ^p rules could be added as variants of the calculus.
- **Section 4:** the coeffect / colax-monoidality remark, which would need a categorical semantics.
- **Semantics for GrCore:** there is none in general (the paper doesn't claim one). The only model is the resource-counting one used to prove that some types have no derivation.
- **Section 5:** Granule's data types (ADTs/GADTs) and its SMT-based constraint solving are not modelled.
- **Theorem 1:** the GrCore → IMELL direction is proved in the paper's form ("there exists a term M"), but the term translation is not written out as a function.
- **Atomic types:** both calculi still have them added. Without them every type has a closed term, and the statements that something cannot be derived become trivial.

The Properties table has the new file paths and a new proved entry for the least-upper-bound result.

# Summary of changes for run a4956e45-9086-43b2-bc45-896bb2cd8d9c
The Lean project already built with no errors and no `sorry`, so I took "fix it" to mean the errors in the paper. I fixed two of them in the project's copy of the paper source, `Linear Exponentials as Graded Modal Types.typ`. I did not touch the PDF, because no Typst compiler was available to regenerate it.

1. **Theorem 1's translation (Section 4).** The paper said the GrCore → IMELL translation sends both \(\square_0 A\) and \(\square_\omega A\) to \(!⟦A⟧\). That makes the theorem false. The text now maps \(\square_\omega A\) to \(!⟦A⟧\), \(\square_1 A\) to \(⟦A⟧\), and \(\square_0 A\) to the unit type \(1\), with the same rule for graded assumptions (e.g. \(x : [A]_0\) becomes \(x : 1\)). It also includes the counterexample showing why \(\square_0 A\) can't go to \(!⟦A⟧\): the term \(\lambda z.\ \mathsf{let}\ [y] = z\ \mathsf{in}\ (y,[y])\) has type \(\square_1 \alpha \multimap \alpha \otimes \square_0 \alpha\) in the adjusted calculus, but \(\alpha \multimap \alpha \otimes !\alpha\) is not provable in IMELL. The fixed text now matches the Lean results:
   - the corrected Theorem 1 (`theorem1`, in `RequestProject/Solution/Theorem1/Theorem1.lean`) is proved with this translation;
   - the original translation is formally refuted (`theorem1_grcore_to_imell_as_stated_false`, in `RequestProject/Solution/Theorem1/AsStated.lean`).

2. **Equation (1).** The `.typ` source left out the result in the first case of the definition of \(r \sqcup s\). It now reads \(1\) when \(r = s = 1\), and undefined otherwise. This matches the original PDF and the Lean definition `hsup`.

The only Lean change is a doc comment in `RequestProject/Solution/Theorem1/Translations.lean` noting that the paper source now states the corrected translation. The full project still builds with no errors and no `sorry`. I updated the notes on the two Theorem 1 entries in the Properties table to match. The refutation entry still links to the original line of the translation in the uploaded paper, since the table checks links against the files you uploaded.

# Summary of changes for run f9683a90-7f3b-47e1-a90f-96ac54e18a59
I formalized "Linear Exponentials as Graded Modal Types" in Lean 4 under the `LinExp` namespace. The project builds with no errors, no warnings and no `sorry`, and uses only the standard axioms. One result in the paper is wrong: the GrCore → IMELL direction of Theorem 1, using the translation the paper gives, is false once types include atoms. I proved that, then proved a corrected version.

**Design choices you asked for**
- Terms use de Bruijn indices and are indexed by the number of free variables: `Term n`, so `Term 0` means a closed term. Patterns are `Pat k`, and contexts are `Fin n → Option _`.
- `[grcore| ... ]` notation is available for writing GrCore terms.
- The folders under `RequestProject/` follow the paper's sections: `CoreCalculus/` (syntax, typing, renaming, notation), `Introduction/`, `DissectingTheProblem/`, `Solution/` (the adjusted calculus, the none-one-tons semiring, IMELL, a semantic model and Theorem 1), `ImplementationInGranule/` and `Conclusions/`.

**What is proved**
- **Introduction:** `gr_pull` and `gr_push` (GrCore can derive both `pull` and `push` for □), and `ll_pull` (IMELL can derive `pull_!`). `ll_push_not_derivable` shows IMELL cannot derive `push_!`, using two distinct atoms.
- **Section 3:** `grcore_push` – in GrCore, `push` is derivable at every grade.
- **Section 4:**
  - In the adjusted calculus over `{0, 1, ω}`, `push` at grade `ω` has no closed term (`adj_push_many_not_derivable`), but it is still derivable at grade `1` (`adj_push_one`).
  - The defined-`⊔` side condition (`HSup`) is stated generally, and the paper's equation (1) is formalized for none-one-tons.
- **Theorem 1, corrected (`theorem1`):** both directions are proved. The IMELL → GrCore direction uses an explicit translation of terms.
- **Section 5:** `granule_push_many_ill_typed` (the Granule `push` at type `[Many]` no longer typechecks) and `granule_push_many_typed_before` (it did typecheck before the adjustment).
- **Section 6:** `both_push_and_bang` puts the main claims together in one statement.

**The problem with Theorem 1**
The paper translates both `□_0 A` and `□_ω A` to `!⟦A⟧`. `theorem1_grcore_to_imell_as_stated_false` shows this fails:
- The term `λz. let [y] = z in (y,[y])` has type `□_1 α ⊸ α ⊗ □_0 α` in the adjusted calculus.
- Its translation, `α ⊸ α ⊗ !α`, cannot be derived in IMELL. I showed this with a semantic model.

Translating `□_0 A` to the unit type `I` instead makes the theorem true, and that is the version I proved (`theorem1_grcore_to_imell`, used in `theorem1`).

**Assumption to be aware of:** I added atomic types to both GrCore and IMELL. Without atoms every type has a closed inhabitant, so the statements about underivability become trivial.

**Not formalized:** the informal comparisons in Section 3 (Haskell, Idris 2, QTT, Λ^p).

The main results, including the refutation of Theorem 1 as stated, are listed in the Properties table, each linked to its line in the paper's `.typ` source.

## Suggested follow-up

The paper's Theorem 1 (GrCore → IMELL) is wrong as written: translating `□_0 A` to `!⟦A⟧` breaks it, and translating `□_0 A` to the unit type `I` fixes it. The Lean files have both the counterexample and the corrected proof. I can write a short note for the authors explaining the problem and the fix if that would help.