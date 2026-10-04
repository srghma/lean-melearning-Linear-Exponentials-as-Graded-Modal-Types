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