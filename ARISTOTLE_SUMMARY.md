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