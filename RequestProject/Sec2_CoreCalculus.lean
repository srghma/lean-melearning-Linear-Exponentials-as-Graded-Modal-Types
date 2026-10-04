module

public import RequestProject.Sec2_CoreCalculus.Context
public import RequestProject.Sec2_CoreCalculus.Syntax
public import RequestProject.Sec2_CoreCalculus.Notation
public import RequestProject.Sec2_CoreCalculus.Typing
public import RequestProject.Sec2_CoreCalculus.Renaming
public import RequestProject.Sec2_CoreCalculus.Derived
public import RequestProject.Sec2_CoreCalculus.Derivation

/-!
# Section 2: Core calculus (GrCore)

Reading order:

1. `Sec2_CoreCalculus/Context.lean` — contexts over de Bruijn indices (`Fin n → Option E`).
2. `Sec2_CoreCalculus/Syntax.lean` — types `Ty R`, patterns `Pat k`, terms `Term n`
   (`Term 0` is the type of closed terms).
3. `Sec2_CoreCalculus/Notation.lean` — the `[grcore| … ]` surface syntax with named variables.
4. `Sec2_CoreCalculus/Typing.lean` — context addition, pattern typing `?r ⊢ p : A ▷ Δ` and the
   typing rules `Γ ⊢ t : A` (VAR, ABS, APP, DER, WEAK, APPROX, PR, UNIT, PROD, LET).
5. `Sec2_CoreCalculus/Renaming.lean` — renaming (exchange, weakening by unused variables).
6. `Sec2_CoreCalculus/Derived.lean` — small derived rules used to build derivations.
7. `Sec2_CoreCalculus/Derivation.lean` — typing derivations as data (`Derivation`), with
   `Typed hs Γ t A ↔ Nonempty (Derivation hs Γ t A)`; used to define translations by
   induction on derivations.
-/
