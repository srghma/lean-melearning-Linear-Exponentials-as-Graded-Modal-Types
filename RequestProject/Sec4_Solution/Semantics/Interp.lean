module

public import RequestProject.Sec4_Solution.Semantics.CatModel

/-!
# Section 4: interpretation of GrCore derivations in a categorical model

The typing judgement `Typed hs Γ t A` is a proposition, so a function on its proofs cannot
produce data.  We therefore introduce the type of **derivations** `Deriv hs Γ t A` (and
`PatDeriv` for pattern typing): it has exactly the same rules as `Typed` (resp. `PatTy`),
but lives in `Type`.  `Deriv` is inhabited exactly when `Typed` holds
(`typed_iff_nonempty_deriv`).

Given a model `M : CatModel R hs C`, every derivation `d : Deriv hs Γ t A` denotes a morphism
`M.interp d : ⟦Γ⟧ ⟶ ⟦A⟧`, and every pattern derivation `?r ⊢ p : A ▷ Δ` a morphism
`?r⟦A⟧ ⟶ ⟦Δ⟧`.  The clauses are the standard ones:

* `(VAR)`: projection out of a context with a single assumption; `(UNIT)`: discard `I`s;
* `(ABS)` / `(APP)`: currying and evaluation of the closed structure, after splitting the
  context with `⟦Γ⟧ ⟶ ⟦Γ₁⟧ ⊗ ⟦Γ₂⟧` (contraction on shared graded assumptions);
* `(DER)`: counit `D_1 A ⟶ A`; `(APPROX)`: `D_s A ⟶ D_r A` for `r ⊑ s`;
  `(WEAK)`: `D_0 A ⟶ I`;
* `(PR)`: `⟦r * [Γ]⟧ ⟶ D_r ⟦[Γ]⟧ ⟶ D_r ⟦A⟧` (comultiplication and lax monoidality, then
  functoriality of `D_r`);
* `(LET)`: interpret the matched term, then the pattern, then the body;
* patterns: `(PBOX)` is the identity on `D_r ⟦A⟧`, `[PPROD]` is the colax map
  `n_{r,s} : D_{r ⋉ s}(A ⊗ B) ⟶ D_r A ⊗ D_s B`, `(PUNIT)` under a box is `D_r I ⟶ I`.

**Soundness** (`CatModel.sound`): if `Γ ⊢ t : A` is derivable in `Typed hs`, then in every
model of `Typed hs` there is a morphism `⟦Γ⟧ ⟶ ⟦A⟧`.
-/

@[expose] public section

namespace LinExp

namespace Sem

open CategoryTheory MonoidalCategory MonoidalClosed

universe v u

variable {R : Type} [Semiring R] [Preorder R]

/-- Pattern derivations: the same rules as `PatTy`, valued in `Type`. -/
inductive PatDeriv (hs : R → R → Option R) :
    {k : ℕ} → Option R → Pat k → Ty R → GCtx R k → Type
  | var (A : Ty R) : PatDeriv hs none .var A (fun _ => some (.lin A))
  | pair {k₁ k₂ : ℕ} {p₁ : Pat k₁} {p₂ : Pat k₂} {A B : Ty R} {Δ₁ : GCtx R k₁}
      {Δ₂ : GCtx R k₂} :
      PatDeriv hs none p₁ A Δ₁ → PatDeriv hs none p₂ B Δ₂ →
      PatDeriv hs none (.pair p₁ p₂) (A ⊗ B) (Ctx.append Δ₁ Δ₂)
  | box {k : ℕ} {p : Pat k} {A : Ty R} {Δ : GCtx R k} (r : R) :
      PatDeriv hs (some r) p A Δ → PatDeriv hs none (.box p) (□[r] A) Δ
  | gvar (r : R) (A : Ty R) : PatDeriv hs (some r) .var A (fun _ => some (.grad A r))
  | gpair {k₁ k₂ : ℕ} {p₁ : Pat k₁} {p₂ : Pat k₂} {A B : Ty R} {Δ₁ : GCtx R k₁}
      {Δ₂ : GCtx R k₂} {r s t : R} :
      PatDeriv hs (some r) p₁ A Δ₁ → PatDeriv hs (some s) p₂ B Δ₂ → hs r s = some t →
      PatDeriv hs (some t) (.pair p₁ p₂) (A ⊗ B) (Ctx.append Δ₁ Δ₂)
  | unit (o : Option R) : PatDeriv hs o .unit .unit (Ctx.empty 0)

/-- Typing derivations: the same rules as `Typed`, valued in `Type`. -/
inductive Deriv (hs : R → R → Option R) : {n : ℕ} → GCtx R n → Term n → Ty R → Type
  | var {n : ℕ} {Γ : GCtx R n} {i : Fin n} {A : Ty R} :
      Γ i = some (.lin A) → (∀ j, j ≠ i → Γ j = none) → Deriv hs Γ (.var i) A
  | lam {n : ℕ} {Γ : GCtx R n} {t : Term (n + 1)} {A B : Ty R} :
      Deriv hs (Ctx.cons (some (.lin A)) Γ) t B → Deriv hs Γ (.lam t) (A ⊸ B)
  | app {n : ℕ} {Γ₁ Γ₂ Γ : GCtx R n} {t₁ t₂ : Term n} {A B : Ty R} :
      Deriv hs Γ₁ t₁ (A ⊸ B) → Deriv hs Γ₂ t₂ A → CtxAdd Γ₁ Γ₂ Γ → Deriv hs Γ (.app t₁ t₂) B
  | der {n : ℕ} {Γ : GCtx R n} {t : Term n} {A B : Ty R} {i : Fin n} :
      Deriv hs Γ t B → Γ i = some (.lin A) →
      Deriv hs (Function.update Γ i (some (.grad A 1))) t B
  | weak {n : ℕ} {Γ Δ Γ' : GCtx R n} {t : Term n} {A : Ty R} :
      Deriv hs Γ t A → IsZeroCtx Δ → CtxAdd Γ Δ Γ' → Deriv hs Γ' t A
  | approx {n : ℕ} {Γ : GCtx R n} {t : Term n} {A B : Ty R} {i : Fin n} {r s : R} :
      Deriv hs Γ t B → Γ i = some (.grad A r) → r ≤ s →
      Deriv hs (Function.update Γ i (some (.grad A s))) t B
  | pr {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R} (r : R) :
      Deriv hs Γ t A → IsGraded Γ → Deriv hs (scale r Γ) (.box t) (□[r] A)
  | unit {n : ℕ} {Γ : GCtx R n} : (∀ i, Γ i = none) → Deriv hs Γ .unit .unit
  | pair {n : ℕ} {Γ₁ Γ₂ Γ : GCtx R n} {t₁ t₂ : Term n} {A B : Ty R} :
      Deriv hs Γ₁ t₁ A → Deriv hs Γ₂ t₂ B → CtxAdd Γ₁ Γ₂ Γ → Deriv hs Γ (.pair t₁ t₂) (A ⊗ B)
  | letPat {n k : ℕ} {Γ₁ Γ₂ Γ : GCtx R n} {Δ : GCtx R k} {p : Pat k} {t₁ : Term n}
      {t₂ : Term (n + k)} {A B : Ty R} :
      Deriv hs Γ₁ t₁ A → PatDeriv hs none p A Δ → Deriv hs (Ctx.append Γ₂ Δ) t₂ B →
      CtxAdd Γ₁ Γ₂ Γ → Deriv hs Γ (.letPat p t₁ t₂) B

variable {hs : R → R → Option R}

omit [Semiring R] [Preorder R] in
lemma PatDeriv.patTy {k : ℕ} {o : Option R} {p : Pat k} {A : Ty R} {Δ : GCtx R k}
    (d : PatDeriv hs o p A Δ) : PatTy hs o p A Δ := by
  induction d with
  | var A => exact .var A
  | pair _ _ ih1 ih2 => exact .pair ih1 ih2
  | box r _ ih => exact .box r ih
  | gvar r A => exact .gvar r A
  | gpair _ _ h ih1 ih2 => exact .gpair ih1 ih2 h
  | unit o => exact .unit o

omit [Semiring R] [Preorder R] in
lemma _root_.LinExp.PatTy.nonempty_patDeriv {k : ℕ} {o : Option R} {p : Pat k} {A : Ty R} {Δ : GCtx R k}
    (h : PatTy hs o p A Δ) : Nonempty (PatDeriv hs o p A Δ) := by
  induction h with
  | var A => exact ⟨.var A⟩
  | pair _ _ ih1 ih2 => exact ⟨.pair ih1.some ih2.some⟩
  | box r _ ih => exact ⟨.box r ih.some⟩
  | gvar r A => exact ⟨.gvar r A⟩
  | gpair _ _ h ih1 ih2 => exact ⟨.gpair ih1.some ih2.some h⟩
  | unit o => exact ⟨.unit o⟩

lemma Deriv.typed {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R} (d : Deriv hs Γ t A) :
    Typed hs Γ t A := by
  induction d with
  | var h1 h2 => exact .var h1 h2
  | lam _ ih => exact .lam ih
  | app _ _ h ih1 ih2 => exact .app ih1 ih2 h
  | der _ h ih => exact .der ih h
  | weak _ h1 h2 ih => exact .weak ih h1 h2
  | approx _ h1 h2 ih => exact .approx ih h1 h2
  | pr r _ h ih => exact .pr r ih h
  | unit h => exact .unit h
  | pair _ _ h ih1 ih2 => exact .pair ih1 ih2 h
  | letPat _ p _ h ih1 ih2 => exact .letPat ih1 p.patTy ih2 h

lemma _root_.LinExp.Typed.nonempty_deriv {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R}
    (h : Typed hs Γ t A) : Nonempty (Deriv hs Γ t A) := by
  induction h with
  | var h1 h2 => exact ⟨.var h1 h2⟩
  | lam _ ih => exact ⟨.lam ih.some⟩
  | app _ _ h ih1 ih2 => exact ⟨.app ih1.some ih2.some h⟩
  | der _ h ih => exact ⟨.der ih.some h⟩
  | weak _ h1 h2 ih => exact ⟨.weak ih.some h1 h2⟩
  | approx _ h1 h2 ih => exact ⟨.approx ih.some h1 h2⟩
  | pr r _ h ih => exact ⟨.pr r ih.some h⟩
  | unit h => exact ⟨.unit h⟩
  | pair _ _ h ih1 ih2 => exact ⟨.pair ih1.some ih2.some h⟩
  | letPat _ p _ h ih1 ih2 => exact ⟨.letPat ih1.some p.nonempty_patDeriv.some ih2.some h⟩

/-- Derivability in `Typed` is exactly inhabitation of the type of derivations. -/
theorem typed_iff_nonempty_deriv {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R} :
    Typed hs Γ t A ↔ Nonempty (Deriv hs Γ t A) :=
  ⟨Typed.nonempty_deriv, fun ⟨d⟩ => d.typed⟩

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

namespace CatModel

variable (M : CatModel R hs C)

/-- Interpretation of pattern derivations: `?r ⊢ p : A ▷ Δ` denotes `?r⟦A⟧ ⟶ ⟦Δ⟧`. -/
def patInterp : {k : ℕ} → {o : Option R} → {p : Pat k} → {A : Ty R} → {Δ : GCtx R k} →
    PatDeriv hs o p A Δ → (M.optObj o (M.tyObj A) ⟶ M.ctxObj Δ)
  | _, _, _, _, _, .var _ => (λ_ _).inv
  | _, _, _, _, _, .pair d₁ d₂ =>
    (patInterp d₁ ⊗ₘ patInterp d₂) ≫ (M.appendIso _ _).inv
  | _, _, _, _, _, .box _ d => patInterp (o := some _) d
  | _, _, _, _, _, .gvar _ _ => (λ_ _).inv
  | _, _, _, _, _, .gpair d₁ d₂ h =>
    M.N.n h _ _ ≫ (patInterp d₁ ⊗ₘ patInterp d₂) ≫ (M.appendIso _ _).inv
  | _, _, _, _, _, .unit none => 𝟙 _
  | _, _, _, _, _, .unit (some r) => M.unitDisc r

/-- **The denotation of a derivation** `Γ ⊢ t : A` in the model: a morphism `⟦Γ⟧ ⟶ ⟦A⟧`. -/
def interp : {n : ℕ} → {Γ : GCtx R n} → {t : Term n} → {A : Ty R} →
    Deriv hs Γ t A → (M.ctxObj Γ ⟶ M.tyObj A)
  | _, Γ, _, _, .var (i := i) hi hj => M.ctxSingle Γ i hj ≫ M.entryCast hi
  | _, _, _, _, .lam d => curry ((β_ _ _).hom ≫ interp d)
  | _, _, _, _, .app d₁ d₂ h =>
    M.addMap h ≫ (interp d₁ ⊗ₘ interp d₂) ≫ (β_ _ _).hom ≫ (ihom.ev _).app _
  | _, _, _, _, .der (Γ := Γ) (A := A) (i := i) d hi =>
    M.updateMap Γ i _ (M.E.counit.app (M.tyObj A) ≫ M.entryCast hi.symm) ≫ interp d
  | _, _, _, _, .weak d hz h => M.addMap h ≫ (interp d ⊗ₘ M.ctxDiscard _ hz) ≫ (ρ_ _).hom
  | _, _, _, _, .approx (Γ := Γ) (A := A) (i := i) d hi hrs =>
    M.updateMap Γ i _ ((M.E.approx hrs).app (M.tyObj A) ≫ M.entryCast hi.symm) ≫ interp d
  | _, _, _, _, .pr r d hg => M.ctxPromote r _ hg ≫ (M.E.D r).map (interp d)
  | _, Γ, _, _, .unit h => M.ctxNone Γ h
  | _, _, _, _, .pair d₁ d₂ h => M.addMap h ≫ (interp d₁ ⊗ₘ interp d₂)
  | _, _, _, _, .letPat d₁ p d₂ h =>
    M.addMap h ≫ (interp d₁ ▷ _) ≫ (M.patInterp p ▷ _) ≫ (β_ _ _).hom ≫
      (M.appendIso _ _).inv ≫ interp d₂

/-- **Soundness of GrCore in categorical models.** If `Γ ⊢ t : A` is derivable in
`Typed hs`, then every model of `Typed hs` has a morphism `⟦Γ⟧ ⟶ ⟦A⟧`. -/
theorem sound {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R} (h : Typed hs Γ t A) :
    Nonempty (M.ctxObj Γ ⟶ M.tyObj A) :=
  ⟨M.interp h.nonempty_deriv.some⟩

/-- Closed terms denote global elements `I ⟶ ⟦A⟧`. -/
theorem sound_closed {t : Term 0} {A : Ty R} (h : Typed hs (Ctx.empty 0) t A) :
    Nonempty (𝟙_ C ⟶ M.tyObj A) :=
  M.sound h

/-- **Semantic non-derivability.** If some model of `Typed hs` has no global element of
`⟦A⟧`, then no closed term has type `A` in `Typed hs`. -/
theorem not_typed_of_isEmpty {A : Ty R} (hA : IsEmpty (𝟙_ C ⟶ M.tyObj A)) (t : Term 0) :
    ¬ Typed hs (Ctx.empty 0) t A :=
  fun h => hA.false (M.sound_closed h).some

end CatModel

end Sem

end LinExp

end
