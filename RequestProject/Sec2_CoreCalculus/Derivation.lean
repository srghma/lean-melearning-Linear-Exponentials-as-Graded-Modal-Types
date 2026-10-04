module

public import RequestProject.Sec2_CoreCalculus.Typing

/-!
# Section 2: typing derivations as data

`Typed hs Γ t A` is a proposition, so a function cannot inspect *how* a judgement was
derived.  Translations defined by induction on typing derivations (such as the GrCore → IMELL
translation of Theorem 1) are therefore defined on `Derivation hs Γ t A`, the type of typing
derivations: it has exactly the same rules as `Typed`, but lives in `Type`.

`Typed hs Γ t A ↔ Nonempty (Derivation hs Γ t A)` (`typed_iff_nonempty_derivation`).
-/

@[expose] public section

namespace LinExp

variable {R : Type} [Semiring R] [Preorder R]

/-- Typing derivations of GrCore (the rules of `Typed`, as data). -/
inductive Derivation (hs : R → R → Option R) : {n : ℕ} → GCtx R n → Term n → Ty R → Type
  | var {n : ℕ} {Γ : GCtx R n} {i : Fin n} {A : Ty R} :
      Γ i = some (.lin A) → (∀ j, j ≠ i → Γ j = none) → Derivation hs Γ (.var i) A
  | lam {n : ℕ} {Γ : GCtx R n} {t : Term (n + 1)} {A B : Ty R} :
      Derivation hs (Ctx.cons (some (.lin A)) Γ) t B → Derivation hs Γ (.lam t) (A ⊸ B)
  | app {n : ℕ} (Γ₁ Γ₂ : GCtx R n) {Γ : GCtx R n} {t₁ t₂ : Term n} (A : Ty R) {B : Ty R} :
      Derivation hs Γ₁ t₁ (A ⊸ B) → Derivation hs Γ₂ t₂ A → CtxAdd Γ₁ Γ₂ Γ →
      Derivation hs Γ (.app t₁ t₂) B
  | der {n : ℕ} {Γ : GCtx R n} {t : Term n} {A B : Ty R} {i : Fin n} :
      Derivation hs Γ t B → Γ i = some (.lin A) →
      Derivation hs (Function.update Γ i (some (.grad A 1))) t B
  | weak {n : ℕ} (Γ Δ : GCtx R n) {Γ' : GCtx R n} {t : Term n} {A : Ty R} :
      Derivation hs Γ t A → IsZeroCtx Δ → CtxAdd Γ Δ Γ' → Derivation hs Γ' t A
  | approx {n : ℕ} {Γ : GCtx R n} {t : Term n} {A B : Ty R} (i : Fin n) (r s : R) :
      Derivation hs Γ t B → Γ i = some (.grad A r) → r ≤ s →
      Derivation hs (Function.update Γ i (some (.grad A s))) t B
  | pr {n : ℕ} (Γ : GCtx R n) {t : Term n} {A : Ty R} (r : R) :
      Derivation hs Γ t A → IsGraded Γ → Derivation hs (scale r Γ) (.box t) (□[r] A)
  | unit {n : ℕ} {Γ : GCtx R n} : (∀ i, Γ i = none) → Derivation hs Γ .unit .unit
  | pair {n : ℕ} (Γ₁ Γ₂ : GCtx R n) {Γ : GCtx R n} {t₁ t₂ : Term n} {A B : Ty R} :
      Derivation hs Γ₁ t₁ A → Derivation hs Γ₂ t₂ B → CtxAdd Γ₁ Γ₂ Γ →
      Derivation hs Γ (.pair t₁ t₂) (A ⊗ B)
  | letPat {n k : ℕ} (Γ₁ Γ₂ : GCtx R n) {Γ : GCtx R n} {Δ : GCtx R k} (p : Pat k)
      {t₁ : Term n} {t₂ : Term (n + k)} (A : Ty R) {B : Ty R} :
      Derivation hs Γ₁ t₁ A → PatTy hs none p A Δ → Derivation hs (Ctx.append Γ₂ Δ) t₂ B →
      CtxAdd Γ₁ Γ₂ Γ → Derivation hs Γ (.letPat p t₁ t₂) B

/-- Every derivation proves its judgement. -/
theorem Derivation.typed {hs : R → R → Option R} {n : ℕ} {Γ : GCtx R n} {t : Term n}
    {A : Ty R} (d : Derivation hs Γ t A) : Typed hs Γ t A := by
  induction d with
  | var h1 h2 => exact Typed.var h1 h2
  | lam _ ih => exact Typed.lam ih
  | app _ _ _ _ _ h ih1 ih2 => exact Typed.app ih1 ih2 h
  | der _ h ih => exact Typed.der ih h
  | weak _ _ _ h1 h2 ih => exact Typed.weak ih h1 h2
  | approx _ _ _ _ h1 h2 ih => exact Typed.approx ih h1 h2
  | pr _ r _ h ih => exact Typed.pr r ih h
  | unit h => exact Typed.unit h
  | pair _ _ _ _ h ih1 ih2 => exact Typed.pair ih1 ih2 h
  | letPat _ _ _ _ _ hp _ h ih1 ih2 => exact Typed.letPat ih1 hp ih2 h

/-- Every derivable judgement has a derivation. -/
theorem Typed.nonempty_derivation {hs : R → R → Option R} {n : ℕ} {Γ : GCtx R n}
    {t : Term n} {A : Ty R} (h : Typed hs Γ t A) : Nonempty (Derivation hs Γ t A) := by
  induction h with
  | var h1 h2 => exact ⟨Derivation.var h1 h2⟩
  | lam _ ih => exact ⟨Derivation.lam ih.some⟩
  | app _ _ h ih1 ih2 => exact ⟨Derivation.app _ _ _ ih1.some ih2.some h⟩
  | der _ h ih => exact ⟨Derivation.der ih.some h⟩
  | weak _ h1 h2 ih => exact ⟨Derivation.weak _ _ ih.some h1 h2⟩
  | approx _ h1 h2 ih => exact ⟨Derivation.approx _ _ _ ih.some h1 h2⟩
  | pr r _ h ih => exact ⟨Derivation.pr _ r ih.some h⟩
  | unit h => exact ⟨Derivation.unit h⟩
  | pair _ _ h ih1 ih2 => exact ⟨Derivation.pair _ _ ih1.some ih2.some h⟩
  | letPat _ hp _ h ih1 ih2 => exact ⟨Derivation.letPat _ _ _ _ ih1.some hp ih2.some h⟩

theorem typed_iff_nonempty_derivation {hs : R → R → Option R} {n : ℕ} {Γ : GCtx R n}
    {t : Term n} {A : Ty R} : Typed hs Γ t A ↔ Nonempty (Derivation hs Γ t A) :=
  ⟨Typed.nonempty_derivation, fun ⟨d⟩ => d.typed⟩

end LinExp

end
