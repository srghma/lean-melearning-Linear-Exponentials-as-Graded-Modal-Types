module

public import RequestProject.Sec2_CoreCalculus.Typing
public import RequestProject.Sec4_Solution.Coeffect.GradedComonad

/-!
# Section 4: categorical models of GrCore (and of the adjusted calculus)

The paper does not give a semantics for GrCore.  Here we give one, in the standard style of
graded modal type theory: a GrCore type is interpreted as an object of a symmetric monoidal
closed category, the modality `□_r` as an `R`-graded exponential comonad `D_r`
(`GradedExponential`, see `Sec4_Solution/Coeffect/GradedComonad.lean`), and the pattern rule
`[PPROD]` by the partial colax monoidal structure indexed by `⋉` (`HSupColax hs`).

A **model of `Typed hs`** (`CatModel R hs C`) consists of

* a symmetric monoidal closed category `C` (`A ⊗ B`, `I`, `A ⊸ B = ihom A B`);
* a graded exponential comonad `E` on `C` (`D_r`, counit, comultiplication, approximation,
  weakening, contraction and lax monoidal maps);
* a partial colax monoidal structure `N : HSupColax hs E` (maps `D_{r ⋉ s}(A ⊗ B) ⟶ D_r A ⊗ D_s B`);
* a map `D_r I ⟶ I` for every `r` (needed for the unit pattern `r ⊢ unit : 1 ▷ ∅` under a box);
* an interpretation of the atomic types.

This file defines the interpretation of types, assumptions and contexts, and the morphisms
that interpret the structural operations on contexts (context addition, weakening, promotion,
appending pattern contexts, …).  The interpretation of derivations is in `Interp.lean`.
-/

@[expose] public section

namespace LinExp

namespace Sem

open CategoryTheory MonoidalCategory MonoidalClosed

universe v u

/-- A categorical model of the GrCore typing judgement `Typed hs` over the semiring `R`. -/
structure CatModel (R : Type) [Semiring R] [Preorder R] (hs : R → R → Option R)
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] where
  /-- The graded exponential comonad interpreting `□_r`. -/
  E : Coeffect.GradedExponential R C
  /-- The partial colax monoidal structure interpreting `[PPROD]`. -/
  N : Coeffect.HSupColax hs E.toGradedComonad
  /-- Discarding a boxed unit, `D_r I ⟶ I` (interprets `r ⊢ unit : 1 ▷ ∅`). -/
  unitDisc : ∀ r : R, (E.D r).obj (𝟙_ C) ⟶ 𝟙_ C
  /-- Interpretation of the atomic types. -/
  atom : ℕ → C

variable {R : Type} [Semiring R] [Preorder R] {hs : R → R → Option R}
  {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]

namespace CatModel

variable (M : CatModel R hs C)

/-- `⟦A⟧`: interpretation of types. -/
def tyObj : Ty R → C
  | .atom i => M.atom i
  | .unit => 𝟙_ C
  | .lolli A B => (ihom (tyObj A)).obj (tyObj B)
  | .tensor A B => tyObj A ⊗ tyObj B
  | .box r A => (M.E.D r).obj (tyObj A)

/-- Interpretation of an (optional) assumption: `⟦·⟧ = I`, `⟦x : A⟧ = ⟦A⟧`,
`⟦x : [A]_r⟧ = D_r ⟦A⟧`. -/
def entryObj : Option (Assm R) → C
  | none => 𝟙_ C
  | some (.lin A) => M.tyObj A
  | some (.grad A r) => (M.E.D r).obj (M.tyObj A)

/-- `⟦Γ⟧`: interpretation of a context over `n` de Bruijn indices,
`⟦Γ⟧ = (…(I ⊗ ⟦Γ (n-1)⟧) ⊗ …) ⊗ ⟦Γ 0⟧` (the innermost variable is rightmost). -/
def ctxObj : {n : ℕ} → GCtx R n → C
  | 0, _ => 𝟙_ C
  | _ + 1, Γ => ctxObj (fun i => Γ i.succ) ⊗ M.entryObj (Γ 0)

@[simp] lemma ctxObj_zero (Γ : GCtx R 0) : M.ctxObj Γ = 𝟙_ C := rfl

lemma ctxObj_succ {n : ℕ} (Γ : GCtx R (n + 1)) :
    M.ctxObj Γ = M.ctxObj (fun i => Γ i.succ) ⊗ M.entryObj (Γ 0) := rfl

/-- Transport along an equality of contexts. -/
def ctxCast {n : ℕ} {Γ Γ' : GCtx R n} (h : Γ = Γ') : M.ctxObj Γ ⟶ M.ctxObj Γ' :=
  eqToHom (by rw [h])

/-- Transport along an equality of assumptions. -/
def entryCast {e e' : Option (Assm R)} (h : e = e') : M.entryObj e ⟶ M.entryObj e' :=
  eqToHom (by rw [h])

/-- Pointwise maps of assumptions give a map of contexts. -/
def ctxMap : {n : ℕ} → {Γ Γ' : GCtx R n} → (∀ i, M.entryObj (Γ i) ⟶ M.entryObj (Γ' i)) →
    (M.ctxObj Γ ⟶ M.ctxObj Γ')
  | 0, _, _, _ => 𝟙 _
  | _ + 1, _, _, f => ctxMap (fun i => f i.succ) ⊗ₘ f 0

/-- A context with no assumptions is interpreted as (a map to) the unit. -/
def ctxNone : {n : ℕ} → (Γ : GCtx R n) → (∀ i, Γ i = none) → (M.ctxObj Γ ⟶ 𝟙_ C)
  | 0, _, _ => 𝟙 _
  | _ + 1, Γ, h =>
    (ctxNone (fun i => Γ i.succ) (fun i => h i.succ) ⊗ₘ M.entryCast (h 0)) ≫ (λ_ _).hom

/-- A context whose only assumption is at position `i` is interpreted as that assumption. -/
def ctxSingle : {n : ℕ} → (Γ : GCtx R n) → (i : Fin n) → (∀ j, j ≠ i → Γ j = none) →
    (M.ctxObj Γ ⟶ M.entryObj (Γ i))
  | 0, _, i, _ => Fin.elim0 i
  | _ + 1, Γ, i, h =>
    Fin.cases
      (motive := fun i => (∀ j, j ≠ i → Γ j = none) → (M.ctxObj Γ ⟶ M.entryObj (Γ i)))
      (fun h => (M.ctxNone (fun j => Γ j.succ) (fun j => h j.succ (Fin.succ_ne_zero j)) ▷ _) ≫
        (λ_ _).hom)
      (fun i' h => (ctxSingle (fun j => Γ j.succ) i'
          (fun j hj => h j.succ (fun e => hj (Fin.succ_injective _ e))) ▷ _) ≫
        (_ ◁ M.entryCast (h 0 (Fin.succ_ne_zero i').symm)) ≫ (ρ_ _).hom)
      i h

/-- Splitting maps of assumptions give a splitting map of contexts:
`⟦Γ⟧ ⟶ ⟦Γ₁⟧ ⊗ ⟦Γ₂⟧` (uses the symmetry to interleave). -/
def ctxSplit : {n : ℕ} → {Γ Γ₁ Γ₂ : GCtx R n} →
    (∀ i, M.entryObj (Γ i) ⟶ M.entryObj (Γ₁ i) ⊗ M.entryObj (Γ₂ i)) →
    (M.ctxObj Γ ⟶ M.ctxObj Γ₁ ⊗ M.ctxObj Γ₂)
  | 0, _, _, _, _ => (λ_ _).inv
  | _ + 1, _, _, _, f => (ctxSplit (fun i => f i.succ) ⊗ₘ f 0) ≫ tensorμ _ _ _ _

/-- The interpretation of an entry-wise addition `e₁ + e₂ = e`: `⟦e⟧ ⟶ ⟦e₁⟧ ⊗ ⟦e₂⟧`
(a unitor, or contraction `D_{r+s} A ⟶ D_r A ⊗ D_s A`). -/
def entrySplit : (e₁ e₂ e : Option (Assm R)) → EntryAdd e₁ e₂ e →
    (M.entryObj e ⟶ M.entryObj e₁ ⊗ M.entryObj e₂)
  | none, e₂, e, h => M.entryCast (by cases h; rfl) ≫ (λ_ _).inv
  | some a, none, e, h => M.entryCast (by cases h; rfl) ≫ (ρ_ _).inv
  | some (.grad A r), some (.grad B s), e, h =>
    M.entryCast (e' := some (.grad A (r + s))) (by cases h; rfl) ≫
      M.E.contr r s (M.tyObj A) ≫ (_ ◁ M.entryCast (e := some (.grad A s))
        (e' := some (.grad B s)) (by cases h; rfl))
  | some (.lin _), some _, _, h => False.elim (by cases h)
  | some (.grad _ _), some (.lin _), _, h => False.elim (by cases h)

/-- Interpretation of context addition `Γ₁ + Γ₂ = Γ`: a map `⟦Γ⟧ ⟶ ⟦Γ₁⟧ ⊗ ⟦Γ₂⟧`. -/
def addMap {n : ℕ} {Γ₁ Γ₂ Γ : GCtx R n} (h : CtxAdd Γ₁ Γ₂ Γ) :
    M.ctxObj Γ ⟶ M.ctxObj Γ₁ ⊗ M.ctxObj Γ₂ :=
  M.ctxSplit (fun i => M.entrySplit _ _ _ (h i))

/-- Discarding a `0`-graded assumption. -/
def entryDiscard : (e : Option (Assm R)) → (e = none ∨ ∃ A, e = some (.grad A 0)) →
    (M.entryObj e ⟶ 𝟙_ C)
  | none, _ => 𝟙 _
  | some (.lin _), h => False.elim (by rcases h with h | ⟨_, h⟩ <;> cases h)
  | some (.grad A r), h =>
    M.entryCast (e' := some (.grad A 0)) (by rcases h with h | ⟨_, h⟩ <;> cases h; rfl) ≫
      M.E.weak (M.tyObj A)

/-- Interpretation of weakening: a `[Δ]_0` context maps to the unit. -/
def ctxDiscard {n : ℕ} (Δ : GCtx R n) (h : IsZeroCtx Δ) : M.ctxObj Δ ⟶ 𝟙_ C :=
  M.ctxMap (Γ' := Ctx.empty n) (fun i => M.entryDiscard (Δ i) (h i)) ≫
    M.ctxNone (Ctx.empty n) (fun _ => rfl)

/-- A map out of an updated context, from a map of the updated entry. -/
def updateMap {n : ℕ} (Γ : GCtx R n) (i : Fin n) (e : Option (Assm R))
    (g : M.entryObj e ⟶ M.entryObj (Γ i)) :
    M.ctxObj (Function.update Γ i e) ⟶ M.ctxObj Γ :=
  M.ctxMap (fun j => if h : j = i then
      M.entryCast (by subst h; simp) ≫ g ≫ M.entryCast (by subst h; rfl)
    else M.entryCast (by simp [h]))

/-- Promotion of a single graded assumption: `D_{r*s} A ⟶ D_r (D_s A)` (comultiplication),
or the lax unit `I ⟶ D_r I`. -/
def entryPromote (r : R) : (e : Option (Assm R)) → (∀ A, e ≠ some (.lin A)) →
    (M.entryObj (e.map (Assm.scale r)) ⟶ (M.E.D r).obj (M.entryObj e))
  | none, _ => M.E.laxUnit r
  | some (.lin A), h => False.elim (h A rfl)
  | some (.grad A s), _ => (M.E.comult r s).app (M.tyObj A)

/-- Interpretation of the context part of promotion: `⟦r * [Γ]⟧ ⟶ D_r ⟦[Γ]⟧`. -/
def ctxPromote (r : R) : {n : ℕ} → (Γ : GCtx R n) → IsGraded Γ →
    (M.ctxObj (scale r Γ) ⟶ (M.E.D r).obj (M.ctxObj Γ))
  | 0, _, _ => M.E.laxUnit r
  | _ + 1, Γ, h =>
    (ctxPromote r (fun i => Γ i.succ) (fun i A => h i.succ A) ⊗ₘ
      M.entryPromote r (Γ 0) (fun A => h 0 A)) ≫ M.E.lax r _ _

/-- `⟦Γ, Δ⟧ ≅ ⟦Γ⟧ ⊗ ⟦Δ⟧`. -/
def appendIso {n : ℕ} (Γ : GCtx R n) : {k : ℕ} → (Δ : GCtx R k) →
    (M.ctxObj (Ctx.append Γ Δ) ≅ M.ctxObj Γ ⊗ M.ctxObj Δ)
  | 0, Δ => eqToIso (by rw [Ctx.append_zero]) ≪≫ (ρ_ _).symm
  | _ + 1, Δ => eqToIso (by rw [Ctx.append_succ]; rfl) ≪≫
      whiskerRightIso (appendIso Γ (fun j => Δ j.succ)) _ ≪≫ α_ _ _ _

/-- Interpretation of an optional grade `?r` acting on an object. -/
def optObj : Option R → C → C
  | none, X => X
  | some r, X => (M.E.D r).obj X

end CatModel

end Sem

end LinExp

end
