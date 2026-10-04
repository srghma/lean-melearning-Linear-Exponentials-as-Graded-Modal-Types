module

public import Mathlib
public import RequestProject.Sec4_Solution.Hsup

/-!
# Section 4: the coeffect reading of `⋉` — graded comonads and partial colax monoidality

The paper remarks (end of Section 4):

> The operation `⋉` is inspired by the coeffect calculus of Petricek et al. whose graded type
> system includes `⋉` as an operation to control splitting of resources to subterms, modelled
> by colax monoidality of a graded comonad
> `n_{r,s,A,B} : D_{r ⋉ s}(A ⊗ B) → D_r A ⊗ D_s B`.

(In the Lean files the operation `⋉` is called `hsup`, see `Sec4_Solution/Hsup.lean`.)
This file gives the categorical vocabulary needed to state that remark:

* `GradedComonad R C` — an `R`-graded comonad `D : R → C ⥤ C` on a category `C`, for a
  pre-ordered monoid `R` of grades: a counit `D_1 ⟶ Id`, a comultiplication
  `D_{r*s} ⟶ D_r ∘ D_s`, and approximation maps `D_s ⟶ D_r` for `r ⊑ s` (the semantic
  counterpart of the rule `(APPROX)`), with the graded comonad laws.
* `GradedExponential R C` — the extra structure used to interpret graded contexts of GrCore in
  a monoidal category: weakening `D_0 A ⟶ I`, contraction `D_{r+s} A ⟶ D_r A ⊗ D_s A`, and the
  lax monoidal maps `I ⟶ D_r I`, `D_r A ⊗ D_r B ⟶ D_r (A ⊗ B)` used by promotion `(PR)`.
* `HSupColax hs G` — the remark itself: a *partial* colax monoidal structure on `G`, indexed by
  the partial operation `hs = ⋉` on grades. A map
  `n_{r,s,A,B} : D_t (A ⊗ B) ⟶ D_r A ⊗ D_s B` is required exactly when `r ⋉ s = t` is defined.
  This is the semantic content of the rule `[PPROD]`: matching a pair pattern underneath a box
  of grade `r ⋉ s` splits the boxed pair into a box of grade `r` and a box of grade `s`.

Only the laws listed in the docstrings are imposed; the results of this section do not need
further coherence conditions.
-/

@[expose] public section

namespace LinExp

namespace Coeffect

open CategoryTheory MonoidalCategory

universe v u

/-- An `R`-graded comonad on a category `C`, for a pre-ordered monoid `R` of grades.

* `D r` is the graded modality `D_r` (`□_r` in GrCore);
* `counit : D_1 ⟶ 𝟭` is dereliction (`(DER)`);
* `comult r s : D_{r*s} ⟶ D_r ∘ D_s` (written `D s ⋙ D r`) reassociates nested boxes;
* `approx h : D_s ⟶ D_r` for `r ⊑ s` interprets the rule `(APPROX)`.

The equations are the graded comonad laws (with `eqToHom` transporting along the monoid laws)
and functoriality of approximation. -/
structure GradedComonad (R : Type) [Monoid R] [Preorder R] (C : Type u) [Category.{v} C] where
  /-- The graded modality `D_r`. -/
  D : R → C ⥤ C
  /-- Counit (dereliction) `ε : D_1 ⟶ 𝟭`. -/
  counit : D 1 ⟶ 𝟭 C
  /-- Comultiplication `δ_{r,s} : D_{r*s} ⟶ D_r ∘ D_s`. -/
  comult : ∀ r s : R, D (r * s) ⟶ D s ⋙ D r
  /-- Approximation `D_s ⟶ D_r` for `r ⊑ s`. -/
  approx : ∀ {r s : R}, r ≤ s → (D s ⟶ D r)
  counit_comult : ∀ (r : R) (A : C),
    (comult 1 r).app A ≫ counit.app ((D r).obj A) = eqToHom (by rw [one_mul]; rfl)
  comult_counit : ∀ (r : R) (A : C),
    (comult r 1).app A ≫ (D r).map (counit.app A) = eqToHom (by rw [mul_one]; rfl)
  comult_assoc : ∀ (r s t : R) (A : C),
    (comult (r * s) t).app A ≫ (comult r s).app ((D t).obj A) =
      eqToHom (by rw [mul_assoc]) ≫ (comult r (s * t)).app A ≫ (D r).map ((comult s t).app A)
  approx_refl : ∀ r : R, approx (le_refl r) = 𝟙 (D r)
  approx_trans : ∀ {r s t : R} (h₁ : r ≤ s) (h₂ : s ≤ t),
    approx h₂ ≫ approx h₁ = approx (h₁.trans h₂)

/-- The structure used to interpret GrCore's graded contexts in a monoidal category: an
`R`-graded comonad (for a pre-ordered semiring `R`) together with natural weakening
`D_0 A ⟶ I` (`(WEAK)`), contraction `D_{r+s} A ⟶ D_r A ⊗ D_s A` (context addition), and the
lax monoidal maps `I ⟶ D_r I` and `D_r A ⊗ D_r B ⟶ D_r (A ⊗ B)` (promotion `(PR)` of a term
with several graded free variables). -/
structure GradedExponential (R : Type) [Semiring R] [Preorder R] (C : Type u) [Category.{v} C]
    [MonoidalCategory C] extends GradedComonad R C where
  /-- Weakening `D_0 A ⟶ I`. -/
  weak : ∀ A : C, (D 0).obj A ⟶ 𝟙_ C
  /-- Contraction `D_{r+s} A ⟶ D_r A ⊗ D_s A`. -/
  contr : ∀ (r s : R) (A : C), (D (r + s)).obj A ⟶ (D r).obj A ⊗ (D s).obj A
  /-- Nullary lax monoidal map `I ⟶ D_r I`. -/
  laxUnit : ∀ r : R, 𝟙_ C ⟶ (D r).obj (𝟙_ C)
  /-- Binary lax monoidal map `D_r A ⊗ D_r B ⟶ D_r (A ⊗ B)`. -/
  lax : ∀ (r : R) (A B : C), (D r).obj A ⊗ (D r).obj B ⟶ (D r).obj (A ⊗ B)
  weak_natural : ∀ {A A' : C} (f : A ⟶ A'), (D 0).map f ≫ weak A' = weak A
  contr_natural : ∀ (r s : R) {A A' : C} (f : A ⟶ A'),
    (D (r + s)).map f ≫ contr r s A' = contr r s A ≫ ((D r).map f ⊗ₘ (D s).map f)
  lax_natural : ∀ (r : R) {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B'),
    ((D r).map f ⊗ₘ (D r).map g) ≫ lax r A' B' = lax r A B ≫ (D r).map (f ⊗ₘ g)

/-- **The coeffect remark of Section 4.** A partial colax monoidal structure on a graded
comonad `G`, indexed by a partial operation `hs = ⋉` on grades (the operation used by the
rule `[PPROD]` of the adjusted calculus):

`n_{r,s,A,B} : D_{r ⋉ s}(A ⊗ B) ⟶ D_r A ⊗ D_s B`, available exactly when `r ⋉ s` is defined.

The laws are naturality in `A` and `B`, compatibility with the counit (when `1 ⋉ 1 = 1`),
symmetry (with the braiding), and associativity (when both bracketings of `r ⋉ s ⋉ t` are
defined). -/
structure HSupColax {R : Type} [Monoid R] [Preorder R] (hs : R → R → Option R)
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (G : GradedComonad R C) where
  /-- The colax map `n_{r,s,A,B} : D_t (A ⊗ B) ⟶ D_r A ⊗ D_s B` for `r ⋉ s = t`. -/
  n : ∀ {r s t : R}, hs r s = some t → ∀ A B : C,
    (G.D t).obj (A ⊗ B) ⟶ (G.D r).obj A ⊗ (G.D s).obj B
  natural : ∀ {r s t : R} (h : hs r s = some t) {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B'),
    (G.D t).map (f ⊗ₘ g) ≫ n h A' B' = n h A B ≫ ((G.D r).map f ⊗ₘ (G.D s).map g)
  counit : ∀ (h : hs 1 1 = some 1) (A B : C),
    n h A B ≫ (G.counit.app A ⊗ₘ G.counit.app B) = G.counit.app (A ⊗ B)
  symm : ∀ {r s t : R} (h : hs r s = some t) (h' : hs s r = some t) (A B : C),
    n h A B ≫ (β_ _ _).hom = (G.D t).map (β_ A B).hom ≫ n h' B A
  assoc : ∀ {r s t u u' v : R} (h₁ : hs r s = some u) (h₂ : hs u t = some v)
      (h₃ : hs s t = some u') (h₄ : hs r u' = some v) (A B E : C),
    n h₂ (A ⊗ B) E ≫ (n h₁ A B ▷ (G.D t).obj E) ≫ (α_ _ _ _).hom =
      (G.D v).map (α_ A B E).hom ≫ n h₄ A (B ⊗ E) ≫ ((G.D r).obj A ◁ n h₃ B E)

variable {R : Type} [Monoid R] [Preorder R] {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] {G : GradedComonad R C}

/-- The semantic `push` at grade `r`, `D_r (A ⊗ B) ⟶ D_r A ⊗ D_r B`, exists whenever
`r ⋉ r = r`: it is the colax map `n_{r,r,A,B}`. This is the interpretation of the term
`push = λz. let [(x, y)] = z in ([x], [y])`. -/
def HSupColax.push {hs : R → R → Option R} (N : HSupColax hs G) {r : R}
    (h : hs r r = some r) (A B : C) :
    (G.D r).obj (A ⊗ B) ⟶ (G.D r).obj A ⊗ (G.D r).obj B :=
  N.n h A B

/-- The semantic `push` is natural in both components. -/
lemma HSupColax.push_natural {hs : R → R → Option R} (N : HSupColax hs G) {r : R}
    (h : hs r r = some r) {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') :
    (G.D r).map (f ⊗ₘ g) ≫ N.push h A' B' = N.push h A B ≫ ((G.D r).map f ⊗ₘ (G.D r).map g) :=
  N.natural h f g

/-- **GrCore (Section 2) is modelled by "diagonal" colax monoidality.** For the operation
`diagHsup` of Section 2 (`r ⋉ s` defined, and equal to `r`, iff `r = s`), every model of
`[PPROD]` has a semantic `push` at *every* grade — the semantic counterpart of
`grcore_push`. -/
theorem diag_colax_push [DecidableEq R] (N : HSupColax diagHsup G) (r : R) (A B : C) :
    Nonempty ((G.D r).obj (A ⊗ B) ⟶ (G.D r).obj A ⊗ (G.D r).obj B) :=
  ⟨N.push (by simp [diagHsup]) A B⟩

/-- If a graded comonad has, for some objects `A`, `B` and grade `r`, no morphism
`D_t (A ⊗ B) ⟶ D_r A ⊗ D_r B` for any `t`, then it admits no partial colax structure in which
`r ⋉ r` is defined. -/
theorem no_colax_of_no_split {hs : R → R → Option R} {r : R} {A B : C}
    (hne : ∀ t : R, IsEmpty ((G.D t).obj (A ⊗ B) ⟶ (G.D r).obj A ⊗ (G.D r).obj B))
    (hdef : (hs r r).isSome) : IsEmpty (HSupColax hs G) := by
  refine ⟨fun N => ?_⟩
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hdef
  exact (hne t).false (N.n ht A B)

/-- A partial colax structure restricts along any operation `hs'` that is *less defined*
than `hs` (and agrees with it where defined). Semantically: making `⋉` more partial only
removes requirements on a model. -/
def HSupColax.restrict {hs hs' : R → R → Option R}
    (hle : ∀ {r s t : R}, hs' r s = some t → hs r s = some t) (N : HSupColax hs G) :
    HSupColax hs' G where
  n h A B := N.n (hle h) A B
  natural h _ _ _ _ f g := N.natural (hle h) f g
  counit h A B := N.counit (hle h) A B
  symm h h' A B := N.symm (hle h) (hle h') A B
  assoc h₁ h₂ h₃ h₄ A B E := N.assoc (hle h₁) (hle h₂) (hle h₃) (hle h₄) A B E

end Coeffect

end LinExp

end
