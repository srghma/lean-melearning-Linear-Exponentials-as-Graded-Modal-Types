module

public import RequestProject.Sec4_Solution.Semantics.Interp

/-!
# Section 4: the erasure (set-theoretic) model of GrCore

The simplest model of `Typed hs`, for **any** pre-ordered semiring `R` and **any** partial
operation `hs` (in particular for Section 2's GrCore, `hs = diagHsup`, and for the adjusted
calculus): the category of types and functions, with the cartesian product as tensor, function
types as internal hom, and every graded modality interpreted as the identity, `D_r A = A`.
Weakening is the map to the unit, contraction is the diagonal, and all other structure maps
are identities.

In this model a derivation `Γ ⊢ t : A` denotes an ordinary function from the product of the
assumptions to `⟦A⟧` (grades are erased).  As an application: interpreting an atom by the empty
type shows that no closed term has an atomic type, in any of the calculi
(`no_closed_term_of_atom`).
-/

@[expose] public section

namespace LinExp

namespace Sem

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory

variable (R : Type) [Semiring R] [Preorder R]

/-- The graded exponential comonad on `Type` in which every `D_r` is the identity. -/
def erasureExp : Coeffect.GradedExponential R Type where
  D _ := 𝟭 Type
  counit := 𝟙 _
  comult _ _ := 𝟙 _
  approx _ := 𝟙 _
  counit_comult _ _ := rfl
  comult_counit _ _ := rfl
  comult_assoc _ _ _ _ := rfl
  approx_refl _ := rfl
  approx_trans _ _ := rfl
  weak A := toUnit A
  contr _ _ A := lift (𝟙 A) (𝟙 A)
  laxUnit _ := 𝟙 _
  lax _ _ _ := 𝟙 _
  weak_natural _ := rfl
  contr_natural _ _ _ _ _ := rfl
  lax_natural _ _ _ _ _ _ _ := rfl

/-- The erasure model of `Typed hs`, for any `hs`, with atoms interpreted by `atom`. -/
def erasureModel (hs : R → R → Option R) (atom : ℕ → Type) : CatModel R hs Type where
  E := erasureExp R
  N :=
    { n := fun _ _ _ => 𝟙 _
      natural := fun _ _ _ _ _ _ _ => rfl
      counit := fun _ _ _ => rfl
      symm := fun _ _ _ _ => rfl
      assoc := fun _ _ _ _ _ _ _ => rfl }
  unitDisc _ := 𝟙 _
  atom := atom

variable {R}

/-- In every calculus `Typed hs` (including GrCore and the adjusted calculus), no closed term
has an atomic type: interpret the atom by the empty type in the erasure model. -/
theorem no_closed_term_of_atom (hs : R → R → Option R) (i : ℕ) (t : Term 0) :
    ¬ Typed hs (Ctx.empty 0) t (.atom i) :=
  (erasureModel R hs (fun _ => Empty)).not_typed_of_isEmpty
    ⟨fun f => (f PUnit.unit : Empty).elim⟩ t

end Sem

end LinExp

end
