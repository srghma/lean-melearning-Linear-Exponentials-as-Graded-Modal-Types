module

public import RequestProject.Sec4_Solution.Semantics.Interp
public import RequestProject.Sec4_Solution.Model.GrCoreModel
public import RequestProject.Sec3_DissectingTheProblem.Push

/-!
# Section 4: the resource-counting model is an instance of the categorical semantics

The resource-counting model of `Sec4_Solution/Model` (values in `{-∞} ∪ ℤ ∪ {+∞}`, a sequent
`Γ ⊢ A` is valid when `⟦A⟧ ≤ Σ ⟦Γ⟧`) is a *thin* categorical model of the adjusted calculus
over `{0, 1, ω}`:

* objects are values (`CVal`), with a (unique) morphism `x ⟶ y` iff `y ≤ x`;
* the tensor is addition, the unit is `0`, the internal hom is the residual `res`;
* `D_0 x = 0`, `D_1 x = x`, `D_ω x = !x`;
* the colax map exists only for `1 ⋉ 1 = 1` (equation (1)).

`countingModel ν` packages this as a `CatModel LNL HSup.hsup CVal`.  Its interpretation of
types and contexts is exactly the one of `GrModel` (`countingModel_tyObj`,
`countingModel_ctxObj`), so the general soundness theorem `CatModel.sound` specialises to the
soundness theorem `GrModel.sound` (`grModel_sound_from_catModel`), and gives a second proof of
`adj_push_many_not_derivable` through the categorical semantics
(`adj_push_many_not_derivable_sem`).
-/

@[expose] public section

namespace LinExp

namespace Sem

open CategoryTheory MonoidalCategory MonoidalClosed Val LNL

/-- Objects of the counting model: values, ordered by reverse `≤`
(a morphism `x ⟶ y` means that `x` pays for `y`, i.e. `y ≤ x`). -/
structure CVal where
  /-- The underlying value. -/
  v : Val

namespace CVal

instance : Preorder CVal where
  le x y := y.v ≤ x.v
  le_refl x := le_refl x.v
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁

lemma le_def (x y : CVal) : x ≤ y ↔ y.v ≤ x.v := Iff.rfl

/-- A morphism of the thin category from an inequality of values. -/
def hom {x y : CVal} (h : y.v ≤ x.v) : x ⟶ y := homOfLE h

/-- An isomorphism of the thin category from an equality of values. -/
def isoOfEq {x y : CVal} (h : x.v = y.v) : x ≅ y where
  hom := hom (by rw [h])
  inv := hom (by rw [h])

instance : MonoidalCategory CVal where
  tensorObj x y := ⟨x.v + y.v⟩
  whiskerLeft x _ _ f := hom (add_le_add le_rfl ((le_def _ _).mp (leOfHom f)))
  whiskerRight f y := hom (add_le_add ((le_def _ _).mp (leOfHom f)) le_rfl)
  tensorUnit := ⟨0⟩
  associator _ _ _ := isoOfEq (add_assoc _ _ _)
  leftUnitor _ := isoOfEq (zero_add _)
  rightUnitor _ := isoOfEq (add_zero _)

instance : SymmetricCategory CVal where
  braiding _ _ := isoOfEq (add_comm _ _)

@[simp] lemma tensorObj_v (x y : CVal) : (x ⊗ y).v = x.v + y.v := rfl
@[simp] lemma tensorUnit_v : (𝟙_ CVal).v = 0 := rfl

lemma res_mono_right (a : Val) {b b' : Val} (h : b' ≤ b) : res a b' ≤ res a b :=
  (res_le_iff _ _ _).mpr (h.trans ((res_le_iff _ _ _).mp le_rfl))

/-- The internal hom `a ⊸ -`. -/
def ihomFunctor (a : CVal) : CVal ⥤ CVal :=
  Monotone.functor (f := fun b => ⟨res a.v b.v⟩) (fun _ _ h => res_mono_right a.v h)

instance : MonoidalClosed CVal where
  closed a :=
    { rightAdj := ihomFunctor a
      adj := Adjunction.mkOfHomEquiv
        { homEquiv := fun y z =>
            { toFun := fun f => hom ((res_le_iff _ _ _).mpr (by
                have := leOfHom f
                rw [le_def] at this
                simpa [add_comm] using this))
              invFun := fun g => hom (by
                have := (res_le_iff _ _ _).mp (leOfHom g)
                simpa [add_comm] using this)
              left_inv := fun _ => Subsingleton.elim _ _
              right_inv := fun _ => Subsingleton.elim _ _ }
          homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
          homEquiv_naturality_right := fun _ _ => Subsingleton.elim _ _ } }

@[simp] lemma ihom_obj_v (a b : CVal) : ((ihom a).obj b).v = res a.v b.v := rfl

end CVal

open CVal

lemma bang_mono {a b : Val} (h : a ≤ b) : bang a ≤ bang b := by
  unfold bang
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact le_pinf _
  · exact absurd (h.trans h2) h1
  · exact le_rfl

lemma gact_mono_val (r : LNL) {a b : Val} (h : a ≤ b) : GrModel.gact r a ≤ GrModel.gact r b := by
  cases r
  · exact le_rfl
  · exact h
  · exact bang_mono h

lemma gact_zero_val (r : LNL) : GrModel.gact r 0 = 0 := by
  cases r <;> simp [GrModel.gact, bang_zero]

lemma gact_comult (r s : LNL) (a : Val) :
    GrModel.gact r (GrModel.gact s a) ≤ GrModel.gact (r * s) a := by
  cases r <;> cases s <;>
    simp [GrModel.gact, LNL.mul_def, LNL.mul, bang]
  all_goals split_ifs <;> simp_all

lemma gact_lax (r : LNL) (a b : Val) :
    GrModel.gact r (a + b) ≤ GrModel.gact r a + GrModel.gact r b := by
  cases r
  · simp [GrModel.gact]
  · exact le_rfl
  · simp only [GrModel.gact]
    by_cases ha : a ≤ 0
    · by_cases hb : b ≤ 0
      · have hab : a + b ≤ 0 := by simpa using add_le_add ha hb
        simp [bang, ha, hb, hab]
      · simp [bang, hb]
    · simp [bang, ha]

/-- The graded modality of the counting model. -/
def cD (r : LNL) : CVal ⥤ CVal :=
  Monotone.functor (f := fun a => ⟨GrModel.gact r a.v⟩) (fun _ _ h => gact_mono_val r h)

/-- A natural transformation between functors into the thin category `CVal`. -/
def cNat {F G : CVal ⥤ CVal} (h : ∀ a, (G.obj a).v ≤ (F.obj a).v) : F ⟶ G where
  app a := hom (h a)
  naturality _ _ _ := Subsingleton.elim _ _

/-- The counting model is an `{0, 1, ω}`-graded exponential comonad. -/
def cExp : Coeffect.GradedExponential LNL CVal where
  D := cD
  counit := cNat (fun _ => le_rfl)
  comult r s := cNat (fun a => gact_comult r s a.v)
  approx h := cNat (fun a => GrModel.gact_mono h a.v)
  counit_comult _ _ := Subsingleton.elim _ _
  comult_counit _ _ := Subsingleton.elim _ _
  comult_assoc _ _ _ _ := Subsingleton.elim _ _
  approx_refl _ := by ext; exact Subsingleton.elim _ _
  approx_trans _ _ := by ext; exact Subsingleton.elim _ _
  weak _ := hom (by simp [cD, GrModel.gact])
  contr r s a := hom (GrModel.gact_add_le r s a.v)
  laxUnit r := hom (by simp [cD, gact_zero_val])
  lax r a b := hom (gact_lax r a.v b.v)
  weak_natural _ := Subsingleton.elim _ _
  contr_natural _ _ _ _ _ := Subsingleton.elim _ _
  lax_natural _ _ _ _ _ _ _ := Subsingleton.elim _ _

/-- The colax structure of equation (1) in the counting model. -/
def cColax : Coeffect.HSupColax (HSup.hsup : LNL → LNL → Option LNL) cExp.toGradedComonad where
  n {r s t} h a b := hom (by
    obtain ⟨rfl, rfl, rfl⟩ := LNL.hsup_eq_some.mp h
    exact le_rfl)
  natural _ _ _ _ _ _ _ := Subsingleton.elim _ _
  counit _ _ _ := Subsingleton.elim _ _
  symm _ _ _ _ := Subsingleton.elim _ _
  assoc _ _ _ _ _ _ _ := Subsingleton.elim _ _

/-- **The counting model** (for a valuation `ν` of the atoms) as a categorical model of the
adjusted calculus over `{0, 1, ω}`. -/
def countingModel (ν : ℕ → ℤ) : CatModel LNL HSup.hsup CVal where
  E := cExp
  N := cColax
  unitDisc r := hom (by simp [cExp, cD, gact_zero_val])
  atom i := ⟨fin (ν i)⟩

variable (ν : ℕ → ℤ)

/-- The categorical interpretation of types in the counting model is `GrModel.interp`. -/
theorem countingModel_tyObj (A : Ty LNL) :
    ((countingModel ν).tyObj A).v = GrModel.interp ν A := by
  induction A with
  | atom i => rfl
  | unit => rfl
  | lolli A B ihA ihB =>
    show res _ _ = _
    rw [ihA, ihB]; rfl
  | tensor A B ihA ihB =>
    show _ + _ = _
    rw [ihA, ihB]; rfl
  | box r A ih =>
    show GrModel.gact r _ = _
    rw [ih]; rfl

lemma countingModel_entryObj (e : Option (Assm LNL)) :
    ((countingModel ν).entryObj e).v = GrModel.entry ν e := by
  rcases e with _ | ⟨A⟩ | ⟨A, r⟩
  · rfl
  · exact countingModel_tyObj ν A
  · show GrModel.gact r _ = _
    rw [countingModel_tyObj]; rfl

/-- The categorical interpretation of contexts in the counting model is `GrModel.ctxVal`. -/
theorem countingModel_ctxObj {n : ℕ} (Γ : GCtx LNL n) :
    ((countingModel ν).ctxObj Γ).v = GrModel.ctxVal ν Γ := by
  induction n with
  | zero => simp [GrModel.ctxVal]
  | succ n ih =>
    rw [CatModel.ctxObj_succ, tensorObj_v, ih, countingModel_entryObj, GrModel.ctxVal,
      GrModel.ctxVal, Fin.sum_univ_succ, add_comm]

/-- In the counting model, a morphism `⟦Γ⟧ ⟶ ⟦A⟧` exists iff the sequent is valid in the
sense of `GrModel`. -/
theorem countingModel_hom_iff {n : ℕ} (Γ : GCtx LNL n) (A : Ty LNL) :
    Nonempty ((countingModel ν).ctxObj Γ ⟶ (countingModel ν).tyObj A) ↔
      GrModel.interp ν A ≤ GrModel.ctxVal ν Γ := by
  rw [← countingModel_tyObj, ← countingModel_ctxObj]
  exact ⟨fun ⟨f⟩ => leOfHom f, fun h => ⟨hom h⟩⟩

/-- The soundness theorem of the counting model, `GrModel.sound`, is an instance of the
general soundness theorem `CatModel.sound`. -/
theorem grModel_sound_from_catModel {n : ℕ} {Γ : GCtx LNL n} {t : Term n} {A : Ty LNL}
    (h : AdjTyped Γ t A) : GrModel.interp ν A ≤ GrModel.ctxVal ν Γ :=
  (countingModel_hom_iff ν Γ A).mp ((countingModel ν).sound h)

/-- `adj_push_many_not_derivable`, proved through the categorical semantics: in the counting
model with `⟦α⟧ = 1`, `⟦β⟧ = -1`, the type `□_ω (α ⊗ β) ⊸ □_ω α ⊗ □_ω β` has no global
element. -/
theorem adj_push_many_not_derivable_sem {i j : ℕ} (hij : i ≠ j) (t : Term 0) :
    ¬ AdjTyped (Ctx.empty 0) t (pushTy ω (.atom i) (.atom j)) := by
  let ν : ℕ → ℤ := fun k => if k = i then 1 else if k = j then -1 else 0
  refine (countingModel ν).not_typed_of_isEmpty ⟨fun f => ?_⟩ t
  have h := leOfHom f
  rw [CVal.le_def, countingModel_tyObj] at h
  have hj : ν j = -1 := by simp [ν, Ne.symm hij]
  have hi : ν i = 1 := by simp [ν]
  simp [pushTy, GrModel.interp, GrModel.gact, hi, hj, Val.bang, Val.res, Val.zero_eq] at h

end Sem

end LinExp

end
