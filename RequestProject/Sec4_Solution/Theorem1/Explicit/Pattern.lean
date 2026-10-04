module

public import RequestProject.Sec4_Solution.Theorem1.Explicit.Combinators
public import RequestProject.Sec4_Solution.Theorem1.GrCoreToIMELL

/-!
# Section 4 (Theorem 1, explicit translation): pattern matching in IMELL

`patElim p o A M` is the IMELL term that eliminates a GrCore pattern `p` (matched at the
optional grade `o` against the type `A`): if `M` uses the variables bound by `p` (with the
translated types `⟦Δ⟧`), then `patElim p o A M` uses instead one variable of type
`⟦?o A⟧`, at index `0` (`patElim_typed`).  Product patterns become `let _ be x ⊗ y in _`,
and a unit pattern consumes its assumption with `let _ be * in _` (or `discard` it if it is a
`!I`).  This is the explicit version of `patTy_tr`.
-/

@[expose] public section

namespace LinExp

/-! ### Explicit reindexings -/

/-- Reassociation `Γ ++ (Δ₁ ++ Δ₂) ≅ (Γ ++ Δ₁) ++ Δ₂`. -/
def assocR (m k₁ k₂ : ℕ) : Fin (m + (k₁ + k₂)) → Fin (m + k₁ + k₂) :=
  Fin.cast (Nat.add_assoc m k₁ k₂).symm

/-- Exchange `B, (Γ ++ Δ) ≅ (B, Γ) ++ Δ` (the new variable `B` is moved below `Δ`). -/
def swapR (m k : ℕ) : Fin (m + k + 1) → Fin (m + 1 + k) := fun i =>
  if i.val = 0 then ⟨k, by omega⟩ else if i.val - 1 < k then ⟨i.val - 1, by omega⟩
  else ⟨i.val, by omega⟩

/-- Exchange `A, B, Γ ≅ (·, Γ) ++ (x : A, y : B)` (with an unused variable in between). -/
def swap2R (m : ℕ) : Fin (m + 1 + 1) → Fin (m + 1 + 2) := fun i =>
  if i.val = 0 then ⟨1, by omega⟩ else if i.val = 1 then ⟨0, by omega⟩
  else ⟨i.val + 1, by omega⟩

lemma IHasType.append_assoc {m k₁ k₂ : ℕ} {Γ : ICtx m} {D₁ : ICtx k₁} {D₂ : ICtx k₂} {Z : ITy}
    {M : ITerm (m + (k₁ + k₂))} (h : IHasType (Ctx.append Γ (Ctx.append D₁ D₂)) M Z) :
    IHasType (Ctx.append (Ctx.append Γ D₁) D₂) (M.rename (assocR m k₁ k₂)) Z := by
  refine h.rename (ρ := assocR m k₁ k₂) (Fin.cast_injective _)
    (fun i => ?_) (fun k hk => (hk (Fin.cast (Nat.add_assoc m k₁ k₂) k) (by
      ext; simp [assocR])).elim)
  simp only [Ctx.append, assocR, Fin.val_cast]
  by_cases h2 : i.val < k₂
  · simp [h2]; intro h; omega
  · by_cases h1 : i.val - k₂ < k₁
    · have : i.val < k₁ + k₂ := by omega
      simp [h2, h1, this]
    · have : ¬ i.val < k₁ + k₂ := by omega
      simp only [h2, dite_false, h1, this]
      congr 1; ext; simp; omega

lemma IHasType.cons_append_swap {m k : ℕ} {Γ : ICtx m} {D : ICtx k} {B : ITy} {Z : ITy}
    {M : ITerm (m + k + 1)} (h : IHasType (Ctx.cons (some B) (Ctx.append Γ D)) M Z) :
    IHasType (Ctx.append (Ctx.cons (some B) Γ) D) (M.rename (swapR m k)) Z := by
  have hρ : Function.Injective (swapR m k) := by
    intro a b hab
    simp only [swapR] at hab
    split_ifs at hab <;> simp [Fin.ext_iff] at hab <;> exact Fin.ext (by omega)
  refine h.rename hρ (fun i => ?_) (fun j hj => ?_)
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp only [swapR, Fin.val_zero, ↓reduceIte, Ctx.cons_zero]
      rw [Ctx.append_high _ _ _ (by simp)]
      simp [Ctx.cons]
    · simp only [swapR, Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
        Ctx.cons_succ]
      by_cases hi : i.val < k
      · simp only [hi, ↓reduceIte]
        rw [Ctx.append_low _ _ _ hi, Ctx.append_low _ _ _ (by simpa using hi)]
      · simp only [hi, ↓reduceIte]
        rw [Ctx.append_high _ _ _ hi, Ctx.append_high _ _ _ (by simp; omega)]
        have : (⟨i.val + 1 - k, by omega⟩ : Fin (m + 1)) = (⟨i.val - k, by omega⟩ : Fin m).succ :=
          Fin.ext (by simp; omega)
        rw [this]; rfl
  · exfalso
    by_cases hj1 : j.val < k
    · exact hj ⟨j.val + 1, by omega⟩ (by simp [swapR, hj1])
    · by_cases hj2 : j.val = k
      · exact hj 0 (by simp [swapR]; exact Fin.ext hj2.symm)
      · refine hj ⟨j.val, by omega⟩ ?_
        have h3 : ¬ (j.val = 0) := by omega
        have h4 : ¬ (j.val - 1 < k) := by omega
        simp only [swapR, h3, h4, ↓reduceIte]

lemma IHasType.swap_into_ctx2 {m : ℕ} {Γ : ICtx m} {A B Z : ITy} {M : ITerm (m + 1 + 1)}
    (h : IHasType (Ctx.cons (some A) (Ctx.cons (some B) Γ)) M Z) :
    IHasType (Ctx.append (Ctx.cons none Γ) (ctx2 A B)) (M.rename (swap2R m)) Z := by
  have hρ : Function.Injective (swap2R m) := by
    intro a b hab
    simp only [swap2R] at hab
    split_ifs at hab <;> simp only [Fin.ext_iff] at hab <;> exact Fin.ext (by omega)
  rw [append_ctx2]
  refine h.rename hρ (fun i => ?_) (fun j hj => ?_)
  · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · rfl
    · rfl
    · have e : swap2R m i.succ.succ = i.succ.succ.succ := by
        have h3 : ¬ (i.val + 1 + 1 = 0) := by omega
        have h4 : ¬ (i.val + 1 + 1 = 1) := by omega
        simp only [swap2R, Fin.val_succ, h3, h4, ↓reduceIte]; rfl
      rw [e]; rfl
  · refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j) j hj
    · intro hj; exact absurd (by simp [swap2R]) (hj 1)
    · intro hj; exact absurd (by simp [swap2R]) (hj 0)
    · intro _; rfl
    · intro hj
      have h3 : ¬ (j.val + 1 + 1 = 0) := by omega
      have h4 : ¬ (j.val + 1 + 1 = 1) := by omega
      exact absurd (by simp only [swap2R, Fin.val_succ, h3, h4, ↓reduceIte]; rfl) (hj j.succ.succ)

/-! ### Pattern elimination -/

/-- First component of a product type (junk otherwise). -/
def Ty.fstOf {R : Type} : Ty R → Ty R
  | .tensor A _ => A
  | A => A

/-- Second component of a product type (junk otherwise). -/
def Ty.sndOf {R : Type} : Ty R → Ty R
  | .tensor _ B => B
  | A => A

/-- Grade of a boxed type (junk otherwise). -/
def Ty.gradeOf : Ty LNL → LNL
  | .box r _ => r
  | _ => .one

/-- Argument of a boxed type (junk otherwise). -/
def Ty.unboxOf {R : Type} : Ty R → Ty R
  | .box _ A => A
  | A => A

/-- How the assumption `⟦?o 1⟧` of a unit pattern is consumed: `⟦□_ω 1⟧ = !I` is
discarded, the others are `I` and consumed by `let _ be * in _`. -/
def unitKind : Option LNL → AdjKind
  | some .many => .addBang
  | _ => .addUnit

/-- Elimination of the pattern `p` (matched at the optional grade `o` against the type `A`):
turns a term using the `k` variables bound by `p` (the innermost ones) into a term using one
variable (index `0`) of type `⟦?o A⟧`. -/
def patElim : {k : ℕ} → Pat k → Option LNL → Ty LNL → {m : ℕ} → ITerm (m + k) → ITerm (m + 1)
  | _, .var, _, _, _, M => M
  | _, .pair (k₁ := k₁) (k₂ := k₂) p₁ p₂, o, A, m, M =>
    .letPair (.var 0)
      ((patElim p₁ o A.fstOf (m := m + 1)
        ((patElim p₂ o A.sndOf (m := m + k₁) (M.rename (assocR m k₁ k₂))).rename
          (swapR m k₁))).rename (swap2R m))
  | _, .box p, _, A, _, M => patElim p (some A.gradeOf) A.unboxOf M
  | _, .unit, o, _, _, M => adjustAt 0 (unitKind o) (M.rename Fin.succ)

/-- Typing of pattern elimination (explicit version of `patTy_tr`). -/
theorem patElim_typed {k : ℕ} {o : Option LNL} {p : Pat k} {A : Ty LNL} {Δ : GCtx LNL k}
    (h : PatTy HSup.hsup o p A Δ) :
    ∀ {m : ℕ} {Γ : ICtx m} {Z : ITy} {M : ITerm (m + k)},
      IHasType (Ctx.append Γ (trCtx Δ)) M Z →
      IHasType (Ctx.cons (some (trOpt o A)) Γ) (patElim p o A M) Z := by
  induction h with
  | var A =>
    intro m Γ Z M hM; rw [Ctx.append_one] at hM; exact hM
  | @pair k₁ k₂ p₁ p₂ A B Δ₁ Δ₂ _ _ ih1 ih2 =>
    intro m Γ Z M hM
    rw [trCtx_append] at hM
    exact IHasType.letPair (Γ₁ := isingle 0 (.tensor (trTy A) (trTy B)))
      (Γ₂ := Ctx.cons none Γ) (isingle_var 0 _)
      (ih1 (ih2 hM.append_assoc).cons_append_swap).swap_into_ctx2 (fun k => by
        refine Fin.cases ?_ (fun k => ?_) k
        · right; simp [isingle]; rfl
        · left; simp [isingle, Fin.succ_ne_zero])
  | box r _ ih => intro m Γ Z M hM; exact ih hM
  | gvar r A =>
    intro m Γ Z M hM; rw [Ctx.append_one] at hM; exact hM
  | @gpair k₁ k₂ p₁ p₂ A B Δ₁ Δ₂ r s t _ _ hst ih1 ih2 =>
    obtain ⟨rfl, rfl, rfl⟩ := LNL.hsup_eq_some.mp hst
    intro m Γ Z M hM
    rw [trCtx_append] at hM
    exact IHasType.letPair (Γ₁ := isingle 0 (.tensor (trTy A) (trTy B)))
      (Γ₂ := Ctx.cons none Γ) (isingle_var 0 _)
      (ih1 (ih2 hM.append_assoc).cons_append_swap).swap_into_ctx2 (fun k => by
        refine Fin.cases ?_ (fun k => ?_) k
        · right; simp [isingle]; rfl
        · left; simp [isingle, Fin.succ_ne_zero])
  | unit o =>
    intro m Γ Z M hM
    rw [Ctx.append_zero] at hM
    have hM' : IHasType (Ctx.cons none Γ) (M.rename Fin.succ) Z :=
      hM.rename (Fin.succ_injective m) (fun _ => rfl)
        (fun j hj => Fin.cases (fun _ => rfl) (fun j hj => absurd rfl (hj j)) j hj)
    refine adjustAt_typed' (Γ := Ctx.cons none Γ) 0 ?_
      (fun j hj => by
        obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hj
        rfl) hM'
    rcases o with _ | r
    · exact ⟨rfl, rfl⟩
    · cases r
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, _, rfl⟩

end LinExp

end
