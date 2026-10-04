module

public import RequestProject.Sec5_ImplementationInGranule.DataTypes.Typing

/-!
# Section 5: inversion lemmas for the calculus with data types

If the pattern `p` cannot be matched against `A`, then no term of the form
`λz. let p = z in u` has a type `A ⊸ B` (`lam_letPat_var_ill_typed`).  This lifts the
pattern-level statements of `Examples.lean` (such as "`[(x, y)]` cannot be matched against
`(a, b) [Many]`") to statements about whole programs.

The proof follows a derivation upwards through the structural rules `DER`, `WEAK`, `APPROX`,
which never change the *type* of an assumption.
-/

@[expose] public section

namespace LinExp

variable {R : Type}

/-- The type of an assumption. -/
def GAssm.ty : GAssm R → GTy R
  | .lin A => A
  | .grad A _ => A

/-- Every assumption of `Γ` has type `X`. -/
def AllTy {n : ℕ} (Γ : GrCtx R n) (X : GTy R) : Prop := ∀ j e, Γ j = some e → e.ty = X

section

variable [Semiring R]

lemma AllTy.of_add_left {n : ℕ} {Γ₁ Γ₂ Γ : GrCtx R n} {X : GTy R} (h : AllTy Γ X)
    (hadd : GCtxAdd Γ₁ Γ₂ Γ) : AllTy Γ₁ X := by
  intro j e he
  have h' := hadd j
  have hΓ := h j
  revert h' hΓ
  rw [he]
  generalize Γ₂ j = b
  generalize Γ j = c
  intro h' hΓ
  cases h' with
  | noneRight a => exact hΓ _ rfl
  | grad A r s => exact hΓ (.grad A (r + s)) rfl

omit [Semiring R] in
lemma AllTy.of_update {n : ℕ} {Γ : GrCtx R n} {X : GTy R} {i : Fin n} {e₀ e₁ : GAssm R}
    (h : AllTy (Function.update Γ i (some e₁)) X) (hi : Γ i = some e₀) (hty : e₀.ty = e₁.ty) :
    AllTy Γ X := by
  intro j e he
  by_cases hj : j = i
  · subst hj
    rw [hi] at he
    cases he
    rw [hty]
    exact h j e₁ (by simp)
  · exact h j e (by rw [Function.update_of_ne hj]; exact he)

end

variable [Semiring R] [Preorder R] {sig : GSig R} {hs : R → R → Option R}

/-- A variable typed in a context whose assumptions all have type `X` has type `X`. -/
theorem GTyped.var_ty {n : ℕ} {Γ : GrCtx R n} {t : GTerm n} {A : GTy R}
    (h : GTyped sig hs Γ t A) : ∀ (i : Fin n) (X : GTy R), t = .var i → AllTy Γ X → A = X := by
  induction h with
  | var hi _ =>
    intro i X _ hX
    exact hX _ _ hi
  | der _ hi ih =>
    intro i X ht hX
    exact ih i X ht (hX.of_update hi rfl)
  | weak _ _ hadd ih =>
    intro i X ht hX
    exact ih i X ht (hX.of_add_left hadd)
  | approx _ hi _ ih =>
    intro i X ht hX
    exact ih i X ht (hX.of_update hi rfl)
  | _ => intro i X ht; cases ht

/-- Inversion for `let`: the matched term has some type `A` against which the pattern can be
typed, in a context whose assumptions keep their types. -/
theorem GTyped.letPat_inv {n : ℕ} {Γ : GrCtx R n} {t : GTerm n} {B : GTy R}
    (h : GTyped sig hs Γ t B) : ∀ (k : ℕ) (p : GPat k) (t₁ : GTerm n) (u : GTerm (n + k))
    (X : GTy R), t = .letPat p t₁ u → AllTy Γ X →
    ∃ (Γ₁ : GrCtx R n) (A : GTy R) (Δ : GrCtx R k), GTyped sig hs Γ₁ t₁ A ∧
      GPatTy sig hs none p A Δ ∧ AllTy Γ₁ X := by
  induction h with
  | der _ hi ih =>
    intro k p t₁ u X ht hX
    exact ih k p t₁ u X ht (hX.of_update hi rfl)
  | weak _ _ hadd ih =>
    intro k p t₁ u X ht hX
    exact ih k p t₁ u X ht (hX.of_add_left hadd)
  | approx _ hi _ ih =>
    intro k p t₁ u X ht hX
    exact ih k p t₁ u X ht (hX.of_update hi rfl)
  | letPat h₁ hp _ hadd _ _ =>
    intro k p t₁ u X ht hX
    cases ht
    exact ⟨_, _, _, h₁, hp, hX.of_add_left hadd⟩
  | _ => intro k p t₁ u X ht; cases ht

/-- Inversion for `λ` in a context with no assumptions. -/
theorem GTyped.lam_inv {n : ℕ} {Γ : GrCtx R n} {t : GTerm n} {T : GTy R}
    (h : GTyped sig hs Γ t T) : ∀ (t' : GTerm (n + 1)) (A B : GTy R), t = .lam t' →
    T = .lolli A B → (∀ j, Γ j = none) → GTyped sig hs (Ctx.cons (some (.lin A)) Γ) t' B := by
  induction h with
  | lam h' _ =>
    intro t' A B ht hT _
    cases ht
    cases hT
    exact h'
  | @der _ _ _ _ _ i _ _ _ =>
    intro t' A B _ _ hΓ
    exact absurd (hΓ i) (by simp)
  | @approx _ _ _ _ _ i _ _ _ _ _ _ =>
    intro t' A B _ _ hΓ
    exact absurd (hΓ i) (by simp)
  | @weak _ Γ₀ Δ Γ' _ _ _ _ hadd ih =>
    intro t' A B ht hT hΓ
    have hΓ₀ : ∀ j, Γ₀ j = none := fun j => by
      have h' := hadd j
      revert h'
      rw [hΓ j]
      generalize Γ₀ j = a
      generalize Δ j = b
      intro h'
      cases h'
      rfl
    have e : Γ₀ = Γ' := funext fun j => (hΓ₀ j).trans (hΓ j).symm
    rw [← e]
    exact ih t' A B ht hT hΓ₀
  | _ => intro t' A B ht; cases ht

/-- **Programs that match an ill-typed pattern are ill-typed.**  If the pattern `p` cannot be
matched against `A`, then no closed term `λz. let p = z in u` has a type `A ⊸ B`. -/
theorem lam_letPat_var_ill_typed {k : ℕ} {p : GPat k} {A B : GTy R} {u : GTerm (0 + 1 + k)}
    (hp : ¬ ∃ Δ, GPatTy sig hs none p A Δ) :
    ¬ GTyped sig hs (Ctx.empty 0) (.lam (.letPat p (.var 0) u)) (.lolli A B) := by
  intro h
  have h₁ := h.lam_inv _ A B rfl rfl (fun _ => rfl)
  have hX : AllTy (Ctx.cons (some (.lin A)) (Ctx.empty 0) : GrCtx R (0 + 1)) A := by
    intro j e he
    have hj : j = 0 := Fin.ext (by omega)
    subst hj
    simp only [Ctx.cons_zero, Option.some.injEq] at he
    subst he
    rfl
  obtain ⟨Γ₁, A', Δ, hv, hp', hX₁⟩ := h₁.letPat_inv k p (.var 0) u A rfl hX
  obtain rfl := hv.var_ty 0 A rfl hX₁
  exact hp ⟨Δ, hp'⟩

end LinExp

end
