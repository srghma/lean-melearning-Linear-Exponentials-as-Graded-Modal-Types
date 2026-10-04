module

public import RequestProject.Sec2_CoreCalculus.Renaming

/-!
# Section 2: some derived typing rules of GrCore

Small derived rules used to build concrete derivations.
-/

@[expose] public section

namespace LinExp

variable {R : Type} [Semiring R] [Preorder R] {hs : R → R → Option R}

/-- Typing is invariant under (propositional) equality of contexts. -/
lemma Typed.of_eq {n : ℕ} {Γ Γ' : GCtx R n} {t : Term n} {A : Ty R} (h : Typed hs Γ t A)
    (e : Γ = Γ') : Typed hs Γ' t A := e ▸ h

/-- `x : [A]_1 ⊢ x : A` (VAR followed by DER). -/
lemma Typed.var_one {n : ℕ} {Γ : GCtx R n} {i : Fin n} {A : Ty R}
    (hi : Γ i = some (.grad A 1)) (hj : ∀ j, j ≠ i → Γ j = none) : Typed hs Γ (.var i) A := by
  have h0 : Typed hs (Function.update Γ i (some (.lin A))) (.var i) A :=
    Typed.var (by simp) (fun j hne => by rw [Function.update_of_ne hne]; exact hj j hne)
  refine (h0.der (i := i) (A := A) (by simp)).of_eq ?_
  rw [Function.update_idem, ← hi, Function.update_eq_self]

/-- `x : [A]_r ⊢ [x] : □_r A` (VAR, DER and PR). -/
lemma Typed.box_var {n : ℕ} {Γ : GCtx R n} {i : Fin n} {A : Ty R} {r : R}
    (hi : Γ i = some (.grad A r)) (hj : ∀ j, j ≠ i → Γ j = none) :
    Typed hs Γ (.box (.var i)) (□[r] A) := by
  let Γ0 : GCtx R n := fun j => if j = i then some (.grad A 1) else none
  have h0 : Typed hs Γ0 (.var i) A :=
    Typed.var_one (by simp [Γ0]) (fun j hne => by simp [Γ0, hne])
  refine (h0.pr r (fun j B => by simp only [Γ0]; split_ifs <;> simp)).of_eq ?_
  funext j
  by_cases hji : j = i
  · subst hji; simp [scale, Γ0, hi, Assm.scale]
  · simp [scale, Γ0, hji, hj j hji]


end LinExp

end
