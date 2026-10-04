module

public import RequestProject.Sec4_Solution.IMELL.Syntax

/-!
# Section 4: typing rules of IMELL (natural deduction, Benton et al.)

`Γ ⊢ M : A` is `IHasType Γ M A`, where a context `Γ : ICtx n` assigns an optional formula to
each of the `n` de Bruijn indices in scope (`none` = not assumed).  Contexts are split
disjointly between premises (`ISplit`, and `ISplitN` for the `k` premises of promotion).
-/

@[expose] public section

namespace LinExp

/-- IMELL contexts over `n` de Bruijn indices. -/
abbrev ICtx (n : ℕ) := Ctx ITy n

/-- `ISplit Γ₁ Γ₂ Γ`: `Γ` is the disjoint union of `Γ₁` and `Γ₂`. -/
def ISplit {n : ℕ} (Γ₁ Γ₂ Γ : ICtx n) : Prop :=
  ∀ i, (Γ₁ i = none ∧ Γ₂ i = Γ i) ∨ (Γ₂ i = none ∧ Γ₁ i = Γ i)

/-- `ISplitN k Γs Γ`: `Γ` is the disjoint union of the `k` contexts `Γs j`. -/
def ISplitN {n : ℕ} : (k : ℕ) → (Fin k → ICtx n) → ICtx n → Prop
  | 0, _, Γ => ∀ i, Γ i = none
  | k + 1, Γs, Γ => ∃ Γ', ISplitN k (fun j => Γs j.succ) Γ' ∧ ISplit (Γs 0) Γ' Γ

/-- The two-variable context `x : A, y : B` (`y` is index `0`). -/
def ctx2 (A B : ITy) : ICtx 2 := fun i => if i.val = 0 then some B else some A

/-- The typing judgement of IMELL. -/
inductive IHasType : {n : ℕ} → ICtx n → ITerm n → ITy → Prop
  | var {n : ℕ} {Γ : ICtx n} {i : Fin n} {A : ITy} :
      Γ i = some A → (∀ j, j ≠ i → Γ j = none) → IHasType Γ (.var i) A
  | lam {n : ℕ} {Γ : ICtx n} {M : ITerm (n + 1)} {A B : ITy} :
      IHasType (Ctx.cons (some A) Γ) M B → IHasType Γ (.lam M) (.lolli A B)
  | app {n : ℕ} {Γ₁ Γ₂ Γ : ICtx n} {M N : ITerm n} {A B : ITy} :
      IHasType Γ₁ M (.lolli A B) → IHasType Γ₂ N A → ISplit Γ₁ Γ₂ Γ →
      IHasType Γ (.app M N) B
  | star {n : ℕ} {Γ : ICtx n} : (∀ i, Γ i = none) → IHasType Γ .star .unit
  | letStar {n : ℕ} {Γ₁ Γ₂ Γ : ICtx n} {M N : ITerm n} {C : ITy} :
      IHasType Γ₁ M .unit → IHasType Γ₂ N C → ISplit Γ₁ Γ₂ Γ → IHasType Γ (.letStar M N) C
  | pair {n : ℕ} {Γ₁ Γ₂ Γ : ICtx n} {M N : ITerm n} {A B : ITy} :
      IHasType Γ₁ M A → IHasType Γ₂ N B → ISplit Γ₁ Γ₂ Γ →
      IHasType Γ (.pair M N) (.tensor A B)
  | letPair {n : ℕ} {Γ₁ Γ₂ Γ : ICtx n} {M : ITerm n} {N : ITerm (n + 2)} {A B C : ITy} :
      IHasType Γ₁ M (.tensor A B) → IHasType (Ctx.append Γ₂ (ctx2 A B)) N C →
      ISplit Γ₁ Γ₂ Γ → IHasType Γ (.letPair M N) C
  | promote {n k : ℕ} {Γs : Fin k → ICtx n} {Γ : ICtx n} {Ms : Fin k → ITerm n}
      {N : ITerm k} {As : Fin k → ITy} {B : ITy} :
      ISplitN k Γs Γ → (∀ j, IHasType (Γs j) (Ms j) (.bang (As j))) →
      IHasType (fun j => some (.bang (As j))) N B → IHasType Γ (.promote Ms N) (.bang B)
  | derelict {n : ℕ} {Γ : ICtx n} {M : ITerm n} {A : ITy} :
      IHasType Γ M (.bang A) → IHasType Γ (.derelict M) A
  | discard {n : ℕ} {Γ₁ Γ₂ Γ : ICtx n} {M N : ITerm n} {A B : ITy} :
      IHasType Γ₁ M (.bang A) → IHasType Γ₂ N B → ISplit Γ₁ Γ₂ Γ →
      IHasType Γ (.discard M N) B
  | copy {n : ℕ} {Γ₁ Γ₂ Γ : ICtx n} {M : ITerm n} {N : ITerm (n + 2)} {A B : ITy} :
      IHasType Γ₁ M (.bang A) → IHasType (Ctx.append Γ₂ (ctx2 (.bang A) (.bang A))) N B →
      ISplit Γ₁ Γ₂ Γ → IHasType Γ (.copy M N) B

/-- Derivability of a sequent `Γ ⊢ A` in IMELL. -/
def IDeriv {n : ℕ} (Γ : ICtx n) (A : ITy) : Prop := ∃ M, IHasType Γ M A

end LinExp

end
