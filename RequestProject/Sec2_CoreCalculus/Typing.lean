module

public import RequestProject.Sec2_CoreCalculus.Syntax

/-!
# Section 2: the type system of GrCore

Grades form a pre-ordered semiring `(R, *, 1, +, 0, ⊑)`; in Lean: `[Semiring R] [Preorder R]`.

Contexts `Γ ::= ∅ | Γ, x : A | Γ, y : [A]_r` contain linear assumptions `x : A` and graded
assumptions `y : [A]_r`.  Over de Bruijn indices a context is a `GCtx R n`, i.e. a function
from the `n` indices in scope to optional assumptions (`none` = the variable is not assumed).

The typing judgement `Γ ⊢ t : A` is `Typed hs Γ t A`.  It is parametrised by a partial binary
operation `hs : R → R → Option R` on grades, which is only used by the rule `[PPROD]` for
product patterns underneath a box:

* the calculus of Section 2 (where `[PPROD]` requires both sub-patterns to be typed at the
  same grade `r`) is `Typed diagHsup` (see `GrCore`), where `diagHsup r s = r` if `r = s` and
  is undefined otherwise;
* the *adjusted* calculus of Section 4 uses the `hsup` operation `r ⊔ s` of the grade
  structure (see `RequestProject/Sec4_Solution/Hsup.lean`).

Because named contexts are unordered, the rules `DER` and `APPROX` may act on an assumption
at any position.
-/

@[expose] public section

namespace LinExp

/-- An assumption: linear `x : A` or graded `x : [A]_r`. -/
inductive Assm (R : Type) : Type where
  | lin : Ty R → Assm R
  | grad : Ty R → R → Assm R
  deriving DecidableEq

/-- GrCore contexts over `n` de Bruijn indices. -/
abbrev GCtx (R : Type) (n : ℕ) := Ctx (Assm R) n

variable {R : Type}

section Ops

variable [Semiring R]

/-- Pointwise context addition `Γ₁ + Γ₂` (as a relation, since it is partial): linear
assumptions must be disjoint, and a graded assumption present in both contexts has its grades
added: `(Γ, x : [A]_r) + (Γ', x : [A]_s) = (Γ + Γ'), x : [A]_(r+s)`. -/
inductive EntryAdd : Option (Assm R) → Option (Assm R) → Option (Assm R) → Prop where
  | noneLeft (e : Option (Assm R)) : EntryAdd none e e
  | noneRight (a : Assm R) : EntryAdd (some a) none (some a)
  | grad (A : Ty R) (r s : R) :
      EntryAdd (some (.grad A r)) (some (.grad A s)) (some (.grad A (r + s)))

/-- `CtxAdd Γ₁ Γ₂ Γ` means `Γ₁ + Γ₂ = Γ`. -/
def CtxAdd {n : ℕ} (Γ₁ Γ₂ Γ : GCtx R n) : Prop := ∀ i, EntryAdd (Γ₁ i) (Γ₂ i) (Γ i)

/-- `[Δ]_0`: a context containing only assumptions graded by `0`. -/
def IsZeroCtx {n : ℕ} (Δ : GCtx R n) : Prop :=
  ∀ i, Δ i = none ∨ ∃ A, Δ i = some (.grad A 0)

/-- `[Γ]`: a context containing only graded assumptions. -/
def IsGraded {n : ℕ} (Γ : GCtx R n) : Prop := ∀ i A, Γ i ≠ some (.lin A)

/-- Scaling of an assumption by a grade: `r * (x : [A]_s) = x : [A]_(r * s)`. -/
def Assm.scale (r : R) : Assm R → Assm R
  | .lin A => .lin A
  | .grad A s => .grad A (r * s)

/-- `r * Γ`: scale every graded assumption of `Γ` by `r` (on the left). -/
def scale {n : ℕ} (r : R) (Γ : GCtx R n) : GCtx R n := fun i => (Γ i).map (Assm.scale r)

end Ops

variable [Semiring R] [Preorder R]

/-- Pattern typing `?r ⊢ p : A ▷ Δ`.  The optional grade `?r ::= · | r` is `none` for `·` and
`some r` underneath an unboxing pattern.  The operation `hs` is used by `[PPROD]`. -/
inductive PatTy (hs : R → R → Option R) : {k : ℕ} → Option R → Pat k → Ty R → GCtx R k → Prop
  /-- `(PVAR)  · ⊢ x : A ▷ x : A` -/
  | var (A : Ty R) : PatTy hs none .var A (fun _ => some (.lin A))
  /-- `(PPROD)` -/
  | pair {k₁ k₂ : ℕ} {p₁ : Pat k₁} {p₂ : Pat k₂} {A B : Ty R} {Δ₁ : GCtx R k₁}
      {Δ₂ : GCtx R k₂} :
      PatTy hs none p₁ A Δ₁ → PatTy hs none p₂ B Δ₂ →
      PatTy hs none (.pair p₁ p₂) (A ⊗ B) (Ctx.append Δ₁ Δ₂)
  /-- `(PBOX)` -/
  | box {k : ℕ} {p : Pat k} {A : Ty R} {Δ : GCtx R k} (r : R) :
      PatTy hs (some r) p A Δ → PatTy hs none (.box p) (□[r] A) Δ
  /-- `([PVAR])  r ⊢ x : A ▷ x : [A]_r` -/
  | gvar (r : R) (A : Ty R) : PatTy hs (some r) .var A (fun _ => some (.grad A r))
  /-- `([PPROD])`: the sub-patterns are typed at grades `r` and `s`, and the product
  pattern at grade `hs r s` (which must be defined). -/
  | gpair {k₁ k₂ : ℕ} {p₁ : Pat k₁} {p₂ : Pat k₂} {A B : Ty R} {Δ₁ : GCtx R k₁}
      {Δ₂ : GCtx R k₂} {r s t : R} :
      PatTy hs (some r) p₁ A Δ₁ → PatTy hs (some s) p₂ B Δ₂ → hs r s = some t →
      PatTy hs (some t) (.pair p₁ p₂) (A ⊗ B) (Ctx.append Δ₁ Δ₂)
  /-- `(PUNIT)  ?r ⊢ unit : 1 ▷ ∅` -/
  | unit (o : Option R) : PatTy hs o .unit .unit (Ctx.empty 0)

/-- The typing judgement `Γ ⊢ t : A` of GrCore, parametrised by the operation `hs` used in
the pattern rule `[PPROD]`. -/
inductive Typed (hs : R → R → Option R) : {n : ℕ} → GCtx R n → Term n → Ty R → Prop
  /-- `(VAR)  x : A ⊢ x : A` -/
  | var {n : ℕ} {Γ : GCtx R n} {i : Fin n} {A : Ty R} :
      Γ i = some (.lin A) → (∀ j, j ≠ i → Γ j = none) → Typed hs Γ (.var i) A
  /-- `(ABS)` -/
  | lam {n : ℕ} {Γ : GCtx R n} {t : Term (n + 1)} {A B : Ty R} :
      Typed hs (Ctx.cons (some (.lin A)) Γ) t B → Typed hs Γ (.lam t) (A ⊸ B)
  /-- `(APP)` -/
  | app {n : ℕ} {Γ₁ Γ₂ Γ : GCtx R n} {t₁ t₂ : Term n} {A B : Ty R} :
      Typed hs Γ₁ t₁ (A ⊸ B) → Typed hs Γ₂ t₂ A → CtxAdd Γ₁ Γ₂ Γ → Typed hs Γ (.app t₁ t₂) B
  /-- `(DER)`: a linear assumption may be turned into a graded assumption of grade `1`. -/
  | der {n : ℕ} {Γ : GCtx R n} {t : Term n} {A B : Ty R} {i : Fin n} :
      Typed hs Γ t B → Γ i = some (.lin A) →
      Typed hs (Function.update Γ i (some (.grad A 1))) t B
  /-- `(WEAK)  Γ ⊢ t : A  ⟹  Γ + [Δ]_0 ⊢ t : A` -/
  | weak {n : ℕ} {Γ Δ Γ' : GCtx R n} {t : Term n} {A : Ty R} :
      Typed hs Γ t A → IsZeroCtx Δ → CtxAdd Γ Δ Γ' → Typed hs Γ' t A
  /-- `(APPROX)`: a grade `r` may be approximated by any `s` with `r ⊑ s`. -/
  | approx {n : ℕ} {Γ : GCtx R n} {t : Term n} {A B : Ty R} {i : Fin n} {r s : R} :
      Typed hs Γ t B → Γ i = some (.grad A r) → r ≤ s →
      Typed hs (Function.update Γ i (some (.grad A s))) t B
  /-- `(PR)  [Γ] ⊢ t : A  ⟹  r * [Γ] ⊢ [t] : □_r A` -/
  | pr {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R} (r : R) :
      Typed hs Γ t A → IsGraded Γ → Typed hs (scale r Γ) (.box t) (□[r] A)
  /-- `(UNIT)  ∅ ⊢ unit : 1` -/
  | unit {n : ℕ} {Γ : GCtx R n} : (∀ i, Γ i = none) → Typed hs Γ .unit .unit
  /-- `(PROD)` -/
  | pair {n : ℕ} {Γ₁ Γ₂ Γ : GCtx R n} {t₁ t₂ : Term n} {A B : Ty R} :
      Typed hs Γ₁ t₁ A → Typed hs Γ₂ t₂ B → CtxAdd Γ₁ Γ₂ Γ → Typed hs Γ (.pair t₁ t₂) (A ⊗ B)
  /-- `(LET)` -/
  | letPat {n k : ℕ} {Γ₁ Γ₂ Γ : GCtx R n} {Δ : GCtx R k} {p : Pat k} {t₁ : Term n}
      {t₂ : Term (n + k)} {A B : Ty R} :
      Typed hs Γ₁ t₁ A → PatTy hs none p A Δ → Typed hs (Ctx.append Γ₂ Δ) t₂ B →
      CtxAdd Γ₁ Γ₂ Γ → Typed hs Γ (.letPat p t₁ t₂) B

/-- The operation used by `[PPROD]` in the calculus of Section 2: both sub-patterns must be
typed at the same grade `r`, and the product pattern is then typed at `r`. -/
def diagHsup [DecidableEq R] (r s : R) : Option R := if r = s then some r else none

omit [Semiring R] [Preorder R] in
lemma diagHsup_eq_some [DecidableEq R] {r s t : R} : diagHsup r s = some t ↔ r = s ∧ t = r := by
  unfold diagHsup; split_ifs <;> simp_all [eq_comm]

/-- The typing judgement of GrCore exactly as presented in Section 2. -/
abbrev GrCore [DecidableEq R] {n : ℕ} (Γ : GCtx R n) (t : Term n) (A : Ty R) : Prop :=
  Typed diagHsup Γ t A

end LinExp

end
