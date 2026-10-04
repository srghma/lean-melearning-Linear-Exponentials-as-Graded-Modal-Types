module

public import RequestProject.Sec5_ImplementationInGranule.DataTypes.Syntax

/-!
# Section 5: typing GrCore with data types, Granule style

The typing judgement `GTyped sig hs Γ t A` extends the one of Section 2 with constructors and
`case`.  The interesting part is pattern typing (`GPatTy`), which follows the description of
Granule's type checker in Section 5:

* `⋉` "is applied whenever a pattern match occurs against a constructor with at least one
  sub-pattern" (inside a box pattern);
* "The nature of information flow in the type checking of a Granule pattern match is such that
  the grades `r` and `s` in `r ⋉ s` are necessarily the same, i.e. `r ⋉ r`, and we require that
  this is then defined at `r`."

So underneath a box of grade `r`, every sub-pattern of a constructor pattern (and of a product
pattern, which is the built-in data type of pairs) is checked at the same grade `r`, and if
there is at least one sub-pattern the side condition "`r ⋉ r` is defined" is imposed.
Constructor patterns without sub-patterns impose no condition.

Pattern typing is generic in the type `G` of grades (it uses no arithmetic on grades), which is
what lets `Constraints/PatCheck.lean` run it on grade expressions with variables.
-/

@[expose] public section

namespace LinExp

/-- An assumption: linear `x : A` or graded `x : [A]_r` (over the types with data types). -/
inductive GAssm (G : Type) : Type where
  | lin : GTy G → GAssm G
  | grad : GTy G → G → GAssm G
  deriving DecidableEq

/-- Contexts over `n` de Bruijn indices. -/
abbrev GrCtx (G : Type) (n : ℕ) := Ctx (GAssm G) n

/-- Change the grades occurring in an assumption. -/
def GAssm.map {G H : Type} (f : G → H) : GAssm G → GAssm H
  | .lin A => .lin (A.map f)
  | .grad A r => .grad (A.map f) (f r)

/-- Change the grades occurring in a context. -/
def GrCtx.map {G H : Type} (f : G → H) {n : ℕ} (Γ : GrCtx G n) : GrCtx H n :=
  fun i => (Γ i).map (GAssm.map f)

section PatTyping

variable {G : Type}

mutual

/-- Pattern typing `?r ⊢ p : A ▷ Δ`, Granule style.  `hs` is the partial operation `⋉`. -/
inductive GPatTy (sig : GSig G) (hs : G → G → Option G) :
    {k : ℕ} → Option G → GPat k → GTy G → GrCtx G k → Prop
  /-- `(PVAR)` -/
  | var (A : GTy G) : GPatTy sig hs none .var A (fun _ => some (.lin A))
  /-- `([PVAR])` -/
  | gvar (r : G) (A : GTy G) : GPatTy sig hs (some r) .var A (fun _ => some (.grad A r))
  /-- `(PPROD)` -/
  | pair {k₁ k₂ : ℕ} {p₁ : GPat k₁} {p₂ : GPat k₂} {A B : GTy G} {Δ₁ : GrCtx G k₁}
      {Δ₂ : GrCtx G k₂} :
      GPatTy sig hs none p₁ A Δ₁ → GPatTy sig hs none p₂ B Δ₂ →
      GPatTy sig hs none (.pair p₁ p₂) (.tensor A B) (Ctx.append Δ₁ Δ₂)
  /-- `([PPROD])`, Granule style: both sub-patterns at `r`, and `r ⋉ r` must be defined. -/
  | gpair {k₁ k₂ : ℕ} {p₁ : GPat k₁} {p₂ : GPat k₂} {A B : GTy G} {Δ₁ : GrCtx G k₁}
      {Δ₂ : GrCtx G k₂} {r : G} :
      (∃ t, hs r r = some t) → GPatTy sig hs (some r) p₁ A Δ₁ → GPatTy sig hs (some r) p₂ B Δ₂ →
      GPatTy sig hs (some r) (.pair p₁ p₂) (.tensor A B) (Ctx.append Δ₁ Δ₂)
  /-- `(PBOX)` -/
  | box {k : ℕ} {p : GPat k} {A : GTy G} {Δ : GrCtx G k} (r : G) :
      GPatTy sig hs (some r) p A Δ → GPatTy sig hs none (.box p) (.box r A) Δ
  /-- `(PUNIT)` -/
  | unit (o : Option G) : GPatTy sig hs o .unit .unit (Ctx.empty 0)
  /-- `(PCON)`: a constructor pattern, not under a box. -/
  | con {k : ℕ} {c d i : ℕ} {ps : GPats k} {As : List (GTy G)} {Δ : GrCtx G k} :
      sig.fields d i c = some As → GPatsTy sig hs none ps As Δ →
      GPatTy sig hs none (.con c ps) (.data d i) Δ
  /-- `([PCON])`: a constructor pattern under a box of grade `r`.  All sub-patterns are typed
  at `r`; if there is at least one sub-pattern, `r ⋉ r` must be defined. -/
  | gcon {k : ℕ} {c d i : ℕ} {ps : GPats k} {As : List (GTy G)} {Δ : GrCtx G k} {r : G} :
      sig.fields d i c = some As → (ps.nonempty → ∃ t, hs r r = some t) →
      GPatsTy sig hs (some r) ps As Δ →
      GPatTy sig hs (some r) (.con c ps) (.data d i) Δ

/-- Typing of the list of sub-patterns of a constructor pattern against its field types. -/
inductive GPatsTy (sig : GSig G) (hs : G → G → Option G) :
    {k : ℕ} → Option G → GPats k → List (GTy G) → GrCtx G k → Prop
  | nil (o : Option G) : GPatsTy sig hs o .nil [] (Ctx.empty 0)
  | cons {k₁ k₂ : ℕ} {o : Option G} {p : GPat k₁} {ps : GPats k₂} {A : GTy G}
      {As : List (GTy G)} {Δ₁ : GrCtx G k₁} {Δ₂ : GrCtx G k₂} :
      GPatTy sig hs o p A Δ₁ → GPatsTy sig hs o ps As Δ₂ →
      GPatsTy sig hs o (.cons p ps) (A :: As) (Ctx.append Δ₁ Δ₂)

end

end PatTyping

variable {R : Type}

section Ops

variable [Semiring R]

/-- Entry-wise context addition (as in Section 2). -/
inductive GEntryAdd : Option (GAssm R) → Option (GAssm R) → Option (GAssm R) → Prop where
  | noneLeft (e : Option (GAssm R)) : GEntryAdd none e e
  | noneRight (a : GAssm R) : GEntryAdd (some a) none (some a)
  | grad (A : GTy R) (r s : R) :
      GEntryAdd (some (.grad A r)) (some (.grad A s)) (some (.grad A (r + s)))

/-- `GCtxAdd Γ₁ Γ₂ Γ` means `Γ₁ + Γ₂ = Γ`. -/
def GCtxAdd {n : ℕ} (Γ₁ Γ₂ Γ : GrCtx R n) : Prop := ∀ i, GEntryAdd (Γ₁ i) (Γ₂ i) (Γ i)

/-- `[Δ]_0`. -/
def GIsZeroCtx {n : ℕ} (Δ : GrCtx R n) : Prop :=
  ∀ i, Δ i = none ∨ ∃ A, Δ i = some (.grad A 0)

/-- `[Γ]`: only graded assumptions. -/
def GIsGraded {n : ℕ} (Γ : GrCtx R n) : Prop := ∀ i A, Γ i ≠ some (.lin A)

/-- Scaling an assumption by a grade. -/
def GAssm.scale (r : R) : GAssm R → GAssm R
  | .lin A => .lin A
  | .grad A s => .grad A (r * s)

/-- `r * Γ`. -/
def gscale {n : ℕ} (r : R) (Γ : GrCtx R n) : GrCtx R n := fun i => (Γ i).map (GAssm.scale r)

end Ops

variable [Semiring R] [Preorder R]

/-- The typing judgement `Γ ⊢ t : A` of GrCore with data types, Granule style. -/
inductive GTyped (sig : GSig R) (hs : R → R → Option R) :
    {n : ℕ} → GrCtx R n → GTerm n → GTy R → Prop
  | var {n : ℕ} {Γ : GrCtx R n} {i : Fin n} {A : GTy R} :
      Γ i = some (.lin A) → (∀ j, j ≠ i → Γ j = none) → GTyped sig hs Γ (.var i) A
  | lam {n : ℕ} {Γ : GrCtx R n} {t : GTerm (n + 1)} {A B : GTy R} :
      GTyped sig hs (Ctx.cons (some (.lin A)) Γ) t B → GTyped sig hs Γ (.lam t) (.lolli A B)
  | app {n : ℕ} {Γ₁ Γ₂ Γ : GrCtx R n} {t₁ t₂ : GTerm n} {A B : GTy R} :
      GTyped sig hs Γ₁ t₁ (.lolli A B) → GTyped sig hs Γ₂ t₂ A → GCtxAdd Γ₁ Γ₂ Γ →
      GTyped sig hs Γ (.app t₁ t₂) B
  | der {n : ℕ} {Γ : GrCtx R n} {t : GTerm n} {A B : GTy R} {i : Fin n} :
      GTyped sig hs Γ t B → Γ i = some (.lin A) →
      GTyped sig hs (Function.update Γ i (some (.grad A 1))) t B
  | weak {n : ℕ} {Γ Δ Γ' : GrCtx R n} {t : GTerm n} {A : GTy R} :
      GTyped sig hs Γ t A → GIsZeroCtx Δ → GCtxAdd Γ Δ Γ' → GTyped sig hs Γ' t A
  | approx {n : ℕ} {Γ : GrCtx R n} {t : GTerm n} {A B : GTy R} {i : Fin n} {r s : R} :
      GTyped sig hs Γ t B → Γ i = some (.grad A r) → r ≤ s →
      GTyped sig hs (Function.update Γ i (some (.grad A s))) t B
  | pr {n : ℕ} {Γ : GrCtx R n} {t : GTerm n} {A : GTy R} (r : R) :
      GTyped sig hs Γ t A → GIsGraded Γ → GTyped sig hs (gscale r Γ) (.box t) (.box r A)
  | unit {n : ℕ} {Γ : GrCtx R n} : (∀ i, Γ i = none) → GTyped sig hs Γ .unit .unit
  | pair {n : ℕ} {Γ₁ Γ₂ Γ : GrCtx R n} {t₁ t₂ : GTerm n} {A B : GTy R} :
      GTyped sig hs Γ₁ t₁ A → GTyped sig hs Γ₂ t₂ B → GCtxAdd Γ₁ Γ₂ Γ →
      GTyped sig hs Γ (.pair t₁ t₂) (.tensor A B)
  | letPat {n k : ℕ} {Γ₁ Γ₂ Γ : GrCtx R n} {Δ : GrCtx R k} {p : GPat k} {t₁ : GTerm n}
      {t₂ : GTerm (n + k)} {A B : GTy R} :
      GTyped sig hs Γ₁ t₁ A → GPatTy sig hs none p A Δ → GTyped sig hs (Ctx.append Γ₂ Δ) t₂ B →
      GCtxAdd Γ₁ Γ₂ Γ → GTyped sig hs Γ (.letPat p t₁ t₂) B
  /-- `(CON)`: a constructor `c` of `data d i` with fields `As` has type
  `A₁ ⊸ ⋯ ⊸ Aₘ ⊸ data d i`. -/
  | con {n : ℕ} {Γ : GrCtx R n} {c d i : ℕ} {As : List (GTy R)} :
      sig.fields d i c = some As → (∀ j, Γ j = none) →
      GTyped sig hs Γ (.con c) (GTy.conTy As (.data d i))
  /-- `(CASE)`: every branch is checked in the same context `Γ₂` (extended by the variables
  its pattern binds). -/
  | case {n m : ℕ} {Γ₁ Γ₂ Γ : GrCtx R n} {t : GTerm n} {ks : Fin m → ℕ}
      {ps : (j : Fin m) → GPat (ks j)} {us : (j : Fin m) → GTerm (n + ks j)}
      {Δs : (j : Fin m) → GrCtx R (ks j)} {A B : GTy R} :
      GTyped sig hs Γ₁ t A → (∀ j, GPatTy sig hs none (ps j) A (Δs j)) →
      (∀ j, GTyped sig hs (Ctx.append Γ₂ (Δs j)) (us j) B) → GCtxAdd Γ₁ Γ₂ Γ →
      GTyped sig hs Γ (.case t ks ps us) B

end LinExp

end
