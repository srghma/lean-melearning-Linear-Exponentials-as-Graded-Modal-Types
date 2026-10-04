module

public import RequestProject.Sec4_Solution.NoneOneTons

/-!
# Section 5: GrCore with user-defined data types (ADTs and GADTs)

Section 5 says that Granule "has a more general notion of type constructors than we defined in
our calculus here, including user defined algebraic data types (ADTs) as well as generalised
algebraic data types (GADTs)", and that `⋉` "is applied whenever a pattern match occurs against
a constructor with at least one sub-pattern".  This file extends the syntax of GrCore with such
data types.

* Types gain `data d i`: the data type named `d : ℕ` at the (GADT) index `i : ℕ`.  Plain ADTs
  simply ignore the index.  Type parameters (`Maybe a`) are handled by monomorphisation: each
  instance is its own data-type name.
* The data types in scope are described by a *signature* `GSig G`: `fields d i c` is the list
  of argument types of constructor `c` when it builds a value of `data d i`, or `none` when
  `c` cannot build a value of that type.  The index dependence is what makes this a GADT: e.g.
  `Nil : Vec 0`, `Cons : a ⊸ Vec n ⊸ Vec (n+1)`.
* Constructors are first-class terms `con c` (of type `A₁ ⊸ ⋯ ⊸ Aₘ ⊸ data d i`), as in
  Granule; constructor patterns are `con c [p₁, …, pₘ]`.
* Besides `let p = t in u`, there is an `m`-way `case t of p₁ ↦ u₁ | ⋯ | pₘ ↦ uₘ`.

All syntax is generic in the type `G` of grades appearing in types: Section 5's constraint
generation (`Constraints/`) runs on types whose grades are grade *expressions* with variables.

As in Section 2, terms use de Bruijn indices (`GTerm n`, with `GTerm 0` the closed terms), and
patterns are indexed by the number of variables they bind (`GPat k`).
-/

@[expose] public section

namespace LinExp

/-- Types of GrCore extended with data types:
`A, B ::= α | 1 | A ⊸ B | A ⊗ B | □_r A | data d i`. -/
inductive GTy (G : Type) : Type where
  | atom : ℕ → GTy G
  | unit : GTy G
  | lolli : GTy G → GTy G → GTy G
  | tensor : GTy G → GTy G → GTy G
  | box : G → GTy G → GTy G
  /-- the data type named `d` at GADT index `i` -/
  | data : ℕ → ℕ → GTy G
  deriving DecidableEq

namespace GTy

/-- Change the grades occurring in a type. -/
def map {G H : Type} (f : G → H) : GTy G → GTy H
  | atom a => atom a
  | unit => unit
  | lolli A B => lolli (map f A) (map f B)
  | tensor A B => tensor (map f A) (map f B)
  | box r A => box (f r) (map f A)
  | data d i => data d i

/-- `A₁ ⊸ ⋯ ⊸ Aₘ ⊸ B`: the type of a constructor with argument types `As`. -/
def conTy {G : Type} (As : List (GTy G)) (B : GTy G) : GTy G := As.foldr lolli B

/-- The embedding of the types of Section 2. -/
def ofTy {R : Type} : Ty R → GTy R
  | .atom a => atom a
  | .unit => unit
  | .lolli A B => lolli (ofTy A) (ofTy B)
  | .tensor A B => tensor (ofTy A) (ofTy B)
  | .box r A => box r (ofTy A)

@[simp] lemma map_id {G : Type} (A : GTy G) : A.map id = A := by
  induction A <;> simp_all [map]

end GTy

/-- A signature of (generalised) algebraic data types: `fields d i c = some [A₁, …, Aₘ]`
means that constructor `c` has type `A₁ ⊸ ⋯ ⊸ Aₘ ⊸ data d i`; `none` means that `c` does not
construct values of type `data d i`. -/
structure GSig (G : Type) where
  fields : ℕ → ℕ → ℕ → Option (List (GTy G))

/-- Change the grades occurring in a signature. -/
def GSig.map {G H : Type} (f : G → H) (sig : GSig G) : GSig H where
  fields d i c := (sig.fields d i c).map (List.map (GTy.map f))

mutual

/-- Patterns, indexed by the number of variables they bind:
`p ::= x | (p₁, p₂) | [p] | unit | c p₁ ⋯ pₘ`. -/
inductive GPat : ℕ → Type where
  | var : GPat 1
  | pair {k₁ k₂ : ℕ} : GPat k₁ → GPat k₂ → GPat (k₁ + k₂)
  | box {k : ℕ} : GPat k → GPat k
  | unit : GPat 0
  /-- a constructor pattern `c p₁ ⋯ pₘ` -/
  | con {k : ℕ} : ℕ → GPats k → GPat k

/-- Lists of sub-patterns, indexed by the total number of variables they bind; the variables
of later sub-patterns are the innermost ones (as for `(p₁, p₂)`). -/
inductive GPats : ℕ → Type where
  | nil : GPats 0
  | cons {k₁ k₂ : ℕ} : GPat k₁ → GPats k₂ → GPats (k₁ + k₂)

end

/-- Does a list of sub-patterns have at least one element? -/
def GPats.nonempty : {k : ℕ} → GPats k → Bool
  | _, .nil => false
  | _, .cons _ _ => true

/-- Terms with `n` free de Bruijn indices.  `case t ks ps us` is
`case t of p₀ ↦ u₀ | ⋯ | p_{m-1} ↦ u_{m-1}`, where branch `j` binds `ks j` variables. -/
inductive GTerm : ℕ → Type where
  | var {n : ℕ} : Fin n → GTerm n
  | lam {n : ℕ} : GTerm (n + 1) → GTerm n
  | app {n : ℕ} : GTerm n → GTerm n → GTerm n
  | pair {n : ℕ} : GTerm n → GTerm n → GTerm n
  | unit {n : ℕ} : GTerm n
  | box {n : ℕ} : GTerm n → GTerm n
  | letPat {n k : ℕ} : GPat k → GTerm n → GTerm (n + k) → GTerm n
  /-- a data constructor, used as a (curried, linear) function -/
  | con {n : ℕ} : ℕ → GTerm n
  /-- `case t of p₀ ↦ u₀ | ⋯ | p_{m-1} ↦ u_{m-1}` -/
  | case {n m : ℕ} (t : GTerm n) (ks : Fin m → ℕ) (ps : (j : Fin m) → GPat (ks j))
      (us : (j : Fin m) → GTerm (n + ks j)) : GTerm n

/-- The embedding of the patterns of Section 2. -/
def GPat.ofPat : {k : ℕ} → Pat k → GPat k
  | _, .var => .var
  | _, .pair p q => .pair (ofPat p) (ofPat q)
  | _, .box p => .box (ofPat p)
  | _, .unit => .unit

/-- The embedding of the terms of Section 2. -/
def GTerm.ofTerm : {n : ℕ} → Term n → GTerm n
  | _, .var i => .var i
  | _, .lam t => .lam (ofTerm t)
  | _, .app t u => .app (ofTerm t) (ofTerm u)
  | _, .pair t u => .pair (ofTerm t) (ofTerm u)
  | _, .unit => .unit
  | _, .box t => .box (ofTerm t)
  | _, .letPat p t u => .letPat (GPat.ofPat p) (ofTerm t) (ofTerm u)

end LinExp

end
