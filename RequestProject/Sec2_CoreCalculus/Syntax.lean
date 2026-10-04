module

public import RequestProject.Sec2_CoreCalculus.Context

/-!
# Section 2: syntax of GrCore

Types, patterns and terms of the core calculus GrCore (the linear λ-calculus with products,
units, pattern matching and a semiring-graded necessity modality `□_r A`).

* Terms use de Bruijn indices: `Term n` is the type of terms with (at most) `n` free
  variables, so `Term 0` is the type of closed terms.
* Patterns are indexed by the number of variables they bind: `Pat k`.
* `let p = t₁ in t₂` binds the `k` variables of `p : Pat k` in `t₂ : Term (n + k)`.  The
  variables of a pattern are numbered from right to left: in the pattern `(x, y)` the variable
  `y` gets index `0` and `x` gets index `1` (this matches the paper's context `Γ, x, y`).

The paper's calculus is monomorphic and has no base types.  We add *atomic* types
`Ty.atom i` (type variables, as in Granule): without them every type of the calculus (and
every IMELL formula built from the unit) is inhabited, which would make the expressivity
statements of Section 4 trivial.
-/

@[expose] public section

namespace LinExp

/-- Types of GrCore over a semiring of grades `R`:
`A, B ::= α | 1 | A ⊸ B | A ⊗ B | □_r A`. -/
inductive Ty (R : Type) : Type where
  /-- atomic (base) types -/
  | atom : ℕ → Ty R
  /-- the unit type `1` -/
  | unit : Ty R
  /-- linear functions `A ⊸ B` -/
  | lolli : Ty R → Ty R → Ty R
  /-- multiplicative products `A ⊗ B` -/
  | tensor : Ty R → Ty R → Ty R
  /-- the graded necessity modality `□_r A` -/
  | box : R → Ty R → Ty R
  deriving DecidableEq

@[inherit_doc] scoped infixr:25 " ⊸ " => Ty.lolli
@[inherit_doc] scoped infixl:35 " ⊗ " => Ty.tensor
@[inherit_doc] scoped notation "□[" r "] " A:max => Ty.box r A

/-- Patterns, indexed by the number of variables they bind:
`p ::= x | (p₁, p₂) | [p] | unit`. -/
inductive Pat : ℕ → Type where
  /-- a variable pattern `x` -/
  | var : Pat 1
  /-- a product pattern `(p₁, p₂)`; the variables of `p₂` are the innermost ones -/
  | pair {k₁ k₂ : ℕ} : Pat k₁ → Pat k₂ → Pat (k₁ + k₂)
  /-- a box (unboxing) pattern `[p]` -/
  | box {k : ℕ} : Pat k → Pat k
  /-- the unit pattern -/
  | unit : Pat 0

/-- Terms with `n` free de Bruijn indices:
`t ::= x | λx.t | t₁ t₂ | (t₁, t₂) | unit | [t] | let p = t₁ in t₂`. -/
inductive Term : ℕ → Type where
  | var {n : ℕ} : Fin n → Term n
  | lam {n : ℕ} : Term (n + 1) → Term n
  | app {n : ℕ} : Term n → Term n → Term n
  | pair {n : ℕ} : Term n → Term n → Term n
  | unit {n : ℕ} : Term n
  /-- promotion `[t]` -/
  | box {n : ℕ} : Term n → Term n
  /-- pattern matching `let p = t₁ in t₂` -/
  | letPat {n k : ℕ} : Pat k → Term n → Term (n + k) → Term n

namespace Term

/-- Renaming of free variables. -/
def rename {n m : ℕ} (ρ : Fin n → Fin m) : Term n → Term m
  | var i => var (ρ i)
  | lam t => lam (rename (Ctx.liftN 1 ρ) t)
  | app t u => app (rename ρ t) (rename ρ u)
  | pair t u => pair (rename ρ t) (rename ρ u)
  | unit => unit
  | box t => box (rename ρ t)
  | letPat (k := k) p t u => letPat p (rename ρ t) (rename (Ctx.liftN k ρ) u)

/-- Weakening: shift all free variables up by one. -/
def shift {n : ℕ} (t : Term n) : Term (n + 1) := rename Fin.succ t

end Term

end LinExp

end
