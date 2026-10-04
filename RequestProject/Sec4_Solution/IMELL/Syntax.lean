module

public import RequestProject.Sec2_CoreCalculus.Context

/-!
# Section 4: IMELL with Benton et al.'s term assignment

Intuitionistic Multiplicative Exponential Linear Logic, with the term assignment of Benton,
Bierman, de Paiva and Hyland ("A term calculus for intuitionistic linear logic", 1993),
restricted to the multiplicative-exponential fragment:

```
M, N ::= x | λx.M | M N | * | let M be * in N | M ⊗ N | let M be x ⊗ y in N
       | promote M₁, …, Mₖ for x₁, …, xₖ in N | derelict M | discard M in N
       | copy M as x, y in N
```

Terms use de Bruijn indices (`ITerm n`).  In `promote Ms for xs in N` the body `N : ITerm k`
only has the `k` variables `x₁ … xₖ` free; `xⱼ` is index `j`.  In `let M be x ⊗ y in N` and
`copy M as x, y in N`, `y` is index `0` and `x` index `1` of `N`.
-/

@[expose] public section

namespace LinExp

/-- IMELL formulas: atoms, `I`, `A ⊸ B`, `A ⊗ B`, `!A`. -/
inductive ITy : Type where
  | atom : ℕ → ITy
  | unit : ITy
  | lolli : ITy → ITy → ITy
  | tensor : ITy → ITy → ITy
  | bang : ITy → ITy
  deriving DecidableEq

/-- IMELL terms (Benton et al.'s term assignment) with `n` free de Bruijn indices. -/
inductive ITerm : ℕ → Type where
  | var {n : ℕ} : Fin n → ITerm n
  | lam {n : ℕ} : ITerm (n + 1) → ITerm n
  | app {n : ℕ} : ITerm n → ITerm n → ITerm n
  /-- `*` -/
  | star {n : ℕ} : ITerm n
  /-- `let M be * in N` -/
  | letStar {n : ℕ} : ITerm n → ITerm n → ITerm n
  /-- `M ⊗ N` -/
  | pair {n : ℕ} : ITerm n → ITerm n → ITerm n
  /-- `let M be x ⊗ y in N` -/
  | letPair {n : ℕ} : ITerm n → ITerm (n + 2) → ITerm n
  /-- `promote M₁, …, Mₖ for x₁, …, xₖ in N` -/
  | promote {n k : ℕ} : (Fin k → ITerm n) → ITerm k → ITerm n
  /-- `derelict M` -/
  | derelict {n : ℕ} : ITerm n → ITerm n
  /-- `discard M in N` -/
  | discard {n : ℕ} : ITerm n → ITerm n → ITerm n
  /-- `copy M as x, y in N` -/
  | copy {n : ℕ} : ITerm n → ITerm (n + 2) → ITerm n

namespace ITerm

/-- Renaming of free variables. -/
def rename {n m : ℕ} (ρ : Fin n → Fin m) : ITerm n → ITerm m
  | var i => var (ρ i)
  | lam M => lam (rename (Ctx.liftN 1 ρ) M)
  | app M N => app (rename ρ M) (rename ρ N)
  | star => star
  | letStar M N => letStar (rename ρ M) (rename ρ N)
  | pair M N => pair (rename ρ M) (rename ρ N)
  | letPair M N => letPair (rename ρ M) (rename (Ctx.liftN 2 ρ) N)
  | promote Ms N => promote (fun j => rename ρ (Ms j)) N
  | derelict M => derelict (rename ρ M)
  | discard M N => discard (rename ρ M) (rename ρ N)
  | copy M N => copy (rename ρ M) (rename (Ctx.liftN 2 ρ) N)

end ITerm

end LinExp

end
