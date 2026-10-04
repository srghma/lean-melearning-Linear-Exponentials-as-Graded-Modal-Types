module

public import RequestProject.Sec2_CoreCalculus.Syntax

/-!
# Section 2: surface syntax `[grcore| … ]` for GrCore terms

Terms can be written with *named* variables; the quotation is translated into the de Bruijn
representation `Term n`.  A quotation without context produces a closed term (`Term 0`);
free variables can be declared in front of `⊢`, the last one being the innermost:

* `[grcore| λ z. let [(x, y)] = z in ([x], [y]) ] : Term 0`
* `[grcore| a b ⊢ (a, b) ] : Term 2`   (here `b` is index `0` and `a` index `1`)

Syntax (the identifier `unit` is reserved for the unit term and the unit pattern):
```
t ::= x | λ x. t | t t | (t, t) | unit | [t] | let p = t in t | (t)
p ::= x | (p, p) | [p] | unit
```
-/

@[expose] public section

namespace LinExp

declare_syntax_cat grpat
declare_syntax_cat grterm

syntax ident : grpat
syntax "(" grpat ", " grpat ")" : grpat
syntax "[" grpat "]" : grpat

syntax ident : grterm
syntax "(" grterm ", " grterm ")" : grterm
syntax "(" grterm ")" : grterm
syntax "[" grterm "]" : grterm
syntax:20 "λ " ident ". " grterm:20 : grterm
syntax:20 "let " grpat " = " grterm " in " grterm:20 : grterm
syntax:70 grterm:70 grterm:71 : grterm

open Lean in
/-- Translate a pattern; returns the pattern and its bound names, from left to right. -/
meta partial def elabGrPat : TSyntax `grpat → MacroM (TSyntax `term × List Name)
  | `(grpat| $x:ident) =>
      if x.getId == `unit then return (← `(Pat.unit), []) else return (← `(Pat.var), [x.getId])
  | `(grpat| ($p, $q)) => do
      let (p', xs) ← elabGrPat p
      let (q', ys) ← elabGrPat q
      return (← `(Pat.pair $p' $q'), xs ++ ys)
  | `(grpat| [$p]) => do
      let (p', xs) ← elabGrPat p
      return (← `(Pat.box $p'), xs)
  | _ => Macro.throwUnsupported

open Lean in
/-- Translate a term; `ctx` lists the names in scope, innermost first. -/
meta partial def elabGrTerm (ctx : List Name) : TSyntax `grterm → MacroM (TSyntax `term)
  | `(grterm| $x:ident) => do
      if x.getId == `unit then return ← `(Term.unit)
      match ctx.idxOf? x.getId with
      | some i =>
        let n := Syntax.mkNumLit (toString ctx.length)
        let i := Syntax.mkNumLit (toString i)
        `(Term.var (n := $n) ⟨$i, by decide⟩)
      | none => Macro.throwErrorAt x s!"grcore: unbound variable {x.getId}"
  | `(grterm| ($t, $u)) => do `(Term.pair $(← elabGrTerm ctx t) $(← elabGrTerm ctx u))
  | `(grterm| ($t)) => elabGrTerm ctx t
  | `(grterm| [$t]) => do `(Term.box $(← elabGrTerm ctx t))
  | `(grterm| λ $x. $t) => do `(Term.lam $(← elabGrTerm (x.getId :: ctx) t))
  | `(grterm| let $p = $t in $u) => do
      let (p', xs) ← elabGrPat p
      `(Term.letPat $p' $(← elabGrTerm ctx t) $(← elabGrTerm (xs.reverse ++ ctx) u))
  | `(grterm| $t $u) => do `(Term.app $(← elabGrTerm ctx t) $(← elabGrTerm ctx u))
  | _ => Macro.throwUnsupported

/-- `[grcore| t ]`: a closed GrCore term written with named variables. -/
syntax "[grcore| " grterm " ]" : term
/-- `[grcore| x₁ … xₙ ⊢ t ]`: a GrCore term in `Term n` with free variables `x₁ … xₙ`
(`xₙ` is de Bruijn index `0`). -/
syntax "[grcore| " ident* " ⊢ " grterm " ]" : term

macro_rules
  | `([grcore| $t:grterm ]) => do `(($(← elabGrTerm [] t) : Term 0))
  | `([grcore| $xs:ident* ⊢ $t:grterm ]) => do
      let ctx := (xs.map (·.getId)).toList.reverse
      let n := Lean.Syntax.mkNumLit (toString ctx.length)
      `(($(← elabGrTerm ctx t) : Term $n))

/-- The term `push` of the introduction: `λ z. let [(x, y)] = z in ([x], [y])`. -/
example : [grcore| λ z. let [(x, y)] = z in ([x], [y]) ] =
    Term.lam (Term.letPat (Pat.box (Pat.pair Pat.var Pat.var)) (Term.var 0)
      (Term.pair (Term.box (Term.var 1)) (Term.box (Term.var 0)))) := rfl

example : [grcore| a b ⊢ (a, b) ] = Term.pair (Term.var 1) (Term.var 0) := rfl

example : [grcore| λ u. let unit = u in unit ] =
    Term.lam (Term.letPat Pat.unit (Term.var 0) Term.unit) := rfl

example : [grcore| λ f. λ x. f x ] = Term.lam (Term.lam (Term.app (Term.var 1) (Term.var 0))) :=
  rfl

end LinExp

end
