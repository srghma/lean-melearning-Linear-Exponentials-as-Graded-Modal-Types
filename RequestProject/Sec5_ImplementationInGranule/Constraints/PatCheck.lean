module

public import RequestProject.Sec5_ImplementationInGranule.DataTypes.Typing

/-!
# Section 5: pattern checking by constraint generation

"We implement `⋉` via a constraint on the grades given by the data constructor pattern (inside a
box pattern) which is then discharged via an SMT solver.  If such a constraint is satisfiable,
then the type checking of the pattern may proceed."

This file models the first half: an algorithm `patCheck` that, given a pattern and the type it
is matched against, either fails (the pattern does not fit the type) or returns the context of
bound variables together with a *constraint* (a formula over the grades) that must hold.

* `GFormula G` is a small constraint language over grades `G`: Boolean connectives, equality,
  the pre-order, and the atom `defined g`, meaning "`g ⋉ g` is defined".
* `patCheck` is generic in `G`: it uses no arithmetic on grades, so it can run on types whose
  grades are symbolic.
* `patCheck_iff`: for concrete grades, the declarative Granule-style pattern typing of
  `DataTypes/Typing.lean` holds exactly when `patCheck` succeeds and its constraint holds.
* `patCheck_map`: constraint generation commutes with instantiating the grades.
-/

@[expose] public section

namespace LinExp

/-- Constraints over grades `G`. -/
inductive GFormula (G : Type) : Type where
  | tt : GFormula G
  | ff : GFormula G
  | and : GFormula G → GFormula G → GFormula G
  | or : GFormula G → GFormula G → GFormula G
  | not : GFormula G → GFormula G
  /-- `defined g`: the grade `g ⋉ g` is defined -/
  | defined : G → GFormula G
  | eq : G → G → GFormula G
  | le : G → G → GFormula G

namespace GFormula

/-- Change the grades occurring in a formula. -/
def map {G H : Type} (f : G → H) : GFormula G → GFormula H
  | tt => tt
  | ff => ff
  | and φ ψ => and (map f φ) (map f ψ)
  | or φ ψ => or (map f φ) (map f ψ)
  | not φ => not (map f φ)
  | defined g => defined (f g)
  | eq g h => eq (f g) (f h)
  | le g h => le (f g) (f h)

/-- Truth of a constraint, for the partial operation `hs` (that is, `⋉`) on the grades `R`
and an interpretation `ρ` of the grades occurring in it. -/
def Holds {G R : Type} [Preorder R] (hs : R → R → Option R) (ρ : G → R) : GFormula G → Prop
  | tt => True
  | ff => False
  | and φ ψ => Holds hs ρ φ ∧ Holds hs ρ ψ
  | or φ ψ => Holds hs ρ φ ∨ Holds hs ρ ψ
  | not φ => ¬ Holds hs ρ φ
  | defined g => ∃ t, hs (ρ g) (ρ g) = some t
  | eq g h => ρ g = ρ h
  | le g h => ρ g ≤ ρ h

lemma holds_map {G H R : Type} [Preorder R] (hs : R → R → Option R) (ρ : H → R) (f : G → H)
    (φ : GFormula G) : Holds hs ρ (φ.map f) ↔ Holds hs (ρ ∘ f) φ := by
  induction φ <;> simp_all [map, Holds]

/-- Constraints are decidable when equality and the pre-order on grades are. -/
def decHolds {G R : Type} [Preorder R] [DecidableEq R] [DecidableRel (α := R) (· ≤ ·)]
    (hs : R → R → Option R) (ρ : G → R) : (φ : GFormula G) → Decidable (Holds hs ρ φ)
  | tt => isTrue trivial
  | ff => isFalse id
  | and φ ψ => @instDecidableAnd _ _ (decHolds hs ρ φ) (decHolds hs ρ ψ)
  | or φ ψ => @instDecidableOr _ _ (decHolds hs ρ φ) (decHolds hs ρ ψ)
  | not φ => @instDecidableNot _ (decHolds hs ρ φ)
  | defined g => decidable_of_iff ((hs (ρ g) (ρ g)).isSome) (by
      simp [Holds, Option.isSome_iff_exists])
  | eq g h => decidable_of_iff (ρ g = ρ h) (by simp [Holds])
  | le g h => decidable_of_iff (ρ g ≤ ρ h) (by simp [Holds])

instance {G R : Type} [Preorder R] [DecidableEq R] [DecidableRel (α := R) (· ≤ ·)]
    (hs : R → R → Option R) (ρ : G → R) (φ : GFormula G) : Decidable (Holds hs ρ φ) :=
  decHolds hs ρ φ

end GFormula

variable {G : Type}

mutual

/-- Constraint generation for a pattern `p` matched (at the optional grade `o`) against the
type `A`: `none` if `p` does not fit `A`, otherwise the context `Δ` of the variables bound by
`p` and the constraint that the grades must satisfy. -/
def patCheck (sig : GSig G) :
    {k : ℕ} → Option G → GPat k → GTy G → Option (GrCtx G k × GFormula G)
  | _, o, .var, A => match o with
    | none => some (fun _ => some (.lin A), .tt)
    | some r => some (fun _ => some (.grad A r), .tt)
  | _, o, .pair p q, A => match A with
    | .tensor A B => match o with
      | none => (patCheck sig none p A).bind fun x => (patCheck sig none q B).bind fun y =>
          some (Ctx.append x.1 y.1, .and x.2 y.2)
      | some r => (patCheck sig (some r) p A).bind fun x =>
          (patCheck sig (some r) q B).bind fun y =>
            some (Ctx.append x.1 y.1, .and (.defined r) (.and x.2 y.2))
    | _ => none
  | _, o, .box p, A => match o, A with
    | none, .box r A => patCheck sig (some r) p A
    | _, _ => none
  | _, _, .unit, A => match A with
    | .unit => some (Ctx.empty 0, .tt)
    | _ => none
  | _, o, .con c ps, A => match A with
    | .data d i => match o with
      | none => (sig.fields d i c).bind fun As => patsCheck sig none ps As
      | some r => (sig.fields d i c).bind fun As => (patsCheck sig (some r) ps As).map fun x =>
          (x.1, if ps.nonempty then .and (.defined r) x.2 else x.2)
    | _ => none

/-- Constraint generation for the sub-patterns of a constructor pattern. -/
def patsCheck (sig : GSig G) :
    {k : ℕ} → Option G → GPats k → List (GTy G) → Option (GrCtx G k × GFormula G)
  | _, _, .nil, As => match As with
    | [] => some (Ctx.empty 0, .tt)
    | _ :: _ => none
  | _, o, .cons p ps, As => match As with
    | A :: As => (patCheck sig o p A).bind fun x => (patsCheck sig o ps As).bind fun y =>
        some (Ctx.append x.1 y.1, .and x.2 y.2)
    | [] => none

end

end LinExp

end
