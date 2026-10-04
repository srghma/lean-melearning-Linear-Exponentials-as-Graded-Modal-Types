module

public import RequestProject.Sec5_ImplementationInGranule.Constraints.Instantiate

/-!
# Section 5: discharging the constraints (grade polymorphism and a decision procedure)

In Granule, grades in types may be variables (as in `∀ {r : LNL} . (a, b) [r] → …`), so the
constraints produced by pattern checking mention grade variables, and they are handed to an
SMT solver.  We model this as follows.

* `GExp R V`: grade expressions, either a literal grade of `R` or a variable from `V`.  A
  *valuation* `ρ : V → R` instantiates them (`GExp.eval ρ`).
* Pattern checking runs once, symbolically, on the types over `GExp R V`
  (`patCheck`), and the result is correct for every instance (`patTy_instance_iff`).
* `Satisfiable` / `Valid`: the constraint holds for some / for all valuations.  The paper says
  pattern checking proceeds when the constraint is *satisfiable*; `patTy_some_instance_iff`
  shows this means "the pattern can be typed at some instantiation of the grade variables",
  and `patTy_all_instances_iff` shows that validity means "at every instantiation".
* When `V` and `R` are finite (as for `LNL`), both are decidable (by enumerating valuations):
  this is our stand-in for the SMT solver.  `checkPatSat` / `checkPatValid` are the resulting
  executable checkers, with correctness theorems `checkPatSat_iff` and `checkPatValid_iff`.
-/

@[expose] public section

namespace LinExp

/-- Grade expressions: literals and grade variables. -/
inductive GExp (R V : Type) : Type where
  | lit : R → GExp R V
  | var : V → GExp R V
  deriving DecidableEq

/-- Instantiate a grade expression with a valuation of the grade variables. -/
def GExp.eval {R V : Type} (ρ : V → R) : GExp R V → R
  | lit r => r
  | var v => ρ v

variable {R V : Type} [Preorder R]

namespace GFormula

/-- A constraint is *satisfiable* if it holds for some valuation of its grade variables. -/
def Satisfiable (hs : R → R → Option R) (φ : GFormula (GExp R V)) : Prop :=
  ∃ ρ : V → R, φ.Holds hs (GExp.eval ρ)

/-- A constraint is *valid* if it holds for every valuation of its grade variables. -/
def Valid (hs : R → R → Option R) (φ : GFormula (GExp R V)) : Prop :=
  ∀ ρ : V → R, φ.Holds hs (GExp.eval ρ)

variable [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R] [DecidableRel (α := R) (· ≤ ·)]

instance (hs : R → R → Option R) (φ : GFormula (GExp R V)) : Decidable (φ.Satisfiable hs) :=
  by unfold Satisfiable; infer_instance

instance (hs : R → R → Option R) (φ : GFormula (GExp R V)) : Decidable (φ.Valid hs) :=
  by unfold Valid; infer_instance

end GFormula

variable (sig : GSig (GExp R V)) (hs : R → R → Option R)

/-- **Symbolic pattern checking is correct at every instance.**  Matching `p` against an
instance of `A` (under the same instance of the signature and of `o`) succeeds with `Δ'`
exactly when the symbolic check succeeds with some `Δ` whose instance is `Δ'`, and the
symbolic constraint holds at that valuation. -/
theorem patTy_instance_iff {k : ℕ} (ρ : V → R) (o : Option (GExp R V)) (p : GPat k)
    (A : GTy (GExp R V)) (Δ' : GrCtx R k) :
    GPatTy (sig.map (GExp.eval ρ)) hs (o.map (GExp.eval ρ)) p (A.map (GExp.eval ρ)) Δ' ↔
      ∃ Δ φ, patCheck sig o p A = some (Δ, φ) ∧ Δ' = Δ.map (GExp.eval ρ) ∧
        φ.Holds hs (GExp.eval ρ) := by
  rw [patCheck_iff, patCheck_map]
  constructor
  · rintro ⟨φ', h, hφ'⟩
    obtain ⟨⟨Δ, φ⟩, e, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨Δ, φ, e, rfl, by simpa [GFormula.holds_map] using hφ'⟩
  · rintro ⟨Δ, φ, e, rfl, hφ⟩
    exact ⟨φ.map (GExp.eval ρ), by simp [e], by simpa [GFormula.holds_map] using hφ⟩

/-- Pattern checking succeeds at *some* instantiation of the grade variables exactly when the
symbolic check succeeds with a *satisfiable* constraint. -/
theorem patTy_some_instance_iff {k : ℕ} (o : Option (GExp R V)) (p : GPat k)
    (A : GTy (GExp R V)) :
    (∃ ρ : V → R, ∃ Δ',
        GPatTy (sig.map (GExp.eval ρ)) hs (o.map (GExp.eval ρ)) p (A.map (GExp.eval ρ)) Δ') ↔
      ∃ Δ φ, patCheck sig o p A = some (Δ, φ) ∧ φ.Satisfiable hs := by
  constructor
  · rintro ⟨ρ, Δ', h⟩
    obtain ⟨Δ, φ, e, -, hφ⟩ := (patTy_instance_iff sig hs ρ o p A Δ').mp h
    exact ⟨Δ, φ, e, ρ, hφ⟩
  · rintro ⟨Δ, φ, e, ρ, hφ⟩
    exact ⟨ρ, _, (patTy_instance_iff sig hs ρ o p A _).mpr ⟨Δ, φ, e, rfl, hφ⟩⟩

/-- Pattern checking succeeds at *every* instantiation of the grade variables exactly when the
symbolic check succeeds with a *valid* constraint. -/
theorem patTy_all_instances_iff [Nonempty R] {k : ℕ} (o : Option (GExp R V)) (p : GPat k)
    (A : GTy (GExp R V)) :
    (∀ ρ : V → R, ∃ Δ',
        GPatTy (sig.map (GExp.eval ρ)) hs (o.map (GExp.eval ρ)) p (A.map (GExp.eval ρ)) Δ') ↔
      ∃ Δ φ, patCheck sig o p A = some (Δ, φ) ∧ φ.Valid hs := by
  constructor
  · intro h
    obtain ⟨Δ', h₀⟩ := h (fun _ => Classical.arbitrary R)
    obtain ⟨Δ, φ, e, -, -⟩ := (patTy_instance_iff sig hs _ o p A Δ').mp h₀
    refine ⟨Δ, φ, e, fun ρ => ?_⟩
    obtain ⟨Δ'', hρ⟩ := h ρ
    obtain ⟨Δ₁, φ₁, e₁, -, hφ₁⟩ := (patTy_instance_iff sig hs ρ o p A Δ'').mp hρ
    rw [e] at e₁
    cases e₁
    exact hφ₁
  · rintro ⟨Δ, φ, e, hφ⟩ ρ
    exact ⟨_, (patTy_instance_iff sig hs ρ o p A _).mpr ⟨Δ, φ, e, rfl, hφ ρ⟩⟩

section Checkers

variable [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R] [DecidableRel (α := R) (· ≤ ·)]

/-- Executable pattern checker, accepting when the generated constraint is satisfiable. -/
def checkPatSat {k : ℕ} (o : Option (GExp R V)) (p : GPat k) (A : GTy (GExp R V)) : Bool :=
  match patCheck sig o p A with
  | some (_, φ) => decide (φ.Satisfiable hs)
  | none => false

/-- Executable pattern checker, accepting when the generated constraint is valid. -/
def checkPatValid {k : ℕ} (o : Option (GExp R V)) (p : GPat k) (A : GTy (GExp R V)) : Bool :=
  match patCheck sig o p A with
  | some (_, φ) => decide (φ.Valid hs)
  | none => false

theorem checkPatSat_iff {k : ℕ} (o : Option (GExp R V)) (p : GPat k) (A : GTy (GExp R V)) :
    checkPatSat sig hs o p A = true ↔
      ∃ ρ : V → R, ∃ Δ',
        GPatTy (sig.map (GExp.eval ρ)) hs (o.map (GExp.eval ρ)) p (A.map (GExp.eval ρ)) Δ' := by
  rw [patTy_some_instance_iff, checkPatSat]
  split <;> simp_all

theorem checkPatValid_iff [Nonempty R] {k : ℕ} (o : Option (GExp R V)) (p : GPat k)
    (A : GTy (GExp R V)) :
    checkPatValid sig hs o p A = true ↔
      ∀ ρ : V → R, ∃ Δ',
        GPatTy (sig.map (GExp.eval ρ)) hs (o.map (GExp.eval ρ)) p (A.map (GExp.eval ρ)) Δ' := by
  rw [patTy_all_instances_iff, checkPatValid]
  split <;> simp_all

end Checkers

end LinExp

end
