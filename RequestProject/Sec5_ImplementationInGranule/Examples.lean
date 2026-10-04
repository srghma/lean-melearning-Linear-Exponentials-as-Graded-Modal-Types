module

public import RequestProject.Sec5_ImplementationInGranule.Constraints.Solver
public import RequestProject.Sec5_ImplementationInGranule.DataTypes.Embedding
public import RequestProject.Sec5_ImplementationInGranule.DataTypes.Inversion
public import RequestProject.Sec5_ImplementationInGranule.Granule

/-!
# Section 5: examples (`LNL`, ADTs, GADTs, grade polymorphism)

All examples use the `LNL` semiring (`0`, `1`, `Many`) with `⋉` given by equation (1), i.e.
Granule's setting in Section 5, and the signature `exSig` declaring

```granule
data Maybe a where Nothing : Maybe a; Just : a → Maybe a
data Vec (n : Nat) a where Nil : Vec 0 a; Cons : a → Vec n a → Vec (n + 1) a
```

(with `a` the atom `0`).

* **The paper's example.**  The pattern `[(x, y)]` of `push` cannot be matched against
  `(a, b) [Many]` (`pushPat_many_rejected`), so the program
  `push [(x, y)] = ([x], [y])` at type `(a, b) [Many] → (a [Many], b [Many])` is ill-typed in
  the calculus with data types too (`granule_push_many_ill_typed_dt`); at `[1]` it is accepted
  (`granule_push_one_typed_dt`).
* **ADTs.**  `[Just x]` cannot be matched under `Many` (`justPat_many_rejected`), but the
  nullary `[Nothing]` can (`nothingPat_many_accepted`): "`⋉` is applied whenever a pattern match
  occurs against a constructor with at least one sub-pattern".
* **GADTs.**  `Nil` cannot be matched against `Vec 1 a` (`nilPat_vecOne_rejected`: index
  refinement); `[Cons x Nil]` can be matched against `(Vec 1 a) [1]` but not against
  `(Vec 1 a) [Many]` (`vecOnePat_one_accepted`, `vecOnePat_many_rejected`), and
  `unwrap : (Vec 1 a) [1] → a [1]`, `unwrap [Cons x Nil] = [x]` is well typed
  (`unwrap_typed`).
* **Constructors and `case`.**  `λz. case z of Nothing ↦ Nothing | Just x ↦ Just x` has type
  `Maybe a ⊸ Maybe a` (`maybeId_typed`).
* **Grade polymorphism.**  For `push : ∀ {r : LNL} . (a, b) [r] → (a [r], b [r])` the
  generated constraint "`r ⋉ r` is defined" is satisfiable (by `r = 1`) but not valid
  (`pushPat_poly_satisfiable`, `pushPat_poly_not_valid`), decided by the executable checkers.
-/

@[expose] public section

namespace LinExp

open LNL

instance : Fintype LNL where
  elems := {zero, one, many}
  complete x := by cases x <;> simp

/-- The signature of `Maybe a` (name `0`; constructors `Nothing = 0`, `Just = 1`) and of the
GADT `Vec n a` (name `1`; constructors `Nil = 2 : Vec 0 a`,
`Cons = 3 : a ⊸ Vec n a ⊸ Vec (n+1) a`), with `a` the atom `0`. -/
def exSig {G : Type} : GSig G where
  fields
    | 0, _, 0 => some []
    | 0, _, 1 => some [.atom 0]
    | 1, 0, 2 => some []
    | 1, n + 1, 3 => some [.atom 0, .data 1 n]
    | _, _, _ => none

/-- `⋉` on `LNL`, given by equation (1). -/
abbrev lnlHs : LNL → LNL → Option LNL := HSup.hsup

/-! ### The paper's `push` -/

/-- The pattern `[(x, y)]`. -/
def pushPat : GPat (1 + 1) := .box (.pair .var .var)

/-- `(a, b) [r]` -/
def pushPatTy {G : Type} (r : G) : GTy G := .box r (.tensor (.atom 0) (.atom 1))

theorem pushPat_many_rejected : ¬ ∃ Δ, GPatTy exSig lnlHs none pushPat (pushPatTy ω) Δ := by
  simp [patCheck_iff, pushPat, pushPatTy, patCheck, GFormula.Holds, lnlHs, HSup.hsup, LNL.hsup]

theorem pushPat_one_accepted : ∃ Δ, GPatTy exSig lnlHs none pushPat (pushPatTy (1 : LNL)) Δ := by
  simp [patCheck_iff, pushPat, pushPatTy, patCheck, GFormula.Holds, lnlHs, HSup.hsup, LNL.hsup]

/-- **Section 5's ill-typed Granule program, with data types.**  No program
`push [(x, y)] = u`, i.e. `λz. let [(x, y)] = z in u`, has a type
`(a, b) [Many] → B` in the calculus with data types; in particular the paper's `push` at type
`(a, b) [Many] → (a [Many], b [Many])` is rejected. -/
theorem granule_push_many_ill_typed_dt (u : GTerm (0 + 1 + (1 + 1))) (B : GTy LNL) :
    ¬ GTyped exSig lnlHs (Ctx.empty 0) (.lam (.letPat pushPat (.var 0) u))
      (.lolli (pushPatTy ω) B) :=
  lam_letPat_var_ill_typed pushPat_many_rejected

/-- The paper's `push` term itself (embedded from Section 2) is rejected at `[Many]`. -/
theorem granule_push_many_ill_typed_dt' :
    ¬ GTyped exSig lnlHs (Ctx.empty 0) (GTerm.ofTerm pushTerm)
      (GTy.ofTy (pushTy ω (.atom 0) (.atom 1))) :=
  granule_push_many_ill_typed_dt _ _

/-- At grade `1` the paper's `push` is accepted. -/
theorem granule_push_one_typed_dt :
    GTyped exSig lnlHs (Ctx.empty 0) (GTerm.ofTerm pushTerm)
      (GTy.ofTy (pushTy 1 (.atom 0) (.atom 1))) :=
  grcore_embeds lnl_hsup_diagonal exSig (adj_push_one _ _)

/-! ### ADTs: `Maybe` -/

/-- `[Just x]` -/
def justPat : GPat (1 + 0) := .box (.con 1 (.cons .var .nil))

/-- `[Nothing]` -/
def nothingPat : GPat 0 := .box (.con 0 .nil)

theorem justPat_many_rejected : ¬ ∃ Δ, GPatTy exSig lnlHs none justPat (.box ω (.data 0 0)) Δ := by
  simp [patCheck_iff, justPat, patCheck, patsCheck, exSig, GPats.nonempty, GFormula.Holds,
    lnlHs, HSup.hsup, LNL.hsup]

theorem justPat_one_accepted :
    ∃ Δ, GPatTy exSig lnlHs none justPat (.box (1 : LNL) (.data 0 0)) Δ := by
  simp [patCheck_iff, justPat, patCheck, patsCheck, exSig, GPats.nonempty, GFormula.Holds,
    lnlHs, HSup.hsup, LNL.hsup]

theorem nothingPat_many_accepted :
    GPatTy exSig lnlHs none nothingPat (.box ω (.data 0 0)) (Ctx.empty 0) :=
  .box ω (.con_nullary rfl)

/-! ### GADTs: `Vec` -/

/-- `Nil` -/
def nilPat : GPat 0 := .con 2 .nil

/-- `[Cons x Nil]` -/
def vecOnePat : GPat (1 + (0 + 0)) := .box (.con 3 (.cons .var (.cons nilPat .nil)))

/-- `Nil` does not match a vector of length `1` (GADT index refinement). -/
theorem nilPat_vecOne_rejected (o : Option LNL) :
    ¬ ∃ Δ, GPatTy exSig lnlHs o nilPat (.data 1 1) Δ := by
  cases o <;> simp [patCheck_iff, nilPat, patCheck, exSig]

theorem vecOnePat_one_accepted :
    ∃ Δ, GPatTy exSig lnlHs none vecOnePat (.box (1 : LNL) (.data 1 1)) Δ := by
  simp [patCheck_iff, vecOnePat, nilPat, patCheck, patsCheck, exSig, GPats.nonempty,
    GFormula.Holds, lnlHs, HSup.hsup, LNL.hsup]

theorem vecOnePat_many_rejected :
    ¬ ∃ Δ, GPatTy exSig lnlHs none vecOnePat (.box ω (.data 1 1)) Δ := by
  simp [patCheck_iff, vecOnePat, nilPat, patCheck, patsCheck, exSig, GPats.nonempty,
    GFormula.Holds, lnlHs, HSup.hsup, LNL.hsup]

/-- `unwrap [Cons x Nil] = [x]`, i.e. `λz. let [Cons x Nil] = z in [x]`. -/
def unwrapTerm : GTerm 0 := .lam (.letPat vecOnePat (.var 0) (.box (.var 0)))

/-- `unwrap : (Vec 1 a) [1] → a [1]` is well typed. -/
theorem unwrap_typed :
    GTyped exSig lnlHs (Ctx.empty 0) unwrapTerm
      (.lolli (.box (1 : LNL) (.data 1 1)) (.box 1 (.atom 0))) := by
  refine .lam (.letPat (Γ₁ := Ctx.cons (some (.lin (.box 1 (.data 1 1)))) (Ctx.empty 0))
    (Γ₂ := Ctx.empty _) (.var rfl (fun j hj => absurd (Fin.ext (by omega)) hj))
    (.box 1 (.gcon rfl (fun _ => ⟨1, rfl⟩) (.cons (.gvar 1 _)
      (.cons (.gcon rfl (by simp [GPats.nonempty]) (.nil _)) (.nil _))))) ?_ ?_)
  · let Γ₀ : GrCtx LNL (0 + 1 + (1 + (0 + 0))) :=
      fun j => if j = 0 then some (.lin (.atom 0)) else none
    have hv : GTyped exSig lnlHs Γ₀ (.var 0) (.atom 0) :=
      .var (by simp [Γ₀]) (fun j hj => by simp [Γ₀, hj])
    have hd := GTyped.der (i := 0) (A := .atom 0) hv (by simp [Γ₀])
    have hp := GTyped.pr 1 hd (by
      intro j A
      by_cases hj : j = 0
      · subst hj; simp
      · simp [Γ₀, hj])
    convert hp using 1
    funext j
    match j with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  · intro j
    match j with
    | ⟨0, _⟩ => exact .noneRight _

/-! ### Constructors and `case` -/

/-- Numbers of variables bound by the branches of `case z of Nothing ↦ … | Just x ↦ …`. -/
def maybeKs : Fin 2 → ℕ
  | 0 => 0
  | 1 => 1 + 0

/-- The patterns `Nothing` and `Just x`. -/
def maybePs : (j : Fin 2) → GPat (maybeKs j)
  | 0 => .con 0 .nil
  | 1 => .con 1 (.cons .var .nil)

/-- The branch bodies `Nothing` and `Just x`. -/
def maybeUs : (j : Fin 2) → GTerm (0 + 1 + maybeKs j)
  | 0 => .con 0
  | 1 => .app (.con 1) (.var 0)

/-- `λz. case z of Nothing ↦ Nothing | Just x ↦ Just x`. -/
def maybeIdTerm : GTerm 0 := .lam (.case (.var 0) maybeKs maybePs maybeUs)

/-- The variable contexts bound by the two patterns. -/
def maybeDs : (j : Fin 2) → GrCtx LNL (maybeKs j)
  | 0 => Ctx.empty 0
  | 1 => Ctx.append (fun _ => some (.lin (.atom 0))) (Ctx.empty 0)

/-- `case` and constructors: `λz. case z of Nothing ↦ Nothing | Just x ↦ Just x` has type
`Maybe a ⊸ Maybe a`. -/
theorem maybeId_typed :
    GTyped exSig lnlHs (Ctx.empty 0) maybeIdTerm (.lolli (.data 0 0) (.data 0 0)) := by
  refine .lam (.case (Γ₁ := Ctx.cons (some (.lin (.data 0 0))) (Ctx.empty 0))
    (Γ₂ := Ctx.empty _) (Δs := maybeDs) (.var rfl (fun j hj => absurd (Fin.ext (by omega)) hj))
    ?_ ?_ ?_)
  · intro j
    match j with
    | 0 => exact .con rfl (.nil _)
    | 1 => exact .con rfl (.cons (.var _) (.nil _))
  · intro j
    match j with
    | 0 => exact .con (As := []) rfl (fun _ => by unfold Ctx.append; split <;> rfl)
    | 1 =>
      refine .app (Γ₁ := Ctx.empty _) (Γ₂ := Ctx.append (Ctx.empty _) (maybeDs 1)) (A := .atom 0)
        (.con (As := [.atom 0]) rfl (fun _ => rfl)) (.var (by rfl) ?_) ?_
      · intro j hj
        match j with
        | ⟨0, _⟩ => exact absurd rfl hj
        | ⟨1, _⟩ => rfl
      · intro j
        exact .noneLeft _
  · intro j
    match j with
    | ⟨0, _⟩ => exact .noneRight _

/-! ### Grade polymorphism -/

theorem pushPat_poly_check :
    checkPatSat (R := LNL) (V := Unit) exSig lnlHs none pushPat (pushPatTy (.var ())) = true ∧
      checkPatValid (R := LNL) (V := Unit) exSig lnlHs none pushPat (pushPatTy (.var ())) =
        false := by
  decide

/-- For `push : ∀ {r} . (a, b) [r] → …`, the pattern `[(x, y)]` can be typed at *some*
instantiation of `r` … -/
theorem pushPat_poly_satisfiable :
    ∃ ρ : Unit → LNL, ∃ Δ, GPatTy (exSig.map (GExp.eval ρ)) lnlHs none pushPat
      ((pushPatTy (.var ())).map (GExp.eval ρ)) Δ :=
  (checkPatSat_iff (R := LNL) (V := Unit) exSig lnlHs none pushPat _).mp pushPat_poly_check.1

/-- … but not at *every* instantiation. -/
theorem pushPat_poly_not_valid :
    ¬ ∀ ρ : Unit → LNL, ∃ Δ, GPatTy (exSig.map (GExp.eval ρ)) lnlHs none pushPat
      ((pushPatTy (.var ())).map (GExp.eval ρ)) Δ := by
  intro h
  have := (checkPatValid_iff (R := LNL) (V := Unit) exSig lnlHs none pushPat _).mpr h
  simp [pushPat_poly_check.2] at this

end LinExp

end
