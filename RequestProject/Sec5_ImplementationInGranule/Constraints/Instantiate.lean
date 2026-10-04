module

public import RequestProject.Sec5_ImplementationInGranule.Constraints.Correctness

/-!
# Section 5: constraint generation commutes with instantiating grades

`patCheck_map`: running `patCheck` on a signature, grade and type whose grades have been
changed by `f` gives the result of running it on the originals, with `f` applied to the
context and to the constraint.  This is what makes it sound to check a pattern once,
symbolically, for all instantiations of the grade variables (`Solver.lean`).
-/

@[expose] public section

namespace LinExp

variable {G H : Type}

lemma GrCtx.map_append (f : G → H) {k₁ k₂ : ℕ} (Δ₁ : GrCtx G k₁) (Δ₂ : GrCtx G k₂) :
    GrCtx.map f (Ctx.append Δ₁ Δ₂) = Ctx.append (Δ₁.map f) (Δ₂.map f) := by
  funext i; simp only [GrCtx.map, Ctx.append]; split_ifs <;> rfl

@[simp] lemma GSig.map_fields (f : G → H) (sig : GSig G) (d i c : ℕ) :
    (sig.map f).fields d i c = (sig.fields d i c).map (List.map (GTy.map f)) := rfl

mutual

theorem patCheck_map (f : G → H) (sig : GSig G) : {k : ℕ} → (o : Option G) → (p : GPat k) →
    (A : GTy G) → patCheck (sig.map f) (o.map f) p (A.map f) =
      (patCheck sig o p A).map (fun x => (x.1.map f, x.2.map f))
  | _, o, .var, A => by cases o <;> rfl
  | _, o, .pair p q, A => by
    cases A <;> try rfl
    case tensor A B =>
      have h1 := patCheck_map f sig o p A
      have h2 := patCheck_map f sig o q B
      cases o <;> simp only [Option.map_none, Option.map_some] at h1 h2 <;>
        simp [patCheck, GTy.map, h1, h2, Option.map_bind, Option.bind_map, GrCtx.map_append,
          GFormula.map]
  | _, o, .box p, A => by
    cases o <;> cases A <;> try rfl
    case none.box r A =>
      have h := patCheck_map f sig (some r) p A
      simpa [patCheck, GTy.map] using h
  | _, o, .unit, A => by cases o <;> cases A <;> rfl
  | _, o, .con c ps, A => by
    cases A <;> try rfl
    case data d i =>
      cases hf : sig.fields d i c with
      | none => cases o <;> simp [patCheck, GTy.map, hf]
      | some As =>
        have h := patsCheck_map f sig o ps As
        cases o <;> simp only [Option.map_none, Option.map_some] at h <;>
          simp [patCheck, GTy.map, hf, h, Option.map_map, Function.comp_def]
        split_ifs <;> rfl

theorem patsCheck_map (f : G → H) (sig : GSig G) : {k : ℕ} → (o : Option G) → (ps : GPats k) →
    (As : List (GTy G)) → patsCheck (sig.map f) (o.map f) ps (As.map (GTy.map f)) =
      (patsCheck sig o ps As).map (fun x => (x.1.map f, x.2.map f))
  | _, o, .nil, As => by cases As <;> rfl
  | _, o, .cons p ps, As => by
    cases As with
    | nil => rfl
    | cons A As =>
      have h1 := patCheck_map f sig o p A
      have h2 := patsCheck_map f sig o ps As
      simp [patsCheck, h1, h2, Option.map_bind, Option.bind_map, GrCtx.map_append, GFormula.map]

end

end LinExp

end
