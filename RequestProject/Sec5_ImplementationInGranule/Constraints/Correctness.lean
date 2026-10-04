module

public import RequestProject.Sec5_ImplementationInGranule.Constraints.PatCheck

/-!
# Section 5: correctness of constraint generation

* `patCheck_sound`, `patCheck_complete`, `patCheck_iff`: for concrete grades, Granule-style
  pattern typing holds exactly when `patCheck` succeeds and the generated constraint holds.
* Consequences, read off from the generated constraint: under a box of grade `r`, a
  constructor pattern with at least one sub-pattern, or a pair pattern, needs `r ⋉ r` to be
  defined (`GPatTy.con_requires_hsup`, `GPatTy.pair_requires_hsup`), while a constructor with
  no sub-patterns imposes no condition (`GPatTy.con_nullary`).
-/

@[expose] public section

namespace LinExp

variable {R : Type} [Preorder R] (sig : GSig R) (hs : R → R → Option R)

mutual

theorem patCheck_sound : {k : ℕ} → (o : Option R) → (p : GPat k) → (A : GTy R) →
    (Δ : GrCtx R k) → (φ : GFormula R) → patCheck sig o p A = some (Δ, φ) →
    φ.Holds hs id → GPatTy sig hs o p A Δ
  | _, o, .var, A, Δ, φ, h, _ => by
    cases o <;> simp [patCheck] at h <;> obtain ⟨rfl, rfl⟩ := h
    · exact .var A
    · exact .gvar _ A
  | _, o, .pair p q, A, Δ, φ, h, hφ => by
    cases o <;> cases A <;> simp [patCheck, Option.bind_eq_some_iff] at h
    · obtain ⟨Δ₁, φ₁, h₁, Δ₂, φ₂, h₂, rfl, rfl⟩ := h
      exact .pair (patCheck_sound _ _ _ _ _ h₁ hφ.1) (patCheck_sound _ _ _ _ _ h₂ hφ.2)
    · obtain ⟨Δ₁, φ₁, h₁, Δ₂, φ₂, h₂, rfl, rfl⟩ := h
      exact .gpair hφ.1 (patCheck_sound _ _ _ _ _ h₁ hφ.2.1) (patCheck_sound _ _ _ _ _ h₂ hφ.2.2)
  | _, o, .box p, A, Δ, φ, h, hφ => by
    cases o <;> cases A <;> simp [patCheck] at h
    exact .box _ (patCheck_sound _ _ _ _ _ h hφ)
  | _, o, .unit, A, Δ, φ, h, hφ => by
    cases o <;> cases A <;> simp [patCheck] at h <;> obtain ⟨rfl, rfl⟩ := h <;> exact .unit _
  | _, o, .con c ps, A, Δ, φ, h, hφ => by
    cases o <;> cases A <;> simp [patCheck, Option.bind_eq_some_iff] at h
    · obtain ⟨As, hAs, h⟩ := h
      exact .con hAs (patsCheck_sound _ _ _ _ _ h hφ)
    · obtain ⟨As, hAs, φ', h, rfl⟩ := h
      cases hne : ps.nonempty
      · simp [hne] at hφ
        exact .gcon hAs (by simp [hne]) (patsCheck_sound _ _ _ _ _ h hφ)
      · simp [hne, GFormula.Holds] at hφ
        exact .gcon hAs (fun _ => hφ.1) (patsCheck_sound _ _ _ _ _ h hφ.2)

theorem patsCheck_sound : {k : ℕ} → (o : Option R) → (ps : GPats k) → (As : List (GTy R)) →
    (Δ : GrCtx R k) → (φ : GFormula R) → patsCheck sig o ps As = some (Δ, φ) →
    φ.Holds hs id → GPatsTy sig hs o ps As Δ
  | _, o, .nil, As, Δ, φ, h, _ => by
    cases As <;> simp [patsCheck] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .nil _
  | _, o, .cons p ps, As, Δ, φ, h, hφ => by
    cases As <;> simp [patsCheck, Option.bind_eq_some_iff] at h
    obtain ⟨Δ₁, φ₁, h₁, Δ₂, φ₂, h₂, rfl, rfl⟩ := h
    exact .cons (patCheck_sound _ _ _ _ _ h₁ hφ.1) (patsCheck_sound _ _ _ _ _ h₂ hφ.2)

end

mutual

theorem patCheck_complete {k : ℕ} {o : Option R} {p : GPat k} {A : GTy R} {Δ : GrCtx R k} :
    GPatTy sig hs o p A Δ → ∃ φ, patCheck sig o p A = some (Δ, φ) ∧ φ.Holds hs id
  | .var A => ⟨.tt, rfl, trivial⟩
  | .gvar r A => ⟨.tt, rfl, trivial⟩
  | .pair h₁ h₂ => by
    obtain ⟨φ₁, e₁, hφ₁⟩ := patCheck_complete h₁
    obtain ⟨φ₂, e₂, hφ₂⟩ := patCheck_complete h₂
    exact ⟨.and φ₁ φ₂, by simp [patCheck, e₁, e₂], hφ₁, hφ₂⟩
  | .gpair hd h₁ h₂ => by
    obtain ⟨φ₁, e₁, hφ₁⟩ := patCheck_complete h₁
    obtain ⟨φ₂, e₂, hφ₂⟩ := patCheck_complete h₂
    exact ⟨.and (.defined _) (.and φ₁ φ₂), by simp [patCheck, e₁, e₂], hd, hφ₁, hφ₂⟩
  | .box r h => by
    obtain ⟨φ, e, hφ⟩ := patCheck_complete h
    exact ⟨φ, by simpa [patCheck] using e, hφ⟩
  | .unit o => ⟨.tt, by cases o <;> rfl, trivial⟩
  | .con hAs hps => by
    obtain ⟨φ, e, hφ⟩ := patsCheck_complete hps
    exact ⟨φ, by simp [patCheck, hAs, e], hφ⟩
  | .gcon (ps := ps) (r := r) hAs hne hps => by
    obtain ⟨φ, e, hφ⟩ := patsCheck_complete hps
    refine ⟨if ps.nonempty then .and (.defined r) φ else φ, by simp [patCheck, hAs, e], ?_⟩
    cases h : ps.nonempty
    · simpa using hφ
    · exact ⟨hne h, hφ⟩

theorem patsCheck_complete {k : ℕ} {o : Option R} {ps : GPats k} {As : List (GTy R)}
    {Δ : GrCtx R k} :
    GPatsTy sig hs o ps As Δ → ∃ φ, patsCheck sig o ps As = some (Δ, φ) ∧ φ.Holds hs id
  | .nil o => ⟨.tt, rfl, trivial⟩
  | .cons h₁ h₂ => by
    obtain ⟨φ₁, e₁, hφ₁⟩ := patCheck_complete h₁
    obtain ⟨φ₂, e₂, hφ₂⟩ := patsCheck_complete h₂
    exact ⟨.and φ₁ φ₂, by simp [patsCheck, e₁, e₂], hφ₁, hφ₂⟩

end

/-- **Correctness of constraint generation.**  A pattern `p` can be typed against `A` (at the
optional grade `o`), binding `Δ`, exactly when `patCheck` succeeds with `Δ` and a constraint
that holds. -/
theorem patCheck_iff {k : ℕ} (o : Option R) (p : GPat k) (A : GTy R) (Δ : GrCtx R k) :
    GPatTy sig hs o p A Δ ↔ ∃ φ, patCheck sig o p A = some (Δ, φ) ∧ φ.Holds hs id :=
  ⟨patCheck_complete sig hs, fun ⟨_, e, hφ⟩ => patCheck_sound sig hs _ _ _ _ _ e hφ⟩

end LinExp


namespace LinExp

variable {R : Type} [Preorder R] {sig : GSig R} {hs : R → R → Option R}

/-- Under a box of grade `r`, matching a constructor with at least one sub-pattern requires
`r ⋉ r` to be defined. -/
theorem GPatTy.con_requires_hsup {k : ℕ} {r : R} {c : ℕ} {ps : GPats k} {A : GTy R}
    {Δ : GrCtx R k} (h : GPatTy sig hs (some r) (.con c ps) A Δ) (hne : ps.nonempty = true) :
    ∃ t, hs r r = some t := by
  obtain ⟨φ, e, hφ⟩ := patCheck_complete sig hs h
  cases A <;> simp [patCheck, Option.bind_eq_some_iff] at e
  obtain ⟨As, -, φ', -, rfl⟩ := e
  simp only [hne, if_true] at hφ
  exact hφ.1

/-- Under a box of grade `r`, matching a pair requires `r ⋉ r` to be defined. -/
theorem GPatTy.pair_requires_hsup {k₁ k₂ : ℕ} {r : R} {p : GPat k₁} {q : GPat k₂} {A : GTy R}
    {Δ : GrCtx R (k₁ + k₂)} (h : GPatTy sig hs (some r) (.pair p q) A Δ) :
    ∃ t, hs r r = some t := by
  obtain ⟨φ, e, hφ⟩ := patCheck_complete sig hs h
  cases A <;> simp [patCheck, Option.bind_eq_some_iff] at e
  obtain ⟨Δ₁, φ₁, -, Δ₂, φ₂, -, -, rfl⟩ := e
  exact hφ.1

omit [Preorder R] in
/-- Constructors without sub-patterns impose no constraint on the grade. -/
theorem GPatTy.con_nullary {r : R} {c d i : ℕ} (hc : sig.fields d i c = some []) :
    GPatTy sig hs (some r) (.con c .nil) (.data d i) (Ctx.empty 0) :=
  .gcon hc (by simp [GPats.nonempty]) (.nil _)

end LinExp

end
