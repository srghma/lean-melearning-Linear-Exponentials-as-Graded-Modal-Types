module

public import RequestProject.Sec5_ImplementationInGranule.DataTypes.Typing

/-!
# Section 5: GrCore is a fragment of the calculus with data types

Every GrCore derivation (Section 2, for any `⋉` that is only defined on the diagonal, with
`r ⋉ r = r`) is also a derivation of the Granule-style calculus with data types, for every
signature of data types (`grcore_embeds`).  The side condition is what lets GrCore's `[PPROD]`
(sub-patterns at grades `r`, `s` and the pattern at `r ⋉ s`) be read as Granule's rule
(both sub-patterns at the same grade `r`, and `r ⋉ r` defined).  It holds for Section 2's
`diagHsup` and for equation (1) (`diagHsup_diagonal`, `lnl_hsup_diagonal`).
-/

@[expose] public section

namespace LinExp

variable {R : Type}

/-- The embedding of the assumptions of Section 2. -/
def Assm.toG : Assm R → GAssm R
  | .lin A => .lin (GTy.ofTy A)
  | .grad A r => .grad (GTy.ofTy A) r

/-- The embedding of the contexts of Section 2. -/
def ctxToG {n : ℕ} (Γ : GCtx R n) : GrCtx R n := fun i => (Γ i).map Assm.toG

/-- `⋉` is defined only on the diagonal, with `r ⋉ r = r` when defined. -/
def DiagonalHsup (hs : R → R → Option R) : Prop := ∀ r s t, hs r s = some t → r = s ∧ t = r

lemma diagHsup_diagonal [DecidableEq R] : DiagonalHsup (diagHsup (R := R)) :=
  fun _ _ _ h => by
    have := (diagHsup_eq_some).mp h
    exact ⟨this.1, this.2⟩

lemma lnl_hsup_diagonal : DiagonalHsup (HSup.hsup : LNL → LNL → Option LNL) :=
  fun _ _ _ h => by
    obtain ⟨rfl, rfl, rfl⟩ := LNL.hsup_eq_some.mp h
    exact ⟨rfl, rfl⟩

section CtxLemmas

lemma ctxToG_append {n k : ℕ} (Γ : GCtx R n) (Δ : GCtx R k) :
    ctxToG (Ctx.append Γ Δ) = Ctx.append (ctxToG Γ) (ctxToG Δ) := by
  funext i; simp only [ctxToG, Ctx.append]; split_ifs <;> rfl

lemma ctxToG_cons {n : ℕ} (e : Option (Assm R)) (Γ : GCtx R n) :
    ctxToG (Ctx.cons e Γ) = Ctx.cons (e.map Assm.toG) (ctxToG Γ) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma ctxToG_update {n : ℕ} (Γ : GCtx R n) (i : Fin n) (e : Option (Assm R)) :
    ctxToG (Function.update Γ i e) = Function.update (ctxToG Γ) i (e.map Assm.toG) := by
  funext j
  by_cases h : j = i
  · subst h; simp [ctxToG]
  · simp [ctxToG, Function.update_of_ne h]

lemma ctxToG_empty {k : ℕ} : ctxToG (Ctx.empty k : GCtx R k) = Ctx.empty k := rfl

lemma isGraded_toG {n : ℕ} {Γ : GCtx R n} (h : IsGraded Γ) : GIsGraded (ctxToG Γ) := by
  intro i A hA
  simp only [ctxToG, Option.map_eq_some_iff] at hA
  obtain ⟨a, ha, he⟩ := hA
  cases a with
  | lin B => exact h i B ha
  | grad B r => simp [Assm.toG] at he

variable [Semiring R]

lemma ctxAdd_toG {n : ℕ} {Γ₁ Γ₂ Γ : GCtx R n} (h : CtxAdd Γ₁ Γ₂ Γ) :
    GCtxAdd (ctxToG Γ₁) (ctxToG Γ₂) (ctxToG Γ) := by
  intro i
  have h' := h i
  simp only [ctxToG]
  revert h'
  generalize Γ₁ i = a
  generalize Γ₂ i = b
  generalize Γ i = c
  intro h'
  cases h' with
  | noneLeft e => exact .noneLeft _
  | noneRight a => exact .noneRight _
  | grad A r s => exact .grad _ r s

lemma isZeroCtx_toG {n : ℕ} {Δ : GCtx R n} (h : IsZeroCtx Δ) : GIsZeroCtx (ctxToG Δ) := by
  intro i
  rcases h i with h | ⟨A, h⟩
  · left; simp [ctxToG, h]
  · right; exact ⟨GTy.ofTy A, by simp [ctxToG, h, Assm.toG]⟩

lemma ctxToG_scale {n : ℕ} (r : R) (Γ : GCtx R n) :
    ctxToG (scale r Γ) = gscale r (ctxToG Γ) := by
  funext i
  simp only [ctxToG, scale, gscale, Option.map_map]
  congr 1
  funext a
  cases a <;> rfl

end CtxLemmas

/-- GrCore pattern typing embeds into Granule-style pattern typing. -/
theorem patTy_embeds {hs : R → R → Option R} [Semiring R] [Preorder R]
    (hdiag : DiagonalHsup hs) (sig : GSig R) {k : ℕ} {o : Option R} {p : Pat k} {A : Ty R}
    {Δ : GCtx R k} (h : PatTy hs o p A Δ) :
    GPatTy sig hs o (GPat.ofPat p) (GTy.ofTy A) (ctxToG Δ) := by
  induction h with
  | var A => exact .var _
  | pair _ _ ih₁ ih₂ => rw [ctxToG_append]; exact .pair ih₁ ih₂
  | box r _ ih => exact .box r ih
  | gvar r A => exact .gvar r _
  | gpair _ _ ht ih₁ ih₂ =>
    obtain ⟨rfl, rfl⟩ := hdiag _ _ _ ht
    rw [ctxToG_append]
    exact .gpair ⟨_, ht⟩ ih₁ ih₂
  | unit o => exact .unit o

/-- **GrCore is a fragment of the calculus with data types.**  For a `⋉` defined only on the
diagonal (as in Section 2 and in equation (1)), every GrCore derivation `Γ ⊢ t : A` is a
derivation of the Granule-style calculus, over any signature of data types. -/
theorem grcore_embeds {hs : R → R → Option R} [Semiring R] [Preorder R]
    (hdiag : DiagonalHsup hs) (sig : GSig R) {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R}
    (h : Typed hs Γ t A) : GTyped sig hs (ctxToG Γ) (GTerm.ofTerm t) (GTy.ofTy A) := by
  induction h with
  | var hi hj =>
    refine .var (by simp [ctxToG, hi, Assm.toG]) (fun j hne => by simp [ctxToG, hj j hne])
  | lam _ ih =>
    refine .lam ?_
    rw [ctxToG_cons] at ih
    exact ih
  | app _ _ hadd ih₁ ih₂ => exact .app ih₁ ih₂ (ctxAdd_toG hadd)
  | der _ hi ih =>
    rw [ctxToG_update]
    exact .der ih (by simp [ctxToG, hi, Assm.toG])
  | weak _ hz hadd ih => exact .weak ih (isZeroCtx_toG hz) (ctxAdd_toG hadd)
  | approx _ hi hle ih =>
    rw [ctxToG_update]
    exact .approx ih (by simp [ctxToG, hi, Assm.toG]) hle
  | pr r _ hg ih =>
    rw [ctxToG_scale]
    exact .pr r ih (isGraded_toG hg)
  | unit hΓ => exact .unit (fun i => by simp [ctxToG, hΓ i])
  | pair _ _ hadd ih₁ ih₂ => exact .pair ih₁ ih₂ (ctxAdd_toG hadd)
  | letPat _ hp _ hadd ih₁ ih₂ =>
    refine .letPat ih₁ (patTy_embeds hdiag sig hp) ?_ (ctxAdd_toG hadd)
    rw [← ctxToG_append]
    exact ih₂

end LinExp

end
