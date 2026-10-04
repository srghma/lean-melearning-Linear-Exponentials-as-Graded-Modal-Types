module

public import RequestProject.Sec4_Solution.Hsup
public import RequestProject.Sec4_Solution.IMELL.Typing

/-!
# Atomic types are type variables: substitution of types for atoms

The paper's calculi have no base types; their types (`push : □_r (A ⊗ B) ⊸ □_r A ⊗ □_r B`,
`!(A ⊗ B) ⊸ !A ⊗ !B`, …) are *schemas* in metavariables `A`, `B`.  This project adds atomic
types `Ty.atom i` (and `ITy.atom i`) to both calculi.  This file shows that atoms behave
exactly like the paper's metavariables:

* `Ty.substAtoms σ` / `ITy.substAtoms σ` replace every atom `α_i` by the type `σ i`;
* **substitution lemmas** `Typed.substAtoms` (GrCore, for every `⋉`, hence also the adjusted
  calculus) and `IHasType.substAtoms` (IMELL): a derivation stays valid, with the *same term*,
  after substituting arbitrary types for the atoms;
* consequently, a closed term has a type built from atoms iff it has *every* instance of that
  type (`typed_atoms_iff_schematic`, `ihasType_atoms_iff_schematic`).
-/

@[expose] public section

namespace LinExp

variable {R : Type}

/-! ## GrCore -/

/-- Simultaneous substitution of the types `σ i` for the atoms `α_i`. -/
def Ty.substAtoms (σ : ℕ → Ty R) : Ty R → Ty R
  | .atom i => σ i
  | .unit => .unit
  | .lolli A B => .lolli (A.substAtoms σ) (B.substAtoms σ)
  | .tensor A B => .tensor (A.substAtoms σ) (B.substAtoms σ)
  | .box r A => .box r (A.substAtoms σ)

@[simp] lemma Ty.substAtoms_atoms (A : Ty R) : A.substAtoms Ty.atom = A := by
  induction A <;> simp_all [Ty.substAtoms]

/-- Substitution in an assumption. -/
def Assm.substAtoms (σ : ℕ → Ty R) : Assm R → Assm R
  | .lin A => .lin (A.substAtoms σ)
  | .grad A r => .grad (A.substAtoms σ) r

/-- Substitution in a context. -/
def GCtx.substAtoms {n : ℕ} (σ : ℕ → Ty R) (Γ : GCtx R n) : GCtx R n :=
  fun i => (Γ i).map (Assm.substAtoms σ)

namespace GCtx

variable {σ : ℕ → Ty R}

@[simp] lemma substAtoms_empty (n : ℕ) :
    GCtx.substAtoms σ (Ctx.empty n : GCtx R n) = Ctx.empty n := by
  funext i; rfl

lemma substAtoms_cons {n : ℕ} (e : Option (Assm R)) (Γ : GCtx R n) :
    GCtx.substAtoms σ (Ctx.cons e Γ) =
      Ctx.cons (e.map (Assm.substAtoms σ)) (GCtx.substAtoms σ Γ) := by
  funext i; refine Fin.cases rfl (fun j => rfl) i

lemma substAtoms_append {n k : ℕ} (Γ : GCtx R n) (Δ : GCtx R k) :
    GCtx.substAtoms σ (Ctx.append Γ Δ) =
      Ctx.append (GCtx.substAtoms σ Γ) (GCtx.substAtoms σ Δ) := by
  funext i; simp only [GCtx.substAtoms, Ctx.append]; split_ifs <;> rfl

lemma substAtoms_update {n : ℕ} (Γ : GCtx R n) (i : Fin n) (e : Option (Assm R)) :
    GCtx.substAtoms σ (Function.update Γ i e) =
      Function.update (GCtx.substAtoms σ Γ) i (e.map (Assm.substAtoms σ)) := by
  funext j
  by_cases h : j = i
  · subst h; simp [GCtx.substAtoms]
  · simp [GCtx.substAtoms, Function.update_of_ne h]

end GCtx

section Semiring

variable [Semiring R] {σ : ℕ → Ty R}

lemma CtxAdd.substAtoms {n : ℕ} {Γ₁ Γ₂ Γ : GCtx R n} (h : CtxAdd Γ₁ Γ₂ Γ) :
    CtxAdd (GCtx.substAtoms σ Γ₁) (GCtx.substAtoms σ Γ₂) (GCtx.substAtoms σ Γ) := by
  intro i
  have hi := h i
  simp only [GCtx.substAtoms]
  generalize Γ₁ i = a, Γ₂ i = b, Γ i = c at hi ⊢
  cases hi with
  | noneLeft e => exact EntryAdd.noneLeft _
  | noneRight a => exact EntryAdd.noneRight _
  | grad A r s => exact EntryAdd.grad _ r s

lemma IsZeroCtx.substAtoms {n : ℕ} {Δ : GCtx R n} (h : IsZeroCtx Δ) :
    IsZeroCtx (GCtx.substAtoms σ Δ) := by
  intro i
  rcases h i with h | ⟨A, h⟩
  · left; simp [GCtx.substAtoms, h]
  · right; exact ⟨A.substAtoms σ, by simp [GCtx.substAtoms, h, Assm.substAtoms]⟩

omit [Semiring R] in
lemma IsGraded.substAtoms {n : ℕ} {Γ : GCtx R n} (h : IsGraded Γ) :
    IsGraded (GCtx.substAtoms σ Γ) := by
  intro i A hA
  simp only [GCtx.substAtoms] at hA
  rcases hΓ : Γ i with _ | (B | ⟨B, r⟩)
  · simp [hΓ] at hA
  · exact h i B hΓ
  · simp [hΓ, Assm.substAtoms] at hA

lemma scale_substAtoms {n : ℕ} (r : R) (Γ : GCtx R n) :
    GCtx.substAtoms σ (scale r Γ) = scale r (GCtx.substAtoms σ Γ) := by
  funext i
  simp only [GCtx.substAtoms, scale, Option.map_map]
  congr 1
  funext a; cases a <;> rfl

variable [Preorder R]

omit [Semiring R] [Preorder R] in
/-- Substitution lemma for pattern typing. -/
theorem PatTy.substAtoms {hs : R → R → Option R} {k : ℕ} {o : Option R} {p : Pat k}
    {A : Ty R} {Δ : GCtx R k} (h : PatTy hs o p A Δ) (σ : ℕ → Ty R) :
    PatTy hs o p (A.substAtoms σ) (GCtx.substAtoms σ Δ) := by
  induction h with
  | var A => exact PatTy.var _
  | pair _ _ ih1 ih2 => rw [GCtx.substAtoms_append]; exact PatTy.pair ih1 ih2
  | box r _ ih => exact PatTy.box r ih
  | gvar r A => exact PatTy.gvar r _
  | gpair _ _ hrs ih1 ih2 => rw [GCtx.substAtoms_append]; exact PatTy.gpair ih1 ih2 hrs
  | unit o => rw [GCtx.substAtoms_empty]; exact PatTy.unit o

/-- **Substitution lemma** for GrCore (for every operation `⋉` used by `[PPROD]`, so both
for Section 2's calculus and the adjusted calculus): substituting arbitrary types for the
atoms preserves typing, with the same term. -/
theorem Typed.substAtoms {hs : R → R → Option R} {n : ℕ} {Γ : GCtx R n} {t : Term n}
    {A : Ty R} (h : Typed hs Γ t A) (σ : ℕ → Ty R) :
    Typed hs (GCtx.substAtoms σ Γ) t (A.substAtoms σ) := by
  induction h with
  | var hi hj =>
    exact Typed.var (by simp [GCtx.substAtoms, hi, Assm.substAtoms])
      (fun j hne => by simp [GCtx.substAtoms, hj j hne])
  | lam _ ih =>
    rw [GCtx.substAtoms_cons] at ih; exact Typed.lam ih
  | app _ _ hadd ih1 ih2 => exact Typed.app ih1 ih2 hadd.substAtoms
  | der _ hi ih =>
    rw [GCtx.substAtoms_update]
    exact Typed.der ih (by simp [GCtx.substAtoms, hi, Assm.substAtoms])
  | weak _ hz hadd ih => exact Typed.weak ih hz.substAtoms hadd.substAtoms
  | approx _ hi hrs ih =>
    rw [GCtx.substAtoms_update]
    exact Typed.approx ih (by simp [GCtx.substAtoms, hi, Assm.substAtoms]) hrs
  | pr r _ hg ih =>
    rw [scale_substAtoms]; exact Typed.pr r ih hg.substAtoms
  | unit hΓ => exact Typed.unit (fun i => by simp [GCtx.substAtoms, hΓ i])
  | pair _ _ hadd ih1 ih2 => exact Typed.pair ih1 ih2 hadd.substAtoms
  | letPat _ hp _ hadd ih1 ih2 =>
    rw [GCtx.substAtoms_append] at ih2
    exact Typed.letPat ih1 (hp.substAtoms σ) ih2 hadd.substAtoms

/-- **Atoms are schematic variables (GrCore).**  A closed term has a type built from atoms iff
it has every instance of that type obtained by substituting types for the atoms. -/
theorem typed_atoms_iff_schematic (hs : R → R → Option R) (t : Term 0) (A : Ty R) :
    Typed hs (Ctx.empty 0) t A ↔
      ∀ σ : ℕ → Ty R, Typed hs (Ctx.empty 0) t (A.substAtoms σ) := by
  refine ⟨fun h σ => ?_, fun h => by simpa using h Ty.atom⟩
  simpa using h.substAtoms σ

end Semiring

/-! ## IMELL -/

/-- Simultaneous substitution of the formulas `σ i` for the atoms `α_i`. -/
def ITy.substAtoms (σ : ℕ → ITy) : ITy → ITy
  | .atom i => σ i
  | .unit => .unit
  | .lolli A B => .lolli (A.substAtoms σ) (B.substAtoms σ)
  | .tensor A B => .tensor (A.substAtoms σ) (B.substAtoms σ)
  | .bang A => .bang (A.substAtoms σ)

@[simp] lemma ITy.substAtoms_atoms (A : ITy) : A.substAtoms ITy.atom = A := by
  induction A <;> simp_all [ITy.substAtoms]

/-- Substitution in an IMELL context. -/
def ICtx.substAtoms {n : ℕ} (σ : ℕ → ITy) (Γ : ICtx n) : ICtx n :=
  fun i => (Γ i).map (ITy.substAtoms σ)

namespace ICtx

variable {σ : ℕ → ITy}

@[simp] lemma substAtoms_empty (n : ℕ) :
    ICtx.substAtoms σ (Ctx.empty n : ICtx n) = Ctx.empty n := by
  funext i; rfl

lemma substAtoms_cons {n : ℕ} (e : Option ITy) (Γ : ICtx n) :
    ICtx.substAtoms σ (Ctx.cons e Γ) =
      Ctx.cons (e.map (ITy.substAtoms σ)) (ICtx.substAtoms σ Γ) := by
  funext i; refine Fin.cases rfl (fun j => rfl) i

lemma substAtoms_append {n k : ℕ} (Γ : ICtx n) (Δ : ICtx k) :
    ICtx.substAtoms σ (Ctx.append Γ Δ) =
      Ctx.append (ICtx.substAtoms σ Γ) (ICtx.substAtoms σ Δ) := by
  funext i; simp only [ICtx.substAtoms, Ctx.append]; split_ifs <;> rfl

lemma substAtoms_ctx2 (A B : ITy) :
    ICtx.substAtoms σ (ctx2 A B) = ctx2 (A.substAtoms σ) (B.substAtoms σ) := by
  funext i; simp only [ICtx.substAtoms, ctx2]; split_ifs <;> rfl

end ICtx

lemma ISplit.substAtoms {σ : ℕ → ITy} {n : ℕ} {Γ₁ Γ₂ Γ : ICtx n} (h : ISplit Γ₁ Γ₂ Γ) :
    ISplit (ICtx.substAtoms σ Γ₁) (ICtx.substAtoms σ Γ₂) (ICtx.substAtoms σ Γ) := by
  intro i
  rcases h i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; simp [ICtx.substAtoms, h1, h2]
  · right; simp [ICtx.substAtoms, h1, h2]

lemma ISplitN.substAtoms {σ : ℕ → ITy} {n : ℕ} :
    ∀ (k : ℕ) (Γs : Fin k → ICtx n) (Γ : ICtx n), ISplitN k Γs Γ →
      ISplitN k (fun j => ICtx.substAtoms σ (Γs j)) (ICtx.substAtoms σ Γ)
  | 0, _, Γ, h => fun i => by simp [ICtx.substAtoms, h i]
  | k + 1, Γs, _, ⟨Γ', h1, h2⟩ =>
      ⟨ICtx.substAtoms σ Γ', ISplitN.substAtoms k _ Γ' h1, h2.substAtoms⟩

/-- **Substitution lemma** for IMELL: substituting arbitrary formulas for the atoms preserves
typing, with the same term. -/
theorem IHasType.substAtoms {n : ℕ} {Γ : ICtx n} {M : ITerm n} {A : ITy} (h : IHasType Γ M A)
    (σ : ℕ → ITy) : IHasType (ICtx.substAtoms σ Γ) M (A.substAtoms σ) := by
  induction h with
  | var hi hj =>
    exact IHasType.var (by simp [ICtx.substAtoms, hi])
      (fun j hne => by simp [ICtx.substAtoms, hj j hne])
  | lam _ ih => rw [ICtx.substAtoms_cons] at ih; exact IHasType.lam ih
  | app _ _ hs ih1 ih2 => exact IHasType.app ih1 ih2 hs.substAtoms
  | star hΓ => exact IHasType.star (fun i => by simp [ICtx.substAtoms, hΓ i])
  | letStar _ _ hs ih1 ih2 => exact IHasType.letStar ih1 ih2 hs.substAtoms
  | pair _ _ hs ih1 ih2 => exact IHasType.pair ih1 ih2 hs.substAtoms
  | letPair _ _ hs ih1 ih2 =>
    rw [ICtx.substAtoms_append, ICtx.substAtoms_ctx2] at ih2
    exact IHasType.letPair ih1 ih2 hs.substAtoms
  | @promote n k Γs Γ Ms N As B hsplit _ _ ih1 ih2 =>
    exact IHasType.promote (As := fun j => (As j).substAtoms σ)
      (ISplitN.substAtoms k Γs Γ hsplit) ih1 ih2
  | derelict _ ih => exact IHasType.derelict ih
  | discard _ _ hs ih1 ih2 => exact IHasType.discard ih1 ih2 hs.substAtoms
  | copy _ _ hs ih1 ih2 =>
    rw [ICtx.substAtoms_append, ICtx.substAtoms_ctx2] at ih2
    exact IHasType.copy ih1 ih2 hs.substAtoms

/-- **Atoms are schematic variables (IMELL).** -/
theorem ihasType_atoms_iff_schematic (M : ITerm 0) (A : ITy) :
    IHasType (Ctx.empty 0) M A ↔ ∀ σ : ℕ → ITy, IHasType (Ctx.empty 0) M (A.substAtoms σ) := by
  refine ⟨fun h σ => ?_, fun h => by simpa using h ITy.atom⟩
  simpa using h.substAtoms σ

end LinExp

end
