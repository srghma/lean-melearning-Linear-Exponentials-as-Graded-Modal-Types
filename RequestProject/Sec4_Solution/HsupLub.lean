module

public import RequestProject.Sec4_Solution.Hsup
public import RequestProject.Sec2_CoreCalculus.Derived

/-!
# Section 4: `hsup` as the partial least upper bound recovers GrCore

"For the semirings where we wish to permit the full `⊗` distributive law we can set `hsup`
to be the (partial) least-upper bound `⊔` derived from the preordering, which recovers the
existing pattern matching typing."

We prove this for a partially ordered semiring: if `hs r s = some t` exactly when `t` is a
least upper bound of `r` and `s`, then the adjusted calculus `Typed hs` derives exactly the
same judgements as the calculus of Section 2 (`GrCore`).  The direction from the adjusted
calculus to GrCore uses (APPROX) to raise the grades of the binders of a product pattern
from `r`, `s` to `r ⊔ s`.
-/

@[expose] public section

namespace LinExp

variable {R : Type} [Semiring R]

section Mono

variable [Preorder R]

omit [Semiring R] [Preorder R] in
/-- Enlarging the domain of the operation used by `[PPROD]` preserves pattern typing. -/
theorem PatTy.mono {hs hs' : R → R → Option R}
    (hle : ∀ r s t, hs r s = some t → hs' r s = some t) {k : ℕ} {o : Option R} {p : Pat k}
    {A : Ty R} {Δ : GCtx R k} (h : PatTy hs o p A Δ) : PatTy hs' o p A Δ := by
  induction h with
  | var A => exact .var A
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | box r _ ih => exact .box r ih
  | gvar r A => exact .gvar r A
  | gpair _ _ hrs ih₁ ih₂ => exact .gpair ih₁ ih₂ (hle _ _ _ hrs)
  | unit o => exact .unit o

/-- Enlarging the domain of the operation used by `[PPROD]` preserves typing. -/
theorem Typed.mono {hs hs' : R → R → Option R}
    (hle : ∀ r s t, hs r s = some t → hs' r s = some t) {n : ℕ} {Γ : GCtx R n} {t : Term n}
    {A : Ty R} (h : Typed hs Γ t A) : Typed hs' Γ t A := by
  induction h with
  | var h₁ h₂ => exact .var h₁ h₂
  | lam _ ih => exact .lam ih
  | app _ _ hadd ih₁ ih₂ => exact .app ih₁ ih₂ hadd
  | der _ hi ih => exact .der ih hi
  | weak _ hz hadd ih => exact .weak ih hz hadd
  | approx _ hi hrs ih => exact .approx ih hi hrs
  | pr r _ hg ih => exact .pr r ih hg
  | unit h => exact .unit h
  | pair _ _ hadd ih₁ ih₂ => exact .pair ih₁ ih₂ hadd
  | letPat _ hp _ hadd ih₁ ih₂ => exact .letPat ih₁ (hp.mono hle) ih₂ hadd

/-- One context entry is obtained from another by raising the grade of a graded assumption
(or is equal to it). -/
inductive EntryLe : Option (Assm R) → Option (Assm R) → Prop where
  | refl (e : Option (Assm R)) : EntryLe e e
  | grad (A : Ty R) {r s : R} : r ≤ s → EntryLe (some (.grad A r)) (some (.grad A s))

/-- `CtxLe Γ Γ'`: `Γ'` is obtained from `Γ` by raising grades pointwise. -/
def CtxLe {n : ℕ} (Γ Γ' : GCtx R n) : Prop := ∀ i, EntryLe (Γ i) (Γ' i)

omit [Semiring R] in
lemma CtxLe.refl {n : ℕ} (Γ : GCtx R n) : CtxLe Γ Γ := fun _ => .refl _

omit [Semiring R] in
lemma CtxLe.append {n k : ℕ} {Γ Γ' : GCtx R n} {Δ Δ' : GCtx R k} (h₁ : CtxLe Γ Γ')
    (h₂ : CtxLe Δ Δ') : CtxLe (Ctx.append Γ Δ) (Ctx.append Γ' Δ') := by
  intro i
  by_cases hi : i.val < k
  · rw [Ctx.append_low _ _ _ hi, Ctx.append_low _ _ _ hi]; exact h₂ _
  · rw [Ctx.append_high _ _ _ hi, Ctx.append_high _ _ _ hi]; exact h₁ _

/-- Admissible "multi-(APPROX)": typing is preserved by raising grades of any number of graded
assumptions. -/
theorem Typed.approxCtx {hs : R → R → Option R} {n : ℕ} {Γ Γ' : GCtx R n} {t : Term n}
    {B : Ty R} (h : Typed hs Γ t B) (hle : CtxLe Γ Γ') : Typed hs Γ' t B := by
  classical
  suffices key : ∀ (S : Finset (Fin n)) (Γ : GCtx R n), Typed hs Γ t B → CtxLe Γ Γ' →
      (∀ i ∉ S, Γ i = Γ' i) → Typed hs Γ' t B from
    key Finset.univ Γ h hle (by simp)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro Γ h _ heq
    exact h.of_eq (funext fun i => heq i (Finset.notMem_empty i))
  | insert i S _ ih =>
    intro Γ h hle heq
    have h1 : Typed hs (Function.update Γ i (Γ' i)) t B := by
      have hi := hle i
      generalize hx : Γ i = x at hi
      generalize hy : Γ' i = y at hi
      cases hi with
      | refl e => exact h.of_eq (by rw [← hx]; simp)
      | grad A hrs => exact Typed.approx h hx hrs
    refine ih _ h1 (fun j => ?_) (fun j hj => ?_)
    · by_cases hji : j = i
      · subst hji; simp; exact .refl _
      · rw [Function.update_of_ne hji]; exact hle j
    · by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji]
        exact heq j (by simp [hji, hj])

end Mono

section Lub

variable [PartialOrder R] [DecidableEq R]

/-- `hs` is the partial least upper bound of the order: `r ⊔ s = t` iff `t` is a least upper
bound of `r` and `s` (and `r ⊔ s` is undefined when there is none). -/
def IsPartialLub (hs : R → R → Option R) : Prop :=
  ∀ r s t, hs r s = some t ↔ IsLUB {r, s} t

/-- Optional grades `?r`, ordered by `· ≤ ·` and `r ≤ u ⟹ r ≤ u`. -/
def OptGradeLe : Option R → Option R → Prop
  | none, none => True
  | some r, some u => r ≤ u
  | _, _ => False

omit [Semiring R] in
/-- A pattern typed with the partial lub can be re-typed in the calculus of Section 2 at any
larger grade, producing binders whose grades are raised. -/
theorem PatTy.toDiag {hs : R → R → Option R} (hlub : IsPartialLub hs) {k : ℕ} {o : Option R}
    {p : Pat k} {A : Ty R} {Δ : GCtx R k} (h : PatTy hs o p A Δ) :
    ∀ o', OptGradeLe o o' → ∃ Δ', PatTy diagHsup o' p A Δ' ∧ CtxLe Δ Δ' := by
  induction h with
  | var A =>
    intro o' ho
    cases o' with
    | none => exact ⟨_, .var A, CtxLe.refl _⟩
    | some _ => exact ho.elim
  | pair _ _ ih₁ ih₂ =>
    intro o' ho
    cases o' with
    | none =>
      obtain ⟨Δ₁', h₁, l₁⟩ := ih₁ none trivial
      obtain ⟨Δ₂', h₂, l₂⟩ := ih₂ none trivial
      exact ⟨_, .pair h₁ h₂, l₁.append l₂⟩
    | some _ => exact ho.elim
  | box r _ ih =>
    intro o' ho
    cases o' with
    | none =>
      obtain ⟨Δ', h', l⟩ := ih (some r) (le_refl r)
      exact ⟨_, .box r h', l⟩
    | some _ => exact ho.elim
  | gvar r A =>
    intro o' ho
    cases o' with
    | none => exact ho.elim
    | some u => exact ⟨_, .gvar u A, fun _ => .grad A ho⟩
  | gpair _ _ hrs ih₁ ih₂ =>
    rename_i r s t _ _
    intro o' ho
    cases o' with
    | none => exact ho.elim
    | some u =>
      have hub := ((hlub _ _ _).1 hrs).1
      have hr : r ≤ u := le_trans (hub (by simp)) ho
      have hs' : s ≤ u := le_trans (hub (by simp)) ho
      obtain ⟨Δ₁', h₁, l₁⟩ := ih₁ (some u) hr
      obtain ⟨Δ₂', h₂, l₂⟩ := ih₂ (some u) hs'
      exact ⟨_, .gpair h₁ h₂ (by simp [diagHsup]), l₁.append l₂⟩
  | unit o =>
    intro o' _
    exact ⟨_, .unit o', CtxLe.refl _⟩

/-- Adjusted calculus with the partial lub ⟹ calculus of Section 2. -/
theorem Typed.toGrCore {hs : R → R → Option R} (hlub : IsPartialLub hs) {n : ℕ}
    {Γ : GCtx R n} {t : Term n} {A : Ty R} (h : Typed hs Γ t A) : GrCore Γ t A := by
  induction h with
  | var h₁ h₂ => exact .var h₁ h₂
  | lam _ ih => exact .lam ih
  | app _ _ hadd ih₁ ih₂ => exact .app ih₁ ih₂ hadd
  | der _ hi ih => exact .der ih hi
  | weak _ hz hadd ih => exact .weak ih hz hadd
  | approx _ hi hrs ih => exact .approx ih hi hrs
  | pr r _ hg ih => exact .pr r ih hg
  | unit h => exact .unit h
  | pair _ _ hadd ih₁ ih₂ => exact .pair ih₁ ih₂ hadd
  | letPat _ hp _ hadd ih₁ ih₂ =>
    obtain ⟨Δ', hp', hle⟩ := hp.toDiag hlub none trivial
    exact .letPat ih₁ hp' (ih₂.approxCtx ((CtxLe.refl _).append hle)) hadd

/-- **Section 4.** Setting `hsup` to the partial least upper bound of the order recovers the
pattern typing of Section 2: the adjusted calculus and GrCore derive the same judgements. -/
theorem adjTyped_lub_iff_grcore {hs : R → R → Option R} (hlub : IsPartialLub hs) {n : ℕ}
    (Γ : GCtx R n) (t : Term n) (A : Ty R) : Typed hs Γ t A ↔ GrCore Γ t A := by
  refine ⟨fun h => h.toGrCore hlub, fun h => h.mono fun r s t hrs => ?_⟩
  obtain ⟨rfl, rfl⟩ := diagHsup_eq_some.1 hrs
  exact (hlub _ _ _).2 (by simp)

omit [Semiring R] in
/-- For a discretely ordered set of grades (e.g. the exact-usage semiring `ℕ` ordered by
equality) the partial least upper bound is `diagHsup`: `r ⊔ s` is defined only when `r = s`. -/
theorem isPartialLub_diagHsup (hdisc : ∀ r s : R, r ≤ s ↔ r = s) :
    IsPartialLub (diagHsup (R := R)) := by
  intro r s t
  rw [diagHsup_eq_some]
  constructor
  · rintro ⟨rfl, rfl⟩
    simp
  · intro h
    have hr : r = t := (hdisc _ _).1 (h.1 (by simp))
    have hs : s = t := (hdisc _ _).1 (h.1 (by simp))
    exact ⟨hr.trans hs.symm, hr.symm⟩

end Lub

end LinExp

end
