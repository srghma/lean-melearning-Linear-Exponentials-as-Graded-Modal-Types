module

public import RequestProject.Sec4_Solution.IMELL.Renaming

/-!
# Section 4 (Theorem 1, auxiliary): admissible rules of IMELL

Derivability-level admissible rules of IMELL (cut, per-position context entailments,
contraction of shared assumptions, promotion of all-`!` contexts) used to translate GrCore
derivations into IMELL derivations.
-/

@[expose] public section

namespace LinExp

/-- The context with the single assumption `e` at position `i`. -/
def isingle {n : ℕ} (i : Fin n) (e : ITy) : ICtx n := fun k => if k = i then some e else none

lemma isingle_var {n : ℕ} (i : Fin n) (A : ITy) : IHasType (isingle i A) (.var i) A :=
  IHasType.var (by simp [isingle]) (fun j hj => by simp [isingle, hj])

lemma ISplit.symm {n : ℕ} {Γ₁ Γ₂ Γ : ICtx n} (h : ISplit Γ₁ Γ₂ Γ) : ISplit Γ₂ Γ₁ Γ :=
  fun i => (h i).symm

lemma ISplit.single_update {n : ℕ} (Γ : ICtx n) (i : Fin n) (e : ITy) :
    ISplit (isingle i e) (Function.update Γ i none) (Function.update Γ i (some e)) := by
  intro k
  by_cases hk : k = i
  · subst hk; right; simp [isingle]
  · left; simp [isingle, hk]

lemma ISplit.empty_left {n : ℕ} (Γ : ICtx n) : ISplit (Ctx.empty n) Γ Γ :=
  fun _ => Or.inl ⟨rfl, rfl⟩

lemma ISplit.empty_right {n : ℕ} (Γ : ICtx n) : ISplit Γ (Ctx.empty n) Γ :=
  fun _ => Or.inr ⟨rfl, rfl⟩

/-- The map inserting a new innermost variable at position `j` (all other indices shifted). -/
def moveToZero {n : ℕ} (j : Fin n) : Fin n → Fin (n + 1) :=
  fun i => if i = j then 0 else i.succ

lemma moveToZero_injective {n : ℕ} (j : Fin n) : Function.Injective (moveToZero j) := by
  intro a b h
  unfold moveToZero at h
  split_ifs at h with h1 h2 h2
  · rw [h1, h2]
  · exact absurd h.symm (Fin.succ_ne_zero _)
  · exact absurd h (Fin.succ_ne_zero _)
  · exact Fin.succ_injective _ h

/-- **Cut** (derivability level): a hypothesis `A` at position `j` can be discharged by a
derivation of `A` from a disjoint context. -/
theorem IDeriv.cut {n : ℕ} {Γ₁ Ξ Γ : ICtx n} {A B : ITy} {j : Fin n} (h₁ : IDeriv Γ₁ A)
    (h₂ : IDeriv Ξ B) (hj : Ξ j = some A) (hs : ISplit Γ₁ (Function.update Ξ j none) Γ) :
    IDeriv Γ B := by
  obtain ⟨N, hN⟩ := h₁
  obtain ⟨M, hM⟩ := h₂
  have hM' : IHasType (Ctx.cons (some A) (Function.update Ξ j none))
      (M.rename (moveToZero j)) B := by
    refine hM.rename (moveToZero_injective j) (fun i => ?_) (fun k hk => ?_)
    · unfold moveToZero
      by_cases hi : i = j
      · subst hi; simp [hj]
      · simp [hi]
    · refine Fin.cases (fun hk => absurd (by simp [moveToZero]) (hk j)) (fun k hk => ?_) k hk
      simp only [Ctx.cons_succ]
      by_cases hkj : k = j
      · subst hkj; simp
      · exact absurd (by simp [moveToZero, hkj]) (hk k)
  exact ⟨_, IHasType.app (IHasType.lam hM') hN hs.symm⟩

/-- `PosEnt e e'`: at any position, an assumption `e'` can stand in for an assumption `e`. -/
def PosEnt (e e' : Option ITy) : Prop :=
  ∀ (n : ℕ) (Γ : ICtx n) (i : Fin n) (B : ITy),
    IDeriv (Function.update Γ i e) B → IDeriv (Function.update Γ i e') B

lemma PosEnt.refl (e : Option ITy) : PosEnt e e := fun _ _ _ _ h => h

lemma PosEnt.trans {e e' e'' : Option ITy} (h₁ : PosEnt e e') (h₂ : PosEnt e' e'') :
    PosEnt e e'' := fun n Γ i B h => h₂ n Γ i B (h₁ n Γ i B h)

/-- Dereliction: `!A` can stand in for `A`. -/
lemma PosEnt.derelict (A : ITy) : PosEnt (some A) (some (.bang A)) := by
  intro n Γ i B h
  refine IDeriv.cut (j := i) ⟨_, IHasType.derelict (isingle_var i (.bang A))⟩ h (by simp) ?_
  rw [Function.update_idem]
  exact ISplit.single_update Γ i _

/-- An assumption of type `I` can be added (and consumed by `let _ be * in _`). -/
lemma PosEnt.addUnit : PosEnt none (some .unit) := by
  intro n Γ i B ⟨M, hM⟩
  exact ⟨_, IHasType.letStar (isingle_var i .unit) hM (ISplit.single_update Γ i _)⟩

/-- An assumption of type `!C` can be added (and discarded). -/
lemma PosEnt.addBang (C : ITy) : PosEnt none (some (.bang C)) := by
  intro n Γ i B ⟨M, hM⟩
  exact ⟨_, IHasType.discard (isingle_var i (.bang C)) hM (ISplit.single_update Γ i _)⟩

/-- An assumption of type `I` can be removed (by cutting against `*`). -/
lemma PosEnt.removeUnit : PosEnt (some .unit) none := by
  intro n Γ i B h
  refine IDeriv.cut (j := i) ⟨_, IHasType.star (Γ := Ctx.empty n) (fun _ => rfl)⟩ h
    (by simp) ?_
  rw [Function.update_idem]
  exact ISplit.empty_left _

/-- Pointwise entailment of contexts. -/
theorem IDeriv.ctxwise {n : ℕ} {Γ Γ' : ICtx n} (h : ∀ i, PosEnt (Γ i) (Γ' i)) {B : ITy}
    (hd : IDeriv Γ B) : IDeriv Γ' B := by
  let Γm : ℕ → ICtx n := fun m i => if i.val < m then Γ' i else Γ i
  have key : ∀ m, IDeriv (Γm m) B := by
    intro m
    induction m with
    | zero => simpa [Γm] using hd
    | succ m ih =>
      by_cases hm : m < n
      · have e1 : Γm m = Function.update (Γm m) ⟨m, hm⟩ (Γ ⟨m, hm⟩) := by
          rw [eq_comm, Function.update_eq_iff]
          exact ⟨by simp [Γm], fun _ _ => rfl⟩
        have e2 : Γm (m + 1) = Function.update (Γm m) ⟨m, hm⟩ (Γ' ⟨m, hm⟩) := by
          funext i
          by_cases hi : i = ⟨m, hm⟩
          · subst hi; simp [Γm]
          · rw [Function.update_of_ne hi]
            have : i.val ≠ m := fun h' => hi (Fin.ext h')
            simp only [Γm]
            split_ifs <;> first | rfl | omega
        rw [e2]
        rw [e1] at ih
        exact h _ _ _ _ _ ih
      · have : Γm (m + 1) = Γm m := by
          funext i; simp only [Γm]
          have := i.isLt
          split_ifs <;> first | rfl | omega
        rw [this]; exact ih
  have : Γm n = Γ' := by funext i; simp [Γm, i.isLt]
  rw [← this]; exact key n

/-- A context consisting only of `I` assumptions derives `I`. -/
theorem IDeriv.units {n : ℕ} (Γ : ICtx n) (h : ∀ i, Γ i = none ∨ Γ i = some .unit) :
    IDeriv Γ .unit := by
  refine IDeriv.ctxwise (Γ := Ctx.empty n) (fun i => ?_)
    ⟨_, IHasType.star (fun _ => rfl)⟩
  rcases h i with h | h <;> rw [h]
  · exact PosEnt.refl _
  · exact PosEnt.addUnit

end LinExp

end
