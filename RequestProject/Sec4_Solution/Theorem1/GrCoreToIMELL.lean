module

public import RequestProject.Sec4_Solution.Theorem1.Translations
public import RequestProject.Sec4_Solution.Theorem1.Sharing
public import RequestProject.Sec4_Solution.Theorem1.Promotion

/-!
# Section 4: Theorem 1, GrCore into IMELL (corrected translation)

For the adjusted calculus over `{0, 1, ω}` (with `hsup` given by equation (1)):

`Γ ⊢ t : A  ⟹  ∃ M. ⟦Γ⟧ ⊢_IMELL M : ⟦A⟧`

where `⟦□_0 A⟧ = I`, `⟦□_1 A⟧ = ⟦A⟧` and `⟦□_ω A⟧ = !⟦A⟧` (and graded assumptions
`x : [A]_r` are translated as `x : ⟦□_r A⟧`).  The proof is by induction on the GrCore
derivation; shared graded variables are contracted (`IDeriv.share`), and promotion uses
`IDeriv.promote_all`.
-/

@[expose] public section

namespace LinExp

/-! ### Reindexing lemmas for IMELL derivability -/

lemma IDeriv.append_assoc {m k₁ k₂ : ℕ} {Γ : ICtx m} {D₁ : ICtx k₁} {D₂ : ICtx k₂} {Z : ITy}
    (h : IDeriv (Ctx.append Γ (Ctx.append D₁ D₂)) Z) :
    IDeriv (Ctx.append (Ctx.append Γ D₁) D₂) Z := by
  refine h.rename (ρ := Fin.cast (Nat.add_assoc m k₁ k₂).symm) (Fin.cast_injective _)
    (fun i => ?_) (fun k hk => (hk (Fin.cast (Nat.add_assoc m k₁ k₂) k) (by ext; simp)).elim)
  simp only [Ctx.append, Fin.val_cast]
  by_cases h2 : i.val < k₂
  · simp [h2]; intro h; omega
  · by_cases h1 : i.val - k₂ < k₁
    · have : i.val < k₁ + k₂ := by omega
      simp [h2, h1, this]
    · have : ¬ i.val < k₁ + k₂ := by omega
      simp only [h2, dite_false, h1, this]
      congr 1; ext; simp; omega

lemma IDeriv.cons_append_swap {m k : ℕ} {Γ : ICtx m} {D : ICtx k} {B : ITy} {Z : ITy}
    (h : IDeriv (Ctx.cons (some B) (Ctx.append Γ D)) Z) :
    IDeriv (Ctx.append (Ctx.cons (some B) Γ) D) Z := by
  let ρ : Fin (m + k + 1) → Fin (m + 1 + k) := fun i =>
    if i.val = 0 then ⟨k, by omega⟩ else if i.val - 1 < k then ⟨i.val - 1, by omega⟩
    else ⟨i.val, by omega⟩
  have hρ : Function.Injective ρ := by
    intro a b hab
    simp only [ρ] at hab
    split_ifs at hab <;> simp [Fin.ext_iff] at hab <;> exact Fin.ext (by omega)
  refine h.rename hρ (fun i => ?_) (fun j hj => ?_)
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp only [ρ, Fin.val_zero, ↓reduceIte, Ctx.cons_zero]
      rw [Ctx.append_high _ _ _ (by simp)]
      simp [Ctx.cons]
    · simp only [ρ, Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
        Ctx.cons_succ]
      by_cases hi : i.val < k
      · simp only [hi, ↓reduceIte]
        rw [Ctx.append_low _ _ _ hi, Ctx.append_low _ _ _ (by simpa using hi)]
      · simp only [hi, ↓reduceIte]
        rw [Ctx.append_high _ _ _ hi, Ctx.append_high _ _ _ (by simp; omega)]
        have : (⟨i.val + 1 - k, by omega⟩ : Fin (m + 1)) = (⟨i.val - k, by omega⟩ : Fin m).succ :=
          Fin.ext (by simp; omega)
        rw [this]; rfl
  · exfalso
    by_cases hj1 : j.val < k
    · exact hj ⟨j.val + 1, by omega⟩ (by simp [ρ, hj1])
    · by_cases hj2 : j.val = k
      · exact hj 0 (by simp [ρ]; exact Fin.ext hj2.symm)
      · refine hj ⟨j.val, by omega⟩ ?_
        have h3 : ¬ (j.val = 0) := by omega
        have h4 : ¬ (j.val - 1 < k) := by omega
        simp only [ρ, h3, h4, ↓reduceIte]

lemma IDeriv.swap_into_ctx2 {m : ℕ} {Γ : ICtx m} {A B Z : ITy}
    (h : IDeriv (Ctx.cons (some A) (Ctx.cons (some B) Γ)) Z) :
    IDeriv (Ctx.append (Ctx.cons none Γ) (ctx2 A B)) Z := by
  let ρ : Fin (m + 1 + 1) → Fin (m + 1 + 2) := fun i =>
    if i.val = 0 then ⟨1, by omega⟩ else if i.val = 1 then ⟨0, by omega⟩
    else ⟨i.val + 1, by omega⟩
  have hρ : Function.Injective ρ := by
    intro a b hab
    simp only [ρ] at hab
    split_ifs at hab <;> simp only [Fin.ext_iff] at hab <;> exact Fin.ext (by omega)
  rw [append_ctx2]
  refine h.rename hρ (fun i => ?_) (fun j hj => ?_)
  · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · rfl
    · rfl
    · have e : ρ i.succ.succ = i.succ.succ.succ := by
        have h3 : ¬ (i.val + 1 + 1 = 0) := by omega
        have h4 : ¬ (i.val + 1 + 1 = 1) := by omega
        simp only [ρ, Fin.val_succ, h3, h4, ↓reduceIte]; rfl
      rw [e]; rfl
  · refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j) j hj
    · intro hj; exact absurd (by simp [ρ]) (hj 1)
    · intro hj; exact absurd (by simp [ρ]) (hj 0)
    · intro _; rfl
    · intro hj
      have h3 : ¬ (j.val + 1 + 1 = 0) := by omega
      have h4 : ¬ (j.val + 1 + 1 = 1) := by omega
      exact absurd (by simp only [ρ, Fin.val_succ, h3, h4, ↓reduceIte]; rfl) (hj j.succ.succ)

lemma IDeriv.addFront {m : ℕ} {Γ : ICtx m} {U Z : ITy} (hU : PosEnt none (some U))
    (h : IDeriv Γ Z) : IDeriv (Ctx.cons (some U) Γ) Z := by
  have h' : IDeriv (Ctx.cons none Γ) Z :=
    h.rename (Fin.succ_injective m) (fun _ => rfl)
      (fun j hj => Fin.cases (fun _ => rfl) (fun j hj => absurd rfl (hj j)) j hj)
  have e1 : Ctx.cons none Γ = Function.update (Ctx.cons (some U) Γ) 0 none := by
    funext k; refine Fin.cases ?_ (fun k => ?_) k <;> simp [Ctx.cons]
  have e2 : Ctx.cons (some U) Γ = Function.update (Ctx.cons (some U) Γ) 0 (some U) := by
    simp
  rw [e2]; rw [e1] at h'
  exact hU _ _ _ _ h'

/-- Elimination of a tensor in the first position. -/
lemma IDeriv.pairStep {k₁ k₂ : ℕ} {D₁ : ICtx k₁} {D₂ : ICtx k₂} {A B : ITy}
    (h₁ : ∀ (m : ℕ) (Γ : ICtx m) (Z : ITy), IDeriv (Ctx.append Γ D₁) Z →
      IDeriv (Ctx.cons (some A) Γ) Z)
    (h₂ : ∀ (m : ℕ) (Γ : ICtx m) (Z : ITy), IDeriv (Ctx.append Γ D₂) Z →
      IDeriv (Ctx.cons (some B) Γ) Z)
    (m : ℕ) (Γ : ICtx m) (Z : ITy) (h : IDeriv (Ctx.append Γ (Ctx.append D₁ D₂)) Z) :
    IDeriv (Ctx.cons (some (.tensor A B)) Γ) Z := by
  have s4 := h₁ _ _ _ (h₂ _ _ _ h.append_assoc).cons_append_swap
  obtain ⟨M, hM⟩ := s4.swap_into_ctx2
  refine ⟨_, IHasType.letPair (Γ₁ := isingle 0 (.tensor A B)) (Γ₂ := Ctx.cons none Γ)
    (isingle_var 0 _) hM (fun k => ?_)⟩
  refine Fin.cases ?_ (fun k => ?_) k
  · right; simp [isingle]
  · left; simp [isingle, Fin.succ_ne_zero]

/-! ### Properties of the corrected translation -/

lemma trCtx_cons {n : ℕ} (e : Option (Assm LNL)) (Γ : GCtx LNL n) :
    trCtx (Ctx.cons e Γ) = Ctx.cons (e.map trAssm) (trCtx Γ) := by
  funext k; refine Fin.cases ?_ (fun k => ?_) k <;> rfl

lemma trCtx_append {n k : ℕ} (Γ : GCtx LNL n) (Δ : GCtx LNL k) :
    trCtx (Ctx.append Γ Δ) = Ctx.append (trCtx Γ) (trCtx Δ) := by
  funext i; simp only [trCtx, Ctx.append]; split_ifs <;> rfl

lemma trCtx_update {n : ℕ} (Γ : GCtx LNL n) (i : Fin n) (e : Option (Assm LNL)) :
    trCtx (Function.update Γ i e) = Function.update (trCtx Γ) i (e.map trAssm) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [trCtx]
  · simp [trCtx, Function.update_of_ne hk]

lemma contract_tr (A : Ty LNL) (r s : LNL) :
    Contract (trTy (.box r A)) (trTy (.box s A)) (trTy (.box (r + s) A)) := by
  cases r <;> cases s
  · exact Contract.unit_left _
  · exact Contract.unit_left _
  · exact Contract.unit_left _
  · exact Contract.unit_right _
  · exact Contract.lin_lin _
  · exact Contract.lin_bang _
  · exact Contract.unit_right _
  · exact Contract.bang_lin _
  · exact Contract.bang _

lemma entryAdd_sadd {e₁ e₂ e : Option (Assm LNL)} (h : EntryAdd e₁ e₂ e) :
    SAdd (e₁.map trAssm) (e₂.map trAssm) (e.map trAssm) := by
  cases h with
  | noneLeft e => exact SAdd.noneLeft _
  | noneRight a => exact SAdd.noneRight _
  | grad A r s => exact SAdd.share _ _ _ (contract_tr A r s)

lemma ctxAdd_sadd {n : ℕ} {Γ₁ Γ₂ Γ : GCtx LNL n} (h : CtxAdd Γ₁ Γ₂ Γ) :
    ∀ i, SAdd (trCtx Γ₁ i) (trCtx Γ₂ i) (trCtx Γ i) := fun i => entryAdd_sadd (h i)

lemma posEnt_approx (A : Ty LNL) {r s : LNL} (h : r ≤ s) :
    PosEnt (some (trTy (.box r A))) (some (trTy (.box s A))) := by
  rcases h with rfl | rfl
  · exact PosEnt.refl _
  · cases r
    · exact PosEnt.removeUnit.trans (PosEnt.addBang _)
    · exact PosEnt.derelict _
    · exact PosEnt.refl _

/-- Translation of an optional grade acting on a type. -/
def trOpt : Option LNL → Ty LNL → ITy
  | none, A => trTy A
  | some r, A => trTy (.box r A)

/-- Pattern matching in IMELL: a pattern `?r ⊢ p : A ▷ Δ` can be eliminated. -/
theorem patTy_tr {k : ℕ} {o : Option LNL} {p : Pat k} {A : Ty LNL} {Δ : GCtx LNL k}
    (h : PatTy HSup.hsup o p A Δ) :
    ∀ (m : ℕ) (Γ : ICtx m) (Z : ITy), IDeriv (Ctx.append Γ (trCtx Δ)) Z →
      IDeriv (Ctx.cons (some (trOpt o A)) Γ) Z := by
  induction h with
  | var A =>
    intro m Γ Z hd; rw [Ctx.append_one] at hd; exact hd
  | pair _ _ ih1 ih2 =>
    intro m Γ Z hd
    rw [trCtx_append] at hd
    exact IDeriv.pairStep ih1 ih2 m Γ Z hd
  | box r _ ih => exact ih
  | gvar r A =>
    intro m Γ Z hd; rw [Ctx.append_one] at hd; exact hd
  | gpair _ _ hst ih1 ih2 =>
    obtain ⟨rfl, rfl, rfl⟩ := LNL.hsup_eq_some.mp hst
    intro m Γ Z hd
    rw [trCtx_append] at hd
    exact IDeriv.pairStep ih1 ih2 m Γ Z hd
  | unit o =>
    intro m Γ Z hd
    rw [Ctx.append_zero] at hd
    rcases o with _ | r
    · exact hd.addFront PosEnt.addUnit
    · cases r
      · exact hd.addFront PosEnt.addUnit
      · exact hd.addFront PosEnt.addUnit
      · exact hd.addFront (PosEnt.addBang _)

/-! ### The theorem -/

/-- **Theorem 1 (GrCore into IMELL), corrected.**  Every derivable judgement `Γ ⊢ t : A` of
the adjusted calculus over `{0, 1, ω}` translates to a provable IMELL sequent
`⟦Γ⟧ ⊢ M : ⟦A⟧`, where `⟦□_0 A⟧ = I`, `⟦□_1 A⟧ = ⟦A⟧`, `⟦□_ω A⟧ = !⟦A⟧`. -/
theorem theorem1_grcore_to_imell {n : ℕ} {Γ : GCtx LNL n} {t : Term n} {A : Ty LNL}
    (h : AdjTyped Γ t A) : ∃ M, IHasType (trCtx Γ) M (trTy A) := by
  induction h with
  | @var n Γ i A hi hj =>
    exact ⟨.var i, IHasType.var (by simp [trCtx, hi, trAssm])
      (fun j hne => by simp [trCtx, hj j hne])⟩
  | lam _ ih =>
    obtain ⟨M, hM⟩ := ih
    rw [trCtx_cons] at hM
    exact ⟨_, IHasType.lam hM⟩
  | app _ _ hadd ih1 ih2 =>
    exact IDeriv.share (fun m Δ₁ Δ₂ Δ hs ⟨M, hM⟩ ⟨N, hN⟩ => ⟨_, IHasType.app hM hN hs⟩)
      _ _ _ _ (ctxAdd_sadd hadd) ih1 ih2
  | @der n Γ t A B i _ hi ih =>
    have : trCtx (Function.update Γ i (some (.grad A 1))) = trCtx Γ := by
      rw [trCtx_update]; simp only [Option.map_some]
      rw [show trAssm (.grad A 1) = trAssm (.lin A) from rfl, ← Option.map_some, ← hi]
      exact Function.update_eq_self _ _
    rw [this]; exact ih
  | @weak n Γ Δ Γ' t A _ hz hadd ih =>
    refine IDeriv.share (Y := .unit)
      (fun m Δ₁ Δ₂ Δ hs ⟨M, hM⟩ ⟨N, hN⟩ => ⟨_, IHasType.letStar hN hM hs.symm⟩)
      _ _ _ _ (ctxAdd_sadd hadd) ih (IDeriv.units _ (fun i => ?_))
    rcases hz i with h | ⟨B, h⟩ <;> simp [trCtx, h, trAssm, trTy]
  | @approx n Γ t A B i r s _ hi hrs ih =>
    refine IDeriv.ctxwise (fun j => ?_) ih
    rw [trCtx_update]
    by_cases hj : j = i
    · subst hj; simp only [trCtx, hi, Option.map_some, Function.update_self, trAssm]
      exact posEnt_approx A hrs
    · rw [Function.update_of_ne hj]; exact PosEnt.refl _
  | @pr n Γ t A r _ hg ih =>
    cases r with
    | zero =>
      refine IDeriv.units _ (fun i => ?_)
      rcases h : Γ i with _ | ⟨B⟩ | ⟨B, s⟩
      · simp [trCtx, scale, h]
      · exact absurd h (hg i B)
      · right; simp only [trCtx, scale, h, Option.map_some, Assm.scale, trAssm]
        cases s <;> rfl
    | one =>
      have e : scale (1 : LNL) Γ = Γ := by
        funext i
        rcases h : Γ i with _ | ⟨B⟩ | ⟨B, s⟩ <;> simp [scale, Assm.scale, h]
        cases s <;> rfl
      show ∃ M, IHasType (trCtx (scale (1 : LNL) Γ)) M (trTy A)
      rw [e]; exact ih
    | many =>
      let Γa : ICtx n := fun i => match Γ i with
        | some (.grad B .one) => some (.bang (trTy B))
        | some (.grad B .many) => some (.bang (trTy B))
        | _ => none
      have h1 : IDeriv Γa (trTy A) := by
        refine IDeriv.ctxwise (fun i => ?_) ih
        rcases h : Γ i with _ | ⟨B⟩ | ⟨B, s⟩
        · simp only [trCtx, h, Option.map_none, Γa]; exact PosEnt.refl _
        · exact absurd h (hg i B)
        · cases s
          · simp only [trCtx, h, Option.map_some, trAssm, trTy, Γa]; exact PosEnt.removeUnit
          · simp only [trCtx, h, Option.map_some, trAssm, trTy, Γa]; exact PosEnt.derelict _
          · simp only [trCtx, h, Option.map_some, trAssm, trTy, Γa]; exact PosEnt.refl _
      have h2 : IDeriv Γa (.bang (trTy A)) := by
        refine IDeriv.promote_all Γa (fun i => ?_) h1
        simp only [Γa]
        rcases Γ i with _ | ⟨B⟩ | ⟨B, s⟩
        · left; rfl
        · left; rfl
        · cases s
          · left; rfl
          · right; exact ⟨_, rfl⟩
          · right; exact ⟨_, rfl⟩
      refine IDeriv.ctxwise (fun i => ?_) h2
      rcases h : Γ i with _ | ⟨B⟩ | ⟨B, s⟩
      · simp only [trCtx, scale, h, Option.map_none, Γa]; exact PosEnt.refl _
      · exact absurd h (hg i B)
      · cases s
        · simp only [trCtx, scale, h, Option.map_some, Assm.scale, Γa]
          exact PosEnt.addUnit
        · simp only [trCtx, scale, h, Option.map_some, Assm.scale, Γa]; exact PosEnt.refl _
        · simp only [trCtx, scale, h, Option.map_some, Assm.scale, Γa]; exact PosEnt.refl _
  | unit hΓ =>
    exact ⟨_, IHasType.star (fun i => by simp [trCtx, hΓ i])⟩
  | pair _ _ hadd ih1 ih2 =>
    exact IDeriv.share (fun m Δ₁ Δ₂ Δ hs ⟨M, hM⟩ ⟨N, hN⟩ => ⟨_, IHasType.pair hM hN hs⟩)
      _ _ _ _ (ctxAdd_sadd hadd) ih1 ih2
  | letPat _ hp _ hadd ih1 ih2 =>
    rw [trCtx_append] at ih2
    obtain ⟨F, hF⟩ := patTy_tr hp _ _ _ ih2
    exact IDeriv.share (fun m Δ₁ Δ₂ Δ hs ⟨M, hM⟩ ⟨N, hN⟩ => ⟨_, IHasType.app hN hM hs.symm⟩)
      _ _ _ _ (ctxAdd_sadd hadd) ih1 ⟨_, IHasType.lam hF⟩

end LinExp

end
