module

public import RequestProject.Sec2_CoreCalculus.Derivation
public import RequestProject.Sec4_Solution.Theorem1.Explicit.Pattern

/-!
# Section 4 (Theorem 1): the GrCore → IMELL term translation, written out

`trDeriv d` is the IMELL term obtained from a GrCore derivation `d : Γ ⊢ t : A` (of the
adjusted calculus over `{0, 1, ω}`), by recursion on `d`.  The translation of types and
contexts is the corrected one of `Translations.lean` (`⟦□_0 A⟧ = I`, `⟦□_1 A⟧ = ⟦A⟧`,
`⟦□_ω A⟧ = !⟦A⟧`).  Rule by rule:

* `x ↦ x`, `λx.t ↦ λx.⟦t⟧`;
* `t₁ t₂ ↦ ⟦t₁⟧ ⟦t₂⟧`, `(t₁, t₂) ↦ ⟦t₁⟧ ⊗ ⟦t₂⟧` and `let p = t₁ in t₂ ↦ (λz. ⟦p⟧(⟦t₂⟧)) ⟦t₁⟧`,
  where every graded variable used by both premises (grades `r` and `s`) is first split with
  the colax map `n_{r,s} : ⟦□_{r+s} A⟧ ⊸ ⟦□_r A⟧ ⊗ ⟦□_s A⟧` (`shareL`, `splitTm`), and
  `⟦p⟧` is pattern elimination (`patElim`);
* `DER` is the identity (`⟦[A]_1⟧ = ⟦A⟧`); `WEAK` consumes every new `x : [A]_0` (an
  assumption `x : I`) with `let x be * in _`; `APPROX` from `0` to `ω` replaces `x : I` by
  `x : !A` (`discard x in *`), from `1` to `ω` uses `derelict`;
* `PR` at grade `0` builds `*` after consuming all (unit) assumptions; at grade `1` it is the
  identity; at grade `ω` it uses Benton et al.'s `promote` (`promoteTm`), after removing the
  `I`-assumptions and derelicting the grade-`1` assumptions.

Main result: `trDeriv_typed : IHasType (trCtx Γ) (trDeriv d) (trTy A)`.
-/

@[expose] public section

namespace LinExp

/-! ### Auxiliary functions on GrCore context entries -/

/-- The grade of a graded assumption (`0` otherwise). -/
def entryGrade : Option (Assm LNL) → LNL
  | some (.grad _ r) => r
  | _ => .zero

/-- The variables used by both premises of a binary rule, with their two grades. -/
def sharedList {n : ℕ} (Γ₁ Γ₂ : GCtx LNL n) : List (Fin n × LNL × LNL) :=
  ((List.finRange n).filter (fun i => (Γ₁ i).isSome && (Γ₂ i).isSome)).map
    (fun i => (i, entryGrade (Γ₁ i), entryGrade (Γ₂ i)))

/-- `WEAK`: a variable that is only present in the weakening context `[Δ]_0` is consumed. -/
def weakKind : Option (Assm LNL) → Option (Assm LNL) → AdjKind
  | none, some _ => .addUnit
  | _, _ => .keep

/-- `APPROX` from grade `r` to grade `s`. -/
def approxKind : LNL → LNL → AdjKind
  | .zero, .many => .unitToBang
  | .one, .many => .derel
  | _, _ => .keep

/-- `PR` at grade `0`: every (unit) assumption is consumed. -/
def prZeroKind : Option (Assm LNL) → AdjKind
  | some _ => .addUnit
  | none => .keep

/-- `PR` at grade `ω`, before promotion: remove units, derelict grade-`1` assumptions. -/
def prManyPre : Option (Assm LNL) → AdjKind
  | some (.grad _ .zero) => .dropUnit
  | some (.grad _ .one) => .derel
  | _ => .keep

/-- `PR` at grade `ω`: the positions that are arguments of `promote`. -/
def prManyArg : Option (Assm LNL) → Bool
  | some (.grad _ .one) => true
  | some (.grad _ .many) => true
  | _ => false

/-- `PR` at grade `ω`, after promotion: consume the unit assumptions again. -/
def prManyPost : Option (Assm LNL) → AdjKind
  | some (.grad _ .zero) => .addUnit
  | _ => .keep

/-- The context in which `promote` is applied in the translation of `PR` at grade `ω`. -/
def prManyMid : Option (Assm LNL) → Option ITy
  | some (.grad B .one) => some (.bang (trTy B))
  | some (.grad B .many) => some (.bang (trTy B))
  | _ => none

/-- Translation of the rule `PR` at grade `r` (from the context `Γ` of the premise). -/
def prTerm {n : ℕ} (Γ : GCtx LNL n) : LNL → ITerm n → ITerm n
  | .zero, _ => adjustAll (fun i => prZeroKind (Γ i)) .star
  | .one, M => M
  | .many, M => adjustAll (fun i => prManyPost (Γ i))
      (promoteTm (fun i => prManyArg (Γ i)) (adjustAll (fun i => prManyPre (Γ i)) M))

/-! ### The translation -/

/-- **The GrCore → IMELL translation of Theorem 1**, by recursion on typing derivations of the
adjusted calculus over `{0, 1, ω}`. -/
def trDeriv : {n : ℕ} → {Γ : GCtx LNL n} → {t : Term n} → {A : Ty LNL} →
    Derivation HSup.hsup Γ t A → ITerm n
  | _, _, _, _, .var (i := i) _ _ => .var i
  | _, _, _, _, .lam d => .lam (trDeriv d)
  | _, _, _, _, .app Γ₁ Γ₂ _ d₁ d₂ _ =>
    shareL (fun M N => .app M N) (sharedList Γ₁ Γ₂) (trDeriv d₁) (trDeriv d₂)
  | _, _, _, _, .der d _ => trDeriv d
  | _, _, _, _, .weak Γ Δ d _ _ => adjustAll (fun i => weakKind (Γ i) (Δ i)) (trDeriv d)
  | _, _, _, _, .approx i r s d _ _ => adjustAt i (approxKind r s) (trDeriv d)
  | _, _, _, _, .pr Γ r d _ => prTerm Γ r (trDeriv d)
  | _, _, _, _, .unit _ => .star
  | _, _, _, _, .pair Γ₁ Γ₂ d₁ d₂ _ =>
    shareL (fun M N => .pair M N) (sharedList Γ₁ Γ₂) (trDeriv d₁) (trDeriv d₂)
  | _, _, _, _, .letPat Γ₁ Γ₂ p A d₁ _ d₂ _ =>
    shareL (fun M N => .app N M) (sharedList Γ₁ Γ₂) (trDeriv d₁)
      (.lam (patElim p none A (trDeriv d₂)))

/-! ### Correctness -/

lemma entryAdd_inv {e₁ e₂ e : Option (Assm LNL)} (h : EntryAdd e₁ e₂ e) :
    (e₁ = none ∧ e₂ = e) ∨ (∃ a, e₁ = some a ∧ e₂ = none ∧ e = some a) ∨
      (∃ A r s, e₁ = some (.grad A r) ∧ e₂ = some (.grad A s) ∧ e = some (.grad A (r + s))) := by
  cases h with
  | noneLeft => exact Or.inl ⟨rfl, rfl⟩
  | noneRight a => exact Or.inr (Or.inl ⟨a, rfl, rfl, rfl⟩)
  | grad A r s => exact Or.inr (Or.inr ⟨A, r, s, rfl, rfl, rfl⟩)

lemma sharedList_typed {n : ℕ} {Γ₁ Γ₂ Γ : GCtx LNL n} (hadd : CtxAdd Γ₁ Γ₂ Γ)
    (F : ∀ {m : ℕ}, ITerm m → ITerm m → ITerm m) {X Y Z : ITy}
    (rule : ∀ {m : ℕ} {Δ₁ Δ₂ Δ : ICtx m} {M N : ITerm m}, ISplit Δ₁ Δ₂ Δ →
      IHasType Δ₁ M X → IHasType Δ₂ N Y → IHasType Δ (F M N) Z)
    {P₁ P₂ : ITerm n} (h₁ : IHasType (trCtx Γ₁) P₁ X) (h₂ : IHasType (trCtx Γ₂) P₂ Y) :
    IHasType (trCtx Γ) (shareL F (sharedList Γ₁ Γ₂) P₁ P₂) Z := by
  have hfst : (sharedList Γ₁ Γ₂).map Prod.fst =
      (List.finRange n).filter (fun i => (Γ₁ i).isSome && (Γ₂ i).isSome) := by
    simp [sharedList, List.map_map, Function.comp_def]
  refine shareL_typed F rule _ ?_ (fun i hi => ?_) (fun x hx => ?_) h₁ h₂
  · rw [hfst]; exact (List.nodup_finRange n).filter _
  · rw [hfst] at hi
    simp only [List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true,
      Option.isSome_iff_ne_none, ne_eq, not_and, not_not] at hi
    rcases entryAdd_inv (hadd i) with ⟨h1, h2⟩ | ⟨a, h1, h2, h3⟩ | ⟨A, r, s, h1, h2, h3⟩
    · left; simp [trCtx, h1, h2]
    · right; simp [trCtx, h1, h2, h3]
    · exfalso; exact absurd (hi (by simp [h1])) (by simp [h2])
  · simp only [sharedList, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      Bool.and_eq_true, Option.isSome_iff_ne_none, ne_eq] at hx
    obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hx
    rcases entryAdd_inv (hadd i) with ⟨h1, h2⟩ | ⟨a, h1, h2, h3⟩ | ⟨A, r, s, h1, h2, h3⟩
    · exact absurd h1 hi1
    · exact absurd h2 hi2
    · exact ⟨A, by simp [trCtx, h1, entryGrade, trAssm], by simp [trCtx, h2, entryGrade, trAssm],
        by simp [trCtx, h1, h2, h3, entryGrade, trAssm]⟩

theorem prTerm_typed {n : ℕ} {Γ : GCtx LNL n} (hg : IsGraded Γ) (r : LNL) {M : ITerm n}
    {A : Ty LNL} (hM : IHasType (trCtx Γ) M (trTy A)) :
    IHasType (trCtx (scale r Γ)) (prTerm Γ r M) (trTy (.box r A)) := by
  cases r with
  | zero =>
    refine adjustAll_typed (Γ := Ctx.empty n) _ (fun i => ?_) (IHasType.star (fun _ => rfl))
    rcases h : Γ i with _ | ⟨B⟩ | ⟨B, s⟩
    · simp [trCtx, scale, h, prZeroKind, KindOK, Ctx.empty]
    · exact absurd h (hg i B)
    · simp only [trCtx, scale, h, Option.map_some, Assm.scale, trAssm, prZeroKind, KindOK,
        Ctx.empty, true_and]
      cases s <;> rfl
  | one =>
    have e : scale (1 : LNL) Γ = Γ := by
      funext i
      rcases h : Γ i with _ | ⟨B⟩ | ⟨B, s⟩ <;> simp [scale, Assm.scale, h]
      cases s <;> rfl
    show IHasType (trCtx (scale (1 : LNL) Γ)) M (trTy A)
    rw [e]; exact hM
  | many =>
    let Γa : ICtx n := fun i => prManyMid (Γ i)
    have h1 : IHasType Γa (adjustAll (fun i => prManyPre (Γ i)) M) (trTy A) := by
      refine adjustAll_typed _ (fun i => ?_) hM
      rcases h : Γ i with _ | ⟨B⟩ | ⟨B, s⟩
      · simp [trCtx, h, Γa, prManyMid, prManyPre, KindOK]
      · exact absurd h (hg i B)
      · cases s <;> simp [trCtx, h, Γa, prManyMid, prManyPre, KindOK, trAssm, trTy]
    have h2 := promoteTm_typed Γa (fun i => prManyArg (Γ i)) (fun i => by
      rcases h : Γ i with _ | ⟨B⟩ | ⟨B, s⟩
      · simp [h, Γa, prManyMid, prManyArg]
      · simp [h, Γa, prManyMid, prManyArg]
      · cases s <;> simp [h, Γa, prManyMid, prManyArg]) h1
    refine adjustAll_typed _ (fun i => ?_) h2
    rcases h : Γ i with _ | ⟨B⟩ | ⟨B, s⟩
    · simp [trCtx, scale, h, Γa, prManyMid, prManyPost, KindOK]
    · exact absurd h (hg i B)
    · cases s <;> simp [trCtx, scale, h, Γa, prManyMid, prManyPost, KindOK, Assm.scale,
        trAssm] <;> rfl

/-- **Correctness of the translation**: the translation of a derivation of `Γ ⊢ t : A`
is an IMELL term of type `⟦A⟧` in context `⟦Γ⟧`. -/
theorem trDeriv_typed {n : ℕ} {Γ : GCtx LNL n} {t : Term n} {A : Ty LNL}
    (d : Derivation HSup.hsup Γ t A) : IHasType (trCtx Γ) (trDeriv d) (trTy A) := by
  induction d with
  | @var n Γ i A hi hj =>
    exact IHasType.var (by simp [trCtx, hi, trAssm]) (fun j hne => by simp [trCtx, hj j hne])
  | lam d ih =>
    rw [trCtx_cons] at ih
    exact IHasType.lam ih
  | app Γ₁ Γ₂ A d₁ d₂ hadd ih1 ih2 =>
    exact sharedList_typed hadd _ (fun hs h1 h2 => IHasType.app h1 h2 hs) ih1 ih2
  | @der n Γ t A B i d hi ih =>
    have : trCtx (Function.update Γ i (some (.grad A 1))) = trCtx Γ := by
      rw [trCtx_update]; simp only [Option.map_some]
      rw [show trAssm (.grad A 1) = trAssm (.lin A) from rfl, ← Option.map_some, ← hi]
      exact Function.update_eq_self _ _
    rw [this]; exact ih
  | @weak n Γ Δ Γ' t A d hz hadd ih =>
    refine adjustAll_typed _ (fun i => ?_) ih
    rcases entryAdd_inv (hadd i) with ⟨h1, h3⟩ | ⟨a, h1, h2, h3⟩ | ⟨B, r, s, h1, h2, h3⟩
    · rcases hz i with h | ⟨B, h⟩
      · simp [trCtx, h1, ← h3, h, weakKind, KindOK]
      · simp [trCtx, h1, ← h3, h, weakKind, KindOK, trAssm, trTy]
    · simp [trCtx, h1, h2, h3, weakKind, KindOK]
    · rcases hz i with h | ⟨B', h⟩
      · rw [h] at h2; simp at h2
      · rw [h] at h2
        simp only [Option.some.injEq, Assm.grad.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        simp [trCtx, h1, h3, weakKind, KindOK]
        rfl
  | @approx n Γ t A B i r s d hi hrs ih =>
    refine adjustAt_typed' i ?_ (fun j hj => by simp [trCtx, Function.update_of_ne hj]) ih
    simp only [trCtx, hi, Option.map_some, Function.update_self, trAssm]
    rcases hrs with rfl | rfl
    · cases r <;> rfl
    · cases r
      · exact ⟨rfl, _, rfl⟩
      · exact ⟨_, rfl, rfl⟩
      · rfl
  | pr Γ r d hg ih => exact prTerm_typed hg r ih
  | unit hΓ =>
    exact IHasType.star (fun i => by simp [trCtx, hΓ i])
  | pair Γ₁ Γ₂ d₁ d₂ hadd ih1 ih2 =>
    exact sharedList_typed hadd _ (fun hs h1 h2 => IHasType.pair h1 h2 hs) ih1 ih2
  | letPat Γ₁ Γ₂ p A d₁ hp d₂ hadd ih1 ih2 =>
    rw [trCtx_append] at ih2
    exact sharedList_typed hadd _ (fun hs h1 h2 => IHasType.app h2 h1 hs.symm) ih1
      (IHasType.lam (patElim_typed hp ih2))

/-- Example: the derivation of `⊢ λx. x : A ⊸ A` translates to the IMELL term `λx. x`. -/
example (A : Ty LNL) :
    trDeriv (Derivation.lam (Γ := Ctx.empty 0) (A := A) (B := A)
      (Derivation.var (hs := HSup.hsup) (i := 0) rfl
        (fun j hj => absurd (Fin.ext (by omega)) hj))) =
      .lam (.var 0) := rfl

end LinExp

end
