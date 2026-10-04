module

public import RequestProject.Sec4_Solution.Theorem1.Translations
public import RequestProject.Sec4_Solution.Theorem1.Admissible
public import RequestProject.Sec2_CoreCalculus.Derived

/-!
# Section 4: Theorem 1, IMELL into GrCore

`Γ ⊢_IMELL M : T  ⟹  ⟦Γ⟧ ⊢ ⟦M⟧ : ⟦T⟧` in the adjusted calculus over `{0, 1, ω}`, where
`⟦!A⟧ = □_ω ⟦A⟧`, IMELL assumptions become linear assumptions, and `⟦M⟧` is the following
syntactic translation of Benton et al.'s terms:

* `let M be * in N ↦ let unit = ⟦M⟧ in ⟦N⟧`
* `let M be x ⊗ y in N ↦ let (x, y) = ⟦M⟧ in ⟦N⟧`
* `derelict M ↦ let [z] = ⟦M⟧ in z`
* `discard M in N ↦ let [z] = ⟦M⟧ in ⟦N⟧`
* `copy M as x, y in N ↦ let [z] = ⟦M⟧ in (λx. λy. ⟦N⟧) [z] [z]`
* `promote M₁ … Mₖ for x₁ … xₖ in N ↦ ap (… ap ([λx₁ … λxₖ. ⟦N⟧], ⟦Mₖ⟧) …) ⟦M₁⟧`,
  where `ap(G, M) = let [f] = G in let [c] = M in [f [c]]`.
-/

@[expose] public section

namespace LinExp

namespace Term

/-- `lams k t = λ … λ. t` (`k` abstractions; the innermost binds index `0`). -/
def lams {n : ℕ} : (k : ℕ) → Term (n + k) → Term n
  | 0, t => t
  | k + 1, t => lams k (.lam t)

/-- `ap G M = let [f] = G in let [c] = M in [f [c]]`: applicative action of `□_ω`. -/
def ap {n : ℕ} (G M : Term n) : Term n :=
  .letPat (.box .var) G
    (.letPat (.box .var) M.shift (.box (.app (.var 1) (.box (.var 0)))))

/-- Iterated `ap`: `apN k G Ms = ap (ap (… (ap G (Ms (k-1))) …) (Ms 1)) (Ms 0)`. -/
def apN {n : ℕ} : (k : ℕ) → Term n → (Fin k → Term n) → Term n
  | 0, G, _ => G
  | k + 1, G, Ms => ap (apN k G (fun j => Ms j.succ)) (Ms 0)

/-- Embedding of `k` variables as the innermost indices of a scope of size `n + k`. -/
def embedLow (n k : ℕ) : Fin k → Fin (n + k) := fun j => ⟨j.val, by omega⟩

end Term

/-- The translation of IMELL terms into GrCore terms. -/
def trTerm {n : ℕ} : ITerm n → Term n
  | .var i => .var i
  | .lam M => .lam (trTerm M)
  | .app M N => .app (trTerm M) (trTerm N)
  | .star => .unit
  | .letStar M N => .letPat .unit (trTerm M) (trTerm N)
  | .pair M N => .pair (trTerm M) (trTerm N)
  | .letPair M N => .letPat (.pair .var .var) (trTerm M) (trTerm N)
  | .promote (k := k) Ms N =>
      Term.apN k (.box (Term.lams k ((trTerm N).rename (Term.embedLow n k))))
        (fun j => trTerm (Ms j))
  | .derelict M => .letPat (.box .var) (trTerm M) (.var 0)
  | .discard M N => .letPat (.box .var) (trTerm M) (trTerm N).shift
  | .copy M N => .letPat (.box .var) (trTerm M)
      (.app (.app (.lam (.lam ((trTerm N).rename (Ctx.liftN 2 Fin.succ)))) (.box (.var 0)))
        (.box (.var 0)))

/-! ### Auxiliary typing lemmas -/

open LNL

/-- `A₀ ⊸ … ⊸ C` with the arguments taken from the end: `arrows (k+1) B C =
arrows k (B ∘ succ) (B 0 ⊸ C)`. -/
def arrows : (k : ℕ) → (Fin k → Ty LNL) → Ty LNL → Ty LNL
  | 0, _, C => C
  | k + 1, B, C => arrows k (fun j => B j.succ) (.lolli (B 0) C)

lemma typed_lams {n : ℕ} : ∀ (k : ℕ) (Γ : GCtx LNL n) (B : Fin k → Ty LNL) (C : Ty LNL)
    (t : Term (n + k)),
    AdjTyped (Ctx.append Γ (fun j => some (.lin (B j)))) t C →
    AdjTyped Γ (Term.lams k t) (arrows k B C)
  | 0, Γ, B, C, t, h => by simpa using h
  | k + 1, Γ, B, C, t, h => by
    rw [Ctx.append_succ] at h
    exact typed_lams k Γ (fun j => B j.succ) _ _ (Typed.lam h)

/-- Sums of contexts starting from a base context. -/
def SumFrom {n : ℕ} : (k : ℕ) → GCtx LNL n → (Fin k → GCtx LNL n) → GCtx LNL n → Prop
  | 0, B, _, Γ => Γ = B
  | k + 1, B, Γs, Γ => ∃ Γ', SumFrom k B (fun j => Γs j.succ) Γ' ∧ CtxAdd Γ' (Γs 0) Γ

lemma typed_ap {n : ℕ} {Γ₁ Γ₂ Γ : GCtx LNL n} {G M : Term n} {A R : Ty LNL}
    (hG : AdjTyped Γ₁ G (□[ω] (□[ω] A ⊸ R))) (hM : AdjTyped Γ₂ M (□[ω] A))
    (hadd : CtxAdd Γ₁ Γ₂ Γ) : AdjTyped Γ (Term.ap G M) (□[ω] R) := by
  let F : Ty LNL := □[ω] A ⊸ R
  let Z : GCtx LNL (n + 1) := Ctx.cons (some (.grad F ω)) (Ctx.empty n)
  refine Typed.letPat hG (PatTy.box ω (PatTy.gvar ω F)) ?_ hadd
  rw [Ctx.append_one]
  refine Typed.letPat (Γ₂ := Z) hM.shift (PatTy.box ω (PatTy.gvar ω A)) ?_ ?_
  · rw [Ctx.append_one]
    let Γb : GCtx LNL (n + 1 + 1) :=
      Ctx.cons (some (.grad A ω)) (Ctx.cons (some (.grad F 1)) (Ctx.empty n))
    have hb : AdjTyped Γb (.app (.var 1) (.box (.var 0))) R := by
      refine Typed.app (Γ₁ := Ctx.cons none (Ctx.cons (some (.grad F 1)) (Ctx.empty n)))
        (Γ₂ := Ctx.cons (some (.grad A ω)) (Ctx.cons none (Ctx.empty n)))
        (Typed.var_one rfl (fun j hj => ?_)) (Typed.box_var rfl (fun j hj => ?_)) (fun i => ?_)
      · refine Fin.cases (fun _ => rfl) (fun j => Fin.cases (fun hj => absurd rfl hj)
          (fun j _ => rfl) j) j hj
      · refine Fin.cases (fun hj => absurd rfl hj) (fun j _ => Fin.cases rfl (fun j => rfl) j) j hj
      · refine Fin.cases (EntryAdd.noneLeft _) (fun i => Fin.cases (EntryAdd.noneRight _)
          (fun i => EntryAdd.noneLeft _) i) i
    refine (Typed.pr ω hb (fun i B => ?_)).of_eq ?_
    · refine Fin.cases (by simp [Γb]) (fun i => Fin.cases (by simp [Γb, Ctx.cons])
        (fun i => by simp [Γb, Ctx.cons, Ctx.empty]) i) i
    · funext i
      refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i
  · intro i
    refine Fin.cases (EntryAdd.noneLeft _) (fun i => ?_) i
    simp only [Z, Ctx.cons_succ, Ctx.empty]
    rcases Γ₂ i with _ | a
    · exact EntryAdd.noneLeft _
    · exact EntryAdd.noneRight _

lemma typed_apN {n : ℕ} : ∀ (k : ℕ) (G : Term n) (Ms : Fin k → Term n) (As : Fin k → Ty LNL)
    (C : Ty LNL) (ΓG : GCtx LNL n) (Γs : Fin k → GCtx LNL n) (Γ : GCtx LNL n),
    AdjTyped ΓG G (□[ω] (arrows k (fun j => □[ω] (As j)) C)) →
    (∀ j, AdjTyped (Γs j) (Ms j) (□[ω] (As j))) → SumFrom k ΓG Γs Γ →
    AdjTyped Γ (Term.apN k G Ms) (□[ω] C)
  | 0, G, Ms, As, C, ΓG, Γs, Γ, hG, _, hsum => by
    rw [show Γ = ΓG from hsum]; exact hG
  | k + 1, G, Ms, As, C, ΓG, Γs, Γ, hG, hMs, ⟨Γ', hsum, hadd⟩ =>
    typed_ap (typed_apN k G (fun j => Ms j.succ) (fun j => As j.succ) _ ΓG _ Γ' hG
      (fun j => hMs j.succ) hsum) (hMs 0) hadd

/-! ### Properties of the translation of contexts -/

lemma trCtxI_cons {n : ℕ} (A : ITy) (Γ : ICtx n) :
    trCtxI (Ctx.cons (some A) Γ) = Ctx.cons (some (.lin (trTyI A))) (trCtxI Γ) := by
  funext k; refine Fin.cases ?_ (fun k => ?_) k <;> rfl

lemma trCtxI_append {n k : ℕ} (Γ : ICtx n) (Δ : ICtx k) :
    trCtxI (Ctx.append Γ Δ) = Ctx.append (trCtxI Γ) (trCtxI Δ) := by
  funext i; simp only [trCtxI, Ctx.append]; split_ifs <;> rfl

lemma ISplit.ctxAdd {n : ℕ} {Γ₁ Γ₂ Γ : ICtx n} (h : ISplit Γ₁ Γ₂ Γ) :
    CtxAdd (trCtxI Γ₁) (trCtxI Γ₂) (trCtxI Γ) := by
  intro i
  simp only [trCtxI]
  rcases h i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact EntryAdd.noneLeft _
  · rw [h1, ← h2]
    rcases Γ₁ i with _ | a
    · exact EntryAdd.noneLeft _
    · exact EntryAdd.noneRight _

lemma ISplitN.sumFrom {n : ℕ} : ∀ (k : ℕ) (Γs : Fin k → ICtx n) (Γ : ICtx n),
    ISplitN k Γs Γ → SumFrom k (Ctx.empty n) (fun j => trCtxI (Γs j)) (trCtxI Γ)
  | 0, Γs, Γ, h => by
    show trCtxI Γ = Ctx.empty n
    funext i; simp [trCtxI, h i, Ctx.empty]
  | k + 1, Γs, Γ, ⟨Γ', h1, h2⟩ =>
    ⟨trCtxI Γ', ISplitN.sumFrom k _ Γ' h1, h2.symm.ctxAdd⟩

lemma trCtxI_ctx2 (A B : ITy) :
    trCtxI (ctx2 A B) = Ctx.append (fun _ => some (Assm.lin (trTyI A)) : GCtx LNL 1)
      (fun _ => some (Assm.lin (trTyI B)) : GCtx LNL 1) := by
  funext i; fin_cases i <;> rfl

/-! ### The theorem -/

/-- **Theorem 1 (IMELL into GrCore).**  If `Γ ⊢ M : T` in IMELL then `⟦Γ⟧ ⊢ ⟦M⟧ : ⟦T⟧` in
the adjusted calculus over `{0, 1, ω}`, with `⟦!A⟧ = □_ω ⟦A⟧`. -/
theorem theorem1_imell_to_grcore {n : ℕ} {Γ : ICtx n} {M : ITerm n} {T : ITy}
    (h : IHasType Γ M T) : AdjTyped (trCtxI Γ) (trTerm M) (trTyI T) := by
  induction h with
  | var hi hj =>
    exact Typed.var (by simp [trCtxI, hi]) (fun j hne => by simp [trCtxI, hj j hne])
  | lam _ ih =>
    rw [trCtxI_cons] at ih
    exact Typed.lam ih
  | app _ _ hs ih1 ih2 => exact Typed.app ih1 ih2 hs.ctxAdd
  | star hΓ => exact Typed.unit (fun i => by simp [trCtxI, hΓ i])
  | letStar _ _ hs ih1 ih2 =>
    refine Typed.letPat ih1 (PatTy.unit none) ?_ hs.ctxAdd
    rw [Ctx.append_zero]; exact ih2
  | letPair _ _ hs ih1 ih2 =>
    refine Typed.letPat ih1 (PatTy.pair (PatTy.var _) (PatTy.var _)) ?_ hs.ctxAdd
    rw [trCtxI_append, trCtxI_ctx2] at ih2
    exact ih2
  | pair _ _ hs ih1 ih2 => exact Typed.pair ih1 ih2 hs.ctxAdd
  | @promote n k Γs Γ Ms N As B hsplit _ _ ihs ihN =>
    refine typed_apN k _ _ (fun j => trTyI (As j)) (trTyI B) (Ctx.empty n) _ _ ?_ ihs
      (ISplitN.sumFrom k Γs Γ hsplit)
    have hN : AdjTyped (Ctx.append (Ctx.empty n) (fun j => some (.lin (□[ω] (trTyI (As j))))))
        ((trTerm N).rename (Term.embedLow n k)) (trTyI B) := by
      refine ihN.rename (fun a b hab => Fin.ext (by simpa [Term.embedLow] using hab))
        (fun j => ?_) (fun j hj => ?_)
      · rw [Ctx.append_low _ _ _ (by simp [Term.embedLow])]; rfl
      · by_cases hjk : j.val < k
        · exact absurd (Fin.ext rfl) (hj ⟨j.val, hjk⟩)
        · rw [Ctx.append_high _ _ _ hjk]; rfl
    refine (Typed.pr ω (typed_lams k _ _ _ _ hN) (fun i A => by simp [Ctx.empty])).of_eq ?_
    funext i; rfl
  | @derelict n Γ M A _ ih =>
    refine Typed.letPat (Γ₂ := Ctx.empty n) ih (PatTy.box ω (PatTy.gvar ω _)) ?_
      (fun i => by simp only [Ctx.empty]; rcases trCtxI _ i with _ | a
                   · exact EntryAdd.noneLeft _
                   · exact EntryAdd.noneRight _)
    rw [Ctx.append_one]
    have h1 : AdjTyped (Ctx.cons (some (.grad (trTyI A) (1 : LNL))) (Ctx.empty n)) (.var 0)
        (trTyI A) :=
      Typed.var_one rfl (fun j hj => Fin.cases (fun h => absurd rfl h) (fun j _ => rfl) j hj)
    refine (h1.approx (i := 0) rfl (show (1 : LNL) ≤ ω from Or.inr rfl)).of_eq ?_
    funext i; refine Fin.cases rfl (fun i => rfl) i
  | @discard n Γ₁ Γ₂ Γ M N A B _ _ hs ih1 ih2 =>
    refine Typed.letPat ih1 (PatTy.box ω (PatTy.gvar ω _)) ?_ hs.ctxAdd
    rw [Ctx.append_one]
    have h2 := ih2.shift.weak (Δ := Ctx.cons (some (.grad (trTyI A) 0)) (Ctx.empty n))
      (Γ' := Ctx.cons (some (.grad (trTyI A) 0)) (trCtxI Γ₂))
      (fun i => Fin.cases (Or.inr ⟨_, rfl⟩) (fun i => Or.inl rfl) i)
      (fun i => Fin.cases (EntryAdd.noneLeft _) (fun i => by
        simp only [Ctx.cons_succ, Ctx.empty]
        rcases trCtxI Γ₂ i with _ | a
        · exact EntryAdd.noneLeft _
        · exact EntryAdd.noneRight _) i)
    refine (h2.approx (i := 0) rfl (show (0 : LNL) ≤ ω from Or.inr rfl)).of_eq ?_
    funext i; refine Fin.cases rfl (fun i => rfl) i
  | @copy n Γ₁ Γ₂ Γ M N A B _ _ hs ih1 ih2 =>
    refine Typed.letPat ih1 (PatTy.box ω (PatTy.gvar ω _)) ?_ hs.ctxAdd
    rw [Ctx.append_one]
    let A' := trTyI A
    let Γ₂' := trCtxI Γ₂
    let D := trCtxI (ctx2 (.bang A) (.bang A))
    have hN : AdjTyped (Ctx.append (Ctx.cons none Γ₂') D)
        ((trTerm N).rename (Ctx.liftN 2 Fin.succ)) (trTyI B) := by
      rw [trCtxI_append] at ih2
      refine ih2.rename (Ctx.liftN_injective 2 _ (Fin.succ_injective _)) (fun i => ?_)
        (Ctx.liftN_off _ _ _ (fun j hj => ?_))
      · rw [Ctx.liftN_append_apply]; rfl
      · refine Fin.cases (fun _ => rfl) (fun j hj => absurd rfl (hj j)) j hj
    rw [Ctx.append_succ, Ctx.append_one] at hN
    have hF : AdjTyped (Ctx.cons none Γ₂') (.lam (.lam ((trTerm N).rename (Ctx.liftN 2 Fin.succ))))
        (□[ω] A' ⊸ □[ω] A' ⊸ trTyI B) := Typed.lam (Typed.lam hN)
    let S : GCtx LNL (n + 1) := Ctx.cons (some (.grad A' ω)) (Ctx.empty n)
    have hz : AdjTyped S (.box (.var 0)) (□[ω] A') :=
      Typed.box_var rfl (fun j hj => Fin.cases (fun h => absurd rfl h) (fun j _ => rfl) j hj)
    have hrest : ∀ i : Fin n, EntryAdd (Γ₂' i) (Ctx.empty n i) (Γ₂' i) := by
      intro i; simp only [Ctx.empty]
      rcases Γ₂' i with _ | a
      · exact EntryAdd.noneLeft _
      · exact EntryAdd.noneRight _
    refine Typed.app (Typed.app (Γ := Ctx.cons (some (.grad A' ω)) Γ₂') hF hz
      (fun i => Fin.cases (EntryAdd.noneLeft _)
      (fun i => hrest i) i)) hz (fun i => Fin.cases (EntryAdd.grad A' ω ω) (fun i => hrest i) i)

end LinExp

end
