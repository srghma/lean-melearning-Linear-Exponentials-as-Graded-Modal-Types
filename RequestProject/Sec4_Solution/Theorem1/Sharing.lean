module

public import RequestProject.Sec4_Solution.Theorem1.Admissible

/-!
# Section 4 (Theorem 1, auxiliary): sharing assumptions and promotion in IMELL

GrCore adds contexts pointwise, so a graded variable may be used by both premises of a binary
rule.  In IMELL such a shared variable must be contracted.  `IDeriv.share` shows that any
binary IMELL rule (stated for disjoint contexts) extends to contexts that share assumptions,
as long as each shared assumption can be *contracted* (`Contract`).

We also prove that an IMELL context consisting only of `!`-assumptions can be promoted.
-/

@[expose] public section

namespace LinExp

/-- A two-variable context `x : e₁, y : e₂` with optional entries (`y` is index `0`). -/
def ctxP (x y : Option ITy) : ICtx 2 := fun k => if k.val = 0 then y else x

lemma ctx2_eq_ctxP (A B : ITy) : ctx2 A B = ctxP (some A) (some B) := rfl

lemma append_ctx2 {n : ℕ} (Γ : ICtx n) (A B : ITy) :
    Ctx.append Γ (ctx2 A B) = Ctx.cons (some B) (Ctx.cons (some A) Γ) := by
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
  · simp [Ctx.append, ctx2]
  · simp [Ctx.append, ctx2]; rfl
  · simp only [Ctx.append, Ctx.cons_succ]
    have : ¬ (k.succ.succ.val < 2) := by simp
    rw [dif_neg this]; congr 1

/-- `Contract a b c`: two hypotheses `x : a, y : b` can be obtained from one hypothesis `c`. -/
def Contract (a b c : ITy) : Prop :=
  ∀ (n : ℕ) (Γ : ICtx n) (i : Fin n) (Z : ITy),
    IDeriv (Ctx.append (Function.update Γ i none) (ctx2 a b)) Z →
    IDeriv (Function.update Γ i (some c)) Z

lemma Contract.bang (A : ITy) : Contract (.bang A) (.bang A) (.bang A) := by
  intro n Γ i Z ⟨M, hM⟩
  exact ⟨_, IHasType.copy (isingle_var i (.bang A)) hM (ISplit.single_update Γ i _)⟩

lemma ctx2_ent {n : ℕ} (Γ : ICtx n) {a b a' b' : ITy} (ha : PosEnt (some a) (some a'))
    (hb : PosEnt (some b) (some b')) {Z : ITy} (h : IDeriv (Ctx.append Γ (ctx2 a b)) Z) :
    IDeriv (Ctx.append Γ (ctx2 a' b')) Z := by
  refine IDeriv.ctxwise (fun k => ?_) h
  by_cases hk : k.val < 2
  · rw [Ctx.append_low _ _ _ hk, Ctx.append_low _ _ _ hk]
    by_cases hk0 : k.val = 0
    · simp only [ctx2, hk0, ↓reduceIte]; exact hb
    · simp only [ctx2, hk0, ↓reduceIte]; exact ha
  · rw [Ctx.append_high _ _ _ hk, Ctx.append_high _ _ _ hk]; exact PosEnt.refl _

lemma Contract.lin_lin (A : ITy) : Contract A A (.bang A) := fun n Γ i Z h =>
  Contract.bang A n Γ i Z (ctx2_ent _ (PosEnt.derelict A) (PosEnt.derelict A) h)

lemma Contract.bang_lin (A : ITy) : Contract (.bang A) A (.bang A) := fun n Γ i Z h =>
  Contract.bang A n Γ i Z (ctx2_ent _ (PosEnt.refl _) (PosEnt.derelict A) h)

lemma Contract.lin_bang (A : ITy) : Contract A (.bang A) (.bang A) := fun n Γ i Z h =>
  Contract.bang A n Γ i Z (ctx2_ent _ (PosEnt.derelict A) (PosEnt.refl _) h)

lemma lam_lam {n : ℕ} {Γ : ICtx n} {a b Z : ITy}
    (h : IDeriv (Ctx.append Γ (ctx2 a b)) Z) : IDeriv Γ (.lolli a (.lolli b Z)) := by
  obtain ⟨M, hM⟩ := h
  rw [append_ctx2] at hM
  exact ⟨_, IHasType.lam (IHasType.lam hM)⟩

lemma Contract.unit_left (X : ITy) : Contract .unit X X := by
  intro n Γ i Z h
  obtain ⟨F, hF⟩ := lam_lam h
  exact ⟨_, IHasType.app (IHasType.app hF (IHasType.star (Γ := Ctx.empty n) (fun _ => rfl))
    (ISplit.empty_right _)) (isingle_var i X) (ISplit.single_update Γ i X).symm⟩

lemma Contract.unit_right (X : ITy) : Contract X .unit X := by
  intro n Γ i Z h
  obtain ⟨F, hF⟩ := lam_lam h
  exact ⟨_, IHasType.app (IHasType.app hF (isingle_var i X) (ISplit.single_update Γ i X).symm)
    (IHasType.star (Γ := Ctx.empty n) (fun _ => rfl)) (ISplit.empty_right _)⟩

/-- Sharing addition of IMELL contexts: disjoint union, except that shared assumptions must be
contractible. -/
inductive SAdd : Option ITy → Option ITy → Option ITy → Prop where
  | noneLeft (e : Option ITy) : SAdd none e e
  | noneRight (a : ITy) : SAdd (some a) none (some a)
  | share (a b c : ITy) : Contract a b c → SAdd (some a) (some b) (some c)

lemma SAdd.inv {e₁ e₂ e : Option ITy} (h : SAdd e₁ e₂ e) :
    (e₁ = none ∧ e₂ = e) ∨ (∃ a, e₁ = some a ∧ e₂ = none ∧ e = some a) ∨
      (∃ a b c, e₁ = some a ∧ e₂ = some b ∧ e = some c ∧ Contract a b c) := by
  cases h with
  | noneLeft => exact Or.inl ⟨rfl, rfl⟩
  | noneRight a => exact Or.inr (Or.inl ⟨a, rfl, rfl, rfl⟩)
  | share a b c hc => exact Or.inr (Or.inr ⟨a, b, c, rfl, rfl, rfl, hc⟩)

/-- Positions assumed in both contexts. -/
def sharedSet {n : ℕ} (Γ₁ Γ₂ : ICtx n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (Γ₁ i).isSome ∧ (Γ₂ i).isSome)

/-- Embedding of the old indices after two new innermost variables. -/
def up2 (n : ℕ) : Fin n ↪ Fin (n + 2) := ⟨fun j => ⟨j.val + 2, by omega⟩, by
  intro a b h; simp [Fin.ext_iff] at h; exact Fin.ext h⟩

/-- Renaming placing position `i` at index `p` (`p < 2`) and shifting the others by two. -/
def place {n : ℕ} (i : Fin n) (p : Fin (n + 2)) : Fin n → Fin (n + 2) :=
  fun j => if j = i then p else up2 n j

lemma place_injective {n : ℕ} (i : Fin n) (p : Fin (n + 2)) (hp : p.val < 2) :
    Function.Injective (place i p) := by
  intro a b h
  simp only [place, up2, Function.Embedding.coeFn_mk] at h
  split_ifs at h with h1 h2 h2
  · rw [h1, h2]
  · subst h; simp at hp
  · rw [← h] at hp; simp at hp
  · simp [Fin.ext_iff] at h; exact Fin.ext h

lemma place_rename {n : ℕ} {Γ : ICtx n} {i : Fin n} {a : ITy} (hi : Γ i = some a)
    (x y : Option ITy) (p : Fin (n + 2)) (hp : p.val < 2)
    (hxy : ctxP x y ⟨p.val, hp⟩ = some a) (hother : ctxP x y ⟨1 - p.val, by omega⟩ = none)
    {X : ITy} (h : IDeriv Γ X) :
    IDeriv (Ctx.append (Function.update Γ i none) (ctxP x y)) X := by
  refine h.rename (place_injective i p hp) (fun j => ?_) (fun k hk => ?_)
  · unfold place
    by_cases hj : j = i
    · subst hj; simp only [↓reduceIte, Ctx.append_low _ _ _ hp]; rw [hxy, hi]
    · simp only [hj, ↓reduceIte, up2, Function.Embedding.coeFn_mk]
      rw [Ctx.append_high _ _ _ (by simp),
        show (⟨j.val + 2 - 2, by omega⟩ : Fin n) = j from Fin.ext (by simp),
        Function.update_of_ne hj]
  · by_cases hk2 : k.val < 2
    · rw [Ctx.append_low _ _ _ hk2]
      have hkp : k.val ≠ p.val := fun e => hk i (by simp [place]; exact Fin.ext e.symm)
      have : (⟨k.val, hk2⟩ : Fin 2) = ⟨1 - p.val, by omega⟩ := Fin.ext (by simp; omega)
      rw [this, hother]
    · rw [Ctx.append_high _ _ _ hk2]
      by_cases hki : k.val - 2 = i.val
      · have : (⟨k.val - 2, by omega⟩ : Fin n) = i := Fin.ext hki
        rw [this]; simp
      · exfalso
        apply hk ⟨k.val - 2, by omega⟩
        have : (⟨k.val - 2, by omega⟩ : Fin n) ≠ i := fun e => hki (by rw [← e])
        simp only [place, this, ↓reduceIte, up2, Function.Embedding.coeFn_mk]
        ext; simp; omega

/-- **Sharing lemma**: a binary rule on disjoint contexts extends to contexts related by
`SAdd`. -/
theorem IDeriv.share {X Y Z : ITy}
    (rule : ∀ (m : ℕ) (Δ₁ Δ₂ Δ : ICtx m), ISplit Δ₁ Δ₂ Δ → IDeriv Δ₁ X → IDeriv Δ₂ Y →
      IDeriv Δ Z) :
    ∀ (n : ℕ) (Γ₁ Γ₂ Γ : ICtx n), (∀ i, SAdd (Γ₁ i) (Γ₂ i) (Γ i)) → IDeriv Γ₁ X →
      IDeriv Γ₂ Y → IDeriv Γ Z := by
  suffices H : ∀ (s n : ℕ) (Γ₁ Γ₂ Γ : ICtx n), (sharedSet Γ₁ Γ₂).card ≤ s →
      (∀ i, SAdd (Γ₁ i) (Γ₂ i) (Γ i)) → IDeriv Γ₁ X → IDeriv Γ₂ Y → IDeriv Γ Z from
    fun n Γ₁ Γ₂ Γ => H _ n Γ₁ Γ₂ Γ le_rfl
  intro s
  induction s with
  | zero =>
    intro n Γ₁ Γ₂ Γ hs hadd h₁ h₂
    refine rule n Γ₁ Γ₂ Γ (fun i => ?_) h₁ h₂
    rcases (hadd i).inv with ⟨h1, h2⟩ | ⟨a, h1, h2, h3⟩ | ⟨a, b, c, h1, h2, h3, _⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1.trans h3.symm⟩
    · exfalso
      have : i ∈ sharedSet Γ₁ Γ₂ := by simp [sharedSet, h1, h2]
      simp_all
  | succ s ih =>
    intro n Γ₁ Γ₂ Γ hs hadd h₁ h₂
    by_cases hex : ∃ i, i ∈ sharedSet Γ₁ Γ₂
    · obtain ⟨i, hi⟩ := hex
      have hi' := hi
      simp only [sharedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
      obtain ⟨ha, hb⟩ := hi'
      obtain ⟨a, b, c, h1, h2, h3, hc⟩ : ∃ a b c, Γ₁ i = some a ∧ Γ₂ i = some b ∧
          Γ i = some c ∧ Contract a b c := by
        rcases (hadd i).inv with ⟨h1, _⟩ | ⟨a, _, h2, _⟩ | h
        · simp [h1] at ha
        · simp [h2] at hb
        · exact h
      let Γ₁' := Ctx.append (Function.update Γ₁ i none) (ctxP (some a) none)
      let Γ₂' := Ctx.append (Function.update Γ₂ i none) (ctxP none (some b))
      let Γ' := Ctx.append (Function.update Γ i none) (ctx2 a b)
      have h₁' : IDeriv Γ₁' X :=
        place_rename h1 (some a) none ⟨1, by omega⟩ (by simp) (by simp [ctxP]) (by simp [ctxP]) h₁
      have h₂' : IDeriv Γ₂' Y :=
        place_rename h2 none (some b) ⟨0, by omega⟩ (by simp) (by simp [ctxP]) (by simp [ctxP]) h₂
      have hadd' : ∀ k, SAdd (Γ₁' k) (Γ₂' k) (Γ' k) := by
        intro k
        by_cases hk : k.val < 2
        · simp only [Γ₁', Γ₂', Γ', Ctx.append_low _ _ _ hk, ctx2_eq_ctxP, ctxP]
          by_cases hk0 : k.val = 0
          · simp only [hk0, ↓reduceIte]; exact SAdd.noneLeft _
          · simp only [hk0, ↓reduceIte]; exact SAdd.noneRight _
        · simp only [Γ₁', Γ₂', Γ', Ctx.append_high _ _ _ hk]
          by_cases hki : (⟨k.val - 2, by omega⟩ : Fin n) = i
          · rw [hki]; simp only [Function.update_self]; exact SAdd.noneLeft _
          · simp only [Function.update_of_ne hki]; exact hadd _
      have hsub : sharedSet Γ₁' Γ₂' ⊆ ((sharedSet Γ₁ Γ₂).erase i).map (up2 n) := by
        intro k hk
        simp only [sharedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        obtain ⟨hk1, hk2⟩ := hk
        by_cases hk' : k.val < 2
        · exfalso
          simp only [Γ₁', Γ₂', Ctx.append_low _ _ _ hk', ctxP] at hk1 hk2
          by_cases hk0 : k.val = 0 <;> simp [hk0] at hk1 hk2
        · simp only [Γ₁', Γ₂', Ctx.append_high _ _ _ hk'] at hk1 hk2
          have hki : (⟨k.val - 2, by omega⟩ : Fin n) ≠ i := by
            intro e; rw [e] at hk1; simp at hk1
          rw [Function.update_of_ne hki] at hk1 hk2
          simp only [Finset.mem_map, Finset.mem_erase, sharedSet, Finset.mem_filter,
            Finset.mem_univ, true_and]
          refine ⟨⟨k.val - 2, by omega⟩, ⟨hki, hk1, hk2⟩, ?_⟩
          simp only [up2, Function.Embedding.coeFn_mk]
          ext; simp; omega
      have hcard : (sharedSet Γ₁' Γ₂').card ≤ s := by
        refine le_trans (Finset.card_le_card hsub) ?_
        rw [Finset.card_map, Finset.card_erase_of_mem hi]
        omega
      have := hc n Γ i Z (ih (n + 2) Γ₁' Γ₂' Γ' hcard hadd' h₁' h₂')
      rwa [← h3, Function.update_eq_self] at this
    · refine rule n Γ₁ Γ₂ Γ (fun i => ?_) h₁ h₂
      rcases (hadd i).inv with ⟨h1, h2⟩ | ⟨a, h1, h2, h3⟩ | ⟨a, b, c, h1, h2, h3, _⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1.trans h3.symm⟩
      · exfalso
        exact hex ⟨i, by simp [sharedSet, h1, h2]⟩

end LinExp

end
