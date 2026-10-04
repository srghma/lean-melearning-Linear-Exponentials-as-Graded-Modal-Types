module

public import RequestProject.Sec4_Solution.Theorem1.Translations
public import RequestProject.Sec4_Solution.Theorem1.Sharing
public import RequestProject.Sec4_Solution.Theorem1.Promotion

/-!
# Section 4 (Theorem 1, explicit translation): IMELL term combinators

Explicit IMELL terms realising the admissible rules used by the GrCore → IMELL translation
(`Admissible.lean`, `Sharing.lean`, `Promotion.lean` only prove that the corresponding
sequents are *derivable*; here we write the terms down):

* `cutAt i C M` — substitute (by a β-redex) the term `C` for the variable `i` of `M`;
* `adjustAt i k M` — change the assumption at position `i` according to `k : AdjKind`
  (dereliction, removing/adding a unit assumption, discarding a `!`-assumption, …), and
  `adjustAll f M` doing this at every position;
* `splitTm r s` — the colax map `⟦□_{r+s} A⟧ ⊸ ⟦□_r A⟧ ⊗ ⟦□_s A⟧` (for `{0, 1, ω}`);
* `shareL F L P₁ P₂` — combine two terms with a binary rule `F` when the contexts of `P₁`
  and `P₂` share the variables listed in `L` (each shared variable is split by `splitTm`);
* `promoteTm S N` — promotion of a term whose context only contains `!`-assumptions.
-/

@[expose] public section

namespace LinExp

/-! ### Cut -/

/-- `cutAt i C M`: substitute `C` for the variable `i` of `M`, as the β-redex
`(λx. M[x/i]) C`. -/
def cutAt {n : ℕ} (i : Fin n) (C M : ITerm n) : ITerm n :=
  .app (.lam (M.rename (moveToZero i))) C

theorem cutAt_typed {n : ℕ} {Γ₁ Ξ Γ : ICtx n} {A B : ITy} {i : Fin n} {C M : ITerm n}
    (hC : IHasType Γ₁ C A) (hM : IHasType Ξ M B) (hi : Ξ i = some A)
    (hs : ISplit Γ₁ (Function.update Ξ i none) Γ) : IHasType Γ (cutAt i C M) B := by
  have hM' : IHasType (Ctx.cons (some A) (Function.update Ξ i none))
      (M.rename (moveToZero i)) B := by
    refine hM.rename (moveToZero_injective i) (fun j => ?_) (fun k hk => ?_)
    · unfold moveToZero
      by_cases hj : j = i
      · subst hj; simp [hi]
      · simp [hj]
    · refine Fin.cases (fun hk => absurd (by simp [moveToZero]) (hk i)) (fun k hk => ?_) k hk
      simp only [Ctx.cons_succ]
      by_cases hki : k = i
      · subst hki; simp
      · exact absurd (by simp [moveToZero, hki]) (hk k)
  exact IHasType.app (IHasType.lam hM') hC hs.symm

/-! ### Adjusting one position of the context -/

/-- The ways in which the assumption at one position may be changed. -/
inductive AdjKind : Type where
  /-- leave it unchanged -/
  | keep
  /-- replace `A` by `!A` (dereliction) -/
  | derel
  /-- remove an assumption `I` -/
  | dropUnit
  /-- add an assumption `I` (consumed by `let _ be * in _`) -/
  | addUnit
  /-- add an assumption `!A` (discarded) -/
  | addBang
  /-- replace `I` by `!A` -/
  | unitToBang
  deriving DecidableEq

/-- The IMELL term implementing an `AdjKind` at position `i`. -/
def adjustAt {n : ℕ} (i : Fin n) : AdjKind → ITerm n → ITerm n
  | .keep, M => M
  | .derel, M => cutAt i (.derelict (.var i)) M
  | .dropUnit, M => cutAt i .star M
  | .addUnit, M => .letStar (.var i) M
  | .addBang, M => .discard (.var i) M
  | .unitToBang, M => cutAt i (.discard (.var i) .star) M

/-- `KindOK k e e'`: the adjustment `k` turns the assumption `e` into `e'`. -/
def KindOK : AdjKind → Option ITy → Option ITy → Prop
  | .keep, e, e' => e = e'
  | .derel, e, e' => ∃ A, e = some A ∧ e' = some (.bang A)
  | .dropUnit, e, e' => e = some .unit ∧ e' = none
  | .addUnit, e, e' => e = none ∧ e' = some .unit
  | .addBang, e, e' => e = none ∧ ∃ A, e' = some (.bang A)
  | .unitToBang, e, e' => e = some .unit ∧ ∃ A, e' = some (.bang A)

theorem adjustAt_typed {n : ℕ} (Γ : ICtx n) (i : Fin n) {k : AdjKind} {e e' : Option ITy}
    (hk : KindOK k e e') {M : ITerm n} {B : ITy}
    (hM : IHasType (Function.update Γ i e) M B) :
    IHasType (Function.update Γ i e') (adjustAt i k M) B := by
  cases k with
  | keep => cases hk; exact hM
  | derel =>
    obtain ⟨A, rfl, rfl⟩ := hk
    refine cutAt_typed (IHasType.derelict (isingle_var i (.bang A))) hM (by simp) ?_
    rw [Function.update_idem]; exact ISplit.single_update Γ i _
  | dropUnit =>
    obtain ⟨rfl, rfl⟩ := hk
    refine cutAt_typed (IHasType.star (Γ := Ctx.empty n) (fun _ => rfl)) hM (by simp) ?_
    rw [Function.update_idem]; exact ISplit.empty_left _
  | addUnit =>
    obtain ⟨rfl, rfl⟩ := hk
    exact IHasType.letStar (isingle_var i .unit) hM (ISplit.single_update Γ i _)
  | addBang =>
    obtain ⟨rfl, A, rfl⟩ := hk
    exact IHasType.discard (isingle_var i (.bang A)) hM (ISplit.single_update Γ i _)
  | unitToBang =>
    obtain ⟨rfl, A, rfl⟩ := hk
    refine cutAt_typed (IHasType.discard (isingle_var i (.bang A))
      (IHasType.star (Γ := Ctx.empty n) (fun _ => rfl)) (ISplit.empty_right _)) hM
      (by simp) ?_
    rw [Function.update_idem]; exact ISplit.single_update Γ i _

/-- Version of `adjustAt_typed` for an arbitrary pair of contexts that differ only at `i`. -/
theorem adjustAt_typed' {n : ℕ} {Γ Γ' : ICtx n} (i : Fin n) {k : AdjKind}
    (hk : KindOK k (Γ i) (Γ' i)) (hother : ∀ j, j ≠ i → Γ j = Γ' j) {M : ITerm n} {B : ITy}
    (hM : IHasType Γ M B) : IHasType Γ' (adjustAt i k M) B := by
  have e1 : Γ = Function.update Γ' i (Γ i) := by
    funext j; by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]; exact hother j hj
  have e2 : Γ' = Function.update Γ' i (Γ' i) := by simp
  rw [e2]; rw [e1] at hM
  exact adjustAt_typed Γ' i hk hM

/-- Apply the adjustments `f i` at all positions `i` of the list `L`. -/
def adjustList {n : ℕ} (f : Fin n → AdjKind) (L : List (Fin n)) (M : ITerm n) : ITerm n :=
  L.foldr (fun i M => adjustAt i (f i) M) M

/-- Apply the adjustment `f i` at every position `i`. -/
def adjustAll {n : ℕ} (f : Fin n → AdjKind) (M : ITerm n) : ITerm n :=
  adjustList f (List.finRange n) M

theorem adjustList_typed {n : ℕ} (f : Fin n → AdjKind) :
    ∀ (L : List (Fin n)), L.Nodup → ∀ {Γ Γ' : ICtx n},
      (∀ i ∈ L, KindOK (f i) (Γ i) (Γ' i)) → (∀ i, i ∉ L → Γ i = Γ' i) →
      ∀ {M : ITerm n} {B : ITy}, IHasType Γ M B → IHasType Γ' (adjustList f L M) B
  | [], _, Γ, Γ', _, hout, M, B, hM => by
    have : Γ = Γ' := funext fun i => hout i (by simp)
    subst this; exact hM
  | i :: L, hnd, Γ, Γ', hin, hout, M, B, hM => by
    rw [List.nodup_cons] at hnd
    have ih := adjustList_typed f L hnd.2 (Γ := Γ) (Γ' := Function.update Γ' i (Γ i))
      (fun j hj => by
        have hji : j ≠ i := fun e => hnd.1 (e ▸ hj)
        rw [Function.update_of_ne hji]; exact hin j (List.mem_cons_of_mem _ hj))
      (fun j hj => by
        by_cases hji : j = i
        · subst hji; simp
        · rw [Function.update_of_ne hji]; exact hout j (by simp [hji, hj])) hM
    show IHasType Γ' (adjustAt i (f i) (adjustList f L M)) B
    refine adjustAt_typed' i ?_ (fun j hj => by rw [Function.update_of_ne hj]) ih
    simpa using hin i (by simp)

theorem adjustAll_typed {n : ℕ} (f : Fin n → AdjKind) {Γ Γ' : ICtx n}
    (h : ∀ i, KindOK (f i) (Γ i) (Γ' i)) {M : ITerm n} {B : ITy} (hM : IHasType Γ M B) :
    IHasType Γ' (adjustAll f M) B :=
  adjustList_typed f _ (List.nodup_finRange n) (fun i _ => h i)
    (fun i hi => absurd (List.mem_finRange i) hi) hM

/-! ### The colax maps `n_{r,s} : ⟦□_{r+s} A⟧ ⊸ ⟦□_r A⟧ ⊗ ⟦□_s A⟧` -/

/-- The colax map splitting an assumption of grade `r + s` into grades `r` and `s` (as a
closed term, available in every scope). -/
def splitTm {n : ℕ} : LNL → LNL → ITerm n
  | .zero, _ => .lam (.pair .star (.var 0))
  | _, .zero => .lam (.pair (.var 0) .star)
  | .one, .one => .lam (.copy (.var 0) (.pair (.derelict (.var 1)) (.derelict (.var 0))))
  | .one, .many => .lam (.copy (.var 0) (.pair (.derelict (.var 1)) (.var 0)))
  | .many, .one => .lam (.copy (.var 0) (.pair (.var 1) (.derelict (.var 0))))
  | .many, .many => .lam (.copy (.var 0) (.pair (.var 1) (.var 0)))

/-- The body of the colax maps for `r, s ∈ {1, ω}`: in context `x : !A, y : !A` (after an
unused variable), build `dᵣ x ⊗ dₛ y`. -/
lemma split_body {n : ℕ} (A : ITy) {X Y : ITy} {M N : ITerm (n + 1 + 2)}
    (hM : IHasType (isingle 1 (.bang A)) M X) (hN : IHasType (isingle 0 (.bang A)) N Y) :
    IHasType (Ctx.empty n) (.lam (.copy (.var 0) (.pair M N)))
      (.lolli (.bang A) (.tensor X Y)) := by
  refine IHasType.lam (IHasType.copy (Γ₂ := Ctx.cons none (Ctx.empty n))
    (isingle_var 0 (.bang A)) (IHasType.pair hM hN (fun k => ?_)) (fun k => ?_))
  · rw [append_ctx2]
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
    · left; simp [isingle]
    · right; exact ⟨by simp [isingle], rfl⟩
    · left
      have h1 : k.succ.succ ≠ (1 : Fin (n + 1 + 2)) := fun h => by
        have := congrArg Fin.val h
        rw [Fin.val_succ, Fin.val_succ] at this
        have h' : ((1 : Fin (n + 1 + 2)) : ℕ) = 1 := rfl
        omega
      have h0 : k.succ.succ ≠ (0 : Fin (n + 1 + 2)) := Fin.succ_ne_zero _
      simp only [isingle, if_neg h1, if_neg h0]
      exact ⟨trivial, Fin.cases rfl (fun _ => rfl) k⟩
  · refine Fin.cases ?_ (fun k => ?_) k
    · right; simp [isingle]
    · left; exact ⟨by simp [isingle, Fin.succ_ne_zero], rfl⟩

theorem splitTm_typed {n : ℕ} (r s : LNL) (A : Ty LNL) :
    IHasType (Ctx.empty n) (splitTm r s)
      (.lolli (trTy (.box (r + s) A)) (.tensor (trTy (.box r A)) (trTy (.box s A)))) := by
  have unitL : ∀ X : ITy, IHasType (Ctx.empty n) (.lam (.pair .star (.var 0)))
      (.lolli X (.tensor .unit X)) := fun X =>
    IHasType.lam (IHasType.pair (Γ₁ := Ctx.empty (n + 1)) (IHasType.star (fun _ => rfl))
      (isingle_var 0 X) (fun k => Fin.cases (Or.inl ⟨rfl, by simp [isingle]⟩)
        (fun k => Or.inl ⟨rfl, by simp [isingle, Fin.succ_ne_zero]; rfl⟩) k))
  have unitR : ∀ X : ITy, IHasType (Ctx.empty n) (.lam (.pair (.var 0) .star))
      (.lolli X (.tensor X .unit)) := fun X =>
    IHasType.lam (IHasType.pair (Γ₂ := Ctx.empty (n + 1)) (isingle_var 0 X)
      (IHasType.star (fun _ => rfl)) (fun k => Fin.cases (Or.inr ⟨rfl, by simp [isingle]⟩)
        (fun k => Or.inr ⟨rfl, by simp [isingle, Fin.succ_ne_zero]; rfl⟩) k))
  have v1 := isingle_var (n := n + 1 + 2) 1 (.bang (trTy A))
  have v0 := isingle_var (n := n + 1 + 2) 0 (.bang (trTy A))
  cases r <;> cases s
  · exact unitL _
  · exact unitL _
  · exact unitL _
  · exact unitR _
  · exact split_body _ (IHasType.derelict v1) (IHasType.derelict v0)
  · exact split_body _ (IHasType.derelict v1) v0
  · exact unitR _
  · exact split_body _ v1 (IHasType.derelict v0)
  · exact split_body _ v1 v0

/-! ### Sharing -/

/-- Term-level version of `place_rename`. -/
lemma place_rename_typed {n : ℕ} {Γ : ICtx n} {i : Fin n} {a : ITy} (hi : Γ i = some a)
    (x y : Option ITy) (p : Fin (n + 2)) (hp : p.val < 2)
    (hxy : ctxP x y ⟨p.val, hp⟩ = some a) (hother : ctxP x y ⟨1 - p.val, by omega⟩ = none)
    {M : ITerm n} {X : ITy} (h : IHasType Γ M X) :
    IHasType (Ctx.append (Function.update Γ i none) (ctxP x y)) (M.rename (place i p)) X := by
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

/-- `shareL F L P₁ P₂` combines `P₁` and `P₂` with the binary rule `F`.  Each entry
`(i, r, s)` of `L` is a variable `i` used by both terms, at grade `r` in `P₁` and at grade `s`
in `P₂`: it is split with the colax map `splitTm r s` into two fresh variables, one for each
term. -/
def shareL (F : ∀ {m : ℕ}, ITerm m → ITerm m → ITerm m) :
    {m : ℕ} → List (Fin m × LNL × LNL) → ITerm m → ITerm m → ITerm m
  | _, [], P₁, P₂ => F P₁ P₂
  | m, (i, r, s) :: L, P₁, P₂ =>
    .letPair (.app (splitTm r s) (.var i))
      (shareL F (L.map (fun x => (up2 m x.1, x.2)))
        (P₁.rename (place i ⟨1, by omega⟩)) (P₂.rename (place i ⟨0, by omega⟩)))
termination_by _ L => L.length

/-- Typing of `shareL`. -/
theorem shareL_typed (F : ∀ {m : ℕ}, ITerm m → ITerm m → ITerm m) {X Y Z : ITy}
    (rule : ∀ {m : ℕ} {Δ₁ Δ₂ Δ : ICtx m} {M N : ITerm m}, ISplit Δ₁ Δ₂ Δ →
      IHasType Δ₁ M X → IHasType Δ₂ N Y → IHasType Δ (F M N) Z) :
    ∀ {m : ℕ} (L : List (Fin m × LNL × LNL)) {Δ₁ Δ₂ Δ : ICtx m} {P₁ P₂ : ITerm m},
      (L.map Prod.fst).Nodup →
      (∀ i, i ∉ L.map Prod.fst →
        (Δ₁ i = none ∧ Δ₂ i = Δ i) ∨ (Δ₂ i = none ∧ Δ₁ i = Δ i)) →
      (∀ x ∈ L, ∃ A, Δ₁ x.1 = some (trTy (.box x.2.1 A)) ∧
        Δ₂ x.1 = some (trTy (.box x.2.2 A)) ∧ Δ x.1 = some (trTy (.box (x.2.1 + x.2.2) A))) →
      IHasType Δ₁ P₁ X → IHasType Δ₂ P₂ Y → IHasType Δ (shareL F L P₁ P₂) Z
  | m, [], Δ₁, Δ₂, Δ, P₁, P₂, _, hout, _, h₁, h₂ => by
    rw [shareL]; exact rule (fun i => hout i (by simp)) h₁ h₂
  | m, (i, r, s) :: L, Δ₁, Δ₂, Δ, P₁, P₂, hnd, hout, hin, h₁, h₂ => by
    rw [shareL]
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨A, e1, e2, e3⟩ := hin (i, r, s) (by simp)
    simp only at e1 e2 e3
    let Δ₁' := Ctx.append (Function.update Δ₁ i none) (ctxP (some (trTy (.box r A))) none)
    let Δ₂' := Ctx.append (Function.update Δ₂ i none) (ctxP none (some (trTy (.box s A))))
    let Δ' := Ctx.append (Function.update Δ i none) (ctx2 (trTy (.box r A)) (trTy (.box s A)))
    have h₁' : IHasType Δ₁' (P₁.rename (place i ⟨1, by omega⟩)) X :=
      place_rename_typed e1 (some (trTy (.box r A))) none ⟨1, by omega⟩ (by simp) (by simp [ctxP])
        (by simp [ctxP]) h₁
    have h₂' : IHasType Δ₂' (P₂.rename (place i ⟨0, by omega⟩)) Y :=
      place_rename_typed e2 none (some (trTy (.box s A))) ⟨0, by omega⟩ (by simp) (by simp [ctxP])
        (by simp [ctxP]) h₂
    have hmap : (L.map (fun x => (up2 m x.1, x.2))).map Prod.fst =
        (L.map Prod.fst).map (up2 m) := by simp [List.map_map, Function.comp_def]
    have hrec := shareL_typed F rule (L.map (fun x => (up2 m x.1, x.2)))
      (Δ₁ := Δ₁') (Δ₂ := Δ₂') (Δ := Δ') (P₁ := P₁.rename (place i ⟨1, by omega⟩))
      (P₂ := P₂.rename (place i ⟨0, by omega⟩))
      (by rw [hmap]; exact hnd.2.map (up2 m).injective)
      (fun k hk => by
        by_cases hk2 : k.val < 2
        · simp only [Δ₁', Δ₂', Δ', Ctx.append_low _ _ _ hk2, ctx2_eq_ctxP, ctxP]
          by_cases hk0 : k.val = 0
          · simp [hk0]
          · simp [hk0]
        · simp only [Δ₁', Δ₂', Δ', Ctx.append_high _ _ _ hk2]
          by_cases hki : (⟨k.val - 2, by omega⟩ : Fin m) = i
          · rw [hki]; simp
          · simp only [Function.update_of_ne hki]
            refine hout _ ?_
            simp only [List.map_cons, List.mem_cons, not_or]
            refine ⟨hki, fun hmem => hk ?_⟩
            rw [hmap, List.mem_map]
            exact ⟨_, hmem, by simp only [up2, Function.Embedding.coeFn_mk]; ext; simp; omega⟩)
      (fun x hx => by
        rw [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        obtain ⟨B, f1, f2, f3⟩ := hin y (List.mem_cons_of_mem _ hy)
        have hyi : y.1 ≠ i := fun e => hnd.1 (e ▸ List.mem_map_of_mem hy)
        have hlt : ¬ ((up2 m) y.1).val < 2 := by simp [up2]
        have hidx : (⟨((up2 m) y.1).val - 2, by omega⟩ : Fin m) = y.1 :=
          Fin.ext (by simp [up2])
        refine ⟨B, ?_, ?_, ?_⟩ <;>
        · simp only [Δ₁', Δ₂', Δ', Ctx.append_high _ _ _ hlt]
          rw [hidx, Function.update_of_ne hyi]
          assumption)
      h₁' h₂'
    have hsplit := ISplit.single_update Δ i (trTy (.box (r + s) A))
    rw [← e3, Function.update_eq_self] at hsplit
    refine IHasType.letPair (Γ₁ := isingle i (trTy (.box (r + s) A))) (Γ₂ := Function.update Δ i none)
      (IHasType.app (Γ₁ := Ctx.empty m) (splitTm_typed r s A) (isingle_var i _)
        (ISplit.empty_left _)) hrec hsplit
termination_by _ L => L.length

/-! ### Promotion -/

/-- Promotion of a term whose context only contains `!`-assumptions; `S i` records whether
position `i` carries an assumption. -/
def promoteTm {n : ℕ} (S : Fin n → Bool) (N : ITerm n) : ITerm n :=
  .promote (fun i => if S i then .var i else .promote (k := 0) Fin.elim0 .star)
    (adjustAll (fun i => if S i then .keep else .addBang) N)

theorem promoteTm_typed {n : ℕ} (Γ : ICtx n) (S : Fin n → Bool)
    (h : ∀ i, (S i = false ∧ Γ i = none) ∨ (S i = true ∧ ∃ A, Γ i = some (.bang A)))
    {N : ITerm n} {B : ITy} (hN : IHasType Γ N B) : IHasType Γ (promoteTm S N) (.bang B) := by
  let As : Fin n → ITy := fun i => bangArg (Γ i)
  have hfill : IHasType (fun i => some (.bang (As i)))
      (adjustAll (fun i => if S i then .keep else .addBang) N) B := by
    refine adjustAll_typed _ (fun i => ?_) hN
    rcases h i with ⟨hS, hi⟩ | ⟨hS, A, hi⟩
    · simp only [hS, Bool.false_eq_true, ↓reduceIte, KindOK, hi, true_and]; exact ⟨_, rfl⟩
    · simp [hS, KindOK, hi, As, bangArg]
  let Γs : Fin n → ICtx n := fun i x => if x = i then Γ x else none
  refine IHasType.promote (Γs := Γs) (As := As) ?_ (fun i => ?_) hfill
  · refine ISplitN.of_pointwise n Γs Γ (fun x => ?_)
    by_cases hx : Γ x = none
    · left; exact ⟨hx, fun j => by simp only [Γs]; split_ifs <;> simp_all⟩
    · right; exact ⟨x, by simp [Γs], fun j hj => by simp [Γs, Ne.symm hj]⟩
  · rcases h i with ⟨hS, hi⟩ | ⟨hS, A, hi⟩
    · have hΓs : Γs i = Ctx.empty n := by
        funext x; simp only [Γs, Ctx.empty]; split_ifs with hx
        · rw [hx, hi]
        · rfl
      simp only [hS, Bool.false_eq_true, ↓reduceIte, hΓs, As, hi, bangArg]
      exact promote_unit
    · simp only [hS, ↓reduceIte, As, hi, bangArg]
      exact IHasType.var (by simp [Γs, hi]) (fun j hj => by simp [Γs, hj])

end LinExp

end
