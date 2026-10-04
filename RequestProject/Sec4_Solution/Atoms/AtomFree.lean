module

public import RequestProject.Sec4_Solution.Atoms.Substitution
public import RequestProject.Sec4_Solution.PushNotDerivable
public import RequestProject.Sec4_Solution.IMELL.Facts
public import RequestProject.Sec4_Solution.Theorem1.Admissible
public import RequestProject.Sec4_Solution.Theorem1.AsStated

/-!
# Why atomic types are needed: without atoms every type is inhabited

The paper's grammar of types has no base types.  This file proves that in that atom-free
fragment every type has a closed term, both in GrCore and the adjusted calculus (for every
`⋉`, over every pre-ordered semiring in which each grade `r` satisfies `0 ⊑ r` or `1 ⊑ r`,
which includes `{0, 1, ω}`) and in IMELL.  Hence the underivability statements of the paper
(`⊬ push_!`, `⊬ □_ω (A ⊗ B) ⊸ □_ω A ⊗ □_ω B`, `⊬ A ⊸ A ⊗ !A`) are false for every atom-free
instance: they are only meaningful as statements about *schemas*, i.e. with `A`, `B` read as
type variables, which is what the atoms of this formalization are
(`RequestProject/Sec4_Solution/Atoms/Substitution.lean`).

Main results:
* `Ty.AtomFree`, `ITy.AtomFree`: the paper's (atom-free) types;
* `atomFree_inhabited` (GrCore / adjusted calculus) and `iatomFree_inhabited` (IMELL);
* `ideriv_atomFree`: without atoms every IMELL sequent `Γ ⊢ B` is provable;
* `adj_push_many_schema`, `imell_push_schema`, `imell_dup_bang_schema`: the paper's
  underivability results hold for the schema (no single term works for all instances,
  equivalently for distinct atoms), while every atom-free instance is derivable;
* `theorem1_as_stated_atomFree`: Theorem 1 with the paper's original translation holds on
  atom-free judgements, so its refutation needs atoms.
-/

@[expose] public section

namespace LinExp

variable {R : Type}

/-! ## GrCore -/

/-- A type of the paper's grammar `A ::= 1 | A ⊸ B | A ⊗ B | □_r A` (no atoms). -/
def Ty.AtomFree : Ty R → Prop
  | .atom _ => False
  | .unit => True
  | .lolli A B => A.AtomFree ∧ B.AtomFree
  | .tensor A B => A.AtomFree ∧ B.AtomFree
  | .box _ A => A.AtomFree

section GrCore

variable [Semiring R]

lemma CtxAdd.empty_left {n : ℕ} (Γ : GCtx R n) : CtxAdd (Ctx.empty n) Γ Γ :=
  fun _ => EntryAdd.noneLeft _

lemma CtxAdd.empty_right {n : ℕ} (Γ : GCtx R n) : CtxAdd Γ (Ctx.empty n) Γ := by
  intro i
  rcases h : Γ i with _ | a
  · exact EntryAdd.noneLeft _
  · exact EntryAdd.noneRight a

variable [Preorder R] {hs : R → R → Option R}

/-- A closed term can be used in any scope (with the empty context). -/
lemma Typed.closed {t : Term 0} {A : Ty R} (h : Typed hs (Ctx.empty 0) t A) (n : ℕ) :
    Typed hs (Ctx.empty n) (t.rename Fin.elim0) A :=
  h.rename (fun a => a.elim0) (fun i => i.elim0) (fun _ _ => rfl)

/-- Applying a closed function to a (linear) variable. -/
lemma Typed.app_closed_var {n : ℕ} {f : Term 0} {A B : Ty R}
    (hf : Typed hs (Ctx.empty 0) f (A ⊸ B)) {Γ : GCtx R n} {i : Fin n}
    (hi : Γ i = some (.lin A)) (hj : ∀ j, j ≠ i → Γ j = none) :
    Typed hs Γ (.app (f.rename Fin.elim0) (.var i)) B :=
  Typed.app (hf.closed n) (Typed.var hi hj) (CtxAdd.empty_left Γ)

/-- Applying a closed function to a closed argument. -/
lemma Typed.app_closed {n : ℕ} {f a : Term 0} {A B : Ty R}
    (hf : Typed hs (Ctx.empty 0) f (A ⊸ B)) (ha : Typed hs (Ctx.empty 0) a A) :
    Typed hs (Ctx.empty n) (.app (f.rename Fin.elim0) (a.rename Fin.elim0)) B :=
  Typed.app (hf.closed n) (ha.closed n) (CtxAdd.empty_left _)

/-- **Every atom-free type is inhabited** (GrCore and the adjusted calculus, for every `⋉`),
provided every grade is above `0` or above `1`.  Each such type `A` has a closed term, and
a closed term of type `A ⊸ 1` (so assumptions of type `A` can be discarded). -/
theorem atomFree_inhabited (h01 : ∀ r : R, 0 ≤ r ∨ 1 ≤ r) {A : Ty R} (hA : A.AtomFree) :
    (∃ t : Term 0, Typed hs (Ctx.empty 0) t A) ∧
      ∃ e : Term 0, Typed hs (Ctx.empty 0) e (A ⊸ .unit) := by
  induction A with
  | atom i => exact hA.elim
  | unit =>
    refine ⟨⟨.unit, Typed.unit (fun i => i.elim0)⟩, ⟨.lam (.var 0), Typed.lam ?_⟩⟩
    exact Typed.var rfl (fun j hj => by fin_cases j; simp at hj)
  | lolli A B ihA ihB =>
    obtain ⟨⟨a, ha⟩, ⟨ea, hea⟩⟩ := ihA hA.1
    obtain ⟨⟨b, hb⟩, ⟨eb, heb⟩⟩ := ihB hA.2
    refine ⟨⟨.lam (.letPat .unit (.app (ea.rename Fin.elim0) (.var 0)) (b.rename Fin.elim0)),
      Typed.lam ?_⟩, ⟨.lam (.app (eb.rename Fin.elim0)
        (.app (.var 0) (a.rename Fin.elim0))), Typed.lam ?_⟩⟩
    · refine Typed.letPat (Γ₂ := Ctx.empty 1) (Δ := Ctx.empty 0)
        (Typed.app_closed_var hea rfl ?_) (PatTy.unit none) ?_ (CtxAdd.empty_right _)
      · intro j hj; fin_cases j; simp at hj
      · simpa using hb.closed 1
    · refine Typed.app (heb.closed 1) ?_ (CtxAdd.empty_left _)
      refine Typed.app (Typed.var (i := 0) rfl ?_) (ha.closed 1) (CtxAdd.empty_right _)
      intro j hj; fin_cases j; simp at hj
  | tensor A B ihA ihB =>
    obtain ⟨⟨a, ha⟩, ⟨ea, hea⟩⟩ := ihA hA.1
    obtain ⟨⟨b, hb⟩, ⟨eb, heb⟩⟩ := ihB hA.2
    refine ⟨⟨.pair a b, Typed.pair ha hb (CtxAdd.empty_left _)⟩,
      ⟨.lam (.letPat (.pair .var .var) (.var 0)
        (.letPat .unit (.app (ea.rename Fin.elim0) (.var 1))
          (.app (eb.rename Fin.elim0) (.var 0)))), Typed.lam ?_⟩⟩
    refine Typed.letPat (Γ₂ := Ctx.empty 1)
      (Typed.var (i := 0) rfl (fun j hj => by fin_cases j; simp at hj))
      (PatTy.pair (PatTy.var A) (PatTy.var B)) ?_ (CtxAdd.empty_right _)
    let ΓA : GCtx R (1 + (1 + 1)) := fun i => if i.val = 1 then some (.lin A) else none
    let ΓB : GCtx R (1 + (1 + 1)) := fun i => if i.val = 0 then some (.lin B) else none
    refine Typed.letPat (Γ₁ := ΓA) (Γ₂ := ΓB) (Δ := Ctx.empty 0)
      (Typed.app_closed_var hea (by simp [ΓA]) (fun j hj => if_neg (fun h => hj (Fin.ext h))))
      (PatTy.unit none) ?_ ?_
    · simpa using Typed.app_closed_var heb (i := 0) (Γ := ΓB) (by simp [ΓB])
        (fun j hj => if_neg (fun h => hj (Fin.ext h)))
    · intro i
      fin_cases i <;> simp [ΓA, ΓB, Ctx.append, Ctx.empty] <;> constructor
  | box r A ihA =>
    obtain ⟨⟨a, ha⟩, ⟨ea, hea⟩⟩ := ihA hA
    refine ⟨⟨.box a, (ha.pr r (fun i => i.elim0)).of_eq (funext fun i => i.elim0)⟩, ?_⟩
    let Γb : GCtx R (1 + 1) := Ctx.append (Ctx.empty 1) (fun _ => some (.grad A r))
    suffices hbody : ∃ body : Term (1 + 1), Typed hs Γb body .unit by
      obtain ⟨body, hbody⟩ := hbody
      refine ⟨.lam (.letPat (.box .var) (.var 0) body), Typed.lam ?_⟩
      exact Typed.letPat (Γ₂ := Ctx.empty 1)
        (Typed.var (i := 0) rfl (fun j hj => by fin_cases j; simp at hj))
        (PatTy.box r (PatTy.gvar r A)) hbody (CtxAdd.empty_right _)
    rcases h01 r with h0 | h1
    · let Γ0 : GCtx R (1 + 1) := fun i => if i.val = 0 then some (.grad A 0) else none
      have hz : Typed hs Γ0 .unit .unit := by
        refine Typed.weak (Typed.unit (Γ := Ctx.empty _) (fun _ => rfl)) (Δ := Γ0) ?_
          (CtxAdd.empty_left _)
        intro i; simp only [Γ0]; split_ifs
        · exact Or.inr ⟨A, rfl⟩
        · exact Or.inl rfl
      refine ⟨.unit, (hz.approx (i := 0) (A := A) (by simp [Γ0]) h0).of_eq ?_⟩
      funext i; fin_cases i <;> simp [Γ0, Γb, Ctx.append, Ctx.empty]
    · let Γ1 : GCtx R (1 + 1) := fun i => if i.val = 0 then some (.grad A 1) else none
      have h1' : Typed hs Γ1 (.app (ea.rename Fin.elim0) (.var 0)) .unit :=
        Typed.app (hea.closed _) (Typed.var_one (by simp)
          (fun j hj => if_neg (fun h => hj (Fin.ext h)))) (CtxAdd.empty_left _)
      refine ⟨_, (h1'.approx (i := 0) (A := A) (by simp [Γ1]) h1).of_eq ?_⟩
      funext i; fin_cases i <;> simp [Γ1, Γb, Ctx.append, Ctx.empty]

end GrCore

/-! ## IMELL -/

/-- An IMELL formula without atoms: `A ::= I | A ⊸ B | A ⊗ B | !A`. -/
def ITy.AtomFree : ITy → Prop
  | .atom _ => False
  | .unit => True
  | .lolli A B => A.AtomFree ∧ B.AtomFree
  | .tensor A B => A.AtomFree ∧ B.AtomFree
  | .bang A => A.AtomFree

/-- A closed IMELL term can be used in any scope (with the empty context). -/
lemma IHasType.closed {M : ITerm 0} {A : ITy} (h : IHasType (Ctx.empty 0) M A) (n : ℕ) :
    IHasType (Ctx.empty n) (M.rename Fin.elim0) A :=
  h.rename (fun a => a.elim0) (fun i => i.elim0) (fun _ _ => rfl)

/-- Applying a closed IMELL function to a variable. -/
lemma IHasType.app_closed_var {n : ℕ} {f : ITerm 0} {A B : ITy}
    (hf : IHasType (Ctx.empty 0) f (.lolli A B)) {Γ : ICtx n} {i : Fin n}
    (hi : Γ i = some A) (hj : ∀ j, j ≠ i → Γ j = none) :
    IHasType Γ (.app (f.rename Fin.elim0) (.var i)) B :=
  IHasType.app (hf.closed n) (IHasType.var hi hj) (ISplit.empty_left Γ)

/-- **Every atom-free IMELL formula is provable.**  Each such formula `A` has a closed term,
and so does `A ⊸ I`. -/
theorem iatomFree_inhabited {A : ITy} (hA : A.AtomFree) :
    (∃ M : ITerm 0, IHasType (Ctx.empty 0) M A) ∧
      ∃ E : ITerm 0, IHasType (Ctx.empty 0) E (.lolli A .unit) := by
  induction A with
  | atom i => exact hA.elim
  | unit =>
    refine ⟨⟨.star, IHasType.star (fun i => i.elim0)⟩, ⟨.lam (.var 0), IHasType.lam ?_⟩⟩
    exact IHasType.var rfl (fun j hj => by fin_cases j; simp at hj)
  | lolli A B ihA ihB =>
    obtain ⟨⟨a, ha⟩, ⟨ea, hea⟩⟩ := ihA hA.1
    obtain ⟨⟨b, hb⟩, ⟨eb, heb⟩⟩ := ihB hA.2
    refine ⟨⟨.lam (.letStar (.app (ea.rename Fin.elim0) (.var 0)) (b.rename Fin.elim0)),
      IHasType.lam ?_⟩, ⟨.lam (.app (eb.rename Fin.elim0)
        (.app (.var 0) (a.rename Fin.elim0))), IHasType.lam ?_⟩⟩
    · exact IHasType.letStar (IHasType.app_closed_var hea rfl
        (fun j hj => by fin_cases j; simp at hj)) (hb.closed 1) (ISplit.empty_right _)
    · refine IHasType.app (heb.closed 1) ?_ (ISplit.empty_left _)
      exact IHasType.app (IHasType.var (i := 0) rfl (fun j hj => by fin_cases j; simp at hj))
        (ha.closed 1) (ISplit.empty_right _)
  | tensor A B ihA ihB =>
    obtain ⟨⟨a, ha⟩, ⟨ea, hea⟩⟩ := ihA hA.1
    obtain ⟨⟨b, hb⟩, ⟨eb, heb⟩⟩ := ihB hA.2
    refine ⟨⟨.pair a b, IHasType.pair ha hb (ISplit.empty_left _)⟩,
      ⟨.lam (.letPair (.var 0)
        (.letStar (.app (ea.rename Fin.elim0) (.var 1))
          (.app (eb.rename Fin.elim0) (.var 0)))), IHasType.lam ?_⟩⟩
    refine IHasType.letPair (Γ₂ := Ctx.empty 1)
      (IHasType.var (i := 0) rfl (fun j hj => by fin_cases j; simp at hj)) ?_
      (ISplit.empty_right _)
    let ΓA : ICtx (1 + 2) := fun i => if i.val = 1 then some A else none
    let ΓB : ICtx (1 + 2) := fun i => if i.val = 0 then some B else none
    refine IHasType.letStar (Γ₁ := ΓA) (Γ₂ := ΓB)
      (IHasType.app_closed_var hea (by simp [ΓA]) (fun j hj => if_neg (fun h => hj (Fin.ext h))))
      (IHasType.app_closed_var heb (i := 0) (by simp [ΓB])
        (fun j hj => if_neg (fun h => hj (Fin.ext h)))) ?_
    intro i
    fin_cases i <;> simp [ΓA, ΓB, Ctx.append, Ctx.empty, ctx2]
  | bang A ihA =>
    obtain ⟨⟨a, ha⟩, _⟩ := ihA hA
    refine ⟨⟨.promote (k := 0) Fin.elim0 a, ?_⟩,
      ⟨.lam (.discard (.var 0) .star), IHasType.lam ?_⟩⟩
    · have e : (fun j : Fin 0 => some (ITy.bang ((Fin.elim0 : Fin 0 → ITy) j))) =
          Ctx.empty 0 := funext fun j => j.elim0
      exact IHasType.promote (Γs := Fin.elim0) (As := Fin.elim0) (fun i => i.elim0)
        (fun j => j.elim0) (e ▸ ha)
    · exact IHasType.discard (IHasType.var (i := 0) rfl
        (fun j hj => by fin_cases j; simp at hj)) (IHasType.star (fun _ => rfl))
        (ISplit.empty_right _)

/-! ## Consequences: the paper's underivability results are statements about schemas -/

/-- In `{0, 1, ω}` every grade is above `0` or above `1`. -/
lemma LNL.zero_le_or_one_le (r : LNL) : 0 ≤ r ∨ 1 ≤ r := by
  cases r
  · exact Or.inl le_rfl
  · exact Or.inr le_rfl
  · exact Or.inl (Or.inr rfl)

/-- **Every atom-free type of the adjusted calculus over `{0, 1, ω}` is inhabited.** -/
theorem adj_atomFree_inhabited {A : Ty LNL} (hA : A.AtomFree) :
    ∃ t : Term 0, AdjTyped (Ctx.empty 0) t A :=
  (atomFree_inhabited LNL.zero_le_or_one_le hA).1

/-- **Every atom-free type of GrCore over `{0, 1, ω}` is inhabited.** -/
theorem grcore_atomFree_inhabited {A : Ty LNL} (hA : A.AtomFree) :
    ∃ t : Term 0, GrCore (Ctx.empty 0) t A :=
  (atomFree_inhabited LNL.zero_le_or_one_le hA).1

open LNL in
/-- **`⊬ □_ω (A ⊗ B) ⊸ □_ω A ⊗ □_ω B` is a statement about the schema.**  In the adjusted
calculus over `{0, 1, ω}`, no single closed term has this type for all `A`, `B` (equivalently,
by `typed_atoms_iff_schematic`, for distinct atoms), but every atom-free instance is
inhabited (by some term depending on `A` and `B`). -/
theorem adj_push_many_schema :
    (¬ ∃ t : Term 0, ∀ A B : Ty LNL, AdjTyped (Ctx.empty 0) t (pushTy ω A B)) ∧
      ∀ A B : Ty LNL, A.AtomFree → B.AtomFree →
        ∃ t : Term 0, AdjTyped (Ctx.empty 0) t (pushTy ω A B) := by
  refine ⟨fun ⟨t, ht⟩ => adj_push_many_not_derivable (i := 0) (j := 1) (by decide)
    ⟨t, ht _ _⟩, fun A B hA hB => adj_atomFree_inhabited ?_⟩
  exact ⟨⟨hA, hB⟩, hA, hB⟩

/-- **`⊬_LL push_!` is a statement about the schema.**  No single IMELL term proves
`!(A ⊗ B) ⊸ !A ⊗ !B` for all `A`, `B` (equivalently, for distinct atoms), but every atom-free
instance is provable. -/
theorem imell_push_schema :
    (¬ ∃ M : ITerm 0, ∀ A B : ITy, IHasType (Ctx.empty 0) M (pushBangTy A B)) ∧
      ∀ A B : ITy, A.AtomFree → B.AtomFree → IDeriv (Ctx.empty 0) (pushBangTy A B) := by
  refine ⟨fun ⟨M, hM⟩ => imell_push_not_derivable (i := 0) (j := 1) (by decide)
    ⟨M, hM _ _⟩, fun A B hA hB => (iatomFree_inhabited ?_).1⟩
  exact ⟨⟨hA, hB⟩, hA, hB⟩

/-- The same holds for `A ⊸ A ⊗ !A` (whose underivability refutes Theorem 1 as stated): no
single IMELL term proves it for all `A`, but every atom-free instance is provable.  So the
refutation `theorem1_grcore_to_imell_as_stated_false` needs atoms. -/
theorem imell_dup_bang_schema :
    (¬ ∃ M : ITerm 0, ∀ A : ITy, IHasType (Ctx.empty 0) M (.lolli A (.tensor A (.bang A)))) ∧
      ∀ A : ITy, A.AtomFree → IDeriv (Ctx.empty 0) (.lolli A (.tensor A (.bang A))) := by
  refine ⟨fun ⟨M, hM⟩ => imell_not_derivable_atom_tensor_bang 0 ⟨M, hM _⟩,
    fun A hA => (iatomFree_inhabited ?_).1⟩
  exact ⟨hA, hA, hA⟩

/-- An atom-free formula can be added as an extra assumption (and consumed with its
eliminator `A ⊸ I`). -/
lemma PosEnt.addAtomFree {C : ITy} (hC : C.AtomFree) : PosEnt none (some C) := by
  intro n Γ i B ⟨M, hM⟩
  obtain ⟨_, E, hE⟩ := iatomFree_inhabited hC
  exact ⟨_, IHasType.letStar (IHasType.app_closed_var hE (Γ := isingle i C) (i := i)
    (by simp [isingle]) (fun j hj => by simp [isingle, hj])) hM (ISplit.single_update Γ i _)⟩

/-- **Without atoms every IMELL sequent is provable**: if all assumptions and the conclusion
are atom-free, then `Γ ⊢ B`. -/
theorem ideriv_atomFree {n : ℕ} {Γ : ICtx n} {B : ITy} (hΓ : ∀ i C, Γ i = some C → C.AtomFree)
    (hB : B.AtomFree) : IDeriv Γ B := by
  obtain ⟨⟨M, hM⟩, _⟩ := iatomFree_inhabited hB
  refine IDeriv.ctxwise (Γ := Ctx.empty n) (fun i => ?_) ⟨_, hM.closed n⟩
  rcases h : Γ i with _ | C
  · exact PosEnt.refl _
  · exact PosEnt.addAtomFree (hΓ i C h)

/-- An assumption without atoms. -/
def Assm.AtomFree {R : Type} : Assm R → Prop
  | .lin A => A.AtomFree
  | .grad A _ => A.AtomFree

lemma trTyPaper_atomFree {A : Ty LNL} (hA : A.AtomFree) : (trTyPaper A).AtomFree := by
  induction A with
  | atom i => exact hA.elim
  | unit => trivial
  | lolli A B ihA ihB => exact ⟨ihA hA.1, ihB hA.2⟩
  | tensor A B ihA ihB => exact ⟨ihA hA.1, ihB hA.2⟩
  | box r A ih => cases r <;> exact ih hA

/-- **Theorem 1 as stated holds without atoms.**  With the paper's own translation
(`□_0 A ↦ !⟦A⟧`), every atom-free judgement `Γ ⊢ A` (derivable or not) has an IMELL term
`⟦Γ⟧ ⊢ M : ⟦A⟧`.  So the refutation `theorem1_grcore_to_imell_as_stated_false` depends on the
atoms, i.e. on reading the paper's types as schemas. -/
theorem theorem1_as_stated_atomFree {n : ℕ} (Γ : GCtx LNL n) (A : Ty LNL)
    (hΓ : ∀ i a, Γ i = some a → a.AtomFree) (hA : A.AtomFree) :
    ∃ M, IHasType (trCtxPaper Γ) M (trTyPaper A) := by
  refine ideriv_atomFree (fun i C hC => ?_) (trTyPaper_atomFree hA)
  simp only [trCtxPaper, Option.map_eq_some_iff] at hC
  obtain ⟨a, ha, rfl⟩ := hC
  cases a with
  | lin B => exact trTyPaper_atomFree (hΓ i _ ha)
  | grad B r => exact trTyPaper_atomFree (A := .box r B) (hΓ i _ ha)

end LinExp

end
