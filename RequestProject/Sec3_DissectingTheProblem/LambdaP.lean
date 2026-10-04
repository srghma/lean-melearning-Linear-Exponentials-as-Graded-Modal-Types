module

public import RequestProject.Sec3_DissectingTheProblem.QTT

/-!
# Section 3: Abel and Bernardy's `Λ^p`

`Λ^p` is a graded type system in which every variable of the context carries a grade, so a
judgement is `γ Γ ⊢ t : A` with a *grade vector* `γ` (one grade per variable).  Its rule for
pattern matching on products carries an extra grade `q`:

```
γ Γ ⊢ t : A × B        δ Γ, x :^q A, y :^q B ⊢ u : C
────────────────────────────────────────────────────
     (q γ + δ) Γ ⊢ let (x, y) =^q t in u : C
```

`q`-many inhabitants of `A × B` yield `q`-many `A`s and `q`-many `B`s.  With `q = 1` this is
the simplified QTT rule.

We formalize the propositional fragment of `Λ^p` used in the paper: linear functions, tensor
products, the unit and a graded box `□_r A`, with grade annotations `q` on the eliminators
(`letPair q`, `letBox q`, `letUnit q`), and a subsumption rule `γ ⊑ γ'`.  (The function types of
`Λ^p` are themselves graded, `q A → B`; we only use `1 A → B`, written `A ⊸ B`.)  Terms use
de Bruijn indices and are indexed by the number of free variables (`LTerm R 0` = closed terms);
contexts are a type vector `Γ : Fin n → Ty R` and a grade vector `γ : Fin n → R`.

Results:

* `LTyped.letPair_one`: the `q = 1` instance of the `Λ^p` rule is the simplified QTT rule;
* `lamP_push`: `Λ^p` admits `push` at every grade, over every semiring;
* `grcore_lamP_letPair`: the `Λ^p` rule is a derived rule of GrCore, by nesting a product
  pattern inside an unboxing pattern (`let [(x, y)] = [t] in u`), i.e. it is "akin to the
  elimination behaviour underneath a graded modality in GrCore";
* `lamP_vs_qtt`: over `{0, 1, ω}`, `Λ^p` derives `□_ω (α ⊗ β) ⊸ □_ω α ⊗ □_ω β`, but neither
  QTT nor linear logic (after translation) does.
-/

@[expose] public section

namespace LinExp

namespace LamP

/-- Terms of `Λ^p` with `n` free de Bruijn indices; the eliminators carry a grade `q`. -/
inductive LTerm (R : Type) : ℕ → Type where
  | var {n : ℕ} : Fin n → LTerm R n
  | lam {n : ℕ} : LTerm R (n + 1) → LTerm R n
  | app {n : ℕ} : LTerm R n → LTerm R n → LTerm R n
  | pair {n : ℕ} : LTerm R n → LTerm R n → LTerm R n
  | unit {n : ℕ} : LTerm R n
  /-- `[t]`, introduction of the graded box -/
  | box {n : ℕ} : LTerm R n → LTerm R n
  /-- `let (x, y) =^q t in u`; in `u`, `y` has index `0` and `x` index `1` -/
  | letPair {n : ℕ} : R → LTerm R n → LTerm R (n + 2) → LTerm R n
  /-- `let [x] =^q t in u` -/
  | letBox {n : ℕ} : R → LTerm R n → LTerm R (n + 1) → LTerm R n
  /-- `let () =^q t in u` -/
  | letUnit {n : ℕ} : R → LTerm R n → LTerm R n → LTerm R n

/-- Extend a vector (of types or grades) by a new innermost variable. -/
def ext {α : Type} {n : ℕ} (a : α) (v : Fin n → α) : Fin (n + 1) → α := Fin.cons a v

@[simp] lemma ext_zero {α : Type} {n : ℕ} (a : α) (v : Fin n → α) : ext a v 0 = a := rfl
@[simp] lemma ext_succ {α : Type} {n : ℕ} (a : α) (v : Fin n → α) (i : Fin n) :
    ext a v i.succ = v i := rfl

variable {R : Type} [Semiring R] [Preorder R]

/-- The typing judgement `γ Γ ⊢ t : A` of `Λ^p`. -/
inductive LTyped : {n : ℕ} → (Fin n → Ty R) → (Fin n → R) → LTerm R n → Ty R → Prop
  /-- a variable is used once: its grade vector is the unit vector at `i` -/
  | var {n : ℕ} {Γ : Fin n → Ty R} (i : Fin n) : LTyped Γ (Pi.single i 1) (.var i) (Γ i)
  | lam {n : ℕ} {Γ : Fin n → Ty R} {γ : Fin n → R} {t : LTerm R (n + 1)} {A B : Ty R} :
      LTyped (ext A Γ) (ext 1 γ) t B → LTyped Γ γ (.lam t) (A ⊸ B)
  | app {n : ℕ} {Γ : Fin n → Ty R} {γ δ : Fin n → R} {t u : LTerm R n} {A B : Ty R} :
      LTyped Γ γ t (A ⊸ B) → LTyped Γ δ u A → LTyped Γ (γ + δ) (.app t u) B
  | pair {n : ℕ} {Γ : Fin n → Ty R} {γ δ : Fin n → R} {t u : LTerm R n} {A B : Ty R} :
      LTyped Γ γ t A → LTyped Γ δ u B → LTyped Γ (γ + δ) (.pair t u) (A ⊗ B)
  | unit {n : ℕ} {Γ : Fin n → Ty R} : LTyped Γ 0 .unit .unit
  | box {n : ℕ} {Γ : Fin n → Ty R} {γ : Fin n → R} {t : LTerm R n} {A : Ty R} (r : R) :
      LTyped Γ γ t A → LTyped Γ (r • γ) (.box t) (□[r] A)
  /-- the `Λ^p` rule for pattern matching on products -/
  | letPair {n : ℕ} {Γ : Fin n → Ty R} {γ δ : Fin n → R} {t : LTerm R n} {u : LTerm R (n + 2)}
      {A B C : Ty R} (q : R) :
      LTyped Γ γ t (A ⊗ B) → LTyped (ext B (ext A Γ)) (ext q (ext q δ)) u C →
      LTyped Γ (q • γ + δ) (.letPair q t u) C
  | letBox {n : ℕ} {Γ : Fin n → Ty R} {γ δ : Fin n → R} {t : LTerm R n} {u : LTerm R (n + 1)}
      {A C : Ty R} {r : R} (q : R) :
      LTyped Γ γ t (□[r] A) → LTyped (ext A Γ) (ext (q * r) δ) u C →
      LTyped Γ (q • γ + δ) (.letBox q t u) C
  | letUnit {n : ℕ} {Γ : Fin n → Ty R} {γ δ : Fin n → R} {t u : LTerm R n} {C : Ty R}
      (q : R) :
      LTyped Γ γ t .unit → LTyped Γ δ u C → LTyped Γ (q • γ + δ) (.letUnit q t u) C
  /-- subsumption: grades may be approximated upwards -/
  | sub {n : ℕ} {Γ : Fin n → Ty R} {γ γ' : Fin n → R} {t : LTerm R n} {A : Ty R} :
      LTyped Γ γ t A → γ ≤ γ' → LTyped Γ γ' t A

/-- Typing is invariant under (propositional) equality of grade vectors. -/
lemma LTyped.cast {n : ℕ} {Γ : Fin n → Ty R} {γ γ' : Fin n → R} {t : LTerm R n} {A : Ty R}
    (h : LTyped Γ γ t A) (e : γ = γ') : LTyped Γ γ' t A := e ▸ h

/-- With `q = 1` the `Λ^p` rule is the simplified QTT rule: one `A × B` yields one `A` and
one `B`. -/
theorem LTyped.letPair_one {n : ℕ} {Γ : Fin n → Ty R} {γ δ : Fin n → R} {t : LTerm R n}
    {u : LTerm R (n + 2)} {A B C : Ty R} (ht : LTyped Γ γ t (A ⊗ B))
    (hu : LTyped (ext B (ext A Γ)) (ext 1 (ext 1 δ)) u C) :
    LTyped Γ (γ + δ) (.letPair 1 t u) C :=
  (LTyped.letPair 1 ht hu).cast (by rw [one_smul])

/-- `push` in `Λ^p` at grade `r`: `λz. let [w] =¹ z in let (x, y) =^r w in ([x], [y])`. -/
def pushTerm (r : R) : LTerm R 0 :=
  .lam (.letBox 1 (.var 0) (.letPair r (.var 0) (.pair (.box (.var 1)) (.box (.var 0)))))

/-- **`Λ^p` admits `push`**, at every grade and over every semiring. -/
theorem lamP_push (r : R) (A B : Ty R) :
    LTyped (Fin.elim0 : Fin 0 → Ty R) 0 (pushTerm r) (pushTy r A B) := by
  unfold pushTerm pushTy
  refine LTyped.lam ?_
  refine (LTyped.letBox (γ := Pi.single 0 1) (δ := 0) (r := r) (A := A ⊗ B) 1
    (LTyped.var 0) ?_).cast ?_
  · refine (LTyped.letPair (γ := Pi.single 0 1) (δ := 0) (A := A) (B := B) r
      (LTyped.var 0) ?_).cast ?_
    · refine (LTyped.pair (LTyped.box r (LTyped.var (Γ := ext B (ext A (ext (A ⊗ B)
        (ext (□[r] (A ⊗ B)) Fin.elim0)))) 1))
        (LTyped.box r (LTyped.var 0))).cast ?_
      funext i
      fin_cases i <;> simp [ext] <;> rfl
    · funext i
      fin_cases i <;> simp [ext]
  · funext i
    fin_cases i
    simp [ext]

end LamP

open LamP

variable {R : Type} [Semiring R] [Preorder R]

/-- **The `Λ^p` rule is derivable in GrCore** (Section 2), by nesting a product pattern inside
an unboxing pattern: from `[Γ₁] ⊢ t : A ⊗ B` and `Γ₂, x : [A]_q, y : [B]_q ⊢ u : C` we get
`q * Γ₁ + Γ₂ ⊢ let [(x, y)] = [t] in u : C`.  (In `Λ^p` every assumption is graded, hence the
hypothesis that `Γ₁` is graded.) -/
theorem grcore_lamP_letPair [DecidableEq R] {n : ℕ} {Γ₁ Γ₂ Γ : GCtx R n} {t : Term n}
    {u : Term (n + (1 + 1))} {A B C : Ty R} (q : R) (ht : GrCore Γ₁ t (A ⊗ B))
    (hg : IsGraded Γ₁)
    (hu : GrCore (Ctx.append Γ₂ (Ctx.append (fun _ => some (.grad A q))
      (fun _ => some (.grad B q)))) u C)
    (hadd : CtxAdd (scale q Γ₁) Γ₂ Γ) :
    GrCore Γ (.letPat (.box (.pair .var .var)) (.box t) u) C :=
  Typed.letBoxPair (by simp [diagHsup]) (ht.pr q hg) hu hadd

open LNL in
/-- **`Λ^p` versus QTT.**  Over `{0, 1, ω}` and for distinct atoms `α`, `β`, `Λ^p` derives
`□_ω (α ⊗ β) ⊸ □_ω α ⊗ □_ω β`, but QTT does not, and neither does linear logic (the
translation of this type with `□_ω = !` is `!(α ⊗ β) ⊸ !α ⊗ !β`). -/
theorem lamP_vs_qtt {i j : ℕ} (hij : i ≠ j) :
    LTyped (Fin.elim0 : Fin 0 → Ty LNL) 0 (LamP.pushTerm ω) (pushTy ω (.atom i) (.atom j)) ∧
      (¬ ∃ t : Term 0, QTTTyped (Ctx.empty 0) t (pushTy ω (.atom i) (.atom j))) ∧
      ¬ IDeriv (Ctx.empty 0) (trTy (pushTy ω (.atom i) (.atom j))) :=
  ⟨lamP_push ω _ _, qtt_push_many_not_derivable hij, imell_push_not_derivable hij⟩

end LinExp

end
