module

public import RequestProject.Sec3_DissectingTheProblem.Push
public import RequestProject.Sec4_Solution.HsupLub
public import RequestProject.Sec4_Solution.Theorem1.Theorem1
public import RequestProject.Sec4_Solution.PushNotDerivable

/-!
# Section 3: Quantitative Type Theory as a variant of GrCore

QTT eliminates tensor products only *linearly*.  Ignoring type dependency, taking `σ = 1`
and `π = 1`, the paper simplifies QTT's rule to

```
0Γ₁ = 0Γ₂     Γ₁ ⊢ M : S ⊗ T     Γ₂, x¹ : S, y¹ : T ⊢ N : U
─────────────────────────────────────────────────────────────
           Γ₁ + Γ₂ ⊢ let (x, y) = M in N : U
```

(the premise `0Γ₁ = 0Γ₂` only concerns the types of the variables and is automatic for a
simply typed calculus).  Keeping `π` general, QTT's graded pair `(x^π : S) ⊗ T` is the GrCore
type `□_π S ⊗ T`, eliminated by the pattern `([x], y)`, which binds `x : [S]_π`.

What QTT does *not* have is a way to take apart a pair that sits underneath a grade: there is
no counterpart of GrCore's `[PPROD]` rule.  We therefore model (the propositional fragment of)
QTT as the variant of GrCore whose `[PPROD]` rule is never applicable, i.e. `Typed qttHsup`
where `qttHsup r s` is always undefined (`QTTTyped`).  All other rules, including `(PPROD)`
for unboxed pairs, `(PBOX)` and `[PVAR]`, are kept.

Results:

* `QTTTyped.letPair` and `QTTTyped.letGradedPair`: the two QTT rules above are rules of the
  variant;
* `qtt_no_pair_under_box`: no product pattern can be typed underneath a box;
* `qtt_pushTerm_ill_typed`: over *any* semiring, at *any* grade, the GrCore term
  `push = λz. let [(x, y)] = z in ([x], [y])` has no type in QTT;
* `qttTyped_to_typed`: every QTT derivation is a derivation of GrCore (Section 2) and of
  the adjusted calculus (Section 4), whatever `hsup` is;
* `qtt_push_many_not_derivable`: over `{0, 1, ω}`, *no* closed term of QTT has type
  `□_ω (α ⊗ β) ⊸ □_ω α ⊗ □_ω β`;
* `qtt_conservative_over_imell`: over `{0, 1, ω}`, every QTT judgement translates into a
  derivable IMELL judgement (QTT is a conservative extension of linear logic).

The last two results use the model and Theorem 1 of Section 4; like Section 1, this file
refers forward to that section.
-/

@[expose] public section

namespace LinExp

variable {R : Type}

/-- The operation used by `[PPROD]` in QTT: never defined, so that a product pattern can never
be matched underneath a box. -/
def qttHsup (_ _ : R) : Option R := none

/-- `qttHsup` is (vacuously) a partial commutative and associative operation. -/
def HSup.qtt (R : Type) : HSup R where
  hsup := qttHsup
  comm _ _ := rfl
  assoc _ _ _ := rfl

variable [Semiring R] [Preorder R]

/-- The typing judgement of (simply typed, propositional) QTT, as a variant of GrCore. -/
abbrev QTTTyped {n : ℕ} (Γ : GCtx R n) (t : Term n) (A : Ty R) : Prop :=
  Typed qttHsup Γ t A

/-- The simplified QTT rule for tensor products (`π = σ = 1`): the components are bound
linearly. -/
theorem QTTTyped.letPair {n : ℕ} {Γ₁ Γ₂ Γ : GCtx R n} {M : Term n} {N : Term (n + (1 + 1))}
    {S T U : Ty R} (hM : QTTTyped Γ₁ M (S ⊗ T))
    (hN : QTTTyped (Ctx.append Γ₂ (Ctx.append (fun _ => some (.lin S))
      (fun _ => some (.lin T)))) N U)
    (hadd : CtxAdd Γ₁ Γ₂ Γ) :
    QTTTyped Γ (Term.letPat (Pat.pair Pat.var Pat.var) M N) U :=
  Typed.letPat hM (PatTy.pair (PatTy.var S) (PatTy.var T)) hN hadd

/-- QTT's rule for its graded pairs `(x^π : S) ⊗ T` (non-dependent, `σ = 1`), with
`(x^π : S) ⊗ T` read as `□_π S ⊗ T`: the first component is bound with grade `π`. -/
theorem QTTTyped.letGradedPair {n : ℕ} {Γ₁ Γ₂ Γ : GCtx R n} {M : Term n}
    {N : Term (n + (1 + 1))} {S T U : Ty R} {π : R} (hM : QTTTyped Γ₁ M (□[π] S ⊗ T))
    (hN : QTTTyped (Ctx.append Γ₂ (Ctx.append (fun _ => some (.grad S π))
      (fun _ => some (.lin T)))) N U)
    (hadd : CtxAdd Γ₁ Γ₂ Γ) :
    QTTTyped Γ (Term.letPat (Pat.pair (Pat.box Pat.var) Pat.var) M N) U :=
  Typed.letPat hM (PatTy.pair (PatTy.box π (PatTy.gvar π S)) (PatTy.var T)) hN hadd

/-- Is a pattern a product pattern? -/
def Pat.isPair {k : ℕ} : Pat k → Bool
  | .pair _ _ => true
  | _ => false

omit [Semiring R] [Preorder R] in
/-- In QTT, a pattern typed underneath a box is never a product pattern. -/
theorem PatTy.qtt_not_isPair {k : ℕ} {o : Option R} {p : Pat k} {A : Ty R} {Δ : GCtx R k}
    (h : PatTy qttHsup o p A Δ) : o.isSome → p.isPair = false := by
  induction h with
  | gpair _ _ hrs => exact absurd hrs (by simp [qttHsup])
  | pair => intro h; simp at h
  | _ => intro _; rfl

omit [Semiring R] [Preorder R] in
/-- In QTT no product pattern can be typed underneath a box. -/
theorem qtt_no_pair_under_box {k₁ k₂ : ℕ} (p₁ : Pat k₁) (p₂ : Pat k₂) (r : R) (A : Ty R)
    (Δ : GCtx R (k₁ + k₂)) : ¬ PatTy (qttHsup (R := R)) (some r) (Pat.pair p₁ p₂) A Δ :=
  fun h => absurd (h.qtt_not_isPair rfl) (by simp [Pat.isPair])

/-- Does a term start with a match on a product pattern underneath a box,
`let [(p₁, p₂)] = t₁ in t₂`? -/
def Term.isLetBoxPair {n : ℕ} : Term n → Bool
  | .letPat (.box (.pair _ _)) _ _ => true
  | _ => false

/-- A QTT-typable term never starts with `let [(p₁, p₂)] = t₁ in t₂`. -/
theorem QTTTyped.not_isLetBoxPair {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R}
    (h : QTTTyped Γ t A) : t.isLetBoxPair = false := by
  induction h with
  | letPat _ hp _ _ =>
    cases hp with
    | box r hp' =>
      cases hp' with
      | gvar => rfl
      | gpair _ _ hrs => exact absurd hrs (by simp [qttHsup])
      | unit => rfl
    | _ => rfl
  | der _ _ ih => exact ih
  | weak _ _ _ ih => exact ih
  | approx _ _ _ ih => exact ih
  | _ => rfl

/-- Inversion for abstractions (in any variant of GrCore): the body of a typable abstraction is
typable. -/
theorem Typed.lam_inv {hs : R → R → Option R} {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R}
    (h : Typed hs Γ t A) :
    ∀ b : Term (n + 1), t = .lam b → ∃ (Γ' : GCtx R (n + 1)) (B : Ty R), Typed hs Γ' b B := by
  induction h with
  | lam hb _ =>
    intro b e
    cases e
    exact ⟨_, _, hb⟩
  | der _ _ ih => exact ih
  | weak _ _ _ ih => exact ih
  | approx _ _ _ ih => exact ih
  | _ => intro b e; cases e

/-- **QTT does not admit `push`.**  Over any semiring and at any grade, the GrCore term
`push = λz. let [(x, y)] = z in ([x], [y])` has no type in QTT, in any context. -/
theorem qtt_pushTerm_ill_typed {n : ℕ} (Γ : GCtx R n) (T : Ty R)
    (t : Term (n + 1)) (ht : t.isLetBoxPair = true) : ¬ QTTTyped Γ (.lam t) T := by
  intro h
  obtain ⟨Γ', B, hb⟩ := h.lam_inv t rfl
  rw [QTTTyped.not_isLetBoxPair hb] at ht
  exact Bool.false_ne_true ht

/-- In particular, the closed term `push` of Section 1 has no type in QTT. -/
theorem qtt_push_ill_typed (T : Ty R) : ¬ QTTTyped (Ctx.empty 0) pushTerm T :=
  qtt_pushTerm_ill_typed _ T _ rfl

/-- Every QTT derivation is a derivation of the variant of GrCore whose `[PPROD]` rule uses
any operation `hs`. -/
theorem qttTyped_to_typed (hs : R → R → Option R) {n : ℕ} {Γ : GCtx R n} {t : Term n}
    {A : Ty R} (h : QTTTyped Γ t A) : Typed hs Γ t A :=
  h.mono (fun _ _ _ e => absurd e (by simp [qttHsup]))

/-- QTT is a fragment of GrCore (Section 2). -/
theorem qttTyped_to_grcore [DecidableEq R] {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R}
    (h : QTTTyped Γ t A) : GrCore Γ t A :=
  qttTyped_to_typed _ h

/-- QTT is a fragment of the adjusted calculus (Section 4), for any `hsup`. -/
theorem qttTyped_to_adjTyped [HSup R] {n : ℕ} {Γ : GCtx R n} {t : Term n} {A : Ty R}
    (h : QTTTyped Γ t A) : AdjTyped Γ t A :=
  qttTyped_to_typed _ h

open LNL in
/-- **QTT does not admit `push` (at the type level).**  Over `{0, 1, ω}`, no closed term of
QTT has type `□_ω (α ⊗ β) ⊸ □_ω α ⊗ □_ω β` for distinct atoms `α`, `β`. -/
theorem qtt_push_many_not_derivable {i j : ℕ} (hij : i ≠ j) :
    ¬ ∃ t : Term 0, QTTTyped (Ctx.empty 0) t (pushTy ω (.atom i) (.atom j)) :=
  fun ⟨t, ht⟩ => adj_push_many_not_derivable hij ⟨t, qttTyped_to_adjTyped ht⟩

/-- **QTT is a conservative extension of linear logic.**  Over `{0, 1, ω}`, every QTT
judgement `Γ ⊢ t : A` translates (with the translation of Theorem 1) into a derivable IMELL
judgement `⟦Γ⟧ ⊢ M : ⟦A⟧`. -/
theorem qtt_conservative_over_imell {n : ℕ} {Γ : GCtx LNL n} {t : Term n} {A : Ty LNL}
    (h : QTTTyped Γ t A) : ∃ M, IHasType (trCtx Γ) M (trTy A) :=
  theorem1.1 n Γ t A (qttTyped_to_adjTyped h)

end LinExp

end
