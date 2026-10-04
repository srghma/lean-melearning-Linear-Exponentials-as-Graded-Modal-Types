module

public import RequestProject.Sec2_CoreCalculus.Typing

/-!
# Section 4: the `hsup` operation

The pre-ordered semiring of grades is extended with a partial, commutative and associative
binary operation `⊔ : R × R ⇀ R` (pronounced "hsup"), used in the typing of product patterns
underneath a box:

```
r ⊢ p₁ : A ▷ Γ₁     s ⊢ p₂ : B ▷ Γ₂
────────────────────────────────────── [PPROD]
 r ⊔ s ⊢ (p₁, p₂) : A ⊗ B ▷ Γ₁, Γ₂
```

Partiality is modelled with `Option`; associativity is Kleene equality of the two
bracketings.  The *adjusted* GrCore calculus is `Typed HSup.hsup` (written `AdjTyped`).
-/

@[expose] public section

namespace LinExp

/-- A partial commutative and associative operation on grades. -/
class HSup (R : Type) where
  /-- `hsup r s = some t` means `r ⊔ s = t`; `none` means undefined. -/
  hsup : R → R → Option R
  comm : ∀ r s, hsup r s = hsup s r
  assoc : ∀ r s t, (hsup r s).bind (fun u => hsup u t) = (hsup s t).bind (fun u => hsup r u)

/-- The typing judgement of the adjusted GrCore calculus of Section 4, whose rule `[PPROD]`
uses the `hsup` operation of the grades. -/
abbrev AdjTyped {R : Type} [Semiring R] [Preorder R] [HSup R] {n : ℕ} (Γ : GCtx R n)
    (t : Term n) (A : Ty R) : Prop :=
  Typed HSup.hsup Γ t A

/-- The operation `diagHsup` (`r ⊔ s = r` if `r = s`, undefined otherwise) is a valid `hsup`
operation; with it the adjusted calculus is exactly the calculus of Section 2 (`GrCore`).
For the exact-usage semiring (`ℕ` ordered by equality) this is the partial least upper bound,
as remarked in the paper. -/
def HSup.diag (R : Type) [DecidableEq R] : HSup R where
  hsup := diagHsup
  comm r s := by unfold diagHsup; split_ifs <;> simp_all
  assoc r s t := by
    unfold diagHsup
    by_cases h1 : r = s <;> by_cases h2 : s = t <;> simp_all

lemma adjTyped_diag_iff {R : Type} [Semiring R] [Preorder R] [DecidableEq R] {n : ℕ}
    (Γ : GCtx R n) (t : Term n) (A : Ty R) :
    @AdjTyped R _ _ (HSup.diag R) n Γ t A ↔ GrCore Γ t A := Iff.rfl

end LinExp

end
