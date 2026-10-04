module

public import Mathlib

/-!
# Section 4 (proof tool): a resource-counting model of linear logic

To show that certain types are *not* derivable (e.g. that `push` is not derivable for
`!A = □_ω A` in the adjusted calculus, and not derivable in IMELL) we use a simple
algebraic model.

Values are integers extended with `-∞` and `+∞`, read as "costs": a sequent `Γ ⊢ A` is
valid when `⟦A⟧ ≤ Σ ⟦Γ⟧`.  The tensor is addition (with `+∞` absorbing everything, and
`-∞` absorbing finite values), the unit is `0`, linear implication is the residual
`a ⊸ b` (`res a b ≤ c ↔ b ≤ c + a`), and the exponential is
`!a = 0` if `a ≤ 0` and `!a = +∞` otherwise.
-/

@[expose] public section

namespace LinExp

/-- Extended integers `{-∞} ∪ ℤ ∪ {+∞}`. -/
inductive Val : Type where
  | ninf
  | fin (a : ℤ)
  | pinf
  deriving DecidableEq

namespace Val

/-- Order embedding into `WithBot (WithTop ℤ)`. -/
def toW : Val → WithBot (WithTop ℤ)
  | ninf => ⊥
  | fin a => ((a : WithTop ℤ) : WithBot (WithTop ℤ))
  | pinf => ((⊤ : WithTop ℤ) : WithBot (WithTop ℤ))

lemma toW_injective : Function.Injective toW := by
  intro a b h
  cases a <;> cases b <;> simp_all [toW]

instance : LinearOrder Val := LinearOrder.lift' toW toW_injective

lemma le_def (a b : Val) : a ≤ b ↔ toW a ≤ toW b := Iff.rfl

@[simp] lemma ninf_le (a : Val) : ninf ≤ a := by
  rw [le_def]; exact bot_le

@[simp] lemma le_pinf (a : Val) : a ≤ pinf := by
  rw [le_def]; cases a <;> simp [toW]

@[simp] lemma fin_le_fin (a b : ℤ) : fin a ≤ fin b ↔ a ≤ b := by
  rw [le_def]; simp [toW]

@[simp] lemma pinf_le_iff (a : Val) : pinf ≤ a ↔ a = pinf := by
  rw [le_def]; cases a <;> simp [toW]

@[simp] lemma le_ninf_iff (a : Val) : a ≤ ninf ↔ a = ninf := by
  rw [le_def]; cases a <;> simp [toW]

/-- Addition: `+∞` is absorbing, then `-∞` is absorbing. -/
def add : Val → Val → Val
  | pinf, _ => pinf
  | _, pinf => pinf
  | ninf, _ => ninf
  | _, ninf => ninf
  | fin a, fin b => fin (a + b)

instance : Zero Val := ⟨fin 0⟩
instance : Add Val := ⟨add⟩

lemma zero_eq : (0 : Val) = fin 0 := rfl

attribute [local simp] zero_eq
@[simp] lemma pinf_add (a : Val) : pinf + a = pinf := by cases a <;> rfl
@[simp] lemma add_pinf (a : Val) : a + pinf = pinf := by cases a <;> rfl
@[simp] lemma fin_add_fin (a b : ℤ) : fin a + fin b = fin (a + b) := rfl
@[simp] lemma ninf_add_fin (a : ℤ) : ninf + fin a = ninf := rfl
@[simp] lemma fin_add_ninf (a : ℤ) : fin a + ninf = ninf := rfl
@[simp] lemma ninf_add_ninf : ninf + ninf = ninf := rfl

instance : AddCommMonoid Val where
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> simp [add_assoc]
  zero_add a := by cases a <;> simp
  add_zero a := by cases a <;> simp
  add_comm a b := by cases a <;> cases b <;> simp [add_comm]
  nsmul := nsmulRec

instance : IsOrderedAddMonoid Val where
  add_le_add_left a b h c := by
    cases a <;> cases b <;> cases c <;> simp_all

/-- Residual (linear implication) `a ⊸ b`. -/
def res : Val → Val → Val
  | _, ninf => ninf
  | pinf, _ => ninf
  | ninf, _ => pinf
  | fin a, fin b => fin (b - a)
  | fin _, pinf => pinf

lemma res_le_iff (a b c : Val) : res a b ≤ c ↔ b ≤ c + a := by
  cases a <;> cases b <;> cases c <;> simp [res]

/-- The exponential: `!a = 0` if `a ≤ 0`, and `+∞` otherwise. -/
def bang (a : Val) : Val := if a ≤ 0 then 0 else pinf

/-- "Idempotent" values: `0` and `+∞`. -/
def IsIdem (v : Val) : Prop := v = 0 ∨ v = pinf

lemma bang_isIdem (a : Val) : IsIdem (bang a) := by
  unfold bang IsIdem; split_ifs <;> simp

lemma IsIdem.add {v w : Val} (hv : IsIdem v) (hw : IsIdem w) : IsIdem (v + w) := by
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;> simp [IsIdem]

lemma IsIdem.zero : IsIdem 0 := Or.inl rfl

lemma IsIdem.sum {ι : Type} (s : Finset ι) (f : ι → Val) (h : ∀ i ∈ s, IsIdem (f i)) :
    IsIdem (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsIdem.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Promotion in the model: below an idempotent value, `a` may be replaced by `!a`. -/
lemma bang_le_of_le {a v : Val} (hv : IsIdem v) (h : a ≤ v) : bang a ≤ v := by
  rcases hv with rfl | rfl
  · unfold bang; rw [if_pos h]
  · simp

lemma le_bang (a : Val) : a ≤ bang a := by
  unfold bang; split_ifs with h
  · exact h
  · simp

lemma zero_le_bang (a : Val) : 0 ≤ bang a := by
  unfold bang; split_ifs <;> simp

lemma bang_add_bang (a : Val) : bang a + bang a = bang a := by
  unfold bang; split_ifs <;> simp

lemma add_le_bang (a : Val) : a + a ≤ bang a := by
  unfold bang; split_ifs with h
  · cases a <;> simp_all
  · simp

lemma bang_add_le (a : Val) : bang a + a ≤ bang a := by
  unfold bang; split_ifs with h
  · rw [zero_add]; exact h
  · simp

lemma bang_zero : bang 0 = 0 := by simp [bang]

end Val

end LinExp

end
