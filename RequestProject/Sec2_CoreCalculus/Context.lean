module

public import Mathlib

/-!
# Contexts over de Bruijn indices (generic infrastructure)

A context for a term with `n` free de Bruijn indices is a function `Fin n → Option E`:
index `0` is the most recently bound variable.  An entry `none` means that the variable is
in scope but *not available* (it carries no assumption); this is how the paper's named
contexts (which only list the variables actually assumed) are represented over a fixed
scope of `n` indices.

This file is generic in the type of entries `E` and is shared by `GrCore` (Section 2) and by
IMELL (Section 4).
-/

@[expose] public section

namespace LinExp

/-- A context over `n` de Bruijn indices with entries in `E`. -/
abbrev Ctx (E : Type) (n : ℕ) := Fin n → Option E

namespace Ctx

variable {E : Type}

/-- The empty context: no variable carries an assumption. -/
def empty (n : ℕ) : Ctx E n := fun _ => none

/-- Extend a context by a new innermost variable (de Bruijn index `0`). -/
def cons {n : ℕ} (e : Option E) (Γ : Ctx E n) : Ctx E (n + 1) := Fin.cons e Γ

/-- `Γ ++ Δ`: extend `Γ` by the `k` binders of `Δ`.  The entries of `Δ` occupy the innermost
indices `0, …, k-1` (so the paper's `Γ, Δ`). -/
def append {n k : ℕ} (Γ : Ctx E n) (Δ : Ctx E k) : Ctx E (n + k) :=
  fun i => if h : i.val < k then Δ ⟨i.val, h⟩ else Γ ⟨i.val - k, by omega⟩

@[inherit_doc] scoped infixl:65 " ++ " => append

@[simp] lemma cons_zero {n : ℕ} (e : Option E) (Γ : Ctx E n) : cons e Γ 0 = e := rfl
@[simp] lemma cons_succ {n : ℕ} (e : Option E) (Γ : Ctx E n) (i : Fin n) :
    cons e Γ i.succ = Γ i := rfl

lemma append_low {n k : ℕ} (Γ : Ctx E n) (Δ : Ctx E k) (i : Fin (n + k)) (h : i.val < k) :
    append Γ Δ i = Δ ⟨i.val, h⟩ := by simp [append, h]

lemma append_high {n k : ℕ} (Γ : Ctx E n) (Δ : Ctx E k) (i : Fin (n + k)) (h : ¬ i.val < k) :
    append Γ Δ i = Γ ⟨i.val - k, by omega⟩ := by simp [append, h]

@[simp] lemma append_zero {n : ℕ} (Γ : Ctx E n) (Δ : Ctx E 0) : append Γ Δ = Γ := by
  funext i; simp [append]

lemma append_one {n : ℕ} (Γ : Ctx E n) (Δ : Ctx E 1) : append Γ Δ = cons (Δ 0) Γ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [append, cons]
  · simp [append, cons]

lemma append_succ {n k : ℕ} (Γ : Ctx E n) (Δ : Ctx E (k + 1)) :
    append Γ Δ = cons (Δ 0) (append Γ (fun j => Δ j.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [append, cons]
  · simp only [append, cons, Fin.cons_succ, Fin.val_succ]
    by_cases h : i.val < k
    · rw [dif_pos (by omega), dif_pos h]; rfl
    · rw [dif_neg (by omega), dif_neg h]; congr 1; ext; simp

/-- Lift a renaming under `k` binders. -/
def liftN {n m : ℕ} (k : ℕ) (ρ : Fin n → Fin m) : Fin (n + k) → Fin (m + k) :=
  fun i => if h : i.val < k then ⟨i.val, by omega⟩ else
    ⟨(ρ ⟨i.val - k, by omega⟩).val + k, by have := (ρ ⟨i.val - k, by omega⟩).isLt; omega⟩

lemma liftN_injective {n m : ℕ} (k : ℕ) (ρ : Fin n → Fin m) (hρ : Function.Injective ρ) :
    Function.Injective (liftN k ρ) := by
  intro a b h
  simp only [liftN] at h
  split_ifs at h with h1 h2 h2 <;> simp [Fin.ext_iff] at h
  · exact Fin.ext h
  · omega
  · omega
  · have := hρ (Fin.ext h)
    simp [Fin.ext_iff] at this
    exact Fin.ext (by omega)

/-- Push a context forward along a renaming: entries are moved to their new positions and the
positions outside the range of `ρ` become unavailable. -/
noncomputable def push {n m : ℕ} (ρ : Fin n → Fin m) (Γ : Ctx E n) : Ctx E m := by
  classical
  exact fun j => if h : ∃ i, ρ i = j then Γ h.choose else none

lemma push_apply {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (Γ : Ctx E n)
    (i : Fin n) : push ρ Γ (ρ i) = Γ i := by
  classical
  have h : ∃ i', ρ i' = ρ i := ⟨i, rfl⟩
  simp only [push, h, dite_true]
  rw [hρ h.choose_spec]

lemma push_off {n m : ℕ} (ρ : Fin n → Fin m) (Γ : Ctx E n) (j : Fin m)
    (hj : ∀ i, ρ i ≠ j) : push ρ Γ j = none := by
  classical
  have h : ¬ ∃ i, ρ i = j := fun ⟨i, hi⟩ => hj i hi
  simp [push, h]

/-- A context agreeing with `Γ` along `ρ` and empty elsewhere is `push ρ Γ`. -/
lemma eq_push {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) {Γ : Ctx E n}
    {Γ' : Ctx E m} (h1 : ∀ i, Γ' (ρ i) = Γ i) (h2 : ∀ j, (∀ i, ρ i ≠ j) → Γ' j = none) :
    Γ' = push ρ Γ := by
  funext j
  by_cases hj : ∃ i, ρ i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [h1, push_apply hρ]
  · push_neg at hj
    rw [h2 j hj, push_off ρ Γ j hj]

/-- Lifting a renaming commutes with appending binders. -/
lemma liftN_append_apply {n m k : ℕ} (ρ : Fin n → Fin m) (Γ' : Ctx E m) (Δ : Ctx E k)
    (i : Fin (n + k)) :
    append Γ' Δ (liftN k ρ i) = append (fun j => Γ' (ρ j)) Δ i := by
  by_cases h : i.val < k
  · simp [liftN, h, append]
  · have h' : ¬ ((ρ ⟨i.val - k, by omega⟩).val + k < k) := by omega
    simp only [liftN, h, dite_false, append, h', dite_false]
    congr 1; ext; simp

lemma liftN_off {n m k : ℕ} (ρ : Fin n → Fin m) (Γ' : Ctx E m) (Δ : Ctx E k)
    (hoff : ∀ j, (∀ i, ρ i ≠ j) → Γ' j = none) (j : Fin (m + k))
    (hj : ∀ i, liftN k ρ i ≠ j) : append Γ' Δ j = none := by
  by_cases h : j.val < k
  · exfalso
    apply hj ⟨j.val, by omega⟩
    simp [liftN, h]
  · rw [append_high _ _ _ h]
    apply hoff
    intro i hi
    apply hj ⟨i.val + k, by omega⟩
    have : ¬ (i.val + k < k) := by omega
    have e : (⟨i.val + k - k, by omega⟩ : Fin n) = i := Fin.ext (by simp)
    simp only [liftN, this, dite_false, e, hi]
    ext; simp; omega

/-- Sums over an appended context split into the two parts. -/
lemma sum_append {M : Type} [AddCommMonoid M] (f : Option E → M) {n k : ℕ} (Γ : Ctx E n)
    (Δ : Ctx E k) :
    ∑ i, f (append Γ Δ i) = (∑ i, f (Γ i)) + ∑ i, f (Δ i) := by
  rw [← Fintype.sum_equiv (finCongr (Nat.add_comm k n)) (fun j => f (append Γ Δ
    (finCongr (Nat.add_comm k n) j))) _ (fun _ => rfl), Fin.sum_univ_add, add_comm]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [append_high]
    · congr 2; ext; simp
    · simp
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [append_low _ _ _ (by simp [finCongr])]
    rfl

end Ctx

end LinExp

end
