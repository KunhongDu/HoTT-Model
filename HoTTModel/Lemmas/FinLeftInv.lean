import Mathlib.Order.Fin
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Fintype.Order

section LeftInv
open Set Function Classical

namespace Fin
/-
lemma aux (x : X.obj m) (hx : Nondegenerate x) (f : m ⟶ n) (hmn : m.len ≤ n.len) :
    Nondegenerate x := by
-/

-- i want to generalize it to arbitrary orders, but well some conditions are needed
-- but i don't know what
/-
noncomputable def left_inv {m n : ℕ} {f : Fin (m + 1) →o Fin (n + 1)} (hf : Injective f) :
  Fin (n + 1) → Fin (m + 1)
| 0 => 0
| ⟨k + 1, lt⟩ => if ⟨k + 1, lt⟩ ∈ range f then (⇑f).invFun ⟨k + 1, lt⟩
    else (left_inv hf ⟨k, k.lt_succ_self.trans lt⟩)

lemma left_inv_zero {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (hf : Injective f)
  (k : ℕ) (lt : k < n + 1) :
    left_inv hf 0 = 0 := by sorry ---?????

lemma left_inv_comp {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (hf : Injective f) :
    left_inv hf ∘ f = id := by
  ext ⟨i, hi⟩; simp
  cases i with
  | zero =>
      simp; by_cases h : f 0 = ⟨0, by norm_num⟩
      rw [h]
      simp [left_inv]
      sorry
  | succ i => sorry
-/

noncomputable def LeftInv {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
  Fin (n + 1) → Fin (m + 1)
| k => if sSup {i | i ≤ k ∧ i ∈ range f} = 0 then 0
    else f.invFun (sSup {i | i ≤ k ∧ i ∈ range f})

namespace LeftInv

variable {m n : ℕ} {f : Fin (m + 1) → Fin (n + 1)} {k : Fin (n + 1)}

lemma sSup_eq (h : sSup {i | i ≤ k ∧ i ∈ range f} = 0) :
    LeftInv f k = 0 := by
  dsimp [LeftInv]; rw [if_pos h]

lemma sSup_ne (h : sSup {i | i ≤ k ∧ i ∈ range f} ≠ 0) :
    LeftInv f k = f.invFun (sSup {i | i ≤ k ∧ i ∈ range f}) := by
  dsimp [LeftInv]; rw [if_neg h]

lemma zero :
    LeftInv f 0 = 0 := by
  apply sSup_eq
  erw [eq_bot_iff]
  apply sSup_le
  simp [Fin.bot_eq_zero]

lemma ne_zero_mem_range (hk : k ≠ 0) (hk' : k ∈ range f):
    LeftInv f k = f.invFun k := by
  have : sSup {i | i ≤ k ∧ i ∈ range f} = k := by
    apply le_antisymm
    apply sSup_le
    simp
    exact fun _ h _ _ ↦ h
    apply le_sSup
    simpa
  rw [sSup_ne (by convert hk), this]

lemma comp_eq_id (hf : Injective f) (hf' : Monotone f) :
    LeftInv f ∘ f = id := by
  ext ⟨l, hl⟩ : 1
  cases l with
  | zero =>
      simp
      by_cases h : f 0 = 0
      . rw [h, zero]
      . rw [ne_zero_mem_range h (by simp)]
        apply leftInverse_invFun hf
  | succ l =>
      simp
      by_cases h : f ⟨l + 1, hl⟩ = 0
      . have : f 0 = 0 := by
          erw [eq_bot_iff, Fin.bot_eq_zero, ← h]
          apply hf' (Fin.zero_le _)
        rw [← h] at this
        apply hf at this
        simp only [← val_eq_val, val_zero] at this
      . rw [ne_zero_mem_range h (by simp)]
        apply leftInverse_invFun hf

lemma _root_.Fin.invFun_partially_monotone (hf : Injective f) (hf' : Monotone f)
  {i j : Fin (n + 1)} (hi : i ∈ range f) (hj : j ∈ range f) (hij : i ≤ j):
    f.invFun i ≤ f.invFun j := by
  obtain ⟨i', hi'⟩ := hi
  obtain ⟨j', hj'⟩ := hj
  rw [← hi', leftInverse_invFun hf i',
      ← hj', leftInverse_invFun hf j']
  rwa [← hi', ← hj', (hf'.strictMono_of_injective hf).le_iff_le] at hij

lemma sSup_mem (S : Set (Fin (n + 1))) (hS : sSup S ≠ 0) :
    sSup S ∈ S := by
  apply Set.Nonempty.csSup_mem
  . contrapose! hS
    simp only [hS, sSup_empty, Fin.bot_eq_zero]
  . rw [finite_def]
    exact ⟨Subtype.fintype _⟩

lemma monotone (hf : Injective f) (hf' : Monotone f) :
    Monotone (LeftInv f) := by
  intro i j hij
  have : sSup {k | k ≤ i ∧ k ∈ range f} ≤ sSup {k | k ≤ j ∧ k ∈ range f} := by
    apply sSup_le_sSup
    intro l hl
    exact ⟨hl.1.trans hij, hl.2⟩
  by_cases hi : sSup {k | k ≤ i ∧ k ∈ range f} = 0
  . simp only [sSup_eq hi, Fin.zero_le]
  have hj : sSup {k | k ≤ j ∧ k ∈ range f} ≠ 0 := by
    contrapose! hi
    rwa [← Fin.le_zero_iff, ← hi]
  rw [sSup_ne hi, sSup_ne hj]
  apply invFun_partially_monotone hf hf' _ _ this
  . apply Set.mem_of_mem_of_subset (sSup_mem _ hi) (fun _ h ↦ h.2)
  . apply Set.mem_of_mem_of_subset (sSup_mem _ hj) (fun _ h ↦ h.2)

end LeftInv

end Fin
