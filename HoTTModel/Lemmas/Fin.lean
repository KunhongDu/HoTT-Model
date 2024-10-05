import Mathlib.Order.Monotone.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Fintype.Order

namespace Fin

lemma le_image_of_StrictMono {f : Fin m → Fin n} (hf : StrictMono f) (i : Fin m) :
(i : ℕ) ≤ f i  := by
  obtain ⟨i, hi⟩ := i
  simp
  induction i with
  | zero => simp
  | succ n hn =>
      calc n + 1 ≤ f ⟨n, (Nat.lt_succ_self n).trans hi⟩ + 1 := by simp [hn]
      _ ≤ f ⟨n+1, hi⟩ := by
        rw [Nat.add_one_le_iff, ← Fin.lt_def]
        exact hf (by simp only [Fin.mk_lt_mk, Nat.lt_succ_self])

lemma StrictMono.le {f : Fin m → Fin n} (hf : StrictMono f) :
    m ≤ n := by
  cases m with
  | zero => simp
  | succ m =>
      rw [Nat.succ_le_iff]
      apply lt_of_le_of_lt (Fin.le_image_of_StrictMono hf (Fin.last _)) (is_lt _)

end Fin
