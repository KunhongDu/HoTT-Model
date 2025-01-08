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

lemma Monotone.exists_eq_of_le {f : Fin (m + 1) → Fin n} (hf : Monotone f) :
    n ≤ m → ∃ i : Fin m, f i.castSucc = f i.succ := by
  intro h; contrapose! h
  apply StrictMono.le (hf.strictMono_of_injective (injective_of_lt_imp_ne _))
  intro i j hij
  apply (lt_of_lt_of_le
    ((hf (castSucc_lt_succ i).le).lt_of_ne (h <| i.castPred (ne_last_of_lt hij)))
    (hf (castSucc_lt_iff_succ_le.mp hij))).ne

open Set in
lemma range_succAbove_succAbove_of_castSucc_lt (i : Fin (n + 1)) (j : Fin (n + 2))
  (hij : i.castSucc < j) :
    range (j.succAbove ∘ i.succAbove) = {i.castSucc, j}ᶜ := by
  simp only [range_comp, range_succAbove, compl_eq_univ_diff,
             image_diff succAbove_right_injective, image_univ,
             range_succAbove, image_singleton, diff_diff,
             union_comm {j}]
  congr
  rw [succAbove_of_castSucc_lt _ _ hij]

-- a crucial one

section

open Set
noncomputable def factor_of_range_subset (f : Fin (n + 1) →o Fin m) (g : Fin k →o Fin m)
  (h : range g ⊆ range f) :
    Fin k →o Fin (n + 1) where
  toFun i := sSup {j | f j = g i}
  monotone' i j hij := by
    rcases eq_or_lt_of_le (g.monotone hij) with hij | hij
    simp only [hij]; apply le_refl
    simp only [mem_setOf_eq]
    apply sSup_le_sSup_of_forall_exists_le
    intro l hl
    obtain ⟨l', hl'⟩ := h ⟨j, rfl⟩
    exact ⟨l', hl', (f.monotone.reflect_lt (hl'.symm ▸ hl.symm ▸ hij)).le⟩

lemma factor_of_range_subset_spec (f : Fin (n + 1) →o Fin m) (g : Fin k →o Fin m) (h : range g ⊆ range f) :
    g = f ∘ factor_of_range_subset f g h := by
  ext i : 1
  simp [factor_of_range_subset]
  have : sSup {j | f j = g i} ∈ {j | f j = g i} := by
    apply Nonempty.csSup_mem
    exact h ⟨i, rfl⟩
    rw [← finite_coe_iff]
    apply Subtype.finite
  exact this.symm

lemma exists_OrderHom_comp_iff_range_subset {n m k} (f : Fin n →o Fin m) (g : Fin k →o Fin m) :
    (∃ h : Fin k →o Fin n, g = f ∘ h) ↔ range g ⊆ range f := by
  constructor
  . rw [range_subset_range_iff_exists_comp]
    exact fun ⟨h, hh⟩ ↦ ⟨⇑h, hh⟩
  . cases n with
  | zero =>
      cases k with
      | zero => intro; use OrderHom.id; ext i; exact i.elim0
      | succ => rw [Set.range_eq_empty f]; intro h; apply False.elim $ h ⟨0, rfl⟩
  | succ n =>
      intro h
      exact ⟨factor_of_range_subset f g h, factor_of_range_subset_spec _ _ h⟩


end
end Fin
