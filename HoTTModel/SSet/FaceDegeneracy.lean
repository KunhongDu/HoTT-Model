import Mathlib.AlgebraicTopology.SimplicialSet
import HoTTModel.Lemmas.Fin

open Function Set Classical
namespace Fin

section FinTransfer

def _root_.Eq.FinTransfer {m n : ℕ} (h : m = n) :
    Fin m ≃ Fin n where
      toFun :=  fun i ↦ ⟨i, h ▸ i.isLt⟩
      invFun := fun i ↦ ⟨i, h.symm ▸ i.isLt⟩
      left_inv := by dsimp [LeftInverse]; intro; rfl
      right_inv := by dsimp [Function.RightInverse]; intro; rfl

@[simp]
lemma FinTransfer.val {h : m = n} (i : Fin m) :
  (h.FinTransfer i).val = i.val := rfl

lemma FinTransfer.symm_comp {h h': m = n} :
    h.FinTransfer.symm ∘ h'.FinTransfer = id := rfl

lemma FinTransfer.symm_comp_apply {h h': m = n} (i : Fin m):
    h.FinTransfer.symm (h'.FinTransfer i) = i := rfl

lemma FinTransfer.trans {h : m = n} {h' : n = k} :
    h'.FinTransfer ∘ h.FinTransfer = (h.trans h').FinTransfer := rfl

lemma FinTransfer.trans_apply {h : m = n} {h' : n = k} (i : Fin m):
    h'.FinTransfer (h.FinTransfer i) = (h.trans h').FinTransfer i := rfl

lemma FinTransfer.symm_eq_symm {h : m = n} :
    h.FinTransfer.symm = h.symm.FinTransfer := rfl

lemma FinTransfer.comm  (h : m = n) {F G H : ℕ → ℕ} {h' : F m = F n} {h'' : G m = G n}
  {h''' : H m = H n}
  (f : {m : ℕ} → Fin (H m) → Fin (F m) → Fin (G m)) (i : Fin (H m)):
    f (h'''.FinTransfer i) ∘ h'.FinTransfer = h''.FinTransfer ∘ f i := by
  cases h
  rfl

lemma FinTransfer.comm_succAbove {h : m + 1 = n + 1} {h' : m = n} (i : Fin (m + 1)) :
    (h.FinTransfer i).succAbove  ∘ h'.FinTransfer = h.FinTransfer ∘ i.succAbove := by
  convert FinTransfer.comm h' (F := id) (G := Nat.succ) (H := Nat.succ) succAbove i

lemma FinTransfer.comm_succAbove' {h : m + 1 = n + 1} {h' : m = n} (i : Fin (m + 1)) :
    (h.FinTransfer i).succAbove = h.FinTransfer ∘ i.succAbove ∘ h'.FinTransfer.symm := by
  rw [← Function.comp_assoc, ← FinTransfer.comm_succAbove,
      Function.comp_assoc, Equiv.self_comp_symm, comp_id]

lemma FinTransfer.comm_predAbove {h : m = n} {h' : m + 1 = n + 1} (i : Fin m) :
    (h.FinTransfer i).predAbove  ∘ h'.FinTransfer = h.FinTransfer ∘ i.predAbove := by
  convert FinTransfer.comm h (F := Nat.succ) (G := id) (H := id) predAbove i

lemma FinTransfer.comm_predAbove' {h : m = n} {h' : m + 1 = n + 1} (i : Fin m) :
    (h.FinTransfer i).predAbove = h.FinTransfer ∘ i.predAbove ∘ h'.FinTransfer.symm := by
  rw [← Function.comp_assoc, ← FinTransfer.comm_predAbove,
      Function.comp_assoc, Equiv.self_comp_symm, comp_id]

end FinTransfer


section Face

def Face (n k : ℕ) := (i : Fin k) → Fin (n + ↑i + 1)

namespace Face

def head {n k : ℕ} : Face n (k + 1) → Face n k
  | f => fun i ↦ f i.castSucc

def tail {n k : ℕ} : Face n (k + 1) → Face (n + 1) k
  | f => fun i ↦ f i.succ

def function : {n k : ℕ} → (l : Face n k) → (Fin n → Fin (n + k))
  | _, 0, _ => id
  | _, _ + 1, l => (l (last _)).succAbove ∘ (l.head).function

def cons {n k: ℕ} (l : Face n k) (c : Fin (n + k + 1)) :
    Face n (k + 1)
  | i => if h : i ≠ (last k) then l (i.castPred h) else ⟨c.val, by
              convert c.isLt
              rwa [ne_eq, not_not, ← Fin.val_eq_val, val_last] at h⟩

def transport (d : Face n k) (e₁ : n = n') (e₂ : k = k')  :
    Face n' k'
  | i => (Eq.FinTransfer (by rw [e₁]; rfl)) (d (e₂.symm.FinTransfer i))

lemma head_transport (d : Face n (k + 1)) {e₁ : n = n'} {e₂ : k = k'} :
    d.head.transport e₁ e₂ = (d.transport e₁ (by rw [e₂])).head := by
  rfl

lemma transport_function (d : Face n k) {e₁ : n = n'} {e₂ : k = k'}  :
    (d.transport e₁ e₂).function =
      (Eq.FinTransfer (by rw [e₁, e₂]) ) ∘ d.function ∘ e₁.symm.FinTransfer := by
  induction k generalizing k' with
  | zero => subst e₂; simp [function]; rfl
  | succ k hk =>
      subst e₂
      simp [function, transport]
      have := @hk k d.head (Eq.refl _)
      rw [head_transport] at this
      rw [this, Function.comp_assoc, ← Function.comp_assoc (g := succAbove _),
          ← Function.comp_assoc (f := succAbove _)]
      congr! 1
      ext i
      erw [FinTransfer.comm_succAbove' (h' := by rw [e₁, FinTransfer.val, val_last])]
      rfl

lemma cons_head {n k : ℕ} (l : Face n k) (c : Fin (n + k + 1)):
    (l.cons c).head = l := by
  funext i
  simp only [head, cons]
  split_ifs with h
  . rfl
  . apply False.elim <| h (Fin.castSucc_lt_last _).ne

lemma head_cons {n k : ℕ} (l : Face n (k + 1)):
    l.head.cons (l (last k)) = l := by
  funext i
  simp only [head, cons]
  split_ifs with h
  . rfl
  . rw [ne_eq, not_not, eq_comm] at h
    have : k = i := by rwa [← val_eq_val, val_last] at h
    congr

variable (k n : ℕ)

namespace function

lemma zero {l : Face n 0} :
    l.function = id := rfl

lemma succ {l : Face n (k + 1)} :
    l.function = (l (last _)).succAbove ∘ (l.head).function := rfl

lemma one {l : Face n 1} :
    l.function = (l (last _)).succAbove := rfl

lemma one' {l : Face n 1} :
    l.function = (l 0).succAbove := rfl

end function

lemma cons_function {n k : ℕ} (l : Face n k) (c : Fin (n + k + 1)):
    (l.cons c).function = ((l.cons c) (last _)).succAbove ∘ l.function := by
  dsimp [function]; rw [cons_head]

variable {n k}

lemma strictMono (l : Face n k) :
    StrictMono l.function := by
  induction k with
  | zero => simp [function.zero]; apply strictMono_id
  | succ k hk =>
      simp [function.succ]
      apply StrictMono.comp (strictMono_succAbove _) (hk _)

lemma injective (l : Face n k) :
    l.function.Injective := l.strictMono.injective

lemma monotone (l : Face n k) :
    Monotone l.function := l.strictMono.monotone

def OrderEmbedding {k n} (l : Face n k) :
    Fin n ↪o Fin (n + k) := OrderEmbedding.ofStrictMono _ l.strictMono

end Face

section
-- goal, every OrderEmbedding can be written as `l.OrderEmebdding`

lemma not_surjective_of_lt (f : Fin m → Fin n) (h : m < n) :
    ¬ f.Surjective := by
  by_contra! hf
  apply not_le_of_lt h
  convert Fintype.card_le_of_surjective _ hf
  <;> simp only [Fintype.card_fin]

lemma le_of_surjective (f : Fin m → Fin n) (h : f.Surjective) :
    n ≤ m := by
  contrapose! h
  apply not_surjective_of_lt f h

lemma exists_not_mem_range_of_lt (f : Fin m → Fin n) (h : m < n) :
    ∃ i , i ∉ range f := by
  convert not_surjective_of_lt f h
  simp only [mem_range, not_exists, Surjective, not_forall]

noncomputable def choose_range (f : Fin m ↪o Fin (m + k + 1)) :
    Fin (m + k + 1) := choose (exists_not_mem_range_of_lt ⇑f
      (Nat.lt_add_of_pos_right (Nat.succ_pos _)))

lemma choose_range_spec (f : Fin m ↪o Fin (m + k + 1)) :
    choose_range f ∉ range f := choose_spec (exists_not_mem_range_of_lt ⇑f
      (Nat.lt_add_of_pos_right (Nat.succ_pos _)))

lemma choose_range_spec' (f : Fin m ↪o Fin (m + k + 1)) :
    ∀ i, f i ≠ choose_range f := by
  have := choose_range_spec f
  simp at this; exact this

noncomputable abbrev choose_range_succ (f : Fin m ↪o Fin (m + 1)) :
    Fin (m + 1) := choose_range (k := 0) f

lemma choose_range_succ_spec (f : Fin m ↪o Fin (m + 1)) :
    choose_range_succ f ∉ range f := choose_spec (exists_not_mem_range_of_lt ⇑f
      (Nat.lt_add_of_pos_right (Nat.succ_pos _)))

lemma mem_range_of_ne (f : Fin m ↪o Fin (m + 1)) (i j : Fin (m + 1))
  (hi : i ∉ range f) (hij : i ≠ j) :
    j ∈ range f := by
  have : (range ⇑f).toFinset.card = m := by
    simp [range]
    rw [Finset.card_image_of_injective _ f.injective]
    simp only [Finset.card_univ, Fintype.card_fin]
  have : (range ⇑f) ∪ {i} = univ := by
    rw [← Set.toFinset_inj]
    apply Finset.eq_of_subset_of_card_le
    . simp
    . simp only [toFinset_univ, Finset.card_univ, Fintype.card_fin, union_singleton,
      toFinset_insert]; rw [Finset.card_insert_of_not_mem (by rwa [Set.mem_toFinset]), this]
  have : j ∈ range f ∪ {i} := by rw [this]; trivial
  simp only [union_singleton, mem_insert_iff, or_iff_not_imp_left] at this
  apply this hij.symm

lemma choose_range_succ_uniq {f : Fin m ↪o Fin (m + 1)} (i : Fin (m + 1))
  (hi : ∀ j, f j ≠ i) :
    i = choose_range_succ f := by
  contrapose! hi
  convert mem_range_of_ne f (choose_range_succ f) i (choose_range_succ_spec f) hi.symm

lemma card_le (i : Fin n) : {j | j ≤ i}.toFinset.card = (i : ℕ) + 1 := by
  rw [toFinset_card]
  convert Fintype.card_fin_lt_of_le i.2 using 2
  simp only [coe_setOf]
  congr
  ext j
  rw [le_iff_val_le_val, Nat.lt_succ_iff]

lemma card_lt (i : Fin n) : {j | j < i}.toFinset.card = i := by
  have : {j | j ≤ i} = insert i {j | j < i} := by
    ext; simp [le_iff_eq_or_lt]
  rw [← Nat.add_left_inj (n := 1), ← card_le]
  simp only [this, toFinset_insert]
  rw [Finset.card_insert_of_not_mem (by simp)]

lemma card_gt_add (i : Fin n) : {j | j > i}.toFinset.card + i + 1 = n := by
  /-
  `rw [← Fintype.card_fin n]`  gives
  tactic 'rewrite' failed, motive is not type correct
  -/
  conv => rhs; rw [← Fintype.card_fin n]
  rw [add_assoc, ← card_le]
  convert Finset.card_add_card_compl {j | j > i}.toFinset
  simp only [mem_setOf_eq, toFinset_setOf, gt_iff_lt,
             Finset.compl_filter, not_lt]

lemma card_ge_add (i : Fin n) : {j | j ≥ i}.toFinset.card + i = n := by
  /-
  `rw [← Fintype.card_fin n]`  gives
  tactic 'rewrite' failed, motive is not type correct
  -/
  conv => rhs; rw [← Fintype.card_fin n]
  rw [← card_lt]
  convert Finset.card_add_card_compl {j | j ≥ i}.toFinset
  simp only [mem_setOf_eq, toFinset_setOf, ge_iff_le,
             Finset.compl_filter, not_le]

lemma image_eq_le (f : Fin m ↪o Fin (n)) (i : Fin m) (h : ∀ j ≤ f i, j ∈ range f) :
    f '' {j | j ≤ i} = {j | j ≤ f i} := by
  apply subset_antisymm
  . rintro j ⟨i', ⟨hi'₁, hi'₂⟩⟩
    simpa [← hi'₂]
  . intro j hj
    obtain ⟨i', hi'⟩ := h j hj
    use i'
    constructor
    . simp only [mem_setOf_eq, ← f.strictMono.le_iff_le]
      rwa [hi']
    . exact hi'

lemma image_eq_of_forall_le_mem_range {f : Fin m ↪o Fin (n)} {i : Fin m}
  (h : ∀ j ≤ f i, j ∈ range f) :
    (i : ℕ) = f i := by
  have := image_eq_le f i h
  rw [← Nat.succ_inj]
  apply_fun (fun x ↦ x.toFinset.card) at this
  convert this
  . simp only [toFinset_image, mem_setOf_eq]
    rw [Finset.card_image_of_injective _ f.injective, card_le]
  . convert (card_le _).symm
    -- why rw [card_le] does not work?????
    -- even `exact (card_le (f i)).symm` does not work
    -- ok; when do `apply Eq.trans (card_le (f i)).symm; congr`
    -- obtain; now i see the problem
    /-
    ⊢ (fun a ↦ decidableSetOf a fun j ↦ j ≤ f i) = fun a ↦ propDecidable (a ∈ {j | j ≤ f i})
    -/

lemma image_eq_castSucc_of_forall_le_castSucc_mem_range (f : Fin m ↪o Fin (m + 1))
  (i : Fin m) (h : ∀ j ≤ i.castSucc, j ∈ range f) :
    f i = i.castSucc := by
  obtain ⟨i', hi'⟩ := h i.castSucc (le_refl _)
  rw [← hi'] at h ⊢
  have := image_eq_of_forall_le_mem_range h
  rw [hi', coe_castSucc] at this
  congr
  rwa [← Fin.val_eq_val, eq_comm]

lemma image_eq_ge (f : Fin m ↪o Fin (n)) (i : Fin m) (h : ∀ j ≥ f i, j ∈ range f) :
    f '' {j | i ≤ j} = {j | f i ≤ j} := by
  apply subset_antisymm
  . rintro j ⟨i', ⟨hi'₁, hi'₂⟩⟩
    simpa [← hi'₂]
  . intro j hj
    obtain ⟨i', hi'⟩ := h j hj
    use i'
    constructor
    . simp only [mem_setOf_eq, ← f.strictMono.le_iff_le]
      rwa [hi']
    . exact hi'

lemma image_eq_of_forall_ge_mem_range {f : Fin m ↪o Fin (m + k)} {i : Fin m}
  (h : ∀ j ≥ f i, j ∈ range f) :
    (i : ℕ) + k = f i := by
  have := image_eq_ge f i h
  apply_fun toFinset at this
  have : (f '' {j | i ≤ j}).toFinset.card = {j | f i ≤ j}.toFinset.card := by
    congr
    -- if we don't do the previous two lines
    -- it asks us to show
    -- `HEq ({j | i ≤ j}.fintypeMap ⇑f) (Subtype.fintype fun x ↦ x ∈ {j | f i ≤ j})`
  simp only [toFinset_image, mem_setOf_eq] at this
  rwa [← Nat.add_left_inj (n := i), Finset.card_image_of_injective _ f.injective,
      card_ge_add, ← Nat.add_left_inj (n := f i), add_assoc, add_comm (i : ℕ),
      ← add_assoc, card_ge_add, add_assoc, Nat.add_right_inj, add_comm k,
      eq_comm] at this

lemma image_eq_succ_of_forall_ge_succ_mem_range (f : Fin m ↪o Fin (m + 1)) (i : Fin m)
  (h : ∀ j ≥ i.succ, j ∈ range f) :
    f i = i.succ := by
  -- rw [← Fin.val_eq_val, ← image_eq_of_forall_ge_mem_range, val_succ]
  obtain ⟨i', hi'⟩ := h i.succ (le_refl _)
  rw [← hi'] at h ⊢
  have := image_eq_of_forall_ge_mem_range (f := f) h
  rw [hi', val_succ] at this
  congr
  rwa [← Fin.val_eq_val, eq_comm, ← Nat.succ_inj]

lemma image_eq_castSucc_of_castSucc_lt {f : Fin m ↪o Fin (m + 1)} {i : Fin (m + 1)}
  (hi : i ∉ range f) {j : Fin m} (hj : j.castSucc < i) :
    f j = j.castSucc := by
  rw [← val_eq_val, coe_castSucc,
      image_eq_castSucc_of_forall_le_castSucc_mem_range, coe_castSucc]
  intro k hk
  apply mem_range_of_ne f i k hi (lt_of_le_of_lt hk hj).ne.symm

lemma image_eq_succ_of_forall_lt_succ {f : Fin m ↪o Fin (m + 1)} {i : Fin (m + 1)}
 (hi : i ∉ range f) {j : Fin m} (hj : i < j.succ) :
    f j = j.succ := by
  rw [← val_eq_val, val_succ,
      image_eq_succ_of_forall_ge_succ_mem_range, val_succ]
  intro k hk
  apply mem_range_of_ne f i k hi (lt_of_lt_of_le hj hk).ne

lemma eq_succAbove (f : Fin m ↪o Fin (m + 1)) :
    f = (choose_range_succ f).succAbove := by
  ext i : 1
  by_cases hi : i.castSucc < choose_range_succ f
  . rw [image_eq_castSucc_of_castSucc_lt (choose_range_succ_spec f) hi,
        succAbove_of_castSucc_lt _ _ hi]
  . rw [image_eq_succ_of_forall_lt_succ (choose_range_succ_spec f),
        succAbove_of_lt_succ _ _ ]
    <;> exact lt_of_le_of_lt (le_of_not_lt hi) (castSucc_lt_succ _)

-- `φ : Fin m → Fin (k + 2)` factors through `Fin m → Fin (k + 1)`

def factor {m k : ℕ} (f : Fin m → Fin (k + 2)) (j : Fin (k + 2)) :
    Fin m → Fin (k + 1) :=
  (predAbove 0 j).predAbove ∘ f

-- copied from
#check SimplexCategory.factor_δ_spec
lemma factor_spec {m k : ℕ} (f : Fin m → Fin (k + 2)) (j : Fin (k + 2))
  (hj : ∀ (k : Fin m), f k ≠ j) :
    j.succAbove ∘ (factor f j) = f := by
  ext k : 1
  specialize hj k
  cases' j using cases with j
  . dsimp [factor]
    rw [predAbove_of_castSucc_lt _ _
          (by rw [predAbove_of_le_castSucc _ _ (zero_le _), castPred_zero]; exact hj.bot_lt),
        succ_pred]
  . dsimp [factor]
    rw [predAbove_of_castSucc_lt 0 _ (castSucc_zero ▸ succ_pos _), pred_succ]
    rcases hj.lt_or_lt with (hj | hj)
    · rw [predAbove_of_le_castSucc j _]
      swap
      · exact (le_castSucc_iff.mpr hj)
      · rw [succAbove_of_castSucc_lt]
        swap
        · rwa [castSucc_lt_succ_iff, castPred_le_iff, le_castSucc_iff]
        rw [castSucc_castPred]
    · rw [predAbove_of_castSucc_lt]
      swap
      · exact (castSucc_lt_succ _).trans hj
      rw [succAbove_of_le_castSucc]
      swap
      · rwa [succ_le_castSucc_iff, lt_pred_iff]
      rw [succ_pred]
/-
-- `cast` is basically not-reasonable!!

def transp : Fin (m + 1 + k) ≃ Fin (m + k + 1) := by
  rw [add_assoc m, add_comm 1, ← add_assoc]

def transp' : Fin (m + 1 + k + 1) ≃ Fin (m + k + 1 + 1) := by
  rw [add_assoc m, add_comm 1, ← add_assoc]

def factor' : {m k : ℕ} → (f : Fin m → Fin (m + k + 1)) →
  (j : Fin (m + k + 1)) → (Fin m → Fin (m + k))
  | 0, _, _, _ => IsEmpty.elim' inferInstance
  | _ + 1, _, f, j => transp.invFun ∘ factor (transp'.toFun ∘ f) (transp'.toFun j)

def factor'_spec {m k : ℕ} (f : Fin m → Fin (m + k + 1)) (j : Fin (m + k + 1))
  (hj : ∀ (k : Fin m), f k ≠ j) :
    f = j.succAbove ∘ (factor' f j) := by
      cases m with
      | zero => ext x; apply IsEmpty.elim' inferInstance x
      | succ m =>
          simp [factor']
          have := factor_spec (transp'.toFun ∘ f) (transp'.toFun j) (by simp; exact hj)
          apply_fun fun x ↦ transp'.invFun ∘ x at this
          simp at this
          simp [← Function.comp_assoc, Equiv.symm_comp_self] at this
          conv => lhs; rw [this]
          conv => rhs; rw [← Function.comp_assoc]
          congr! 1
          sorry
-/

/-
def factor' : {m k : ℕ} → (f : Fin m → Fin (m + k + 1)) →
  (j : Fin (m + k + 1)) → (Fin m → Fin (m + k))
  | _, 0, _, _ => id
  | _, _ + 1, f, j => (predAbove ⟨0, by norm_num⟩ j).predAbove ∘ f

def factor'_eq {m k : ℕ} (f : Fin m → Fin (m + (k + 1) + 1))
    (j : Fin (m + (k + 1) + 1)) :
  factor' f j = factor f j := rfl

lemma factor'_spec {m k : ℕ} (f : Fin m → Fin (m + k + 1))
  (j : Fin (m + k + 1)) (hj : ∀ (l : Fin m), f l ≠ j) :
    f = j.succAbove ∘ (factor' f j) := by
  cases k with
  | zero => simp [factor']; sorry
  | succ k => rw [factor'_eq]; apply factor_spec _ _ hj
-/

def OrderEmbedding.factor : {m k : ℕ} → (f : Fin m ↪o Fin (m + k + 1)) →
  (j : Fin (m + k + 1)) → (hj : ∀ (k : Fin m), f k ≠ j) → (Fin m ↪o Fin (m + k))
  | _, 0, _, _, _ => RelEmbedding.refl _
  | _, _ + 1, f, j, hj =>{
    toFun := (predAbove ⟨0, by norm_num⟩ j).predAbove ∘ f
    inj' := by
      apply Injective.of_comp (f := j.succAbove)
      erw [factor_spec f j hj]
      exact f.injective
    map_rel_iff' := by
      intro i i'
      simp only [zero_eta, Embedding.coeFn_mk, comp_apply]
      conv =>
        lhs
        rw [← j.succAboveOrderEmb.map_rel_iff']
        repeat erw [Fin.succAboveOrderEmb_apply j]; rw [← Function.comp_apply
            (f := j.succAbove), ← Function.comp_apply (f := j.succAbove ∘ _)]
        erw [factor_spec f j hj]
      apply f.map_rel_iff'
  }

lemma OrderEmbedding.factor.coe {m k : ℕ} (f : Fin m ↪o Fin (m + (k + 1) + 1))
  (j : Fin (m + (k + 1) + 1)) (hj : ∀ (k : Fin m), f k ≠ j):
    ⇑(OrderEmbedding.factor f j hj) = Fin.factor ⇑f j := rfl

lemma OrderEmbedding.factor.spec {m k : ℕ} (f : Fin m ↪o Fin (m + k + 1))
  (j : Fin (m + k + 1)) (hj : ∀ (l : Fin m), f l ≠ j) :
    j.succAbove ∘ (OrderEmbedding.factor f j hj) = f := by
  cases k with
  | zero => simp [OrderEmbedding.factor]; rw [eq_succAbove, choose_range_succ_uniq j hj]; rfl
  | succ k => rw [OrderEmbedding.factor.coe]; apply factor_spec _ _ hj

noncomputable def toFace : {m k : ℕ} → (f : Fin m ↪o Fin (m + k)) → Face m k
  | _, 0, _ => fun i ↦ i.elim0
  | _, _ + 1, f =>
      (toFace <| OrderEmbedding.factor  f _ (choose_range_spec' f)).cons (choose_range f)

lemma OrderEmbedding.coe_eq_id (f : Fin m ↪o Fin m) :
    ⇑f = id := by
  have : (⇑f).Surjective := f.injective.surjective_of_fintype (Equiv.refl _)
  set h : Fin m ≃o Fin m := (RelIso.ofSurjective f this).symm
  have (i) : h (f i) = i := by
    apply_fun RelIso.ofSurjective f this
    simp only [h, RelIso.apply_symm_apply, RelIso.ofSurjective_apply]
  ext i; simp
  apply le_antisymm
  . erw [← Fin.le_iff_val_le_val, ← h.map_rel_iff', this,
         Fin.le_iff_val_le_val]
    apply le_image_of_StrictMono h.strictMono
  . apply le_image_of_StrictMono f.strictMono

lemma OrderHom.coe_eq_id_of_surjective (f : Fin m →o Fin m) (hf : Surjective f):
    ⇑f = id := OrderEmbedding.coe_eq_id (OrderEmbedding.ofStrictMono f
      (f.monotone.strictMono_of_injective (hf.injective_of_fintype (Equiv.refl _))))

lemma toFace.function {m k : ℕ} (f : Fin m ↪o Fin (m + k)) :
    (toFace f).function = ⇑f := by
  induction k with
  | zero => simp only [Nat.add_zero, Face.function, ← OrderEmbedding.coe_eq_id f]
  | succ k hk =>
      simp [toFace, Face.cons_function, hk, Face.cons]
      apply OrderEmbedding.factor.spec _ _ (choose_range_spec' f)

lemma toFace.OrderEmebdding {m k : ℕ} (f : Fin m ↪o Fin (m + k)) :
    (toFace f).OrderEmbedding = f :=
  DFunLike.coe_injective' (toFace.function f)

end

end Face

section Degeneracy

def Degeneracy (n k : ℕ) := (i : Fin k) → Fin (n + ↑i)

namespace Degeneracy

def head {n k : ℕ} : Degeneracy n (k + 1) → Degeneracy n k
  | f => fun i ↦ f i.castSucc

def function : {k n : ℕ} → (l : Degeneracy n k) → (Fin (n + k) → Fin n)
  | 0, _, _ => id
  | _ + 1, _, l => (l.head).function ∘ (l (last _)).predAbove

def cons {n k: ℕ} (l : Degeneracy n k) (c : Fin (n + k)) :
    Degeneracy n (k + 1)
  | i => if h : i ≠ (last k) then l (i.castPred h) else ⟨c.val, by
              convert c.isLt
              rwa [ne_eq, not_not, ← Fin.val_eq_val, val_last] at h⟩

def consd : {k : ℕ} → Degeneracy (n + 1) k → Fin n → Degeneracy n (k + 1)
  | _, _, j, 0 => j
  | _, l, _, ⟨k + 1, hk⟩ => by
    have eq : n + 1 + k = n + (k + 1) := by rw [Nat.add_comm k 1, ← Nat.add_assoc]
    exact eq.FinTransfer (l ⟨k, by rwa [← Nat.succ_lt_succ_iff]⟩)

def transport (d : Degeneracy n k) (e₁ : n = n') (e₂ : k = k') :
    Degeneracy n' k'
  | i => (Eq.FinTransfer (by rw [e₁]; rfl)) (d (e₂.symm.FinTransfer i))

lemma head_transport (d :Degeneracy n (k + 1)) {e₁ : n = n'} {e₂ : k = k'} :
    d.head.transport e₁ e₂ = (d.transport e₁ (by rw [e₂])).head := by
  rfl

lemma transport_function (d : Degeneracy n k) {e₁ : n = n'} {e₂ : k = k'}  :
    (d.transport e₁ e₂).function =
      e₁.FinTransfer ∘ d.function ∘ (Eq.FinTransfer (by rw [e₁, e₂]) ) := by
  induction k generalizing k' with
  | zero => subst e₂; simp [function]; rfl
  | succ k hk =>
      subst e₂
      simp [function, transport]
      have := @hk k d.head (Eq.refl _)
      rw [head_transport] at this
      rw [this, Function.comp_assoc, Function.comp_assoc, Function.comp_assoc,
          ← Function.comp_assoc (g := function _), ← Function.comp_assoc (g := function _)]
      congr! 1
      ext i
      rw [FinTransfer.comm_predAbove' (h' := by rw [e₁])]
      rfl

lemma cons_head {n k : ℕ} (l : Degeneracy n k) (c : Fin (n + k)):
    (l.cons c).head = l := by
  funext i
  simp only [head, cons]
  split_ifs with h
  . rfl
  . apply False.elim <| h (Fin.castSucc_lt_last _).ne

lemma head_cons {n k : ℕ} (l : Degeneracy n (k + 1)):
    l.head.cons (l (last k)) = l := by
  funext i
  simp only [head, cons]
  split_ifs with h
  . rfl
  . rw [ne_eq, not_not, eq_comm] at h
    have : k = i := by rwa [← val_eq_val, val_last] at h
    congr

def tail {n k : ℕ} : Degeneracy n (k + 1) → Degeneracy (n + 1) k
  | f => fun i ↦ by
      apply (Eq.FinTransfer _) (f i.succ)
      rw [val_succ, Nat.add_comm i.val, ← Nat.add_assoc]

variable (k n : ℕ)

lemma function.zero {l : Degeneracy n 0} :
    l.function = id := rfl

lemma function.succ {l : Degeneracy n (k + 1)} :
    l.function = (l.head).function ∘ (l (last _)).predAbove := rfl

lemma function.one {l : Degeneracy n 1} :
    l.function = (l (last _)).predAbove := rfl

lemma function.one' {l : Degeneracy n 1} :
    l.function = (l 0).predAbove := rfl

lemma cons_function {n k : ℕ} (l : Degeneracy n k) (c : Fin (n + k)):
    (l.cons c).function = l.function ∘ ((l.cons c) (last _)).predAbove := by
  dsimp [function]; rw [cons_head]

variable {n k}

lemma monotone (l : Degeneracy n k) :
    Monotone l.function := by
  induction k with
  | zero => simp [function.zero]; apply monotone_id
  | succ k hk =>
      simp [function.succ]
      apply Monotone.comp (hk _) (predAbove_right_monotone _)

-- put it somewhere else...
lemma _root_.Fin.predAbove_right_surjective {n : ℕ} (p : Fin n) :
    Surjective p.predAbove := by
  intro i
  rcases le_or_lt i p with h | h
  . use i.castSucc; rw [predAbove_castSucc_of_le _ _ h]
  . use i.succ; rw [predAbove_succ_of_le _ _ h.le]

lemma surjective (l : Degeneracy n k) :
    Surjective l.function := by
  induction k with
  | zero => simp [function.zero]; apply surjective_id
  | succ k hk =>
      simp [function.succ]
      apply Surjective.comp (hk _) (predAbove_right_surjective _)

def OrderHom {k n} (l : Degeneracy n k) :
    Fin (n + k) →o Fin n where
      toFun := l.function
      monotone' := l.monotone

end Degeneracy

section
-- goal, every Surjective OrderHom can be written as `l.OrderHom`

namespace OrderHom

variable {m k : ℕ} (f : Fin m →o Fin k)

def factor_succ (j : Fin k) :
    Fin m →o Fin (k + 1) where
      toFun := j.castSucc.succAbove ∘ f
      monotone' := Monotone.comp j.castSucc.strictMono_succAbove.monotone f.monotone

def factor_succ_spec (j : Fin k) :
    j.predAbove ∘ (factor_succ f j) = f := by
  dsimp [factor_succ]
  ext; simp only [comp_apply, predAbove_succAbove]

-- goal; factor Surjective OrderHom `Fin (m + 1) → Fin n`
-- into `Fin (m + 1) → Fin m` & `Fin m → Fin n`
variable(f : Fin (m + 1) →o Fin k)

def factor_pred (j : Fin m) :
    Fin m →o Fin k where
      toFun := f ∘ j.castSucc.succAbove
      monotone' := Monotone.comp f.monotone j.castSucc.strictMono_succAbove.monotone

lemma factor_pred_spec (j : Fin m) (hj : f j.castSucc = f j.succ) :
    (factor_pred f j) ∘ j.predAbove  = f := by
  ext i : 1
  rcases eq_or_ne i j.castSucc with h | h
  . simp only [factor_pred, OrderHom.coe_mk, comp_apply,
               h, hj, predAbove_castSucc_self, succAbove_castSucc_self]
  . simp only [factor_pred, OrderHom.coe_mk, comp_apply, Fin.succAbove_predAbove h]

lemma factor_pred_sujective (j : Fin m) (hj : f j.castSucc = f j.succ) (hf : Surjective f) :
    Surjective (factor_pred f j) := by
  rw [← factor_pred_spec _ _  hj] at hf
  apply Function.Surjective.of_comp hf

-- better proof???
lemma exists_eq_of_le (h : k ≤ m):
    ∃ i : Fin m, f i.castSucc = f i.succ := by
  contrapose! h
  apply StrictMono.le (f.monotone.strictMono_of_injective (injective_of_lt_imp_ne _))
  intro i j hij
  apply (lt_of_lt_of_le
    ((f.monotone (castSucc_lt_succ i).le).lt_of_ne (h <| i.castPred (ne_last_of_lt hij)))
    (f.monotone (castSucc_lt_iff_succ_le.mp hij))).ne

end OrderHom

noncomputable def choose_image_eq {m k : ℕ} (f : Fin (m + k + 1) →o Fin m) :
    Fin (m + k) := choose <| OrderHom.exists_eq_of_le f (Nat.le_add_right _ _)

lemma choose_image_eq_spec {m k : ℕ} (f : Fin (m + k + 1) →o Fin m) :
    f (choose_image_eq f).castSucc = f (choose_image_eq f).succ :=
  choose_spec <| OrderHom.exists_eq_of_le f (Nat.le_add_right _ _)

noncomputable def toDegeneracy : {m k : ℕ} → (f : Fin (m + k) →o Fin m) → Degeneracy m k
  | _, 0, _ => fun i ↦ i.elim0
  | _, _ + 1, f =>
      (toDegeneracy (OrderHom.factor_pred f (choose_image_eq f))).cons (choose_image_eq f)

open OrderHom Degeneracy in
lemma toDegeneracy.function {m k : ℕ} (f : Fin (m + k) →o Fin m) (hf : Surjective f) :
    (toDegeneracy f).function = ⇑f := by
  induction k with
  | zero =>
      dsimp [toDegeneracy, function]
      exact (coe_eq_id_of_surjective f hf).symm
  | succ k hk =>
      simp [toDegeneracy, function, cons_function, Degeneracy.cons]
      rw [hk _ (factor_pred_sujective _ _ (choose_image_eq_spec _) hf)]
      exact factor_pred_spec f (choose_image_eq f) (choose_image_eq_spec f)

end

section

-- goal : every injective `Fin n → Fin (n + k)` has an explicit left inverse
-- every surjective `Fin (n + k) → Fin n` has an explicit right inverse

-- note that `Degeneracy 0 k` is empty, so need to exclude that case

namespace Face
def reverse {n k : ℕ} (l : Face (n + 1) k) :
    Degeneracy (n + 1) k :=
  fun i ↦  predAbove ⟨0, by norm_num⟩ (l i)

lemma _root_.Fin.predAbove_succ_succAbove {n : ℕ} (p : Fin n) (i : Fin n) :
    p.predAbove (p.succ.succAbove i) = i := by
  rcases le_or_lt i p with h | h
  . rw [succAbove_of_succ_le _ _ (by rwa [succ_le_succ_iff]),
        predAbove_of_le_castSucc _ _ (by rwa [castSucc_le_castSucc_iff]),
        castPred_castSucc]
  . rw [succAbove_of_lt_succ _ _ (by rwa [succ_lt_succ_iff]),
        predAbove_of_succ_le _ _ (le_of_lt (by rwa [succ_lt_succ_iff])),
        pred_succ]

lemma _root_.Fin.zero_predAbove_predAbove_succAbove {n : ℕ} {k} :
    ((0 : Fin (n + 1)).predAbove k).predAbove ∘ k.succAbove = id := by
  ext i : 1; simp only [comp_apply, id_eq]
  cases' k using cases with k
  . simp only [predAbove_right_zero, zero_succAbove, predAbove_zero_succ]
  . simp only [predAbove_zero_succ, predAbove_succ_succAbove]

lemma _root_.Fin.zero_predAbove_predAbove_succAbove' (n : ℕ) (hn : 0 < n) (k) :
    (predAbove ⟨0, hn⟩ k).predAbove ∘ k.succAbove = id := by
  cases n with
  | zero => simp at hn
  | succ n => apply zero_predAbove_predAbove_succAbove

lemma reverse.is_leftInv {n k : ℕ} (l : Face (n + 1) k) :
    l.reverse.function ∘ l.function = id := by
  induction k with
  | zero => simp [function, Degeneracy.function]
  | succ k hk =>
      nth_rw 2 [← head_cons l]
      rw [← Degeneracy.head_cons l.reverse, cons_function l.head (l (last k)),
          Degeneracy.cons_function]
      simp [cons, Degeneracy.cons, reverse]
      rw [Function.comp_assoc, ← Function.comp_assoc (predAbove _)]
      simp [zero_predAbove_predAbove_succAbove' (n + 1 + k) (by norm_num) (l (last k))]
      exact hk l.head

end Face

namespace OrderEmbedding

noncomputable def leftInv (f : Fin (n + 1) ↪o Fin (n + 1 + k)) :
    Fin (n + 1 + k) →o Fin (n + 1) := (toFace f).reverse.OrderHom

lemma leftInv_spec (f : Fin (n + 1) ↪o Fin (n + 1 + k)) :
    (leftInv f) ∘ f = id := by
      dsimp [leftInv]
      convert Face.reverse.is_leftInv (toFace f)
      exact (toFace.function _).symm

noncomputable def leftInv_neZero : {n k : ℕ} → [NeZero n] → (f : Fin n ↪o Fin (n + k)) →
    Fin (n + k) →o Fin n
  | 0, _, ne, _ => by simp only [neZero_zero_iff_false] at ne
  | _ + 1, _, _, f => leftInv f

lemma leftInv_neZero_spec [NeZero n] (f : Fin n ↪o Fin (n + k)) :
    (leftInv_neZero f) ∘ f = id := by
  cases n with
  | zero => rename (NeZero 0) => ne; simp at ne
      -- there should be a lemma as an elimination rule fron `NeZero 0` automatically
  | succ => exact leftInv_spec _

end OrderEmbedding

namespace Degeneracy

def reverse {n k : ℕ} (l : Degeneracy n k) :
    Face n k :=
  fun i ↦  (l i).castSucc

lemma reverse.is_rightInv {n k : ℕ} (l : Degeneracy n k) :
     l.function ∘ l.reverse.function = id := by
  induction k with
  | zero => simp [function, Face.function]
  | succ k hk =>
      nth_rw 1 [← head_cons l]
      rw [← Face.head_cons l.reverse, cons_function l.head (l (last k)),
          Face.cons_function]
      simp [cons, Face.cons, reverse]
      ext i : 1
      simp only [comp_apply, id_eq]
      erw [predAbove_succAbove]
      exact congrFun (hk l.head) i

end Degeneracy

namespace OrderHom

noncomputable def rightInv (f : Fin (n + k) →o Fin n) :
    Fin n ↪o Fin (n + k) := (toDegeneracy f).reverse.OrderEmbedding

lemma rightInv_spec_of_surjective (f : Fin (n + k) →o Fin n) (hf : Surjective f):
     f ∘ (rightInv f) = id := by
      dsimp [rightInv]
      convert Degeneracy.reverse.is_rightInv (toDegeneracy f)
      exact (toDegeneracy.function _ hf).symm

end OrderHom

end

section
-- goal: `DT = T'D'`
-- where `D` and `D'` are compositions of faces
-- `T` and `T'` are compositions of degeneracies

-- maybe I need this

variable {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))

lemma eq_or_lt_or_lt (i : Fin (n + 1)) (j : Fin n) :
    (i = j.castSucc ∨ i = j.succ) ∨ i < j.castSucc ∨ j.succ < i := by
  simp [← val_eq_val, lt_iff_val_lt_val]
  rcases lt_or_le i.val j.val with h | h
  . exact Or.inr (Or.inl h)
  . rw [← Nat.lt_succ_iff, Nat.lt_succ_iff_lt_or_eq] at h
    rcases h with h | h
    rw [← Nat.succ_le_iff] at h
    . rcases lt_or_le (j.val + 1) i.val with h' | h'
      . exact Or.inr (Or.inr h')
      . exact Or.inl (Or.inr (le_antisymm h' h))
    . exact Or.inl (Or.inl h.symm)

lemma eq_of_not_lt_of_not_lt {i : Fin (n + 1)} {j : Fin n}
  (h : ¬ i < j.castSucc) (h' : ¬ j.succ < i) :
    i = j.castSucc ∨ i = j.succ := by
  rcases eq_or_lt_or_lt i j with h'' | h''
  . exact h''
  . exfalso
    rcases h'' with h'' | h''
    . apply h h''
    . apply h' h''

def swap_succ_lt_i (h : j.succ < i):
    Fin (n + 1) := i.pred (ne_bot_of_gt h)

def swap_succ_lt_j (h : j.succ < i):
    Fin n := j.castPred ((succ_ne_last_iff _).mp <| ne_last_of_lt h)

def swap_succ_lt (h : j.succ < i) :=
    (swap_succ_lt_i i j h).succAbove ∘ (swap_succ_lt_j i j h).predAbove

def swap_rt_castSucc_i (h : i < j.castSucc) :
    Fin (n + 1) := i.castPred (ne_last_of_lt h)

def swap_rt_castSucc_j (h : i < j.castSucc) :
    Fin n := j.pred ((castSucc_ne_zero_iff _).mp (ne_bot_of_gt h))

def swap_rt_castSucc (h : i < j.castSucc) :=
    (swap_rt_castSucc_i i j h).succAbove ∘ (swap_rt_castSucc_j i j h).predAbove

lemma predAbove_comp_succAbove_eq_castSucc (h : i = j.castSucc) :
    j.predAbove ∘ i.succAbove = id := by
  rw [h]; ext; simp only [comp_apply, predAbove_succAbove, id_eq]

lemma predAbove_comp_succAbove_eq_succ (h : i = j.succ) :
    j.predAbove ∘ i.succAbove = id := by
  rw [h]; ext; simp only [comp_apply, predAbove_succ_succAbove, id_eq]

lemma predAbove_comp_succAbove_eq_castSucc_or_eq_succ (h : i = j.castSucc ∨ i = j.succ) :
    j.predAbove ∘ i.succAbove = id := by
  rcases h with h | h
  . apply predAbove_comp_succAbove_eq_castSucc _ _ h
  . apply predAbove_comp_succAbove_eq_succ _ _ h

lemma predAbove_comp_succAbove_succ_lt (h : j.succ < i) :
    j.predAbove ∘ i.succAbove
      = (swap_succ_lt_i i j h).succAbove ∘ (swap_succ_lt_j i j h).predAbove := by
  ext k : 1
  simp [swap_succ_lt_i, swap_succ_lt_j]
  rcases le_or_lt k j with hkj | hkj
  . rw [succAbove_of_succ_le _ _ ((succ_le_succ_iff.mpr hkj).trans h.le),
        predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr hkj),
        castPred_castSucc,
        predAbove_of_le_castSucc _ _ (by rwa [castSucc_castPred]),
        succAbove_of_succ_le _ _ ?_ , castSucc_castPred]
    rw [le_pred_iff, ← castSucc_lt_iff_succ_le, ← succ_castSucc, castSucc_castPred]
    apply lt_of_le_of_lt (succ_le_succ_iff.mpr hkj) h
  . by_cases hki : i = k.succ
    . simp only [hki]
      rw [succAbove_succ_self, pred_succ, predAbove_castSucc_of_lt _ _ hkj,
          predAbove_of_castSucc_lt _ _ (by rwa [castSucc_castPred]),
          succAbove_pred_self]
      rfl
    . by_cases hki' : k.succ < i
      rw [succAbove_of_succ_le _ _ hki'.le,
          predAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.mpr hkj),
          predAbove_of_castSucc_lt _ _ (by rwa [castSucc_castPred]),
          succAbove_of_succ_le _ _ (le_of_lt (by rwa [lt_pred_iff, succ_pred]))]
      rfl
      . rw [not_lt] at hki'
        have hki := lt_of_le_of_ne hki' hki
        rw [succAbove_of_lt_succ _ _ hki, predAbove_succ_of_le _ _ hkj.le,
            predAbove_of_castSucc_lt _ _ (by rwa [castSucc_castPred]),
            succAbove_of_lt_succ _ _ (by rwa [succ_pred, pred_lt_iff]), succ_pred]

lemma predAbove_comp_succAbove_lt_castSucc (h : i < j.castSucc) :
    j.predAbove ∘ i.succAbove
      = (swap_rt_castSucc_i i j h).succAbove ∘ (swap_rt_castSucc_j i j h).predAbove := by
  ext k : 1
  simp [swap_rt_castSucc_i, swap_rt_castSucc_j]
  rcases lt_or_le k j with hkj | hkj
  . by_cases hki : k.castSucc < i
    rw [succAbove_of_castSucc_lt _ _ hki, predAbove_castSucc_of_le _ _ hkj.le,
        predAbove_of_lt_succ _ _ (by rwa [succ_pred]),
        succAbove_castPred_of_lt _ _ (by rwa [lt_castPred_iff])]
    . rw [not_lt] at hki
      rw [succAbove_of_le_castSucc _ _ hki, predAbove_succ_of_lt _ _ hkj,
          predAbove_of_lt_succ _ _ (by rwa [succ_pred]),
          succAbove_castPred_of_le _ _ (by rwa [castPred_le_iff])]
      rfl
  . rw [succAbove_of_le_castSucc _ _ (h.le.trans (castSucc_le_castSucc_iff.mpr hkj)),
        predAbove_succ_of_le _ _ hkj, predAbove_of_succ_le _ _ (by rwa [succ_pred]),
        succAbove_pred_of_lt _ _ ?_]
    rw [castPred_lt_iff]
    exact lt_of_lt_of_le h (castSucc_le_castSucc_iff.mpr hkj)

lemma predAbove_not_injective (i : Fin n) :
    ¬ i.predAbove.Injective := by
  simp only [Injective, not_forall]
  use i.castSucc, i.succ
  simp only [predAbove_castSucc_self, predAbove_succ_self, exists_const]
  simp only [← val_eq_val, val_succ, coe_castSucc, self_eq_add_right,
             one_ne_zero, not_false_eq_true]

lemma predAbove_comp_succAbove_eq_id_iff :
    j.predAbove ∘ i.succAbove = id ↔ i = j.castSucc ∨ i = j.succ := by
  constructor
  . intro h
    apply eq_of_not_lt_of_not_lt
    . by_contra this
      rw [predAbove_comp_succAbove_lt_castSucc _ _ this] at h
      apply predAbove_not_injective (i.swap_rt_castSucc_j j this)
      apply Injective.of_comp (f := (i.swap_rt_castSucc_i j this).succAbove)
      rw [h]
      apply injective_id
    . by_contra this
      rw [predAbove_comp_succAbove_succ_lt _ _ this] at h
      apply predAbove_not_injective (i.swap_succ_lt_j j this)
      apply Injective.of_comp (f := (i.swap_succ_lt_i j this).succAbove)
      rw [h]
      apply injective_id
  . rintro (h | h)
    apply predAbove_comp_succAbove_eq_castSucc _ _ h
    apply predAbove_comp_succAbove_eq_succ _ _ h

end

section

variable {n : ℕ}

-- `g : Fin m ↪o Fin (m + s)` and surjective `f : Fin (m + s) →o Fin (m + s - k)`
-- composed to `f ∘ g` swap to some `Faces ∘ Degeneracies` with certain terms cancalled
-- `length of degeneracies = m - |range|`
-- `length of faces = m + s - (k + |range|)`

-- `g : Fin (m + s) ↪o Fin (m + s + k)` and surjective `f : Fin (m + s + k) →o Fin (m + k)`
-- composed to `f ∘ g` swap to some `Faces ∘ Degeneracies` with certain terms cancalled
-- `length of degeneracies = m + s - |range|`
-- `length of faces = m + k - |range|`

def range_card (f : Fin n → Fin m) := (range f).toFinset.card

-- do the easy case first
-- `g : Fin (m + 1) ↪o Fin (m + 1 + k)` and surjective `f : Fin (m + 1 + k) →o Fin (m + k)`

def swap_l (r : Fin (n + 2)) (l : Fin (n + 1)) :
    Option (Fin (n + 1)) :=
  if h : r < l.castSucc then swap_rt_castSucc_i r l h
    else (if h' : l.succ < r then swap_succ_lt_i r l h'
      else none)

def swap_l' : {n : ℕ} → (r : Fin (n + 1)) → (l : Fin n) →
    Option (Fin n)
  | 0, _, _ => none
  | _ + 1, r, l => if h : r < l.castSucc then swap_rt_castSucc_i r l h
    else (if h' : l.succ < r then swap_succ_lt_i r l h'
      else none)

def swap_r (r : Fin (n + 2)) (l : Fin (n + 1)) :
    Option (Fin n) :=
  if h : r < l.castSucc then swap_rt_castSucc_j r l h
    else (if h' : l.succ < r then swap_succ_lt_j r l h'
      else none)

def _root_.Option.succAbove' {n} := Option.map (@succAbove n)

def _root_.Option.predAbove' {n} := Option.map (@predAbove n)

def opt_comp : Option (Fin n → Fin m) → Option (Fin m → Fin n) → (Fin m → Fin m)
  | none, _ => id
  | _, none => id
  | some f, some g => f ∘ g

infixr:90 " ⊚ "  => opt_comp

def Option.comp.{u} {α β δ : Type u} :
    (f : Option (β → δ)) → (g : Option (α → β)) → (Option (α → δ))
  | none, _ => none
  | _, none => none
  | some f, some g => some (f ∘ g)

infixr:90 " ● "  => Option.comp

lemma Option.comp.assoc.{u} {α β φ δ : Type u} (f : Option (φ → δ)) (g : Option (β → φ))
  (h : Option (α → β)) :
    (f ● g) ● h = f ● g ● h := by
  cases f
  . simp only [comp]
  . cases g
    . simp only [comp]
    . cases h
      . simp only [comp]
      . simp only [comp, Option.some.injEq]; apply Function.comp_assoc

lemma Option.comp_eq_none_iff {f : Option (φ → δ)} {g : Option (β → φ)} :
    f ● g = none ↔ f = none ∨ g = none := by
  cases g
  cases f
  <;> . simp [comp]
  cases f
  <;> . simp [comp]

lemma Option.none_of_some_comp_eq_none {f : φ → δ} {g : Option (β → φ)} :
    some f ● g = none → g = none := by
  cases g
  . simp only [implies_true]
  . simp only [comp, reduceCtorEq, imp_self]

lemma Option.comp_none {f : Option (φ → δ)}:
    f ● none (α := β → φ) = none := by
  cases f
  <;> simp [Option.comp]

lemma Option.none_comp {f : Option (β → φ)}:
    none (α := φ → δ) ● f = none := by
  cases f
  <;> simp [Option.comp]

lemma Option.some_comp_some {f : φ → δ} {g : β → φ}:
    some f ● some g = some (f ∘ g) := rfl

def swap_l_eq_none_iff_not_and_not {r : Fin (n + 2)} {l : Fin (n + 1)} :
    swap_l r l = none ↔ ¬ r < l.castSucc ∧ ¬ l.succ < r := by
  dsimp [swap_l]
  split_ifs with h₁ h₂
  . simp [h₁]
  . simp [h₂]
  . simp only [true_iff]
    exact ⟨h₁, h₂⟩

lemma predAbove_comp_succAbove (i : Fin (n + 2)) (j : Fin (n + 1)) :
    j.predAbove ∘ i.succAbove = (swap_l i j).succAbove' ⊚ (swap_r i j).predAbove' := by
  dsimp [swap_l, swap_r]
  split_ifs with h₁ h₂
  . simp [Option.succAbove', Option.predAbove', opt_comp]
    apply predAbove_comp_succAbove_lt_castSucc
  . simp [Option.succAbove', Option.predAbove', opt_comp]
    apply predAbove_comp_succAbove_succ_lt
  . simp [Option.succAbove', Option.predAbove', opt_comp]
    rcases eq_of_not_lt_of_not_lt h₁ h₂ with h | h
    .  apply predAbove_comp_succAbove_eq_castSucc _ _ h
    .  apply predAbove_comp_succAbove_eq_succ _ _ h

def OptFace (n k : ℕ) := (i : Fin k) → Option (Fin (n + ↑i + 1))

namespace OptFace

-- this is weird (dependent type) but it's working
def mk0 (s : Option (Fin (n + 1))) : OptFace n 1 := fun _ ↦ s

lemma mk0_def : OptFace.mk0 s 0 = s := by
  simp only [val_zero, Nat.add_zero, mk0, cast_val_eq_self, Option.pure_def,
             Option.bind_eq_bind, Option.bind_some]

def head {n k : ℕ} : OptFace n (k + 1) → OptFace n k
  | f => fun i ↦ f i.castSucc

def tail {n k : ℕ} : OptFace n (k + 1) → OptFace (n + 1) k
  | f => fun i ↦ f i.succ

def consd : {k : ℕ} → OptFace (n + 1) k → Option (Fin (n + 1)) → OptFace n (k + 1)
  | _, _, j, 0 => j
  | _, l, _, ⟨k + 1, hk⟩ => by
    have eq : n + 1 + k + 1 = n + (k + 1) + 1 := by rw [Nat.add_comm k 1, ← Nat.add_assoc]
    exact Option.map eq.FinTransfer (l ⟨k, by rwa [← Nat.succ_lt_succ_iff]⟩)

lemma consd_succ {l : OptFace (n + 1) k} {c : Option (Fin (n + 1))} (i : Fin k)
  {eq : n + 1 + i.val + 1 = n + i.succ.val + 1} :
    l.consd c i.succ = Option.map eq.FinTransfer (l i) := rfl

lemma consd_head {l : OptFace (n + 1) (k + 1)} {c : Option (Fin (n + 1))} :
    (l.consd c).head = l.head.consd c := by
  funext i
  simp [head]
  cases i with
  | mk i _ =>
      cases i
      <;> rfl

def cons {n k: ℕ} (l : OptFace n k) : (c : Option (Fin (n + k + 1))) →
    OptFace n (k + 1)
  | some c, i => if h : i ≠ (last k) then l (i.castPred h) else some ⟨c.val, by
              convert c.isLt
              rwa [ne_eq, not_not, ← Fin.val_eq_val, val_last] at h⟩
  | none, i => if h : i ≠ (last k) then l (i.castPred h) else none

def cons' {n k m: ℕ} (l : OptFace n k) (eq : m = n + k + 1): (c : Option (Fin m)) →
    OptFace n (k + 1)
  | some c, i => if h : i ≠ (last k) then l (i.castPred h) else some ⟨c.val, by
              convert c.isLt;
              rw [ne_eq, not_not, ← Fin.val_eq_val, val_last] at h
              rw [h, eq]⟩
  | none, i => if h : i ≠ (last k) then l (i.castPred h) else none

def function : {k : ℕ} → (l : OptFace n k) → (Option (Fin n → Fin (n + k)))
  | 0, _ => some id
  | _ + 1, l => (l (last _)).succAbove'● l.head.function

def tailFunction : {k : ℕ} → (l : OptFace n (k + 1)) → (Option (Fin (n + 1) → Fin (n + k + 1)))
  | 0, _ => some id
  | _ + 1, l => (l (last _)).succAbove'● l.head.tailFunction

-- Q : you know the question
lemma cons_head {n k : ℕ} (l : OptFace n k) (c : Option (Fin (n + k + 1))):
    (l.cons c).head = l := by
  cases c
  . funext i
    simp only [head, cons]
    split_ifs with h
    . rfl
    . apply False.elim <| h (Fin.castSucc_lt_last _).ne
  . funext i
    simp only [head, cons]
    split_ifs with h
    . rfl
    . apply False.elim <| h (Fin.castSucc_lt_last _).ne

lemma cons_function {n k : ℕ} (l : OptFace n k) (c : Option (Fin (n + k + 1))):
    (l.cons c).function = ((l.cons c) (last _)).succAbove' ● l.function := by
  dsimp [function]; rw [cons_head]

lemma consd_tailFunction {n k : ℕ} (l : OptFace (n + 1) (k + 1)) (c : Option (Fin (n + 1)))
{eq : n + 1 + k + 1 = n + (k + 1) + 1}:
    (l.consd c).tailFunction = (some eq.FinTransfer) ● l.function := by
  induction k with
  | zero =>
    simp [tailFunction, function]
    have : l.consd c (last (0 + 1)) = Option.map eq.FinTransfer (l (last 0)) := rfl
    rw [this]
    cases l (last 0)
    . simp [Option.succAbove', Option.none_comp, Option.comp_none]
    . simp [Option.succAbove', Option.comp]
      ext i; simp [FinTransfer.val]; rfl
  | succ k hk =>
      have aa := hk l.head (eq := by rw [Nat.add_comm k 1, ← Nat.add_assoc])
      have : (l.consd c).tailFunction =
        ((l.consd c) (last _)).succAbove'● (l.consd c).head.tailFunction := rfl
      rw [this, consd_head, aa]
      have : l.function = (l (last _)).succAbove'● l.head.function := rfl
      conv => rhs; rw [this, ← Option.comp.assoc]
      rw [← Option.comp.assoc]
      congr 1
      have : l.consd c (last (k + 1 + 1))
        = Option.map eq.FinTransfer (l (last (k + 1))) := rfl
      rw [this]
      cases l (last (k + 1)) with
      | none => simp [Option.succAbove', Option.none_comp, Option.comp_none]
      | some j =>
          simp [Option.succAbove', Option.comp]
          ext i; simp [FinTransfer.val]
          rw [FinTransfer.comm_succAbove' (h' := by linarith)]
          rfl

def transport (e₁ : n = n') (e₂ : k = k') (d : OptFace n k) :
    OptFace n' k'
  | i => Option.map (Eq.FinTransfer (by rw [e₁]; rfl)) (d (e₂.symm.FinTransfer i))

end OptFace

def Face.toOpt (l : Face n k) :
    OptFace n k := fun i ↦ some (l i)

namespace Face.toOpt

lemma apply (l : Face n k) (i : Fin k) :
    l.toOpt i = some (l i) := rfl

lemma cons (l : Face n k) (c : Fin (n + k + 1)) :
    (l.cons c).toOpt = l.toOpt.cons (some c) := by
  funext i
  simp [OptFace.cons, Face.toOpt, Face.cons]
  split_ifs
  <;> rfl

lemma head (l : Face n (k + 1)) :
    l.toOpt.head = l.head.toOpt := rfl

lemma function (l : Face n k) :
    l.toOpt.function = some (l.function) := by
  induction k with
  | zero => simp [OptFace.function, Face.function]
  | succ k hk =>
      rw [← Face.head_cons l, Face.cons_function, Face.toOpt.cons]
      simp [OptFace.function, Face.function, OptFace.cons, Face.cons, ← Option.some_comp_some]
      rw [← hk l.head]
      congr
      rw [← Face.toOpt.cons, Face.head_cons, Face.toOpt.head]

end Face.toOpt

def swap₀ : {k : ℕ} → Option (Fin (n + 1 + k)) → Face (n + 1) (k + 1) → Option (Fin n)
  | _, none, _ => none
  | 0, some i, l => swap_r (l (last _)) i
  | _ + 1 , some i, l => swap₀ (swap_r (l (last _)) i) l.head

def swap₀' : {k : ℕ} → Option (Fin (n + 1 + k)) → Face (n + 1) (k + 1) →
    OptFace n (k + 1)
  | _, none, _ => fun i ↦ none
  | 0, some j, l => OptFace.mk0 (swap_l (l (last _)) j)
  | k + 1, some j, l => if swap_l (l (last _)) j = none
      then l.toOpt.head.consd none
      else (swap₀' (swap_r (l (last _)) j) l.head).cons' (m := n + 1 + k + 1)
     (by rw [add_comm k, ← add_assoc]) (swap_l (l (last _)) j)

def function_comp₀ : {k : ℕ} → Option (Fin n) → OptFace n k →
    Option (Fin (n + 1) → Fin (n + k))
  | 0, j, _ => j.predAbove'
  | _ + 1, j, l => l.function ● j.predAbove'

-- maybe add k = 0 too???
def function_comp_test (i : Option (Fin n)) (l : OptFace n (k + 1)) :
    Option (Fin (n + 1) → Fin (n + (k + 1))) :=
  if function_comp₀ i l = none then l.tailFunction
    else function_comp₀ i l

lemma function_comp_test_some (i : Option (Fin n)) (l : OptFace n (k + 1))
  {f : Fin (n + 1) → Fin (n + (k + 1))} (h : function_comp₀ i l = some f):
    function_comp_test i l = some f := by
  dsimp [function_comp_test]
  split_ifs with h'
  . simp [h] at h'
  . exact h

lemma function_comp_test_none (i : Option (Fin n)) (l : OptFace n (k + 1))
  (h : function_comp₀ i l = none):
    function_comp_test i l = l.tailFunction := by
  simp only [function_comp_test, if_pos h]

open OptFace in
lemma function_comp₀_cons (i : Option (Fin n)) (l : OptFace n (k + 1))
  (j : Option (Fin (n + k + 1 + 1))) :
    function_comp₀ i (l.cons j) = j.succAbove'● (function_comp₀ (n := n) i l) := by
  dsimp [function_comp₀]
  rw [← Option.comp.assoc, cons_function]
  congr
  cases j
  <;> simp [OptFace.cons]

open OptFace in
lemma function_comp_test_cons (i : Option (Fin n)) (l : OptFace n (k + 1))
  (j : Option (Fin (n + k + 1 + 1))) :
    function_comp_test i (l.cons j) = j.succAbove'● (function_comp_test (n := n) i l) := by
    dsimp [function_comp_test]
    split_ifs with h₁ h₂ h₃
    . simp [OptFace.tailFunction]
      cases j
      . simp [OptFace.cons, Option.succAbove', Option.none_comp]
      . simp [OptFace.cons, Option.succAbove', cons_head]
    . cases j
      . simp [OptFace.tailFunction, OptFace.cons, Option.succAbove', Option.comp]
      . simp [function_comp₀, cons_function, OptFace.cons, Option.comp.assoc] at h₁
        apply False.elim <| h₂ (Option.none_of_some_comp_eq_none h₁)
    . apply False.elim <| h₁ (by simp [function_comp₀_cons, h₃, Option.comp_none])
    . apply function_comp₀_cons

lemma function_comp_test_cons' (i : Option (Fin n)) (l : OptFace n (k + 1))
  (eq : m = n + k + 1 + 1) (j : Option (Fin m)) :
    function_comp_test i (l.cons' eq j) =
  (Option.map eq.FinTransfer j).succAbove'● (function_comp_test (n := n) i l) := by
  cases eq
  convert function_comp_test_cons i l j
  . ext i₀ -- make it a lemma
    cases i₀
    <;> rfl
  . cases j
    <;> rfl

lemma haha (l : Face (n + 1) 1) (j : Fin (n + 1)) :
    function_comp_test (swap₀ (some j) l) (swap₀' (some j) l) = j.predAbove ∘ l.function := by
  simp [Face.function]
  dsimp [swap₀, swap₀', swap_r, swap_l]
  split_ifs with h₁ h₂
  . rw [function_comp_test_some _ _]
    simp [function_comp_test, function_comp₀,
          OptFace.function, Option.succAbove', Option.predAbove']
    erw [OptFace.mk0_def]
    simp [Option.comp]
    apply (predAbove_comp_succAbove_lt_castSucc _ _ _).symm
  . rw [function_comp_test_some _ _]
    simp [function_comp_test, function_comp₀,
          OptFace.function, Option.succAbove', Option.predAbove']
    erw [OptFace.mk0_def]
    simp [Option.comp]
    apply (predAbove_comp_succAbove_succ_lt _ _ _).symm
  rw [function_comp_test_none _ _]
  dsimp [OptFace.tailFunction]
  rcases eq_of_not_lt_of_not_lt h₁ h₂ with h | h
  . rw [predAbove_comp_succAbove_eq_castSucc _ _ h]
  . rw [predAbove_comp_succAbove_eq_succ _ _ h]
  . rfl

example : have eq : n + 1 + k = n + k + 1 := by rw [add_assoc, add_comm 1]; rfl
  function_comp_test (swap₀ (some j) l) (swap₀' (some j) l) =
    some (eq.FinTransfer ∘ (j.predAbove ∘ l.function)) := by
  induction k with
  | zero => apply haha
  | succ k hk =>
      dsimp [swap₀']
      split_ifs with h
      . rw [swap_l_eq_none_iff_not_and_not] at h
        simp [swap₀, swap_r, dif_neg h.2, dif_neg h.1]
        rw [function_comp_test_none]
        . rw [OptFace.consd_tailFunction (eq := by rw [add_comm k 1, ← add_assoc])]
          rw [← Option.some_comp_some, ← Option.some_comp_some]
          rw [Face.toOpt.head, Face.toOpt.function]
          conv => rhs; rw [← Face.head_cons l,
                           Face.cons_function, ← Option.some_comp_some, Face.head_cons]
          congr
          rw [← Function.comp_assoc,
              predAbove_comp_succAbove_eq_castSucc_or_eq_succ _ _ (eq_of_not_lt_of_not_lt h.1 h.2)]
          rfl
        . simp [function_comp₀, Option.predAbove', Option.comp_none]
      . dsimp [swap₀, swap₀', swap_r, swap_l]
        split_ifs with h₁ h₂
        . rw [function_comp_test_cons', hk]
          simp [Option.succAbove', Option.comp]
          conv =>
            rhs
            rw [← Face.head_cons l, Face.cons_function,
                ← Function.comp_assoc, ← Function.comp_assoc]
            simp [Face.cons]
          rw [← Function.comp_assoc _ _ l.head.function,
              ← Function.comp_assoc]
          congr! 1
          rw [Function.comp_assoc]
          ext i
          simp [FinTransfer.val]
          rw [FinTransfer.comm_succAbove'
            (h' := by rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc])]
          simp [FinTransfer.val]
          congr
          rw [← Function.comp_apply (f := j.predAbove),
              predAbove_comp_succAbove_lt_castSucc _ _ h₁]
          rfl
        . rw [function_comp_test_cons', hk]
          simp [Option.succAbove', Option.comp]
          conv =>
            rhs
            rw [← Face.head_cons l, Face.cons_function,
                ← Function.comp_assoc, ← Function.comp_assoc]
            simp [Face.cons]
          rw [← Function.comp_assoc _ _ l.head.function,
              ← Function.comp_assoc]
          congr! 1
          rw [Function.comp_assoc]
          ext i
          simp [FinTransfer.val]
          rw [FinTransfer.comm_succAbove'
            (h' := by rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc])]
          simp [FinTransfer.val]
          congr
          rw [← Function.comp_apply (f := j.predAbove),
              predAbove_comp_succAbove_succ_lt _ _ h₂]
          rfl
        . simp only [swap_l_eq_none_iff_not_and_not, not_and_iff_or_not_not] at h
          rcases h with h | h
          . apply False.elim (h h₁)
          . apply False.elim (h h₂)

-- instead of `tailfuction`, define a function sends `dddnnn` to function of `ddd`.


-- now we need degeneracy

namespace OptDegeneracy

end OptDegeneracy

def OptDegeneracy (n k : ℕ) := (i : Fin k) → Option (Fin (n + ↑i))

namespace OptDegeneracy

def mk0 (s : Option (Fin n)) : OptDegeneracy n 1 :=
    fun i ↦ Option.map (Eq.FinTransfer (by rw [coe_fin_one, add_zero])) s

lemma mk0_def {s : Option (Fin n)} {k : Fin 1}:
    OptDegeneracy.mk0 s k = Option.map (Eq.FinTransfer (by rw [coe_fin_one, add_zero])) s := by
  simp only [val_zero, Nat.add_zero, mk0, cast_val_eq_self, Option.pure_def,
             Option.bind_eq_bind, Option.bind_some]

def head {n k : ℕ} : OptDegeneracy n (k + 1) → OptDegeneracy n k
  | f => fun i ↦ f i.castSucc

def tail {n k : ℕ} : OptDegeneracy n (k + 1) → OptDegeneracy (n + 1) k
  | f => fun i ↦ by
      apply Option.map (Eq.FinTransfer _) (f i.succ)
      rw [val_succ, Nat.add_comm i.val, ← Nat.add_assoc]

def function : {k n : ℕ} → (l : OptDegeneracy n k) → Option (Fin (n + k) → Fin n)
  | 0, _, _ => some id
  | _ + 1, _, l => (l.head).function ● (l (last _)).predAbove'

def cons {n k: ℕ} (l : OptDegeneracy n k) : (c : Option (Fin (n + k))) →
    OptDegeneracy n (k + 1)
  | some c, i => if h : i ≠ (last k) then l (i.castPred h) else some ⟨c.val, by
              convert c.isLt
              rwa [ne_eq, not_not, ← Fin.val_eq_val, val_last] at h⟩
  | none, i => if h : i ≠ (last k) then l (i.castPred h) else none

def consd : {k : ℕ} → OptDegeneracy (n + 1) k → Option (Fin n) → OptDegeneracy n (k + 1)
  | _, _, j, 0 => j
  | _, l, _, ⟨k + 1, hk⟩ => by
    have eq : n + 1 + k = n + (k + 1) := by rw [Nat.add_comm k 1, ← Nat.add_assoc]
    exact Option.map eq.FinTransfer (l ⟨k, by rwa [← Nat.succ_lt_succ_iff]⟩)

lemma cons_head {n k : ℕ} (l : OptDegeneracy n k) (c : Fin (n + k)):
    (l.cons c).head = l := by
  funext i
  simp only [head, cons]
  split_ifs with h
  . rfl
  . apply False.elim <| h (Fin.castSucc_lt_last _).ne

lemma head_cons {n k : ℕ} (l : OptDegeneracy n (k + 1)):
    l.head.cons (l (last k)) = l := by
  funext i
  cases h : (l (last k))
  simp only [head, cons]
  split_ifs with h'
  . rfl
  . simp only [ne_eq, not_not] at h'
    rw [h', h]
  simp only [head, cons]
  split_ifs with h'
  . rfl
  . simp only [ne_eq, not_not] at h'
    convert h.symm

def transport (e₁ : n = n') (e₂ : k = k') (d : OptDegeneracy n k) :
    OptDegeneracy n' k'
  | i => Option.map (Eq.FinTransfer (by rw [e₁]; rfl)) (d (e₂.symm.FinTransfer i))

end OptDegeneracy

def Degeneracy.toOpt (l : Degeneracy n k) :
    OptDegeneracy n k := fun i ↦ some (l i)

namespace Degeneracy.toOpt

lemma apply (l : Degeneracy n k) (i : Fin k) :
    l.toOpt i = some (l i) := rfl

lemma cons (l : Degeneracy n k) (c : Fin (n + k)) :
    (l.cons c).toOpt = l.toOpt.cons (some c) := by
  funext i
  simp [OptDegeneracy.cons, Degeneracy.toOpt, Degeneracy.cons]
  split_ifs
  <;> rfl

lemma head (l : Degeneracy n (k + 1)) :
    l.toOpt.head = l.head.toOpt := rfl

lemma function (l : Degeneracy n k) :
    l.toOpt.function = some (l.function) := by
  induction k with
  | zero => simp [OptDegeneracy.function, Degeneracy.function]
  | succ k hk =>
      rw [← Degeneracy.head_cons l, Degeneracy.cons_function, Degeneracy.toOpt.cons]
      simp [OptFace.function, Face.function, OptFace.cons, Face.cons, ← Option.some_comp_some]
      rw [← hk l.head, ← Degeneracy.toOpt.cons, Degeneracy.head_cons]
      rfl

end Degeneracy.toOpt

def swap_l_opt : (r : Option (Fin (n + 2))) → (l : Option (Fin (n + 1))) →
    Option (Fin (n + 1))
  | none, _ => none
  | _, none => none
  | some r, some l => swap_l r l

/--
  swap `l r` to `(swap_l r l) (swap_r r l)`
-/
def swap_r_opt : (r : Option (Fin (n + 2))) → (l : Option (Fin (n + 1))) →
    Option (Fin n)
  | none, _  => none
  | _, none => none
  | some r, some l => swap_r r l

def swap0 : {k : ℕ} → Option (Fin (n + 1 + k)) → OptFace (n + 1) (k + 1) → Option (Fin n)
  | _, none, _ => none
  | 0, some i, l => swap_r_opt (l (last _)) (some i)
  | _ + 1 , some i, l => swap0 (swap_r_opt (l (last _)) (some i)) l.head

def swap0' : {k : ℕ} → Option (Fin (n + 1 + k)) → OptFace (n + 1) (k + 1) →
    OptFace n (k + 1)
  | _, none, _ => fun i ↦ none
  | 0, some j, l => OptFace.mk0 (swap_l_opt (l (last _)) (some j))
  | k + 1, some j, l => if swap_l_opt (l (last _)) (some j) = none
      then l.head.consd none
      else (swap0' (swap_r_opt (l (last _)) (some j)) l.head).cons' (m := n + 1 + k + 1)
     (by rw [add_comm k, ← add_assoc]) (swap_l_opt (l (last _)) (some j))

def swapd : {n k m: ℕ} → OptDegeneracy (n + k) m → OptFace (n + m) k
  → OptDegeneracy n m
    | n, _, 0, _, _ => fun i ↦ i.elim0
    | _, 0, _, s, _ => s
    | n, k + 1, m + 1, s, d => by
        have eq : n + k + 1 + (last m).val = n + m + 1 + k:= by
          rw [val_last, Nat.add_assoc n, Nat.add_comm k, Nat.add_assoc,
              Nat.add_comm _ m, ← Nat.add_assoc, ← Nat.add_assoc]
        have eq₁ : n + (k + 1) = n + 1 + k := by
          rw [Nat.add_comm k, Nat.add_assoc]
        have eq₂ : n + (m + 1) = n + 1 + m := by
          rw [Nat.add_comm m, Nat.add_assoc]

        exact if d 0 = none then
            (swapd (s.head.transport eq₁ (Eq.refl _))
              (((swap0' (Option.map eq.FinTransfer (s (last _))) d)).tail.transport eq₂ (Eq.refl _))).consd none
          else
            (swapd s.head (swap0' (Option.map eq.FinTransfer (s (last _))) d)).cons
              (swap0 (Option.map eq.FinTransfer (s (last _))) d)

def swapf : {n k m: ℕ} → OptDegeneracy (n + k) m → OptFace (n + m) k
  → OptFace n k
    | _, _, 0, _, d => d
    | _, 0, _, _, _ => fun i ↦ i.elim0
    | n, k + 1, m + 1, s, d => by
        have eq : n + k + 1 + (last m).val = n + m + 1 + k:= by
          rw [val_last, Nat.add_assoc n, Nat.add_comm k, Nat.add_assoc,
              Nat.add_comm _ m, ← Nat.add_assoc, ← Nat.add_assoc]
        exact swapf s.head (swap0' (k := k) (Option.map eq.FinTransfer $ s (last _)) d)

def concatfunc : {n k l : ℕ} → (d : OptFace n k) → (s : OptDegeneracy n l) →
    Option (Fin (n + l) → Fin (n + k))
  | _, 0, _, _, s => s.function
  | _, _ + 1, 0, d, _ => d.function
  | _, k + 1, l + 1, d, s =>
    if d.function ● s.function = none then
      (some (Eq.FinTransfer (by rw [Nat.add_comm k 1, Nat.add_assoc]))
        ● d.tail.function ● s.tail.function)
        ● (some (Eq.FinTransfer (by rw [Nat.add_comm l 1, Nat.add_assoc])))
    else d.function ● s.function

lemma concatfunc_OptDegeneracy_zero (d : OptFace n k) (s : OptDegeneracy n 0) :
    concatfunc d s = d.function := by
  cases k
  <;> rfl

lemma main1 (d : Face (n + 1) 1) (s : Degeneracy (n + 1) 1) :
  (swapf s.toOpt d.toOpt).function ● (swapd s.toOpt d.toOpt).function = none ↔
    (s (last 0)).predAbove ∘ (d (last 0)).succAbove = id := by
  simp [swapf, swapd, swap0', swap0]
  simp [OptDegeneracy.function, OptFace.function, Face.toOpt, Degeneracy.toOpt]
  simp [swap_r_opt, swap_l_opt, swap_l, swap_r]
  split_ifs with h₁ h₂ -- how to apply <;> to multiple tactics at the same time???
  . erw [OptFace.mk0_def]
    simp [OptDegeneracy.cons, Option.succAbove', Option.predAbove', Option.comp]
    rw [predAbove_comp_succAbove_eq_id_iff, not_or]
    exact ⟨h₁.ne, (h₁.trans (castSucc_lt_succ _)).ne⟩
  . erw [OptFace.mk0_def]
    simp [OptDegeneracy.cons, Option.succAbove', Option.predAbove', Option.comp]
    rw [predAbove_comp_succAbove_eq_id_iff, not_or]
    exact ⟨((castSucc_lt_succ _).trans h₂).ne.symm, h₂.ne.symm⟩
  . erw [OptFace.mk0_def]
    simp [OptDegeneracy.cons, Option.succAbove', Option.predAbove', Option.comp]
    rw [predAbove_comp_succAbove_eq_id_iff]
    apply eq_of_not_lt_of_not_lt h₁ h₂


example (d : Face (n + 1) 1) (s : Degeneracy (n + 1) 1) :
    (some s.function) ● (some d.function) =
      concatfunc (swapf s.toOpt d.toOpt) (swapd s.toOpt d.toOpt) := by
  simp [concatfunc]
  split_ifs with h₁
  . simp [swapd, swapf]
    split_ifs with h₂
    . simp [Face.toOpt] at h₂
    . simp [OptDegeneracy.function, OptFace.function,
            Degeneracy.function, Face.function,
            Option.predAbove', Option.succAbove',
            Option.comp]
      rw [(main1 _ _).mp h₁]; rfl
  . simp [swapd, swapf]
    split_ifs with h₂
    . simp [Face.toOpt] at h₂
    . simp [OptDegeneracy.function, OptFace.function]
      simp [swap0', swap0]
      erw [OptFace.mk0_def]
      simp [Face.toOpt, swap_l_opt, swap_r_opt, swap_l, swap_r]
      split_ifs with h₃ h₄
      . simp [Face.function, Degeneracy.function]
        simp [Option.succAbove', OptDegeneracy.cons, Option.predAbove']
        simp [Option.comp]
        apply predAbove_comp_succAbove_lt_castSucc _ _ h₃
      . simp [Face.function, Degeneracy.function]
        simp [Option.succAbove', OptDegeneracy.cons, Option.predAbove']
        simp [Option.comp]
        apply predAbove_comp_succAbove_succ_lt _ _ h₄
      . rw [main1] at h₁
        apply False.elim (h₁ _)
        rcases eq_of_not_lt_of_not_lt h₃ h₄ with h₄ | h₄
        . apply predAbove_comp_succAbove_eq_castSucc _ _ h₄
        . apply predAbove_comp_succAbove_eq_succ _ _ h₄

lemma step1 (d : Face (n + 1) (k + 1)) {eq : (n + 1) + k = m} {eq' : (n + 1) + (k + 1) = m + 1}
  {eq'' : n + (k + 1) = m} (i : Fin m) :
    some (i.predAbove ∘ eq'.FinTransfer ∘ d.function) =
        (some eq''.FinTransfer) ● concatfunc (swap0' (some (eq.symm.FinTransfer i)) d.toOpt)
          (OptDegeneracy.mk0 <| swap0 (some (eq.symm.FinTransfer i)) d.toOpt) := by
    sorry

lemma step2_aux_deg (s : OptDegeneracy n l) :
    s.function = none ↔ ∃ i, s i = none := by
  induction l with
  | zero => simp [OptDegeneracy.function]
  | succ l hl =>
      simp [OptDegeneracy.function, Option.predAbove']
      rw [Option.comp_eq_none_iff, hl]
      cases h : s (last l)
      . simp; exact ⟨last l, h⟩
      . simp
        constructor
        . exact fun ⟨i, hi⟩ ↦ ⟨i.castSucc, hi⟩
        . intro ⟨i, hi⟩
          use i.castPred (by contrapose! h; rw [h] at hi; rw [hi]; simp)
          exact hi

lemma step2_aux_face (s : OptFace n l) :
    s.function = none ↔ ∃ i, s i = none := by
  induction l with
  | zero => simp [OptFace.function]
  | succ l hl =>
      simp [OptFace.function, Option.succAbove']
      rw [Option.comp_eq_none_iff, hl]
      cases h : s (last l)
      . simp; exact ⟨last l, h⟩
      . simp
        constructor
        . exact fun ⟨i, hi⟩ ↦ ⟨i.castSucc, hi⟩
        . intro ⟨i, hi⟩
          use i.castPred (by contrapose! h; rw [h] at hi; rw [hi]; simp)
          exact hi

lemma step2_aux {d : OptFace n k} {s : OptDegeneracy n l}
  (h : ¬ d.function ● s.function = none) {k' l' : ℕ}
  {d' : OptFace n k'} {s' : OptDegeneracy n l'} (hk : k' ≤ k) (hl : l' ≤ l)
  (hd : ∀ i, d' i = d (i.castLE hk)) (hs : ∀ i, s' i = s (i.castLE hl)) :
    ¬ d'.function ● s'.function = none := by
  contrapose! h
  rw [Option.comp_eq_none_iff, step2_aux_deg, step2_aux_face] at h ⊢
  rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
  left; use i.castLE hk; rwa [← hd]
  right; use i.castLE hl; rwa [← hs]

example (d : Face (n + m) k) (s : Degeneracy (n + k) m) :
    have eq : n + m + k = n + k + m := by rw [Nat.add_assoc, Nat.add_comm m, ← Nat.add_assoc]
    some (s.function ∘ eq.FinTransfer ∘ d.function)
        = concatfunc (swapf s.toOpt d.toOpt) (swapd s.toOpt d.toOpt) := by
  induction k generalizing m n with
  | zero =>
      cases m with
      | zero =>
          simp [Face.function, Degeneracy.function, concatfunc, swapd, OptDegeneracy.function]
          rfl
      | succ m =>
          simp [swapf, swapd, concatfunc, Face.function, Degeneracy.toOpt.function]
          rfl
  | succ k hk =>
      cases m with
      | zero =>
          simp [Face.function, Degeneracy.function, concatfunc, swapd, OptDegeneracy.function,
                swapf]
          nth_rw 3 [← Face.head_cons d]
          simp [Face.toOpt.cons, OptFace.function, OptFace.cons, OptFace.cons_head,
                Option.succAbove']
          specialize hk d.head (fun i ↦ i.elim0)
          simp [Face.function, Degeneracy.function, swapf, swapd,
                concatfunc_OptDegeneracy_zero] at hk
          simp [← hk, Option.comp]
          rfl
      | succ m =>
          have eq₁ {n m : ℕ} : n + (m + 1) = n + 1 + m := by rw [add_comm m, add_assoc]
          have hk := @hk (n + 1) m (d.head.transport eq₁ (Eq.refl _))
            (s.head.transport eq₁ (Eq.refl _))
          simp [Face.transport_function, Degeneracy.transport_function] at hk
          -- shoule have a lemma saying if h₁ hold then in some step we have a composition id
          simp [concatfunc]
          split_ifs with h₁
          . simp [swapd, swapf]
            split_ifs with h₂
            . simp [Face.toOpt] at h₂
            . simp [Degeneracy.toOpt]
              sorry
          . simp [swapd, swapf]
            split_ifs with h₂
            . simp [Face.toOpt] at h₂
            . simp [Degeneracy.function]
              rw [Function.comp_assoc, ← Option.some_comp_some]
              -- step 1. swap `(s last)` with `d`
              erw [step1
                  (eq := by erw [add_assoc, add_comm 1, add_assoc n, add_comm m, ← add_assoc])
                  (eq'' := by erw [add_assoc n, add_comm m, ← add_assoc])]
              -- step 2. unfold concat at lhs
              sorry

              -- step 3.

































end
