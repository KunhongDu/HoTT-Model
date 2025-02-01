import Mathlib.Data.List.Indexes
universe u

namespace PureTypeSystem

structure Specification where
  sort : Type u
  ax : sort → sort → Prop
  rel : sort → sort → sort → Prop

inductive PTerm (S : Specification)
| var : ℕ → PTerm S
| sort : S.sort → PTerm S
| app : PTerm S → PTerm S → PTerm S
| pi : PTerm S → PTerm S → PTerm S
| abs : PTerm S → PTerm S → PTerm S

open PTerm List

section LiftSubst

notation "#"n => var n
notation "!"M => sort M
infixl:100 " ⬝ " => app
prefix:max "Π." => pi
prefix:max "λ." => abs

variable {S : Specification}

@[simp]
def lift (i c : ℕ) : PTerm S → PTerm S
| #n => if n < c then #n else #(n + i)
| sort M => !M
| app N M => (lift i c N) ⬝ (lift i c M)
| pi N M => Π.(lift i c N) (lift i (c + 1) M)
| abs N M => λ.(lift i c N) (lift i (c + 1) M)

notation N" ↑ "i" # "c => lift i c N

notation N" ↑ "i => lift i 0 N

variable {M N : PTerm S}

lemma lift_eq_var_lift {i c k : ℕ} :
  ∀ {M : PTerm S}, (M ↑ i # c) = ((#k) ↑ i # c) → M = #k
| .var l, h => by
  simp at h
  split_ifs at h with h₀ h₁ h₁
  . assumption
  . simp at h; simp [h] at h₀
    simpa using not_lt_of_le (Nat.le_add_right k i) $ lt_of_lt_of_le h₀ (le_of_not_lt h₁)
  . simp at h; simp [← h] at h₁
    simpa using not_lt_of_le (Nat.le_add_right l i) $  lt_of_lt_of_le h₁ (le_of_not_lt h₀)
  . simpa using h
| .sort _, h => by simp at h; split_ifs at h
| .app _ _, h => by simp at h; split_ifs at h
| .abs _ _, h => by simp at h; split_ifs at h
| .pi _ _, h => by simp at h; split_ifs at h

lemma lift_inj {i c : ℕ} {M : PTerm S}:
  ∀ {N : PTerm S}, (M ↑ i # c) = (N ↑ i # c) → M = N
| .var _, h => lift_eq_var_lift h
| .sort _, h => by
  cases M; all_goals simp at h
  split_ifs at h; simpa
| .app _ _, h => by
  cases M; all_goals simp at h
  split_ifs at h
  simpa using ⟨lift_inj h.1, lift_inj h.2⟩
| .abs _ _, h => by
  cases M; all_goals simp at h
  split_ifs at h
  simpa using ⟨lift_inj h.1, lift_inj h.2⟩
| .pi _ _, h => by
  cases M; all_goals simp at h
  split_ifs at h
  simpa using ⟨lift_inj h.1, lift_inj h.2⟩

lemma lift0_inj {i : ℕ} :
    (M ↑ i) = (N ↑ i) → M = N :=
  lift_inj

@[simp]
lemma lift_zero {c : ℕ} :
    ∀ {M : PTerm S}, (M ↑ 0 # c) = M
| .var _ => by simp
| .sort _ => by simp
| .app _ _ => by simp [lift_zero]
| .abs _ _ => by simp [lift_zero]
| .pi _ _ => by simp [lift_zero]

lemma lift_lift (i j k : ℕ) :
    ∀ {M : PTerm S}, ((M ↑ j # i) ↑ k # (j + i)) = M ↑ (j + k) # i
| .var _ => by
  simp
  split_ifs with h
  . simp only [lift]
    rw [if_pos]
    apply lt_of_lt_of_le h (Nat.le_add_left _ _)
  . simp
    rw [if_neg, Nat.add_assoc]
    simpa [Nat.add_comm j i] using h
| .sort _ => by simp
| .app _ _ => by simp [lift_lift]
| .abs M N => by simp [Nat.add_assoc j i 1, lift_lift]
| .pi _ _ => by simp [Nat.add_assoc j i 1, lift_lift]

lemma lift_lift_of_le (i j k n : ℕ) (h : i ≤ n) :
    ∀ {M : PTerm S}, ((M ↑ j # i) ↑ k # (j + n)) = (M ↑ k # n) ↑ j # i
| .var m => by
  simp
  split_ifs with h₁ h₂ h₃
  . simp only [lift, if_pos h₁, if_pos (lt_of_lt_of_le h₂ (Nat.le_add_left _ _))]
  . simpa using lt_of_le_of_lt (le_of_not_lt h₂) (lt_of_lt_of_le h₁ h)
  . simp only [lift]
    rw [if_neg h₁, if_pos (by simpa [Nat.add_comm m])]
  . simp only [lift]
    rw [if_neg, if_neg, Nat.add_assoc, Nat.add_comm j, ← Nat.add_assoc]
    apply not_lt_of_le ((le_of_not_lt h₁).trans (Nat.le_add_right m k))
    apply not_lt_of_le (by simpa [Nat.add_comm j] using h₃)
| .sort _ => by simp
| .app _ _ => by simp [lift_lift_of_le _ _ _ _ h]
| .abs M N => by
  simp [lift_lift_of_le _ _ _ _ h, Nat.add_assoc j n 1,
        lift_lift_of_le _ _ _ _ (Nat.succ_le_succ h)]
| .pi _ _ => by
  simp [lift_lift_of_le _ _ _ _ h, Nat.add_assoc j n 1,
        lift_lift_of_le _ _ _ _ (Nat.succ_le_succ h)]

lemma lift_lift_of_le_of_le (i j k n : ℕ) (h₁ : i ≤ k) (h₂ : k ≤ i + n) :
  ∀ {M : PTerm S}, ((M ↑ n # i) ↑ j # k) = M ↑ (n + j) # i
| .var m => by
  simp only [lift]
  split_ifs with h₃
  . simp only [lift, if_pos (lt_of_lt_of_le h₃ h₁)]
  . simp only [lift]
    rw [if_neg, ← Nat.add_assoc]
    apply not_lt_of_le (h₂.trans (Nat.add_le_add_right (le_of_not_lt h₃) _))
| .sort _ => by simp
| .app _ _ => by simp [lift_lift_of_le_of_le _ _ _ _ h₁ h₂]
| .abs M N => by
  simp [lift]
  constructor
  . rw [lift_lift_of_le_of_le _ _ _ _ h₁ h₂]
  . rw [lift_lift_of_le_of_le _ _ _ _ (Nat.succ_le_succ h₁)]
    rw [Nat.succ_add]; exact Nat.succ_le_succ h₂
| .pi _ _ => by
  simp [lift]
  constructor
  . rw [lift_lift_of_le_of_le _ _ _ _ h₁ h₂]
  . rw [lift_lift_of_le_of_le _ _ _ _ (Nat.succ_le_succ h₁)]
    rw [Nat.succ_add]; exact Nat.succ_le_succ h₂

lemma lift0_lift0 (i j : ℕ) :
    ((M ↑ i) ↑ j) = M ↑ (i + j) :=
  lift_lift_of_le_of_le _ _ _ _ (by simp) (by simp)

@[simp]
def subst (e : PTerm S) (m : ℕ) : PTerm S → PTerm S
| #n => if n < m then #n else (if n = m then e ↑ n else #(n - 1))
| sort M => !M
| app N M => (subst e m N) ⬝ (subst e m M)
| pi N M => Π.(subst e m N) (subst e (m + 1) M)
| abs N M => λ.(subst e m N) (subst e (m + 1) M)

notation N "{" e " // " m "}" => subst e m N

notation N "{" e "}" => subst e 0 N

def subst_lift (i j k : ℕ) :
  ∀ {M N : PTerm S}, (M{N // j} ↑ k # (j + i)) = (M ↑ k # j + i + 1){N ↑ k # i // j}
| .var m, N => by
  simp; split_ifs with h₁ h₂ h₃ h₄ h₅
  . simp; rw [if_pos (lt_of_lt_of_le h₁ (Nat.le_add_right _ _)), if_pos h₁]
  . simpa using (not_lt_of_le $ (Nat.le_add_right j i).trans (Nat.le_add_right _ 1))
      (lt_of_le_of_lt (le_of_not_lt h₂) h₁)
  . simp [h₃]; rw [lift_lift_of_le _ _ _ _ (by simp)]
  . simp [h₃] at h₄
    simpa using (not_le_of_lt $ lt_of_le_of_lt (Nat.le_add_right j i) (Nat.lt_add_one _)) h₄
  . simp
    rw [if_pos, if_neg h₁, if_neg h₃]
    rwa [Nat.sub_lt_iff_lt_add, Nat.add_comm 1]
    apply Nat.one_le_of_lt $ lt_of_le_of_ne (le_of_not_lt h₁) (Ne.symm h₃)
  . simp
    have : j < m :=
      lt_of_le_of_ne (le_of_not_lt h₁) (by simpa [eq_comm] using h₃)
    rw [if_neg, if_neg, if_neg, Nat.sub_add_comm]
    . apply Nat.one_le_of_lt $ lt_of_le_of_ne (le_of_not_lt h₁) (by simpa [eq_comm] using h₃)
    . contrapose! this
      simp [← this]
    . contrapose! this
      apply (Nat.le_add_right _ _).trans this.le
    . simp; apply Nat.le_sub_of_add_le (le_of_not_lt h₅)
| .sort _, _ => rfl
| .app _ _, _ => by simp [subst_lift, subst_lift]
| .abs _ _, _ => by
  simp; constructor
  . rw [subst_lift]
  . rw [Nat.add_assoc j, Nat.add_comm i 1, ← Nat.add_assoc, subst_lift]
| .pi _ _, _ => by
  simp; constructor
  . rw [subst_lift]
  . rw [Nat.add_assoc j, Nat.add_comm i 1, ← Nat.add_assoc, subst_lift]

def subst_lift_of_le (i j n : ℕ) (h : i ≤ n) :
  ∀ {M N : PTerm S}, (M{N // n} ↑ j # i) = (M ↑ j # i){N // j + n}
| .var m, N => by
  simp; split_ifs with h₁ h₂ h₃ h₄ h₅
  . simp; rw [if_pos h₂, if_pos (Nat.lt_add_left _ h₁)]
  . simp; rw [if_neg h₂, if_pos (by simpa [Nat.add_comm j])]
  . rw [h₃] at h₄; simpa using not_le_of_lt h₄ h
  . simp; rw [if_neg (by simp [h₃, Nat.add_comm]), if_pos (by rw [h₃, Nat.add_comm])]
    rw [lift_lift_of_le_of_le _ _ _ _ (by simp) (by simpa [h₃])]
  . simpa using lt_of_lt_of_le h₅ $ h.trans (le_of_not_lt h₁)
  . simp
    rw [if_neg, if_neg, if_neg, Nat.sub_add_comm]
    . apply Nat.one_le_of_lt $ lt_of_le_of_ne (le_of_not_lt h₁) (Ne.symm h₃)
    . contrapose! h₃
      rw [Nat.add_comm, Nat.add_left_cancel_iff] at h₃
      exact h₃
    . contrapose! h₁
      rw [Nat.add_comm, Nat.add_lt_add_iff_left] at h₁
      exact h₁
    . simp; apply Nat.le_sub_one_of_lt $ lt_of_le_of_lt h $
        lt_of_le_of_ne (le_of_not_lt h₁) (Ne.symm h₃)
| .sort _, _ => rfl
| .app _ _, _ => by simp [subst_lift_of_le _ _ _ h]
| .abs _ _, _ => by
  simp; constructor
  . rw [subst_lift_of_le _ _ _ h]
  . rw [subst_lift_of_le _ _ _ (by simpa [Nat.add_le_add_iff_right]), ← Nat.add_assoc]
| .pi _ _, _ => by
  simp; constructor
  . rw [subst_lift_of_le _ _ _ h]
  . rw [subst_lift_of_le _ _ _ (by simpa [Nat.add_le_add_iff_right]), ← Nat.add_assoc]

def lift_subst_of_le_of_le (i k n : ℕ) (h₁ : i ≤ k) (h₂ : k ≤ i + n) :
    ∀ {M N : PTerm S}, (M ↑ (n + 1) # i){N // k} = M ↑ n # i
| .var m, N => by
  simp; split_ifs with h₃
  . simp only [subst]; rw [if_pos (lt_of_lt_of_le h₃ h₁)]
  . simp; rw [if_neg, if_neg]
    . contrapose! h₂
      rw [← h₂, Nat.add_comm n, ← Nat.add_assoc, Nat.add_lt_add_iff_right,
          Nat.lt_add_one_iff]
      exact le_of_not_lt h₃
    . contrapose! h₂
      exact (Nat.add_le_add (le_of_not_lt h₃) (Nat.le_add_right _ 1)).trans h₂
| .sort _, _ => rfl
| .app _ _, _ => by simp [lift_subst_of_le_of_le _ _ _ h₁ h₂]
| .abs _ _, _ => by
  simp; constructor
  . rw [lift_subst_of_le_of_le _ _ _ h₁ h₂]
  . rw [lift_subst_of_le_of_le _ _ _ (Nat.succ_le_succ h₁)]
    rwa [Nat.succ_eq_add_one, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1,
         ← Nat.add_assoc, Nat.add_le_add_iff_right]
| .pi _ _, _ => by
  simp; constructor
  . rw [lift_subst_of_le_of_le _ _ _ h₁ h₂]
  . rw [lift_subst_of_le_of_le _ _ _ (Nat.succ_le_succ h₁)]
    rwa [Nat.succ_eq_add_one, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1,
         ← Nat.add_assoc, Nat.add_le_add_iff_right]

variable {P : PTerm S}

def subst_subst (i j : ℕ) :
    ∀ {M N : PTerm S}, M{N // j}{P // i + j} = M{P // i + j + 1}{N{P // i} // j}
| .var n, N => by
  simp; split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  . simp; rw [if_pos (lt_of_lt_of_le h₁ (Nat.le_add_left _ _)), if_pos h₁]
  . rw [h₃, Nat.add_assoc, Nat.add_comm j, ← Nat.add_assoc] at h₁
    simpa using not_lt_of_le (Nat.le_add_left j (i + 1)) h₁
  . have := (lt_of_le_of_ne (le_of_not_lt h₂) (Ne.symm h₃)).trans h₁
    rw [Nat.add_assoc, Nat.add_comm j, ← Nat.add_assoc] at this
    simpa using not_lt_of_le (Nat.le_add_left j (i + 1)) this
  . simp [h₄]; rw [subst_lift_of_le _ _ _ (by simp), Nat.add_comm i]
  . rw [h₄, Nat.add_assoc, Nat.add_comm j, ← Nat.add_assoc,
      Nat.self_eq_add_left] at h₆
    simpa using Nat.add_one_ne_zero _ h₆
  . rw [h₄, Nat.add_comm i] at h₅
    simpa using h₅ $ Nat.lt_add_one_of_le (Nat.le_add_right j i)
  . simp
    rw [if_pos, if_neg h₁, if_neg h₄]
    rwa [Nat.sub_lt_iff_lt_add, Nat.add_comm]
    apply Nat.one_le_of_lt $ lt_of_le_of_ne (le_of_not_lt h₁) (Ne.symm h₄)
  . simp [h₈]; rw [lift_subst_of_le_of_le _ _ _ (by simp) (by simp)]
  . simp
    have aux₁ := lt_of_le_of_ne (le_of_not_lt h₇) (Ne.symm h₈)
    have aux₂ := lt_of_le_of_ne (le_of_not_lt h₁) (Ne.symm h₄)
    rw [if_neg, if_neg, if_neg, if_neg]
    . contrapose! aux₁
      rw [← aux₁, Nat.add_assoc, Nat.sub_add_cancel (Nat.one_le_of_lt aux₂)]
      simp only [Nat.le_add_left]
    . apply not_lt_of_le $ Nat.le_sub_one_of_lt aux₂
    . contrapose! aux₁
      rw [← aux₁, Nat.sub_add_cancel (Nat.one_le_of_lt aux₂)]
    . apply not_lt_of_le $ Nat.le_sub_one_of_lt (lt_trans (Nat.lt_add_one _) aux₁)
| .sort _, _ => rfl
| .app _ _, _ => by simp [subst_subst]
| .abs _ _, _ => by
  simp; constructor
  . rw [subst_subst]
  . rw [Nat.add_assoc i, subst_subst]
| .pi _ _, _ => by
  simp; constructor
  . rw [subst_subst]
  . rw [Nat.add_assoc i, subst_subst]

def subst0_subst (k : ℕ) :
    M{N}{P // k} = M{P // k + 1}{N{P // k}} :=
  subst_subst _ 0

end LiftSubst

section Context

def PCtx (S : Specification) := List (PTerm S)

def PCtx.lift (i c : ℕ) : PCtx S → PCtx S := List.map (PureTypeSystem.lift i c)

notation Γ" ↑↑ "i" # "c => PCtx.lift i c Γ

@[simp]
lemma PCtx.lift_length {i c : ℕ} {Γ : PCtx S} : (Γ ↑↑ i # c).length = Γ.length :=
  List.length_map _ _

notation Γ" ↑↑ "i => PCtx.lift i 0 Γ

variable {α : Type*}

inductive isItem : α → List α → ℕ → Type _
| zero Γ : isItem x (x :: Γ) 0
| succ {Γ n} y : isItem x Γ n → isItem x (y :: Γ) (n + 1)

notation x " ↓ " n " in " Γ => isItem x Γ n

lemma isItem.lt_length : ∀ (_ : x ↓ n in Γ), n < length Γ
| .zero _ => by simp
| .succ x h => by simp; apply lt_length h

lemma isItem_unique {x y : α} {Γ : List α} {n : ℕ} :
    (x ↓ n in Γ) → (y ↓ n in Γ) → x = y := by
  induction n generalizing x y Γ
  . intro h₁ h₂
    cases h₁; cases h₂; rfl
  . intro h₁ h₂
    cases h₁; cases h₂
    rename_i ih _ _ h₁ h₂
    apply ih h₁ h₂

def isItem.pred {x y : α} {Γ : List α}: ∀ (_ : x ↓ (n + 1) in (y :: Γ)), x ↓ n in Γ
| .succ _ h => h

lemma isItem.eq {x y : α} {Γ : List α} : ∀ (_ : x ↓ 0 in y :: Γ), x = y
| .zero _ => rfl

-- isTruncate the first k-term and have =
inductive isTrunc : ℕ → List α → List α → Type _
| zero Γ : isTrunc 0 Γ Γ
| succ {k : ℕ} {Γ Γ' : List α} (x : α) : isTrunc k Γ Γ' → isTrunc (k + 1) (x :: Γ) Γ'

def isTrunc.pred : ∀ {k Γ Δ} {A : PTerm S} (_ : isTrunc k Γ (A :: Δ)), isTrunc (k + 1) Γ Δ
| 0, _, _, _, h => by cases h; apply isTrunc.succ; apply isTrunc.zero
| k, [], Δ, A, h => by cases h
| k + 1, B :: Γ, Δ, A, h => by
  apply isTrunc.succ
  cases h
  apply isTrunc.pred (by assumption)

def isTrunc.nil_length {Γ : List α}: ∀ {k} (_ : isTrunc k Γ []), Γ.length = k
| 0, h => by cases h; rfl
| k + 1, .succ x h => by simp only [length_cons, nil_length h]

def isTrunc.heads : ∀ {k : ℕ} {Γ Δ : List α} (_ : isTrunc k Γ Δ), List α
| 0, _, _, _ => []
| _ + 1, A :: _, _, .succ _ h => A :: h.heads

lemma isTrunc.heads_append : ∀  {k : ℕ} {Γ Δ : List α} (h : isTrunc k Γ Δ),
    h.heads.append Δ = Γ
| 0, _, _, .zero _ => rfl
| k + 1, A :: Γ, Δ, .succ _ h => by
  simp [heads]
  apply h.heads_append

@[simp]
lemma isTrunc.heads_length : ∀  {k : ℕ} {Γ Δ : List α} (h : isTrunc k Γ Δ),
    h.heads.length = k
| 0, _, _, .zero _ => rfl
| k + 1, A :: Γ, Δ, .succ _ h => by
  simpa [heads] using h.heads_length

def isTrunc.isItem {Γ Δ : List α} {A : α} : ∀ {k : ℕ},
    isTrunc k Γ (A :: Δ) → A ↓ k in Γ
| 0, h => by cases h; apply isItem.zero
| k + 1, .succ _ h => isItem.succ _ h.isItem

def isItem.isTrunc {k : ℕ} {Γ : List α} {x : α} :
  (_ : x ↓ k in Γ) → Σ Γ', isTrunc (k + 1) Γ Γ'
| .zero Γ => ⟨Γ, isTrunc.succ _ (isTrunc.zero _)⟩
| .succ y h => by
  exact ⟨_, isTrunc.succ _ h.isTrunc.2⟩

lemma exists_isTrunc_of_isItem {k : ℕ} {Γ : List α} {x : α} :
  (_ : x ↓ k in Γ) → ∃ Γ', Nonempty (isTrunc (k + 1) Γ Γ')
| .zero Γ => ⟨Γ, ⟨isTrunc.succ _ (isTrunc.zero _)⟩⟩
| .succ y h => by
  obtain ⟨Γ, ⟨hΓ⟩⟩ := exists_isTrunc_of_isItem h
  exact ⟨Γ, ⟨isTrunc.succ _ hΓ⟩⟩

inductive isInsert (Γ : PCtx S) (t : PTerm S) : ℕ → PCtx S → PCtx S → Type _
| zero : isInsert Γ t 0 Γ (t :: Γ)
| succ {n Δ Δ'} u : isInsert Γ t n Δ Δ' → isInsert Γ t (n + 1) (u :: Δ) ((u ↑ 1 # n) :: Δ')

def isItem_of_isInsert_of_le {t : PTerm S} {n : ℕ} {Γ Δ Δ' : PCtx S} :
    isInsert Γ t n Δ Δ' → ∀ {k}, (n ≤ k → ∀ {u}, (u ↓ k in Δ) → u ↓ k + 1 in Δ') := by
  induction n generalizing t Δ Δ'
  . intro h k hk u hu; cases h
    apply isItem.succ _ hu
  . intro h k hk u hu
    cases h
    rename_i n ih Δ Δ' v ht
    apply isItem.succ
    cases k
    . simp at hk
    . cases hu
      rename_i hu
      simp at hk
      apply ih ht hk hu

def isItem_of_isInsert_of_lt {u t : PTerm S} {n k : ℕ} {Γ Δ Δ' : PCtx S} :
    isInsert Γ t n Δ Δ' → k < n → (u ↓ k in Δ) → (u ↑ 1 # (n - (k + 1)) ) ↓ k in Δ'
| .zero, h, _ => by simp at h
| .succ _ h₁, h₂, .zero _ => by simpa using isItem.zero _
| .succ _ h₁, h₂, .succ _ h₃ => by
  simpa using isItem.succ _ (isItem_of_isInsert_of_lt h₁ (by simpa using h₂) h₃)

structure isItemLift (t : PTerm S) (Γ : PCtx S) (n : ℕ) where
  item : PTerm S
  eq : t = item ↑ n + 1
  is : item ↓ n in Γ

notation x " ↓ " n " sub " Γ => isItemLift x Γ n

lemma isItemLift.eq_lift_one {t u : PTerm S} {Γ : PCtx S} (h : t ↓ 0 sub (u :: Γ)) :
    t = u ↑ 1 := by
  simp only [h.2, h.3.eq]

def isItemLift_of_isInsert_of_lt {t u : PTerm S} {n : ℕ} {Γ Δ Δ' : PCtx S}
  (h : isInsert Γ t n Δ Δ') {k : ℕ} (hk : k < n) (hu : u ↓ k sub Δ) :
    (u ↑ 1 # n) ↓ k sub Δ' := by
  cases hu with
  | mk w hw₁ hw₂ =>
    use w ↑ 1 # (n - (k + 1))
    . rw [hw₁]
      have : n = (k + 1) + (n - (k + 1)) :=  (Nat.add_sub_of_le hk).symm
      rw [this, lift_lift_of_le _ _ _ _ (Nat.zero_le _)]
      congr
    . clear u hw₁
      cases h
      . simp at hk
      . rename_i n Δ Δ' u ht
        cases hw₂
        . apply isItem.zero
        . rename_i n' hw
          apply isItem.succ
          simp at hk ⊢
          apply isItem_of_isInsert_of_lt ht hk hw

inductive isSubst (Γ : PCtx S) (t T : PTerm S) : ℕ → PCtx S → PCtx S → Type _
| zero : isSubst Γ t T 0 (T :: Γ) Γ
| succ {n Δ Δ'} w : isSubst Γ t T n Δ Δ' → isSubst Γ t T (n + 1) (w :: Δ) (w{t // n} :: Δ')

def isItem_of_isSubst_of_le {Γ Δ Δ' : PCtx S} {a A B : PTerm S} {n : ℕ} :
    {k : ℕ} → isSubst Γ a A n Δ Δ' → n ≤ k → (B ↓ k + 1 in Δ) → B ↓ k in Δ'
| _, .zero, _, .succ _ h => h
| k + 1, .succ _ h₁, h₂, .succ _ h₃ => by
  apply isItem.succ
  apply isItem_of_isSubst_of_le h₁ (by simpa using h₂) h₃


def isItem_of_isSubst_of_lt {Γ Δ Δ' : PCtx S} {a A B : PTerm S} {n k : ℕ} :
    isSubst Γ a A n Δ Δ' → k < n → (B ↓ k in Δ) → B{a // n - (k + 1)} ↓ k in Δ'
| .zero, h, _ => by simp at h
| .succ _ h₁, h₂, .zero _ => by
  simp; apply isItem.zero
| .succ _ h₁, h₂, .succ _ h₃ => by
  apply isItem.succ
  simp
  apply isItem_of_isSubst_of_lt h₁ (by simpa using h₂) h₃

def isItemLift_of_isSubst_of_lt {Γ Δ Δ' : PCtx S} {a A B : PTerm S} {n k : ℕ} :
    isSubst Γ a A n Δ Δ' → k < n → (B ↓ k sub Δ) → B{a // n} ↓ k sub Δ' := by
  intro h₁ h₂ h₃
  use h₃.1{a // n - (k + 1)}
  . conv_lhs => rw [h₃.2]
    rw [subst_lift_of_le _ _ _ (by simp)]
    congr 1
    rw [Nat.add_sub_cancel' (by simpa)]
  . apply isItem_of_isSubst_of_lt h₁ h₂ h₃.3

lemma eq_of_isSubst_of_isItem {n : ℕ} {Γ Δ Δ' : PCtx S} {a A B: PTerm S} :
    isSubst Γ a A n Δ Δ' → (B ↓ n in Δ) → A = B
| .zero, h => by cases h; rfl
| .succ _ h₁, .succ _ h₂ => eq_of_isSubst_of_isItem h₁ h₂

def isSubst.isTrunc {n : ℕ} {Γ Δ Δ' : PCtx S} {a A : PTerm S} :
    isSubst Γ a A n Δ Δ' → isTrunc n Δ' Γ
| .zero => isTrunc.zero _
| .succ _ h => isTrunc.succ _ h.isTrunc

end Context

section Reduction

variable {S : Specification}

inductive beta : PTerm S → PTerm S → Type _
| red (A M N : PTerm S) : beta ((λ.A M) ⬝ N) (M{N})
| appl (A A' M : PTerm S) : beta A A' → beta (A ⬝ M) (A' ⬝ M)
| appr (A M M' : PTerm S) : beta M M' → beta (A ⬝ M) (A ⬝ M')
| pil (A A' M : PTerm S) : beta A A' → beta (Π.A M) (Π.A' M)
| pir (A M M' : PTerm S) : beta M M' → beta (Π.A M) (Π.A M')
| absl (A A' M : PTerm S) : beta A A' → beta (λ.A M) (λ.A' M)
| absr (A M M' : PTerm S) : beta M M' → beta (λ.A M) (λ.A M')

infix:50 " →β " => beta

inductive betar : PTerm S → PTerm S → Type _
| beta x y : x →β y → betar x y
| refl x : betar x x
| trans x y z : betar x y → betar y z → betar x z

infix:50 " ↠β " => betar

inductive betac : PTerm S → PTerm S → Type _
| betar x y : x ↠β y → betac x y
| symm x y : betac x y → betac y x
| trans x y z : betac x y → betac y z → betac x z

infix:50 " ≃β " => betac

def betac.refl (A : PTerm S) : A ≃β A := betac.betar _ _ (betar.refl _)

def beta.betac {A B : PTerm S} (h : A →β B) : A ≃β B := betac.betar _ _ (betar.beta _ _ h)

def betar.betac {A B : PTerm S} (h : A ↠β B) : A ≃β B := betac.betar _ _ h

def beta.lift : (h : A →β B) → (A ↑ i # n) →β B ↑ i # n
| .red A M N => by
  have : n = 0 + n := by simp
  conv_rhs =>
    rw [this, subst_lift]
  simpa using beta.red _ _ _
| .appl _ _ _ h => by simpa using beta.appl _ _ _ (beta.lift h)
| .appr _ _ _ h => by simpa using beta.appr _ _ _ (beta.lift h)
| .pil _ _ _ h => by simpa using beta.pil _ _ _ (beta.lift h)
| .pir _ _ _ h => by simpa using beta.pir _ _ _ (beta.lift h)
| .absl _ _ _ h => by simpa using beta.absl _ _ _ (beta.lift h)
| .absr _ _ _ h => by simpa using beta.absr _ _ _ (beta.lift h)

def betar.lift : (h : A ↠β B) → (A ↑ i # n) ↠β B ↑ i # n
| .beta _ _ h => betar.beta _ _ h.lift
| .refl _ => betar.refl _
| .trans _ _ _ h₁ h₂ => h₁.lift.trans _ _ _ h₂.lift

def betac.lift : (h : A ≃β B) → (A ↑ i # n) ≃β B ↑ i # n
| .betar _ _ h => betac.betar _ _ h.lift
| .symm _ _ h => h.lift.symm
| .trans _ _ _ h₁ h₂ => h₁.lift.trans _ _ _ h₂.lift

def betar.appl {A A' B : PTerm S} : ∀ (_ : A ↠β A'), A ⬝ B ↠β A' ⬝ B
| .beta _ _ h => beta _ _ (beta.appl _ _ _ h)
| .refl _ => refl _
| .trans _ _ _ h₁ h₂ => h₁.appl.trans _ _ _ h₂.appl

def betar.appr {A B B' : PTerm S} : ∀ (_ : B ↠β B'), A ⬝ B ↠β A ⬝ B'
| .beta _ _ h => beta _ _ (beta.appr _ _ _ h)
| .refl _ => refl _
| .trans _ _ _ h₁ h₂ => h₁.appr.trans _ _ _ h₂.appr

def betar.app  {A B A' B' : PTerm S} (h₁ : A ↠β A') (h₂ : B ↠β B') :
    A ⬝ B ↠β A' ⬝ B' :=
  h₁.appl.trans _ _ _ h₂.appr

def betac.appl {A A' B : PTerm S} : ∀ (_ : A ≃β A'), A ⬝ B ≃β A' ⬝ B
| .betar _ _ h => betar _ _ h.appl
| .symm _ _ h => h.appl.symm
| .trans _ _ _ h₁ h₂ => h₁.appl.trans _ _ _ h₂.appl

def betac.appr {A B B' : PTerm S} : ∀ (_ : B ≃β B'), A ⬝ B ≃β A ⬝ B'
| .betar _ _ h => betar _ _ h.appr
| .symm _ _ h => h.appr.symm
| .trans _ _ _ h₁ h₂ => h₁.appr.trans _ _ _ h₂.appr

def betac.app  {A B A' B' : PTerm S} (h₁ : A ≃β A') (h₂ : B ≃β B') :
    A ⬝ B ≃β A' ⬝ B' :=
  h₁.appl.trans _ _ _ h₂.appr

def betar.absl {A A' B : PTerm S} : ∀ (_ : A ↠β A'), λ.A B ↠β λ.A' B
| .beta _ _ h => beta _ _ (beta.absl _ _ _ h)
| .refl _ => refl _
| .trans _ _ _ h₁ h₂ => h₁.absl.trans _ _ _ h₂.absl

def betar.absr {A B B' : PTerm S} : ∀ (_ : B ↠β B'), λ.A B ↠β λ.A B'
| .beta _ _ h => beta _ _ (beta.absr _ _ _ h)
| .refl _ => refl _
| .trans _ _ _ h₁ h₂ => h₁.absr.trans _ _ _ h₂.absr

def betar.abs  {A B A' B' : PTerm S} (h₁ : A ↠β A') (h₂ : B ↠β B') :
    λ.A B ↠β λ.A' B' :=
  h₁.absl.trans _ _ _ h₂.absr

def betac.absl {A A' B : PTerm S} : ∀ (_ : A ≃β A'), λ.A B ≃β λ.A' B
| .betar _ _ h => betar _ _ h.absl
| .symm _ _ h => h.absl.symm
| .trans _ _ _ h₁ h₂ => h₁.absl.trans _ _ _ h₂.absl

def betac.absr {A B B' : PTerm S} : ∀ (_ : B ≃β B'), λ.A B ≃β λ.A B'
| .betar _ _ h => betar _ _ h.absr
| .symm _ _ h => h.absr.symm
| .trans _ _ _ h₁ h₂ => h₁.absr.trans _ _ _ h₂.absr

def betac.abs  {A B A' B' : PTerm S} (h₁ : A ≃β A') (h₂ : B ≃β B') :
    λ.A B ≃β λ.A' B' :=
  h₁.absl.trans _ _ _ h₂.absr

def betar.pil {A A' B : PTerm S} : ∀ (_ : A ↠β A'), Π.A B ↠β Π.A' B
| .beta _ _ h => beta _ _ (beta.pil _ _ _ h)
| .refl _ => refl _
| .trans _ _ _ h₁ h₂ => h₁.pil.trans _ _ _ h₂.pil

def betar.pir {A B B' : PTerm S} : ∀ (_ : B ↠β B'), Π.A B ↠β Π.A B'
| .beta _ _ h => beta _ _ (beta.pir _ _ _ h)
| .refl _ => refl _
| .trans _ _ _ h₁ h₂ => h₁.pir.trans _ _ _ h₂.pir

def betar.pi  {A B A' B' : PTerm S} (h₁ : A ↠β A') (h₂ : B ↠β B') :
    Π.A B ↠β Π.A' B' :=
  h₁.pil.trans _ _ _ h₂.pir

def betac.pil {A A' B : PTerm S} : ∀ (_ : A ≃β A'), Π.A B ≃β Π.A' B
| .betar _ _ h => betar _ _ h.pil
| .symm _ _ h => h.pil.symm
| .trans _ _ _ h₁ h₂ => h₁.pil.trans _ _ _ h₂.pil

def betac.pir {A B B' : PTerm S} : ∀ (_ : B ≃β B'), Π.A B ≃β Π.A B'
| .betar _ _ h => betar _ _ h.pir
| .symm _ _ h => h.pir.symm
| .trans _ _ _ h₁ h₂ => h₁.pir.trans _ _ _ h₂.pir

def betac.pi  {A B A' B' : PTerm S} (h₁ : A ≃β A') (h₂ : B ≃β B') :
    Π.A B ≃β Π.A' B' :=
  h₁.pil.trans _ _ _ h₂.pir

def beta.substl {A B C : PTerm S} {n : ℕ} : ∀ (_ : A →β B), A{C//n} →β B{C//n}
| .red A M N => by
  simpa [subst0_subst] using beta.red (A{C // n}) (M{C // n + 1}) (N{C // n})
| .appl _ _ _ h => h.substl.appl _ _ _
| .appr _ _ _ h => h.substl.appr _ _ _
| .absl _ _ _ h => h.substl.absl _ _ _
| .absr _ _ _ h => h.substl.absr _ _ _
| .pil _ _ _ h => h.substl.pil _ _ _
| .pir _ _ _ h => h.substl.pir _ _ _

def betar.substl {A B C : PTerm S} {n : ℕ} : ∀ (_ : A ↠β B), A{C//n} ↠β B{C//n}
| .beta _ _ h => beta _ _ h.substl
| .refl _ => refl _
| .trans _ _ _ h₁ h₂ => h₁.substl.trans _ _ _ h₂.substl

def betar.substr {B C : PTerm S} {n : ℕ} (h : B ↠β C) : ∀ {A}, A{B//n} ↠β A{C//n}
| .var i => by
  simp
  split_ifs
  . apply refl _
  . apply h.lift
  . apply refl _
| .sort s => refl _
| .app M N => h.substr.app h.substr
| .abs M N => h.substr.abs h.substr
| .pi M N => h.substr.pi h.substr

def betar.subst {A A' B B' : PTerm S} {n : ℕ} {h₁ : A ↠β A'} {h₂ : B ↠β B'} :
    A{B // n} ↠β A'{B'//n} :=
  h₁.substl.trans _ _ _ h₂.substr

def betac.substl {A B C : PTerm S} {n : ℕ} : ∀ (_ : A ≃β B), A{C//n} ≃β B{C//n}
| .betar _ _ h => betar _ _ h.substl
| .symm _ _ h => h.substl.symm
| .trans _ _ _ h₁ h₂ => h₁.substl.trans _ _ _ h₂.substl

def betac.substr {B C : PTerm S} {n : ℕ} (h : B ≃β C) : ∀ {A}, A{B//n} ≃β A{C//n}
| .var i => by
  simp
  split_ifs
  . apply refl _
  . apply h.lift
  . apply refl _
| .sort s => refl _
| .app M N => h.substr.app h.substr
| .abs M N => h.substr.abs h.substr
| .pi M N => h.substr.pi h.substr

def betac.subst {A A' B B' : PTerm S} {n : ℕ} (h₁ : A ≃β A') (h₂ : B ≃β B') :
    A{B // n} ≃β A'{B'//n} :=
  h₁.substl.trans _ _ _ h₂.substr

lemma betar.eq_of_sort_betar' {s : S.sort} {A B : PTerm S} (h : B = !s):
    B ↠β A → A = !s
| .beta _ _ h' => by cases h; cases h'
| .refl _ => h
| .trans _ _ _ h₁ h₂ => h₂.eq_of_sort_betar' (h₁.eq_of_sort_betar' h)

lemma betar.eq_of_sort_betar {s : S.sort} {A : PTerm S} :
    (!s) ↠β A → A = !s
| h => h.eq_of_sort_betar' rfl

lemma betar.eq_of_var_betar' {n : ℕ} {A B : PTerm S} (h : B = #n):
    B ↠β A → A = #n
| .beta _ _ h' => by cases h; cases h'
| .refl _ => h
| .trans _ _ _ h₁ h₂ => h₂.eq_of_var_betar' (h₁.eq_of_var_betar' h)

lemma betar.eq_of_var_betar {n : ℕ} {A : PTerm S} :
    (#n) ↠β A → A = #n
| h => h.eq_of_var_betar' rfl

structure betar.PiStruct (A B C : PTerm S) where
  left : PTerm S
  right : PTerm S
  eq : C = Π.left right
  betarl : A ↠β left
  betarr : B ↠β right

def betar.PiStruct.trans {A B A' B' C C' : PTerm S} (S : PiStruct A B C)
  (h₁ : A' = S.left) (h₂ : B' = S.right) (S' : PiStruct A' B' C') :
    PiStruct A B C' where
  left := S'.left
  right := S'.right
  eq := S'.eq
  betarl := by
    cases h₁
    exact S.betarl.trans _ _ _ S'.betarl
  betarr := by
    cases h₂
    exact S.betarr.trans _ _ _ S'.betarr

def beta.of_pi_beta {A B C : PTerm S} :
    (h : Π.A B →β C) → betar.PiStruct A B C
| .pil _ A' _ h => ⟨A', _, rfl, betar.beta _ _ h, betar.refl _⟩
| .pir _ _ B' h => ⟨_, B', rfl, betar.refl _, betar.beta _ _ h⟩

def betar.of_pi_betar' {A B C D : PTerm S} (h : D = Π.A B) :
    (h : D ↠β C) → PiStruct A B C
| .beta _ _ h' => by cases h; exact h'.of_pi_beta
| .refl _ => by cases h; exact ⟨_, _, rfl, betar.refl _, betar.refl _⟩
| .trans _ _ _ h₁ h₂ =>
  (h₁.of_pi_betar' h).trans rfl rfl (h₂.of_pi_betar' (h₁.of_pi_betar' h).eq)

def betar.of_pi_betar {A B C : PTerm S} (h : Π.A B ↠β C) :
    PiStruct A B C := h.of_pi_betar' rfl

section Confluence
/--
  Parallel reduction
-/
inductive betap : PTerm S → PTerm S → Type _
| var n : betap (#n) (#n)
| sort s : betap (!s) (!s)
| pi A A' M M' : betap A A' → betap M M' → betap (Π.A M) (Π.A' M')
| abs A A' M M' : betap A A' → betap M M' → betap (λ.A M) (λ.A' M')
| app A A' M M' : betap A A' → betap M M' → betap (A ⬝ M) (A' ⬝ M')
| red A M M' N N' : betap M M' → betap N N' → betap ((λ. A M) ⬝ N) (M'{N'})

inductive betapr : PTerm S → PTerm S → Type _
| betap x y : betap x y → betapr x y
| refl x : betapr x x
| trans x y z : betapr x y → betapr y z → betapr x z

infix:50 " →'β " => betap

infix:50 " ↠'β " => betapr

def betap.refl : (A : PTerm S) → A →'β A
| .var _ => var _
| .sort _ => sort _
| .app _ _ => app _ _ _ _ (refl _) (refl _)
| .abs _ _ => abs _ _ _ _ (refl _) (refl _)
| .pi _ _ => pi _ _ _ _ (refl _) (refl _)

def betap.lift {i c : ℕ} {A B : PTerm S} : A →'β B → (A ↑ i # c) →'β (B ↑ i # c)
| .var _ => by
  simp; split_ifs
  <;> apply var
| .sort _ => betap.sort _
| .app _ _ _ _ h₁ h₂ => app _ _ _ _ h₁.lift h₂.lift
| .abs _ _ _ _ h₁ h₂ => abs _ _ _ _ h₁.lift h₂.lift
| .pi _ _ _ _ h₁ h₂ => pi _ _ _ _ h₁.lift h₂.lift
| .red _ _ _ _ _ h₁ h₂ => by
  have : c = 0 + c := by simp
  conv_rhs => rw [this, subst_lift]; simp
  apply red _ _ _ _ _ h₁.lift h₂.lift

def betap.subst {n : ℕ} {A B : PTerm S} :
  A →'β A' → B →'β B' → A{B // n} →'β A'{B'// n}
| .var _, h => by
  simp; split_ifs
  . apply var
  . apply h.lift
  . apply var
| .sort _, _ => betap.sort _
| .app _ _ _ _ h₁ h₂, h => app _ _ _ _ (h₁.subst h) (h₂.subst h)
| .abs _ _ _ _ h₁ h₂, h => abs _ _ _ _ (h₁.subst h) (h₂.subst h)
| .pi _ _ _ _ h₁ h₂, h => pi _ _ _ _ (h₁.subst h) (h₂.subst h)
| .red _ _ _ _ _ h₁ h₂, h => by
  simp
  have : n = n + 0 := rfl
  conv_rhs => rw [this, subst_subst n 0]; simp
  apply red _ _ _ _ _ (h₁.subst h) (h₂.subst h)

def betap.betar {A B : PTerm S} :
    A →'β B → A ↠β B
| .var _ => betar.refl _
| .sort _ => betar.refl _
| .app _ _ _ _ h₁ h₂ => betar.app h₁.betar h₂.betar
| .abs _ _ _ _ h₁ h₂ => betar.abs h₁.betar h₂.betar
| .pi _ _ _ _ h₁ h₂ => betar.pi h₁.betar h₂.betar
| .red _ _ _ _ _ h₁ h₂ =>
  betar.trans _ _ _ (betar.beta _ _ (beta.red _ _ _))
    (betar.subst (h₁ := h₁.betar) (h₂ := h₂.betar))

def betapr.betar {A B : PTerm S} :
    A ↠'β B → A ↠β B
| .betap _ _ h => h.betar
| .refl _ => betar.refl _
| .trans _ _ _ h₁ h₂ => h₁.betar.trans _ _ _ h₂.betar

def beta.betap {A B : PTerm S} :
    A →β B → A →'β B
| .red _ _ _ => betap.red _ _ _ _ _ (betap.refl _) (betap.refl _)
| .appl _ _ _ h => betap.app _ _ _ _ h.betap (betap.refl _)
| .appr _ _ _ h => betap.app _ _ _ _ (betap.refl _) h.betap
| .pil _ _ _ h => betap.pi _ _ _ _ h.betap (betap.refl _)
| .pir _ _ _ h => betap.pi _ _ _ _ (betap.refl _) h.betap
| .absl _ _ _ h => betap.abs _ _ _ _ h.betap (betap.refl _)
| .absr _ _ _ h => betap.abs _ _ _ _ (betap.refl _) h.betap

def beta.betapr {A B : PTerm S} :
    A →β B → A ↠'β B :=
  fun h ↦ betapr.betap _ _ h.betap

def betar.betapr {A B : PTerm S} :
    A ↠β B → A ↠'β B
| .beta _ _ h => h.betapr
| .refl _ => betapr.refl _
| .trans _ _ _ h₁ h₂ => h₁.betapr.trans _ _ _ h₂.betapr

def betap.diamond {A B C : PTerm S} :
  A →'β B → A →'β C → Σ D, B →'β D × C →'β D
| .var _, .var _ => ⟨_, refl _, refl _⟩
| .sort _, .sort _ => ⟨_, refl _, refl _⟩
| .pi _ _ _ _ h₁ h₂, .pi _ _ _ _ h₃ h₄ =>
  ⟨_, pi _ _ _ _ (h₁.diamond h₃).2.1 (h₂.diamond h₄).2.1,
    pi _ _ _ _ (h₁.diamond h₃).2.2 (h₂.diamond h₄).2.2⟩
| .abs _ _ _ _ h₁ h₂, .abs _ _ _ _ h₃ h₄ =>
  ⟨_, abs _ _ _ _ (h₁.diamond h₃).2.1 (h₂.diamond h₄).2.1,
    abs _ _ _ _ (h₁.diamond h₃).2.2 (h₂.diamond h₄).2.2⟩
| .app _ _ _ _ h₁ h₂, .app _ _ _ _ h₃ h₄ =>
  ⟨_, app _ _ _ _ (h₁.diamond h₃).2.1 (h₂.diamond h₄).2.1,
    app _ _ _ _ (h₁.diamond h₃).2.2 (h₂.diamond h₄).2.2⟩
| .app _ _ _ _ (.abs _ _ _ _ _ h₁) h₂, .red _ _ _ _ _ h₃ h₄ =>
  ⟨_, red _ _ _ _ _ (h₁.diamond h₃).2.1 (h₂.diamond h₄).2.1,
    subst (h₁.diamond h₃).2.2 (h₂.diamond h₄).2.2⟩
| .red _ _ _ _ _ h₁ h₂, .red _ _ _ _ _ h₃ h₄ =>
  ⟨_, subst (h₁.diamond h₃).2.1 (h₂.diamond h₄).2.1,
    subst (h₁.diamond h₃).2.2 (h₂.diamond h₄).2.2⟩
| .red _ _ _ _ _ h₁ h₂, .app _ _ _ _ (.abs _ _ _ _ _ h₃) h₄ =>
  ⟨_, subst (h₁.diamond h₃).2.1 (h₂.diamond h₄).2.1,
    red _ _ _ _ _ (h₁.diamond h₃).2.2 (h₂.diamond h₄).2.2⟩

def betap.diamond_aux {A B C : PTerm S} :
  A →'β B → A ↠'β C → Σ D, B ↠'β D × C →'β D
| h₁, .betap _ _ h₂ => ⟨_, betapr.betap _ _ (h₁.diamond h₂).2.1, (h₁.diamond h₂).2.2⟩
| h₁, .refl _ => ⟨_, betapr.refl _, h₁⟩
| h₁, .trans _ _ _ h₂ h₃ => by
  let h₄ := h₁.diamond_aux h₂
  exact ⟨_, h₄.2.1.trans _ _ _ (h₄.2.2.diamond_aux h₃).2.1,
    (h₄.2.2.diamond_aux h₃).2.2⟩

def betapr.diamond {A B C : PTerm S} :
  A ↠'β B → A ↠'β C → Σ D, B ↠'β D × C ↠'β D
| .betap _ _ h₁, h₂ => ⟨_, (h₁.diamond_aux h₂).2.1, betapr.betap _ _ (h₁.diamond_aux h₂).2.2⟩
| .refl _, h₂ => ⟨_, h₂, betapr.refl _⟩
| .trans _ _ _ h₁ h₂, h₃ => by
  let h₄ := h₁.diamond h₃
  exact ⟨_, (h₂.diamond h₄.2.1).2.1, h₄.2.2.trans _ _ _ (h₂.diamond h₄.2.1).2.2⟩

def betar.diamond {A B C : PTerm S} :
    A ↠β B → A ↠β C → Σ D, B ↠β D × C ↠β D :=
  fun h₁ h₂ ↦ ⟨_, (h₁.betapr.diamond h₂.betapr).2.1.betar,
    (h₁.betapr.diamond h₂.betapr).2.2.betar⟩

def betac.confl {A B : PTerm S} :
    A ≃β B → Σ (C : PTerm S), (A ↠β C) × (B ↠β C)
| .betar _ _ h => ⟨_, h, betar.refl _⟩
| .symm _ _ h => ⟨_, h.confl.2.2, h.confl.2.1⟩
| .trans _ _ _ h₁ h₂ =>
  ⟨_, h₁.confl.2.1.trans _ _ _ (h₁.confl.2.2.diamond h₂.confl.2.1).2.1,
    h₂.confl.2.2.trans _ _ _ (h₁.confl.2.2.diamond h₂.confl.2.1).2.2⟩

alias betac_confl := betac.confl

end Confluence

def betac_of_pi_betac {A B A' B' : PTerm S} (h : Π.A B ≃β Π.A' B') :
    A ≃β A' × B ≃β B' := by
  have := h.confl.2.1.of_pi_betar.eq.symm.trans h.confl.2.2.of_pi_betar.eq
  simp only [pi.injEq] at this
  constructor
  . apply betac.trans
    apply h.confl.2.1.of_pi_betar.betarl.betac
    rw [this.1]
    exact h.confl.2.2.of_pi_betar.betarl.betac.symm
  . apply betac.trans
    apply h.confl.2.1.of_pi_betar.betarr.betac
    rw [this.2]
    exact h.confl.2.2.of_pi_betar.betarr.betac.symm
alias pi_inj := betac_of_pi_betac

def betar_of_betac_sort {s : S.sort} {t : PTerm S} (h : t ≃β (!s)) :
    t ↠β (!s) := by
  let H := h.confl
  rw [← H.2.2.eq_of_sort_betar]
  exact H.2.1

lemma betac.eq_of_sort_betac_sort {s₁ s₂ : S.sort} (h : (!s₁) ≃β (!s₂)) :
    s₁ = s₂ := by
  let H := h.confl
  simpa using H.2.1.eq_of_sort_betar.symm.trans H.2.2.eq_of_sort_betar

end Reduction

section Typing

mutual
inductive wf {S : Specification} : PCtx S → Type _
| nil : wf []
| cons Γ A s : typing Γ A (!s) → wf (A :: Γ)

inductive typing {S : Specification} : PCtx S → PTerm S → PTerm S → Type _
| var Γ A n : wf Γ → (A ↓ n sub Γ) → typing Γ (#n) A
| sort Γ s₁ s₂ (h : S.ax s₁ s₂) : wf Γ → typing Γ (!s₁) (!s₂)
| pi Γ A B s₁ s₂ s₃ (h : S.rel s₁ s₂ s₃) :
    typing Γ A (!s₁) →  typing (A :: Γ) B (!s₂) → typing Γ (Π.A B) (!s₃)
| abs Γ A b B s₁ s₂ s₃ (h : S.rel s₁ s₂ s₃) :
    typing Γ A (!s₁) →  typing (A :: Γ) B (!s₂) → typing (A :: Γ) b B →
      typing Γ (λ.A b) (Π.A B)
| app Γ f A B a :
    typing Γ f (Π.A B) → typing Γ a A → typing Γ (f ⬝ a) (B{a})
| conv Γ a A B s (h : A ≃β B):
    typing Γ a A → typing Γ B (!s) → typing Γ a B

end

notation:20 Γ " ⊢ ⬝ " => wf Γ
notation:20 Γ " ⊢ " a  " : " A => typing Γ a A

variable {S : Specification}

def wf_of_typing : ∀ (_ : Γ ⊢ t : T), Γ ⊢ ⬝
| .var _ _ _ _ _ => by assumption
| .sort _ _ _ _ _ => by assumption
| .pi _ _ _ _ _ _ _ h _ => wf_of_typing h
| .abs _ _ _ _ _ _ _ _ h _ _ => wf_of_typing h
| .app _ _ _ _ _ h _ => wf_of_typing h
| .conv Γ a A B s h₀ h₁ h₂ => wf_of_typing h₁
alias typing.wf := wf_of_typing

lemma exists_of_cons (h : A :: Γ ⊢ ⬝) : ∃ s, Nonempty (Γ ⊢ A : !s) := by
  cases h with
  | cons Γ A s h => exact ⟨s, ⟨h⟩⟩

-- remove it later, substitute by `wf.sort_of_cons`
def exists_of_cons' (h : A :: Γ ⊢ ⬝) : Σs, (Γ ⊢ A : !s) := by
  cases h with
  | cons Γ A s h => exact ⟨s, h⟩

def wf.sort_of_cons {Γ : PCtx S} {A : PTerm S} : (A :: Γ ⊢ ⬝) → S.sort
| .cons Γ A s h => s

def wf.typing_of_cons {Γ : PCtx S} {A : PTerm S} :
    (h : A :: Γ ⊢ ⬝) → (Γ ⊢ A : !(h.sort_of_cons))
| .cons Γ A s h => h

def wf_of_cons (h : A :: Γ ⊢ ⬝) : Γ ⊢ ⬝ :=
  wf_of_typing h.typing_of_cons

open Relation
/-
lemma exists_of_var_typing : ∀ (_ : Γ ⊢ #n : A),
    ∃ B, B ≃β A ∧ (B ↓ n sub Γ)
| .var _ _ _ h₀ h₁ => ⟨A ,⟨EqvGen.refl _, by assumption⟩⟩
| .conv _ _ B _ s h₀ h₁ h₂ => by
    obtain ⟨C, hC⟩ := exists_of_var_typing h₁
    use C
    exact ⟨EqvGen.trans _ _ _ hC.1 h₀, hC.2⟩

def exists_of_sort_typing : ∀ (_ : Γ ⊢ !s : A),
    ∃ t, ((!t) ≃β A) ∧ S.ax s t
| .sort _ _ t h₀ h₁ => ⟨t, ⟨EqvGen.refl _, by assumption⟩⟩
| .conv _ _ B _ s h₀ h₁ h₂ => by
    obtain ⟨C, hC⟩ := exists_of_sort_typing h₁
    use C
    exact ⟨EqvGen.trans _ _ _ hC.1 h₀, hC.2⟩
-/

lemma exists_of_pi_typing : ∀ (_ : Γ ⊢ Π.A B : T),
    ∃ s₁ s₂ s₃, Nonempty (T ≃β !s₃) ∧ S.rel s₁ s₂ s₃ ∧
      Nonempty (Γ ⊢ A : !s₁) ∧ Nonempty (A :: Γ ⊢ B : !s₂)
| .pi _ _ _ s₁ s₂ s₃ h₁ h₂ h₃ => ⟨s₁, s₂, s₃, ⟨betac.refl _⟩, h₁, ⟨h₂⟩, ⟨h₃⟩⟩
| .conv _ _ _ _ _ h₁ h₂ h₃ => by
  obtain ⟨s₁, s₂, s₃, ⟨h₄⟩, h₅, ⟨h₆⟩, ⟨h₇⟩⟩ := exists_of_pi_typing h₂
  exact ⟨s₁, s₂, s₃, ⟨⟨(h₁.symm).trans _ _ _ h₄⟩, h₅, ⟨h₆⟩, ⟨h₇⟩⟩⟩

structure PiTypingStruct {Γ : PCtx S} {A B T : PTerm S} (h : Γ ⊢ Π.A B : T) where
  s₁ : S.sort
  s₂ : S.sort
  s₃ : S.sort
  betac : T ≃β !s₃
  rel : S.rel s₁ s₂ s₃
  typing₁ : Γ ⊢ A : !s₁
  typing₂ : A :: Γ ⊢ B : !s₂

def of_pi_typing : ∀ (h : Γ ⊢ Π.A B : T), PiTypingStruct h
| .pi _ _ _ s₁ s₂ s₃ h₁ h₂ h₃ => ⟨s₁, s₂, s₃, betac.refl _, h₁, h₂, h₃⟩
| .conv _ _ _ _ _ h₁ h₂ h₃ => by
  exact ⟨_, _, _, (h₁.symm).trans _ _ _ (of_pi_typing h₂).betac,
    (of_pi_typing h₂).rel, (of_pi_typing h₂).typing₁, (of_pi_typing h₂).typing₂⟩
alias pi_inversion := of_pi_typing

structure AbsTypingStruct {Γ : PCtx S} {A b T : PTerm S} (h : Γ ⊢ λ.A b : T) where
  s₁ : S.sort
  s₂ : S.sort
  s₃ : S.sort
  type : PTerm S
  betac : T ≃β Π.A type
  rel : S.rel s₁ s₂ s₃
  typing₁ : Γ ⊢ A : !s₁
  typing₂ : A :: Γ ⊢ type : !s₂
  typing₃ : A :: Γ ⊢ b : type

def of_abs_typing : ∀ (h : Γ ⊢ λ.A b : T), AbsTypingStruct h
| .abs _ _ _ _ _ _ _ h₀ h₁ h₂ h₃ => ⟨_, _, _, _, betac.refl _, h₀, h₁, h₂, h₃⟩
| .conv _ _ _ _ _ h₁ h₂ h₃ => by
  exact ⟨_, _, _, _, (h₁.symm).trans _ _ _ (of_abs_typing h₂).betac,
    (of_abs_typing h₂).rel, (of_abs_typing h₂).typing₁,
    (of_abs_typing h₂).typing₂, (of_abs_typing h₂).typing₃⟩
alias abs_inversion := of_pi_typing

/-
def exists_of_abs_typing (h : Derivable (Γ ⊢ λ.A b : T)) :
    ∃ s₁ s₂ s₃, ∃ B, (T ≃β Π.A B) ∧ S.rel s₁ s₂ s₃ ∧
      Derivable (Γ ⊢ A : !s₁) ∧ Derivable (A :: Γ ⊢ b : B) ∧
      Derivable (A :: Γ ⊢ B : !s₂) := by
  generalize hJ : (Γ ⊢ λ.A b : T) = J at h
  induction h generalizing A b T
  all_goals cases hJ
  . rename_i B s₁ s₂ s₃ _ _ _ _ _ _ _
    use s₁, s₂, s₃, B
    exact ⟨EqvGen.refl _, ⟨by assumption, ⟨by assumption, ⟨by assumption, by assumption⟩⟩⟩⟩
  . rename_i h _ _ _ ih
    obtain ⟨s₁, ⟨s₂, ⟨s₃, ⟨B, hs⟩⟩⟩⟩ := ih rfl
    use s₁, s₂, s₃, B
    exact ⟨EqvGen.trans _ _ _ (EqvGen.symm _ _ h) hs.1, hs.2⟩

def exists_of_app_typing (h : Derivable (Γ ⊢ f ⬝ a : T)) :
    ∃ A B, T ≃β B{a} ∧ Derivable (Γ ⊢ f : Π.A B) ∧ Derivable (Γ ⊢ a : A) := by
  generalize hJ : (Γ ⊢ f ⬝ a : T) = J at h
  induction h generalizing f a T
  all_goals cases hJ
  . rename_i A B _ _ _ _ _
    use A, B
    exact ⟨EqvGen.refl _, ⟨by assumption, by assumption⟩⟩
  . rename_i h _ _ _ ih
    obtain ⟨A, ⟨B, h'⟩⟩ := ih rfl
    use A, B
    exact ⟨EqvGen.trans _ _ _ (EqvGen.symm _ _ h) h'.1, h'.2⟩
-/

mutual
def weakening_typing : (Γ ⊢ t : T) → isInsert Δ A n Γ Γ' → (Δ ⊢ A : !s) →
    (Γ' ⊢ t ↑ 1 # n : T ↑ 1 # n)
| .var _ _ k h₀ h₁, h₂, h₃ => by
  dsimp
  split_ifs with h
  . apply typing.var _ _ _ (weakening_wf h₀ h₂ h₃)
      (isItemLift_of_isInsert_of_lt h₂ h h₁)
  . apply typing.var _ _ _ (weakening_wf h₀ h₂ h₃)
    use h₁.1
    conv_lhs => rw [h₁.2]
    . rw [lift_lift_of_le_of_le _ _ _ _ (by simp)
        (by simp at h ⊢; apply h.trans (Nat.le_succ _))]
    . apply isItem_of_isInsert_of_le h₂ (by simpa using h) h₁.3
| .sort _ s₁ s₂ h₀ h₁, h₂, h₃ =>
    typing.sort _ _ _ h₀ (weakening_wf h₁ h₂ h₃)
| .pi _ A B s₁ s₂ s₃ h₀ h₁ h₃, h₄, h₅ =>
  typing.pi _ _ _ _ _ _ h₀ (weakening_typing h₁ h₄ h₅)
    (weakening_typing h₃ (h₄.succ A) h₅)
| .abs _ A b B s₁ s₂ s₃ h₀ h₁ h₂ h₃, h₄, h₅ =>
  typing.abs _ _ _ _ _ _ _ h₀ (weakening_typing h₁ h₄ h₅)
    (weakening_typing h₂ (h₄.succ A) h₅) (weakening_typing h₃ (h₄.succ A) h₅)
| .app _ f B C b h₀ h₁, h₂, h₃ => by
  have : n = 0 + n := by simp
  rw [this, subst_lift]; simp
  apply typing.app _ _ _ _ _ (weakening_typing h₀ h₂ h₃) (weakening_typing h₁ h₂ h₃)
| .conv _ _ B _ s h₀ h₁ h₂, h₃, h₄ =>
  typing.conv _ _ (B ↑ 1 # n) _ _ h₀.lift (weakening_typing h₁ h₃ h₄)
    (weakening_typing h₂ h₃ h₄)

def weakening_wf : Γ ⊢ ⬝ → isInsert Δ A n Γ Γ' → (Δ ⊢ A : !s) → (Γ' ⊢ ⬝ )
| _, .zero, h₃ => wf.cons _ _ _ h₃
| .cons _ _ s _, .succ u (Δ := Γ) (n := n) h₂, h₃ => by
    rename_i h₁ _
    apply wf.cons _ _ s (weakening_typing h₁ h₂ h₃)
end

def weakening_cons {Γ : PCtx S} {t T : PTerm S} {s : S.sort} (h₁ : Γ ⊢ t : T) (h₂ : Γ ⊢ A : !s) :
    A :: Γ ⊢ t ↑ 1 : T ↑ 1 :=
  weakening_typing h₁ isInsert.zero h₂

def weakening_isTrunc {Γ Γ' : PCtx S} {t T : PTerm S} :
  ∀ (_ : isTrunc n Γ Γ') (_ : Γ' ⊢ t : T) (_ : Γ ⊢ ⬝), Γ ⊢ t ↑ n : T ↑ n
| .zero _, _, _ => by simpa
| .succ _ h₀, h₁, h₂ => by
  rw [← lift0_lift0, ← lift0_lift0]
  apply weakening_cons (weakening_isTrunc h₀ h₁ h₂.typing_of_cons.wf) h₂.typing_of_cons

mutual

def substitution_typing : ∀ (_ : Γ ⊢ t : T) (_ : isSubst Δ a A n Γ Γ') (_ : Δ ⊢ a : A),
    Γ' ⊢ t{a//n} : T{a//n}
| .var _ _ k h₀ h₁, h₂, h₃ => by
  dsimp
  split_ifs with h h'
  . apply typing.var _ _ _ (substitution_wf h₀ h₂ h₃)
    use h₁.1{a // n - (k + 1)}
    . conv_lhs => rw [h₁.2]
      rw [subst_lift_of_le _ _ _ (by simp)]
      rw [← Nat.add_sub_assoc h, Nat.add_sub_cancel_left]
    . apply isItem_of_isSubst_of_lt h₂ h h₁.3
  . cases h'
    have : T{a // n} = A ↑ n := by
      obtain ⟨b, h₁, h₁'⟩ := h₁
      rw [eq_of_isSubst_of_isItem h₂ h₁', h₁]
      rw [lift_subst_of_le_of_le 0 _ _ (by simp) (by simp)]
    rw [this]
    apply weakening_isTrunc h₂.isTrunc h₃ (substitution_wf h₀ h₂ h₃)
  . apply typing.var _ _ _ (substitution_wf h₀ h₂ h₃)
    have : 1 ≤ k := by
      apply Nat.add_one_le_of_lt
      apply lt_of_le_of_lt (Nat.zero_le n) (lt_of_le_of_ne (le_of_not_lt h) (Ne.symm h'))
    use h₁.1
    . conv_lhs => rw [h₁.2]
      rw [lift_subst_of_le_of_le 0 _ _ (by simp) (by simpa using h)]
      rw [Nat.sub_add_cancel this]
    . apply isItem_of_isSubst_of_le h₂ _
        (by simpa [Nat.sub_add_cancel this] using h₁.3)
      apply Nat.le_sub_one_of_lt (lt_of_le_of_ne (le_of_not_lt h) (Ne.symm h'))
| .sort _ s₁ s₂ h₀ h₁, h₂, h₃ =>
  typing.sort _ _ _ h₀ (substitution_wf h₁ h₂ h₃)
| .pi _ A B s₁ s₂ s₃ h₀ h₁ h₃, h₄, h₅ =>
  typing.pi _ _ _ _ _ _ h₀ (substitution_typing h₁ h₄ h₅)
    (substitution_typing h₃ (h₄.succ A) h₅)
| .abs _ A b B s₁ s₂ s₃ h₀ h₁ h₂ h₃, h₄, h₅ =>
  typing.abs _ _ _ _ _ _ _ h₀ (substitution_typing h₁ h₄ h₅)
    (substitution_typing h₂ (h₄.succ A) h₅) (substitution_typing h₃ (h₄.succ A) h₅)
| .app _ f B C b h₀ h₁, h₂, h₃ => by
  rw [subst0_subst]
  apply typing.app _ _ _ _ _ (substitution_typing h₀ h₂ h₃) (substitution_typing h₁ h₂ h₃)
| .conv _ _ B _ s h₀ h₁ h₂, h₃, h₄ =>
  typing.conv _ _ (B{a//n}) _ _ h₀.substl (substitution_typing h₁ h₃ h₄)
    (substitution_typing h₂ h₃ h₄)

def substitution_wf : ∀ (_ : Γ ⊢ ⬝ ) (_ : isSubst Δ a A n Γ Γ') (_ : Δ ⊢ a : A), Γ' ⊢ ⬝
| _, .zero, h₃ => h₃.wf
| .cons _ _ s _, .succ (n := n) (Δ := Γ) (Δ' := Γ') u h₂, h₃ => by
  rename_i h₁
  apply wf.cons _ _ s (substitution_typing h₁ h₂ h₃)

end

def typing_of_isItem_of_isTrunc {Γ Γ' : PCtx S} {A : PTerm S} {n : ℕ} :
  ∀ (_ : A ↓ n in Γ) (_ : isTrunc (n + 1) Γ Γ')  (_ : Γ ⊢ ⬝),
    Σ s : S.sort, Γ' ⊢ A : !s
| .zero _, .succ _ (.zero _), .cons _ _ s h => ⟨s, h⟩
| .succ B h₀, .succ _ h₁, h₂ =>
  typing_of_isItem_of_isTrunc h₀ h₁ h₂.typing_of_cons.wf

lemma exists_typing_of_isItem_of_isTrunc {Γ Γ' : PCtx S} {A : PTerm S} {n : ℕ} :
  ∀ (_ : A ↓ n in Γ) (_ : isTrunc (n + 1) Γ Γ')  (_ : Γ ⊢ ⬝),
    ∃ s : S.sort, Nonempty (Γ' ⊢ A : !s)
| h₁, h₂, h₃ => ⟨_, ⟨(typing_of_isItem_of_isTrunc h₁ h₂ h₃).2⟩⟩

def typing_of_isItemLift {Γ : PCtx S} {A : PTerm S} {n : ℕ} :
  ∀ (_ : A ↓ n sub Γ)  (_ : Γ ⊢ ⬝),
    Σ s : S.sort, (Γ ⊢ A : !s) := by
  intro ⟨B, h₁, h₂⟩ h₃
  use (typing_of_isItem_of_isTrunc h₂ h₂.isTrunc.2 h₃).1
  simpa [h₁] using weakening_isTrunc h₂.isTrunc.2
    (typing_of_isItem_of_isTrunc h₂ h₂.isTrunc.2 h₃).2 h₃

lemma exists_typing_of_isItemLift {Γ : PCtx S} {A : PTerm S} {n : ℕ} :
  ∀ (_ : A ↓ n sub Γ)  (_ : Γ ⊢ ⬝),
    ∃ s : S.sort, Nonempty (Γ ⊢ A : !s) := by
  intro ⟨B, h₁, h₂⟩ h₃
  obtain ⟨Γ', ⟨hΓ'⟩⟩ := exists_isTrunc_of_isItem h₂
  obtain ⟨s, ⟨hs⟩⟩ := exists_typing_of_isItem_of_isTrunc h₂ hΓ' h₃
  use s
  constructor
  simpa [h₁] using weakening_isTrunc hΓ' hs h₃

lemma exists_eq_sort_or_typing_sort {Γ : PCtx S} {a A: PTerm S} : ∀ (_ : Γ ⊢ a : A),
    (∃ s : S.sort, A = (!s)) ∨ (∃ s, Nonempty (Γ ⊢ A : !s))
| .var Γ A i h₁ h₂ => by right; exact exists_typing_of_isItemLift h₂ h₁
| .sort Γ s₁ s₂ h₁ h₂ => by left; exact ⟨_, rfl⟩
| .conv _ _ _ _ _ _ _ h => by right; exact ⟨_, ⟨h⟩⟩
| .app _ f A B a h₁ h₂ => by
  rcases exists_eq_sort_or_typing_sort h₁ with ⟨s, h⟩ | ⟨s, ⟨h⟩⟩
  . simp at h
  . right
    obtain ⟨s₁, s₂, s₃, ⟨h₃⟩, h₄, ⟨h₅⟩, ⟨h₆⟩⟩ := exists_of_pi_typing h
    exact ⟨s₂, ⟨substitution_typing h₆ isSubst.zero h₂⟩⟩
| .abs _ _ _ _ _ _ _  h₀ h₁ h₂ _ => by right; exact ⟨_, ⟨typing.pi _ _ _ _ _ _ h₀ h₁ h₂⟩⟩
| .pi _ _ _ _ _ _ _ h₀ h₁ => by left; exact ⟨_, rfl⟩
alias typing_correct := exists_eq_sort_or_typing_sort

lemma exists_typing_sort_of_ne {Γ : PCtx S} {a A: PTerm S} (h₁ : Γ ⊢ a : A)
    (h₂ : ∀ s : S.sort, A ≠ (!s)) : ∃ s, Nonempty (Γ ⊢ A : !s) := by
  rcases exists_eq_sort_or_typing_sort h₁ with ⟨s, h⟩ | h
  . simpa using h₂ s h
  . exact h

def typing_sort_of_ne {Γ : PCtx S} {a A: PTerm S} (h : ∀ s : S.sort, A ≠ !s) :
    ∀ (_ : Γ ⊢ a : A), Σ s, Γ ⊢ A : !s
| .var Γ A i h₁ h₂ => typing_of_isItemLift h₂ h₁
| .sort Γ s₁ s₂ h₁ h₂ => by simp at h
| .conv _ _ _ _ _ _ _ h' => ⟨_, h'⟩
| .abs _ _ _ _ _ _ _  h₀ h₁ h₂ _ => ⟨_, typing.pi _ _ _ _ _ _ h₀ h₁ h₂⟩
| .pi _ _ _ _ _ _ _ h₀ h₁ => by simp at h
| .app _ f A B a h₁ h₂ =>
  ⟨_ , substitution_typing (of_pi_typing (typing_sort_of_ne (by simp) h₁).2).typing₂
    isSubst.zero h₂⟩

def typing_sort_of_pi_typing {Γ : PCtx S} {a A B : PTerm S} :
    ∀ (_ : Γ ⊢ a : Π.A B), Σ s : S.sort, Γ ⊢ Π.A B : !s
| h => typing_sort_of_ne (by simp) h

lemma lift_inv_of_typing : ∀ (_ : Γ ⊢ t : T), (t ↑ 1 # Γ.length) = t
| .var Γ t n h₁ ⟨B, _, h₂⟩ => by simp [h₂.lt_length]
| .sort _ _ _ _ _ => by simp
| .conv _ _ _ _ _ _ h _ => lift_inv_of_typing h
| .app _ _ _ _ _ h₁ h₂ => by
  simp; exact ⟨lift_inv_of_typing h₁, lift_inv_of_typing h₂⟩
| .abs _ _ _ _ _ _ _ _ h₀ _ h₂ => by
  simp; exact ⟨lift_inv_of_typing h₀, lift_inv_of_typing h₂⟩
| .pi _ _ _ _ _ _ _ h₀ h₁ => by
  simp; exact ⟨lift_inv_of_typing h₀, lift_inv_of_typing h₁⟩

lemma lift_inv_of_typing'  (h : Γ ⊢ t : T) :
    (T ↑ 1 # Γ.length) = T := by
  rcases typing_correct h with ⟨_, hs⟩ | ⟨_, ⟨hs⟩⟩
  . simp [hs]
  . apply lift_inv_of_typing hs

lemma lift_inv_of_typing''  (h : T :: Γ ⊢ ⬝) : (T ↑ 1 # Γ.length) = T := by
  cases h
  apply lift_inv_of_typing (by assumption)

def isInsert_length : ∀ {Γ Δ : PCtx S} (_ : Δ ⊢ ⬝ ),
  isInsert Γ A (length Δ) (List.append Δ Γ) (List.append Δ (A :: Γ))
| Γ, [], h => by simp; apply isInsert.zero
| Γ, B :: Δ, h => by
  simp
  convert isInsert.succ _ _
  rw [lift_inv_of_typing'' h]
  apply isInsert_length (wf_of_cons h)

def append_typing : ∀ {Γ Δ : PCtx S} (_ : Γ ⊢ ⬝) (_ : Δ ⊢ t : T),
    List.append Δ Γ ⊢ t : T
| [], Δ, h₁, h₂ => by simpa
| A :: Γ, Δ, wf.cons _ _ s h₁, h₂ => by
  simp
  rw [← lift_inv_of_typing h₂, ← lift_inv_of_typing' h₂]
  apply weakening_typing (append_typing (wf_of_typing h₁) h₂) _ h₁
  apply isInsert_length (wf_of_typing h₂)

def append_wf : ∀ {Γ Δ : PCtx S} (_ : Γ ⊢ ⬝) (_ : Δ ⊢ ⬝), List.append Δ Γ ⊢ ⬝
| _, [], h, _ => h
| _, _ :: _, h₁, .cons _ _ _ h₂ =>
  weakening_wf (append_wf h₁ (wf_of_typing h₂)) isInsert.zero
    (append_typing h₁ h₂)

def weakening_cons_typing {Γ : PCtx S} {A : PTerm S} (h : A :: Γ ⊢ ⬝ ):
    Σs, (A :: Γ) ⊢ A ↑ 1 : !s :=
  ⟨_, weakening_typing (exists_of_cons' h).2 isInsert.zero (exists_of_cons' h).2⟩

end Typing

section beta

open Relation
variable {S : Specification}

namespace PCtx

inductive beta : PCtx S → PCtx S → Type _
| head {A B Γ} : A →β B → beta (A :: Γ) (B :: Γ)
| tail {A Γ Δ} : beta Γ Δ → beta (A :: Γ) (A :: Δ)

infix:50 " →β " => beta

inductive betar : PCtx S → PCtx S → Type _
| beta (x y : PCtx S) : x →β y → betar x y
| refl x : betar x x
| trans x y z : betar x y → betar y z → betar x z

infix:50 " ↠β " => betar

inductive betac : PCtx S → PCtx S → Type _
| betar (x y : PCtx S) : x ↠β y → betac x y
| symm x y : betac x y → betac y x
| trans x y z : betac x y → betac y z → betac x z

infix:50 " ≃β " => betac

variable {Γ Δ : PCtx S} {A B : PTerm S}

def betac.refl (Γ : PCtx S) : Γ ≃β Γ := .betar _ _ (betar.refl Γ)

lemma beta.length_eq : ∀ {Γ Δ : PCtx S} (_ : Γ →β Δ), Γ.length = Δ.length
| A :: Γ, B :: _, .head h => rfl
| A :: Γ, _ :: Δ, .tail h => by simp [h.length_eq]

lemma betar.length_eq {Γ Δ : PCtx S} : ∀ (_ : Γ ↠β Δ), Γ.length = Δ.length
| .beta _ _ h => h.length_eq
| .refl _ => rfl
| .trans _ _ _ h₁ h₂ => h₁.length_eq.trans h₂.length_eq

lemma betac.length_eq {Γ Δ : PCtx S} : ∀ (_ : Γ ≃β Δ), Γ.length = Δ.length
| .betar _ _ h => h.length_eq
| .symm _ _ h => h.length_eq.symm
| .trans _ _ _ h₁ h₂ => h₁.length_eq.trans h₂.length_eq

lemma betar.nil (h : Γ ↠β []) : Γ = [] := by
  simpa using h.length_eq

def betar.head {Γ Δ : PCtx S} {A B : PTerm S} : ∀ (_ : (A :: Γ) ↠β (B :: Δ)), A ↠β B
| .beta _ _ (beta.head h) => PureTypeSystem.betar.beta _ _ h
| .beta _ _ (beta.tail h) => PureTypeSystem.betar.refl _
| .refl _ =>  PureTypeSystem.betar.refl _
| .trans _ [] _ h₁ h₂ => by simpa using h₁.length_eq
| .trans _ (C :: Θ) _ h₁ h₂ => h₁.head.trans _ _ _ h₂.head

def betar.tail {Γ Δ : PCtx S} {A B : PTerm S} : ∀ (_ : (A :: Γ) ↠β (B :: Δ)), Γ ↠β Δ
| .beta _ _ (beta.head h) => betar.refl _
| .beta _ _ (beta.tail h) => betar.beta _ _ h
| .refl _ =>  betar.refl _
| .trans _ [] _ h₁ h₂ => by simpa using h₁.length_eq
| .trans _ (C :: Θ) _ h₁ h₂ => h₁.tail.trans _ _ _ h₂.tail

def _root_.PureTypeSystem.betar.singleton_betar {A B : PTerm S} : ∀ (_ : A ↠β B), [A] ↠β [B]
| .beta _ _ h => by apply betar.beta _ _ (beta.head h)
| .refl _ => by apply betar.refl
| .trans _ _ _ h₁ h₂ => h₁.singleton_betar.trans _ _ _ h₂.singleton_betar

def betar.of_tail_of_eq {A : PTerm S} {Γ Δ : PCtx S} : ∀ (_ : Γ ↠β Δ),
  A :: Γ ↠β A :: Δ
| .beta _ _ h => .beta _ _ (beta.tail h)
| .refl _ => .refl _
| .trans _ _ _ h₁ h₂ =>
  h₁.of_tail_of_eq.trans _ _ _ h₂.of_tail_of_eq

def _root_.PureTypeSystem.betar.of_head_of_eq {A B : PTerm S} {Γ : PCtx S} : ∀ (_ : A ↠β B),
  A :: Γ ↠β B :: Γ
| .beta _ _ h => .beta _ _ (beta.head h)
| .refl _ => .refl _
| .trans _ _ _ h₁ h₂ =>
  h₁.of_head_of_eq.trans _ _ _ h₂.of_head_of_eq

def _root_.PureTypeSystem.betar.of_head_of_tail {A B : PTerm S} {Γ Δ : PCtx S}
  (h₁ : A ↠β B) (h₂ : Γ ↠β Δ) :
    A :: Γ ↠β B :: Δ :=
  h₁.of_head_of_eq.trans _ _ _ h₂.of_tail_of_eq

def betar.of_append : ∀ {Γ Δ Γ' Δ' : PCtx S} (_ : Γ ↠β Δ) (_ : Γ' ↠β Δ'),
  List.append Γ Γ' ↠β List.append Δ Δ'
| [], [], _, _, _, _ => by simpa
| _ :: _, [], _, _, h₁, h₂ => by simpa using h₁.length_eq
| [], _ :: _,  _, _, h₁, h₂ => by simpa using h₁.length_eq
| A :: Γ, B :: Δ, Γ', Δ', h₁, h₂ =>
  h₁.head.of_head_of_tail (h₁.tail.of_append h₂)

def betac.head {Γ Δ : PCtx S} {A B : PTerm S} : ∀ (_ : (A :: Γ) ≃β (B :: Δ)), A ≃β B
| .betar _ _ h => PureTypeSystem.betac.betar _ _ h.head
| .symm _ _ h => PureTypeSystem.betac.symm _ _ h.head
| .trans _ [] _ h₁ h₂ => by simpa using h₁.length_eq
| .trans _ (C :: Θ) _ h₁ h₂ => h₁.head.trans _ _ _ h₂.head

def betac.tail {Γ Δ : PCtx S} {A B : PTerm S} : ∀ (_ : (A :: Γ) ≃β (B :: Δ)), Γ ≃β Δ
| .betar _ _ h => betac.betar _ _ h.tail
| .symm _ _ h => betac.symm _ _ h.tail
| .trans _ [] _ h₁ h₂ => by simpa using h₁.length_eq
| .trans _ (C :: Θ) _ h₁ h₂ => h₁.tail.trans _ _ _ h₂.tail

def betac.tail' : ∀ {Γ Δ : PCtx S} (_ : Γ ≃β Δ), Γ.tail ≃β Δ.tail
| [], [], _ => refl _
| _ :: _, [], h => by simpa using h.length_eq
| [], _ :: _, h => by simpa using h.length_eq
| _ :: _, _ :: _, h => h.tail

def _root_.PureTypeSystem.betac.singleton_betac {A B : PTerm S} : ∀ (_ : A ≃β B), [A] ≃β [B]
| .betar _ _ h => betac.betar _ _ h.singleton_betar
| .symm _ _ h => h.singleton_betac.symm
| .trans _ _ _ h₁ h₂ => h₁.singleton_betac.trans _ _ _ h₂.singleton_betac

def betac.of_tail_of_eq {A : PTerm S} {Γ Δ : PCtx S} : ∀ (_ : Γ ≃β Δ),
  A :: Γ ≃β A :: Δ
| .betar _ _ h => betac.betar _ _ h.of_tail_of_eq
| .symm _ _ h => h.of_tail_of_eq.symm
| .trans _ _ _ h₁ h₂ =>
  h₁.of_tail_of_eq.trans _ _ _ h₂.of_tail_of_eq

def _root_.PureTypeSystem.betac.of_head_of_eq {A B : PTerm S} {Γ : PCtx S} : ∀ (_ : A ≃β B),
  A :: Γ ≃β B :: Γ
| .betar _ _ h => .betar _ _ h.of_head_of_eq
| .symm _ _ h => h.of_head_of_eq.symm
| .trans _ _ _ h₁ h₂ =>
  h₁.of_head_of_eq.trans _ _ _ h₂.of_head_of_eq

def _root_.PureTypeSystem.betac.of_head_of_tail {A B : PTerm S} {Γ Δ : PCtx S}
  (h₁ : A ≃β B) (h₂ : Γ ≃β Δ) :
    A :: Γ ≃β B :: Δ :=
  h₁.of_head_of_eq.trans _ _ _ h₂.of_tail_of_eq

def betac.of_append : ∀ {Γ Δ Γ' Δ' : PCtx S} (_ : Γ ≃β Δ) (_ : Γ' ≃β Δ'),
  List.append Γ Γ' ≃β List.append Δ Δ'
| [], [], _, _, _, _ => by simpa
| _ :: _, [], _, _, h₁, h₂ => by simpa using h₁.length_eq
| [], _ :: _,  _, _, h₁, h₂ => by simpa using h₁.length_eq
| A :: Γ, B :: Δ, Γ', Δ', h₁, h₂ =>
  h₁.head.of_head_of_tail (h₁.tail.of_append h₂)

def betar.lift {i n : ℕ} : ∀ {Γ Δ : PCtx S} (_ : Γ ↠β Δ),
    (Γ ↑↑ i # n) ↠β Δ ↑↑ i # n
| [], [], _ => by simpa
| _ :: _, [], h => by simpa using h.length_eq
| [], _ :: _,  h => by simpa using h.length_eq
| A :: Γ, B :: Δ, h =>
    h.head.lift.of_head_of_tail h.tail.lift

def betac.lift {i n : ℕ} : ∀ {Γ Δ : PCtx S} (_ : Γ ≃β Δ),
    (Γ ↑↑ i # n) ≃β Δ ↑↑ i # n
| [], [], _ => by simpa
| _ :: _, [], h => by simpa using h.length_eq
| [], _ :: _,  h => by simpa using h.length_eq
| A :: Γ, B :: Δ, h =>
    h.head.lift.of_head_of_tail h.tail.lift

end PCtx

end beta

section Morphism

@[simp]
def simulSubst (t : PTerm S) : ℕ → PCtx S → PTerm S
| _, [] => t
| n, A :: Γ => (simulSubst t (n + 1) Γ){A // n}
-- ((simulSubst t (n + 1) Γ) ↑ 1 # (n + 1)){A ↑ 1// n}

@[simp]
def simulSubstCtx : PCtx S → ℕ → PCtx S → PCtx S
| [], _, _ => []
| A :: Γ, n, Δ => simulSubst A (n + Γ.length) Δ :: simulSubstCtx Γ n Δ

@[simp]
lemma simulSubstCtx_nil : ∀ {Γ : PCtx S} {n}, simulSubstCtx Γ n [] = Γ
| [], _ => rfl
| A :: Γ, _ => by simp only [simulSubstCtx, simulSubst, simulSubstCtx_nil]

@[simp]
lemma simulSubst_sort {s : S.sort} {n : ℕ} : ∀ {Γ : PCtx S},
    simulSubst (!s) n Γ = (!s : PTerm S)
| [] => rfl
| _ :: _ => by dsimp [simulSubst]; rw [simulSubst_sort]; rfl

lemma simulSubst_pi {A B : PTerm S} {n : ℕ} : ∀ {Γ : PCtx S},
    simulSubst (Π.A B) n Γ = Π. (simulSubst A n Γ) (simulSubst B (n + 1) Γ)
| [] => rfl
| C :: Γ => by simp [simulSubst]; rw [simulSubst_pi]; rfl

lemma simulSubst_abs {A B : PTerm S} {n : ℕ} : ∀ {Γ : PCtx S},
    simulSubst (λ.A B) n Γ = λ. (simulSubst A n Γ) (simulSubst B (n + 1) Γ)
| [] => rfl
| C :: Γ => by simp [simulSubst]; rw [simulSubst_abs]; rfl

lemma simulSubst_app {A B : PTerm S} {n : ℕ} : ∀ {Γ : PCtx S},
    simulSubst (A ⬝ B) n Γ = (simulSubst A n Γ) ⬝ (simulSubst B n Γ)
| [] => rfl
| C :: Γ => by simp [simulSubst]; rw [simulSubst_app]; rfl

lemma simulSubst_append {t : PTerm S} {n : ℕ} : ∀ {Γ Δ : PCtx S},
    simulSubst t n (List.append Γ Δ) =
      simulSubst (simulSubst t (n + Γ.length) Δ) n Γ
| [], _ => rfl
| A :: Γ, Δ => by
  simp; erw [simulSubst_append, Nat.add_assoc, Nat.add_comm 1]

def betac.simulSubst {A B : PTerm S} (h : A ≃β B) {n : ℕ} :
  ∀ {F : PCtx S}, simulSubst A n F ≃β simulSubst B n F
| [] => h
| _ :: _ => h.simulSubst.substl

def PCtx.betac.simulSubst {A : PTerm S} {n : ℕ} :
  ∀ {F F' : PCtx S} (_ : F ≃β F'), simulSubst A n F ≃β simulSubst A n F'
| [], [], _ => by simp; apply PureTypeSystem.betac.refl _
| _ :: _, [], h => by simpa using h.length_eq
| [], _ :: _, h => by simpa using h.length_eq
| f :: F, f' :: F', h => h.tail.simulSubst.subst h.head

def simulSubst_betac {A B : PTerm S} {F G : PCtx S} {n : ℕ}
  (h₁ : A ≃β B) (h₂ : F ≃β G) :
    simulSubst A n F ≃β simulSubst B n G :=
  h₁.simulSubst.trans _ _ _ h₂.simulSubst

inductive isSimulSubst : PCtx S → ℕ → PCtx S → PCtx S → Type _
| nil Γ n : isSimulSubst Γ n [] Γ
| cons Γ n f F Γ' Γs Δ A s :
  isSimulSubst Γ' (n + 1) F Γ → isTrunc (n + 1) Γ Γs →
  (Γs ⊢ A : !s) → (Γs ⊢ f : A) → -- isInsert Γs A (n + 1) Γ Γ₁ →
  isSubst Γs f A n Γ Δ → isSimulSubst Γ' n (f :: F) Δ

def simulSubst_wf (h : Γ' ⊢ ⬝) : ∀ (_ : isSimulSubst Γ' n F Γ),
    Γ ⊢ ⬝
| .nil Γ n => h
| .cons _ n f F Γ' _ Δ _ _ h₁ h₂ h₃ h₄ h₅ =>
  substitution_wf (simulSubst_wf h h₁) h₅ h₄

def simulSubst_typing (h : Γ' ⊢ t : T) : ∀ (_ : isSimulSubst Γ' n F Γ),
    Γ ⊢ simulSubst t n F : simulSubst T n F
| .nil Γ n => h
| .cons _ n f F Γ' _ Δ _ _ h₁ h₂ h₃ h₄ h₅ =>
  substitution_typing (simulSubst_typing h h₁) h₅ h₄

inductive isMor (Γ : PCtx S) : PCtx S → PCtx S → Type _
| nil : isMor Γ [] []
| cons : isMor Γ Δ F → (Γ ⊢ simulSubst D 0 F : !s) →
    (Γ ⊢ f : (simulSubst D 0 F)) → isMor Γ (D :: Δ) (f :: F)

lemma isMor.of_mor_nil {Γ Δ : PCtx S} (h : isMor Γ Δ []) :
    Δ = [] := by
  cases h; rfl

lemma isMor.of_nil {Γ F : PCtx S} (h : isMor Γ [] F) :
    F = [] := by
  cases h; rfl

lemma isMor.length_eq {Γ : PCtx S} : ∀ {Δ F : PCtx S} (_ : isMor Γ Δ F), Δ.length = F.length
| _, [], h => by cases h.of_mor_nil; rfl
| [], _, h => by cases h.of_nil; rfl
| _ :: _, _ :: _, .cons h _ _ => by simp [h.length_eq]

def isMor.of_cons {Γ Δ F : PCtx S} {D f : PTerm S} :
  ∀ (_ : isMor Γ (D :: Δ) (f :: F)), isMor Γ Δ F
| .cons h _ _ => h

def isMor.typing_of_cons {Γ Δ F : PCtx S} {D f : PTerm S} :
  ∀ (_ : isMor Γ (D :: Δ) (f :: F)), Γ ⊢ f : (simulSubst D 0 F)
| .cons _ _ h => h

def isMor.typing_sort_of_cons {Γ Δ F : PCtx S} {D f : PTerm S} :
  ∀ (_ : isMor Γ (D :: Δ) (f :: F)), Σ(s : S.sort), Γ ⊢ simulSubst D 0 F : !s
| .cons _ h _ => ⟨_, h⟩

lemma isSubst.length_eq_add_one {Γ Δ Δ' : PCtx S} : ∀ (_ : isSubst Γ f A n Δ Δ'),
  Δ.length = Δ'.length + 1
| .zero => by simp
| .succ _ h => by simp; apply length_eq_add_one h

lemma isSubst.length_lt {Γ Δ Δ' : PCtx S} (h : isSubst Γ f A n Δ Δ') :
    Δ'.length < Δ.length := by
  rw [length_eq_add_one h]
  simp only [Nat.lt_add_one]

lemma isSimulSubst.length_le {Γ F Δ : PCtx S} : ∀ (_ : isSimulSubst Γ n F Δ),
    Δ.length ≤ Γ.length
| .nil Γ n => le_refl _
| .cons _ n f F Γ' _ Δ _ _ h₁ h₂ h₃ h₄ h₅ =>
  h₅.length_lt.le.trans h₁.length_le

lemma isSimulSubst.nil_of_nil {F Δ : PCtx S} (h : isSimulSubst [] n F Δ) :
    Δ = [] := by
  apply List.eq_nil_of_length_eq_zero
  apply Nat.eq_zero_of_le_zero
  apply h.length_le

def isSimulSubst.append (A : PTerm S) : ∀ {Γ Θ F} (_ : isSimulSubst Γ k F Θ),
  isSimulSubst (A :: Γ) (k + 1) F ((simulSubst A k F) :: Θ)
| Γ, Θ, [], h => by cases h; apply nil
| Γ, Θ, f :: F, .cons Γ' _ _ _ _ Γs _ C s h₁ h₂ h₃ h₄ h₅ => by
  simp
  apply cons
  apply h₁.append
  apply h₂.succ
  apply h₃
  apply h₄
  apply isSubst.succ _ h₅

def isSimulSubst.drop : ∀ {Γ Δ F} (_ : isSimulSubst (D :: Γ) (k + 1) F (A :: Δ)),
  isSimulSubst Γ k F Δ
| Γ, Δ, [], h => by cases h; apply nil
| Γ, Δ, f :: F, .cons _ _ _ _ _ _ _ _ _ h₁ (isTrunc.succ _ h₂) h₃ h₄ (isSubst.succ _ h₅) =>
  cons _ _ _ _ _ _ _ _ _ h₁.drop h₂ h₃ h₄ h₅

def isTrunc.eq : ∀ {Γ Δ Δ' : PCtx S} {k : ℕ}
  (_ : isTrunc k Γ Δ) (_ : isTrunc k Γ Δ'), Δ = Δ'
| _, _, _, 0, .zero _, .zero _ => rfl
| _ :: _, _, _, _ + 1, .succ _ h₁, .succ _ h₂ => h₁.eq h₂

def isSubst.eq : ∀ {Γ Δ Θ Θ' : PCtx S} {f B B' : PTerm S} {k : ℕ}
  (_ : isSubst Γ f B k Δ Θ) (_ : isSubst Γ f B' k Δ Θ'), Θ = Θ'
| _, _, _, _, _, _, _, 0, .zero, .zero => rfl
| _, _, _, _, _, _, _, _ + 1, .succ _ h₁, .succ _ h₂ => by
  rw [h₁.eq h₂]

def isSimulSubst.eq : ∀ {Γ Δ Δ' F : PCtx S}
  (_ : isSimulSubst Γ k F Δ) (_ : isSimulSubst Γ k F Δ'), Δ = Δ'
| Γ, Δ, Δ', [], h₃, h₄ => by cases h₃; cases h₄; rfl
| Γ, Δ, Δ', f :: F,
  .cons Γ₀ _ _ _ _ Γs _ B s h₃ h₄ h₅ h₆ h₇,
  .cons Γ₀' _ _ _ _ Γs' _ B' s' h₃' h₄' h₅' h₆' h₇' => by
  cases h₃.eq h₃'
  cases h₄.eq h₄'
  apply h₇.eq h₇'

abbrev isMor' (Γ Δ F : PCtx S) : Type _ := isSimulSubst (List.append Δ Γ) 0 F Γ

def isMor'_isMor : ∀ {Γ Δ F : PCtx S} (_ : isMor Γ Δ F), isMor' Γ Δ F
| _, [], _, h => by cases h; apply isSimulSubst.nil
| _, _, [], h => by cases h; apply isSimulSubst.nil
| Γ, D :: Δ, f :: F, isMor.cons h₁ h₂ h₃ => by
  apply isSimulSubst.cons
  apply (isMor'_isMor h₁).append
  apply isTrunc.succ _ (isTrunc.zero _)
  have := isMor'_isMor h₁
  simp [isMor'] at this
  apply h₂
  apply h₃
  apply isSubst.zero

lemma test₂ {Γ Δ F : PCtx S} : ∀ (_ : isSimulSubst Γ n Δ F), Γ.length = Δ.length + F.length
| .nil _ _ => by simp
| .cons Γ n f F Γ' Γs Δ A s h₁ h₂ h₃ h₄ h₅ => by
  rw [test₂ h₁, h₅.length_eq_add_one]
  simp
  rw [Nat.add_comm _ 1, ← Nat.add_assoc]

lemma test₄ {Γ Δ : PCtx S} (h : isMor' Γ Δ []) : Δ = [] := by
  simpa using test₂ h

lemma test₅ {Γ F : PCtx S} (h : isMor' Γ [] F) : F = [] := by
  simpa using test₂ h

def isMor_isMor' : ∀ {Γ Δ F : PCtx S} (_ : isMor' Γ Δ F), isMor Γ Δ F
| Γ, [], F, h => by cases test₅ h; apply isMor.nil
| Γ, Δ, [], h => by cases test₄ h; apply isMor.nil
| Γ, D :: Δ, f :: F,
  isSimulSubst.cons _ _ _ _ _ _ _ A s h₁ h₂ h₃ h₄ isSubst.zero  => by
  rw [(List.cons.inj (h₁.eq (h₁.drop.append _))).1] at h₃ h₄
  apply isMor.cons (isMor_isMor' h₁.drop) h₃ h₄

lemma testsimulsubstsubst (i k : ℕ) : ∀ {F : PCtx S},
    simulSubst T (i + k + 2) F{simulSubst g (i + 1) F // k} =
      simulSubst (T{g // k}) (i + k + 1) F
| [] => by simp
| f :: F => by
  simp
  have : i + k + 2 = i + 1 + k + 1 := by
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_left_cancel_iff, Nat.add_comm 1]
    -- I don't want to import linarith... so
  rw [this, ← subst_subst (i + 1) k]
  congr 1
  rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc]
  apply testsimulsubstsubst

lemma liftaux (hn : k ≤ n) : ∀ {t : PTerm S} (_ : (t ↑ 1 # k) = t) , t{f//n} = t
| .var i, h => by simp at h; simp only [subst, if_pos (lt_of_lt_of_le h hn)]
| .sort _, h => rfl
| .pi _ _, h => by
  simp at h ⊢
  exact ⟨liftaux hn h.1, liftaux (Nat.succ_le_succ hn) h.2⟩
| .abs _ _, h => by
  simp at h ⊢
  exact ⟨liftaux hn h.1, liftaux (Nat.succ_le_succ hn) h.2⟩
| .app _ _, h => by
  simp at h ⊢
  exact ⟨liftaux hn h.1, liftaux hn h.2⟩

lemma liftinv {t: PTerm S} (hn : k ≤ n) : ∀ {F : PCtx S} (_ : (t ↑ 1 # k) = t),
  simulSubst t n F = t
| [], _ => by rfl
| f :: F, h => by
  simp; rw [liftinv (hn.trans (Nat.le_succ _)) h]
  apply liftaux hn h

/-
the following is wrong! k is given by the info of `θ ⊢ T : !s`

lemma simulSubst_pcomp {T : PTerm S} : ∀ {F G : PCtx S} ,
  simulSubst T k (pcomp F G) = simulSubst (simulSubst T k G) k F
| F, [] => by
  simp [liftinv]
  sorry
| [], g :: G => by
  simp
  rw [simulSubst_pcomp]
  rfl
| f :: F, g :: G => by
  simp
  rw [simulSubst_pcomp]
  simp
  have : k + 1 = 0 + k + 1 := by simp
  rw [this, ← subst_subst 0 k]
  simp
  congr
  convert testsimulsubstsubst 0 k using 3
  simp only [Nat.zero_add]
-/

section pcomp

def pcomp : PCtx S → PCtx S → PCtx S
| _, [] => []
| F, g :: G =>  simulSubst g 0 F :: pcomp F G

@[simp]
lemma nil_pcomp : ∀ {G : PCtx S}, pcomp [] G = G
| [] => rfl
| g :: G => by simp [pcomp]; rw [nil_pcomp]

lemma simulSubst_pcomp {Γ Δ Θ Θ': PCtx S} {T : PTerm S} (h : (T ↑ 1 # length Θ') = T):
  ∀ {F G : PCtx S} (_ : isMor Γ Δ F) (_ : isMor Δ Θ G) (_ : isTrunc k Θ' Θ),
  simulSubst T k (pcomp F G) = simulSubst (simulSubst T k G) k F
| F, [], h₁, h₂, h₃ => by
  simp
  cases h₂
  rw [liftinv (le_refl _)]
  rw [← h₃.nil_length]
  apply h
| [], G, h₁, h₂, h₃ => by
  cases h₁
  simp
| f :: F, g :: G, h₁, isMor.cons h₂ h₃ h₄, h₅ => by
  simp
  rw [simulSubst_pcomp h h₁ h₂ (isTrunc.pred h₅)]
  simp
  have : k + 1 = 0 + k + 1 := by simp
  rw [this, ← subst_subst 0 k]
  simp
  congr
  convert testsimulsubstsubst 0 k using 3
  simp only [Nat.zero_add]

def pcomp_isMor {Γ : PCtx S} : ∀ {Δ Θ F G : PCtx S} (_ : Γ ⊢ ⬝) (_ : Θ ⊢ ⬝)
    (_ : isMor Γ Δ F) (_ : isMor Δ Θ G),
  isMor Γ Θ (pcomp F G)
| Δ, θ, F, [], _, _, h₁, h₂ => by cases h₂; apply isMor.nil
| Δ, [], F, g :: G, _, _, h₁, h₂ => by cases h₂
| Δ, T :: Θ , F, g :: G, hΓ, hΘ, h₁, isMor.cons h₂ h₃ h₄ => by
  apply isMor_isMor'
  simp [isMor']
  apply isSimulSubst.cons
  apply isSimulSubst.append
  apply isMor'_isMor
  apply pcomp_isMor hΓ (wf_of_cons hΘ) h₁ h₂
  apply isTrunc.succ _ (isTrunc.zero _)
  simpa [simulSubst_sort] using simulSubst_typing (append_typing hΓ h₃) (isMor'_isMor h₁)
  apply simulSubst_typing (append_typing hΓ h₄) (isMor'_isMor h₁)
  convert isSubst.zero using 2
  apply simulSubst_pcomp (lift_inv_of_typing'' hΘ) h₁ h₂ (isTrunc.zero _)

end pcomp

section id


@[simp]
def idN : ℕ → ℕ → PCtx S
| _, 0 => []
| n, k + 1 => (#n) :: (idN (n + 1) k)

def id₀ (n : ℕ) (Γ : PCtx S) : PCtx S := idN n Γ.length

def id (Γ : PCtx S) : PCtx S := id₀ 0 Γ

@[simp]
lemma idN_length {n} : ∀ {k}, (idN n k : PCtx S).length = k
| 0 => rfl
| k + 1 => by simp [idN_length]

lemma idN_lift {n i c: ℕ} (h : c ≤ n) : ∀ {k}, ((idN n k : PCtx S) ↑↑ i # c) = idN (n + i) k
| 0 => rfl
| k + 1 => by
    simp [PCtx.lift, if_neg h.not_lt]
    congr
    have : n + i + 1 = n + 1 + i := by rw [Nat.add_assoc, Nat.add_comm i, ← Nat.add_assoc]
    rw [this]
    apply idN_lift (h.trans (Nat.le_succ _))

lemma idN_append_idN : ∀ (n k m : ℕ),
  List.append (idN n k : PCtx S) (idN (n + k) m) = idN n (k + m)
| _, 0, _ => by simp
| n, k + 1, m => by
  rw [Nat.add_assoc, Nat.add_comm 1 m]; simp
  rw [Nat.add_comm k 1, ← Nat.add_assoc]
  apply idN_append_idN

lemma simulSubst_var_of_lt {n l : ℕ} (hl : n < l) : ∀ (F : PCtx S) ,
    simulSubst (#n : PTerm S) l F = (#n)
| [] => rfl
| f :: F => by
  simp; rw [simulSubst_var_of_lt (hl.trans (Nat.lt_succ_self _))]
  simp [hl]

lemma simulSubst_var_of_length_add_le {n : ℕ} : ∀ {F : PCtx S} (_ : F.length + l ≤ n),
    simulSubst (#n) l F = (#n - F.length)
| [], h => by simp
| f :: F, h => by
  simp
  rw [simulSubst_var_of_length_add_le (by simpa only [Nat.add_comm l, ← Nat.add_assoc])]
  have : l < n - F.length := by
    rw [Nat.lt_sub_iff_add_lt, ← Nat.succ_le_iff]
    convert h using 1
    simp [Nat.add_comm l, Nat.add_assoc]
  simp [if_neg (not_lt_of_lt this), if_neg this.ne.symm, Nat.sub_sub]

lemma simulSubst_var_idN_of_length_add_le {n m l s : ℕ} (h : s + l ≤ n) :
    simulSubst (#n : PTerm S) l (idN m s)  = (#n - s) := by
  convert simulSubst_var_of_length_add_le (F := idN m s) _
  simp; simpa using h

lemma simulSubst_lift_of_length_add_le {F : PCtx S} :
  ∀ (f : PTerm S), simulSubst (f ↑ F.length # l) l F = f
| .var i => by
  rcases lt_or_le i l with hl | hl
  . simp [hl]
    rw [simulSubst_var_of_lt hl]
  . rcases hl.lt_or_eq with h | h
    . simp [if_neg h.not_lt]
      rw [simulSubst_var_of_length_add_le (by simpa [Nat.add_comm])]
      simp only [Nat.add_sub_cancel]
    . simp [h]
      rw [simulSubst_var_of_length_add_le (by simp [Nat.add_comm])]
      simp only [Nat.add_sub_cancel]
| .sort _ => by simp [simulSubst_sort]
| .pi _ _ => by
  simp [simulSubst_pi, simulSubst_lift_of_length_add_le]
| .abs _ _ => by
  simp [simulSubst_abs, simulSubst_lift_of_length_add_le]
| .app _ _ => by
  simp [simulSubst_app, simulSubst_lift_of_length_add_le]

lemma simulSubst_var_of_isTrunc {f : PTerm S} {F G : PCtx S} (h : isTrunc k F (f :: G)) :
    simulSubst (#k) 0 F = f := by
  rw [← h.heads_append, simulSubst_append]; simp
  rw [simulSubst_var_of_lt (by simp)]; simp
  simp only [← h.heads_length]
  apply simulSubst_lift_of_length_add_le

-- can be strengthened???? `n ≤ s`
lemma simulSubst_var_idN_of_lt_length {n k l : ℕ} {s : ℕ} (hn : n < s) :
    simulSubst (#n : PTerm S) l (idN k s) = (#n) ↑ k # l := by
  rcases lt_or_le n l with hl | hl
  . simp [hl, simulSubst_var_of_lt hl _]
  . obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hl
    have aux₁ : (idN k s : PCtx S) = List.append (idN k a) (idN (k + a) (s - a)) := by
      convert (idN_append_idN k a (s - a)).symm
      rw [Nat.add_sub_of_le]
      apply le_trans _ hn.le
      simp only [ha, Nat.le_add_left]
    have aux₂ : idN (k + a) (s - a) = (#k + a : PTerm S) :: (idN (k + a + 1) (s - (a + 1))) := by
      have : s - a = s - (a + 1) + 1 := by
        rw [← Nat.sub_add_comm, Nat.add_sub_add_right]
        apply le_trans _ hn
        simp [ha]
      rw [this]; rfl
    rw [aux₁, aux₂]
    erw [simulSubst_append] -- no!!
    simp [if_neg (not_lt_of_le hl)]
    rw [simulSubst_var_of_lt (by simp only [ha, Nat.lt_add_one]) _]
    simp [ha]
    rw [simulSubst_var_idN_of_length_add_le
      (by rw [← Nat.add_assoc, Nat.add_assoc k, Nat.add_comm k,
        Nat.add_assoc]; simp only [Nat.le_add_right])]
    rw [Nat.add_sub_assoc (by simp), Nat.add_sub_self_right, Nat.add_assoc, Nat.add_comm,
        Nat.add_comm a]

lemma simulSubst_var_id₀_of_lt_length {n k l : ℕ} {Γ : PCtx S} (hn : n < Γ.length) :
    simulSubst (#n) l (id₀ k Γ) = (#n) ↑ k # l :=
  simulSubst_var_idN_of_lt_length hn

lemma isMorAuxLift' {k l m} : ∀ {A : PTerm S} (_ : (A ↑ 1 # l + m) = A),
    simulSubst A l (idN k m) = simulSubst A l (idN k (m + 1))
| .var i, h => by
    rw [← idN_append_idN k m 1, simulSubst_append]
    congr
    have : i < l + m := by simpa using h
    simp [this]
| .sort s, _ => by simp [simulSubst_sort]
| .pi A B, h => by
    simp only [lift, pi.injEq, simulSubst_pi, subst] at h ⊢
    refine ⟨isMorAuxLift' h.1, isMorAuxLift' ?_⟩
    convert h.2 using 1
    rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc]
| .abs A B, h => by
    simp only [lift, abs.injEq, simulSubst_abs, subst] at h ⊢
    refine ⟨isMorAuxLift' h.1, isMorAuxLift' ?_⟩
    convert h.2 using 1
    rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc]
| .app A B, h => by
    simp only [lift, app.injEq, simulSubst_app, subst] at h ⊢
    refine ⟨isMorAuxLift' h.1, isMorAuxLift' h.2⟩

lemma test2 {k l} (h : k ≤ l) : ∀ {A : PTerm S} (_ : (A ↑ 1 # k) = A), (A ↑ 1 # l) = A
| .var i, h' => by simp at h' ⊢; apply lt_of_lt_of_le h' h
| .sort s, _ => rfl
| .pi _ _, h' => by simp at h' ⊢; exact ⟨test2 h h'.1, test2 (by simpa) h'.2⟩
| .abs _ _, h' => by simp at h' ⊢; exact ⟨test2 h h'.1, test2 (by simpa) h'.2⟩
| .app _ _, h' => by simp at h' ⊢; exact ⟨test2 h h'.1, test2 h h'.2⟩

lemma isMorAuxLift {k l m} : ∀ {A : PTerm S} (_ : (A ↑ 1 # m) = A),
    simulSubst A l (idN k m) = A ↑ k # l
-- `A` has only var from `0` to `Δ.length - 1`; so `A ↑ Δ.length = A`
| .var i, h => by
    rw [simulSubst_var_idN_of_lt_length]
    simpa using h
| .sort s, _ => by simp [simulSubst_sort]
| .pi A B, h => by
    simp [simulSubst_pi] at h ⊢
    constructor
    apply isMorAuxLift h.1
    rw [isMorAuxLift' (by refine test2 ?_ h.2; rw [Nat.add_assoc, Nat.add_comm 1]; simp)]
    apply isMorAuxLift h.2
| .abs A B, h => by
    simp [simulSubst_abs] at h ⊢
    constructor
    apply isMorAuxLift h.1
    rw [isMorAuxLift' (by refine test2 ?_ h.2; rw [Nat.add_assoc, Nat.add_comm 1]; simp)]
    apply isMorAuxLift h.2
| .app A B, h => by
    simp [simulSubst_app] at h ⊢
    exact ⟨isMorAuxLift h.1, isMorAuxLift h.2⟩

def simulSubst_id_of_cons_wf :
    (_ : A :: Γ ⊢ ⬝) → simulSubst A 0 (id Γ) = A
| .cons _ _ _ h => by
  simp [id, id₀]
  rw [isMorAuxLift, lift_zero]
  apply lift_inv_of_typing h

def simulSubst_id_of_typing {Γ : PCtx S} {f A : PTerm S} (h : Γ ⊢ f : A) :
    simulSubst f 0 (id Γ) = f := by
  simp [id, id₀]
  rw [isMorAuxLift, lift_zero]
  apply lift_inv_of_typing h

def wf_of_isTrunc {k} {Γ Δ : PCtx S} : ∀ (_ : isTrunc k Γ Δ) (_ : Γ ⊢ ⬝),
    Δ ⊢ ⬝
| .zero _, h => h
| .succ _ _, h => by
  apply wf_of_isTrunc (by assumption)
  cases h
  apply wf_of_typing (by assumption)

def isMorAux {k} {Γ Δ : PCtx S} {A} (h₀ : isTrunc k Γ (A :: Δ)) (h₁ : Γ ⊢ ⬝) :
    Γ ⊢ #k : simulSubst A 0 (id₀ (k + 1) Δ) :=
  typing.var _ _ _ h₁ ⟨A,
    isMorAuxLift (lift_inv_of_typing (wf_of_isTrunc h₀ h₁).typing_of_cons), isTrunc.isItem h₀⟩

def id₀_isMor : ∀ {Γ Δ : PCtx S} (_ : isTrunc k Γ Δ) (_ : Γ ⊢ ⬝), isMor Γ Δ (id₀ k Δ)
| Γ, [], h, h' => by apply isMor.nil
| Γ, A :: Δ, h, h' => by
    apply isMor.cons
    apply id₀_isMor (isTrunc.pred h) h'
    simpa [simulSubst_sort] using simulSubst_typing
      (append_typing h' (exists_of_cons' (wf_of_isTrunc h h')).snd)
      (isMor'_isMor (id₀_isMor (isTrunc.pred h) h'))
    apply isMorAux h h'

def id₀_isMor_tail : ∀ {Γ : PCtx S} (_ : Γ ⊢ ⬝), isMor Γ Γ.tail (id₀ 1 Γ.tail)
| [], _ => isMor.nil
| A :: Γ, h => by apply id₀_isMor (isTrunc.succ _ (isTrunc.zero _)) h

def id_isMor (Γ : PCtx S) (h : Γ ⊢ ⬝) :
    isMor Γ Γ (id Γ) :=
  id₀_isMor (isTrunc.zero _) h

end id

section
-- weakening of isMor

lemma simulSubst_lift {A : PTerm S} {k : ℕ}  :
  ∀ {F : PCtx S} (_ : (A ↑ 1 # k + F.length) = A),
    ((simulSubst A k F) ↑ 1 # k) = simulSubst A k (F ↑↑ 1)
| [], h => by simpa
| f :: F, h => by
  simp
  conv_lhs =>
    congr
    . skip
    . rw [← Nat.add_zero k]
    . skip
  rw [subst_lift]
  congr
  simp
  apply simulSubst_lift
  convert h using 2
  simp only [length_cons]
  rw [Nat.add_comm F.length, Nat.add_assoc]

/-
def isMor.weakening {Γ Θ : PCtx S} {n : ℕ} (h₁ : Γ ⊢ ⬝) (h₂ : Θ ⊢ A : !s) :
  ∀ {Δ F : PCtx S} (_ : isInsert Θ A n Γ Γ') (_ : isMor Γ Δ F), isMor Γ' Δ (F ↑↑ 1 # n)
| _, _, _, .nil => nil
| D :: Δ, f :: F, h₃, .cons h₄ h₅ h₆ => by
  let hΓ' := weakening_wf h₁ h₃ h₂
  apply isMor.cons (h₄.weakening h₁ h₂ h₃)
  #check simulSubst_typing _ (isMor'_isMor (h₄.weakening h₁ h₂ h₃))

  #check weakening_typing h₅ h₃ h₂
-/

-- can be generalized to the previous one; but needs more specific lift lemmas...
def isMor.weakening_cons {Γ : PCtx S} (h : (A :: Γ) ⊢ ⬝) :
  ∀ {Δ F : PCtx S} (_ : Δ ⊢ ⬝) (_ : isMor Γ Δ F), isMor (A :: Γ) Δ (F ↑↑ 1)
| _, _, _, .nil => nil
| D :: Δ, f :: F, h₀, .cons h₁ h₂ h₃ => by
  have : ((simulSubst D 0 F) ↑ 1) = simulSubst D 0 (F ↑↑ 1) := by
    apply simulSubst_lift
    simp [← h₁.length_eq]
    apply lift_inv_of_typing (exists_of_cons' h₀).snd
  apply isMor.cons (h₁.weakening_cons h (wf_of_cons h₀))
  rw [← this]; exact weakening_typing h₂ isInsert.zero (exists_of_cons' h).snd
  rw [← this]; exact weakening_typing h₃ isInsert.zero (exists_of_cons' h).snd

end

section

-- invariance of lift for PCtx

lemma lift_inv_of_isMor {Γ : PCtx S} : ∀ {Δ F : PCtx S} (_ : isMor Γ Δ F),
  (F ↑↑ 1 # Γ.length) = F
| _, [], h => by rfl
| D :: Δ, f :: F, .cons h₁ h₂ h₃ => by
  simp [PCtx.lift]
  congr
  . exact lift_inv_of_typing h₃
  . apply lift_inv_of_isMor h₁

end

section

-- `(f ∘ g, #0) = (f, #0) ∘ (g, #0)`
lemma zero_cons_pcomp_zero_cons_aux₁ {g : PTerm S} : ∀ {F : PCtx S} ,
    simulSubst (g ↑ 1) (k + 1) F = (simulSubst g k F) ↑ 1
| [] => by simp
| f :: F => by
  simp
  rw [zero_cons_pcomp_zero_cons_aux₁, subst_lift_of_le _ _ _ (by simp), Nat.add_comm k]

lemma zero_cons_pcomp_zero_cons_aux₂ {F : PCtx S} : ∀ {G : PCtx S}
  (_ : (G ↑↑ 1 # F.length) = G),
    pcomp ((#0) :: F ↑↑ 1) (G ↑↑ 1) = pcomp F G ↑↑ 1
| [], h => by rfl
| g :: G, h => by
  simp [PCtx.lift] at h
  rw [List.cons.injEq] at h
  simp [pcomp]
  congr 1
  . rw [simulSubst_lift (by simpa using h.1)]
    rw [zero_cons_pcomp_zero_cons_aux₁, lift_subst_of_le_of_le 0 _ _ (by simp) (by simp),
      lift_zero]
  . apply zero_cons_pcomp_zero_cons_aux₂ h.2

lemma zero_cons_pcomp_zero_cons {F G : PCtx S} (h : (G ↑↑ 1 # F.length) = G) :
    pcomp ((#0) :: F ↑↑ 1) ((#0) :: G ↑↑ 1) = (#0) :: (pcomp F G) ↑↑ 1 := by
  simp [pcomp]
  congr 1
  . rw [simulSubst_var_of_lt (by simp)]; rfl
  . apply zero_cons_pcomp_zero_cons_aux₂ h

lemma cons_pcomp_lift_one {F : PCtx S} : ∀ {G : PCtx S},
    pcomp (A :: F) (G ↑↑ 1) = pcomp F G
| [] => by rfl
| g :: G => by
  simp [pcomp]
  congr 1
  . rw [zero_cons_pcomp_zero_cons_aux₁, lift_subst_of_le_of_le 0 _ _ (by simp) (by simp),
      lift_zero]
  . apply cons_pcomp_lift_one

end

section

lemma pcomp_id₀_aux : ∀ {F G : PCtx S} (_ : isTrunc k F G), pcomp F (id₀ k G) = G
| F, [], h => rfl
| F, g :: G, h => by
  simp [pcomp]
  congr
  apply simulSubst_var_of_isTrunc h
  apply pcomp_id₀_aux h.pred

lemma pcomp_id₀ {F G Δ : PCtx S} (h : isTrunc k F G) (h' : Δ.length = G.length) :
    pcomp F (id₀ k Δ) = G := by
  convert pcomp_id₀_aux h using 2
  simp [id₀, id, h']

lemma pcomp_id {Γ Δ F : PCtx S} (h : isMor Γ Δ F) : pcomp F (id Δ) = F :=
  pcomp_id₀ (isTrunc.zero _) h.length_eq

lemma idN_pcomp {k n : ℕ} : ∀ {F : PCtx S} (_ : (F ↑↑ 1 # n) = F),
    pcomp (idN k n) F = F ↑↑ k
| [], _ => rfl
| A :: F, h => by
  simp only [pcomp]
  apply List.cons.inj at h
  rw [idN_pcomp h.2, isMorAuxLift h.1]
  rfl

lemma id₀_pcomp {k : ℕ} : ∀ {F G : PCtx S} (_ : (F ↑↑ 1 # G.length) = F),
    pcomp (id₀ k G) F = F ↑↑ k :=
  idN_pcomp

lemma id_pcomp : ∀ {Γ Δ F : PCtx S} (_ : isMor Γ Δ F), pcomp (id Γ) F = F
| Γ, _, _, .nil => rfl
| Γ, D :: Δ, f :: F, .cons h₁ h₂ h₃ => by
  simp only [pcomp, id_pcomp h₁, simulSubst_id_of_typing h₃]

lemma pcomp_pcomp {Γ Δ Θ Κ: PCtx S}: ∀ {F G H : PCtx S}
  (_ : isMor Γ Δ F) (_ : isMor Δ Θ G) (_ : isMor Θ Κ H)
  , pcomp (pcomp F G) H = pcomp F (pcomp G H)
| F, G, [], _, _, _ => by simp [pcomp]
| F, G, h :: H, h₁, h₂, .cons h₃ h₄ h₅ => by
  simp only [pcomp, simulSubst_pcomp (lift_inv_of_typing h₅) h₁ h₂ (isTrunc.zero _),
    pcomp_pcomp h₁ h₂ h₃]

end

noncomputable section

namespace PCtx.beta

@[simp]
def nat {Γ Δ : PCtx S} : (Γ →β Δ) → ℕ
| .head _ => 0
| .tail h => h.nat + 1

def pterml {Γ Δ : PCtx S} : (Γ →β Δ) → PTerm S
| .head (A := A) _ => A
| .tail h => h.pterml

def ptermr {Γ Δ : PCtx S} : (Γ →β Δ) → PTerm S
| .head (B := B) _ => B
| .tail h => h.ptermr

def pctx {Γ Δ : PCtx S} : (Γ →β Δ) → PCtx S
| .head (Γ := Γ) _ => Γ
| .tail h => h.pctx

def ptermBeta {Γ Δ : PCtx S} : (h : Γ →β Δ) → (h.pterml →β h.ptermr)
| .head h' => h'
| .tail h => h.ptermBeta

def isIteml {Γ Δ : PCtx S} : (h : Γ →β Δ) → h.pterml ↓ h.nat in Γ
| .head _ => isItem.zero _
| .tail h => isItem.succ _ h.isIteml

def isTruncl {Γ Δ : PCtx S} : (h : Γ →β Δ) → isTrunc (h.nat + 1) Γ h.pctx
| .head _ => isTrunc.succ _ (isTrunc.zero _)
| .tail h => isTrunc.succ _ h.isTruncl

def isItemr {Γ Δ : PCtx S} : (h : Γ →β Δ) → h.ptermr ↓ h.nat in Δ
| .head _ => isItem.zero _
| .tail h => isItem.succ _ h.isItemr

def isTruncr {Γ Δ : PCtx S} : (h : Γ →β Δ) → isTrunc (h.nat + 1) Δ h.pctx
| .head _ => isTrunc.succ _ (isTrunc.zero _)
| .tail h => isTrunc.succ _ h.isTruncr

def isItem_of_ne {Γ Δ : PCtx S} {A : PTerm S} :
    {n : ℕ} → (h : Γ →β Δ) → (n ≠ h.nat) → (A ↓ n in Γ) → (A ↓ n in Δ)
| 0, .head _, h₂, h₃ => by simp at h₂
| n + 1, .head _, h₂, h₃ => isItem.succ _ h₃.pred
| 0, .tail _, h₂, .zero _ => isItem.zero _
| n + 1, .tail h₁, h₂, h₃ => by
  apply isItem.succ
  apply isItem_of_ne h₁ _ h₃.pred
  simpa using h₂

def isItemLift_of_ne {Γ Δ : PCtx S} {A : PTerm S} {n : ℕ} :
    (h : Γ →β Δ) → (n ≠ h.nat) → (A ↓ n sub Γ) → (A ↓ n sub Δ)
| h₁, h₂, ⟨B, h₃, h₄⟩ => by
  exact ⟨_, h₃, h₁.isItem_of_ne h₂ h₄⟩

def exp_isItem_of_ne {Γ Δ : PCtx S} {A : PTerm S} :
    {n : ℕ} → (h : Γ →β Δ) → (n ≠ h.nat) → (A ↓ n in Δ) → (A ↓ n in Γ)
| 0, .head _, h₂, h₃ => by simp at h₂
| n + 1, .head _, h₂, h₃ => isItem.succ _ h₃.pred
| 0, .tail _, h₂, .zero _ => isItem.zero _
| n + 1, .tail h₁, h₂, h₃ => by
  apply isItem.succ
  apply exp_isItem_of_ne h₁ _ h₃.pred
  simpa using h₂

def exp_isItemLift_of_ne {Γ Δ : PCtx S} {A : PTerm S} {n : ℕ} :
    (h : Γ →β Δ) → (n ≠ h.nat) → (A ↓ n sub Δ) → (A ↓ n sub Γ)
| h₁, h₂, ⟨B, h₃, h₄⟩ => by
  exact ⟨_, h₃, h₁.exp_isItem_of_ne h₂ h₄⟩

end PCtx.beta

def ctx_beta_typing_var_eq {Γ Γ' : PCtx S} {A : PTerm S} :
  {n : ℕ} → (Γ ⊢ ⬝) → (Γ' ⊢ ⬝) → (h₃ : Γ →β Γ') → (A ↓ n sub Γ) → (n = h₃.nat)
  → (Γ' ⊢ #n : A)
| n, h₁, h₂, h₃, ⟨B, h₄, h₅⟩, h₆ => by
  cases h₆
  cases isItem_unique h₅ h₃.isIteml
  cases h₄
  apply typing.conv _ _ _ _ _ (h₃.ptermBeta.betac.symm).lift
  apply typing.var _ _ _ h₂ ⟨_, rfl, h₃.isItemr⟩
  exact weakening_isTrunc h₃.isTruncr (typing_of_isItem_of_isTrunc h₅ h₃.isTruncl h₁).2 h₂

def ctx_beta_typing_var_ne {Γ Γ' : PCtx S} {A : PTerm S} :
  {n : ℕ} → (Γ' ⊢ ⬝) → (h₃ : Γ →β Γ') → (A ↓ n sub Γ) → (n ≠ h₃.nat)
  → (Γ' ⊢ #n : A)
| _, h₁, h₂, h₃, h₄ => typing.var _ _ _ h₁ (h₂.isItemLift_of_ne h₄ h₃)

def ctx_beta_typing_var {Γ Γ' : PCtx S} {A : PTerm S} :
  {n : ℕ} → (Γ ⊢ ⬝) → (Γ' ⊢ ⬝) → (Γ →β Γ') → (A ↓ n sub Γ) → (Γ' ⊢ #n : A)
| n, h₁, h₂, h₃, h₄ =>
  if h : n = h₃.nat then ctx_beta_typing_var_eq h₁ h₂ h₃ h₄ h
    else ctx_beta_typing_var_ne h₂ h₃ h₄ h

def ctx_beta_typing {Γ Γ' : PCtx S} {a A : PTerm S} :
    ∀ (_ : Γ ⊢ a : A) (_ : Γ' ⊢ ⬝) (_ : Γ →β Γ'), Γ' ⊢ a : A
| .var _ _ _ h₁ h₂, h₃, h₄ => ctx_beta_typing_var h₁ h₃ h₄ h₂
| .sort _ _ _ h₁ _, h₃, _ => typing.sort _ _ _ h₁ h₃
| .pi _ _ _ _ _ _ h₁ h₂ h₃, h₄, h₅ => by
  apply typing.pi _ _ _ _ _ _ h₁
  apply ctx_beta_typing h₂ h₄ h₅
  apply ctx_beta_typing h₃ (wf.cons _ _ _ (ctx_beta_typing h₂ h₄ h₅)) (PCtx.beta.tail h₅)
| .abs _ _ _ _ _ _ _ h₀ h₁ h₂ h₃, h₄, h₅ => by
  apply typing.abs _ _ _ _ _ _ _ h₀
  apply ctx_beta_typing h₁ h₄ h₅
  apply ctx_beta_typing h₂ (wf.cons _ _ _ (ctx_beta_typing h₁ h₄ h₅)) (PCtx.beta.tail h₅)
  apply ctx_beta_typing h₃ (wf.cons _ _ _ (ctx_beta_typing h₁ h₄ h₅)) (PCtx.beta.tail h₅)
| .app _ _ _ _ _ h₁ h₂, h₃, h₄ =>
  typing.app _ _ _ _ _ (ctx_beta_typing h₁ h₃ h₄) (ctx_beta_typing h₂ h₃ h₄)
| .conv _ _ _ _ _ h₁ h₂ h₃, h₄, h₅ =>
  typing.conv _ _ _ _ _ h₁ (ctx_beta_typing h₂ h₄ h₅) (ctx_beta_typing h₃ h₄ h₅)

def ctx_beta_exp_typing_var_eq {Γ Γ' : PCtx S} {A : PTerm S} :
  {n : ℕ} → (Γ ⊢ ⬝) → (Γ' ⊢ ⬝) → (h₃ : Γ' →β Γ) → (A ↓ n sub Γ) → (n = h₃.nat)
  → (Γ' ⊢ #n : A)
| n, h₁, h₂, h₃, ⟨B, h₄, h₅⟩, h₆ => by
  cases h₆
  cases isItem_unique h₅ h₃.isItemr
  cases h₄
  apply typing.conv _ _ _ _ _ (h₃.ptermBeta.betac).lift
  apply typing.var _ _ _ h₂ ⟨_, rfl, h₃.isIteml⟩
  exact weakening_isTrunc h₃.isTruncl (typing_of_isItem_of_isTrunc h₅ h₃.isTruncr h₁).2 h₂

def ctx_beta_exp_typing_var_ne {Γ Γ' : PCtx S} {A : PTerm S} :
  {n : ℕ} → (Γ' ⊢ ⬝) → (h₃ : Γ' →β Γ) → (A ↓ n sub Γ) → (n ≠ h₃.nat)
  → (Γ' ⊢ #n : A)
| _, h₁, h₂, h₃, h₄ => typing.var _ _ _ h₁ (h₂.exp_isItemLift_of_ne h₄ h₃)

def ctx_beta_exp_typing_var {Γ Γ' : PCtx S} {A : PTerm S} :
  {n : ℕ} → (Γ ⊢ ⬝) → (Γ' ⊢ ⬝) → (Γ' →β Γ) → (A ↓ n sub Γ) → (Γ' ⊢ #n : A)
| n, h₁, h₂, h₃, h₄ =>
  if h : n = h₃.nat then ctx_beta_exp_typing_var_eq h₁ h₂ h₃ h₄ h
    else ctx_beta_exp_typing_var_ne h₂ h₃ h₄ h

def ctx_beta_exp_typing {Γ Γ' : PCtx S} {a A : PTerm S} :
    ∀ (_ : Γ ⊢ a : A) (_ : Γ' ⊢ ⬝) (_ : Γ' →β Γ), Γ' ⊢ a : A
| .var _ _ _ h₁ h₂, h₃, h₄ => ctx_beta_exp_typing_var h₁ h₃ h₄ h₂
| .sort _ _ _ h₁ _, h₃, _ => typing.sort _ _ _ h₁ h₃
| .pi _ _ _ _ _ _ h₁ h₂ h₃, h₄, h₅ => by
  apply typing.pi _ _ _ _ _ _ h₁
  apply ctx_beta_exp_typing h₂ h₄ h₅
  apply ctx_beta_exp_typing h₃ (wf.cons _ _ _ (ctx_beta_exp_typing h₂ h₄ h₅)) (PCtx.beta.tail h₅)
| .abs _ _ _ _ _ _ _ h₀ h₁ h₂ h₃, h₄, h₅ => by
  apply typing.abs _ _ _ _ _ _ _ h₀
  apply ctx_beta_exp_typing h₁ h₄ h₅
  apply ctx_beta_exp_typing h₂ (wf.cons _ _ _ (ctx_beta_exp_typing h₁ h₄ h₅)) (PCtx.beta.tail h₅)
  apply ctx_beta_exp_typing h₃ (wf.cons _ _ _ (ctx_beta_exp_typing h₁ h₄ h₅)) (PCtx.beta.tail h₅)
| .app _ _ _ _ _ h₁ h₂, h₃, h₄ =>
  typing.app _ _ _ _ _ (ctx_beta_exp_typing h₁ h₃ h₄) (ctx_beta_exp_typing h₂ h₃ h₄)
| .conv _ _ _ _ _ h₁ h₂ h₃, h₄, h₅ =>
  typing.conv _ _ _ _ _ h₁ (ctx_beta_exp_typing h₂ h₄ h₅) (ctx_beta_exp_typing h₃ h₄ h₅)

def term_beta_typing {Γ : PCtx S} {t s M : PTerm S} :
    ∀ (_: Γ ⊢ t : M) (_ : t →β s), Γ ⊢ s : M
| .pi _ _ _ _ _ _ h₁ h₂ h₃, .pil _ _ _ h₄ =>
  typing.pi _ _ _ _ _ _ h₁ (term_beta_typing h₂ h₄)
    (ctx_beta_typing h₃ (wf.cons _ _ _ (term_beta_typing h₂ h₄)) (PCtx.beta.head h₄))
| .pi _ _ _ _ _ _ h₁ h₂ h₃, .pir _ _ _ h₄ =>
  typing.pi _ _ _ _ _ _ h₁ h₂ (term_beta_typing h₃ h₄)
| .abs _ _ _ B _ _ _ h₀ h₁ h₂ h₃, .absl _ A' _ h₄ => by
  apply typing.conv _ _ _ _ _ (beta.pil _ _ B h₄).betac.symm
  apply typing.abs _ _ _ _ _ _ _ h₀ (term_beta_typing h₁ h₄)
    (ctx_beta_typing h₂ (wf.cons _ _ _ (term_beta_typing h₁ h₄)) (PCtx.beta.head h₄))
    (ctx_beta_typing h₃ (wf.cons _ _ _ (term_beta_typing h₁ h₄)) (PCtx.beta.head h₄))
  apply (typing.pi _ _ _ _ _ _ h₀ h₁ h₂)
| .abs _ _ _ _ _ _ _ h₀ h₁ h₂ h₃, .absr _ _ _ h₄ =>
  typing.abs _ _ _ _ _ _ _ h₀ h₁ h₂ (term_beta_typing h₃ h₄)
| .app _ _ _ _ _ h₁ h₂, .red _ _ _ => by
  apply typing.conv _ _ _ _ _ ((pi_inj (of_abs_typing h₁).betac).2.symm).substl
  apply substitution_typing (of_abs_typing h₁).typing₃ isSubst.zero
  apply typing.conv _ _ _ _ _ (pi_inj (of_abs_typing h₁).betac).1 h₂
    (of_abs_typing h₁).typing₁
  apply substitution_typing (of_pi_typing (typing_sort_of_pi_typing h₁).2).typing₂ isSubst.zero h₂
| .app _ _ _ _ _ h₁ h₂, .appl _ _ _ h₄ =>
  typing.app _ _ _ _ _ (term_beta_typing h₁ h₄) h₂
| .app _ _ _ _ _ h₁ h₂, .appr _ _ _ h₄ => by
  apply typing.conv _ _ _ _ _ (h₄.betac.symm).substr
  apply typing.app _ _ _ _ _ h₁ (term_beta_typing h₂ h₄)
  apply substitution_typing (of_pi_typing (typing_sort_of_pi_typing h₁).2).typing₂ isSubst.zero h₂
| .conv _ _ _ _ _ h₁ h₂ h₃, h₄ =>
  typing.conv _ _ _ _ _ h₁ (term_beta_typing h₂ h₄) h₃

def term_betar_typing {Γ : PCtx S} {t s M : PTerm S} :
    ∀ (_: Γ ⊢ t : M) (_ : t ↠β s), Γ ⊢ s : M
| h₁, .beta _ _ h₂ => term_beta_typing h₁ h₂
| h₁, .refl _ => h₁
| h₁, .trans _ _ _ h₂ h₃ => term_betar_typing (term_betar_typing h₁ h₂) h₃
alias subject_reduction := term_betar_typing

def ctx_beta_wf :
  ∀ {Γ Γ' : PCtx S} (_ : Γ ⊢ ⬝) (_ : Γ →β Γ'), Γ' ⊢ ⬝
| [], [], _, _ => wf.nil
| [], _ :: _, _, h => by simpa using h.length_eq
| _ :: _, [], _, h => by simpa using h.length_eq
| _ :: _, _ :: _, .cons _ _ _ h, .head h' => wf.cons _ _ _ (term_beta_typing h h')
| _ :: _, _ :: _, .cons _ _ _ h, .tail h' =>
  wf.cons _ _ _ (ctx_beta_typing h (ctx_beta_wf h.wf h') h')

def ctx_betar_wf {Γ Γ' : PCtx S} :
    ∀ (_ : Γ ⊢ ⬝) (_ : Γ ↠β Γ'), Γ' ⊢ ⬝
| h, .beta _ _ h' => ctx_beta_wf h h'
| h, .refl _ => h
| h, .trans _ _ _ h₁ h₂ => ctx_betar_wf (ctx_betar_wf h h₁) h₂

def ctx_betar_typing {Γ Γ' : PCtx S} : ∀ (_ : Γ ⊢ a : A) (_ : Γ ↠β Γ'),
    Γ' ⊢ a : A
| h, .beta _ _ h' => ctx_beta_typing h (ctx_betar_wf h.wf (PCtx.betar.beta _ _ h')) h'
| h, .refl _ => h
| h, .trans _ _ _ h₁ h₂ => ctx_betar_typing (ctx_betar_typing h h₁) h₂

def ctx_betar_exp_typing {Γ Γ' : PCtx S} : ∀ (_ : Γ ⊢ a : A) (_ : Γ' ⊢ ⬝) (_ : Γ' ↠β Γ),
    Γ' ⊢ a : A
| h₁, h₂, .beta _ _ h₃ => ctx_beta_exp_typing h₁ h₂ h₃
| h₁, h₂, .refl _ => h₁
| h₁, h₂, .trans _ _ _ h₃ h₄ =>
  ctx_betar_exp_typing (ctx_betar_exp_typing h₁ (ctx_betar_wf h₂ h₃) h₄) h₂ h₃

def ctx_betac_confl : ∀ {Γ Δ : PCtx S} (_ : Γ ≃β Δ),
    Σ (Θ : PCtx S), (Γ ↠β Θ) × (Δ ↠β Θ)
| [], [], h => ⟨[], ⟨PCtx.betar.refl _,  PCtx.betar.refl _⟩⟩
| _ :: _, [], h => by simpa using h.length_eq
| [], _ :: _, h => by simpa using h.length_eq
| G :: Γ, D :: Δ, h =>
  ⟨(betac_confl h.head).1 :: (ctx_betac_confl h.tail).1,
    ⟨(betac_confl h.head).2.1.of_head_of_tail (ctx_betac_confl h.tail).2.1,
      (betac_confl h.head).2.2.of_head_of_tail (ctx_betac_confl h.tail).2.2⟩⟩

def ctx_betac_typing {Γ Γ' : PCtx S} (h₁ : Γ ⊢ a : A) (h₂ : Γ' ⊢ ⬝) (h₃ : Γ ≃β Γ') :
    Γ' ⊢ a : A := by
  let hΔ₁ := (ctx_betac_confl h₃).2.1
  let hΔ₂ := (ctx_betac_confl h₃).2.2
  exact (ctx_betar_exp_typing (ctx_betar_typing h₁ hΔ₁) h₂ hΔ₂)

def ctx_betac_wf_cons {Γ Γ' : PCtx S} (h₁ : A :: Γ ⊢ ⬝) (h₂ : Γ' ⊢ ⬝) (h₃ : Γ ≃β Γ') :
    (A :: Γ') ⊢ ⬝ :=
  wf.cons _ _ _ (ctx_betac_typing (exists_of_cons' h₁).snd h₂ h₃)

end

section

-- `isMor` is sound wrt to `betac`

def isMor_betac₁ {Γ Γ' : PCtx S} (h₁ : Γ' ⊢ ⬝) (h₂ : Γ ≃β Γ'):
  ∀ {Δ F : PCtx S} (_ : isMor Γ Δ F), isMor Γ' Δ F
| [], _, h => by cases h.of_nil; apply isMor.nil
| _, [], h => by cases h.of_mor_nil; apply isMor.nil
| D :: Δ, f :: F, .cons h₃ h₄ h₅ =>
  isMor.cons (isMor_betac₁ h₁ h₂ h₃) (ctx_betac_typing h₄ h₁ h₂)
    (ctx_betac_typing h₅ h₁ h₂)

def isMor_betac₂ {Γ : PCtx S} (h : Γ ⊢ ⬝) :
  ∀ {Δ Δ' F : PCtx S} (_ : Δ ≃β Δ') (_ : Δ' ⊢ ⬝) (_ : isMor Γ Δ F) ,
    isMor Γ Δ' F
| _, Δ', [], h₁, _, h₂ => by cases h₂; convert isMor.nil; simpa using h₁.length_eq.symm
| [], _ :: _, _, h, _, _ => by simpa using h.length_eq
| _ :: _, [], _, h, _, _ => by simpa using h.length_eq
| D :: Δ, D' :: Δ', f :: F, h₁, h₂, .cons h₃ h₄ h₅ => by
  have : Γ ⊢ simulSubst D' 0 F : !((exists_of_cons' h₂).fst) := by
    simpa [simulSubst_sort] using simulSubst_typing (append_typing h (exists_of_cons' h₂).snd)
      (isMor'_isMor (isMor_betac₂ h h₁.tail (wf_of_cons h₂) h₃))
  apply isMor.cons
  apply isMor_betac₂ h h₁.tail (wf_of_cons h₂) h₃
  exact this
  apply h₅.conv _ _ _ _ _ h₁.head.simulSubst this

/-
-- This is NOT TRUE!!!
def isMor_betac {Γ : PCtx S} (h : Γ ⊢ ⬝) :
  ∀ {Δ F G : PCtx S} (_ : Δ ⊢ ⬝) (_ : isMor Γ Δ F) (_ : F ≃β G),
    isMor Γ Δ G
| _, [], [], _, h₁, _ => by cases h₁; apply isMor.nil
| _, _ :: _, [], _, _, h₂ => by simpa using h₂.length_eq
| _, [], _ :: _, _, _, h₂ => by simpa using h₂.length_eq
| D :: Δ, f :: F, g :: G, h₀, .cons h₁ h₂ h₃, h₄ => by
  have : Γ ⊢ simulSubst D 0 G : !((exists_of_cons' h₀).fst) := by
    simpa [simulSubst_sort] using simulSubst_typing (append_typing h (exists_of_cons' h₀).snd)
      (isMor'_isMor (isMor_betac h (wf_of_cons h₀) h₁ h₄.tail))
  apply isMor.cons
  apply isMor_betac h (wf_of_cons h₀) h₁ h₄.tail
  exact this
-/

def isMor_betac {Γ Γ' Δ Δ': PCtx S} (h₁ : Γ ⊢ ⬝) (h₂ : Γ' ⊢ ⬝) (h₃ : Δ' ⊢ ⬝) (h₄ : Γ ≃β Γ')
  (h₅ : Δ ≃β Δ') (h₆ : isMor Γ Δ F) :
    isMor Γ' Δ' F :=
  isMor_betac₁ h₂ h₄ (isMor_betac₂ h₁ h₅ h₃ h₆)

def pcomp_betac₁ : ∀ {F F' G : PCtx S} (_ : F ≃β F'), pcomp F G ≃β pcomp F' G
| _, _, [], _ => PCtx.betac.refl _
| _, _, _ :: _, h => betac.of_head_of_tail h.simulSubst (pcomp_betac₁ h)

def pcomp_betac₂ : ∀ {F G G' : PCtx S} (_ : G ≃β G'), pcomp F G ≃β pcomp F G'
| _, [], [], _ => PCtx.betac.refl _
| _, _ :: _, [], h => by simpa using h.length_eq
| _, [], _ :: _, h => by simpa using h.length_eq
| _, _ :: _, _ :: _, h => betac.of_head_of_tail h.head.simulSubst (pcomp_betac₂ h.tail)

def pcomp_betac {F F' G G' : PCtx S} (h₁ : F ≃β F') (h₂ : G ≃β G') :
    pcomp F G ≃β pcomp F' G' :=
  (pcomp_betac₁ h₁).trans _ _ _ (pcomp_betac₂ h₂)

end
