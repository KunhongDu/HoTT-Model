import Mathlib.Logic.Relation
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

lemma lift_inj {i c : ℕ} :
    (M ↑ i # c) = (N ↑ i # c) → M = N := by
  intro h
  induction M generalizing N c with
  | var n =>
      simp at h
      split_ifs at h with h₀
      . cases N
        all_goals simp at h
        rename ℕ => k
        have : k < c := by
          split_ifs at h
          . assumption
          . simp at h; simp [h] at h₀; exact lt_of_le_of_lt (Nat.le_add_right _ _) h₀
        simp [this] at h; simpa
      . cases N
        all_goals simp at h
        rename ℕ => k
        have : ¬ k < c := by
          split_ifs at h
          . simp at h h₀ ⊢; simp [← h]; exact h₀.trans (Nat.le_add_right _ _)
          . assumption
        simp [this] at h; simpa
  | sort =>
      cases N; all_goals simp at h
      split_ifs at h
      simp [h]
  | app _ _ ih₁ ih₂ =>
      cases N; all_goals simp at h
      split_ifs at h
      simpa using ⟨ih₁ h.1, ih₂ h.2⟩
  | pi  _ _ ih₁ ih₂ =>
      cases N; all_goals simp at h
      split_ifs at h
      simpa using ⟨ih₁ h.1, ih₂ h.2⟩
  | abs  _ _ ih₁ ih₂ =>
      cases N; all_goals simp at h
      split_ifs at h
      simpa using ⟨ih₁ h.1, ih₂ h.2⟩

lemma lift0_inj {i : ℕ} :
    (M ↑ i) = (N ↑ i) → M = N :=
  lift_inj

lemma lift_zero {c : ℕ} :
    (M ↑ 0 # c) = M := by
  induction M generalizing c
  all_goals simp
  all_goals rename_i ih₁ ih₂
  all_goals exact ⟨ih₁, ih₂⟩

lemma lift_lift (i j k : ℕ) :
    ((M ↑ j # i) ↑ k # (j + i)) = M ↑ (j + k) # i := by
  sorry

lemma lift_lift_of_le (i j k n : ℕ) :
    i ≤ n → ((M ↑ j # i) ↑ k # (j + n)) = (M ↑ k # n) ↑ j # i := by
  sorry

lemma lift_lift_of_le_of_le (i j k n : ℕ) :
    i ≤ n → k ≤ i + n → ((M ↑ n # i) ↑ j # k) = M ↑ (n + j) # i := by
  sorry

lemma lift0_lift0 (i j : ℕ) :
    ((M ↑ i) ↑ j) = M ↑ (i + j) :=
  lift_lift_of_le_of_le _ _ _ _ (by simp) (by simp)

def subst (e : PTerm S) (m : ℕ) : PTerm S → PTerm S
| #n => if n < m then #n else (if n = m then e ↑ n else #(n - 1))
| sort M => !M
| app N M => (subst e m N) ⬝ (subst e m M)
| pi N M => Π.(subst e m N) (subst e (m + 1) M)
| abs N M => λ.(subst e m N) (subst e (m + 1) M)

notation N "{" e " // " m "}" => subst e m N

notation N "{" e "}" => subst e 0 N

lemma subst_lift (i j k : ℕ) :
    (M{N // j} ↑ k # (j + i)) = (M ↑ k # j + i + 1){N ↑ k # i // j} := by
  sorry

lemma subst_lift_of_le (i j n : ℕ) :
    i ≤ n → (M{N // n} ↑ j # i) = (M ↑ j # i){N // j + n} := by
  sorry

lemma lift_subst_of_le_of_le (i j k : ℕ) :
    i ≤ k → k ≤ i + n → (M ↑ (n + 1) # j){N // k} = M ↑ n # i := by
  sorry

variable {P : PTerm S}

lemma subst_subst (i j : ℕ) :
    M{N // j}{P // i + j} = M{P // i + j + 1}{N{P // i} // j} := by
  sorry

lemma subst0_subst0 (k : ℕ) :
    M{N}{P // k} = M{P // k + 1}{N{P // k}} :=
  subst_subst _ 0

end LiftSubst

section Context

def PCtx (S : Specification) := List (PTerm S)

variable {α : Type*}

inductive isItem : α → List α → ℕ → Prop
| zero Γ : isItem x (x :: Γ) 0
| succ {Γ n} y : isItem x Γ n → isItem x (y :: Γ) (n + 1)

notation x " ↓ " n " in " Γ => isItem x Γ n

-- need a better name

lemma isItem_unique {x y : α} {Γ : List α} {n : ℕ} :
    (x ↓ n in Γ) → (y ↓ n in Γ) → x = y := by
  induction n generalizing x y Γ
  . intro h₁ h₂
    cases h₁; cases h₂; rfl
  . intro h₁ h₂
    cases h₁; cases h₂
    rename_i ih _ _ h₁ h₂
    apply ih h₁ h₂

-- isTruncate the first k-term and have =
inductive isTrunc : ℕ → List α → List α → Prop
| zero Γ : isTrunc 0 Γ Γ
| succ {k : ℕ} {Γ Γ' : List α} (x : α) : isTrunc k Γ Γ' → isTrunc (k + 1) (x :: Γ) Γ'

lemma exist_isTrunc_of_isItem (k : ℕ) (Γ : List α) (x : α) :
    (x ↓ k in Γ) → ∃ Γ', isTrunc (k + 1) Γ Γ' := by
  induction k generalizing x Γ
  . intro h; cases h; rename_i Γ
    exact ⟨Γ, isTrunc.succ _ (isTrunc.zero _)⟩
  . intro h; cases h
    rename_i ih _ _ h
    obtain ⟨Γ', hΓ'⟩ := ih _ _ h
    exact ⟨Γ', isTrunc.succ _ hΓ'⟩

inductive isInsert (Γ : PCtx S) (t : PTerm S) : ℕ → PCtx S → PCtx S → Prop
| zero : isInsert Γ t 0 Γ (t :: Γ)
| succ {n Δ Δ'} u : isInsert Γ t n Δ Δ' → isInsert Γ t (n + 1) (u :: Δ) ((u ↑ 1 # n) :: Δ')

lemma isItem_of_isInsert_of_le {t : PTerm S} {n : ℕ} {Γ Δ Δ' : PCtx S} :
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

lemma isItem_of_isInsert_of_lt {t : PTerm S} {n : ℕ} {Γ Δ Δ' : PCtx S} :
    isInsert Γ t n Δ Δ' → ∀ {k}, (k < n → ∀ {u}, (u ↓ k in Δ) →
      (u ↑ 1 # (n - (k + 1)) ) ↓ k in Δ') := by
  sorry

def isItemLift (t : PTerm S) (Γ : PCtx S) (n : ℕ) : Prop :=
    ∃ u, (t = u ↑ n + 1) ∧ u ↓ n in Γ

notation x " ↓ " n " sub " Γ => isItemLift x Γ n

lemma isItemLift_of_isInsert_of_lt {t u : PTerm S} {n : ℕ} {Γ Δ Δ' : PCtx S}
  (h : isInsert Γ t n Δ Δ') {k : ℕ} (hk : k < n) (hu : u ↓ k sub Δ) :
    (u ↑ 1 # n) ↓ k sub Δ' := by
  rcases hu with ⟨w, ⟨hw₁, hw₂⟩⟩
  use w ↑ 1 # (n - (k + 1))
  constructor
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

inductive isSubst (Γ : PCtx S) (t T : PTerm S) : ℕ → PCtx S → PCtx S → Prop
| zero : isSubst Γ t T 0 (T :: Γ) Γ
| succ {n Δ Δ'} w : isSubst Γ t T n Δ Δ' → isSubst Γ t T (n + 1) (w :: Δ) (w{t // n} :: Δ')

lemma isTerm_of_isSubst_of_le {n : ℕ} {Γ Δ Δ' : PCtx S} {t T : PTerm S} :
    isSubst Γ t T n Δ Δ' → ∀ {k}, n ≤ k → (∀ {v}, (v ↓ k + 1 in Δ) → v ↓ k in Δ') := by
  induction n
  . intro h k hk v hv
    cases h; cases hv
    assumption
  . sorry

end Context

section Reduction

variable {S : Specification}

inductive beta : PTerm S → PTerm S → Prop
| head (A M N : PTerm S) : beta ((λ.A M) ⬝ N) (M{N ↑ 1 # 0 // 0})
| appl (A A' M : PTerm S) : beta A A' → beta (A ⬝ M) (A' ⬝ M)
| appr (A M M' : PTerm S) : beta M M' → beta (A ⬝ M) (A ⬝ M')
| pil (A A' M : PTerm S) : beta A A' → beta (Π.A M) (Π.A' M)
| pir (A M M' : PTerm S) : beta M M' → beta (Π.A M) (Π.A M')
| absl (A A' M : PTerm S) : beta A A' → beta (λ.A M) (λ.A' M)
| absr (A M M' : PTerm S) : beta M M' → beta (λ.A M) (λ.A M')

open Relation

def betar := ReflTransGen (@beta S)

def betac := EqvGen (@beta S)

infix:50 " →β " => beta
infix:50 " ↠β " => betar
infix:50 " ≃β " => betac

lemma lift_beta_lift (h : A →β B) :
    (A ↑ i # n) →β B ↑ i # n := by
  sorry

lemma lift_betac_lift (h : A ≃β B) :
    (A ↑ i # n) ≃β B ↑ i # n := by
  sorry

end Reduction

section Typing

inductive PJudge (S : Specification)
| wf : PCtx S → PJudge S
| typing : PCtx S → PTerm S → PTerm S → PJudge S

open PJudge Relation

notation (priority := high) "⬝" => ([] : PCtx _)
notation:20 Γ " ⊢ ⬝ " => wf Γ
notation:20 Γ " ⊢ " a  " : " A => typing Γ a A

inductive Derivable {S : Specification} : PJudge S → Prop
| nil : Derivable ((⬝ : PCtx S) ⊢ ⬝)
| cons Γ A s : Derivable (Γ ⊢ A : !s) → Derivable (A :: Γ ⊢ ⬝)
| var Γ A n : Derivable (Γ ⊢ ⬝) → (A ↓ n sub Γ) → Derivable (Γ ⊢ #n : A)
| sort Γ s₁ s₂ (h : S.ax s₁ s₂) : Derivable (Γ ⊢ ⬝) → Derivable (Γ ⊢ !s₁ : !s₂)
| pi Γ A B s₁ s₂ s₃ (h : S.rel s₁ s₂ s₃) :
    Derivable (Γ ⊢ A : !s₁) →  Derivable (A :: Γ ⊢ B : !s₂) → Derivable (Γ ⊢ Π.A B : !s₃)
| abs Γ A b B s₁ s₂ s₃ (h : S.rel s₁ s₂ s₃) :
    Derivable (Γ ⊢ A : !s₁) →  Derivable (A :: Γ ⊢ B : !s₂) → Derivable (A :: Γ ⊢ b : B) →
      Derivable (Γ ⊢ λ.A b : Π.A B)
| app Γ f A B a :
    Derivable (Γ ⊢ f : Π.A B) → Derivable (Γ ⊢ a : A) → Derivable (Γ ⊢ f ⬝ a : B{a})
| conv Γ a A B s (h : A ≃β B):
    Derivable (Γ ⊢ a : A) → Derivable (Γ ⊢ B : !s) → Derivable (Γ ⊢ a : B)

variable {S : Specification}

lemma wf_of_typing (h : Derivable (Γ ⊢ t : T)) :
    Derivable (Γ ⊢ ⬝) := by
  generalize hJ : (Γ ⊢ t : T) = J at h
  induction h generalizing Γ t T
  all_goals cases hJ
  . assumption
  . assumption
  . rename_i h _; apply h rfl
  . rename_i h _ _; apply h rfl
  . rename_i h _; apply h rfl
  . rename_i h _; apply h rfl

lemma exists_of_cons (h : Derivable (A :: Γ ⊢ ⬝)) :
    ∃ s, Derivable (Γ ⊢ A : !s) := by
  cases h with
  | cons _ _ s h => exact ⟨s, h⟩

lemma exists_of_var_typing (h : Derivable (Γ ⊢ #n : A)) :
    ∃ B, B ≃β A ∧ (B ↓ n sub Γ) := by
  generalize hJ : (Γ ⊢ #n : A) = J at h
  induction h generalizing A
  all_goals cases hJ
  . rename_i A _ _ _
    exact ⟨A ,⟨EqvGen.refl _, by assumption⟩⟩
  . rename_i h₁ _ _ _ h₂
    obtain ⟨C, hC⟩ := h₂ rfl
    exact ⟨C, ⟨EqvGen.trans _ _ _ hC.1 h₁, hC.2⟩⟩

lemma exists_of_sort_typing (h : Derivable (Γ ⊢ !s : A)) :
    ∃ t, ((!t) ≃β A) ∧ S.ax s t := by
  generalize hJ : (Γ ⊢ !s : A) = J at h
  induction h generalizing A
  all_goals cases hJ
  . rename_i A _ _ _
    exact ⟨A, ⟨EqvGen.refl _, by assumption⟩⟩
  . rename_i h₁ _ _ _ h₂
    obtain ⟨t, ht⟩ := h₂ rfl
    exact ⟨t, ⟨EqvGen.trans _ _ _ ht.1 h₁, ht.2⟩⟩

lemma exists_of_pi_typing (h : Derivable (Γ ⊢ Π.A B : T)) :
    ∃ s₁ s₂ s₃, (T ≃β !s₃) ∧ S.rel s₁ s₂ s₃ ∧
      Derivable (Γ ⊢ A : !s₁) ∧ Derivable (A :: Γ ⊢ B : !s₂) := by
  generalize hJ : (Γ ⊢ Π.A B : T) = J at h
  induction h generalizing A B T
  all_goals cases hJ
  . rename_i s₁ s₂ s₃ _ _ _ _ _
    use s₁, s₂, s₃
    exact ⟨EqvGen.refl _, ⟨by assumption, ⟨by assumption, by assumption⟩⟩⟩
  . rename_i h _ _ _ ih
    obtain ⟨s₁, ⟨s₂, ⟨s₃, hs⟩⟩⟩ := ih rfl
    use s₁, s₂, s₃
    exact ⟨EqvGen.trans _ _ _ (EqvGen.symm _ _ h) hs.1, hs.2⟩

lemma exists_of_abs_typing (h : Derivable (Γ ⊢ λ.A b : T)) :
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

lemma exists_of_app_typing (h : Derivable (Γ ⊢ f ⬝ a : T)) :
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

/-
mutual
lemma weakening₀₂ (h₁ : Derivable (Γ ⊢ ⬝)) (h₂ : isInsert Δ A n Γ Γ')
  (h₃ : Derivable (Δ ⊢ A : !s)) :
    Derivable (Γ' ⊢ ⬝) := by
  cases h₂
  . apply Derivable.cons _ _ _ h₃
  . cases h₁
    rename_i n Γ Γ' u h₂ s' h
    apply Derivable.cons _ _ s'
    have : (!s') = ((!s') ↑ 1 # n) := by rfl
    rw [this]
    apply weakening₀₁ h h₂ h₃
termination_by Γ.length

lemma weakening₀₁ (h₁ : Derivable (Γ ⊢ t : T)) (h₂ : isInsert Δ A n Γ Γ')
  (h₃ : Derivable (Δ ⊢ A : !s)) :
    Derivable (Γ' ⊢ t ↑ 1 # n : T ↑ 1 # n) := by
  generalize hJ : (Γ ⊢ t : T) = J at h₁
  induction h₁ generalizing Γ t T Δ A n Γ' s
  all_goals cases hJ
  . rename_i k h₄ h₅ _
    dsimp
    split_ifs with h
    . apply Derivable.var _ _ _ (weakening₀₂ h₄ h₂ h₃)
        (isItemLift_of_isInsert_of_lt h₂ h h₅)
    . apply Derivable.var _ _ _ (weakening₀₂ h₄ h₂ h₃)
      obtain ⟨T', hT'⟩ := h₅
      use T'
      rw [hT'.1]
      constructor
      . rw [lift_lift_of_le_of_le _ _ _ _ (by simp)
          (by simp at h ⊢; apply h.trans (Nat.le_succ _))]
      . apply isItem_of_isInsert_of_le h₂ (by simpa using h) hT'.2
  . rename_i h₀ h₁ _
    simp; apply Derivable.sort _ _ _ h₀ (weakening₀₂ h₁ h₂ h₃)
  . rename_i h₀ _ _ ih₁ ih₂
    apply Derivable.pi _ _ _ _ _ _ h₀ (ih₁ h₂ h₃ rfl) (ih₂ (h₂.succ _) h₃ rfl)
  . rename_i h₀ _ _ _ ih₁ ih₂ ih₃
    apply Derivable.abs _ _ _ _ _ _ _ h₀ (ih₁ h₂ h₃ rfl) (ih₂ (h₂.succ _) h₃ rfl)
      (ih₃ (h₂.succ _) h₃ rfl)
  . rename_i ih₁ ih₂
    have : n = 0 + n := by simp
    rw [this, subst_lift]; simp
    apply Derivable.app _ _ _ _ _ (ih₁ h₂ h₃ rfl) (ih₂ h₂ h₃ rfl)
  . rename_i A₀ _ _ h₀ _ _ ih₁ ih₂
    apply Derivable.conv _ _ (A₀ ↑ 1 # n) _ _ (lift_betac_lift h₀) (ih₁ h₂ h₃ rfl)
      (ih₂ h₂ h₃ rfl)
termination_by Γ.length

end
-/

mutual
lemma weakening₀₁ : ∀ (h₁ : Derivable (Γ ⊢ t : T)) (h₂ : isInsert Δ A n Γ Γ')
  (h₃ : Derivable (Δ ⊢ A : !s)),
    Derivable (Γ' ⊢ t ↑ 1 # n : T ↑ 1 # n)
| .var Γ A k h₀ h₁, h₂, h₃ => by
  dsimp
  split_ifs with h
  . apply Derivable.var _ _ _ (weakening₀₂ h₀ h₂ h₃)
      (isItemLift_of_isInsert_of_lt h₂ h h₁)
  . apply Derivable.var _ _ _ (weakening₀₂ h₀ h₂ h₃)
    obtain ⟨T', hT'⟩ := h₁
    use T'
    rw [hT'.1]
    constructor
    . rw [lift_lift_of_le_of_le _ _ _ _ (by simp)
        (by simp at h ⊢; apply h.trans (Nat.le_succ _))]
    . apply isItem_of_isInsert_of_le h₂ (by simpa using h) hT'.2
| .sort Γ s₁ s₂ h₀ h₁, h₂, h₃ => by
  simp; apply Derivable.sort _ _ _ h₀ (weakening₀₂ h₁ h₂ h₃)
| .pi Γ A B s₁ s₂ s₃ h₀ h₁ h₃, h₄, h₅ => by
  apply Derivable.pi
  apply h₀
  apply weakening₀₁ h₁ h₄ h₅
  apply weakening₀₁ h₃ (h₄.succ A) h₅
| .abs Γ A b B s₁ s₂ s₃ h₀ h₁ h₂ h₃, h₄, h₅ => by
  apply Derivable.abs
  apply h₀
  apply weakening₀₁ h₁ h₄ h₅
  apply weakening₀₁ h₂ (h₄.succ A) h₅
  apply weakening₀₁ h₃ (h₄.succ A) h₅
| .app Γ f A B a h₀ h₁, h₂, h₃ => by
  have : n = 0 + n := by simp
  rw [this, subst_lift]; simp
  apply Derivable.app
  apply weakening₀₁ h₀ h₂ h₃
  apply weakening₀₁ h₁ h₂ h₃
| .conv Γ a A B s h₀ h₁ h₂, h₃, h₄ => by
  apply Derivable.conv _ _ (A ↑ 1 # n) _ _ (lift_betac_lift h₀)
  apply weakening₀₁ h₁ h₃ h₄
  apply weakening₀₁ h₂ h₃ h₄

lemma weakening₀₂ (h₁ : Derivable (Γ ⊢ ⬝)) (h₂ : isInsert Δ A n Γ Γ')
  (h₃ : Derivable (Δ ⊢ A : !s)) :
    Derivable (Γ' ⊢ ⬝) := by
  cases h₂
  . apply Derivable.cons _ _ _ h₃
  . cases h₁
    rename_i n Γ Γ' u h₂ s' h
    apply Derivable.cons _ _ s'
    have : (!s') = ((!s') ↑ 1 # n) := by rfl
    rw [this]
    apply weakening₀₁ h h₂ h₃
end





end Typing


/-
section Typing

open Relation

notation (priority := high) "⬝" => ([] : PCtx _)

mutual

inductive Wf {S : Specification} : PCtx S → Prop
| nil : Wf (⬝ : PCtx S)
| cons Γ A s : Der Γ A (!s) → Wf (A :: Γ)

inductive Der {S : Specification} : PCtx S → PTerm S → PTerm S → Prop
| var Γ A n : Wf Γ → (A ↓ n sub Γ) → Der Γ (#n) A
| sort Γ s₁ s₂ (h : S.ax s₁ s₂) : Wf Γ → Der Γ (!s₁) (!s₂)
| pi Γ A B s₁ s₂ s₃ (h : S.rel s₁ s₂ s₃) :
    Der Γ A (!s₁) →  Der (A :: Γ) B (!s₂) → Der Γ (Π.A B) (!s₃)
| abs Γ A b B s₁ s₂ s₃ (h : S.rel s₁ s₂ s₃) :
    Der Γ A (!s₁) →  Der (A :: Γ) B (!s₂) → Der (A :: Γ) b B → Der Γ (λ.A b) (Π.A B)
| app Γ f A B a :
    Der Γ f (Π.A B) → Der Γ a A → Der Γ (f ⬝ a) (B{a})
| conv Γ a A B s (h : A ≃β B):
    Der Γ a A → Der Γ B (!s) → Der Γ a B

end

notation:20 Γ " ⊢ ⬝ " => Wf Γ
notation:20 Γ " ⊢ " a  " : " A => Der Γ a A


lemma cons_inv (h : (A :: Γ) ⊢ ⬝) :
    ∃ s, Γ ⊢ A : !s := by
  cases h with
  | cons _ _ s h => exact ⟨s, h⟩

lemma var_inv (h : Γ ⊢ #n : A) :
    ∃ B, B ≃β A ∧ (B ↓ n sub Γ) := by
  induction h
  sorry

end
-/

section Morphism

def SubstSq (t : PTerm S) : ℕ → PCtx S → PTerm S
| _, [] => t
| n, A :: Γ => (SubstSq t (n + 1) Γ){A // n}

example : SubstSq T 0 [] = T := rfl

example : SubstSq T 0 [f] = T{f // 0} := rfl

example : SubstSq T 0 [g, f] = T{f // 1}{g // 0} := rfl

example : SubstSq T 0 [g, f] = T{f // 1}{g // 0} := rfl

example : SubstSq T 0 [h, g, f] = T{f // 2}{g // 1}{h // 0} := rfl

inductive isMor (Γ : PCtx S) : PCtx S → PCtx S → Prop
| nil : isMor Γ [] []
| cons : isMor Γ Δ F → Derivable (Γ ⊢ f : (SubstSq D 0 F)) → isMor Γ (D :: Δ) (f :: F)

example (Γ Δ F : PCtx S) :
    isMor Γ Δ F → Δ.length = F.length := by
  intro h
  induction Δ generalizing F with
  | nil => cases h; rfl
  | cons A Δ ih =>
      cases h
      rename_i h
      simp [ih _ h]

example : isMor [T₁, T₀] [T₁, T₀] [#1, #0] := by
  apply isMor.cons
  apply isMor.cons
  apply isMor.nil
  . simp [SubstSq]; sorry
  . simp [SubstSq]; sorry

example : isMor [#0, T] [#0, T] [#0, #1] := by
  apply isMor.cons
  apply isMor.cons
  apply isMor.nil
  . simp [SubstSq]; sorry
  . simp [SubstSq, subst]
    apply Derivable.var
    . sorry
    . use #0; simp; apply isItem.zero

example : isMor [#0, #0, T] [#0, #0, T] [#0, #1, #2] := by
  apply isMor.cons
  apply isMor.cons
  apply isMor.cons
  apply isMor.nil
  . simp [SubstSq]; sorry
  . simp [SubstSq, subst]
    apply Derivable.var
    . sorry
    . use #0; simp; apply isItem.succ; apply isItem.zero
  . simp [SubstSq, subst]
    apply Derivable.var
    . sorry
    . use #0; simp; apply isItem.zero

example : isMor [(#0) ⬝ #1, #0, T] [(#0) ⬝ #1, #0, T] [#0, #1, #2] := by
  apply isMor.cons
  apply isMor.cons
  apply isMor.cons
  apply isMor.nil
  . simp [SubstSq]; sorry
  . simp [SubstSq, subst]
    apply Derivable.var
    . sorry
    . use #0; simp; apply isItem.succ; apply isItem.zero
  . simp [SubstSq, subst]
    apply Derivable.var
    . sorry
    . use (#0) ⬝ #1; simp; apply isItem.zero

def id₀ : ℕ → PCtx S →  PCtx S
| _, [] => []
| n, _ :: S => (#n) :: (id₀ (n + 1) S)

def id : PCtx S → PCtx S := id₀ 0

example : id [T₃, T₂, T₁, T₀] = [#0, #1, #2, #3] := rfl

/-l
example (h : Derivable ([] ⊢ A : !s)) : A = A ↑ 1 := by
  generalize hJ : ([] ⊢ A : !s) = J at h
  induction h generalizing A s
  all_goals try cases hJ
  . rename_i h; obtain ⟨_, ⟨_, h⟩⟩ := h
    cases h
  . rfl
  . rename_i h₁ h₂ ih₁ ih₂
    simp
    constructor
    apply ih₁ rfl
/-
example (h : Derivable (Γ ⊢ A : !s)) : A = A ↑ 1 # Γ.length := by
  induction A generalizing s
  . obtain ⟨_, ⟨_, hl⟩⟩ := exists_of_var_typing h
    cases hl
  . simp
  . sorry -- simply exfalso??
  . rename_i A B ih₁ ih₂
  . sorry -- similar
-/


example (h : Derivable (A :: Γ ⊢ ⬝ )) : SubstSq A 0 (id₀ 1 Γ) = A ↑ 1 := by
  induction Γ with
  | nil =>
      cases h with
      | cons _ A s h =>
          simp [id₀, SubstSq]
          sorry
  | cons => sorry

example (Γ : PCtx S) (h : Derivable (Γ ⊢ ⬝)): isMor Γ Γ (id Γ) := by
  induction Γ with
  | nil => apply isMor.nil
  | cons A Γ ih =>
      apply isMor.cons
      . sorry
      . apply Derivable.var
        assumption
        use A; constructor
        . sorry
        . apply isItem.zero







end Morphism

/-
inductive isSubstSeq : PCtx S → ℕ → PCtx S → PTerm S → Prop
| nil : isSubstSeq [T] 0 [] T
| succ : isSubstSeq (T :: Δ) n [] T → isSubstSeq (S :: (T :: Δ)) (n + 1) [] S
| cons : isSubstSeq Γ (n + 1) F T' → isSubstSeq Γ n (f :: F) (T'{f // n})

example : isSubstSeq [T] 0 [] T := by
  apply isSubstSeq.nil

example : isSubstSeq [T₁, T₀] 0 [f] (T₁{f // 0}) := by
  apply isSubstSeq.cons
  apply isSubstSeq.succ
  apply isSubstSeq.nil

example : isSubstSeq [T₂, T₁, T₀] 1 [f] (T₂{f // 1}) := by
  apply isSubstSeq.cons
  apply isSubstSeq.succ
  apply isSubstSeq.succ
  apply isSubstSeq.nil

example : isSubstSeq [T₂, T₁, T₀] 0 [g, f] ((T₂{f // 1}){g // 0}) := by
  apply isSubstSeq.cons
  apply isSubstSeq.cons
  apply isSubstSeq.succ
  apply isSubstSeq.succ
  apply isSubstSeq.nil

example : isSubstSeq [T'] 0 [] T → T = T' := by
  intro h; cases h; rfl

example : isSubstSeq [T', T''] 0 [] T → False := by
  intro h
  cases h
-/
-/
