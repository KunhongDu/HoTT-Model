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

def lift_inj {i c : ℕ} :
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

def lift0_inj {i : ℕ} :
    (M ↑ i) = (N ↑ i) → M = N :=
  lift_inj

def lift_zero {c : ℕ} :
    (M ↑ 0 # c) = M := by
  induction M generalizing c
  all_goals simp
  all_goals rename_i ih₁ ih₂
  all_goals exact ⟨ih₁, ih₂⟩

def lift_lift (i j k : ℕ) :
    ((M ↑ j # i) ↑ k # (j + i)) = M ↑ (j + k) # i := by
  sorry

def lift_lift_of_le (i j k n : ℕ) :
    i ≤ n → ((M ↑ j # i) ↑ k # (j + n)) = (M ↑ k # n) ↑ j # i := by
  sorry

def lift_lift_of_le_of_le (i j k n : ℕ) :
    i ≤ n → k ≤ i + n → ((M ↑ n # i) ↑ j # k) = M ↑ (n + j) # i := by
  sorry

def lift0_lift0 (i j : ℕ) :
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
    (M{N // j} ↑ k # (j + i)) = (M ↑ k # j + i + 1){N ↑ k # i // j} := by
  sorry

def subst_lift_of_le (i j n : ℕ) :
    i ≤ n → (M{N // n} ↑ j # i) = (M ↑ j # i){N // j + n} := by
  sorry

def lift_subst_of_le_of_le (i j k : ℕ) :
    i ≤ k → k ≤ i + n → (M ↑ (n + 1) # j){N // k} = M ↑ n # i := by
  sorry

variable {P : PTerm S}

def subst_subst (i j : ℕ) :
    M{N // j}{P // i + j} = M{P // i + j + 1}{N{P // i} // j} := by
  sorry

def subst0_subst0 (k : ℕ) :
    M{N}{P // k} = M{P // k + 1}{N{P // k}} :=
  subst_subst _ 0

end LiftSubst

section Context

def PCtx (S : Specification) := List (PTerm S)

abbrev PCtx.lift (i c : ℕ) : PCtx S → PCtx S := List.map (PureTypeSystem.lift i c)

variable {α : Type*}

inductive isItem : α → List α → ℕ → Prop
| zero Γ : isItem x (x :: Γ) 0
| succ {Γ n} y : isItem x Γ n → isItem x (y :: Γ) (n + 1)

notation x " ↓ " n " in " Γ => isItem x Γ n

lemma isItem.lt_length : ∀ (_ : x ↓ n in Γ), n < length Γ
| .zero _ => by simp
| .succ x h => by simp; apply lt_length h

-- need a better name

def isItem_unique {x y : α} {Γ : List α} {n : ℕ} :
    (x ↓ n in Γ) → (y ↓ n in Γ) → x = y := by
  induction n generalizing x y Γ
  . intro h₁ h₂
    cases h₁; cases h₂; rfl
  . intro h₁ h₂
    cases h₁; cases h₂
    rename_i ih _ _ h₁ h₂
    apply ih h₁ h₂

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

/-
def exist_isTrunc_of_isItem (k : ℕ) (Γ : List α) (x : α) :
    (x ↓ k in Γ) → ∃ Γ', isTrunc (k + 1) Γ Γ' := by
  induction k generalizing x Γ
  . intro h; cases h; rename_i Γ
    exact ⟨Γ, isTrunc.succ _ (isTrunc.zero _)⟩
  . intro h; cases h
    rename_i ih _ _ h
    obtain ⟨Γ', hΓ'⟩ := ih _ _ h
    exact ⟨Γ', isTrunc.succ _ hΓ'⟩
-/
def isIerm_of_isTrunc {Γ Δ : List α} {A : α} : ∀ {k : ℕ},
    isTrunc k Γ (A :: Δ) → A ↓ k in Γ
| 0, h => by cases h; apply isItem.zero
| k + 1, .succ _ h => isItem.succ _ (isIerm_of_isTrunc h)

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

def isItem_of_isInsert_of_lt {t : PTerm S} {n : ℕ} {Γ Δ Δ' : PCtx S} :
    isInsert Γ t n Δ Δ' → ∀ {k}, (k < n → ∀ {u}, (u ↓ k in Δ) →
      (u ↑ 1 # (n - (k + 1)) ) ↓ k in Δ') := by
  sorry

def isItemLift (t : PTerm S) (Γ : PCtx S) (n : ℕ) : Prop :=
    ∃ u, (t = u ↑ n + 1) ∧ u ↓ n in Γ

notation x " ↓ " n " sub " Γ => isItemLift x Γ n

def isItemLift_of_isInsert_of_lt {t u : PTerm S} {n : ℕ} {Γ Δ Δ' : PCtx S}
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

inductive isSubst (Γ : PCtx S) (t T : PTerm S) : ℕ → PCtx S → PCtx S → Type _
| zero : isSubst Γ t T 0 (T :: Γ) Γ
| succ {n Δ Δ'} w : isSubst Γ t T n Δ Δ' → isSubst Γ t T (n + 1) (w :: Δ) (w{t // n} :: Δ')

def isTerm_of_isSubst_of_le {n : ℕ} {Γ Δ Δ' : PCtx S} {t T : PTerm S} :
    isSubst Γ t T n Δ Δ' → ∀ {k}, n ≤ k → (∀ {v}, (v ↓ k + 1 in Δ) → v ↓ k in Δ') := by
  induction n
  . intro h k hk v hv
    cases h; cases hv
    assumption
  . sorry

end Context

section Reduction

variable {S : Specification}

inductive beta : PTerm S → PTerm S → Type _
| head (A M N : PTerm S) : beta ((λ.A M) ⬝ N) (M{N ↑ 1 # 0 // 0})
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

def lift_beta_lift (h : A →β B) :
    (A ↑ i # n) →β B ↑ i # n := by
  sorry

def lift_betac_lift (h : A ≃β B) :
    (A ↑ i # n) ≃β B ↑ i # n := by
  sorry

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

#check typing.rec
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

lemma exists_of_cons (h : A :: Γ ⊢ ⬝) : ∃ s, Nonempty (Γ ⊢ A : !s) := by
  cases h with
  | cons Γ A s h => exact ⟨s, ⟨h⟩⟩

def exists_of_cons' (h : A :: Γ ⊢ ⬝) : Σs, (Γ ⊢ A : !s) := by
  cases h with
  | cons Γ A s h => exact ⟨s, h⟩

def wf_of_cons (h : A :: Γ ⊢ ⬝) : Γ ⊢ ⬝ :=
  wf_of_typing (exists_of_cons' h).snd

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
/-
def exists_of_pi_typing : ∀ (_ : Γ ⊢ Π.A B : T),
    ∃ s₁ s₂ s₃, (T ≃β !s₃) ∧ S.rel s₁ s₂ s₃ ∧ Nonempty (Γ ⊢ A : !s₁) ∧ Nonempty (A :: Γ ⊢ B : !s₂) :=
  sorry

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
def weakening_typing : ∀ (_ : Γ ⊢ t : T) (_ : isInsert Δ A n Γ Γ') (_ : Δ ⊢ A : !s),
    (Γ' ⊢ t ↑ 1 # n : T ↑ 1 # n)
| .var Γ A k h₀ h₁, h₂, h₃ => by
  dsimp
  split_ifs with h
  . apply typing.var _ _ _ _
      (isItemLift_of_isInsert_of_lt h₂ h h₁)
    apply (weakening_wf h₀ h₂ h₃)
  . apply typing.var _ _ _ (weakening_wf h₀ h₂ h₃)
    obtain ⟨T', hT'⟩ := h₁
    use T'
    rw [hT'.1]
    constructor
    . rw [lift_lift_of_le_of_le _ _ _ _ (by simp)
        (by simp at h ⊢; apply h.trans (Nat.le_succ _))]
    . apply isItem_of_isInsert_of_le h₂ (by simpa using h) hT'.2
| .sort Γ s₁ s₂ h₀ h₁, h₂, h₃ => by
    simp; apply typing.sort _ _ _ h₀ (weakening_wf h₁ h₂ h₃)
| .pi Γ A B s₁ s₂ s₃ h₀ h₁ h₃, h₄, h₅ => by
  apply typing.pi
  apply h₀
  apply weakening_typing h₁ h₄ h₅
  apply weakening_typing h₃ (h₄.succ A) h₅
| .abs Γ A b B s₁ s₂ s₃ h₀ h₁ h₂ h₃, h₄, h₅ => by
  apply typing.abs
  apply h₀
  apply weakening_typing h₁ h₄ h₅
  apply weakening_typing h₂ (h₄.succ A) h₅
  apply weakening_typing h₃ (h₄.succ A) h₅
| .app Γ f A B a h₀ h₁, h₂, h₃ => by
  have : n = 0 + n := by simp
  rw [this, subst_lift]; simp
  apply typing.app
  apply weakening_typing h₀ h₂ h₃
  apply weakening_typing h₁ h₂ h₃
| .conv Γ a A B s h₀ h₁ h₂, h₃, h₄ => by
  apply typing.conv _ _ (A ↑ 1 # n) _ _ (lift_betac_lift h₀)
  apply weakening_typing h₁ h₃ h₄
  apply weakening_typing h₂ h₃ h₄

def weakening_wf : ∀ (_ : Γ ⊢ ⬝) (_ : isInsert Δ A n Γ Γ') (_ : Δ ⊢ A : !s),
    (Γ' ⊢ ⬝)
| _, .zero, h₃ => wf.cons _ _ _ h₃
| _, .succ u (Δ := Γ) (n := n) h₂, h₃ => by
    rename_i h₁ _
    cases h₁
    rename_i s h₀
    apply wf.cons _ _ s
    have : (!s) = ((!s) ↑ 1 # n) := by rfl
    rw [this]
    apply weakening_typing h₀ h₂ h₃
end

#check ℕ

def lift_inv_of_typing : ∀ (_ : Γ ⊢ t : T), (t ↑ 1 # Γ.length) = t
| .var Γ T n h₁ ⟨B, h₂⟩ => by simp [h₂.2.lt_length]
| .sort _ _ _ _ _ => by simp
| .conv _ _ _ _ _ _ h _ => lift_inv_of_typing h
| .app _ _ _ _ _ h₁ h₂ => by
  simp; exact ⟨lift_inv_of_typing h₁, lift_inv_of_typing h₂⟩
| .abs _ _ _ _ _ _ _ _ h₀ _ h₂ => by
  simp; exact ⟨lift_inv_of_typing h₀, lift_inv_of_typing h₂⟩
| .pi _ _ _ _ _ _ _ h₀ h₁ => by
  simp; exact ⟨lift_inv_of_typing h₀, lift_inv_of_typing h₁⟩

def lift_inv_of_typing'  (h : Γ ⊢ t : T) : (T ↑ 1 # Γ.length) = T := sorry

def lift_inv_of_typing''  (h : T :: Γ ⊢ ⬝) : (T ↑ 1 # Γ.length) = T := sorry

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
| Γ, A :: Δ, h₁, .cons _ _ _ h₂ =>
  weakening_wf (append_wf h₁ (wf_of_typing h₂)) isInsert.zero
    (append_typing h₁ h₂)

def substitution_typing : ∀ (_ : Γ ⊢ t : T) (_ : isSubst Δ a A n Γ Γ') (_ : Δ ⊢ a : A),
  Γ' ⊢ t{a//n} : T{a//n} := sorry

def substitution_wf : ∀ (_ : Γ ⊢ ⬝ ) (_ : isSubst Δ a A n Γ Γ') (_ : Δ ⊢ a : A),
  Γ' ⊢ ⬝ := sorry

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
| .trans _ (C :: Θ) _ h₁ h₂ => (head h₁).trans _ _ _ (head h₂)

def betac.head {Γ Δ : PCtx S} {A B : PTerm S} : ∀ (_ : (A :: Γ) ≃β (B :: Δ)), A ≃β B
| .betar _ _ h => PureTypeSystem.betac.betar _ _ h.head
| .symm _ _ h => PureTypeSystem.betac.symm _ _ (head h)
| .trans _ [] _ h₁ h₂ => by simpa using h₁.length_eq
| .trans _ (C :: Θ) _ h₁ h₂ => (head h₁).trans _ _ _ (head h₂)

end PCtx

def term_betar_typing : ∀ {Γ : PCtx S} {t s M} (_: Γ ⊢ t : M) (_ : t ↠β s), Γ ⊢ s : M := sorry

-- reduced to expansion???
def term_betac_typing : ∀ {Γ : PCtx S} {t s M} (_: Γ ⊢ t : M) (_ : t ≃β s), Γ ⊢ s : M
| Γ, t, s, M, h, .betar _ _ h' => term_betar_typing h h'
| Γ, t, s, M, h, .symm _ _ h' => by sorry
| Γ, t, s, M, h, .trans _ r _ h₁ h₂ => by sorry

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

inductive isSimulSubst : PCtx S → ℕ → PCtx S → PCtx S → Type _
| nil Γ n : isSimulSubst Γ n [] Γ
| cons Γ n f F Γ' Γs Δ A s :
  isSimulSubst Γ' (n + 1) F Γ → isTrunc (n + 1) Γ Γs →
  (Γs ⊢ A : !s) → (Γs ⊢ f : A) → -- isInsert Γs A (n + 1) Γ Γ₁ →
  isSubst Γs f A n Γ Δ → isSimulSubst Γ' n (f :: F) Δ

def simulSubst_wf (h : Γ' ⊢ ⬝) : ∀ (_ : isSimulSubst Γ' n F Γ),
    Γ ⊢ ⬝
| .nil Γ n => h
| .cons Γ n f F Γ' Γs Δ A s h₁ h₂ h₃ h₄ h₅ =>
  substitution_wf (simulSubst_wf h h₁) h₅ h₄

def simulSubst_typing (h : Γ' ⊢ t : T) : ∀ (_ : isSimulSubst Γ' n F Γ),
    Γ ⊢ simulSubst t n F : simulSubst T n F
| .nil Γ n => h
| .cons Γ n f F Γ' Γs Δ A s h₁ h₂ h₃ h₄ h₅ =>
  substitution_typing (simulSubst_typing h h₁) h₅ h₄

inductive isMor (Γ : PCtx S) : PCtx S → PCtx S → Type _
| nil : isMor Γ [] []
| cons : isMor Γ Δ F → (Γ ⊢ simulSubst D 0 F : !s) →
    (Γ ⊢ f : (simulSubst D 0 F)) → isMor Γ (D :: Δ) (f :: F)

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
| .cons Γ n f F Γ' Γs Δ A s h₁ h₂ h₃ h₄ h₅ =>
  h₅.length_lt.le.trans h₁.length_le

lemma isSimulSubst.nil_of_nil {F Δ : PCtx S} (h : isSimulSubst [] n F Δ) :
    Δ = [] := by
  apply List.eq_nil_of_length_eq_zero
  apply Nat.eq_zero_of_le_zero
  apply h.length_le

def isSimulSubst.append : ∀ {Γ Θ F} (_ : isSimulSubst Γ k F Θ),
  isSimulSubst (A :: Γ) (k + 1) F ((simulSubst A k F) :: Θ)
| Γ, Θ, [], h => by cases h; apply nil
| Γ, Θ, f :: F, .cons Γ' _ _ _ _ Γs _ C s h₁ h₂ h₃ h₄ h₅ => by
  simp
  apply cons
  apply append h₁
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
  apply isSimulSubst.append (isMor'_isMor h₁)
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
  rw [(List.cons.inj (h₁.eq h₁.drop.append)).1] at h₃ h₄
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

lemma liftaux (hn : k ≤ n ) : ∀ {t : PTerm S} (_ : (t ↑ 1 # k) = t) , t{f//n} = t
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

lemma testeq {T : PTerm S} : ∀ {F G : PCtx S} ,
  simulSubst T k (pcomp F G) = simulSubst (simulSubst T k G) k F
| F, [] => by
  simp [liftinv]
  sorry
| [], g :: G => by
  simp
  rw [testeq]
  rfl
| f :: F, g :: G => by
  simp
  rw [testeq]
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

lemma testeq {Γ Δ Θ : PCtx S} {T : PTerm S} (h : Θ' ⊢ T : !s):
  ∀ {F G : PCtx S} (_ : isMor Γ Δ F) (_ : isMor Δ Θ G) (_ : isTrunc k Θ' Θ),
  simulSubst T k (pcomp F G) = simulSubst (simulSubst T k G) k F
| F, [], h₁, h₂, h₃ => by
  simp
  cases h₂
  rw [liftinv (le_refl _)]
  rw [← h₃.nil_length]
  apply lift_inv_of_typing h
| [], G, h₁, h₂, h₃ => by
  cases h₁
  simp
| f :: F, g :: G, h₁, isMor.cons h₂ h₃ h₄, h₅ => by
  simp
  rw [testeq h h₁ h₂ (isTrunc.pred h₅)]
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
  apply testeq (exists_of_cons' hΘ).snd h₁ h₂ (isTrunc.zero _)

end pcomp

section id


@[simp]
def idN : ℕ → ℕ →  PCtx S
| _, 0 => []
| n, k + 1 => (#n) :: (idN (n + 1) k)

def id₀ (n : ℕ) (Γ : PCtx S) : PCtx S := idN n Γ.length

@[simp]
lemma idN_length {n} : ∀ {k}, (idN n k : PCtx S).length = k
| 0 => rfl
| k + 1 => by simp [idN_length]

lemma idN_append_idN : ∀ (n k m : ℕ),
  List.append (idN n k : PCtx S) (idN (n + k) m) = idN n (k + m)
| _, 0, _ => by simp
| n, k + 1, m => by
  rw [Nat.add_assoc, Nat.add_comm 1 m]; simp
  rw [Nat.add_comm k 1, ← Nat.add_assoc]
  apply idN_append_idN

lemma simulSubst_var_idN_of_lt {n m l : ℕ} (hl : n < l) : ∀ {s : ℕ} ,
    simulSubst (#n : PTerm S) l (idN m s) = (#n)
| 0 => rfl
| s + 1 => by
  simp; rw [simulSubst_var_idN_of_lt (hl.trans (Nat.lt_succ_self _))]
  simp [hl]

lemma simulSubst_var_idN_of_length_add_le {n m l : ℕ} : ∀ {s : ℕ} (_ : s + l ≤ n),
    simulSubst (#n : PTerm S) l (idN m s)  = (#n - s)
| 0, h => by simp
| s + 1, h => by
  simp
  rw [simulSubst_var_idN_of_length_add_le (by simpa only [Nat.add_comm l, ← Nat.add_assoc])]
  have : l < n - s := by
    rw [Nat.lt_sub_iff_add_lt, ← Nat.succ_le_iff]
    convert h using 1
    simp [Nat.add_comm l, Nat.add_assoc]
  simp [if_neg (not_lt_of_lt this), if_neg this.ne.symm, Nat.sub_sub]

-- can be strengthened???? `n ≤ s`
lemma simulSubst_var_idN_of_lt_length {n k l : ℕ} {s : ℕ} (hn : n < s) :
    simulSubst (#n : PTerm S) l (idN k s) = (#n) ↑ k # l := by
  rcases lt_or_le n l with hl | hl
  . simp [hl, simulSubst_var_idN_of_lt hl]
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
    rw [simulSubst_var_idN_of_lt (by simp only [ha, Nat.lt_add_one])]
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

def aux₁wf (h : A :: Γ ⊢ ⬝) : (A ↑ 1 # Γ.length) = A := by
  cases h
  apply lift_inv_of_typing (by assumption)

def wf_of_isTrunc {k} {Γ Δ : PCtx S} : ∀ (_ : isTrunc k Γ Δ) (_ : Γ ⊢ ⬝),
    Δ ⊢ ⬝
| .zero _, h => h
| .succ _ _, h => by
  apply wf_of_isTrunc (by assumption)
  cases h
  apply wf_of_typing (by assumption)


def isMorAux {k} {Γ Δ : PCtx S} {A} (h₀ : isTrunc k Γ (A :: Δ)) (h₁ : Γ ⊢ ⬝) :
    Γ ⊢ #k : simulSubst A 0 (id₀ (k + 1) Δ) := by
  refine typing.var _ _ _ h₁ ⟨A, ⟨?_, isIerm_of_isTrunc h₀⟩⟩
  apply isMorAuxLift
  apply aux₁wf
  apply wf_of_isTrunc h₀ h₁

def id_isMor : ∀ {Γ Δ : PCtx S} (_ : isTrunc k Γ Δ) (_ : Γ ⊢ ⬝), isMor Γ Δ (id₀ k Δ)
| Γ, [], h, h' => by apply isMor.nil
| Γ, A :: Δ, h, h' => by
    apply isMor.cons
    apply id_isMor (isTrunc.pred h) h'
    simpa [simulSubst_sort] using simulSubst_typing (append_typing h' (exists_of_cons' (wf_of_isTrunc h h')).snd)
      (isMor'_isMor (id_isMor (isTrunc.pred h) h'))
    apply isMorAux h h'

end id
