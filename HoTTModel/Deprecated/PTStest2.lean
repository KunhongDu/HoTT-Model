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
inductive isTrunc : ℕ → List α → List α → Prop
| zero Γ : isTrunc 0 Γ Γ
| succ {k : ℕ} {Γ Γ' : List α} (x : α) : isTrunc k Γ Γ' → isTrunc (k + 1) (x :: Γ) Γ'

def exist_isTrunc_of_isItem (k : ℕ) (Γ : List α) (x : α) :
    (x ↓ k in Γ) → ∃ Γ', isTrunc (k + 1) Γ Γ' := by
  induction k generalizing x Γ
  . intro h; cases h; rename_i Γ
    exact ⟨Γ, isTrunc.succ _ (isTrunc.zero _)⟩
  . intro h; cases h
    rename_i ih _ _ h
    obtain ⟨Γ', hΓ'⟩ := ih _ _ h
    exact ⟨Γ', isTrunc.succ _ hΓ'⟩

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

inductive isSubst (Γ : PCtx S) (t T : PTerm S) : ℕ → PCtx S → PCtx S → Prop
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

open Relation

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
def weakening₀₁ : ∀ (_ : Γ ⊢ t : T) (_ : isInsert Δ A n Γ Γ') (_ : Δ ⊢ A : !s),
    (Γ' ⊢ t ↑ 1 # n : T ↑ 1 # n)
| .var Γ A k h₀ h₁, h₂, h₃ => by
  dsimp
  split_ifs with h
  . apply typing.var _ _ _ _
      (isItemLift_of_isInsert_of_lt h₂ h h₁)
    apply (weakening₀₂ h₀ h₂ h₃)
  . apply typing.var _ _ _ (weakening₀₂ h₀ h₂ h₃)
    obtain ⟨T', hT'⟩ := h₁
    use T'
    rw [hT'.1]
    constructor
    . rw [lift_lift_of_le_of_le _ _ _ _ (by simp)
        (by simp at h ⊢; apply h.trans (Nat.le_succ _))]
    . apply isItem_of_isInsert_of_le h₂ (by simpa using h) hT'.2
| .sort Γ s₁ s₂ h₀ h₁, h₂, h₃ => by
    simp; apply typing.sort _ _ _ h₀ (weakening₀₂ h₁ h₂ h₃)
| .pi Γ A B s₁ s₂ s₃ h₀ h₁ h₃, h₄, h₅ => by
  apply typing.pi
  apply h₀
  apply weakening₀₁ h₁ h₄ h₅
  apply weakening₀₁ h₃ (h₄.succ A) h₅
| .abs Γ A b B s₁ s₂ s₃ h₀ h₁ h₂ h₃, h₄, h₅ => by
  apply typing.abs
  apply h₀
  apply weakening₀₁ h₁ h₄ h₅
  apply weakening₀₁ h₂ (h₄.succ A) h₅
  apply weakening₀₁ h₃ (h₄.succ A) h₅
| .app Γ f A B a h₀ h₁, h₂, h₃ => by
  have : n = 0 + n := by simp
  rw [this, subst_lift]; simp
  apply typing.app
  apply weakening₀₁ h₀ h₂ h₃
  apply weakening₀₁ h₁ h₂ h₃
| .conv Γ a A B s h₀ h₁ h₂, h₃, h₄ => by
  apply typing.conv _ _ (A ↑ 1 # n) _ _ (lift_betac_lift h₀)
  apply weakening₀₁ h₁ h₃ h₄
  apply weakening₀₁ h₂ h₃ h₄

def weakening₀₂ : ∀ (_ : Γ ⊢ ⬝) (_ : isInsert Δ A n Γ Γ') (_ : Δ ⊢ A : !s),
    (Γ' ⊢ ⬝)
| _, .zero, h₃ => wf.cons _ _ _ h₃
| _, .succ u (Δ := Γ) (n := n) h₂, h₃ => by
    rename_i h₁ _
    cases h₁
    rename_i s h₀
    apply wf.cons _ _ s
    have : (!s) = ((!s) ↑ 1 # n) := by rfl
    rw [this]
    apply weakening₀₁ h₀ h₂ h₃
end

end Typing

section Morphism

#check isSubst

@[simp]
def psubst (e : PTerm S) (m : ℕ) : PTerm S → PTerm S
| #n => if n = m then e else #n
| sort M => !M
| app N M => (psubst e m N) ⬝ (psubst e m M)
| pi N M => Π.(psubst e m N) (psubst (e ↑ 1) (m + 1) M)
| abs N M => λ.(psubst e m N) (psubst (e ↑ 1) (m + 1) M)

notation N "{" e " // " m "}ₚ" => psubst e m N

notation N "{" e "}ₚ" => psubst e 0 N

def SubstSq (t : PTerm S) : ℕ → PCtx S → PTerm S
| _, [] => t
| n, A :: Γ => (SubstSq t (n + 1) Γ){A // n}ₚ

example : SubstSq T 0 [] = T := rfl

example : SubstSq T 0 [f] = T{f // 0}ₚ := rfl

example : SubstSq (#2 : PTerm S) 0 [#0, #1, #2] = #2 := rfl

example : SubstSq (#1 : PTerm S) 0 [#0, #1, #2] = #1 := rfl

example : SubstSq (#1 : PTerm S) 1 [#1, #2] = #1 := rfl

example : (#2 : PTerm S){#2 // 2}{#1 // 1}{#0 // 0} = #2 := rfl

inductive isMor (Γ : PCtx S) : PCtx S → PCtx S → Prop
| nil : isMor Γ [] []
| cons : isMor Γ Δ F → (Γ ⊢ f : (SubstSq D 0 F)) → isMor Γ (D :: Δ) (f :: F)

example (Γ Δ F : PCtx S) :
    isMor Γ Δ F → Δ.length = F.length := by
  intro h
  induction Δ generalizing F with
  | nil => cases h; rfl
  | cons A Δ ih =>
      cases h
      rename_i h
      simp [ih _ h]

def id₀ : ℕ → PCtx S →  PCtx S
| _, [] => []
| n, _ :: S => (#n) :: (id₀ (n + 1) S)

def id : PCtx S → PCtx S := id₀ 0

example : id [T₃, T₂, T₁, T₀] = [#0, #1, #2, #3] := rfl

def aux: ∀ (_ : Γ ⊢ t : T), t = t ↑ 1 # Γ.length
| .var Γ T n h₁ ⟨B, h₂⟩ => by simp [h₂.2.lt_length]
| .sort _ _ _ _ _ => by simp
| .conv _ _ _ _ _ _ h _ => aux h
| .app _ _ _ _ _ h₁ h₂ => by
  simp; exact ⟨aux h₁, aux h₂⟩
| .abs _ _ _ _ _ _ _ _ h₀ _ h₂ => by
  simp; exact ⟨aux h₀, aux h₂⟩
| .pi _ _ _ _ _ _ _ h₀ h₁ => by
  simp; exact ⟨aux h₀, aux h₁⟩

lemma aux₀₁ : ∀ {n : ℕ} {A : PTerm S} (_ : A = A ↑ 1 # n + 1), A{#1 // n} = A ↑ 1 # n
| 0, .var k, h => by simp at h; split_ifs at h with h'; cases h'; rfl; cases h
| n + 1, var k, h => by
  simp at h ⊢
  split_ifs at h with h₁
  split_ifs with h₂ h₃
  rfl
  rw [Nat.add_comm]
  apply False.elim (h₃ $ Nat.le_antisymm (Nat.le_of_lt_succ h₁) (Nat.le_of_not_lt h₂))
  cases h
| _, .sort _, _ => rfl
| _, .pi A B, h => by
  simp at h ⊢
  exact ⟨aux₀₁ h.1, aux₀₁ h.2⟩
| _, .abs A B, h => by
  simp at h ⊢
  exact ⟨aux₀₁ h.1, aux₀₁ h.2⟩
| _, .app f a, h => by
  simp at h ⊢
  exact ⟨aux₀₁ h.1, aux₀₁ h.2⟩

lemma aux₀₂ : ∀ {n : ℕ} {A : PTerm S} (_ : A = A ↑ 1 # n + 1), A{#1 // n} = A ↑ 1 # n
| 0, .var k, h => by simp at h; split_ifs at h with h'; cases h'; rfl; cases h
| n + 1, var k, h => by
  simp at h ⊢
  split_ifs at h with h₁
  split_ifs with h₂ h₃
  rfl
  rw [Nat.add_comm]
  apply False.elim (h₃ $ Nat.le_antisymm (Nat.le_of_lt_succ h₁) (Nat.le_of_not_lt h₂))
  cases h
| _, .sort _, _ => rfl
| _, .pi A B, h => by
  simp at h ⊢
  exact ⟨aux₀₁ h.1, aux₀₁ h.2⟩
| _, .abs A B, h => by
  simp at h ⊢
  exact ⟨aux₀₁ h.1, aux₀₁ h.2⟩
| _, .app f a, h => by
  simp at h ⊢
  exact ⟨aux₀₁ h.1, aux₀₁ h.2⟩

lemma aux₀ : ∀ {Γ : PCtx S} (_ : A :: Γ ⊢ ⬝), SubstSq A 0 (id₀ 1 Γ) = A ↑ 1
| [], .cons _ _ s h => aux h
| B :: Γ, .cons _ _ s h => by
  simp [SubstSq]
  have : SubstSq A 0 (id₀ 2 Γ) = (SubstSq A 0 (id₀ 2 Γ)) ↑ 1 # 1 := sorry
  

example : ∀ (Γ : PCtx S) (_ : Γ ⊢ ⬝), isMor Γ Γ (id Γ)
| [], _ => isMor.nil
| A :: Γ, .cons _ _ s h => by
  apply isMor.cons
  . sorry
  . simp










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