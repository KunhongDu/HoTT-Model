import Mathlib.Data.Fin.Basic

universe u

inductive Ty (α : Type u)
| base : α → Ty α
| map : Ty α → Ty α → Ty α

notation a"->"b => Ty.map a b

variable (α : Type u)

inductive Tm (α : Type u)
| var : ℕ → Tm α
| abs : Ty α → Tm α → Tm α --- abstraction
| app : Tm α → Tm α → Tm α --- application

notation "#"n => Tm.var n
prefix:max "λ." => Tm.abs
notation t"["s"]" => Tm.app t s

-- define Ctx as lists (in reverse direction)
abbrev Ctx := List (Ty α)

def EmptyCtx : Ctx α := []

abbrev Cons {α} (Γ : Ctx α) (A : Ty α) := List.cons A Γ

abbrev Extend {α} (Γ Δ : Ctx α) := Δ ++ Γ

def Lift {α} (i c: ℕ) : Tm α → Tm α
| #n => if n < c then #n else #(n + i)
| Tm.abs T t => λ.T (Lift i (c+1) t)
| Tm.app t s => (Lift i c t)[Lift i c s]

notation t" ↑ "i" # "c => Lift i c t

lemma lift_var {α} {n i c} : ((#n)↑i#c : Tm α) = if n < c then #n else #(n + i) := rfl

lemma lift_var_lt {α} {n i c} (h : n < c) : ((#n)↑i#c : Tm α) = #n := by rw [lift_var]; simp only [h, ↓reduceIte]

lemma lift_var_not_lt {α} {n i c} (h : ¬ n < c) : ((#n)↑i#c : Tm α) = #(n + i) := by rw [lift_var]; simp only [h, ↓reduceIte]

def Drop {α} (i c: ℕ) : Tm α → Tm α
| #n => if n < c then #n else #(n - i)
| Tm.abs T t => λ.T (Drop i (c+1) t)
| Tm.app t s => (Drop i c t)[Drop i c s]

notation t" ↓ "i" # "c => Drop i c t

lemma drop_var {α} {n i c} : ((#n)↓i#c : Tm α) = if n < c then #n else #(n - i) := rfl

lemma drop_var_lt {α} {n i c} (h : n < c) : ((#n)↓i#c : Tm α) = #n := by rw [drop_var]; simp only [h, ↓reduceIte]

lemma drop_var_not_lt {α} {n i c} (h : ¬ n < c) : ((#n)↓i#c : Tm α) = #(n - i) := by rw [drop_var]; simp only [h, ↓reduceIte]


def Subst {α} (e : Tm α) (m : ℕ) : Tm α → Tm α
| #n => if n = m then e else #n
| Tm.abs T t => λ. T (Subst (e ↑ 1 # 0) (m + 1) t)
| Tm.app t s => (Subst e m t)[Subst e m s]

notation t"["e"//"m"]" => Subst e m t

open Tm Ty List

inductive Under {α} : Ctx α → Tm α → Ty α → Prop
| var Γ (i : Fin (length Γ)) : Under Γ (#↑i) (get Γ i)
| abs Γ A t B : Under (Cons Γ A) t B → Under Γ (λ.A t) (map A B)
| app Γ t A B s : Under Γ t  (A -> B) → Under Γ s A → Under Γ (t[s]) B

notation Γ " ⊢ " t " : " A  => Under Γ t A

variable (Γ : Ctx α) (t : Tm α) (A : Ty α)

lemma unique_typing (Γ : Ctx α) t A B (h : Γ ⊢ t : A) (h' : Γ ⊢ t : B) : A = B := by
  induction h generalizing B with
  | var Γ' i =>
      generalize hi : (#↑i) = t at h'
      cases h' with
      | var Γ j =>
          have : i = j := Fin.val_injective <| Tm.var.inj hi
          rw [this]
      | abs Γ A t B _ =>
          exfalso
          have : (#↑i) ≠ λ.A t := fun h => Tm.noConfusion h
          apply this hi
      | app Γ t A B s =>
          exfalso
          have : (#↑i) ≠ t[s] := fun h => Tm.noConfusion h
          apply this hi
  | abs Γ' C s D _ ih =>
      generalize hi : (λ.C s) = t at h'
      cases h' with
      | var Γ j =>
        exfalso
        have : (λ.C s) ≠ (#↑j) := fun h => Tm.noConfusion h
        apply this hi
      | abs Γ A t B hyp =>
          have := Tm.abs.inj hi
          rw [this.1]
          rw [← this.1, ← this.2] at hyp
          have := ih B hyp
          rw [this]
      | app _ t _ _ s' _ _ =>
          exfalso
          have : λ.C s ≠ t[s'] := fun h => Tm.noConfusion h
          apply this hi
  | app Γ t' C D s _ _ ih₁ _ =>
      generalize hi : t'[s] = t at h'
      cases h' with
      | var _ j =>
        exfalso
        have : t'[s] ≠ #↑j := fun h => Tm.noConfusion h
        apply this hi
      | abs _ A t _ hyp =>
        exfalso
        have : t'[s] ≠ λ.A t := fun h => Tm.noConfusion h
        apply this hi
      | app Γ t A B s' h₁ h₂ =>
        have := Tm.app.inj hi
        rw [← this.1] at h₁
        have := ih₁ (A->B) h₁
        exact (Ty.map.inj this).2

lemma weakening {α} (E F G: Ctx α) e B (h :(G ++ E) ⊢ e : B) : (G ++ F ++ E) ⊢ (e ↑ length F # length G) : B := by
  generalize hG' : (G ++ E) = G' at h
  induction h generalizing F G with
  | var Γ i =>
      by_cases hG : i < length G
      have : ((#↑i)↑length F#length G : Tm α) = #(↑i) := lift_var_lt hG
      rw [this]
      have aux : ↑i < length (G ++ F ++ E) := by apply Fin.val_lt_of_le; rw [← hG']; simp
      have : get Γ i = get (G ++ F ++ E) ⟨↑i, aux⟩  := by
        rw [get_of_eq hG'.symm, get_of_eq (append_assoc G F E)]
        apply Eq.trans (get_append _ hG) (get_append _ hG).symm
      rw [this]
      have : (#↑i : Tm α) = (#↑(⟨↑i, aux⟩ : Fin (length (G ++ F ++ E))) : Tm α) := by apply congrFun rfl
      rw [this]
      apply Under.var _ _

      have : ((#↑i)↑length F#length G : Tm α) = #(↑i + length F) := lift_var_not_lt hG
      rw [this]
      have aux : ↑(i + length F) < length (G ++ F ++ E) := by simp only [length_append]; rw [Nat.add_assoc, Nat.add_comm (length F), ← Nat.add_assoc, Nat.add_lt_add_iff_right]; apply Fin.val_lt_of_le; rw [← hG']; simp
      have : get Γ i = get (G ++ F ++ E) ⟨↑(i + length F), aux⟩  := by
        rw [get_of_eq hG'.symm, get_of_eq (append_assoc G F E)]
        -- sub of Nat causes so many troubles!!!
        rw [get_append_right' (le_of_not_lt hG),
            get_append_right' (by simp; apply le_trans (le_of_not_lt hG) (Nat.le_add_right _ _)),
            get_append_right' (by simp; rw [Nat.add_comm, Nat.add_sub_assoc (le_of_not_lt hG)]; apply Nat.le_add_right)]
        apply congrArg
        simp only [Fin.mk.injEq]
        rw [← Nat.sub_add_eq, Nat.add_comm (length G), Nat.sub_add_eq, Nat.add_sub_self_right]
      rw [this]
      have : (#↑i + length F : Tm α) = (#↑(⟨↑(i + length F), aux⟩ : Fin (length (G ++ F ++ E))) : Tm α) := by apply congrFun rfl
      rw [this]
      apply Under.var _ _

  | abs Γ C s D _ ih =>
      exact Under.abs _ _ _ _ (ih F ([C] ++ G) (congrArg (fun x ↦ Cons x C) hG'))
      -- have aux : λ.C (s↑length F#length ([C] ++ G)) = λ.C s↑length F#length G := rfl
      -- rfl is really much more powerful than expected
  | app Γ t C D s _ _ ih₁ ih₂ =>
      exact Under.app _ _ _ _ _ (ih₁ F G hG') (ih₂ F G hG')

example (Γ : Ctx α) t B A (h : Γ ⊢ t : B) : (Cons Γ A) ⊢ (t ↑ 1 # 0) : B := weakening Γ [A] [] t B h

lemma lift_lift {m n l: ℕ} {a : Tm α} : ((a↑n#l)↑m#l) = a↑(m+n)#l := by
  induction a generalizing l with
  | var k =>
      by_cases hk : k < l
      simp [lift_var_lt hk]
      simp [lift_var_not_lt hk, @lift_var_not_lt _ (k+n) m l (by simp only [not_lt]; apply le_trans (Nat.le_add_right l n) ((Nat.add_le_add_right (le_of_not_lt hk)) _)), Nat.add_comm n, Nat.add_assoc]
  | abs T t ih => simp [Lift]; exact ih
  | app s t ih ih' => simp [Lift]; exact ⟨ih, ih'⟩

lemma lift_drop  {m n k l: ℕ} {a : Tm α} (h₁ : k < l) (h₂ : l ≤ k + m) (h₃ : n ≤ m): ((a↑m#k)↓n#l) = a↑(m-n)#k := by
  induction a generalizing l k with
  | var s =>
    by_cases hs : s < k
    simp [lift_var_lt hs, drop_var_lt (lt_trans hs h₁)]
    simp [lift_var_not_lt hs, drop_var_not_lt (not_lt_of_le <| le_trans h₂ ((Nat.add_le_add_iff_right).mpr (le_of_not_lt hs))),Nat.add_sub_assoc h₃]
  | abs T t ih =>
    simp [Lift, Drop]
    apply ih (by simp [h₁]) (by rwa [Nat.add_assoc, Nat.add_comm 1 m, ← Nat.add_assoc, Nat.add_le_add_iff_right])
  | app s t ih ih' =>
    simp [Lift, Drop]
    exact ⟨ih h₁ h₂, ih' h₁ h₂⟩


lemma abs_subst_aux : ((λ.C s)[a↑(length Δ + 1)#0//length Δ]↓ 1 #length Δ + 1) = λ.C (s[a↑(Nat.succ (length Δ) + 1)#0//Nat.succ (length Δ)]↓ 1 #Nat.succ (length Δ) + 1) := by
  calc ((λ.C s)[a↑(length Δ + 1)#0//length Δ]↓ 1 #length Δ + 1) = (λ.C (s[((a↑(length Δ + 1)#0)↑ 1 #0)//length Δ + 1]))↓ 1 #length Δ + 1:= rfl
  _ = (λ.C (s[((a↑(length Δ + 2)#0))//length Δ + 1]))↓ 1 #length Δ + 1 := by simp [lift_lift]; rw [← Nat.add_assoc, Nat.add_comm 1]
  _ = λ.C (s[a↑Nat.succ (length Δ) + 1 # 0 //Nat.succ (length Δ)] ↓ 1 # Nat.succ (length Δ) + 1) := rfl

lemma subst (Γ Δ: Ctx α) a A b B (h₁ : Γ ⊢ a : A)  (h₂ : (Δ ++ [A] ++ Γ) ⊢ b : B) : (Δ ++ Γ) ⊢ (b[a ↑ (length Δ + 1) # 0 //(length Δ)]↓ 1 # (length Δ + 1)) : B := by
  generalize hΘ : (Δ ++ [A] ++ Γ) = Θ at h₂
  induction h₂ generalizing Δ with
  | var Γ' i =>
    by_cases hi : i < length Δ
    have aux₀ : i < length (Δ ++ Γ) := by simp only [length_append, Nat.lt_add_right _ hi]
    have aux₁ : ((#↑i : Tm α)[a↑length Δ + 1 # 0 //length Δ]↓ 1 # length Δ + 1) = (#↑i) := by
      simp only [Subst, hi.ne, ↓reduceIte, Drop, (Nat.lt_succ.mpr (le_of_lt hi))]
    have aux₂ : (List.get Γ' i) = (List.get (Δ ++ Γ) ⟨i, aux₀⟩) := by
      rw [get_of_eq hΘ.symm, get_append _ hi, get_append, get_append]
    have aux₃ : (#↑i : Tm α) = (#↑(⟨↑i, aux₀⟩ : Fin (length (Δ ++ Γ))) : Tm α) := by apply congrFun rfl
    rw [aux₁, aux₂, aux₃]
    apply Under.var

    by_cases hi' : i = length Δ
    have aux₁ : ((#↑i : Tm α)[a↑length Δ + 1 # 0 //length Δ]↓ 1 # length Δ + 1) = a↑(length Δ)#0 := by
      simp only [Subst, hi', ↓reduceIte]
      apply lift_drop
      repeat simp
    have aux₂ : List.get Γ' i = A := by
      rw [get_of_eq hΘ.symm, get_append, get_append_right _ _ hi]
      simp only [length_singleton, get_singleton]
      simp only [hi', length_append, length_singleton, Nat.lt_succ_self]
      simp only [hi', Nat.sub_self, length_singleton, Nat.zero_lt_one]
    rw [aux₁, aux₂]
    exact weakening Γ Δ [] a A h₁

    have hi := Ne.lt_of_le (Ne.symm hi') (le_of_not_lt hi)
    have aux₀ : ↑i - 1 < length (Δ ++ Γ) := by
      by_cases hi₀ : (i : ℕ) ≠ 0
      apply Nat.lt_of_succ_lt_succ
      rw [← Nat.pred_eq_sub_one, Nat.succ_pred hi₀]
      apply Fin.val_lt_of_le
      simp [hΘ.symm, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [ne_eq, not_not] at hi₀
      rw [← Nat.pred_eq_sub_one, hi₀, Nat.pred_zero]
      simp only [length_append]
      apply Nat.add_pos_left
      rw [hi₀, ← ne_eq] at hi'
      apply Nat.pos_of_ne_zero hi'.symm
    have aux₁ : ((#↑i : Tm α)[a↑length Δ + 1 # 0 //length Δ]↓ 1 #length Δ + 1) = (#(↑i-1)) := by
      simp only [Subst, hi.ne.symm, ↓reduceIte, drop_var_not_lt (not_lt_of_le <| Nat.succ_le_of_lt hi)]
    have aux₂ : List.get Γ' i = List.get (Δ ++ Γ) ⟨↑i-1, aux₀⟩ := by
      rw [get_of_eq hΘ.symm, get_append_right', get_append_right']
      apply congrArg
      apply Fin.ext
      simp only [length_append, length_singleton, Nat.add_comm (length Δ), Nat.sub_sub]
      exact Nat.le_sub_one_of_lt hi
      simp only [length_append, length_singleton, Nat.succ_le_of_lt]
      simp only [Nat.succ_le_of_lt hi]
    have aux₃ : (#(↑i-1) : Tm α) = (#↑(⟨(↑i-1), aux₀⟩ : Fin (length (Δ ++ Γ))) : Tm α) := by apply congrFun rfl
    rw [aux₁, aux₂, aux₃]
    apply Under.var

  | abs Γ' C s D _ ih =>
      rw [abs_subst_aux]
      exact Under.abs _ _ _ _ (ih (Cons Δ C) (by simp [hΘ]))
  | app Γ' t C D s _ _ ih₁ ih₂ =>
      exact Under.app _ _ _ _ _ (ih₁ Δ hΘ) (ih₂ Δ hΘ)
