import Mathlib.Data.Fin.Basic

/-
universe u

inductive Ty (α : Type u)
| base : α → Ty α
| map : Ty α → Ty α → Ty α

variable (α : Type u)

inductive Tm (α : Type u)
| var : ℕ → Tm α
| abs : ℕ → Tm α → Tm α --- abstraction
| app : Tm α → Tm α → Tm α --- application

-- define Ctx as partial functions
def Ctx := ℕ →. Ty α
-- finiteness???

def EmptyCtx : Ctx α := fun _ ↦ {
  Dom := False
  get := False.rec
}

def Extend {α} (Γ : Ctx α) (n : ℕ) (A : Ty α) : Ctx α
| m => if n = m then ⟨True, fun _ ↦ A⟩ else Γ m

def NewVar {α} (Γ : Ctx α) (n : ℕ) : Prop := n ∉ Γ.Dom

-- define `Typing under Ctxs`
open Tm Ty in
inductive HasTypeUnder {α} : Ctx α → Tm α → Ty α → Prop
| var Γ n A : (d: (Γ n).Dom) → (Γ n).get d = A → HasTypeUnder Γ (var n) A
| abs Γ n A t B : NewVar Γ n → HasTypeUnder (Extend Γ n A) t B → HasTypeUnder Γ (abs n t) (map A B)
| app Γ t A B s : HasTypeUnder Γ t (map A B) → HasTypeUnder Γ s A → HasTypeUnder Γ (app t s) B

section test_var
variable (A: Ty α)
def f {α} (A: Ty α) : Ctx α:= fun n ↦
  match n with
  | 0 => ⟨True, fun _ ↦ A⟩
  | _ + 1 =>  ⟨False, False.rec⟩

def feq {α} {A: Ty α} : Part.get (f A 0) True.intro = A := by simp [f]

example : HasTypeUnder (f A) (Tm.var 0) A := HasTypeUnder.var (f A) 0 A True.intro feq

end test_var

section weakening

def WeakerThan {α} (Δ Γ : Ctx α) : Prop := ∀ n, ¬ (Δ n).Dom ∨ Δ n = Γ n

infix:50 " < " =>  WeakerThan

example {Δ Γ : Ctx α} (wt : Δ < Γ) {t : Tm α} {A : Ty α} (p : HasTypeUnder Δ t A) : HasTypeUnder Γ t A := by sorry

end weakening

section substitution

def Subst {α} (Γ Δ : Ctx α) := (n : ℕ) → (p : (Γ n).Dom) → (t : Tm α) → HasTypeUnder Δ t <| (Γ n).get p

variable (Γ Δ : Ctx α) (σ : Subst Δ Γ)

-- example : Subst (EmptyCtx α) Δ := fun _ ↦ False.rec

-- A Ctx made of one Single type
def SCtx {α} (A: Ty α) : Ctx α:= Extend (EmptyCtx α) 0 A

lemma TmSubst₀_lm (A: Ty α) (s : Tm α) (B : Ty α) (p : HasTypeUnder (SCtx A) s B) : HasTypeUnder (EmptyCtx α) (Tm.abs 0 s) (Ty.map A B) := by
  apply HasTypeUnder.abs
  simp [NewVar, EmptyCtx]
  exact p

abbrev TmSubst₀ {α} (t: Tm α) (s: Tm α) : Tm α := Tm.app (Tm.abs 0 s) t

def TmSubstHasTypeUnder₀ {Δ} (σ : Subst Δ Γ) (t: Tm α) (A: Ty α) (s: Tm α) (B : Ty α) (p : HasTypeUnder (SCtx A) s B) : HasTypeUnder Δ (TmSubst₀ t s) B := by
  sorry -- apply HasTypeUnder.app


end substitution
-/

universe u

inductive Ty (α : Type u)
| base : α → Ty α
| map : Ty α → Ty α → Ty α

notation a"->"b => Ty.map a b

variable (α : Type u)

inductive Tm (α : Type u)
| var : ℕ → Tm α
| abs : Tm α → Tm α --- abstraction
| app : Tm α → Tm α → Tm α --- application

notation "#"n => Tm.var n
notation "λ."t => Tm.abs t
notation t"["s"]" => Tm.app t s

-- define Ctx as lists (in reverse direction)
abbrev Ctx := List (Ty α)

def EmptyCtx : Ctx α := []

abbrev Cons {α} (Γ : Ctx α) (A : Ty α) := List.cons A Γ

abbrev Extend {α} (Γ Δ : Ctx α) := Δ ++ Γ

def Lift {α} (i c: ℕ) : Tm α → Tm α
| #n => if n < c then #n else #(n + i)
| λ.t => λ.(Lift i (c+1) t)
| Tm.app t s => (Lift i c t)[Lift i c s]

notation t"↑"i"#"c => Lift i c t

def Subst {α} (e : Tm α) (m : ℕ) : Tm α → Tm α
| #n => if n = m then e else #n
| λ.t => λ.(Subst (e ↑ 1 # 0) (m + 1) t)
| Tm.app t s => (Subst e m t)[Subst e m s]

notation t"["e"//"m"]" => Subst e m t

open Tm Ty List

inductive Judgement (α)
| typing : Tm α → Ty α → Judgement α
| eq : Tm α → Tm α → Ty α → Judgement α

-- Notation precedence??
notation t":"T => Judgement.typing t T
notation t"≡"s":"T => Judgement.eq t s T


/-
-- make it into a judgement so that `=` can be defined
inductive HasTypeUnder {α} : Ctx α → Tm α → Ty α → Prop
| var Γ (i : Fin (length Γ)) : HasTypeUnder Γ (#↑i) (get Γ i)
| wkg Γ Δ t A : HasTypeUnder Γ t A → HasTypeUnder (Extend Γ Δ) (t ↑ length Δ # 0) A
| subst Γ a A b B : HasTypeUnder Γ a A → HasTypeUnder (Cons Γ A) b B → HasTypeUnder Γ (b[a//0]) B
| abs Γ A t B : HasTypeUnder (Cons Γ A) t B → HasTypeUnder Γ (λ. t) (map A B)
| app Γ t A B s : HasTypeUnder Γ t (map A B) → HasTypeUnder Γ s A → HasTypeUnder Γ (app t s) B

notation Γ " ⊢ " t " : " A  => HasTypeUnder Γ t A
-/

inductive Under {α} : Ctx α → Judgement α → Prop
| var Γ (i : Fin (length Γ)) : Under Γ ((#↑i) : get Γ i)
-- | wkg Γ Δ t A : Under Γ (t : A) → Under (Extend Γ Δ) ((t ↑ length Δ # 0) : A)
-- | subst Γ a A b B : Under Γ (a : A) → Under (Cons Γ A) (b : B) → Under Γ ((b[a//0]) : B)
| abs Γ A t B : Under (Cons Γ A) (t : B) → Under Γ ((λ. t) : (map A B))
| app Γ t A B s : Under Γ (t : (map A B)) → Under Γ (s : A) → Under Γ (t[s] : B)
-- | eq_refl Γ t A : Under Γ (t : A) → Under Γ (t ≡ t :' A)
-- | eq_symm Γ t s A : Under Γ (t ≡ s :' A) → Under Γ (s ≡ t :' A)
-- | eq_trans Γ t s r A : Under Γ (t ≡ s :' A) → Under Γ (s ≡ r :' A) → Under Γ (t ≡ r :' A)

notation Γ " ⊢ " J  => Under Γ J

-- predeceny of `#`???
-- variable (A : Ty α)
example (A : Ty α) : [A] ⊢ (#0) : A := Under.var [A] ⟨0, by simp⟩
example (A : Ty α) : [] ⊢ (λ. #0) : (map A A) :=
  Under.abs [] A (#0) A <| Under.var [A] ⟨0, by simp⟩

example (A B C: Ty α) (f a: Tm α) (h1 : [C] ⊢ f : map A B) (h2 : [C] ⊢ a : A) : [C] ⊢ f[a] : B := Under.app [C] f A B a h1 h2

example (A B C: Ty α) (f a: Tm α) (h1 : [C] ⊢ f : map A B) (h2 : [C] ⊢ a : A) : [] ⊢ (λ. f[a]) : map C B :=
  Under.abs [] C (f[a]) B <| Under.app [C] f A B a h1 h2

example (A B C : Ty α) (f c : Tm α) (h1 : [A, A -> B] ⊢ f : C -> B) (h2 : [A, A -> B] ⊢ c : C) : [A, A -> B] ⊢ f[c] : B := Under.app _ f C B c h1 h2

example (A B C : Ty α) (f c : Tm α) (h1 : [A, A -> B] ⊢ f : C -> B) (h2 : [A, A -> B] ⊢ c : C) : [A -> B] ⊢ (λ. f[c]) : A -> B := by
  apply Under.abs
  apply Under.app _ f C B c h1 h2

example (A B C : Ty α) (f c : Tm α) (h1 : [A, A -> B] ⊢ f : C -> B) (h2 : [A, A -> B] ⊢ c : C) : [] ⊢ (λ. λ. f[c]) : (A -> B) -> A -> B := by
  apply Under.abs
  apply Under.abs
  apply Under.app _ f C B c h1 h2

-- free variables??

/-
inductive test : ℕ → Type
| fst : test 0
| snd : ℕ → test 1

#check test.rec
#check Empty.rec

example (a : Empty) : True := Empty.rec a

example (a : test 1) : True := test.rec True.intro (fun _ ↦ True.intro) a
-/

/-
inductive test (p : Prop) : ℕ → Type
| fst : test p 0
| snd : (h : p) → test p 1

#check test.rec
#check Empty.rec

example (a : Empty) : True := Empty.rec a

variable (p : Prop) (a : test p 1)

#check @test.rec p (fun a : ℕ ↦ fun _ : test p a ↦ if a = 1 then p else True) True.intro id 1 a

example (p : Prop) (a : test p 1) : p := @test.rec p (fun a : ℕ ↦ fun _ : test p a ↦ if a = 1 then p else True) True.intro id 1 a
-/
-- prove weakening

/-
example (Γ Δ : Ctx α) t A (h : Γ ⊢ (t : A)) : (Extend Γ Δ) ⊢ ((t ↑ length Δ # 0) : A) :=
  match h with
  | Under.var Γ i => by
      set l1 : Tm α := ((#↑i)↑length Δ#0)
      -- have this : (((Tm.var ↑i)↑length Δ#0) : Tm α) = (((#↑i)↑length Δ#0) : Tm α) := by sorry
      have : l1 = #(↑i +length Δ) := sorry
      rw [this]
      have : 0 < length Γ := Fin.size_pos i
      have l : Fin (length (Extend Γ Δ)) := ⟨length Δ, by simp [Nat.lt_add_right_iff_pos, this]⟩
      have l' : Fin (length (Extend Γ Δ)) := ⟨↑i , by simp; sorry⟩
      have : List.get Γ i = List.get (Extend Γ Δ) (l' + l) := sorry
      rw [this]
      have : ↑i + length Δ = ↑(l' + l) := sorry
      rw [this]
      apply Under.var (Extend Γ Δ) (l' + l)
  | Under.abs Γ A t B h₁ => by
      have h₂ := Under.abs Γ A t B h₁
      induction t with
      | var a => sorry
      | abs t h =>
          have : ((λ.λ.t)↑length Δ#0) = λ.((λ.t)↑length Δ#0) := sorry
          rw [this]
          apply Under.abs
          sorry
      | app t s ht hs => sorry
  | Under.app _ _ _ _ _ _ _ => sorry
-/


-- weird induction hypothesis (SOLVED!!! DO NOT SPECIFY THE NAME)

example (Γ : Ctx α) t B (h : Γ ⊢ (t : B)) :∀ A, (Cons Γ A) ⊢ ((t ↑ 1 # 0) : B) := by
  generalize hJ : (t :B) = J at *
  induction h generalizing t B with
  | var Γ i => sorry
  | abs Γ C s D h ih =>
      intro A
      have := Under.abs _ _ _ _ h
      cases hJ


  | app _ _ _ _ _ _ _ => sorry


/-
  cases h with
  | var Γ i => sorry
  | abs Γ C t D h =>
      have h₁ := Under.abs Γ C t D h
      have : ((λ.t)↑1#0) = λ.t↑1#1 := rfl
      rw [this]
      apply Under.abs
      generalize hΓ : Cons Γ C = Γ' at *
      generalize hJ : (t:D) = J at *
      induction h with
      | var Γ' i => sorry
      | abs Γ' A' t' B' h₀ ih =>
        apply ih
        rw [hΓ]



      | app _ _ _ _ _ _ _ => sorry

#exit
lemma WeakeningStrengthened (E F G: Ctx α) e T ( h :(E ++ G) ⊢ (e : T)) : (E ++ F ++ G) ⊢ ((e ↑ length F # length G) : B) := by
  generalize h₁ : E ++ G = E' at *
  generalize h₂ : (e : T) = J at *
  induction h with
  | var _ _ => sorry

-/
inductive HasTypeUnder {α} : Ctx α → Tm α → Ty α → Prop
| var Γ (i : Fin (length Γ)) : HasTypeUnder Γ (#↑i) (get Γ i)
| abs Γ A t B : HasTypeUnder (Cons Γ A) t B → HasTypeUnder Γ (λ. t) (map A B)

lemma unique_typing (Γ : Ctx α) t A B (h : HasTypeUnder Γ t A) (h' : HasTypeUnder Γ t B) : A = B := by
  induction h with
  | var Γ' i =>
      generalize hi : (#↑i) = t at h'
      cases h' with
      | var Γ j =>
          have : i = j := Fin.val_injective <| Tm.var.inj hi
          rw [this]
      | abs Γ A t B _ =>
          exfalso
          have : (#↑i) ≠ λ.t := fun h => Tm.noConfusion h
          apply this hi
  | abs Γ' C s D h ih =>
      generalize hi : (λ.s) = t at h'
      cases h' with
      | var Γ j =>
        exfalso
        have : (λ.s) ≠ (#↑j) := fun h => Tm.noConfusion h
        apply this hi
      | abs Γ A t B hyp =>
          have : s = t := Tm.abs.inj hi
          -- hyp is useless
          sorry

example (Γ : Ctx α) t A (h : HasTypeUnder Γ t A) : (B : Ty α) → HasTypeUnder Γ t B → A = B := by
  induction h with
  | var Γ' i =>
      intro B h'
      generalize hi : (#↑i) = t at h'
      cases h' with
      | var Γ j =>
          have : i = j := Fin.val_injective <| Tm.var.inj hi
          rw [this]
      | abs Γ A t B _ =>
          exfalso
          have : (#↑i) ≠ λ.t := fun h => Tm.noConfusion h
          apply this hi
  | abs Γ' C s D h ih =>
      intro B h'
      generalize hi : (λ.s) = t at h'
      cases h' with
      | var Γ j =>
        exfalso
        have : (λ.s) ≠ (#↑j) := fun h => Tm.noConfusion h
        apply this hi
      | abs Γ A t B hyp =>
          have : s = t := Tm.abs.inj hi
          rw [this] at h ih
          -- here is the problem, maybe we need to specify abs?


/-
example (Γ : Ctx α) t A B (h : HasTypeUnder Γ t B) : HasTypeUnder (Cons Γ A)  (t ↑ 1 # 0) B := by
  induction h with
  | abs Γ C s D h ih =>
      have : ((λ.s)↑1#0) = λ.s↑1#1 := rfl
      rw [this]
      apply HasTypeUnder.abs
      -- need stronger hypothesis

example (E: Ctx α) e T  (h : HasTypeUnder E e T): HasTypeUnder [] e T := by
  induction h with
  | abs _ _ _ _ _ _ => sorry

example (E F G: Ctx α) e T (h : HasTypeUnder E e T) : (HasTypeUnder (E ++ F ++ G) (e ↑ length F # length G)  B) := by
  set E' := E ++ G
  generalize hc : h = h'
  induction h' with
  | abs _ _ _ _ _ _ => sorry
-/

#exit
def JLift {α} (J : Judgement α) (i c: ℕ) : Judgement α := by
  cases J with
  | typing a T => exact ((a ↑ i # c) : T)
  | eq a b T => exact ((a ↑ i # c) ≡ (b ↑ i # c) :' T)

notation J"↑↑"i"#"c => JLift J i c
/-
lemma Weakening' (Γ : Ctx α) A J (h : Γ ⊢ J) : (Cons Γ A) ⊢ (J ↑↑ i # c) := by
  induction h with
  | var Γ i => sorry
  | abs Γ C s D h ih =>
      have h₁ := Under.abs Γ C s D h



  | app _ _ _ _ _ _ _ => sorry
-/

example (Γ Δ : Ctx α) J (h : Γ ⊢ J) : (Extend Γ Δ) ⊢ (J ↑↑ length Δ # 0) := by
  induction h with
  | var Γ' i => sorry
  | abs Γ' C s D h ih =>
      sorry
  | app _ _ _ _ _ _ _ => sorry

lemma unique_typing (Γ : Ctx α) t A B (h : Γ ⊢ t : A) (h' : Γ ⊢ t : B) : A = B := by
  generalize (t : A) = J at *
  induction h with
  | var Γ' i => sorry
  | abs Γ' C s D h ih =>
      apply ih

  | app _ _ _ _ _ _ _ => sorry
