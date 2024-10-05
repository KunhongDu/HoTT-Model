import Mathlib.Data.Fin.Basic

universe u

-- let me do dependent types & Id-types first
-- 1. Ty and Tm are mutually inductively defined
-- 2. Ctx is a list
-- 3. Context morphisms are defined within a type theory


mutual
inductive Ty
| Pi : Ty → Ty → Ty
| Id : Ty → Tm → Tm → Ty
| Uni : Ty
| El : Tm → Ty

inductive Tm
| var : ℕ → Tm
| abs : Ty → Tm → Tm
| app : Tm → Tm → Tm
| ref : Ty → Tm → Tm
| uniPi : Tm → Tm → Tm
| uniId : Tm → Tm → Tm → Tm

end

open Ty Tm List

abbrev Ctx := List Ty

notation "#"n => Tm.var n
prefix:max "λ." => Tm.abs
notation f"["a"]" => Tm.app f a

notation "Π" a "," b => Ty.Pi a b

notation:max Γ"⬝"A => List.cons A Γ

mutual

def TyLift (i c: ℕ) : Ty → Ty
| Pi A B => Pi (TyLift i c A) (TyLift i (c+1) B)
| Ty.Id A a b => Id (TyLift i c A) (TmLift i c a) (TmLift i c b)
| Uni => Uni
| El a => El (TmLift i c a)

def TmLift (i c: ℕ) : Tm → Tm
| #n => if n < c then #n else #(n + i)
| abs A b => λ. (TyLift i c A) (TmLift i (c+1) b)
| app f a => app (TmLift i c f) (TmLift i c a)
| ref A a => ref (TyLift i c A) (TmLift i c a)
| uniPi a b => uniPi (TmLift i c a) (TmLift i (c+1) b)
| uniId a b b' => uniId (TmLift i c a) (TmLift i c b) (TmLift i c b')

end

notation t"↑"i"#"c => TmLift i c t
notation t"↑"i"#"c => TyLift i c t

lemma lift_var {n i c} : ((#n)↑i#c : Tm) = if n < c then #n else #(n + i) := by simp [TmLift]

lemma lift_var_lt {n i c} (h : n < c) : ((#n)↑i#c : Tm) = #n := by rw [lift_var]; simp only [h, ↓reduceIte]

lemma lift_var_not_lt {n i c} (h : ¬ n < c) : ((#n)↑i#c : Tm) = #(n + i) := by rw [lift_var]; simp only [h, ↓reduceIte]

mutual

def TyDrop (i c: ℕ) : Ty → Ty
| Pi A B => Pi (TyDrop i c A) (TyDrop i (c+1) B)
| Ty.Id A a b => Id (TyDrop i c A) (TmDrop i c a) (TmDrop i c b)
| Uni => Uni
| El a => El (TmDrop i c a)

def TmDrop (i c: ℕ) : Tm → Tm
| #n => if n < c then #n else #(n - i)
| abs A b => λ. (TyDrop i c A) (TmDrop i (c+1) b)
| app f a => app (TmDrop i c f) (TmDrop i c a)
| ref A a => ref (TyDrop i c A) (TmDrop i c a)
| uniPi a b => uniPi (TmDrop i c a) (TmDrop i (c+1) b)
| uniId a b b' => uniId (TmDrop i c a) (TmDrop i c b) (TmDrop i c b')


end

notation t"↓"i"#"c => TmDrop i c t
notation t"↓"i"#"c => TyDrop i c t


mutual

def TySubst (e : Tm) (m : ℕ) : Ty → Ty
| Pi A B => Pi (TySubst e m A) (TySubst e m B)
| Ty.Id A a b => Id (TySubst e m A) (TmSubst e m a) (TmSubst e m b)
| Uni => Uni
| El a => El (TmSubst e m a)

def TmSubst (e : Tm) (m : ℕ) : Tm → Tm
| #n => if n = m then e else #n
| abs A b => λ. (TySubst e m A) (TmSubst (e ↑ 1 # 0) (m + 1) b)
| app f a => app (TmSubst e m f) (TmSubst e m a)
| ref A a => ref (TySubst e m A) (TmSubst e m a)
| uniPi a b => uniPi (TmSubst e m a) (TmSubst (e ↑ 1 # 0) (m + 1) b)
| uniId a b b' => uniId (TmSubst e m a) (TmSubst e m b) (TmSubst e m b')

end

notation t"["e"//"m"]" => TmSubst e m t
notation t"["e"//"m"]" => TySubst e m t

mutual
inductive isCtx : Ctx → Prop
| empty : isCtx []
| ext : isType Γ A → isCtx Γ⬝A

inductive isType : Ctx → Ty → Prop
| prod : isType (Γ⬝A) B → isType Γ (ΠA,B)
| id : isTerm Γ a A → isTerm Γ b A → isType Γ (Id A a b)
| uni : isType Γ Uni
| el : isTerm Γ a Uni → isType Γ (El a)

inductive isTerm : Ctx → Tm → Ty → Prop
| abs : isTerm (Γ⬝A) b B → isTerm Γ (λ. A b) (ΠA,B)
| app : isTerm Γ f (Pi A B) → isTerm Γ a A → isTerm Γ (f[a]) (B[a//0])
| ref : isTerm Γ a A → isTerm Γ (ref A a) (Id A a a)
| uniAbs : isTerm Γ a A → isTerm (Γ⬝(El a)) b Uni → isTerm Γ (uniPi a (λ. (El a) b)) Uni
| uniId : isTerm Γ a A → isTerm Γ b (El a) → isTerm Γ c (El a) → isTerm Γ (uniId a b c) Uni

end
