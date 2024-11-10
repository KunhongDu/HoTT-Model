import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Limits.HasLimits

namespace CategoryTheory
open Limits MorphismProperty

universe u v
variable {C : Type u} [Category.{v,u} C]

section

variable {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)

infix:50 " □ " => HasLiftingProperty

structure RetractStruct where
  ul : X ⟶ A
  ur : A ⟶ X
  ll : Y ⟶ B
  lr : B ⟶ Y
  sql : CommSq ul g f ll
  sqr : CommSq ur f g lr
  compu : ul ≫ ur = 𝟙 _
  compl : ll ≫ lr = 𝟙 _

variable (l : MorphismProperty C)

def ClosedUnderRetract : Prop :=
    ∀ {A B X Y : C} {f : A ⟶ B} {g : X ⟶ Y}, l f → RetractStruct f g → l g

end

variable (l r : MorphismProperty C)

def ForkLeft : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y), l f ↔ (∀ {X' Y' : C} (g : X' ⟶ Y'), r g → f □ g)

infix:50 " ⋔ₗ " => ForkLeft

def ForkRight : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y), l f ↔ (∀ {X' Y' : C} (g : X' ⟶ Y'), r g → g □ f)

infix:50 " ⋔ᵣ " => ForkRight

structure OrthogonalSys : Prop where
  leftLift_right_of_left {X Y : C} (f : X ⟶ Y) :
    l f → (∀ {X' Y' : C} (g : X' ⟶ Y'), r g → f □ g)
  left_retract : ClosedUnderRetract l
  right_retract : ClosedUnderRetract r

lemma OrthogonalSys.rightLift_left_of_right (S : OrthogonalSys l r) :
    ∀ {X Y : C} (f : X ⟶ Y), r f → (∀ {X' Y' : C} (g : X' ⟶ Y'), l g → g □ f) := by
  intro _ _ _ h _ _ _ h'
  exact S.leftLift_right_of_left _ h' _ h

structure FunctorialWeakFactorSys extends FunctorialFactorizationData l r, OrthogonalSys l r

abbrev FunctorialWeakFactorSys.left (S : FunctorialWeakFactorSys l r) (f : Arrow C) := S.i.app f

abbrev FunctorialWeakFactorSys.right (S : FunctorialWeakFactorSys l r) (f : Arrow C) := S.p.app f

variable {l r}

lemma FunctorialWeakFactorSys.left_fork_right (S : FunctorialWeakFactorSys l r) :
    l ⋔ₗ r := by
  intro X Y f
  constructor
  . apply S.leftLift_right_of_left
  . intro h
    have sq : CommSq (S.left f) f (S.right f) (𝟙 _) := {
      w := by simp
    }
    specialize h (S.right f) (S.hp f)
    have rec : RetractStruct (S.left f) f := {
      ul := 𝟙 _
      ur := 𝟙 _
      ll := sq.lift
      lr := S.right f
      sql := ⟨by simp [sq.fac_left]⟩
      sqr := ⟨by simp⟩
      compu := by simp
      compl := by simp [sq.fac_right]
    }
    apply S.left_retract (S.hi f) rec

lemma FunctorialWeakFactorSys.right_fork_left (S : FunctorialWeakFactorSys l r) :
    r ⋔ᵣ l := by
  intro X Y f
  constructor
  . apply S.rightLift_left_of_right
  . intro h
    have sq : CommSq (𝟙 _) (S.left f) f (S.right f) := {
      w := by simp
    }
    specialize h _ (S.hi f)
    have rec : RetractStruct (S.right f) f := {
      ul := S.left f
      ur := sq.lift
      ll := 𝟙 _
      lr := 𝟙 _
      sql := ⟨by simp⟩
      sqr := ⟨by simp [sq.fac_right]⟩
      compu := by simp [sq.fac_left]
      compl := by simp
    }
    apply S.right_retract (S.hp f) rec

lemma ForkLeft.left_retract (h : l ⋔ₗ r) :
    ∀ {A B X Y : C} {f : A ⟶ B} {g : X ⟶ Y}, l f → RetractStruct f g → l g := by
  intro A B X Y f g
  simp_rw [h f, h g]
  intro h rec X' Y' i h'
  constructor
  intro u v sq
  have sq' : CommSq (rec.ur ≫ u) f i (rec.lr ≫ v) := ⟨by
    rw [Category.assoc, sq.w, ← Category.assoc, rec.sqr.w, Category.assoc]⟩
  specialize h i h'
  exact ⟨⟨{
    l := rec.ll ≫ sq'.lift
    fac_left := by rw [← Category.assoc, ← rec.sql.w, Category.assoc, sq'.fac_left,
                       ← Category.assoc, rec.compu, Category.id_comp]
    fac_right := by rw [Category.assoc, sq'.fac_right, ← Category.assoc, rec.compl,
                        Category.id_comp]
  }⟩⟩

lemma ForkRight.right_retract (h : r ⋔ᵣ l) :
    ∀ {A B X Y : C} {f : A ⟶ B} {g : X ⟶ Y}, r f → RetractStruct f g → r g := by
  intro A B X Y f g
  simp_rw [h f, h g]
  intro h rec X' Y' i h'
  constructor
  intro u v sq
  have sq' : CommSq (u ≫ rec.ul) i f (v ≫ rec.ll) := ⟨by
    rw [Category.assoc, rec.sql.w, ← Category.assoc, sq.w, Category.assoc]⟩
  specialize h i h'
  exact ⟨⟨{
    l := sq'.lift ≫ rec.ur
    fac_left := by rw [← Category.assoc, sq'.fac_left,  Category.assoc, rec.compu,
                       Category.comp_id]
    fac_right := by rw [Category.assoc, rec.sqr.w, ← Category.assoc, sq'.fac_right,
                        Category.assoc, rec.compl, Category.comp_id]
  }⟩⟩

def FunctorialFactorizationData.toFunctorialWeakFactorSysOfFork (S : FunctorialFactorizationData l r)
  (h₁ : l ⋔ₗ r) (h₂ : r ⋔ᵣ l) :
    FunctorialWeakFactorSys l r where
  toFunctorialFactorizationData := S
  leftLift_right_of_left := by
    intro X Y f
    simp only [h₁ f, imp_self]
  left_retract := h₁.left_retract
  right_retract := h₂.right_retract

variable (C) in
class ModelStructure [HasLimits C] [HasColimits C] where
  fib : MorphismProperty C
  cofib : MorphismProperty C
  weakEquiv : MorphismProperty C
  fibWfs : FunctorialWeakFactorSys (cofib ⊓ weakEquiv) fib
  cofibWfs : FunctorialWeakFactorSys cofib (fib ⊓ weakEquiv)
  weakEquivTwoOutOfThree : HasTwoOutOfThreeProperty weakEquiv

attribute [instance] ModelStructure.weakEquivTwoOutOfThree

namespace ModelStructure

variable [HasLimits C] [HasColimits C] [ModelStructure C]

abbrev acyFib : MorphismProperty C := fib ⊓ weakEquiv

abbrev acyCofib : MorphismProperty C := cofib ⊓ weakEquiv

end ModelStructure

end CategoryTheory
