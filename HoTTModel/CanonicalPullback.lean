import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

-- An api for chosen pullbacks?????
namespace CategoryTheory
open Category

universe u v

variable (α : Type u) [Category.{v} α]
/-
def Homs := Σ X : α, Σ Y : α, X ⟶ Y

variable (f : Homs α)
def Homs.source : α := f.fst

def Homs.target : α := f.snd.fst

def Homs.hom : f.fst ⟶ f.snd.fst := f.snd.snd

variable {α} in
def Homs.mk {X Y : α} (f : X ⟶ Y) : Homs α := ⟨X, ⟨Y, f⟩⟩
-/

structure CanonicalPullback (S : Set α) where
  target : S → α
  hom (X : S) : X.val ⟶ target X
  pullback (X : S) {Y : α} (f : Y ⟶ target X) : α
  pullback_fst (X : S) {Y : α} (f : Y ⟶ target X) : pullback X f ⟶ X
  pullback_snd (X : S) {Y : α} (f : Y ⟶ target X) : pullback X f ⟶ Y
  isPullback (X : S) {Y : α} (f : Y ⟶ target X) :
    IsPullback (pullback_fst X f) (pullback_snd X f) (hom X) f

/- not needed
  pullback_in (X : S) {Y : α} (f : Y ⟶ target X) : pullback X f ∈ S
  pullback_snd_heq (X : S) {Y : α} (f : Y ⟶ target X) : HEq (pullback_snd X f) (hom ⟨_, pullback_in X f⟩)

--def CanonicalPullback.pullback_snd' (P : CanonicalPullback S) (p : S) {Y : α} (f : Y ⟶ p.val.target) : S :=
--  ⟨Homs.mk (P.pullback_snd p f), P.pullback_snd_in _ _⟩

structure FunctorialCanonicalPullback extends CanonicalPullback α S where
  id_pullback {X : S} : X = pullback p (𝟙 _)
  id_pullback_fst {X : S} : eqToHom id_pullback ≫ pullback_fst X (𝟙 _) = 𝟙 _
  comp_pullback {X : S} {Y Z : α} {f : Y ⟶ target X} {g : Z ⟶ Y} :
    pullback X (g ≫ f) = pullback () g
  comp_pullback_fst {p : S} {Y Z : α} (f : Y ⟶ p.val.target) (g : Z ⟶ Y) :
    pullback_fst p (g ≫ f) = eqToHom comp_pullback ≫ pullback_fst (toCanonicalPullback.pullback_snd' S p f) g ≫
      pullback_fst p f
-/
end CategoryTheory

/-
namespace ContextualCategory
variable (α : Type*) [ContextualCategory α]

def Pullbacks : CanonicalPullback α (PreContextualCategory.nr α) where
  target X := ft X.val
  hom X := proj X.val
  pullback _ _ f := pb f
  pullback_fst _ _ f := pb_fst f
  pullback_snd _ _ f := pb_snd f
  isPullback _ _ f := isPullback f

end ContextualCategory
-/
