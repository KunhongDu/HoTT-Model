import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.Tactic.ApplyFun

namespace CategoryTheory

open Limits Over

universe v u

class LocallyCartesianClosed (C : Type u) [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasPullbacks C] where
  DProd {X Y : C} (f : X ⟶ Y) : Over X ⥤ Over Y
  adj {X Y : C} (f : X ⟶ Y) : baseChange f ⊣ DProd f

namespace LocallyCartesianClosed

notation f"*" => baseChange f
notation "Π"f => DProd f
notation "Σ"f => Over.map f

variable {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasPullbacks C] [LocallyCartesianClosed C]


noncomputable section

-- follow the notions in Mathlib.CategoryTheory.Limits.Shapes.CommSq
-- ` P X `
-- ` Y Z `

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
(h : IsPullback fst snd f g)

def IsPullback.Iso_of_pullback : pullback f g ≅ P := CategoryTheory.Functor.mapIso (Cones.forget (cospan f g)) (CategoryTheory.Limits.IsLimit.uniqueUpToIso (limit.isLimit (cospan f g)) h.isLimit)

lemma IsPullback.Iso_of_pullback_hom_fst : (IsPullback.Iso_of_pullback h).hom ≫ fst = pullback.fst := IsLimit.fac (self := h.isLimit) (limit.cone (cospan f g)) WalkingCospan.left

lemma IsPullback.Iso_of_pullback_inv_fst : (IsPullback.Iso_of_pullback h).inv ≫ pullback.fst = fst := IsLimit.fac (self := limit.isLimit (cospan f g)) h.cone WalkingCospan.left

lemma IsPullback.Iso_of_pullback_hom_snd : (IsPullback.Iso_of_pullback h).hom ≫ snd = pullback.snd := IsLimit.fac (self := h.isLimit) (limit.cone (cospan f g)) WalkingCospan.right

lemma IsPullback.Iso_of_pullback_inv_snd : (IsPullback.Iso_of_pullback h).inv ≫ pullback.snd = snd := IsLimit.fac (self := limit.isLimit (cospan f g)) h.cone WalkingCospan.right

section
-- follows the notion of
#check baseChange

-- `W Z`
-- `X Y`

variable {W Z X Y : C} {f : X ⟶ Y} {g : Z ⟶ Y} {u : W ⟶ Z} {v : W ⟶ X} (h : IsPullback u v g f) (V : Over X)

def isLimit_equiv : (Over.mk v ⟶ V) ≃ (Over.mk g ⟶ (Πf).obj V) where
  toFun φ := ((adj f).homEquiv _ _).toFun <| Over.homMk (U := (f*).obj (Over.mk g)) (V := V) ((IsPullback.Iso_of_pullback h).hom ≫ φ.left) (by simp [IsPullback.Iso_of_pullback_hom_snd])
  invFun ψ := Over.homMk (U := Over.mk v) (V := (f*).obj (Over.mk g)) (IsPullback.Iso_of_pullback h).inv (by simp [IsPullback.Iso_of_pullback_inv_snd]) ≫ ((adj f).homEquiv _ _).invFun ψ
  left_inv := by intro; ext; simp
  right_inv := by
    intro
    apply_fun ((adj f).homEquiv (Over.mk g) V).invFun
    ext
    simp
    apply Equiv.injective ((adj f).homEquiv _ _).symm

end
end

end LocallyCartesianClosed

end CategoryTheory
