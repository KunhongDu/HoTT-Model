import HoTTModel.LocallyCartesianClosed.Basic
import HoTTModel.Lemmas.CommaPresheaf
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.AlgebraicTopology.SimplicialSet.Quasicategory
import Mathlib.CategoryTheory.Closed.FunctorCategory.Complete

/-
The proof strategy is inspired by `https://github.com/sinhp/Poly/blob/master/Poly/LCCC/Presheaf.lean`
-/

noncomputable section

namespace CategoryTheory
open Limits Functor Adjunction Over Opposite Equivalence Presheaf MonoidalCategory

universe u v w w'
variable {C : Type 0} [Category.{v} C]

instance PresheafCategoryCartesianClosed : CartesianClosed (Cᵒᵖ ⥤ Type max v w) :=
    functorCategoryMonoidalClosed _ _

namespace CategoryOfElements

def overPshIsPshElementsOp' {P : Cᵒᵖ ⥤ Type max v w} :
    Over P ≌ (Elements P)ᵒᵖᵒᵖ ⥤ Type max v w :=
  (YonedaULift.overEquivPresheafCostructuredArrow P).trans
    (congrLeft (costructuredArrowYonedaEquivalenceULift P).op).symm

end CategoryOfElements

open CategoryOfElements

instance : OverCartesianClosed (Cᵒᵖ ⥤ Type max v w) where
  over _ := cartesianClosedOfEquiv overPshIsPshElementsOp'.symm

instance instLocallyCartesianClosedPresheaves :
  LocallyCartesianClosed (Cᵒᵖ ⥤ Type max v w) := inferInstance

instance : LocallyCartesianClosed SSet.{u} := by
  dsimp [SSet, SimplicialObject]
  infer_instance
  -- note that `SimplexCategory` has `Category.{0,0}`
  -- and `Type max 0 u = Type u` definitionally


end CategoryTheory
