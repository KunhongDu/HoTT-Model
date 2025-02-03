import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

noncomputable section

open CategoryTheory CategoryTheory.Limits Fin List

universe u v
structure Universe (C : Type u) [CategoryTheory.Category.{v, u} C] where
  up : C
  down : C
  hom : up ⟶ down
  pt {X} (f : X ⟶ down) : C
  fst {X} (f : X ⟶ down) : pt f ⟶ up
  snd {X} (f : X ⟶ down) : pt f ⟶ X
  isPullback (f : X ⟶ down) : IsPullback (fst f) (snd f) hom f
namespace Universe

variable {C : Type u} [CategoryTheory.Category.{v, u} C] [HasBinaryProducts C]
  {t : C} (ht : IsTerminal t) (U : Universe C)

abbrev proj₁ : U.down ⨯ U.up ⟶ U.down := prod.fst

abbrev proj₂ : U.down ⨯ U.up ⟶ U.up := prod.snd

abbrev proj₁' : Over U.down := Over.mk U.proj₁

abbrev proj₂' : Over U.up := Over.mk U.proj₂

abbrev toTerminal : U.down ⟶ t := IsTerminal.from ht _

abbrev over : Over U.down := Over.mk U.hom

abbrev fst' (f : X ⟶ U.down) : Over U.up := Over.mk (U.fst f)

abbrev snd' (f : X ⟶ U.down) : Over X := Over.mk (U.snd f)

def comm (f : X ⟶ U.down):= (U.isPullback f).w

end Universe
