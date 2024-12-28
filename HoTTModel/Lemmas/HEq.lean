import Mathlib.CategoryTheory.EqToHom

namespace CategoryTheory

variable {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C]

lemma heq_of_eqToHom_comp_eqToHom_eq  {X X' Y Y' : C}
  {f : X ⟶ Y} {g : X' ⟶ Y'} (hX : X' = X) (hY : Y = Y')
  (h : eqToHom hX ≫ f ≫ eqToHom hY = g) :
    HEq f g := by
  cases hX; cases hY
  simpa using h

lemma heq_of_eq_eqToHom_comp_eqToHom  {X X' Y Y' : C}
  {f : X ⟶ Y} {g : X' ⟶ Y'} (hX : X = X') (hY : Y' = Y)
  (h : f = eqToHom hX ≫ g ≫ eqToHom hY) :
    HEq f g := by
  cases hX; cases hY
  simpa using h

lemma heq_of_eqToHom_comp_eq  {X X' Y : C}
  {f : X ⟶ Y} {g : X' ⟶ Y} (hX : X' = X)
  (h : eqToHom hX ≫ f = g) :
    HEq f g := by
  cases hX
  simpa using h

lemma heq_of_eq_eqToHom_comp  {X X' Y : C}
  {f : X ⟶ Y} {g : X' ⟶ Y} (hX : X = X')
  (h : f = eqToHom hX ≫ g) :
    HEq f g := by
  cases hX
  simpa using h

lemma heq_of_eq_comp_eqToHom  {X Y Y' : C}
  {f : X ⟶ Y} {g : X ⟶ Y'} (hY : Y' = Y)
  (h : f = g ≫ eqToHom hY) :
    HEq f g := by
  cases hY
  simpa using h

lemma heq_of_comp_eqToHom_eq  {X Y Y' : C}
  {f : X ⟶ Y} {g : X ⟶ Y'} (hY : Y = Y')
  (h : f ≫ eqToHom hY = g) :
    HEq f g := by
  cases hY
  simpa using h

lemma eqToHom_comp_iff_heq {X X' Y : C} {f : X ⟶ Y} {g : X' ⟶ Y} (hX : X' = X) :
    eqToHom hX ≫ f = g ↔ HEq f g := by
  cases hX; simp

lemma comp_eqToHom_iff_heq {X Y Y' : C} {f : X ⟶ Y} {g : X ⟶ Y'} (hY : Y = Y') :
    f ≫ eqToHom hY = g ↔ HEq f g := by
  cases hY; simp
