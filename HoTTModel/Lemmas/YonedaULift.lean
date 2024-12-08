import Mathlib.CategoryTheory.Elements

namespace CategoryTheory
open Opposite

universe u v w
variable {C : Type u} [Category.{v, u} C]

section

def uliftWhiskering.{w₁, w₂} : (C ⥤ Type w₁) ⥤ (C ⥤ Type (max w₁ w₂)) :=
  (whiskeringRight _ _ _).obj uliftFunctor.{w₂, w₁}

def yonedaULift : C ⥤ Cᵒᵖ ⥤ Type max v w := yoneda ⋙ uliftWhiskering

variable {F : Cᵒᵖ ⥤ Type (max v w)} {X Y : C}

def yonedaULiftEquiv :
    (yonedaULift.obj X ⟶ F) ≃ F.obj (op X) :=
  yonedaCompUliftFunctorEquiv _ _

lemma yonedaULiftEquiv_apply (f : yonedaULift.obj X ⟶ F):
    yonedaULiftEquiv f = f.app (op X) (ULift.up (𝟙 _)) := rfl

lemma yonedaULiftEquiv_yonedaULift_apply (f : X ⟶ Y) :
    yonedaULiftEquiv (yonedaULift.map f) = ULift.up f := by
  rw [yonedaULiftEquiv_apply]
  simp [yonedaULift, uliftWhiskering]

lemma yonedaCompUliftFunctorEquiv_naturality (f : yoneda.obj X ⋙ uliftFunctor.{w, v} ⟶ F)
  (g : Y ⟶ X) :
    F.map g.op (yonedaCompUliftFunctorEquiv _ _ f) =
      yonedaCompUliftFunctorEquiv _ _ ((yoneda ⋙ uliftWhiskering).map g ≫ f) := by
  change (f.app (op X) ≫ F.map g.op) (ULift.up (𝟙 X)) = f.app (op Y) (ULift.up (𝟙 Y ≫ g))
  -- why this kind of display
  /-
    (f.app { unop := X } ≫ F.map g.op) { down := 𝟙 X } = f.app { unop := Y } { down := 𝟙 Y ≫ g }
  -/
  rw [← f.naturality]; simp

lemma yonedaULiftEquiv_naturality (f : yonedaULift.obj X ⟶ F) (g : Y ⟶ X) :
    F.map g.op (yonedaULiftEquiv f) =
      yonedaULiftEquiv (yonedaULift.map g ≫ f) :=
  yonedaCompUliftFunctorEquiv_naturality _ _

lemma yonedaULiftEquiv_symm_naturality (x : F.obj (op X)) (g : Y ⟶ X):
    yonedaULiftEquiv.symm (F.map g.op x) =
      yonedaULift.map g ≫ yonedaULiftEquiv.symm x := by
  apply yonedaULiftEquiv.injective
  simp [← yonedaULiftEquiv_naturality]

lemma yonedaULiftEquiv_comp {F G : Cᵒᵖ ⥤ Type max w v} {X : C}
  (α : yonedaULift.obj X ⟶ F) (β : F ⟶ G) :
    yonedaULiftEquiv (α ≫ β) = β.app _ (yonedaULiftEquiv α) :=
  rfl

lemma yonedaULiftEquiv_symm_comp {F G : Cᵒᵖ ⥤ Type max w v} {X : C} (x : F.obj (op X)) (β : F ⟶ G) :
    yonedaULiftEquiv.symm x ≫ β = yonedaULiftEquiv.symm (β.app _ x) := by
  apply yonedaULiftEquiv.injective
  simp [yonedaULiftEquiv_comp]

end

section

variable (F : Cᵒᵖ ⥤ Type (max v w))

namespace CategoryOfElements

#check toCostructuredArrow
@[simps]
def toCostructuredArrowULift (F : Cᵒᵖ ⥤ Type max v w) :
    F.Elementsᵒᵖ ⥤ CostructuredArrow yonedaULift F where
  obj X := CostructuredArrow.mk (yonedaULiftEquiv.symm (unop X).2)
  map {X Y} f := by
    apply CostructuredArrow.homMk (f.unop.val.unop) _
    ext Z y
    dsimp only [CostructuredArrow.mk_right, Functor.const_obj_obj,
      CostructuredArrow.mk_left, CostructuredArrow.mk_hom_eq_self]
    rw [← yonedaULiftEquiv_symm_naturality]
    simp [f.unop.2]

#check fromCostructuredArrow
@[simps]
def fromCostructuredArrowULift :
    (CostructuredArrow yonedaULift F)ᵒᵖ ⥤ F.Elements where
  obj X := ⟨op (unop X).1, yonedaULiftEquiv (unop X).3⟩
  map {X Y} f :=
    ⟨f.unop.1.op, by dsimp; rw [yonedaULiftEquiv_naturality, f.unop.3]; rfl⟩

@[simp]
theorem fromCostructuredArrowULift_obj_mk {X : C} (f : yonedaULift.obj X ⟶ F) :
    (fromCostructuredArrowULift F).obj (op (CostructuredArrow.mk f)) = ⟨op X, yonedaULiftEquiv f⟩ :=
  rfl

#check costructuredArrowYonedaEquivalence
def costructuredArrowYonedaEquivalenceULift :
    F.Elementsᵒᵖ ≌ CostructuredArrow yonedaULift F where
  functor := toCostructuredArrowULift F
  inverse := (fromCostructuredArrowULift F).rightOp
  unitIso := by
    apply NatIso.ofComponents _ _
    . exact fun X ↦ Iso.op (CategoryOfElements.isoMk _ _ (Iso.refl _) (by simp))
    . intro X Y f; apply Quiver.Hom.unop_inj (by ext; simp)
  counitIso := NatIso.ofComponents (fun X ↦ CostructuredArrow.isoMk (Iso.refl _))

end CategoryOfElements
