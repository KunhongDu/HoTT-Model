import Mathlib.AlgebraicTopology.Quasicategory
import HoTTModel.Lemmas.Limits

section
open CategoryTheory Opposite

universe u v w
variable {C : Type u} [Category.{v, u} C] {F : Cᵒᵖ ⥤ Type (max v w)}

def uliftWhiskering.{w₁, w₂} : (C ⥤ Type w₁) ⥤ (C ⥤ Type (max w₁ w₂)) :=
  (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{w₂, w₁}

lemma CategoryTheory.yonedaCompUliftFunctorEquiv_naturality {X Y: C}
  (f : yoneda.obj X ⋙ uliftFunctor.{w, v} ⟶ F) (g : Y ⟶ X) :
    F.map g.op (yonedaCompUliftFunctorEquiv _ _ f) =
      yonedaCompUliftFunctorEquiv _ _ ((yoneda ⋙ uliftWhiskering).map g ≫ f) := by
  change (f.app (op X) ≫ F.map g.op) (ULift.up (𝟙 X)) = f.app (op Y) (ULift.up (𝟙 Y ≫ g))
  -- why this kind of display
  /-
    (f.app { unop := X } ≫ F.map g.op) { down := 𝟙 X } = f.app { unop := Y } { down := 𝟙 Y ≫ g }
  -/
  rw [← f.naturality]
  dsimp
  simp only [Category.comp_id, Category.id_comp]

end

namespace SSet
open CategoryTheory Simplicial Limits SimplexCategory Function Opposite Classical
open standardSimplex SimplicialObject Fin

section Yoneda

lemma yonedaEquiv_naturality (X : SSet) (x : Δ[n] ⟶ X)
  (f : ([m] : SimplexCategory) ⟶ [n]):
    X.map f.op (X.yonedaEquiv _ x) = (X.yonedaEquiv _) (standardSimplex.map f ≫ x) :=
  yonedaCompUliftFunctorEquiv_naturality _ _

lemma yonedaEquiv_symm_naturality (X : SSet) (x : X _[n])
  (f : ([m] : SimplexCategory) ⟶ [n]):
    X.map f.op x = (X.yonedaEquiv _) (standardSimplex.map f ≫ (X.yonedaEquiv _).symm x) := by
  convert X.yonedaEquiv_naturality ((X.yonedaEquiv _).symm x) f
  simp only [Equiv.apply_symm_apply]

lemma yonedaEquiv_symm_naturality₂ (X : SSet) (x : X _[n])
  (f : ([m] : SimplexCategory) ⟶ [n]):
    (X.yonedaEquiv _).symm (X.map f.op x) = standardSimplex.map f ≫ (X.yonedaEquiv _).symm x := by
  apply (X.yonedaEquiv _).injective
  simp only [Equiv.apply_symm_apply]
  apply yonedaEquiv_symm_naturality

lemma yonedaEquiv_naturality' {X Y: SSet} (f : X ⟶ Y) (x : Δ[n] ⟶ X) :
    f.app _ (X.yonedaEquiv _ x) = Y.yonedaEquiv _ (x ≫ f) :=
  rfl

lemma yonedaEquiv_symm_naturality' {X Y: SSet} (f : X ⟶ Y) (x : X _[n]) :
    f.app _ x = Y.yonedaEquiv _ ((X.yonedaEquiv _).symm x ≫ f) := by
  convert X.yonedaEquiv_naturality' _ _
  simp only [Equiv.apply_symm_apply]

lemma yonedaEquiv_symm_naturality'₂ {X Y: SSet} (f : X ⟶ Y) (x : X _[n]) :
    (Y.yonedaEquiv _).symm (f.app _ x) = (X.yonedaEquiv _).symm x ≫ f := by
  apply (Y.yonedaEquiv _).injective
  simp only [Equiv.apply_symm_apply]
  apply yonedaEquiv_symm_naturality'

end Yoneda

section Miscancellous

@[ext]
lemma standardSimplex.ext (x y : Δ[m].obj n) (h : asOrderHom x = asOrderHom y) : x = y := by
  apply (objEquiv _ _).injective
  dsimp [objEquiv, Equiv.ulift]
  ext a
  dsimp [asOrderHom] at h
  rw [h]

def recop {F : SimplexCategoryᵒᵖ → Sort*} (h : ∀ n : ℕ, F (op [n])) : ∀ X, F X := fun n =>
  h n.unop.len

lemma exists_eq_standardSimplex_map (f : Δ[m] ⟶ Δ[n]) :
    ∃ l : SimplexCategory.mk m ⟶ [n], f = standardSimplex.map l := by
  use objEquiv _ _ (yonedaEquiv _ _ f)
  exact ((yonedaEquiv _ _).left_inv _).symm

end Miscancellous

noncomputable section
instance unique_Δ0 : Unique (Δ[0].obj m) where
  default := const 0 0 m
  uniq := by intro a; ext; simp

def toΔ0 (X : SSet) : X ⟶ Δ[0] where
  app n := fun _ ↦ const 0 0 n
  naturality n m f := by ext; simp;

lemma unique_toΔ0 {X : SSet} (f g : X ⟶ Δ[0]) : f = g := by ext; simp

instance instUnique_toΔ0 {X : SSet} : Unique (X ⟶ Δ[0]) where
  default := X.toΔ0
  uniq _ := unique_toΔ0 _ _

def Δ0_is_terminal : IsTerminal Δ[0] := by
  apply IsTerminal.ofUniqueHom (fun X ↦ toΔ0 X)
  intros; apply unique_toΔ0

namespace Prod

def IsoProdΔ0 : X ≅ X ⨯ Δ[0] := IsoProdTerminal Δ0_is_terminal

def left : X ⟶ X ⨯ Δ[1] :=
  IsoProdΔ0.hom ≫ (prod.lift prod.fst <| prod.snd ≫ standardSimplex.map (δ 1))

lemma left_comp_prod_fst :
    Prod.left (X := X) ≫ prod.fst = 𝟙 _ := by
  simp [Prod.left, IsoProdΔ0, IsoProdTerminal]

def right : X ⟶ X ⨯ Δ[1] :=
  IsoProdΔ0.hom ≫ (prod.lift prod.fst <| prod.snd ≫ standardSimplex.map (δ 0))

lemma right_comp_prod_fst :
    Prod.right (X := X) ≫ prod.fst = 𝟙 _ := by
  simp [Prod.right, IsoProdΔ0, IsoProdTerminal]

def IsoΔ0Prod : X ≅ Δ[0] ⨯ X := IsoTerminalProd Δ0_is_terminal

end Prod
end

noncomputable section
variable {X Y Z X' Y': SSet}

def prod.mapping (f : X ⨯ Y ⟶ Z) (x : X.obj n) (y : Y.obj n) :
    Z.obj n :=
  Z.yonedaEquiv _ (prod.lift ((yonedaEquiv _ _).symm x) ((yonedaEquiv _ _).symm y) ≫ f)

lemma prod.mapping.functoriality (f : X' ⨯ Y' ⟶ Z) (g : X ⟶ X') (h : Y ⟶ Y')
  (x : X.obj n) (y : Y.obj n):
    mapping (prod.map g h ≫ f) x y = mapping f (g.app _ x) (h.app _ y) := by
  simp [mapping]
  congr
  <;> apply (yonedaEquiv_symm_naturality'₂ (n := n.unop.len) _ _).symm

lemma prod.mapping.functoriality' (f : X ⨯ Y ⟶ Z) (g : Z ⟶ Z') (x : X.obj n) (y : Y.obj n) :
    mapping (f ≫ g) x y = g.app _ (mapping f x y) := by
  cases n using recop
  simp only [mapping, Z.yonedaEquiv_naturality', Category.assoc]

lemma prod.mapping.naturality (f : X ⨯ Y ⟶ Z) (x : X.obj n) (y : Y.obj n) (φ : n ⟶ m):
    mapping f (X.map φ x) (Y.map φ y) = Z.map φ (mapping f x y) := by
  cases n using recop
  cases m using recop
  simp [mapping]
  erw [yonedaEquiv_symm_naturality₂, yonedaEquiv_symm_naturality₂,
       yonedaEquiv_naturality, ← Category.assoc]
  congr
  apply prod.hom_ext
  <;> simp

lemma hom_naturality_apply {n m : SimplexCategoryᵒᵖ} (f : X ⟶ Y) (x : X.obj n) (φ : n ⟶ m) :
    f.app _ (X.map φ x) = Y.map φ (f.app _ x) :=
  congrFun (f.naturality φ) x

end

section

lemma asOrderHom_objMk (x : Fin (n + 1) →o Fin (m + 1)) : asOrderHom (objMk x) = x := rfl

end

noncomputable section evalution
universe u v w
-- for the sake of simplcity, Assume `J : Type 0`... Can't figure out the universe contraints
variable {J : Type 0} [Category.{v} J] (F : J ⥤ SSet.{u})

abbrev ev' (k : SimplexCategoryᵒᵖ) : SSet.{u} ⥤ Type u :=
  (evaluation SimplexCategoryᵒᵖ (Type u)).obj k

abbrev ev (k : ℕ) : SSet.{u} ⥤ Type u :=
  ev' (op [k])

instance instPreservesLimitsOfShapeEv' : PreservesLimitsOfShape J (ev'.{u} k) := by
  dsimp [ev']
  apply evaluationPreservesLimitsOfShape
  -- infer instance fails???

instance instPreservesLimitsOfShapeEv : PreservesLimitsOfShape J (ev.{u} k) := by
  dsimp [ev]
  infer_instance

end evalution
end SSet
