import Mathlib.AlgebraicTopology.SimplicialSet.Quasicategory
import HoTTModel.Lemmas.Limits
import HoTTModel.Lemmas.YonedaULift

namespace SSet
open CategoryTheory Simplicial Limits SimplexCategory Function Opposite Classical
open standardSimplex SimplicialObject Fin

universe u

abbrev hom_apply {X : SSet.{u}} {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : X.obj n) :
    X.obj m := X.map f x

scoped[SSet] infix:100 " ~ " => hom_apply

lemma hom_naturality_apply {X Y : SSet.{u}} {n m : SimplexCategoryᵒᵖ}
  (f : X ⟶ Y) (φ : n ⟶ m)  (x : X.obj n) :
    f.app _ (X.map φ x) = Y.map φ (f.app _ x) :=
  congrFun (f.naturality φ) x

/--
  `hom_naturality_apply` but written using `~`
-/
lemma hom_naturality_apply' {X Y : SSet.{u}} {n m : SimplexCategoryᵒᵖ}
  (f : X ⟶ Y) (φ : n ⟶ m)  (x : X.obj n) :
    f.app _ (φ ~ x) = φ ~ (f.app _ x) :=
  congrFun (f.naturality φ) x

section Yoneda

section left
variable (X : SSet) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)

/--
  The naturality of `yonedaEquiv` wrt to `[m] → [n]`.
-/
lemma yonedaEquiv_naturality_left (x : standardSimplex.obj n.unop ⟶ X):
    X.map f (X.yonedaEquiv _ x) = (X.yonedaEquiv _) (standardSimplex.map f.unop ≫ x) :=
  yonedaCompUliftFunctorEquiv_naturality _ _

/--
  The naturality of `yonedaEquiv.symm` wrt to `[m] → [n]`.
-/
lemma yonedaEquiv_symm_naturality_left (x : X.obj n) :
    X.map f x = (X.yonedaEquiv _) (standardSimplex.map f.unop ≫ (X.yonedaEquiv _).symm x) := by
  convert X.yonedaEquiv_naturality_left f ((X.yonedaEquiv _).symm x)
  simp only [Equiv.apply_symm_apply]

/--
  Variant of `yonedaEquiv_symm_naturality_left`.
-/
lemma yonedaEquiv_symm_naturality_left' (x : X.obj n) :
    (X.yonedaEquiv _).symm (X.map f x) = standardSimplex.map f.unop ≫ (X.yonedaEquiv _).symm x := by
  apply (X.yonedaEquiv _).injective
  simp only [Equiv.apply_symm_apply]
  apply yonedaEquiv_symm_naturality_left

end left

section right
variable {X Y: SSet} (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ}
/--
  The naturality of `yonedaEquiv` wrt to `X ⟶ Y`.
-/
lemma yonedaEquiv_naturality_right (x : standardSimplex.obj n.unop ⟶ X) :
    f.app _ (X.yonedaEquiv _ x) = Y.yonedaEquiv _ (x ≫ f) :=
  rfl

/--
  The naturality of `yonedaEquiv.symm` wrt to `X ⟶ Y`.
-/
lemma yonedaEquiv_symm_naturality_right (x : X.obj n) :
    f.app _ x = Y.yonedaEquiv _ ((X.yonedaEquiv _).symm x ≫ f) := by
  convert X.yonedaEquiv_naturality_right _ _
  simp only [Equiv.apply_symm_apply]

/--
  Variant of `yonedaEquiv_symm_naturality_right`.
-/
lemma yonedaEquiv_symm_naturality_right' (x : X.obj n) :
    (Y.yonedaEquiv _).symm (f.app _ x) = (X.yonedaEquiv _).symm x ≫ f := by
  apply (Y.yonedaEquiv _).injective
  simp only [Equiv.apply_symm_apply]
  apply yonedaEquiv_symm_naturality_right

end right
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

@[simp]
def IsoProdΔ0 : X ≅ X ⨯ Δ[0] := IsoProdTerminal Δ0_is_terminal

def left : X ⟶ X ⨯ Δ[1] :=
  IsoProdΔ0.hom ≫ (prod.lift prod.fst <| prod.snd ≫ standardSimplex.map (δ 1))

lemma left_comp_prod_fst :
    left (X := X) ≫ prod.fst = 𝟙 _ := by
  simp [Prod.left, IsoProdΔ0, IsoProdTerminal]

def right : X ⟶ X ⨯ Δ[1] :=
  IsoProdΔ0.hom ≫ (prod.lift prod.fst <| prod.snd ≫ standardSimplex.map (δ 0))

lemma right_comp_prod_fst :
    right (X := X) ≫ prod.fst = 𝟙 _ := by
  simp [Prod.right, IsoProdΔ0, IsoProdTerminal]

lemma left_comp_prod_map {f : X ⟶ Y} :
    left ≫ prod.map f (𝟙 _) = f ≫ left := by
  apply Limits.prod.hom_ext
  . simp [left]
  . simp [left]; rw [← Category.assoc]; congr

lemma right_comp_prod_map {f : X ⟶ Y} :
    right ≫ prod.map f (𝟙 _) = f ≫ right := by
  apply Limits.prod.hom_ext
  . simp [right]
  . simp [right]; rw [← Category.assoc]; congr

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
  <;> apply (yonedaEquiv_symm_naturality_right' _ _).symm

lemma prod.mapping.functoriality' (f : X ⨯ Y ⟶ Z) (g : Z ⟶ Z') (x : X.obj n) (y : Y.obj n) :
    mapping (f ≫ g) x y = g.app _ (mapping f x y) := by
  cases n using recop
  simp only [mapping, Z.yonedaEquiv_naturality_right, Category.assoc]

lemma prod.mapping.naturality (f : X ⨯ Y ⟶ Z) (x : X.obj n) (y : Y.obj n) (φ : n ⟶ m):
    mapping f (X.map φ x) (Y.map φ y) = Z.map φ (mapping f x y) := by
  simp [mapping]
  erw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left,
       yonedaEquiv_naturality_left, ← Category.assoc]
  congr
  apply Limits.prod.hom_ext
  <;> simp

end

section

lemma asOrderHom_objMk (x : Fin (n + 1) →o Fin (m + 1)) : asOrderHom (objMk x) = x := rfl

end

noncomputable section evalution
universe v w
-- for the sake of simplcity, Assume `J : Type 0`... Can't figure out the universe contraints
variable [UnivLE.{v, u}] {J : Type v} [Category.{w} J] (F : J ⥤ SSet.{u})

abbrev ev (k : SimplexCategoryᵒᵖ) : SSet.{u} ⥤ Type u :=
  (evaluation SimplexCategoryᵒᵖ (Type u)).obj k

abbrev ev' (k : ℕ) : SSet.{u} ⥤ Type u :=
  ev (op [k])

instance instPreservesLimitsOfShapeEv : PreservesLimitsOfShape J (ev.{u} k) := by
  dsimp [ev]
  apply evaluationPreservesLimitsOfShape
  -- infer instance fails???

instance instPreservesColimitsOfShapeEv : PreservesColimitsOfShape J (ev.{u} k) := by
  dsimp [ev]
  apply evaluationPreservesColimitsOfShape

instance instPreservesLimitsOfShapeEv' : PreservesLimitsOfShape J (ev'.{u} k) := by
  dsimp [ev']
  infer_instance

end evalution
end SSet

namespace CategoryTheory
section LimitPreNatural
open Limits

variable {J : Type u₁} [Category.{v₁, u₁} J] {K : Type u₂}
  [Category.{v₂, u₂} K] {C : Type u} [Category.{v, u} C]
  {F F' : J ⥤ C} [HasLimit F] [HasLimit F']
  {E : K ⥤ J} [HasLimit (E ⋙ F)] [HasLimit (E ⋙ F')]
  (f : F ⟶ F')

lemma Limits.limit.pre_naturality:
    limit.pre F E ≫ limMap (whiskerLeft E f) = limMap f ≫ (limit.pre F' E) := by
  ext j; simp

lemma Limits.limit.pre_naturality' (g : E ⋙ F ⟶ E ⋙ F') (h : g = whiskerLeft E f) :
    limit.pre F E ≫ limMap g = limMap f ≫ (limit.pre F' E) := by
  rw [h, limit.pre_naturality]

end LimitPreNatural
end CategoryTheory
