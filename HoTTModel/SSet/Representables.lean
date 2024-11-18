import Mathlib.CategoryTheory.Limits.Presheaf
import HoTTModel.SSet.Lemmas

/-
namespace CategoryTheory

open CategoryTheory Limits Opposite

noncomputable section

namespace Presheaf
open Limits Opposite
universe u v
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (G : (Cᵒᵖ ⥤ Type v₁)ᵒᵖ ⥤ D) (Y Z : Cᵒᵖ ⥤ Type v₁) (f : Z ⟶ Y)
  [HasLimit ((functorToRepresentables Y).op ⋙ G)]
  [PreservesLimit (functorToRepresentables Y).op G]
  [HasLimit ((functorToRepresentables Z).op ⋙ G)]
  [PreservesLimit (functorToRepresentables Z).op G]
  [HasLimit ((CategoryOfElements.map f).op.op ⋙ (functorToRepresentables Y).op ⋙ G)]

def IsoOfPreservesLimit : G.obj (op Y) ≅ limit ((functorToRepresentables Y).op ⋙ G) :=
  -- change (G.mapCone (coconeOfRepresentable Y).op).pt ≅ (limit.cone _).pt
  IsLimit.conePointUniqueUpToIso
    (PreservesLimit.preserves (colimitOfRepresentable _).op) (limit.isLimit (_ ⋙ G))

example : (CategoryOfElements.map f).op.op ⋙ (functorToRepresentables Y).op ⋙ G =
  (functorToRepresentables Z).op ⋙ G := rfl

example : (CategoryOfElements.map f).op ⋙ (functorToRepresentables Y) =
  (functorToRepresentables Z) := rfl
  -- all due to this... ha???

example (F G H : C ⥤ C) : F ⋙ G ⋙ H = (F ⋙ G) ⋙ H := rfl

variable {Y Z}
lemma IsoOfPreservesLimit_comp_hom :
    G.map (op f) ≫ (IsoOfPreservesLimit G Z).hom =
      (IsoOfPreservesLimit G Y).hom ≫ limit.pre _ (CategoryOfElements.map f).op.op := by
  dsimp [IsoOfPreservesLimit, IsLimit.conePointUniqueUpToIso]
  ext j; simp
  erw [limit.lift_π]; simp
  erw [← G.map_comp, ← op_comp]
  congr; ext c a; simp
  erw [yonedaEquiv_symm_app_apply, yonedaEquiv_symm_app_apply]
  change (Z.map (op a) ≫ f.app c) _ = (f.app _ ≫ Y.map (op a)) _
  rw [f.naturality]

lemma IsoOfPreservesLimit_comp_inv :
    (IsoOfPreservesLimit G Y).inv ≫ G.map (op f) =
      limit.pre _ (CategoryOfElements.map f).op.op ≫ (IsoOfPreservesLimit G Z).inv:= by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact IsoOfPreservesLimit_comp_hom _ _

end Presheaf

end
end CategoryTheory-/

noncomputable section Representables

namespace SSet
open CategoryTheory Limits Opposite
universe u

variable (X : SSet.{u})

@[reducible]
def functorToRepresentables : X.Elementsᵒᵖ ⥤ SSet.{u} :=
  (CategoryOfElements.π X).leftOp ⋙ standardSimplex

@[simps]
def coconeOfRepresentable :
    Cocone (functorToRepresentables X) where
  pt := X
  ι :=
    { app := fun x ↦ (yonedaEquiv _ _).symm x.unop.2
      naturality := fun {x₁ x₂} f => by
        simp; rw [← yonedaEquiv_symm_naturality_left']
        simp only [op_unop, CategoryOfElements.map_snd]
        }

open standardSimplex in
def colimitOfRepresentable :
    IsColimit (coconeOfRepresentable X) where
  desc s :=
    { app := fun n x => by
        apply (s.ι.app (op (Functor.elementsMk X n x))).app n (yonedaEquiv _ _ (𝟙 _))
      naturality := fun n Y f => by
        ext x
        have eq₁ := congr_fun (congr_app (s.w (CategoryOfElements.homMk (X.elementsMk n x)
          (X.elementsMk Y (X.map f x)) f rfl).op) Y) (yonedaEquiv _ _ (𝟙 _))
        dsimp at eq₁ ⊢
        erw [← eq₁]
        exact congr_fun ((s.ι.app (Opposite.op (X.elementsMk n x))).naturality f)
            (yonedaEquiv _ _ (𝟙 _))}
  fac s j := by
    ext n x
    let φ : j.unop ⟶ Functor.elementsMk X n (((yonedaEquiv _ _).symm j.unop.2).app n x)
      := ⟨(objEquiv _ _ x).op, rfl⟩
    simp
    convert (congr_fun (congr_app (s.ι.naturality φ.op).symm _) (yonedaEquiv _ _ (𝟙 _))) using 1
    erw [yonedaEquiv_naturality_right]; simp
    erw [← yonedaEquiv_naturality_right]; congr!
    exact ((yonedaEquiv _ _).right_inv _).symm
  uniq s m hm := by
    ext n x
    dsimp
    rw [← hm]
    apply congr_arg
    change x = X.map (𝟙 _) x
    rw [X.map_id, types_id_apply]

variable {D : Type u₂} [Category.{v₂} D]
  (G : (SSet.{u})ᵒᵖ ⥤ D) (X Y : SSet.{u}) (f : Y ⟶ X)
  [HasLimit (X.functorToRepresentables.op ⋙ G)]
  [PreservesLimit X.functorToRepresentables.op G]
  [HasLimit (Y.functorToRepresentables.op ⋙ G)]
  [PreservesLimit Y.functorToRepresentables.op G]
  [HasLimit ((CategoryOfElements.map f).op.op ⋙ X.functorToRepresentables.op ⋙ G)]

def IsoOfPreservesLimit : G.obj (op Y) ≅ limit (Y.functorToRepresentables.op ⋙ G) :=
  -- change (G.mapCone (coconeOfRepresentable Y).op).pt ≅ (limit.cone _).pt
  IsLimit.conePointUniqueUpToIso
    (PreservesLimit.preserves (colimitOfRepresentable _).op) (limit.isLimit (_ ⋙ G))

variable {X Y}
lemma IsoOfPreservesLimit_comp_hom :
    G.map (op f) ≫ (IsoOfPreservesLimit G Y).hom =
      (IsoOfPreservesLimit G X).hom ≫ limit.pre _ (CategoryOfElements.map f).op.op := by
  dsimp [IsoOfPreservesLimit, IsLimit.conePointUniqueUpToIso]
  ext j; simp
  erw [limit.lift_π]; simp
  erw [← G.map_comp, ← op_comp]
  congr
  exact (yonedaEquiv_symm_naturality_right' _ _).symm

lemma IsoOfPreservesLimit_comp_inv :
    (IsoOfPreservesLimit G X).inv ≫ G.map (op f) =
      limit.pre _ (CategoryOfElements.map f).op.op ≫ (IsoOfPreservesLimit G Y).inv:= by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact IsoOfPreservesLimit_comp_hom _ _

open Simplicial
variable (n : ℕ) [HasLimit (Δ[n].functorToRepresentables.op ⋙ G)]
  [PreservesLimit Δ[n].functorToRepresentables.op G]

def standardSimplex.IsoOfPreservesLimitInv :
    limit (Δ[n].functorToRepresentables.op ⋙ G) ⟶ G.obj (op (Δ[n])) :=
  limit.π _ (op (op (Functor.elementsMk _ _ (yonedaEquiv _ _ (𝟙 Δ[n])))))

lemma standardSimplex.IsoOfPreservesLimitInv_eq :
    IsoOfPreservesLimitInv G n = (IsoOfPreservesLimit G Δ[n]).inv := by
  rw [← Iso.hom_comp_eq_id]
  simp [IsoOfPreservesLimitInv, IsoOfPreservesLimit,
         IsLimit.conePointUniqueUpToIso]

section

variable {n} (G : (SSet.{u})ᵒᵖ ⥤ Type u)
  [HasLimit (Δ[n].functorToRepresentables.op ⋙ G)]
  [PreservesLimit Δ[n].functorToRepresentables.op G]

def standardSimplex.IsoOfPreservesLimitToPi
  (x : G.obj (op Δ[n])) (j : Δ[n].Elementsᵒᵖᵒᵖ) :
    (Δ[n].functorToRepresentables.op ⋙ G).obj j :=
  G.map ((yonedaEquiv _ _).symm j.unop.unop.2).op x

def standardSimplex.IsoOfPreservesLimitOfPi
  (f : (j : Δ[n].Elementsᵒᵖᵒᵖ) → (Δ[n].functorToRepresentables.op ⋙ G).obj j) :
    G.obj (op Δ[n]) :=
  f (op (op (Functor.elementsMk _ _ (yonedaEquiv _ _ (𝟙 Δ[n])))))

def standardSimplex.limitToPi (f : limit (Δ[n].functorToRepresentables.op ⋙ G))
  (j : Δ[n].Elementsᵒᵖᵒᵖ) :
    (Δ[n].functorToRepresentables.op ⋙ G).obj j :=
  limit.π (Δ[n].functorToRepresentables.op ⋙ G) j f

lemma standardSimplex.IsoOfPreservesLimitToPi_fac_apply (x : G.obj (op Δ[n])) :
    IsoOfPreservesLimitToPi G x =
      limitToPi G ((IsoOfPreservesLimit G Δ[n]).hom x) := by
  ext j
  simp [limitToPi, IsoOfPreservesLimitToPi, IsoOfPreservesLimit,
        IsLimit.conePointUniqueUpToIso]

def standardSimplex.limitToPi_fac_apply
  (f : limit (Δ[n].functorToRepresentables.op ⋙ G)):
    IsoOfPreservesLimitOfPi G (limitToPi G f) = (IsoOfPreservesLimit G Δ[n]).inv f := by
  rw [← IsoOfPreservesLimitInv_eq]
  simp [IsoOfPreservesLimitOfPi, limitToPi, IsoOfPreservesLimit,
        IsLimit.conePointUniqueUpToIso, IsoOfPreservesLimitInv]

variable (G H : (SSet.{u})ᵒᵖ ⥤ Type u)
  (g : (Δ[n].functorToRepresentables.op ⋙ G) ⟶ (Δ[n].functorToRepresentables.op ⋙ H))

lemma standardSimplex.PiWhiskerRight_naturality_apply
  (f : limit (Δ[n].functorToRepresentables.op ⋙ G)) (j : (Functor.Elements Δ[n])ᵒᵖᵒᵖ) :
    limitToPi H (limMap g f) j = g.app _ (limitToPi G f j) := by
  simp [limitToPi]

end
end SSet
end Representables
