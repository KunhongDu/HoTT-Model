import HoTTModel.Contextual
import HoTTModel.Lemmas.HEq

open CategoryTheory CategoryTheory.Limits ContextualCategory PreContextualCategory

universe u
/-
section

structure PreContextualFunctor (α : Type u₁) [PreContextualCategory.{u₁, v₁} α]
    (β : Type u₂) [PreContextualCategory.{u₂, v₂} β] extends α ⥤ β where
  gr_obj {x : α} : gr (obj x) = gr x
  obj_one : obj (one : α) = one
  ft_obj {x : α} : ft (obj x) = obj (ft x)
  proj_map {x : α} : HEq (proj (obj x)) (map (proj x))

attribute [simp] PreContextualFunctor.gr_obj
  PreContextualFunctor.obj_one PreContextualFunctor.ft_obj

namespace PreContextualFunctor

variable {α : Type u₁} [PreContextualCategory.{u₁, v₁} α] {β : Type u₂}
  [PreContextualCategory.{u₂, v₂} β] (F : PreContextualFunctor α β)

instance (x : α) [NR x] :
    NR (F.obj x) where
  nr := by simpa [F.gr_obj] using NR.nr

def map' {x y : α} (f : y ⟶ ft x) :
    F.obj y ⟶ ft (F.obj x) :=
  F.map f ≫ eqToHom F.ft_obj.symm

end PreContextualFunctor

end

section

structure ContextualFunctor (α : Type u₁) [ContextualCategory.{u₁, v₁} α]
    (β : Type u₂) [ContextualCategory.{u₂, v₂} β] extends PreContextualFunctor α β where
  pb_map {x y : α} [NR x] (f : y ⟶ ft x) :
    pb (toPreContextualFunctor.map' f) = obj (pb f)
  pb_fst_map {x y : α} [NR x] (f : y ⟶ ft x) :
    HEq (pb_fst (toPreContextualFunctor.map' f)) (map (pb_fst f))

attribute [simp] ContextualFunctor.pb_map

namespace ContextualFunctor

variable {α : Type u₁} [ContextualCategory.{u₁, v₁} α] {β : Type u₂}
  [ContextualCategory.{u₂, v₂} β] (F : ContextualFunctor α β)

def _root_.ContextualCategory.Ext.map {x : α} (A : Ext x) :
    Ext (F.obj x) where
  obj := F.obj A.obj
  ft' := by simp [A.ft']
  gr' := by simp [A.gr']

end ContextualFunctor


end
-/

section

class PreContextual {α : Type u₁} [PreContextualCategory.{u₁, v₁} α]
    {β : Type u₂} [PreContextualCategory.{u₂, v₂} β] (F : α ⥤ β) : Prop where
  gr_obj {x : α} : gr (F.obj x) = gr x
  obj_one : F.obj (one : α) = one
  ft_obj {x : α} : ft (F.obj x) = F.obj (ft x)
  proj_map {x : α} : HEq (proj (F.obj x)) (F.map (proj x))

attribute [simp] PreContextual.gr_obj
  PreContextual.obj_one PreContextual.ft_obj

namespace PreContextual

variable {α : Type u₁} [PreContextualCategory.{u₁, v₁} α] {β : Type u₂}
  [PreContextualCategory.{u₂, v₂} β] (F : α ⥤ β) [PreContextual F]

@[simp, reassoc]
lemma proj_map_comp_eqToHom {x : α} {y : β} (eq : ft (F.obj x) = y) :
    proj (F.obj x) ≫ eqToHom eq = F.map (proj x) ≫ eqToHom (ft_obj.symm.trans eq) := by
  simpa [comp_eqToHom_iff_heq] using proj_map

instance (x : α) [NR x] :
    NR (F.obj x) where
  nr := by simpa [gr_obj] using NR.nr

--- emm??
def _root_.CategoryTheory.Functor.map' {x y : α} (f : y ⟶ ft x) :
    F.obj y ⟶ ft (F.obj x) :=
  F.map f ≫ eqToHom ft_obj.symm

end PreContextual

end

section

class Contextual {α : Type u₁} [ContextualCategory.{u₁, v₁} α]
    {β : Type u₂} [ContextualCategory.{u₂, v₂} β] (F : α ⥤ β)
      extends PreContextual F where
  pb_map {x y : α} [NR x] (f : y ⟶ ft x) :
    pb (F.map' f) = F.obj (pb f)
  pb_fst_map {x y : α} [NR x] (f : y ⟶ ft x) :
    HEq (pb_fst (F.map' f)) (F.map (pb_fst f))

attribute [simp] Contextual.pb_map

namespace ContextualFunctor

open PreContextual

variable {α : Type u₁} [ContextualCategory.{u₁, v₁} α] {β : Type u₂}
  [ContextualCategory.{u₂, v₂} β] (F : α ⥤ β) [Contextual F]

def _root_.ContextualCategory.Ext.map {x : α} (A : Ext x) :
    Ext (F.obj x) where
  obj := F.obj A.obj
  ft' := by simp [A.ft']
  gr' := by simp [A.gr']

def _root_.ContextualCategory.Section.map {x : α} {A : Ext x} (s : Section A) :
    Section (A.map F) := by
  apply Over.homMk (F.map s.left) _
  simp [Ext.map, Ext.hom]
  rw [← eqToHom_map _ A.ft', ← F.map_comp, ← F.map_comp]
  erw [Over.w s]; simp

end ContextualFunctor


end
