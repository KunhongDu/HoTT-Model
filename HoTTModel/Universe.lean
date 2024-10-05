import HoTTModel.Contextual
import Mathlib.CategoryTheory.Limits.Shapes.CommSq

noncomputable section

/-
open CategoryTheory CategoryTheory.Limits Fin

universe u v
namespace ContextualCategory

structure Universe (α : Type u) [CategoryTheory.Category.{v, u} α] where
  obj : α
  obj' : α
  map : obj' ⟶ obj
  pb {X} (f : X ⟶ obj) : α
  pb_vmap {X} (f : X ⟶ obj) : pb f ⟶ X
  pb_hmap {X} (f : X ⟶ obj) : pb f ⟶ obj'
  comm {f : X ⟶ obj} : pb_vmap f ≫ f =  pb_hmap f ≫ map
  is_pullback {f : X ⟶ obj} : IsLimit <| PullbackCone.mk (pb_vmap f) (pb_hmap f) comm

variable {α : Type u} [CategoryTheory.Category.{v, u} α]


structure Chain (U : Universe α) (X : α) (n : ℕ) where
  obj (i : Fin (n + 1) ) : α
  map (i : Fin (n + 1) ) : obj i ⟶ U.obj
  coh₀ : X = obj 0
  coh (i : Fin n) : U.pb (map (castSucc i)) = obj (succ i)

abbrev Pb {α : Type u} [CategoryTheory.Category.{v, u} α] {U : Universe α} {X : α} {n : ℕ} (C : Chain U X n) : α :=

variable (U : Universe α) (t : α) (ht : IsTerminal t)

def PreChainCat := Σ n : ℕ, Chain U t n
/-
namespace PreChainCat
variable {U : Universe α} {t : α}

@[simp]
def Hom (x : PreChainCat U t) (y : PreChainCat U t) := (Pb x.snd) ⟶ (Pb y.snd)

@[simp]
def comp {x y z : PreChainCat U t} : (Pb x.snd ⟶ Pb y.snd) → (Pb y.snd ⟶ Pb z.snd) → (Pb x.snd ⟶ Pb z.snd) := @CategoryStruct.comp _ _ (Pb x.snd) (Pb y.snd) (Pb z.snd)

instance : Category (PreChainCat U t) where
  Hom := Hom
  id x := 𝟙 (Pb x.snd)
  comp := comp
  id_comp := by simp
  comp_id := by simp
  assoc := by simp

end PreChainCat
-/
inductive ChainCat (U : Universe α) (t : α)
  | of : PreChainCat U t → ChainCat U t
  | one : ChainCat U t

namespace ChainCat

variable {U : Universe α} {t : α}
@[simp]

def Hom : ChainCat U t → ChainCat U t → Type v
  | of x, of y => (Pb x.snd) ⟶ (Pb y.snd)
  | one, of y => t ⟶ (Pb y.snd)
  | one, one => t ⟶ t
  | of x, one => (Pb x.snd) ⟶ t

@[simp]
def id : ∀ X : ChainCat U t, Hom X X
  | of _ => 𝟙 _
  | one => 𝟙 t

@[simp]
def comp : ∀ {X Y Z : ChainCat U t}, Hom X Y → Hom Y Z → Hom X Z
  | of _X, of _Y, of _Z => fun f g => f ≫ g
  | of _X, _, one => fun _f _g => PUnit.unit
  | one, of _X, of _Y => fun f g => f ≫ g
  | one, _, one => fun _ _ => PUnit.unit
  | one, one, of _Y => by sorry
  | of _X, one, of _Y => by sorry



#exit

/-
open Sum in
instance : Category (ChainUni U t) where
  Hom
    | inl x, inr y => t ⟶ (Pb y.snd)
    | inl x, inl y => t ⟶ t
    | inr x, inl y => (Pb x.snd) ⟶ t
    | inr x, inr y => (Pb x.snd) ⟶ (Pb y.snd)
  id
    | inl x => 𝟙 t
    | inr x => 𝟙 (Pb x.snd)
  comp := _
  id_comp := _
  comp_id := _
  assoc := _
-/




/-
abbrev Mor := Σ x : α, Σ y : α, x ⟶ y

abbrev dom {α : Type u} [CategoryTheory.Category.{v, u} α] : Mor α → α := fun f ↦ f.fst

abbrev cod {α : Type u} [CategoryTheory.Category.{v, u} α] : Mor α → α := fun f ↦ f.snd.fst

structure Chain {α} [CategoryTheory.Category α] (U : Universe α) (X : α) (n : ℕ) where
  maps : Fin (n + 1) → Mor α
  cod (i : Fin (n +1)) : cod (maps i) = U.obj
  dom₀ : dom (maps 0) = X
  dom (i : Fin n) : dom (maps (succ i)) = pb
-/
-/


open CategoryTheory CategoryTheory.Limits Fin List

universe u v
/-
structure Universe (C : Type u) [CategoryTheory.Category.{v, u} C] where
  obj : C
  obj' : C
  map : obj' ⟶ obj
  pb {X} (f : X ⟶ obj) : α
  pb_vmap {X} (f : X ⟶ obj) : pb f ⟶ X
  pb_hmap {X} (f : X ⟶ obj) : pb f ⟶ obj'
  comm {f : X ⟶ obj} : pb_vmap f ≫ f =  pb_hmap f ≫ map
  is_pullback {f : X ⟶ obj} : IsLimit <| PullbackCone.mk (pb_vmap f) (pb_hmap f) comm

namespace Universe
-/
structure Universe (C : Type u) [CategoryTheory.Category.{v, u} C] where
  obj : C
  obj' : C
  map : obj' ⟶ obj
  pt {X} (f : X ⟶ obj) : α
  fst {X} (f : X ⟶ obj) : pt f ⟶ obj'
  snd {X} (f : X ⟶ obj) : pt f ⟶ X
  pullback (f : X ⟶ obj) : IsPullback (fst f) (snd f) map f
namespace Universe

variable {C : Type u} [CategoryTheory.Category.{v, u} C] [HasBinaryProducts C] {t : C} (ht : IsTerminal t)

abbrev Proj₁ (U : Universe C): prod U.obj U.obj' ⟶ U.obj := prod.fst

abbrev Proj₂ (U : Universe C): prod U.obj U.obj' ⟶ U.obj' := prod.snd

abbrev From (U : Universe C) : U.obj ⟶ t := IsTerminal.from ht _

end Universe
