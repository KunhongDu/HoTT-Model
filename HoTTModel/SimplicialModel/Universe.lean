import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks

-- This file aims to construct a universe in sSet
open Simplicial CategoryTheory Opposite Limits Functor

namespace SSet

variable {X Y : SSet} (f : X ⟶ Y)

section WellOrdered

notation "[" n "]" => Opposite.op (SimplexCategory.mk n)

abbrev Fibre (f : X ⟶ Y) {n : ℕ} (y : Y _[n]) : Set (X _[n]) :=
  (f.app [n]) ⁻¹' {y}

notation f "⁻¹" y => Fibre f y

-- decide to use PartialOrder -- Preorder doesn't have antisymmetric for `≤`
structure WellOrderedMap (X Y : SSet) where
  map : X ⟶ Y
  ord {n : ℕ} {y : Y _[n]} : PartialOrder (map ⁻¹ y)
  well_ord : IsWellOrder _ ((ord (y := y)).lt)

attribute [instance] WellOrderedMap.ord WellOrderedMap.well_ord

notation X " ⟶ₒ " Y => WellOrderedMap X Y

/-
#check instIsAntisymmLt

instance {f : X ⟶ₒ Y} {n : ℕ} {y : Y _[n]} : IsAsymm ↑(f.map⁻¹y) fun a b ↦ a ≤ b := instIsAsymmOfIsWellOrder _

instance {f : X ⟶ₒ Y} {n : ℕ} {y : Y _[n]} : PartialOrder (f.map ⁻¹ y) where
  le := f.ord.le
  le_refl := f.ord.le_refl
  le_trans := f.ord.le_trans
  le_antisymm := (IsAsymm.isAntisymm _).antisymm
-/


def FibTrans {f : X ⟶ Y} {f' : X' ⟶ Y} (g : X ⟶ X') {y : Y _[n]}
  (comm : f = g ≫ f') (a : ↑(f ⁻¹ y)): ↑(f' ⁻¹ y) := ⟨(g.app [n]) a,
    by
      simp
      have : f'.app [n] (g.app [n] ↑a) = (g ≫ f').app [n] ↑a := rfl
      rw [this, ← comm]
      exact a.2
    ⟩

-- can't find: nonempty set in a well order has a least element

lemma FibTrans.eq_iff_eq {f : X ⟶ Y} {f' : X' ⟶ Y} (F : Iso X X') {y : Y _[n]}
  (comm : f = F.hom ≫ f') (a b : ↑(f ⁻¹ y)): a = b ↔ FibTrans F.hom comm a = FibTrans F.hom comm b := by
    constructor
    exact fun h ↦ (by rw [h])
    intro h
    apply_fun FibTrans (f := f') (f' := f) F.inv (by simp [comm]) at h
    simp [FibTrans] at h
    exact h

lemma isLeast_lt_false {α β: Type} [Preorder α] [Preorder β] [IsWellOrder α (· < ·)] [IsWellOrder β (· < ·)] {f g : α ≃o β} {a : α} (ha : IsLeast {a | f a = g a}ᶜ a) (lt : f a < g a) : False := by
  set a' := g.symm (f a) with ha'
  apply_fun g at ha'
  simp at ha'
  have aux : f a' < g a' := by
    rwa [ha', OrderIso.lt_iff_lt f, ← OrderIso.lt_iff_lt g, ha']
  have : f a ≤ f a' := by rw [OrderIso.le_iff_le]; exact ha.2 aux.ne
  apply False.elim <| (lt_self_iff_false (f a')).mp (lt_of_lt_of_le aux (ha'.symm ▸ this))


-- use this : InitialSeg.ofIso
def _root_.OrderIso.toInitialSeg {α β: Type*} [Preorder α] [Preorder β] (f : α ≃o β) : InitialSeg (α := α) (β := β) (· < ·) (· < ·) where
  toFun := f
  inj' := f.injective
  map_rel_iff' := by simp only [Function.Embedding.coeFn_mk, OrderIso.lt_iff_lt, implies_true]
  init' := by
    intro _ b _
    use f.symm b
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, OrderIso.apply_symm_apply]

lemma initialSeg_of_isWellOrder_eq {α β: Type*} [Preorder α] [Preorder β] (f : α ≃o β) (a : α) : f a = f.toInitialSeg a := by
  simp only [OrderIso.toInitialSeg]
  rfl

lemma _root_.IsWellOrder.OrderIso_apply_eq (α β: Type*) [Preorder α] [Preorder β] [IsWellOrder α (· < ·)] [IsWellOrder β (· < ·)] (f g : α ≃o β) (a : α) : f a = g a := by
  rw [initialSeg_of_isWellOrder_eq, initialSeg_of_isWellOrder_eq]
  apply InitialSeg.eq

lemma _root_.IsWellOrder.OrderIso_eq (α β: Type) [Preorder α] [Preorder β] [IsWellOrder α (· < ·)] [IsWellOrder β (· < ·)] (f g : α ≃o β) : f = g := by
  ext
  apply IsWellOrder.OrderIso_apply_eq

@[ext]
structure OrderIso (f : X ⟶ₒ Y) (f' : X' ⟶ₒ Y) extends Iso X X' where
  comm : f.1 = hom ≫ f'.1
  lt_iff_lt {y : Y _[n]} (a b : ↑((f.1) ⁻¹ y)) : a < b ↔ (FibTrans hom comm a) < (FibTrans hom comm b)

-- this is stupid!!!
lemma OrderIso.ext' {f : X ⟶ₒ Y} {f' : X' ⟶ₒ Y} (F G : OrderIso f f') (w : F.hom = G.hom) : F = G := by
  ext1
  exact w
  have : F.toIso = G.toIso := Iso.ext w
  apply_fun Iso.inv at this
  exact this

def OrderIso.symm {f : X ⟶ₒ Y} {f' : X' ⟶ₒ Y} (F : OrderIso f f') : OrderIso f' f where
  hom := F.inv
  inv := F.hom
  hom_inv_id := F.inv_hom_id
  inv_hom_id := F.hom_inv_id
  comm := by rw [F.comm]; simp only [Iso.inv_hom_id_assoc]
  lt_iff_lt {n} {y} a b := by
    rw [F.lt_iff_lt]
    simp only [FibTrans, FunctorToTypes.inv_hom_id_app_apply, Subtype.coe_eta]

@[simp]
lemma OrderIso.symm_hom {f : X ⟶ₒ Y} {f' : X' ⟶ₒ Y} (F : OrderIso f f') : F.symm.hom = F.inv := rfl

#check OrderIso.ofRelIsoLT

-- define that OrderIso gives an `OrderIso` between fibres
def FibreOrderIso {f : X ⟶ₒ Y} {g : X' ⟶ₒ Y} (F : OrderIso f g) {n : ℕ} (y : Y _[n]) : (f.map ⁻¹ y) ≃o (g.map ⁻¹ y) where
  toFun x := FibTrans F.hom F.comm x
  invFun x := FibTrans F.symm.hom F.symm.comm x
  left_inv := by simp only [Function.LeftInverse, FibTrans, OrderIso.symm_hom,
      FunctorToTypes.hom_inv_id_app_apply, implies_true]
  right_inv := by simp only [Function.RightInverse, Function.LeftInverse, FibTrans,
    OrderIso.symm_hom, FunctorToTypes.inv_hom_id_app_apply, implies_true]
  map_rel_iff' {a} {b} := by
    simp only [OrderIso.symm_hom, Equiv.coe_fn_mk, le_iff_eq_or_lt]
    rw [F.lt_iff_lt, ← FibTrans.eq_iff_eq _ F.comm _ _]


-- the default ext for simplcial map is not easy to use

lemma SimplicialMap_ext {f g: X ⟶ Y} (h : ∀ n (x : X _[n]), f.app [n] x = g.app [n] x): f = g := by
  ext n a
  cases n with
  | op n => apply h (SimplexCategory.len n)

lemma subsingleton_OrderIso {f : X ⟶ₒ Y} {f' : X' ⟶ₒ Y} (F G : OrderIso f f') : F = G := by
  apply OrderIso.ext'
  apply SimplicialMap_ext
  intro n a
  set F' := FibreOrderIso F (f.map.app [n] a)
  set G' := FibreOrderIso G (f.map.app [n] a)
  have aux1 : F.hom.app [n] a = (FibreOrderIso F (f.map.app [n] a)) ⟨a, by simp⟩ := by
    simp only [FibreOrderIso, FibTrans, OrderIso.symm_hom, RelIso.coe_fn_mk, Equiv.coe_fn_mk]
  have aux2 : G.hom.app [n] a = G' ⟨a, by simp⟩ := by
    simp [G', FibreOrderIso, FibTrans, OrderIso.symm_hom, RelIso.coe_fn_mk, Equiv.coe_fn_mk]
  have : F' ⟨a, by simp⟩ = G' ⟨a, by simp⟩ := by
    apply IsWellOrder.OrderIso_apply_eq _ _ F' G'
  rw [aux1, aux2, this]

end WellOrdered

section UniversalSimplicialSet

variable (α : Cardinal.{0}) {reg : Cardinal.IsRegular α}

abbrev α_small (f : X ⟶ Y) := ∀ n, ∀ y : Y _[n], Cardinal.mk (f ⁻¹ y) < α

structure α_smallWO (Y : SSet) where
  of : SSet
  map : of ⟶ₒ Y
  α_small : α_small α map.1

def α_smallWO.rel {α} (f g : α_smallWO α Y) : Prop := Nonempty (OrderIso f.2 g.2)

def α_smallWO.rel_iseqv {α} : Equivalence (α_smallWO.rel (Y := Y) (α := α)) := sorry

instance Setoid_α_smallWO {α} : Setoid (α_smallWO α Y) where
  r := α_smallWO.rel
  iseqv := α_smallWO.rel_iseqv

def _Ω_obj (α) (Y) := Quotient (@Setoid_α_smallWO Y α)


-- size issue here
-- use `Small` to circumvent this temporarily
instance : Small.{0,1} (_Ω_obj α Y) := sorry

abbrev Ω_obj (α) (Y) := Shrink (_Ω_obj α Y)


def Ω_map (f : Y ⟶ Y') : Ω_obj α Y' ⟶ Ω_obj α Y := sorry

lemma Ω_map_id : Ω_map α (𝟙 Y) = 𝟙 (Ω_obj α Y) := sorry

lemma Ω_map_comp {f : Y ⟶ Y'} {g : Y' ⟶ Y''}: (Ω_map α g) ≫ (Ω_map α f) = Ω_map α (f ≫ g) := sorry

def Ω : SSetᵒᵖ ⥤ Type 0 where
  obj Y := Ω_obj α (unop Y)
  map f := Ω_map α (unop f)
  map_id Y := by simp; rw [← Ω_map_id]; apply congrArg; exact unop_id -- rw does not work....
  map_comp f g:= by simp; rw [Ω_map_comp]; apply congrArg; exact unop_comp

def W : SSet := Functor.op (yoneda (C:= SimplexCategory)) ⋙ Ω α

/-
yoneda.op : SimplexCategoryᵒᵖ ⥤ (SimplexCategoryᵒᵖ ⥤ Type)ᵒᵖ
-/

instance ΩPreservesLimitsOfSize : PreservesLimitsOfSize.{1,0} (Ω α) := sorry

-- the names are BAD!!!!

def W_represent_Ω : yoneda.obj (W α) ≅ (Ω α) := sorry

variable (Z : SSet.{0})

def W_represent_Ω_app := (W_represent_Ω α).app (op Z)

def toW_of_Ω (a : (Ω α).obj (op Z)) : Z ⟶ (W α) := (W_represent_Ω_app α Z).inv a

def Ω_of_toW (f : Z ⟶ (W α)) : (Ω α).obj (op Z) := (W_represent_Ω_app α Z).hom f

end UniversalSimplicialSet

end SSet
