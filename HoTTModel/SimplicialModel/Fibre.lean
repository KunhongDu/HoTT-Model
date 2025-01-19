import HoTTModel.LocallyCartesianClosed.Presheaf
import HoTTModel.SSet.Fibrations
import HoTTModel.SSet.Representables
import HoTTModel.Lemmas.OrderOfEquiv
import HoTTModel.Lemmas.IsWellOrder
-- import Mathlib.SetTheory.Ordinal.Basic
import HoTTModel.Lemmas.Cardinal

/-!

# Fibres of a simplcial sets

1. Well-ordered morphisms

2. Order-isomorphisms

3. Smallness

-/

section
-- equivalence between `SimplexCategory` and `ℕ`

def SimplexCategory.EquivNat :
    SimplexCategory ≃ ℕ where
  toFun := len
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Infinite SimplexCategory := by
  rw [SimplexCategory.EquivNat.infinite_iff]
  infer_instance

instance : Infinite SimplexCategoryᵒᵖ := by
  rw [Opposite.equivToOpposite.symm.infinite_iff]
  infer_instance

lemma SimplexCategory.cardinal_eq_alphe0 :
    Cardinal.mk SimplexCategory = Cardinal.aleph0 := by
  apply Cardinal.mk_congr
  apply SimplexCategory.EquivNat.trans Equiv.ulift.{0,0}.symm

lemma SimplexCategory.opposite_cardinal_eq_alphe0 :
    Cardinal.mk SimplexCategoryᵒᵖ = Cardinal.aleph0 := by
  rw [← cardinal_eq_alphe0]
  apply Cardinal.mk_congr Opposite.equivToOpposite.symm

end

open CategoryTheory Simplicial Opposite Set SSet standardSimplex Classical

namespace SSet
noncomputable section

@[simps]
def _root_.CategoryTheory.IsPullback.PreimageEquiv {P X Y Z : Type u}
  {h : P ⟶ X} {i : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (D : IsPullback h i f g) (y : Y) :
    i ⁻¹' {y} ≃ f ⁻¹' {g y} where
  toFun := fun p ↦ ⟨h p.val, by
    convert congrFun D.w p.val
    simp; rw [p.property]⟩
  invFun := fun x ↦ ⟨D.lift Subtype.val (fun _ ↦ y) (by ext a; exact a.2) x, by
    change (_ ≫ i) x = _
    simp only [IsPullback.lift_snd]⟩
  left_inv := by
    rw [Function.leftInverse_iff_comp]
    apply Function.Injective.comp_left Subtype.val_injective
    simp only [Function.comp_id]
    apply D.hom_ext
    . ext a; simp
      change (_ ≫ h) _ = _
      rw [IsPullback.lift_fst]
    . ext a; simp
      change (_ ≫ i) _ = _
      rw [IsPullback.lift_snd]
      exact a.2.symm
  right_inv := by
    intro a; ext : 1; simp
    change (_ ≫ h) _ = _
    rw [IsPullback.lift_fst]
end

noncomputable section Fibre
variable {X Y : SSet.{u}} (f : X ⟶ Y)

/--
  The fibre of a simplex is the preimage (in its own layer).
-/
abbrev Fibre {n : SimplexCategoryᵒᵖ} (y : Y.obj n) : Set (X.obj n) :=
  (f.app n) ⁻¹' {y}

def _root_.CategoryTheory.IsPullback.FibreEquiv {P X Y Z : SSet.{u}}
  {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (D : IsPullback fst snd f g) {n : SimplexCategoryᵒᵖ} (y : Y.obj n) :
    Fibre snd y ≃ Fibre f (g.app _ y) :=
  (IsPullback.map (ev n) D).PreimageEquiv _

end Fibre

namespace Fibre
variable {X X' Y : SSet.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y} (g : X ⟶ X')
    (comm : f = g ≫ f')

def trans (y : Y.obj n) (a : (Fibre f y)) :
    (Fibre f' y) :=
  ⟨g.app _ a, comm.symm ▸ a.2⟩

end Fibre

section WellOrdered

variable {X Y : SSet.{u}} (f : X ⟶ Y)
-- decide to use PartialOrder -- Preorder doesn't have antisymmetric for `≤`

variable (X Y) in
structure WellOrderedHom where
  hom : X ⟶ Y
  ord {n : SimplexCategoryᵒᵖ} {y : Y.obj n} : LinearOrder (Fibre hom y)
  isWellOrder {n : SimplexCategoryᵒᵖ} {y : Y.obj n} : IsWellOrder _ ((ord (y := y)).lt)

-- ParitialOrder + WellOrder should be LinearOrder
-- but not show about how to define the instance so that
-- the defintion of relations are compatible
-- for now, use LinearOrder

attribute [instance] WellOrderedHom.ord WellOrderedHom.isWellOrder

notation X " ⟶ₒ " Y => WellOrderedHom X Y

@[simp]
noncomputable def toWO (f : X ⟶ Y) : X ⟶ₒ Y where
  hom := f
  ord := by classical exact linearOrderOfSTO WellOrderingRel
  isWellOrder := WellOrderingRel.isWellOrder

abbrev WellOrderedHom.Fibre (f : X ⟶ₒ Y) {n : SimplexCategoryᵒᵖ}
  (y : Y.obj n) := SSet.Fibre f.hom y

infix:80 "⁻¹ " => WellOrderedHom.Fibre

-- This can be defined for any morphism, but since I mainly work with WO
-- restricting the definition gives better pretty-print
def move {f : X ⟶ₒ Y} (φ : n ⟶ m) {y : Y.obj n} (x : f⁻¹ y) :
    f⁻¹ (Y.map φ y) :=
  ⟨X.map φ x, by
    simp only [mem_preimage, mem_singleton_iff];
    rw [hom_naturality_apply, x.2]⟩

lemma fibre_congr {f : X ⟶ₒ Y} {y y' : Y.obj n} {x : X.obj n} (eq : y = y') {h} {h'} :
    HEq (⟨x, h⟩ : f⁻¹ y) (⟨x, h'⟩ : f⁻¹ y') := by
  cases eq; rfl

lemma move_comp_heq {f : X ⟶ₒ Y} {φ : n ⟶ m} {ψ : m ⟶ k} {x : f⁻¹ y} :
    HEq (move (φ ≫ ψ) x) (move ψ (move φ x)) := by
  simp [move]
  apply fibre_congr (by simp)

end WellOrdered
end SSet

section Pullback_Fibre_WellOrdered
namespace CategoryTheory.IsPullback
open SSet

variable {P X Y Z : SSet.{u}} {h : P ⟶ X} {i : P ⟶ Y} {f : X ⟶ₒ Z} {g : Y ⟶ Z}
  (D : IsPullback h i f.hom g) {n : SimplexCategoryᵒᵖ} (y : Y.obj n)

noncomputable def FibreLinearOrder  :
    LinearOrder (Fibre i y) :=
  LinearOrder.ofEquiv (D.FibreEquiv y).symm

namespace FibreLinearOrder

lemma le_iff_le (a b : Fibre i y) :
    (D.FibreLinearOrder y).le a b ↔ D.FibreEquiv _ a ≤ D.FibreEquiv _ b := by
  rfl

lemma lt_iff_lt (a b : Fibre i y) :
    (D.FibreLinearOrder y).lt a b ↔ D.FibreEquiv _ a < D.FibreEquiv _ b := by
  rw [(D.FibreLinearOrder y).lt_iff_le_not_le, lt_iff_le_not_le,
      le_iff_le, le_iff_le]

noncomputable def ltRelIso :
    RelIso (D.FibreLinearOrder y).lt (f.ord (y := g.app _ y)).lt where
  toEquiv := D.FibreEquiv y
  map_rel_iff' := (lt_iff_lt D y _ _).symm

@[simp]
noncomputable def OrderIso :
    @OrderIso (Fibre i y) (f⁻¹ (g.app _ y)) (D.FibreLinearOrder y).toLE _ where
  toEquiv := D.FibreEquiv y
  map_rel_iff' := (le_iff_le D y _ _).symm

def isWellOrder :
    IsWellOrder _ (D.FibreLinearOrder y).lt := by
  apply LinearOrder.ofEquiv.isWellOrderOfIsWellOrder _ f.isWellOrder

end FibreLinearOrder
end CategoryTheory.IsPullback
end Pullback_Fibre_WellOrdered

namespace SSet
section

@[ext]
structure OrderIso (f : X ⟶ₒ Y) (f' : X' ⟶ₒ Y) extends Iso X X' where
  comm : f.1 = hom ≫ f'.1
  mono {y : Y.obj n} : Monotone $ Fibre.trans hom comm (y := y)

section
variable {f : X ⟶ₒ Y} {f' : X' ⟶ₒ Y} (F G : OrderIso f f')
namespace OrderIso

lemma comm_inv :
    F.inv ≫ f.hom = f'.hom :=
  (Iso.inv_comp_eq _).mpr F.comm

lemma ext' (w : F.hom = G.hom) :
    F = G := by
  have := Iso.ext w
  ext1 <;> rw [this]

def trans {n : SimplexCategoryᵒᵖ} (y : Y.obj n) :=
  Fibre.trans F.hom F.comm y

def symm_trans {n : SimplexCategoryᵒᵖ} (y : Y.obj n) :=
  Fibre.trans F.inv F.comm_inv.symm y

def FibreEquiv {n : SimplexCategoryᵒᵖ} (y : Y.obj n) :
    ↑(f⁻¹ y) ≃ ↑(f'⁻¹ y) where
  toFun := F.trans y
  invFun := F.symm_trans y
  left_inv := by intro; simp [trans, Fibre.trans, symm_trans]
  right_inv := by intro; simp [trans, Fibre.trans, symm_trans]

lemma strictMono {y : Y.obj n} :
    StrictMono $ F.trans y :=
  F.mono.strictMono_of_injective (F.FibreEquiv _).injective

lemma lt_iff_lt {n : SimplexCategoryᵒᵖ} {y : Y.obj n} (a b : f⁻¹ y) :
    a < b ↔ F.trans y a < F.trans y b :=
  F.strictMono.lt_iff_lt.symm

lemma le_iff_le {n : SimplexCategoryᵒᵖ} {y : Y.obj n} (a b : f⁻¹ y) :
    a ≤ b ↔ F.trans y a ≤ F.trans y b :=
  F.strictMono.le_iff_le.symm

def symm : OrderIso f' f where
  toIso := F.toIso.symm
  comm := F.comm_inv.symm
  mono := by
    intro n y
    apply StrictMono.monotone
    intro a b hab
    rw [F.lt_iff_lt]
    convert hab
    <;> convert (F.FibreEquiv y).right_inv _

@[simp]
lemma symm_hom : F.symm.hom = F.inv := rfl

def toOverIso : Over.mk f.hom ≅ Over.mk f'.hom :=
  Over.isoMk F.toIso F.comm.symm

def FibreOrderIso {n : SimplexCategoryᵒᵖ} (y : Y.obj n) :
    (f⁻¹ y) ≃o (f'⁻¹ y) where
  toEquiv := F.FibreEquiv y
  map_rel_iff' {_} {_} := F.strictMono.le_iff_le

-- the default ext for simplcial map is not easy to use

lemma allEq {f : X ⟶ₒ Y} {f' : X' ⟶ₒ Y} (F G : OrderIso f f') : F = G := by
  apply OrderIso.ext'
  ext n a: 2
  have aux1 : F.hom.app _ a = (F.FibreOrderIso (f.hom.app _ a)) ⟨a, by simp⟩ :=
    rfl
  have aux2 : G.hom.app _ a = (G.FibreOrderIso (f.hom.app _ a)) ⟨a, by simp⟩ :=
    rfl
  rw [aux1, aux2]
  congr 1
  apply IsWellOrder.OrderIso_apply_eq

lemma FibreOrderIso_move {n m: SimplexCategoryᵒᵖ} {y : Y.obj n} {φ : n ⟶ m} (x : f⁻¹ y) :
    F.FibreOrderIso _ (move φ x) = move φ (F.FibreOrderIso _ x) := by
  simp [FibreOrderIso, FibreEquiv, trans, Fibre.trans, move]
  rw [hom_naturality_apply]

lemma FibreOrderIso_symm_move {n m: SimplexCategoryᵒᵖ} {y : Y.obj n} {φ : n ⟶ m} (x : f'⁻¹ y) :
    (F.FibreOrderIso _).symm (move φ x) = move φ ((F.FibreOrderIso _).symm x) := by
  apply_fun (F.FibreOrderIso _)
  simp [FibreOrderIso_move]

end OrderIso

variable (f f') in
structure Pieces where
  orderIso {n : SimplexCategoryᵒᵖ} (y : Y.obj n) : f⁻¹ y ≃o f'⁻¹ y
  compatible {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    {y : Y.obj n} (x : f⁻¹ y) :
      orderIso (Y.map φ y) (move φ x) = move φ (orderIso y x)

namespace Pieces
variable (P : Pieces f f')

lemma compatible_val {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
  {y : Y.obj n} (x : f⁻¹ y) :
    (P.orderIso (Y.map φ y) (move φ x)).val = X'.map φ (P.orderIso y x) :=
  congrArg Subtype.val (P.compatible _ _)

lemma symm_compatible {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
  {y : Y.obj n} (x : f'⁻¹ y) :
    (P.orderIso (Y.map φ y)).symm (move φ x) = move φ ((P.orderIso y).symm x) := by
  apply_fun P.orderIso _
  simp only [OrderIso.apply_symm_apply, P.compatible]

lemma symm_compatible_val {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
  {y : Y.obj n} (x : f'⁻¹ y) :
    ((P.orderIso (Y.map φ y)).symm (move φ x)).val = X.map φ ((P.orderIso y).symm x) :=
  congrArg Subtype.val (P.symm_compatible _ _)

lemma orderIso_congr {y y' : Y.obj n} (h : y = y')
  {x : f⁻¹ y} {x' : f⁻¹ y'} (h' : HEq x x'):
    (P.orderIso y x).val = ↑(P.orderIso y' x') := by
  cases h; cases h'; rfl

@[simp, simps]
def ofPieces.hom : X ⟶ X' where
  app := fun n x ↦ (P.orderIso (f.hom.app n x) ⟨x, rfl⟩).val
  naturality := by
    intro n m φ
    ext x; simp
    convert P.compatible_val φ ⟨x, rfl⟩ using 1
    have := hom_naturality_apply f.hom φ x
    apply P.orderIso_congr this (fibre_congr this)

lemma orderIso_symm_congr {y y' : Y.obj n} (h : y = y')
  {x : f'⁻¹ y} {x' : f'⁻¹ y'} (h' : HEq x x'):
    ((P.orderIso y).symm x).val = ↑((P.orderIso y').symm x') := by
  cases h; cases h'; rfl

@[simp, simps]
def ofPieces.inv : X' ⟶ X where
  app := fun n x ↦ ((P.orderIso (f'.hom.app n x)).symm ⟨x, rfl⟩).val
  naturality := by
    intro n m φ
    ext x; simp
    convert P.symm_compatible_val φ ⟨x, rfl⟩ using 1
    have := hom_naturality_apply f'.hom φ x
    apply P.orderIso_symm_congr this (fibre_congr this)

lemma symm_apply_apply_of_eq {y y' : Y.obj n} {x : f⁻¹ y'} (eq : y = y') {h} :
    ((P.orderIso y).symm ⟨P.orderIso y' x, h⟩).val = x.val := by
  cases eq; simp

lemma apply_symm_apply_of_eq {y y' : Y.obj n} {x : f'⁻¹ y} (eq : y = y') {h} :
    ((P.orderIso y') ⟨(P.orderIso y).symm x, h⟩).val = x.val := by
  cases eq; simp

def toOrderIso : OrderIso f f' where
  hom := ofPieces.hom P
  inv := ofPieces.inv P
  hom_inv_id := by
    ext n x; erw [NatTrans.vcomp_app]; simp
    rw [symm_apply_apply_of_eq _ ((P.orderIso (f.hom.app n x)) ⟨x, rfl⟩).2]; rfl
  inv_hom_id := by
    ext n x; erw [NatTrans.vcomp_app]; simp
    rw [apply_symm_apply_of_eq _ ((P.orderIso (f'.hom.app n x)).symm ⟨x, rfl⟩).2.symm]; rfl
  comm := by
    ext n x; erw [NatTrans.vcomp_app]; simp
    exact ((P.orderIso (f.hom.app n x)) ⟨x, rfl⟩).2.symm
  mono := by
    intro n y
    convert (P.orderIso y).monotone
    ext x : 2
    simp [Fibre.trans]
    apply P.orderIso_congr x.2 (fibre_congr x.2)

end Pieces
end

noncomputable section UniversalSimplicialSet
variable {α : Cardinal.{u}} {X Y : SSet.{u}}  -- {reg : Cardinal.IsRegular α}

variable (α) in
def SmallFibre  (f : X ⟶ Y) : Prop :=
  ∀ ⦃n⦄, ∀ y : Y.obj n, Cardinal.mk (Fibre f y) < α

variable (α) in
structure SmallWO (Y : SSet.{u}) where
  of : SSet.{u}
  wo : of ⟶ₒ Y
  small : SmallFibre α wo.hom

@[simp]
noncomputable def toSmallWO (f : X ⟶ Y) (hf : SmallFibre α f) : SmallWO α Y where
  wo := toWO f
  small := hf

abbrev SmallWO.hom (f : SmallWO α Y) := f.wo.hom

def SmallWO.rel {α} (f g : SmallWO α Y) : Prop :=
  Nonempty (OrderIso f.2 g.2)

def SmallWO.relIseqv {α} : Equivalence (SmallWO.rel (Y := Y) (α := α)) where
  refl a := ⟨{
    toIso := Iso.refl _
    comm := by simp
    mono := fun {_ _} _ _ h ↦ h
  }⟩
  symm {a b} := by
    intro ⟨h⟩
    exact ⟨{
      toIso := h.toIso.symm
      comm := by simp [h.comm]
      mono := by
        intro _ _ _ _ hcd
        rwa [h.symm.le_iff_le] at hcd
      }⟩
  trans {a b c} := by
    intro ⟨hab⟩ ⟨hbc⟩
    exact ⟨{
      toIso := hab.toIso ≪≫ hbc.toIso
      comm := by simp [hab.comm, hbc.comm]
      mono := by
        intro _ _ _ _ h
        rwa [hab.le_iff_le, hbc.le_iff_le] at h
      }⟩

instance Setoid_SmallWO {α} : Setoid (SmallWO α Y) where
  r := SmallWO.rel
  iseqv := SmallWO.relIseqv

def Ω_obj₀ (α) (Y) := Quotient (@Setoid_SmallWO Y α)

def SmallWO.toOrderIsoCast {a b : SmallWO α Y} (h : a = b) :
    OrderIso a.wo b.wo where
  toIso := eqToIso (congrArg _ h)
  comm := by cases h; simp
  mono := by cases h; exact fun h ↦ h

section Smallness
open Function

variable (α X) in
structure SmallFibresWithStructures where
  fibre {n : SimplexCategoryᵒᵖ} (x : X.obj n) : Shrink (Set.Iio α)
  map {n m : SimplexCategoryᵒᵖ} :
    (n ⟶ m) → (Σ x : X.obj n, ((equivShrink _).symm (fibre x)).1.out) →
      (Σ x : X.obj m, ((equivShrink _).symm (fibre x)).1.out)
  map_nat {n m : SimplexCategoryᵒᵖ} {f : n ⟶ m}
    (a : Σ x : X.obj n, ((equivShrink _).symm (fibre x)).1.out) : (map f a).fst = X.map f a.fst
  map_id {n : SimplexCategoryᵒᵖ} : map (𝟙 n) = id
  map_comp {n m k : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (ψ : m ⟶ k) :
    map (φ ≫ ψ) = map ψ ∘ map φ
  order {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    LinearOrder ((equivShrink _).symm (fibre x)).1.out
  isWellOrder {n : SimplexCategoryᵒᵖ} (x : X.obj n) : IsWellOrder _ ((order x).lt)

attribute [instance] SmallFibresWithStructures.order

@[simp]
def SmallFibresWithStructures.toSSet (S : SmallFibresWithStructures α X) :
    SSet.{u} where
  obj n := Σ x : X.obj n, ((equivShrink _).symm (S.fibre x)).1.out
  map φ := S.map φ
  map_id _ := S.map_id
  map_comp φ ψ := S.map_comp φ ψ

@[simp]
def SmallFibresWithStructures.toHom (S : SmallFibresWithStructures α X) :
    S.toSSet ⟶ X where
  app n y := y.fst
  naturality n m f := by
    ext; apply S.map_nat

def _root_.Sigma.EquivFstPreimage (A : Type u) (f : A → Type u) (a : A) :
    f a ≃ ↑((fun x : (b : A) × f b ↦ x.fst) ⁻¹' {a}) where
  toFun y := ⟨⟨a, y⟩, by simp only [mem_preimage, mem_singleton_iff]⟩
  invFun y := by
    convert y.1.2 -- this is bad... try to use ▸
    have := y.2
    simp only [mem_preimage, mem_singleton_iff] at this
    exact this.symm
  left_inv y := by simp
  right_inv y := by
    ext; all_goals simp
    have := y.2
    simp only [mem_preimage, mem_singleton_iff] at this
    exact this.symm

def SmallFibresWithStructures.FibreToHomEquiv (S : SmallFibresWithStructures α X)
  (y : X.obj n) :
    Fibre S.toHom y ≃ Quotient.out ((equivShrink ↑(Iio α)).symm (S.fibre y)).val :=
  (Sigma.EquivFstPreimage _ (fun x ↦ ((equivShrink _).symm (S.fibre x)).1.out) y).symm

lemma SmallFibresWithStructures.cardinal_mk_fibre_to_hom_lt
  (S : SmallFibresWithStructures α X) (y : X.obj n) :
    Cardinal.mk (Fibre S.toHom y) < α := by
  rw [Cardinal.mk_congr (S.FibreToHomEquiv y)]
  simp only [Cardinal.mk_out]
  exact ((equivShrink ↑(Iio α)).symm (S.fibre y)).2

@[simp]
def SmallFibresWithStructures.toSmallWO (S : SmallFibresWithStructures α X) :
    SmallWO α X where
  wo := {
    hom := S.toHom
    ord := fun {_ y} ↦ LinearOrder.ofEquiv (ord := S.order y) (S.FibreToHomEquiv y).symm
    isWellOrder :=
    LinearOrder.ofEquiv.isWellOrderOfIsWellOrder (ord := S.order _) _ (S.isWellOrder _)
  }
  small {_} _ := S.cardinal_mk_fibre_to_hom_lt _

variable (α X) in
def SmallFibresWithStructures.to (S : SmallFibresWithStructures α X) :
    Ω_obj₀ α X := ⟦S.toSmallWO⟧

def SmallWO.OutEquivFibre (a : SmallWO α X):
    Quotient.out ((equivShrink ↑(Iio α)).symm ((equivShrink ↑(Iio α))
      ⟨Cardinal.mk ↑(Fibre a.wo.hom x), a.small x⟩)).val ≃
        ↑(Fibre a.wo.hom x) := by
  simp only [Equiv.symm_apply_apply]
  apply Cardinal.outMkEquiv

lemma SmallWO.OutEquivFibre_symm_apply_congr {a : SmallWO α X} {x y : X.obj n} (eq : x = y)
  {s : Quotient.out ((equivShrink ↑(Iio α)).symm ((equivShrink ↑(Iio α))
      ⟨Cardinal.mk ↑(Fibre a.wo.hom x), a.small x⟩)).val} {h} :
    HEq (a.OutEquivFibre.symm (⟨(a.OutEquivFibre s).val, h⟩ : Fibre a.wo.hom y)) s := by
  cases eq
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply, heq_eq_eq]

lemma SmallWO.OutEquivFibre_symm_congr {a : SmallWO α X} {x y : X.obj n} (eq : x = y)
  {s : Fibre a.wo.hom x} {s' : Fibre a.wo.hom y} (eq' : HEq s s'):
    HEq (a.OutEquivFibre.symm s) (a.OutEquivFibre.symm s') := by
  cases eq
  cases eq'
  rfl

lemma SmallWO.OutEquivFibre_congr {a : SmallWO α X} {x y : X.obj n} (eq : x = y)
  {s : Quotient.out ((equivShrink ↑(Iio α)).symm ((equivShrink ↑(Iio α))
      ⟨Cardinal.mk ↑(Fibre a.wo.hom x), a.small x⟩)).val}
  {s' : Quotient.out ((equivShrink ↑(Iio α)).symm ((equivShrink ↑(Iio α))
      ⟨Cardinal.mk ↑(Fibre a.wo.hom y), a.small y⟩)).val} (eq' : HEq s s'):
    HEq (a.OutEquivFibre s) (a.OutEquivFibre s') := by
  cases eq
  cases eq'
  rfl

lemma SmallWO.fibre_congr {a : SmallWO α X} {x x' : X.obj n} {b b' : a.of.obj n} {h} {h'}
  (eq : x = x') (eq' : b = b') :
    HEq (⟨b, h⟩ : Fibre a.wo.hom x) (⟨b', h'⟩ : Fibre a.wo.hom x') := by
  cases eq
  cases eq'
  rfl

@[simp]
def SmallWO.toSmallFibresWithStructures (a : SmallWO α X) :
    SmallFibresWithStructures α X where
  fibre {n} x := equivShrink _
      ⟨Cardinal.mk (a.wo⁻¹ x), a.small x⟩
  map {n m} φ x :=
    ⟨X.map φ x.fst, a.OutEquivFibre.symm (move φ (a.OutEquivFibre x.snd))⟩
  map_nat {n m f} x := by simp
  map_id {n} := by
    ext x
    . simp
    . simp [move]
      apply OutEquivFibre_symm_apply_congr (FunctorToTypes.map_id_apply _ _).symm
  map_comp {n m k} φ ψ := by
    ext x
    . simp
    . simp [move]
      apply OutEquivFibre_symm_congr (FunctorToTypes.map_comp_apply _ _ _ _)
        (fibre_congr (FunctorToTypes.map_comp_apply _ _ _ _) rfl)
  order _ := LinearOrder.ofEquiv a.OutEquivFibre.symm
  isWellOrder _ := LinearOrder.ofEquiv.isWellOrderOfIsWellOrder _ a.wo.isWellOrder

@[simp]
def SmallWO.toSmallFibresWithStructures_equivObj (a : SmallWO α X) (n : SimplexCategoryᵒᵖ) :
    (x : X.obj n) ×
      Quotient.out ((equivShrink ↑(Iio α)).symm ((equivShrink ↑(Iio α))
        ⟨Cardinal.mk ↑(Fibre a.wo.hom x), a.small _⟩)).val
          ≃ a.of.obj n where
  toFun s := (a.OutEquivFibre s.snd).val
  invFun x := ⟨a.hom.app _ x, a.OutEquivFibre.symm ⟨x, rfl⟩⟩
  left_inv s := by
    have : a.hom.app n (a.OutEquivFibre s.snd).val = s.fst := (a.OutEquivFibre s.snd).2
    ext; all_goals simp
    . exact this
    . apply OutEquivFibre_symm_apply_congr this.symm
  right_inv x := by simp only [Equiv.apply_symm_apply]

def SmallWO.toSmallFibresWithStructures.Iso (a : SmallWO α X) :
    a.toSmallFibresWithStructures.toSmallWO.of ≅ a.of where
  hom := {
    app := fun n ↦ ⇑(a.toSmallFibresWithStructures_equivObj n)
    naturality := by intro _ _ _; ext; simp; rfl
  }
  inv := {
    app := fun n ↦ ⇑(a.toSmallFibresWithStructures_equivObj n).symm
    naturality := by
      intro m n φ; ext x; simp
      have := hom_naturality_apply a.hom φ x
      exact ⟨this, OutEquivFibre_symm_congr this (fibre_congr this rfl)⟩
  }
  hom_inv_id := by
    ext n b
    erw [NatTrans.vcomp_app]
    simp only [types_comp_apply, Equiv.symm_apply_apply]
    rfl
  inv_hom_id := by
    ext n b
    erw [NatTrans.vcomp_app]
    simp; rfl

def SmallWO.toSmallFibresWithStructures.OrderIso (a : SmallWO α X) :
    OrderIso a.toSmallFibresWithStructures.toSmallWO.wo a.wo where
  toIso := toSmallFibresWithStructures.Iso a
  comm := by
    ext n x
    simp only [WellOrderedHom.Fibre, SmallFibresWithStructures.toSmallWO,
      SmallFibresWithStructures.toSSet, SmallFibresWithStructures.toHom,
      SimplexCategory.len_mk, Iso]
    erw [NatTrans.vcomp_app]
    exact (a.OutEquivFibre x.snd).2.symm
  mono {n y} b₁ b₂ h:= by
    simp [Fibre.trans, Iso]
    erw [LinearOrder.ofEquiv_le_iff_le, Equiv.symm_symm,
         LinearOrder.ofEquiv_le_iff_le, Equiv.symm_symm] at h
    convert h
    . exact b₁.2
    . exact OutEquivFibre_congr b₁.2 (cast_heq _ _).symm
    . exact b₂.2
    . exact OutEquivFibre_congr b₂.2 (cast_heq _ _).symm

lemma SmallFibresWithStructures.surj : Surjective (SmallFibresWithStructures.to α X) := by
  apply Quotient.ind
  intro a
  use a.toSmallFibresWithStructures
  dsimp [SmallFibresWithStructures.to]
  erw [Quotient.eq]
  exact ⟨SmallWO.toSmallFibresWithStructures.OrderIso a⟩

instance : Small.{u, u + 1} (Ω_obj₀ α X) :=
  @small_of_surjective _ _ inferInstance _ SmallFibresWithStructures.surj

end Smallness

end UniversalSimplicialSet

noncomputable section

-- in this section, we prove that the dependent products of
-- small-fibre hom along a small-fibre hom is small-fibre

variable (α : Cardinal.{u}) {X Y : SSet.{u}}

def Fibre.preimage_eq_sigma_fibre (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ} (S : Set (Y.obj n)) :
    f.app n ⁻¹' S ≃ Σ y : S, Fibre f y.val where
  toFun x := ⟨⟨f.app n x, x.2⟩, ⟨x, rfl⟩⟩
  invFun x := ⟨x.2.1, by
    have : f.app _ x.2.1 = x.1 := x.2.2
    simp [this]⟩
  left_inv x := by simp
  right_inv x := by ext; simp; exact x.2.2; rfl

def Fibre.equivOverHom (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ} (y : Y.obj n) :
    Fibre f y ≃ (Over.mk ((Y.yonedaEquiv _).symm y) ⟶ Over.mk f) where
  toFun x := by
    apply Over.homMk ((X.yonedaEquiv _).symm x.val) _
    simp; rw [← yonedaEquiv_symm_naturality_right', x.2]
  invFun g := ⟨(X.yonedaEquiv _) g.left, by
    simp; apply_fun (Y.yonedaEquiv (unop n)).symm
    rw [yonedaEquiv_symm_naturality_right']
    simpa using g.w⟩
  left_inv x := by simp
  right_inv g := by ext; simp

variable {α}

lemma SmallFibre.stableUnderPullback {f : X ⟶ Y} (h : SmallFibre α f) {Z W : SSet.{u}}
  {g : W ⟶ Y} {fst : Z ⟶ X} {snd : Z ⟶ W} (is : IsPullback fst snd f g) :
    SmallFibre α snd := by
  intro n y
  convert h (g.app _ y) using 1
  exact Quotient.sound ⟨is.FibreEquiv y⟩

section
variable [α.Infinite]

lemma lt_infinite_of_fintype {A : Type u} [Fintype A] :
    Cardinal.mk A < α := by
  apply lt_of_lt_of_le _ Cardinal.Infinite.le
  rw [Cardinal.lt_aleph0_iff_finite]
  apply Finite.of_fintype

instance {m n : SimplexCategory} : Fintype (m ⟶ n) := by
  simp [Quiver.Hom, SimplexCategory.Hom]
  apply Fintype.ofInjective _ DFunLike.coe_injective

variable {n : SimplexCategory} {m : SimplexCategoryᵒᵖ}

instance : Fintype ((standardSimplex.obj n).obj m) :=
  Fintype.ofEquiv _ (objEquiv n m).symm

lemma standardSimplex.lt_infinite :
    Cardinal.mk ((standardSimplex.obj n).obj m) < α :=
  lt_infinite_of_fintype

variable {X : SSet.{u}} (x : standardSimplex.obj n ⟶ X)

instance standardSimplex.finte_range :
    Fintype (range (x.app k)) := by
  apply Set.fintypeRange

lemma standardSimplex.range_lt {k : SimplexCategoryᵒᵖ}:
    Cardinal.mk (range (x.app k)) < α := by
  apply lt_infinite_of_fintype

lemma SmallFibre.simplex {n : SimplexCategory} (y : standardSimplex.obj n ⟶ Y) :
    SmallFibre α y := by
  intro k x
  let i : Fibre y x → (standardSimplex.obj n).obj k :=
    Subtype.val
  have hi : i.Injective := Subtype.val_injective
  have := Cardinal.mk_le_of_injective hi
  apply lt_of_le_of_lt this standardSimplex.lt_infinite

end

section

variable [α.Uncountable] [α.IsRegularClass] {X : SSet.{u}} (x : standardSimplex.obj n ⟶ X)

lemma standardSimplex.sigma_range_lt :
    Cardinal.mk (Σ k, range (x.app k)) < α := by
  rw [Cardinal.mk_sigma]
  apply Cardinal.sum_lt_lift_of_isRegular Cardinal.IsRegularClass.is
  have : Cardinal.lift.{u, 0} (Cardinal.mk SimplexCategoryᵒᵖ) = Cardinal.aleph 0 := by
    simp only [Cardinal.aleph_zero, Cardinal.lift_eq_aleph0]
    apply Cardinal.mk_congr
    apply Opposite.equivToOpposite.symm.trans
      (SimplexCategory.EquivNat.trans Equiv.ulift.{0,0}.symm)
  rw [this]
  apply lt_of_lt_of_le _ (Cardinal.Uncountable.le)
  simp only [Cardinal.aleph_lt_aleph, zero_lt_one]
  intro k; apply Cardinal.lt_uncountable_of_fintype

variable {Y : SSet.{u}} (f : Y ⟶ X)

lemma SmallFibre.preimage_range_lt (hf : SmallFibre α f) {k}:
    Cardinal.mk (f.app k ⁻¹' range (x.app k)) < α := by
  rw [Cardinal.mk_congr (Fibre.preimage_eq_sigma_fibre _ _), Cardinal.mk_sigma]
  apply Cardinal.sum_lt_lift_of_isRegular Cardinal.IsRegularClass.is
  rw [Cardinal.lift_id]; apply standardSimplex.range_lt
  intro k; exact hf _

lemma SmallFibre.preimage_sigma_range_lt (hf : SmallFibre α f):
    Cardinal.mk (Σ k, f.app k ⁻¹' range (x.app k)) < α := by
  rw [Cardinal.mk_sigma]
  apply Cardinal.sum_lt_lift_of_isRegular Cardinal.IsRegularClass.is
  rw [SimplexCategory.opposite_cardinal_eq_alphe0]
  apply lt_of_lt_of_le _ (Cardinal.Uncountable.le)
  simp only [Cardinal.lift_aleph0]
  rw [← Cardinal.aleph_zero, Cardinal.aleph_lt_aleph]
  simp only [zero_lt_one]
  intro; apply preimage_range_lt _ _ hf

def SmallFibre.over_hom_to_fun (g g' : Over Y) (φ : g ⟶ g') :
    ∀ k, ∀ y : f.app k ⁻¹' range (x.app k), Fibre g.hom y.val → Fibre g'.hom y.val :=
  fun _ _ ↦ Fibre.trans φ.left φ.w.symm _

open Limits in
lemma SmallFibre.over_hom_to_fun_inj (g : Over Y) :
    (over_hom_to_fun x f ((f*).obj (Over.mk x)) g).Injective := by
  intro φ φ' h
  ext k y
  let y' := ((f*).obj (Over.mk x)).hom.app _ y
  have aux₁ : y' ∈ f.app k ⁻¹' range (x.app k) := by
    simp [y']
    use (pullback.fst x f).app _ y
    change ((pullback.fst x f) ≫ x).app k y = _
    erw [pullback.condition, NatTrans.vcomp_app]
    simp
  let y'' : Fibre ((f*).obj (Over.mk x)).hom y' := ⟨y, rfl⟩
  have aux₂ (φ) : φ.left.app k y = (over_hom_to_fun x f _ g φ k ⟨y', aux₁⟩ y'').val := by
    simp [y'', y', over_hom_to_fun, Fibre.trans]
  rw [aux₂, aux₂, h]

end

section

open Cardinal

variable [α.IsRegularClass] [α.Uncountable] [α.IsStrongLimitClass]
  {X Y : SSet.{u}} {x : standardSimplex.obj n ⟶ X} {f : Y ⟶ X}

lemma SmallFibre.fibre_fun_lt (hf : SmallFibre α f) {g g' : Over Y}
  (hg : SmallFibre α g.hom) (hg' : SmallFibre α g'.hom) :
    #(∀ k, ∀ y : f.app k ⁻¹' range (x.app k),
      Fibre g.hom y.val → Fibre g'.hom y.val) < α := by

  -- make them lemma
  have aux₁ {k} {y : ↑(f.app k ⁻¹' range (x.app k))} :
      #(↑(Fibre g.hom y.val) → ↑(Fibre g'.hom y.val)) < α := by
    rw [← Cardinal.power_def]
    apply pow_lt_of_isStrongLimit IsStrongLimitClass.is (hg' _) (hg _)

  have aux₂ {k} : #((y : ↑(f.app k ⁻¹' range (x.app k))) →
    ↑(Fibre g.hom y.val) → ↑(Fibre g'.hom y.val)) < α := by
    rw [mk_pi]
    apply lt_of_le_of_lt
    apply prod_le_iSup_pow_of_le _ α
    . intro; exact aux₁.le
    . rw [lift_id]
      apply pow_lt_of_isStrongLimit IsStrongLimitClass.is
      . apply iSup_lt_lift_of_isRegular IsRegularClass.is
        rw [lift_id]; apply preimage_range_lt _ _ hf
        intro; apply aux₁
      . rw [lift_id]; apply preimage_range_lt _ _ hf

  rw [mk_pi]
  apply lt_of_le_of_lt
  apply prod_le_iSup_pow_of_le _ α
  . intro; exact aux₂.le
  . simp only [lift_uzero, SimplexCategory.opposite_cardinal_eq_alphe0, lift_aleph0, gt_iff_lt]
    apply pow_lt_of_isStrongLimit IsStrongLimitClass.is
    . apply iSup_lt_lift_of_isRegular IsRegularClass.is
      simp [SimplexCategory.opposite_cardinal_eq_alphe0]
      apply alpeh0_lt_of_uncountable
      intro; exact aux₂
    . apply alpeh0_lt_of_uncountable

lemma SmallFibre.over_hom_lt (hf : SmallFibre α f) {g : Over Y}
  (hg : SmallFibre α g.hom) :
    #((f*).obj (Over.mk x) ⟶ g) < α := by
  apply lt_of_le_of_lt (mk_le_of_injective (over_hom_to_fun_inj x f g))
  apply fibre_fun_lt hf _ hg
  apply stableUnderPullback (simplex _) (IsPullback.of_hasPullback _ _)

open LocallyCartesianClosed in
lemma SmallFibre.stableUnderPushforward {f : Over X} (hf : SmallFibre α f.hom) {g : X ⟶ Y}
  (hg : SmallFibre α g) :
    SmallFibre α ((Πg).obj f).hom := by
  intro n y
  rw [Cardinal.mk_congr ((Fibre.equivOverHom ((Πg).obj f).hom y).trans
        ((adj g).homEquiv _ f).symm)]
  apply over_hom_lt hg hf

end
end
