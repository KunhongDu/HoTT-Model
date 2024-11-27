import HoTTModel.SSet.Fibrations
import HoTTModel.SSet.Representables
import HoTTModel.Lemmas.OrderOfEquiv
import HoTTModel.Lemmas.IsWellOrder
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality

-- This file aims to construct a universe in sSet
open Simplicial CategoryTheory Opposite Limits Functor Set
universe u

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

namespace SSet
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

-- can't find: nonempty set in a well order has a least element
/-
lemma eq_iff_trans_eq_of_iso {f : X ⟶ Y} {f' : X' ⟶ Y} (F : Iso X X') {y : Y.obj n}
  (comm : f = F.hom ≫ f') (a b : Fibre f y):
    a = b ↔ Fibre.trans F.hom comm a = Fibre.trans F.hom comm b := by
  constructor
  exact fun h ↦ by rw [h]
  intro h -- this must be simplifiable
  apply_fun Fibre.trans (f := f') (f' := f) F.inv (by simp [comm]) at h
  simp [Fibre.trans] at h
  exact h-/

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
structure SmallWO (Y : SSet.{u}) where
  of : SSet.{u}
  wo : of ⟶ₒ Y
  small : ∀ ⦃n⦄, ∀ y : Y.obj n, Cardinal.mk (wo⁻¹ y) < α

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

variable (α Y) in
def Ω_obj := Shrink (Ω_obj₀ α Y)

def Ω_obj.mk (a : SmallWO α Y) : Ω_obj α Y :=
  equivShrink (Ω_obj₀ α Y) ⟦a⟧

def Ω_obj.out (a : Ω_obj α Y) : SmallWO α Y :=
  ((equivShrink (Ω_obj₀ α Y)).symm a).out

@[simp]
lemma Ω_obj.mk_out_eq (a : Ω_obj α Y) :
    mk a.out = a := by
  simp [mk, out]

lemma Ω_obj.out_mk_equiv (a : SmallWO α Y) :
    (mk a).out ≈ a := by
  simp only [out, mk, Equiv.symm_apply_apply, ← Quotient.eq_iff_equiv, Quotient.out_eq]

lemma Ω_obj.mk_eq_mk_iff_equiv (a b : SmallWO α Y) :
    Ω_obj.mk a = Ω_obj.mk b ↔ a ≈ b := by
  simp [mk, (equivShrink (Ω_obj₀ α Y)).apply_eq_iff_eq]; exact Quotient.eq

lemma Ω_obj.mk_sound {a b : SmallWO α Y} :
    a ≈ b → Ω_obj.mk a = Ω_obj.mk b := by
  intro h
  simp only [mk, (equivShrink (Ω_obj₀ α Y)).apply_eq_iff_eq]
  apply Quotient.sound h

-- define the functor, which acts on morphisms as pullback
noncomputable section map
variable (a : SmallWO α Y) (f : Y' ⟶ Y)

def SmallWO.pullback :
    SmallWO α Y' where
  of := Limits.pullback a.wo.hom f
  wo := {
    hom := pullback.snd a.wo.hom f
    ord := (IsPullback.of_hasPullback a.wo.hom f).FibreLinearOrder _
    isWellOrder := IsPullback.FibreLinearOrder.isWellOrder _ _
  }
  small n y := by
    convert a.small (f.app _ y) using 1
    exact Quotient.sound ⟨(IsPullback.of_hasPullback a.wo.hom f).FibreEquiv y⟩

def SmallWO.FibreOrderIsoCast {y y' : Y.obj n} (eq : y = y') :
    a.wo⁻¹ y ≃o a.wo⁻¹ y' :=
  RelIso.cast (by cases eq; rfl) (by cases eq; rfl)

@[simp]
lemma SmallWO.FibreOrderIsoCast_refl {y : Y.obj n} (x : a.wo⁻¹ y):
    a.FibreOrderIsoCast (Eq.refl y) x = x := rfl

lemma SmallWO.FibreOrderIsoCast_move {n m} {y y' : Y.obj n} (eq : y = y') (φ : n ⟶ m)
  (x : a.wo⁻¹ y) (h : Y.map φ y = Y.map φ y'):
    a.FibreOrderIsoCast h (move φ x) = move φ (a.FibreOrderIsoCast eq x) := by
  cases eq; rfl

-- RelIso on fibres via pullback
def SmallWO.pullback_RelIso' {n} (y' : Y'.obj n):
    (a.pullback f).wo⁻¹ y' ≃o a.wo⁻¹ (f.app _ y') :=
  IsPullback.FibreLinearOrder.OrderIso _ y'

def SmallWO.pullback_RelIso {n} (y : Y.obj n) (y' : Y'.obj n)
  (h : f.app _ y' = y) :
    (a.pullback f).wo⁻¹ y' ≃o a.wo⁻¹ y :=
  (a.pullback_RelIso' f y').trans (a.FibreOrderIsoCast h)

lemma SmallWO.pullback_RelIso_move {n m} (y : Y.obj n) (y' : Y'.obj n) (h : f.app _ y' = y)
  (φ : n ⟶ m) (x : (a.pullback f).wo⁻¹ y') (h'):
    a.pullback_RelIso f (Y.map φ y) (Y'.map φ y') h' (move φ x) =
  move φ (a.pullback_RelIso f y y' h x) := by
    cases h
    simp [pullback_RelIso, pullback_RelIso', IsPullback.FibreEquiv, FibreOrderIsoCast,
          IsPullback.PreimageEquiv, move, hom_naturality_apply]

lemma SmallWO.pullback_RelIso_symm_move {n m} (y : Y.obj n) (y' : Y'.obj n)
  (h : f.app _ y' = y) (φ : n ⟶ m) (x : a.wo⁻¹ y) {h'}:
    (a.pullback_RelIso f (Y.map φ y) (Y'.map φ y') h').symm (move φ x) =
  move φ ((a.pullback_RelIso f y y' h).symm x) := by
    apply_fun (a.pullback_RelIso f (Y.map φ y) (Y'.map φ y') h')
    rw [a.pullback_RelIso_move _ _ _ h]
    simp only [OrderIso.apply_symm_apply]

lemma SmallWO.pullback_RelIso'_move {n m} (y' : Y'.obj n) (φ : n ⟶ m)
  (x : (a.pullback f).wo⁻¹ y') :
    a.pullback_RelIso' f (Y'.map φ y') (move φ x) =
      (a.FibreOrderIsoCast (hom_naturality_apply _ _ _).symm) (move φ
        (a.pullback_RelIso f (f.app _ y') y' rfl x)) := by
  simp [pullback_RelIso, pullback_RelIso', IsPullback.FibreEquiv, FibreOrderIsoCast,
          IsPullback.PreimageEquiv, move, hom_naturality_apply]

lemma SmallWO.pullback_id :
    a.pullback (𝟙 Y) ≈ a := by
  have : IsIso (pullback.fst a.hom (𝟙 Y)) := by
    rw [← (IsPullback.of_hasPullback a.hom (𝟙 Y)).isoIsPullback_hom_fst _ _
      (IsPullback.id_horiz a.hom)]
    infer_instance
  exact ⟨{
    toIso := asIso (pullback.fst a.wo.hom (𝟙 Y))
    comm := by simp [pullback.condition]; rfl
    mono := by
      intro _ y _ _ h
      rwa [IsPullback.FibreLinearOrder.le_iff_le] at h
  }⟩

open IsPullback in
lemma SmallWO.pullback_comp {f : Z ⟶ Y} {g : W ⟶ Z} :
    (a.pullback f).pullback g ≈ a.pullback (g ≫ f):= by
  let is := IsPullback.of_hasPullback a.hom (g ≫ f)
  let is' := IsPullback.paste_horiz (IsPullback.of_hasPullback (pullback.snd a.hom f) g)
    (IsPullback.of_hasPullback a.hom f)
  exact ⟨{
    toIso := is'.isoIsPullback _ _ is
    comm := by erw [IsPullback.isoIsPullback_hom_snd]; rfl
    mono := by
      intro n y b c h
      rw [FibreLinearOrder.le_iff_le, FibreLinearOrder.le_iff_le] at h
      rw [FibreLinearOrder.le_iff_le]
      convert h using 1
      all_goals
      simp [IsPullback.FibreEquiv, PreimageEquiv, OrderIso.trans,
            Fibre.trans]
      change (_ ∘ _) _ = (_ ∘ _) _
      rw [← types_comp, ← types_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
          IsPullback.isoIsPullback_hom_fst]
      rfl
  }⟩

variable {f} in
open IsPullback in
lemma SmallWO.pullback_sound {a b : SmallWO α Y} :
    a ≈ b → a.pullback f ≈ b.pullback f
| ⟨h⟩ => ⟨{
    toIso := asIso (pullback.map a.hom f b.hom f h.hom (𝟙 _) (𝟙 _)
      (by simp [h.comm]) (by simp))
    comm := by simp; erw [pullback.lift_snd, Category.comp_id]; rfl
    mono := by
      intro n y c d hcd
      rw [FibreLinearOrder.le_iff_le, h.le_iff_le] at hcd
      rw [FibreLinearOrder.le_iff_le]
      convert hcd
      all_goals
      simp [IsPullback.FibreEquiv, PreimageEquiv, OrderIso.trans,
            Fibre.trans]
      change (_ ∘ _) _ = (_ ∘ _) _
      rw [← types_comp, ← types_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
          pullback.lift_fst]
  }⟩

variable (α) in
def Ω_map : Ω_obj α Y ⟶ Ω_obj α Y' :=
  Shrink.rec (Quotient.lift (Ω_obj.mk ∘ fun a ↦ a.pullback f)
    (fun _ _ h ↦ Ω_obj.mk_sound (SmallWO.pullback_sound h)))

@[simp]
lemma Ω_map.mk_eq :
  Ω_map α f (Ω_obj.mk a) =  Ω_obj.mk (a.pullback f) := by
    simp only [Ω_obj.mk, Ω_map, Shrink.rec, Equiv.symm_apply_apply, eq_rec_constant]
    erw [Quotient.lift_mk, Function.comp_apply]
    rfl

lemma Ω_map_id : Ω_map α (𝟙 Y) = 𝟙 (Ω_obj α Y) := by
  ext a; revert a
  apply Shrink.rec; apply Quotient.ind
  intro a
  simp only [types_id_apply, EmbeddingLike.apply_eq_iff_eq]
  erw [Ω_map.mk_eq]
  exact Ω_obj.mk_sound (SmallWO.pullback_id _)

lemma Ω_map_comp {f : Y ⟶ Y'} {g : Y' ⟶ Y''}:
    (Ω_map α g) ≫ (Ω_map α f) = Ω_map α (f ≫ g) := by
  ext a; revert a
  apply Shrink.rec; apply Quotient.ind
  intro a
  simp only [types_comp_apply, EmbeddingLike.apply_eq_iff_eq]
  erw [Ω_map.mk_eq, Ω_map.mk_eq, Ω_map.mk_eq]
  apply Ω_obj.mk_sound a.pullback_comp

namespace Ω_map

variable (f : Y' ⟶ Y) (a : Ω_obj α Y) (y : Y.obj n) (y' : Y'.obj n)
  (h : f.app _ y' = y)

def out_equiv :
    ∀ a : Ω_obj α Y,  (Ω_map α f a).out ≈ a.out.pullback f := by
  apply Shrink.rec; apply Quotient.ind
  intro a; erw [Ω_map.mk_eq]
  exact Setoid.trans (Ω_obj.out_mk_equiv (a.pullback f))
    (SmallWO.pullback_sound (Setoid.symm (Ω_obj.out_mk_equiv _)))

def outOrderIso :
    OrderIso (Ω_map α f a).out.wo (a.out.pullback f).wo :=
  Classical.choice (out_equiv f a)

def outOrderIsoFibre :
    (Ω_map α f a).out.wo⁻¹ y' ≃o (a.out.pullback f).wo⁻¹ y' :=
  OrderIso.FibreOrderIso (outOrderIso f a) _

def FibreOrderIso :
    (Ω_map α f a).out.wo⁻¹ y' ≃o a.out.wo⁻¹ y :=
  (outOrderIsoFibre f a y').trans (a.out.pullback_RelIso f y y' h)

def FibreOrderIsoCast (f : Y' ⟶ Y) (a : Ω_obj α Y) (b : Ω_obj α Y')
  (h : Ω_map α f a = b) {n} (y : Y.obj n) (y' : Y'.obj n)
  (h' : f.app _ y' = y) :
    a.out.wo⁻¹ y ≃o b.out.wo⁻¹ y' :=
  (FibreOrderIso f a y y' h').symm.trans (RelIso.cast (by cases h; rfl) (by cases h; rfl))

lemma FibreOrderIsoCast_move (f : Y' ⟶ Y) (a : Ω_obj α Y) (b : Ω_obj α Y')
  (h : Ω_map α f a = b) (y : Y.obj n) (y' : Y'.obj n) (h' : f.app _ y' = y)
  (φ : n ⟶ m) (h'') (z : a.out.wo⁻¹ y) :
    FibreOrderIsoCast f a b h (φ ~ y) (φ ~ y') h'' (move φ z) =
      move φ (FibreOrderIsoCast f a b h y y' h' z) := by
  ext
  cases h; cases h'
  simp [FibreOrderIsoCast, FibreOrderIso, outOrderIsoFibre]
  rw [SmallWO.pullback_RelIso_symm_move, OrderIso.FibreOrderIso_symm_move]

lemma FibreOrderIsoCast_symm_move (f : Y' ⟶ Y) (a : Ω_obj α Y) (b : Ω_obj α Y')
  (h : Ω_map α f a = b) (y : Y.obj n) (y' : Y'.obj n) (h' : f.app _ y' = y)
  (φ : n ⟶ m) (h'') (z : b.out.wo⁻¹ y') :
    (FibreOrderIsoCast f a b h (φ ~ y) (φ ~ y') h'').symm (move φ z) =
      move φ ((FibreOrderIsoCast f a b h y y' h').symm z) := by
  apply_fun (FibreOrderIsoCast f a b h (φ ~ y) (φ ~ y') h'')
  rw [FibreOrderIsoCast_move (h' := h')]
  simp only [OrderIso.apply_symm_apply]

end Ω_map

end map

variable (α)

def Ω : SSetᵒᵖ ⥤ Type u where
  obj Y := Ω_obj α (unop Y)
  map f := Ω_map α (unop f)
  map_id Y := by simp; rw [← Ω_map_id]; rfl
  map_comp f g:= by simp; rw [Ω_map_comp]; rfl

section

variable [UnivLE.{v, u}] {J : Type v} [Category.{w,v} J] {F : J ⥤ SSet.{u}ᵒᵖ}
  (c : Cone F) (hc : IsLimit c)

namespace Ω.PreservesLimit

open Function Classical

-- view `c.pt.unop` as the limit of `F`

/--
  Morphism from `(Ω α).mapCone c` to the limit cone of `F ⋙ Ω α`.
  Will show this is an isomorphism so that `(Ω α).mapCone c` is a limit cone.
-/
abbrev HomToLimit :
    (Ω α).mapCone c ⟶ limit.cone (F ⋙ Ω α) where
  hom := limit.lift _ _
  w := limit.lift_π _

lemma HomToLimit_hom_π (f : Ω_obj α c.pt.unop) (j : J) :
    limit.π (F ⋙ Ω α) j (limit.lift (F ⋙ Ω α) ((Ω α).mapCone c) f) =
      (Ω α).map (c.π.app j) f :=
  congrFun (limit.lift_π ((Ω α).mapCone c) j) _

variable {α c}

/--
  For any two SmallWO `f,g` over `lim F`,
  if their pullbacks along `F j` are isomorphic,
  then we can construct `OrderIso` between any corresponded fibres
  as compositions of three `OrderIso`s.
-/
def FibreOrderIsoOfPullback (f g : SmallWO α c.pt.unop)
  (h : (j : J) → (OrderIso (f.pullback (c.π.app j).unop).wo (g.pullback (c.π.app j).unop).wo))
  {n : SimplexCategoryᵒᵖ} (y : c.pt.unop.obj n)
  (j : J) (x : (F.obj j).unop.obj n) (hx : (c.π.app j).unop.app _ x = y):
    f.wo⁻¹ y ≃o g.wo⁻¹ y := by
  let r₁ := f.pullback_RelIso (c.π.app j).unop y x hx
  let r₂ := (h j).FibreOrderIso x
  let r₃ := g.pullback_RelIso (c.π.app j).unop y x hx
  exact (r₁.symm.trans r₂).trans r₃

omit [UnivLE.{v, u}] in
/--
  By the virtue of well-order, `FibreOrderIso` is indepdent of the choice of `j` and `x`.
-/
lemma FibreOrderIsoOfPullback_ext {f g : SmallWO α c.pt.unop}
  {h : (j : J) → (OrderIso (f.pullback (c.π.app j).unop).wo (g.pullback (c.π.app j).unop).wo)}
  {n : SimplexCategoryᵒᵖ} {y : (unop c.pt).obj n}
  (j : J) (x : (F.obj j).unop.obj n) (hx : (c.π.app j).unop.app _ x = y)
  (j' : J) (x' : (F.obj j').unop.obj n) (hx' : (c.π.app j').unop.app _ x' = y) :
    FibreOrderIsoOfPullback f g h y j x hx = FibreOrderIsoOfPullback f g h y j' x' hx' :=
  IsWellOrder.OrderIso_ext _ _

lemma jointly_surjective (hc : IsLimit c) (y : c.pt.unop.obj n) :
  ∃ (j : J) (x : (F.obj j).unop.obj n), (c.π.app j).unop.app _ x = y := by
    have : IsColimit $ (ev n).mapCocone (coconeLeftOpOfCone c) :=
      PreservesColimit.preserves (isColimitCoconeLeftOpOfCone _ hc)
    obtain ⟨j, ⟨x, h⟩⟩ := Types.jointly_surjective (F ⋙ (ev n).op).leftOp this y
    exact ⟨j.unop, ⟨x, h⟩⟩

def choose_j (y : c.pt.unop.obj n) : J :=
  choose (jointly_surjective hc y)

lemma choose_spec_j (y : c.pt.unop.obj n) :
    ∃ x : (F.obj (choose_j hc y)).unop.obj n, (c.π.app _).unop.app _ x = y :=
  choose_spec (jointly_surjective hc y)

def choose_x (y : c.pt.unop.obj n) : (F.obj (choose_j hc y)).unop.obj n :=
  choose (choose_spec_j hc y)

lemma choose_spec_x (y : c.pt.unop.obj n) :
    (c.π.app _).unop.app _ (choose_x hc y) = y :=
  choose_spec (choose_spec_j hc y)

/--
  `FibreOrderIso` where `j` and `x` are given by `jointly_surjective`
-/
def FibreOrderIsoOfPullbackChoose (f g : SmallWO α c.pt.unop)
  (h : (j : J) → (OrderIso (f.pullback (c.π.app j).unop).wo (g.pullback (c.π.app j).unop).wo))
  {n : SimplexCategoryᵒᵖ} (y : (unop c.pt).obj n) :
    f.wo⁻¹ y ≃o g.wo⁻¹ y :=
  FibreOrderIsoOfPullback f g h y (choose_j hc y) (choose_x hc y) (choose_spec_x hc y)

def PiecesOfPullbackOrderIso (f g : SmallWO α c.pt.unop)
  (h : (j : J) → (OrderIso (f.pullback (c.π.app j).unop).wo (g.pullback (c.π.app j).unop).wo)):
    Pieces f.wo g.wo where
  orderIso := FibreOrderIsoOfPullbackChoose hc f g h
  compatible := by
    intro n m φ y y'
    let j := choose_j hc y
    let x := choose_x hc y
    let x₂ := (F.obj j).unop.map φ x
    have hx₂ : (c.π.app j).unop.app m x₂ = c.pt.unop.map φ y := by
      change ((F.obj j).unop.map φ ≫ (c.π.app j).unop.app m) x = _
      rw [(c.π.app j).unop.naturality, ← choose_spec_x hc y]; rfl
    dsimp [FibreOrderIsoOfPullbackChoose]
    rw [FibreOrderIsoOfPullback_ext _ _ _ (choose_j hc y) x₂ hx₂]
    dsimp [FibreOrderIsoOfPullback]
    rw [f.pullback_RelIso_symm_move _ _ _ (choose_spec_x hc y), OrderIso.FibreOrderIso_move,
        g.pullback_RelIso_move]

def OrderIsoOfPullbackOrderIso (f g : SmallWO α c.pt.unop)
  (h : ∀ j : J, f.pullback (c.π.app j).unop ≈ g.pullback (c.π.app j).unop) :
    OrderIso f.wo g.wo :=
  (PiecesOfPullbackOrderIso hc f g (fun j ↦ choice (h j))).toOrderIso

variable (c) in
lemma HomToLimit_hom_injective (hc : IsLimit c):
    (limit.lift (F ⋙ Ω α) ((Ω α).mapCone c)).Injective := by
  apply Shrink.rec; apply Quotient.ind; intro f
  apply Shrink.rec; apply Quotient.ind; intro g h
  have (j) := congrArg (limit.π (F ⋙ Ω α) j) h
  simp [HomToLimit_hom_π] at this
  refine Ω_obj.mk_sound ⟨OrderIsoOfPullbackOrderIso hc f g ?_⟩
  intro j; specialize this j
  change (Ω α).map (c.π.app j) (Ω_obj.mk _) = (Ω α).map (c.π.app j) (Ω_obj.mk _) at this
  simp [Ω, Ω_obj.mk_eq_mk_iff_equiv] at this
  exact this

variable (c) (f : limit (F ⋙ Ω α))

def FibreOrderIsoOfExists {j j' : J} (x : (F.obj j).unop.obj n) (x' : (F.obj j').unop.obj n)
  (φ : j' ⟶ j) (hφ : x' = (F.map φ).unop.app _ x):
    ((limit.π (F ⋙ Ω α) j) f).out.wo⁻¹ x ≃o ((limit.π (F ⋙ Ω α) j') f).out.wo⁻¹ x' :=
  (Ω_map.FibreOrderIsoCast (F.map φ).unop ((limit.π (F ⋙ Ω α) j') f)
    ((limit.π (F ⋙ Ω α) j) f) (congrFun (limit.w (F ⋙ Ω α) φ) f) x' x hφ.symm).symm

open Types in
lemma eqvGen_of_app_eq (hc : IsLimit c) {j j' : J} (x : (F.obj j).unop.obj n)
  (x' : (F.obj j').unop.obj n) (h : (c.π.app j).unop.app _ x = (c.π.app j').unop.app _ x') :
    Relation.EqvGen (Quot.Rel (F.leftOp ⋙ ev n)) ⟨op j, x⟩ ⟨op j', x'⟩ := by
  have : IsColimit $ (ev n).mapCocone (coconeLeftOpOfCone c) :=
      PreservesColimit.preserves (isColimitCoconeLeftOpOfCone _ hc)
  apply isColimit_eq _ this h

open Types in
lemma nonempty_OrderIso_of_eqvGen {n : SimplexCategoryᵒᵖ}
  {p₁ p₂ : Σ j : Jᵒᵖ, (F.obj j.unop).unop.obj n}
  (h : Relation.EqvGen (Quot.Rel (F.leftOp ⋙ ev n)) p₁ p₂) :
    Nonempty (((limit.π (F ⋙ Ω α) p₁.fst.unop) f).out.wo⁻¹ p₁.snd ≃o
      ((limit.π (F ⋙ Ω α) p₂.fst.unop) f).out.wo⁻¹ p₂.snd) := by
  induction h with
  | rel _ _ h =>
      obtain ⟨φ, hφ⟩ := h
      exact ⟨FibreOrderIsoOfExists _ _ _ φ.unop hφ⟩
  | refl _ => exact ⟨OrderIso.refl _⟩
  | symm _ _ _ ih =>
      obtain ⟨r⟩ := ih
      exact ⟨r.symm⟩
  | trans _ _ _ _ _ ih₁ ih₂ =>
      obtain ⟨r₁⟩ := ih₁
      obtain ⟨r₂⟩ := ih₂
      exact ⟨r₁.trans r₂⟩

variable (f : limit (F ⋙ Ω α))

def FibreOrderIsoOfAppEq {j j' : J} (x : (F.obj j).unop.obj n) (x' : (F.obj j').unop.obj n)
  (h : (c.π.app j).unop.app _ x = (c.π.app j').unop.app _ x') :
    ((limit.π (F ⋙ Ω α) j) f).out.wo⁻¹ x ≃o ((limit.π (F ⋙ Ω α) j') f).out.wo⁻¹ x' := by
  /-
  (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
  Use `set_option maxHeartbeats <num>` to set the limit.
  Additional diagnostic information may be available using the `set_option diagnostics true` command.
  -/
  let r := choice (nonempty_OrderIso_of_eqvGen f (eqvGen_of_app_eq c hc x x' h))
  dsimp at r
  exact r

lemma FibreOrderIsoOfAppEq_symm_eq {j j' : J} (x : (F.obj j).unop.obj n)
  (x' : (F.obj j').unop.obj n) (h : (c.π.app j).unop.app _ x = (c.π.app j').unop.app _ x') :
    (FibreOrderIsoOfAppEq c hc f x x' h).symm = FibreOrderIsoOfAppEq c hc f x' x h.symm :=
  IsWellOrder.OrderIso_ext _ _

lemma FibreOrderIsoOfAppEq_swap_apply_apply {j j' : J} (x : (F.obj j).unop.obj n)
  (x' : (F.obj j').unop.obj n) (h : (c.π.app j).unop.app _ x = (c.π.app j').unop.app _ x')
  (t : _) :
    (FibreOrderIsoOfAppEq c hc f x x' h) (FibreOrderIsoOfAppEq c hc f x' x h.symm t) = t := by
  change ((FibreOrderIsoOfAppEq c hc f x' x h.symm).trans
    (FibreOrderIsoOfAppEq c hc f x x' h)) t = t
  rw [IsWellOrder.OrderIso_apply_eq (g := OrderIso.refl _) t]
  rfl

lemma FibreOrderIsoOfAppEq_congr {j j' k k' : J}
  (x : (F.obj j).unop.obj n) (x' : (F.obj j').unop.obj n)
  (y : (F.obj k).unop.obj n) (y' : (F.obj k').unop.obj n)
  {hx : (c.π.app j).unop.app _ x = (c.π.app j').unop.app _ x'}
  {hy : (c.π.app k).unop.app _ y = (c.π.app k').unop.app _ y'}
  (eq₁ : j = k) (eq₂ : j' = k') (heq₁ : HEq x y) (heq₂ : HEq x' y')
  (z : ((limit.π (F ⋙ Ω α) j) f).out.wo⁻¹ x)
  (z' : ((limit.π (F ⋙ Ω α) k) f).out.wo⁻¹ y) (heq₃ : HEq z z') :
    HEq (FibreOrderIsoOfAppEq c hc f x x' hx z) (FibreOrderIsoOfAppEq c hc f y y' hy z') := by
  cases eq₁; cases eq₂; cases heq₁; cases heq₂; cases heq₃
  rfl

lemma FibreOrderIsoOfAppEq_symm_congr {j j' k k' : J}
  (x : (F.obj j).unop.obj n) (x' : (F.obj j').unop.obj n)
  (y : (F.obj k).unop.obj n) (y' : (F.obj k').unop.obj n)
  {hx : (c.π.app j).unop.app _ x = (c.π.app j').unop.app _ x'}
  {hy : (c.π.app k).unop.app _ y = (c.π.app k').unop.app _ y'}
  (eq₁ : j = k) (eq₂ : j' = k') (heq₁ : HEq x y) (heq₂ : HEq x' y')
  (z : ((limit.π (F ⋙ Ω α) j') f).out.wo⁻¹ x')
  (z' : ((limit.π (F ⋙ Ω α) k') f).out.wo⁻¹ y') (heq₃ : HEq z z') :
    HEq ((FibreOrderIsoOfAppEq c hc f x x' hx).symm z)
      ((FibreOrderIsoOfAppEq c hc f y y' hy).symm z') := by
  cases eq₁; cases eq₂; cases heq₁; cases heq₂; cases heq₃
  rfl

lemma FibreOrderIsoOfAppEq_move' (p₁ p₂ : Σ j : Jᵒᵖ, (F.obj j.unop).unop.obj n)
  (φ : n ⟶ m) (h) (h') (t : ((limit.π (F ⋙ Ω α) _) f).out.wo⁻¹ p₁.snd) :
    FibreOrderIsoOfAppEq c hc f (φ ~ p₁.snd) (φ ~ p₂.snd) h' (move φ t) =
      move φ (FibreOrderIsoOfAppEq c hc f p₁.snd p₂.snd h t) := by
  have : Relation.EqvGen (Types.Quot.Rel (F.leftOp ⋙ ev n)) p₁ p₂
    := eqvGen_of_app_eq c hc _ _ h
  induction this with
  | rel x y ih =>
      obtain ⟨g, hg⟩ := ih
      let s₁ := FibreOrderIsoOfExists f x.snd y.snd g.unop hg
      let s₂ := FibreOrderIsoOfExists f (φ ~ x.snd) (φ ~ y.snd) g.unop
        (by rw [hom_naturality_apply', hg]; rfl)
      rw [IsWellOrder.OrderIso_apply_eq (g := s₁),
          IsWellOrder.OrderIso_apply_eq (g := s₂)]
      apply Ω_map.FibreOrderIsoCast_symm_move
  | refl x =>
      rw [IsWellOrder.OrderIso_apply_eq (g := OrderIso.refl _),
          IsWellOrder.OrderIso_apply_eq (g := OrderIso.refl _) t]
      rfl
  | symm x y _ ih =>
      specialize ih h.symm h'.symm
      apply_fun (FibreOrderIsoOfAppEq c hc f (φ ~ y.snd) (φ ~ x.snd) h').symm
      simp
      rw [FibreOrderIsoOfAppEq_symm_eq, ih, FibreOrderIsoOfAppEq_swap_apply_apply]
  | trans x y z r₁ r₂ ih₁ ih₂ =>
      have hxy : (c.π.app (unop x.fst)).unop.app _ x.snd =
        (c.π.app (unop y.fst)).unop.app _ y.snd :=
          Types.app_eq_of_eqvGen ((ev n).mapCocone (coconeLeftOpOfCone c)) _ _ r₁
      have hxy' : (c.π.app (unop x.fst)).unop.app _ (φ ~ x.snd) =
        (c.π.app (unop y.fst)).unop.app _ (φ ~ y.snd) := by
          rw [hom_naturality_apply', hom_naturality_apply', hxy]; rfl
      specialize ih₁ hxy hxy'
      specialize ih₂ (hxy.symm.trans h) (hxy'.symm.trans h')
      let s₁ := (FibreOrderIsoOfAppEq c hc f (φ ~ x.snd) (φ ~ y.snd) hxy').trans
        (FibreOrderIsoOfAppEq c hc f (φ ~ y.snd) (φ ~ z.snd) (hxy'.symm.trans h'))
      rw [IsWellOrder.OrderIso_apply_eq (g := s₁)]; dsimp [s₁]
      rw [ih₁, ih₂]
      change move φ ((FibreOrderIsoOfAppEq c hc f x.snd y.snd hxy).trans _ _) = _
      rw [IsWellOrder.OrderIso_apply_eq]

lemma FibreOrderIsoOfAppEq_move {j j' : J} (x : (F.obj j).unop.obj n)
  (x' : (F.obj j').unop.obj n) (h : (c.π.app j).unop.app _ x = (c.π.app j').unop.app _ x')
  (φ : n ⟶ m) (h') (t : ((limit.π (F ⋙ Ω α) j) f).out.wo⁻¹ x) :
    FibreOrderIsoOfAppEq c hc f (φ ~ x) (φ ~ x') h' (move φ t) =
      move φ (FibreOrderIsoOfAppEq c hc f x x' h t) := by
  apply FibreOrderIsoOfAppEq_move' c hc f ⟨op j, x⟩ ⟨op j', x'⟩

def LimitToSSet :
    SSet.{u} where
  obj n :=
    (y : c.pt.unop.obj n) × (((limit.π (F ⋙ Ω α) (choose_j hc y)) f).out.wo⁻¹ (choose_x hc y))
  map {n m} φ := by
    intro z
    let H := FibreOrderIsoOfAppEq c hc f (choose_x hc (φ ~ z.fst)) (φ ~ choose_x hc z.fst)
      (by rw [hom_naturality_apply, choose_spec_x, choose_spec_x]; rfl)
    exact ⟨c.pt.unop.map φ z.fst, H.symm (move φ z.snd)⟩
  map_id n := by
    dsimp; ext z
    . simp
    . simp
      have heq (hx) := FibreOrderIsoOfAppEq_symm_congr c hc f (choose_x hc (𝟙 n ~ z.fst))
        (𝟙 n ~ choose_x hc z.fst) (choose_x hc z.fst) (choose_x hc z.fst) (hx := hx) (hy := rfl)
        (by simp) (by simp) (by congr; simp) (by simp) (move (𝟙 n) z.snd) z.snd
        (by simp [move, Subtype.heq_iff_coe_eq])
      apply HEq.trans (heq _)
      rw [IsWellOrder.OrderIso_apply_eq (g := OrderIso.refl _)]
      rfl
  map_comp {n m k} φ ψ := by
    dsimp; ext z
    . simp
    . cases z with
    | mk z y =>
      have heq₁ (h) := FibreOrderIsoOfAppEq_symm_congr c hc f (choose_x hc ((φ ≫ ψ) ~ z))
        ((φ ≫ ψ) ~ choose_x hc z) (choose_x hc (ψ ~ (unop c.pt).map φ z))
        ((φ ≫ ψ) ~ choose_x hc z) (hx := h)
        (hy := by rw [hom_naturality_apply', choose_spec_x, choose_spec_x]; simp)
        (by simp) (by simp) (by congr 1; simp) (by simp)
        (move (φ ≫ ψ) y) (move (φ ≫ ψ) y) (by rfl)
      apply HEq.trans (heq₁ _)
      simp [heq_eq_eq]
      let r₁ := FibreOrderIsoOfAppEq c hc f ((φ ≫ ψ) ~ choose_x hc z) (ψ ~ choose_x hc (φ ~ z))
        (by rw [hom_naturality_apply', hom_naturality_apply', choose_spec_x, choose_spec_x]; simp)
      let r₂ := FibreOrderIsoOfAppEq c hc f (ψ ~ choose_x hc (φ ~ z)) (choose_x hc (ψ ~ (φ ~ z)))
        (by rw [hom_naturality_apply', choose_spec_x, choose_spec_x]; rfl)
      rw [IsWellOrder.OrderIso_apply_eq (g := r₁.trans r₂), IsWellOrder.OrderIso_apply_eq (g := r₂)]
      have heq₂ (h) := FibreOrderIsoOfAppEq_congr c hc f ((φ ≫ ψ) ~ choose_x hc z)
        (ψ ~ choose_x hc (φ ~ z)) (ψ ~ (φ ~ choose_x hc z)) (ψ ~ choose_x hc (φ ~ z)) (hx := h)
        (hy := by rw [hom_naturality_apply', hom_naturality_apply', hom_naturality_apply',
          choose_spec_x, choose_spec_x]; rfl)
        (by simp) (by simp) (by simp) (by simp)
        (move (φ ≫ ψ) y) (move ψ (move φ y)) move_comp_heq
      simp at heq₂; dsimp [r₁]
      rw [heq₂, FibreOrderIsoOfAppEq_move, FibreOrderIsoOfAppEq_symm_eq]
      rw [hom_naturality_apply', hom_naturality_apply', hom_naturality_apply',
          choose_spec_x, choose_spec_x]

def LimitToHom :
    LimitToSSet c hc f ⟶ c.pt.unop where
  app _ := Sigma.fst
  naturality := by
    intro n m φ
    ext a; simp [LimitToSSet]

def LimitToHomFibreEquiv (y : c.pt.unop.obj n) :
  ((limit.π (F ⋙ Ω α) (choose_j hc y)) f).out.wo⁻¹ (choose_x hc y)
      ≃ Fibre (LimitToHom c hc f) y :=
  Sigma.EquivFstPreimage _
    (fun y ↦ ((limit.π (F ⋙ Ω α) (choose_j hc y)) f).out.wo⁻¹ (choose_x hc y)) y

instance : LinearOrder ↑(Fibre (LimitToHom c hc f) y) :=
  LinearOrder.ofEquiv (LimitToHomFibreEquiv c hc f _)

def LimitToSmallWO :
    SmallWO α c.pt.unop where
  of := LimitToSSet c hc f
  wo := {
    hom := LimitToHom c hc f
    ord := inferInstance
    isWellOrder := LinearOrder.ofEquiv.isWellOrderOfIsWellOrder _ inferInstance
  }
  small {n y} := by
    erw [Cardinal.mk_congr (LimitToHomFibreEquiv c hc f y).symm]
    apply SmallWO.small

def LimitToSmallWOFibreEquiv (y : c.pt.unop.obj n) :
  ((limit.π (F ⋙ Ω α) (choose_j hc y)) f).out.wo⁻¹ (choose_x hc y)
      ≃o (LimitToSmallWO c hc f).wo⁻¹ y :=
  (LinearOrder.ofEquiv.OrderIso (LimitToHomFibreEquiv c hc f y))

open LinearOrder in
lemma LimitToSmallWO.move_eq (y : c.pt.unop.obj n) (x : (LimitToSmallWO c hc f).wo⁻¹ y)
  (φ : n ⟶ m):
    let r := LimitToSmallWOFibreEquiv c hc f y;
    let s₁ := LimitToSmallWOFibreEquiv c hc f (φ ~ y);
    let s₂ := FibreOrderIsoOfAppEq c hc f (choose_x hc (φ ~ y)) (φ ~ choose_x hc y)
      (by rw [hom_naturality_apply', choose_spec_x, choose_spec_x]; rfl);
      s₂ (s₁.symm (move φ x)) = move φ (r.symm x) := by
  ext
  cases x with
  | mk x hx =>
    cases x with
    | mk x z =>
      have : y = x := by
        simp only [WellOrderedHom.Fibre, Fibre, LimitToSmallWO, LimitToHom,
          Set.preimage, Set.mem_singleton] at hx
        exact eq_of_mem_singleton hx.symm
      cases this
      simp [move, LimitToSmallWOFibreEquiv]
      rw [ofEquiv.OrderIso_symm_apply, ofEquiv.OrderIso_symm_apply]
      simp [LimitToHomFibreEquiv, Sigma.EquivFstPreimage, LimitToSmallWO, LimitToSSet]
      rfl

def LimitToSmallWOOrderIso (y y') (h : (c.π.app j).unop.app n y = y'):
    (LimitToSmallWO c hc f).wo⁻¹ y' ≃o (limit.π (F ⋙ Ω α) j f).out.wo⁻¹ y := by
  let r := LimitToSmallWOFibreEquiv c hc f ((c.π.app j).unop.app n y)
  let r' := FibreOrderIsoOfAppEq c hc f _ y (choose_spec_x hc ((c.π.app j).unop.app n y))
  exact (SmallWO.FibreOrderIsoCast _ h.symm).trans (r.symm.trans r')

lemma LimitToSmallWOOrderIso_move (y : (F.obj j).unop.obj n)
  (y' : c.pt.unop.obj n) (h : (c.π.app j).unop.app n y = y') (φ : n ⟶ m)
  (x : ((LimitToSmallWO c hc f).wo⁻¹ y')) (h'):
    LimitToSmallWOOrderIso c hc f (φ ~ y) (φ ~ y') h' (move φ x) =
      move φ (LimitToSmallWOOrderIso c hc f y y' h x) := by
  cases h
  dsimp [LimitToSmallWOOrderIso]
  let r₁ := (LimitToSmallWO c hc f).FibreOrderIsoCast h'.symm
  let r₂ := LimitToSmallWOFibreEquiv c hc f ((c.π.app j).unop.app m (φ ~ y))
  let r₃ := FibreOrderIsoOfAppEq c hc f (choose_x hc ((c.π.app j).unop.app m (φ ~ y))) (φ ~ y)
    (choose_spec_x _ _)
  let s₁ := LimitToSmallWOFibreEquiv c hc f ((c.π.app j).unop.app n y)
  let s₂ := FibreOrderIsoOfAppEq c hc f (choose_x hc ((c.π.app j).unop.app n y)) y (choose_spec_x _ _)
  change r₃ (r₂.symm (r₁ (move φ x))) = move φ (s₂ (s₁.symm x))

  let t₁ := LimitToSmallWOFibreEquiv c hc f (φ ~ (c.π.app j).unop.app _ y)
  let t₂ := FibreOrderIsoOfAppEq c hc f (choose_x hc (φ ~ (c.π.app j).unop.app _ y))
    (choose_x hc ((c.π.app j).unop.app m (φ ~ y)))
    (by rw [choose_spec_x, choose_spec_x, hom_naturality_apply']; rfl)
  -- t₂ (t₁.symm _) = r₂.symm (r₁ _)
  let t₃ := FibreOrderIsoOfAppEq c hc f (choose_x hc (φ ~ (c.π.app j).unop.app _ y))
    (φ ~ choose_x hc ((c.π.app j).unop.app _ y))
    (by rw [choose_spec_x, hom_naturality_apply', choose_spec_x]; rfl)
  let t₄ := FibreOrderIsoOfAppEq c hc f (φ ~ choose_x hc ((c.π.app j).unop.app _ y)) (φ ~ y)
    (by rw [hom_naturality_apply', hom_naturality_apply', choose_spec_x]; rfl)

  have aux₁ : r₂.symm (r₁ (move φ x)) = t₂ (t₁.symm (move φ x)) := by
    change (r₁.trans r₂.symm) (move φ x) = (t₁.symm.trans t₂) (move φ x)
    apply IsWellOrder.OrderIso_apply_eq

  have aux₂ (z) : r₃ (t₂ z) = t₄ (t₃ z) := by
    change (t₂.trans r₃) z = (t₃.trans t₄) z
    apply IsWellOrder.OrderIso_apply_eq

  have aux₃ : t₃ (t₁.symm (move φ x)) = move φ (s₁.symm x) := by
    apply LimitToSmallWO.move_eq

  have aux₄ (z) : t₄ (move φ z) = move φ (s₂ z) := by
    apply FibreOrderIsoOfAppEq_move

  rw [aux₁, aux₂, aux₃, aux₄]

lemma limit_ext (g : ((Ω α).mapCone c).pt)
  (h : ∀ j, (Ω α).map (c.π.app j) g = (limit.π (F ⋙ Ω α) j) f) :
    limit.lift (F ⋙ Ω α) ((Ω α).mapCone c) g = f := by
  ext j
  refine Eq.trans ?_ (h j)
  change (limit.lift (F ⋙ Ω α) _ ≫ limit.π _ _) _ = _
  rw [limit.lift_π]; rfl

def LimitToSmallWOPullbackFibreOrderIso {j : J} (y : (F.obj j).unop.obj n):
    ((LimitToSmallWO c hc f).pullback (c.π.app j).unop).wo⁻¹ y ≃o
  (Ω_obj.out (limit.π (F ⋙ Ω α) j f)).wo⁻¹ y :=
    (SmallWO.pullback_RelIso' _ _ y).trans (LimitToSmallWOOrderIso c hc f y _ rfl)

lemma LimitToSmallWOPullbackFibreOrderIso_ext {j : J} {n m} (y : (F.obj j).unop.obj n)
  (φ : n ⟶ m) :
  ((LimitToSmallWO c hc f).FibreOrderIsoCast (hom_naturality_apply _ _ _).symm).trans
      (LimitToSmallWOOrderIso c hc f ((F.obj j).unop.map φ y) _ rfl) =
    (LimitToSmallWOOrderIso c hc f _ _ (hom_naturality_apply (c.π.app j).unop φ y)) :=
  IsWellOrder.OrderIso_ext _ _

lemma LimitToSmallWOPullbackFibreOrderIso_ext_apply {j : J} {n m} (y : (F.obj j).unop.obj n)
  (φ : n ⟶ m) (x):
    ((LimitToSmallWO c hc f).FibreOrderIsoCast (hom_naturality_apply _ _ _).symm).trans
      (LimitToSmallWOOrderIso c hc f ((F.obj j).unop.map φ y) _ rfl) x =
    (LimitToSmallWOOrderIso c hc f _ _ (hom_naturality_apply (c.π.app j).unop φ y)) x := by
  rw [LimitToSmallWOPullbackFibreOrderIso_ext]; rfl

def LimitToPieces (j : J) :
    Pieces ((LimitToSmallWO c hc f).pullback (c.π.app j).unop).wo
      ((limit.π (F ⋙ Ω α) j) f).out.wo where
  orderIso y := LimitToSmallWOPullbackFibreOrderIso c hc f y
  compatible {n m} φ y x:= by
    dsimp [LimitToSmallWOPullbackFibreOrderIso]
    erw [SmallWO.pullback_RelIso'_move,
         LimitToSmallWOPullbackFibreOrderIso_ext_apply c hc f y φ _,
         LimitToSmallWOOrderIso_move]
    rfl

def LimitToSmallWOPullbackOrderIso (f : limit (F ⋙ Ω α)) (j : J) :
    OrderIso ((LimitToSmallWO c hc f).pullback (unop (c.π.app j))).wo
      ((limit.π (F ⋙ Ω α) j) f).out.wo :=
  (LimitToPieces c hc f j).toOrderIso

lemma HomToLimit_hom_surjective (hc : IsLimit c) :
    (limit.lift (F ⋙ Ω α) ((Ω α).mapCone c)).Surjective := by
  intro f
  use Ω_obj.mk (LimitToSmallWO c hc f)
  apply limit_ext
  intro j
  conv => lhs; dsimp [Ω]; rw [Ω_map.mk_eq]
  rw [← Ω_obj.mk_out_eq (limit.π (F ⋙ Ω α) _ _)]
  exact Ω_obj.mk_sound ⟨LimitToSmallWOPullbackOrderIso c hc f j⟩

variable (α)
def IsoToLimitPt : ((Ω α).mapCone c).pt ≅ (limit.cone (F ⋙ Ω α)).pt := by
  apply Equiv.toIso (Equiv.ofBijective (HomToLimit α c).hom _)
  exact ⟨HomToLimit_hom_injective _ hc, HomToLimit_hom_surjective _ hc⟩

def IsIsoToLimitPt : IsIso (HomToLimit α c).hom where
  out := by
    use (IsoToLimitPt α c hc).inv
    exact ⟨(IsoToLimitPt α c hc).hom_inv_id, (IsoToLimitPt α c hc).inv_hom_id⟩

def IsIsoToLimit : IsIso (HomToLimit α c) := by
  have := IsIsoToLimitPt α c hc
  apply Cones.cone_iso_of_hom_iso

end Ω.PreservesLimit
open Ω.PreservesLimit

instance Ω.PreservesLimit :
    PreservesLimit F (Ω α) where
  preserves {c} hc := by
    have := IsIsoToLimit α c hc
    exact IsLimit.ofIsoLimit (limit.isLimit _) (asIso (HomToLimit α c)).symm

instance Ω.PreservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (Ω α) :=
  ⟨⟨inferInstance⟩⟩

end

def W : SSet := standardSimplex.op ⋙ Ω α

section
open Presheaf
variable (Y)

def Ω.CorepresentableAux₁ :
    (Y ⟶ W α) ≃ limit (Y.functorToRepresentables.op ⋙ (yoneda.obj (W α))) :=
  (IsoOfPreservesLimit (yoneda.obj (W α)) Y).toEquiv

variable {Y' : SSet} (f : Y' ⟶ Y) (g : Y ⟶ W α)

variable {Y} in
abbrev Ω.Corepresentable_compAux (G : SSetᵒᵖ ⥤ Type u) :
  limit ((functorToRepresentables Y).op ⋙ G) ⟶
    limit ((functorToRepresentables Y').op ⋙ G) :=
  limit.pre _ (CategoryOfElements.map f).op.op

variable {α Y} in
lemma Ω.CorepresentableAux₁_comp_apply :
    (CorepresentableAux₁ α Y') (f ≫ g) =
      Corepresentable_compAux f _ ((CorepresentableAux₁ α Y) g) :=
  congrFun (IsoOfPreservesLimit_comp_hom (yoneda.obj (W α)) f) g

def Ω.CorepresentableAux₂ :
    (functorToRepresentables Y).op ⋙ (yoneda.obj (W α)) ≅
      (functorToRepresentables Y).op ⋙ Ω α := by
  refine NatIso.ofComponents (fun x ↦ (yonedaEquiv _ _).toIso) ?_
  intro x y f; ext a; simp
  erw [← yonedaEquiv_naturality_left]
  rfl

variable {α Y} in
lemma Ω.CorepresentableAux₂_comp : (CorepresentableAux₂ α Y').hom =
  whiskerLeft (CategoryOfElements.map f).op.op (CorepresentableAux₂ α Y).hom := by
    ext; simp [CorepresentableAux₂, NatIso.ofComponents]

def Ω.CorepresentableAux₃' :
    limit ((functorToRepresentables Y).op ⋙ (yoneda.obj (W α))) ≅
      limit ((functorToRepresentables Y).op ⋙ Ω α) :=
  lim.mapIso (Ω.CorepresentableAux₂ _ _)

variable {Y} in
lemma Ω.CorepresentableAux₃_comp :
  Corepresentable_compAux f _ ≫ (CorepresentableAux₃' α Y').hom =
    (CorepresentableAux₃' α Y).hom ≫ Corepresentable_compAux f _ := by
  simp [Corepresentable_compAux, CorepresentableAux₃']
  apply limit.pre_naturality' (CorepresentableAux₂ α Y).hom _ (CorepresentableAux₂_comp f)

def Ω.CorepresentableAux₃ :
    limit ((functorToRepresentables Y).op ⋙ (yoneda.obj (W α))) ≃
      limit ((functorToRepresentables Y).op ⋙ Ω α) :=
  (CorepresentableAux₃' _ _).toEquiv

variable {α Y} in
lemma Ω.CorepresentableAux₃_comp_apply (x) :
  CorepresentableAux₃ α Y' (Corepresentable_compAux f _ x) =
    Corepresentable_compAux f _ (CorepresentableAux₃ α Y x) :=
  congrFun (CorepresentableAux₃_comp α f) x

instance : PreservesLimit (functorToRepresentables Y).op (Ω α) := by
  apply (Ω.PreservesLimitsOfSize α).preservesLimitsOfShape.preservesLimit

def Ω.CorepresentableAux₄ :
    limit ((functorToRepresentables Y).op ⋙ Ω α) ≃ (Ω α).obj (op Y) :=
  ((IsoOfPreservesLimit (Ω α) Y).symm).toEquiv

variable {α Y} in
lemma Ω.CorepresentableAux₄_comp_apply (x) :
  CorepresentableAux₄ α Y' (Corepresentable_compAux f _ x) =
    (Ω α).map f.op (CorepresentableAux₄ α Y x) :=
  (congrFun (IsoOfPreservesLimit_comp_inv (Ω α) f) x).symm

end

def Ω.Corepresentable : (Ω α).CorepresentableBy  (op (W α)) where
  homEquiv {Y} := equivToOpposite.symm.trans ((CorepresentableAux₁ _ (unop Y)).trans
    ((CorepresentableAux₃ _ (unop Y)).trans (CorepresentableAux₄ _ (unop Y))))
  homEquiv_comp {Y Y'} g f := by
    dsimp [equivToOpposite]
    erw [CorepresentableAux₁_comp_apply, CorepresentableAux₃_comp_apply,
         CorepresentableAux₄_comp_apply]
    rfl

def Ω.Corepresentable.app (X : SSet.{u}):
    (X ⟶ (W α)) ≃ (Ω α).obj (op X) :=
  Opposite.equivToOpposite.trans ((Ω.Corepresentable α).homEquiv (Y := op X))

namespace Ω
variable {X : SSet.{u}} {α}

def toHom (a : (Ω α).obj (op X)) : X ⟶ W α := (Ω.Corepresentable.app α X).invFun a

def toObj (f : X ⟶ W α) : (Ω α).obj (op X) := (Ω.Corepresentable.app α X).toFun f

@[simp]
lemma Corepresentable.homEquiv_apply {X : SSetᵒᵖ} (f : op (W α) ⟶ X):
    (Ω.Corepresentable α).homEquiv f = toObj f.unop := rfl

@[simp]
lemma Corepresentable.homEquiv_symm_apply {X : SSetᵒᵖ} (a : (Ω α).obj X) :
    (Ω.Corepresentable α).homEquiv.symm a = (toHom a).op := rfl

@[simp]
lemma toHom_toObj (f : X ⟶ W α) :
    toHom (toObj f) = f := (Ω.Corepresentable.app α X).left_inv _

@[simp]
lemma toObj_toHom (a : (Ω α).obj (op X)) :
    toObj (toHom a) = a := (Ω.Corepresentable.app α X).right_inv _

open standardSimplex

lemma toObj.simplex {n : ℕ} (f : Δ[n] ⟶ W α) :
    toObj f = yonedaEquiv _ _ f := by
  change (CorepresentableAux₄ α Δ[n]) ((CorepresentableAux₃ α Δ[n])
      ((CorepresentableAux₁ α Δ[n]) f)) =
    IsoOfPreservesLimitOfPi _ (fun j ↦ (CorepresentableAux₂ α Δ[n]).hom.app _
      (IsoOfPreservesLimitToPi (yoneda.obj (W α)) f j))
  rw [IsoOfPreservesLimitToPi_fac_apply]
  conv => rhs; congr; ext; rw [← PiWhiskerRight_naturality_apply _ (Ω α)]
  erw [limitToPi_fac_apply]
  rfl

end Ω
abbrev UniSmallWO₀ := Ω.toObj (𝟙 (W α))

abbrev UniSmallWO := Quotient.out $ (equivShrink (Ω_obj₀ α (W α))).symm (UniSmallWO₀ α)

lemma UniSmallWO.Ω_obj_mk : Ω_obj.mk (UniSmallWO α) = UniSmallWO₀ α := by
  simp only [Ω_obj.mk, UniSmallWO, Quotient.out_eq, Equiv.apply_symm_apply]

abbrev W' := (UniSmallWO α).of

abbrev UniWO : W' α ⟶ₒ W α := (UniSmallWO α).wo

variable {α}

lemma Ω.Corepresentable.universal (f : X ⟶ W α) :
    toObj f = (Ω α).map (op f) (UniSmallWO₀ α) :=
  (Ω.Corepresentable α).homEquiv_comp (op f) (𝟙 _)

lemma UniSmallWO.universal (g : SmallWO α X) :
    g ≈  (UniSmallWO α).pullback (Ω.toHom (Ω_obj.mk g)):= by
  rw [← Quotient.eq_iff_equiv]
  apply_fun equivShrink (Ω_obj₀ α _)
  change Ω_obj.mk _ = Ω_obj.mk _
  rw [← Ω_map.mk_eq]
  convert Ω.Corepresentable.universal (Ω.toHom (Ω_obj.mk g))
  . simp only [Ω.toObj_toHom]
  . apply UniSmallWO.Ω_obj_mk

-- `Υ` defined as subtype of `Ω`

abbrev SmallWO.Kan (f : SmallWO α Y) : Prop := KanFibration f.hom

lemma Kan.sound (f g : SmallWO α Y) :
    f ≈ g → f.Kan = g.Kan := by
  intro ⟨h₁⟩
  simp only [SmallWO.Kan, SmallWO.hom, eq_iff_iff]
  constructor
  . rw [← (Iso.inv_comp_eq _).mpr h₁.comm]
    apply KanFibration.isIso_comp
  . rw [h₁.comm]
    apply KanFibration.isIso_comp

lemma Kan.sound_iff (f g : SmallWO α Y) :
    f ≈ g → (f.Kan ↔ g.Kan) := by
  rw [← eq_iff_iff]
  exact Kan.sound f g

def Ω_obj.Kan : Ω_obj α Y → Prop :=
  Shrink.rec $ Quotient.lift SmallWO.Kan Kan.sound

lemma SmallWO.Kan_iff_Ω_obj_mk_Kan (a : SmallWO α Y) :
    a.Kan ↔ (Ω_obj.mk a).Kan := by
  simp only [Shrink.rec, Ω_obj.mk, Ω_obj.Kan, Equiv.symm_apply_apply,
    Quotient.lift_mk, eq_rec_constant]

lemma Ω_obj.Kan_iff_pullback_toHom_Kan :
    ∀ a : Ω_obj α Y, a.Kan ↔ ( (UniSmallWO α).pullback (Ω.toHom a)).Kan := by
    apply Shrink.rec
    apply Quotient.ind
    intro a
    erw [← SmallWO.Kan_iff_Ω_obj_mk_Kan]
    exact Kan.sound_iff _ _ (UniSmallWO.universal a)

lemma Ω_obj.Kan_iff_pullback_snd_toHom_Kan (a : Ω_obj α Y) :
    a.Kan ↔ KanFibration (pullback.snd (UniSmallWO α).hom (Ω.toHom a)) := by
  rw [Kan_iff_pullback_toHom_Kan]; rfl

-- Greek `Υ`, not latin `Y`
variable (α Y) in
abbrev Υ_obj := {a : Ω_obj α Y // a.Kan}

def Υ_obj.mk (a : SmallWO α Y) (ha : a.Kan) : Υ_obj α Y :=
  ⟨Ω_obj.mk a, a.Kan_iff_Ω_obj_mk_Kan.mp ha⟩

lemma Ω_map.Kan : ∀ (a : Ω_obj α Y), a.Kan → (Ω_map α f a).Kan := by
  apply Shrink.rec
  apply Quotient.ind
  intro a
  erw [Ω_map.mk_eq, ← SmallWO.Kan_iff_Ω_obj_mk_Kan, ← SmallWO.Kan_iff_Ω_obj_mk_Kan]
  simp only [SmallWO.Kan, SmallWO.pullback, SmallWO.hom]
  apply KanFibration.pullback_snd

variable (α) in
def Υ_map (f : Y' ⟶ Y) : Υ_obj α Y ⟶ Υ_obj α Y' :=
  Subtype.map (Ω_map α f) (Ω_map.Kan)

lemma Υ_map_id : Υ_map α (𝟙 Y) = 𝟙 (Υ_obj α Y) := by
  ext _ : 2
  simp [Υ_map, Ω_map_id]

lemma Υ_map_comp {f : Y ⟶ Y'} {g : Y' ⟶ Y''}:
    (Υ_map α g) ≫ (Υ_map α f) = Υ_map α (f ≫ g) := by
  ext _ : 2
  simp [Υ_map, ← Ω_map_comp]

variable (α)

def Υ : SSetᵒᵖ ⥤ Type u where
  obj Y := Υ_obj α (unop Y)
  map f := Υ_map α (unop f)
  map_id Y := by simp; rw [← Υ_map_id]; rfl
  map_comp f g:= by simp; rw [Υ_map_comp]; rfl

def U : SSet := standardSimplex.op ⋙ Υ α

def Υ.toΩ : Υ α ⟶ Ω α where
  app n a := a.val

def U.toW : U α ⟶ W α := NatTrans.id (standardSimplex.op) ◫ Υ.toΩ α

variable {α} in
lemma U.toW.app_eq_val {k} (x : (U α).obj k) :
    (U.toW α).app _ x = x.val := by
  simp only [U.toW, FunctorToTypes.hcomp, NatTrans.id_app', FunctorToTypes.map_id_apply]
  rfl

instance U.toW.mono : Mono (U.toW α) where
  right_cancellation {Z} g h hyp := by
    ext k a
    apply_fun fun f ↦ f.app k a at hyp
    erw [NatTrans.vcomp_app, NatTrans.vcomp_app] at hyp
    simp [app_eq_val] at hyp
    rwa [← Subtype.val_inj]

abbrev UniSmallWOKan₀ := Ω_map α (U.toW α) (UniSmallWO₀ α)

abbrev UniSmallWOKan := Quotient.out $ (equivShrink (Ω_obj₀ α (U α))).symm (UniSmallWOKan₀ α)

variable {α}
lemma UniSmallWOKan₀.eq_toObj : UniSmallWOKan₀ α = Ω.toObj (U.toW α) :=
  (Ω.Corepresentable.universal _).symm

lemma UniSmallWOKan₀.toHom : Ω.toHom (UniSmallWOKan₀ α) = U.toW α := by
  rw [eq_toObj, Ω.toHom_toObj]

lemma UniSmallWOKan.Ω_obj_mk : Ω_obj.mk (UniSmallWOKan α) = UniSmallWOKan₀ α := by
  simp only [Ω_obj.mk, UniSmallWO, Quotient.out_eq, Equiv.apply_symm_apply]

lemma UniSmallWOKan.equiv_smallWO_pullback :
    UniSmallWOKan α ≈  (UniSmallWO α).pullback (U.toW α):= by
  rw [← Quotient.eq_iff_equiv, Quotient.out_eq]
  apply_fun (equivShrink (Ω_obj₀ α (U α)))
  simp only [Equiv.apply_symm_apply, UniSmallWOKan₀,
      ← UniSmallWO.Ω_obj_mk, Ω_map.mk_eq]
  rfl

variable (α)
abbrev U' := (UniSmallWOKan α).of

abbrev UniWOKan : U' α ⟶ₒ U α := (UniSmallWOKan α).wo

variable {α}

lemma U.toW.simplex_comp_eq_toHom_val {k : ℕ} (σ : Δ[k] ⟶ U α):
    σ ≫ U.toW α = Ω.toHom (((U α).yonedaEquiv [k]) σ).val := by
  rw [← app_eq_val, yonedaEquiv_naturality_right, ← Ω.toObj.simplex, Ω.toHom_toObj]

lemma U.toW.Kan_pullback_snd_simplex_comp {k : ℕ} (σ : Δ[k] ⟶ U α) :
    KanFibration (pullback.snd (UniWO α).hom (σ ≫ U.toW α)) := by
  have := (yonedaEquiv _ _ σ).property
  rwa [Ω_obj.Kan_iff_pullback_snd_toHom_Kan, ← simplex_comp_eq_toHom_val] at this

lemma U.Kan_pullback_snd_simplex : ∀ {k : ℕ} (σ : Δ[k] ⟶ U α),
    KanFibration (pullback.snd (UniWOKan α).hom σ) := by
  intro k σ
  have := toW.Kan_pullback_snd_simplex_comp σ
  rw [← pullback.rightCompIso_hom_comp_snd] at this
  apply KanFibration.of_isIso_comp at this
  obtain ⟨h⟩ := UniSmallWOKan.equiv_smallWO_pullback (α := α)
  have comm : (UniWOKan α).hom =
    h.toIso.hom ≫ (pullback.snd (UniWO α).hom (U.toW α)) := h.comm
  rw [comm, ← pullback.leftCompIso_hom_comp_snd, ← Category.assoc]
  apply KanFibration.isIso_comp -- Lean has the instance that pullback.snd of iso is iso

instance UniWOKan.hom.KanFibration : KanFibration (UniWOKan α).hom :=
  KanFibration.of_forall_pullback_snd_KanFibration U.Kan_pullback_snd_simplex

instance UniWOKan.hom.KanFibration' :
    SSet.KanFibration (pullback.snd (UniSmallWO α).hom (U.toW α)) := by
  have := Kan.sound_iff _ _ (UniSmallWOKan.equiv_smallWO_pullback (α := α))
  dsimp [SmallWO.Kan, SmallWO.pullback, SmallWO.hom] at this
  rw [← this]
  exact UniWOKan.hom.KanFibration

lemma UniSmallWOKan.Kan : (UniSmallWOKan α).Kan :=
  UniWOKan.hom.KanFibration

lemma UniSmallWOKan₀.Kan : (UniSmallWOKan₀ α).Kan := by
  rw [← UniSmallWOKan.Ω_obj_mk, ← SmallWO.Kan_iff_Ω_obj_mk_Kan]
  exact UniSmallWOKan.Kan

variable (α) in
abbrev Υ_obj.UniSmallWOKan₀ : Υ_obj α (U α) :=
  ⟨SSet.UniSmallWOKan₀ α, UniSmallWOKan₀.Kan⟩

lemma factor_iff_forall_Kan (f : Y ⟶ W α) :
    (∃ φ, f = φ ≫ U.toW α) ↔ (∀ ⦃k⦄ (x : Y _[k]), (f.app _ x).Kan) := by
  constructor
  . intro ⟨φ, h⟩ k x
    rw [h, Ω_obj.Kan_iff_pullback_snd_toHom_Kan,
        yonedaEquiv_symm_naturality_right, ← Ω.toObj.simplex, Ω.toHom_toObj,
        ← Category.assoc, ← yonedaEquiv_symm_naturality_right']
    apply U.toW.Kan_pullback_snd_simplex_comp
  . intro h
    use {
      app := fun n y ↦ ⟨f.app _ y, h (k := n.unop.len) y⟩
      naturality := by
        intro _ _ _; ext _; apply Subtype.ext
        change (Y.map _ ≫ f.app _) _ = _
        rw [f.naturality]
        rfl
    }
    ext n y; erw [NatTrans.vcomp_app]
    simp [U.toW, Υ.toΩ]

lemma SmallWO.Kan_iff_factor :
    a.Kan ↔ ∃ φ, Ω.toHom (Ω_obj.mk a)  = φ ≫ U.toW α := by
  rw [SmallWO.Kan_iff_Ω_obj_mk_Kan, Ω_obj.Kan_iff_pullback_snd_toHom_Kan]
  constructor
  . rw [factor_iff_forall_Kan]; intro h k x
    rw [yonedaEquiv_symm_naturality_right, Ω_obj.Kan_iff_pullback_snd_toHom_Kan,
        ← Ω.toObj.simplex, Ω.toHom_toObj, ← pullback.rightCompIso_hom_comp_snd]
    apply KanFibration.isIso_comp' _ _ KanFibration.pullback_snd
  . intro ⟨φ, h⟩
    rw [h, ← pullback.rightCompIso_hom_comp_snd]
    apply KanFibration.isIso_comp' _ _ KanFibration.pullback_snd

lemma Ω_obj.Kan_iff_factor : ∀ a : Ω_obj α Y, a.Kan ↔ ∃ φ, Ω.toHom a  = φ ≫ U.toW α := by
  apply Shrink.rec
  apply Quotient.ind
  intro a
  convert a.Kan_iff_factor
  exact (SmallWO.Kan_iff_Ω_obj_mk_Kan _).symm

lemma Ω_obj.Kan_toObj_comp {f : X ⟶ U α} :
    (Ω.toObj (f ≫ U.toW α)).Kan := by
  rw [Kan_iff_factor, Ω.toHom_toObj]
  use f

open Classical

def Ω_obj.Kan_choose_factor (a : Ω_obj α Y) (ha : a.Kan):
    Y ⟶ U α := choose (a.Kan_iff_factor.mp ha)

lemma Ω_obj.Kan_choose_factor_spec (a : Ω_obj α Y) (ha : a.Kan):
    Ω.toHom a  = a.Kan_choose_factor ha ≫ U.toW α := choose_spec (a.Kan_iff_factor.mp ha)

variable (α) in
def Υ.Corepresentable : (Υ α).CorepresentableBy  (op (U α)) where
  homEquiv {Y} :={
    toFun := fun f ↦ ⟨(Ω.Corepresentable α).homEquiv ((U.toW α).op ≫ f), by
      simp only [Ω.Corepresentable.homEquiv_apply, unop_comp, Quiver.Hom.unop_op]
      apply Ω_obj.Kan_toObj_comp⟩
    invFun := fun a ↦ (a.val.Kan_choose_factor a.property).op
    left_inv := by
      intro f; rw [← Quiver.Hom.unop_inj.eq_iff]; simp
      rw [← cancel_mono (U.toW α), ← Ω_obj.Kan_choose_factor_spec, Ω.toHom_toObj]
    right_inv := by
      intro a; apply Subtype.ext; simp
      rw [← Ω_obj.Kan_choose_factor_spec, Ω.toObj_toHom]
  }
  homEquiv_comp {Y Y'} g f := by
    apply Subtype.ext; simp [Υ, Υ_map]
    apply (Ω.Corepresentable α).homEquiv_comp g _

namespace Υ

variable (α) in
def Corepresentable.app (X : SSet.{u}):
    (X ⟶ (U α)) ≃ (Υ α).obj (op X) :=
  Opposite.equivToOpposite.trans ((Υ.Corepresentable α).homEquiv (Y := op X))

def toHom (a : (Υ α).obj (op X)) : X ⟶ U α := (Corepresentable.app α X).invFun a

def toObj (f : X ⟶ U α) : (Υ α).obj (op X) := (Corepresentable.app α X).toFun f

@[simp]
lemma Corepresentable.homEquiv_apply {X : SSetᵒᵖ} (f : op (U α) ⟶ X):
    (Corepresentable α).homEquiv f = toObj f.unop := rfl

@[simp]
lemma Corepresentable.homEquiv_symm_apply {X : SSetᵒᵖ} (a : (Υ α).obj X) :
    (Corepresentable α).homEquiv.symm a = (toHom a).op := rfl

@[simp]
lemma toHom_toObj (f : X ⟶ U α) :
    toHom (toObj f) = f := (Corepresentable.app α X).left_inv _

@[simp]
lemma toObj_toHom (a : (Υ α).obj (op X)) :
    toObj (toHom a) = a := (Corepresentable.app α X).right_inv _

lemma Corepresentable.universal (f : X ⟶ U α) :
    toObj f = (Υ α).map (op f) (Υ_obj.UniSmallWOKan₀ α) := by
  convert (Υ.Corepresentable α).homEquiv_comp (op f) (𝟙 _)
  apply Subtype.ext; simp
  rw [UniSmallWOKan₀.eq_toObj]
  rfl

end Υ

lemma UniSmallWOKan.universal (g : SmallWO α X) (hg : g.Kan) :
    Υ_obj.mk g hg = Υ_obj.mk ((UniSmallWOKan α).pullback (Υ.toHom (Υ_obj.mk g hg)))
        KanFibration.pullback_snd := by
  convert Υ.Corepresentable.universal (Υ.toHom (Υ_obj.mk g hg))
  . simp only [Υ.toObj_toHom]
  . apply Subtype.ext
    simp only [Υ_obj.mk, Υ, Υ_map, op_obj, op_map, Subtype.map_coe,  ← Ω_obj_mk,
      Ω_map.mk_eq]

lemma UniSmallWOKan.universal' (g : SmallWO α X) (hg : g.Kan) :
    g ≈  (UniSmallWOKan α).pullback (Υ.toHom (Υ_obj.mk g hg)):= by
  rw [← Quotient.eq_iff_equiv]
  apply_fun equivShrink (Ω_obj₀ α _)
  exact congrArg Subtype.val (universal g hg)

end UniversalSimplicialSet

end
end SSet
