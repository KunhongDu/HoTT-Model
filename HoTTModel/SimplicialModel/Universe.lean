import HoTTModel.SSet.Fibrations
import HoTTModel.RepresentableBy
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import HoTTModel.SimplicialModel.test

-- This file aims to construct a universe in sSet
open Simplicial CategoryTheory Opposite Limits Functor Set

universe u

namespace LinearOrder

variable {A B : Type u} (ord : LinearOrder A) (h : A ≃ B)

-- there is `IsPullback.WellOrderedHom`; merge this two
def ofEquiv :
    LinearOrder B where
  le a b := h.symm a ≤ h.symm b
  le_refl _ := le_refl _
  le_trans _ _ _ := le_trans
  le_antisymm _ _ h₁ h₂ := by
    rw [← h.symm.apply_eq_iff_eq]
    apply le_antisymm h₁ h₂
  le_total _ _ := le_total _ _
  decidableLE _ _ := LinearOrder.decidableLE _ _
  decidableEq a b := by
    rw [← h.symm.apply_eq_iff_eq]
    apply LinearOrder.decidableEq _ _ -- this should be default??

-- LinearOrder.ofEquiv iff
lemma ofEquiv_le_iff_le :
    ∀ a b : B, (ofEquiv ord h).le a b ↔ h.symm a ≤ h.symm b := by
  intros; rfl

lemma ofEquiv_lt_iff_lt :
    ∀ a b : B, (ofEquiv ord h).lt a b ↔ h.symm a < h.symm b := by
  intro a b
  rw [(ofEquiv ord h).lt_iff_le_not_le, lt_iff_le_not_le,
      ofEquiv_le_iff_le, ofEquiv_le_iff_le]

noncomputable def ofEquiv.ltRelIso :
    RelIso ord.lt (ofEquiv ord h).lt where
  toEquiv := h
  map_rel_iff' {_ _} := by
    rw [ofEquiv_lt_iff_lt, h.symm_apply_apply, h.symm_apply_apply]

def ofEquiv.isWellOrderOfIsWellOrder {A B : Type u} (ord : LinearOrder A)
    (h : A ≃ B) (_ : IsWellOrder A ord.lt) : IsWellOrder B (ofEquiv ord h).lt :=
  (ofEquiv.ltRelIso ord h).symm.toRelEmbedding.isWellOrder

end LinearOrder

namespace SSet
noncomputable section Fibre
variable {X Y : SSet.{u}} (f : X ⟶ Y)

def _root_.CategoryTheory.TypesPullbackPreimageEquiv {P X Y Z : Type u}
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

abbrev Fibre {n : SimplexCategoryᵒᵖ} (y : Y.obj n) : Set (X.obj n) :=
  (f.app n) ⁻¹' {y}

variable {f} in
lemma Fibre.app_eq {n : SimplexCategoryᵒᵖ} {y : Y.obj n} (x : Fibre f y) :
    f.app _ x.val = y := by
  have := x.2
  dsimp [Fibre, Set.preimage] at this
  rw [Set.mem_singleton_iff] at this
  exact this

def _root_.CategoryTheory.IsPullback.fibreEquiv {P X Y Z : SSet}
  {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (D : IsPullback fst snd f g) {n : SimplexCategoryᵒᵖ} (y : Y.obj n) :
    Fibre snd y ≃ Fibre f (g.app _ y) :=
  CategoryTheory.TypesPullbackPreimageEquiv (IsPullback.map (ev' n) D) _

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

@[simp]
abbrev WellOrderedHom.fibre (f : WellOrderedHom X Y) {n : SimplexCategoryᵒᵖ}
  (y : Y.obj n) := Fibre f.hom y

-- why isn't wellOrder a class like partialOrder

attribute [instance] WellOrderedHom.ord WellOrderedHom.isWellOrder

notation X " ⟶ₒ " Y => WellOrderedHom X Y

infix:80 "⁻¹ " => WellOrderedHom.fibre
-- notation: f "⁻¹" y => ... gives wrong display on inforview

section Pullback_Fibre_WellOrdered
variable {P X Y Z : SSet} {h : P ⟶ X} {i : P ⟶ Y} {f : X ⟶ₒ Z} {g : Y ⟶ Z}
  (D : IsPullback h i f.hom g) {n : SimplexCategoryᵒᵖ} (y : Y.obj n)

noncomputable def IsPullback.WellOrderedHom  :
    LinearOrder (Fibre i y) :=
  LinearOrder.ofEquiv f.ord (D.fibreEquiv y).symm

-- may be useless
lemma IsPullback.WellOrderedHom.le_iff_le (a b : Fibre i y) :
    (IsPullback.WellOrderedHom D y).le a b ↔ D.fibreEquiv _ a ≤ D.fibreEquiv _ b := by
  rfl

lemma IsPullback.WellOrderedHom.lt_iff_lt (a b : Fibre i y) :
    (IsPullback.WellOrderedHom D y).lt a b ↔ D.fibreEquiv _ a < D.fibreEquiv _ b := by
  rw [(IsPullback.WellOrderedHom D y).lt_iff_le_not_le, lt_iff_le_not_le,
      le_iff_le, le_iff_le]

noncomputable def IsPullback.WellOrderedHom.ltRelIso :
    RelIso (IsPullback.WellOrderedHom D y).lt (f.ord (y := g.app _ y)).lt where
  toEquiv := D.fibreEquiv y
  map_rel_iff' := (lt_iff_lt D y _ _).symm

/-
noncomputable def IsPullback.WellOrderedHom.leRelIso :
    RelIso (IsPullback.WellOrderedHom D y).le (f.ord (y := g.app _ y)).le where
  toEquiv := D.fibreEquiv y
  map_rel_iff' := (le_iff_le D y _ _).symm
-/


noncomputable def IsPullback.WellOrderedHom.OrderIso :
    @OrderIso (Fibre i y) (f⁻¹ (g.app _ y)) (IsPullback.WellOrderedHom D y).toLE _ where
  toEquiv := D.fibreEquiv y
  map_rel_iff' := (le_iff_le D y _ _).symm


def IsPullback.WellOrderedHom.isWellOrder :
    IsWellOrder _ (IsPullback.WellOrderedHom D y).lt := by
  apply LinearOrder.ofEquiv.isWellOrderOfIsWellOrder _ _ f.isWellOrder

--- you really should read the proof of
#check RelEmbedding.acc

end Pullback_Fibre_WellOrdered

def Fibre.trans {f : X ⟶ Y} {f' : X' ⟶ Y} (g : X ⟶ X')
    (comm : f = g ≫ f') {y : Y.obj n} (a : (Fibre f y)): (Fibre f' y) :=
  ⟨g.app _ a, comm.symm ▸ a.2⟩

def Fibre.map {f : X ⟶ Y} {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) {y : Y.obj n}
  (a : Fibre f y) : Fibre f (Y.map φ y) := by
  use X.map φ a.val
  simp only [SimplexCategory.mk_len, op_unop, mem_preimage, mem_singleton_iff]
  change (X.map φ ≫ f.app m) _ = _
  erw [f.naturality φ, types_comp_apply, Fibre.app_eq a]

-- can't find: nonempty set in a well order has a least element

lemma Fibre.eq_iff_trans_eq_of_iso {f : X ⟶ Y} {f' : X' ⟶ Y} (F : Iso X X') {y : Y.obj n}
  (comm : f = F.hom ≫ f') (a b : Fibre f y):
    a = b ↔ Fibre.trans F.hom comm a = Fibre.trans F.hom comm b := by
  constructor
  exact fun h ↦ by rw [h]
  intro h -- this must be simplifiable
  apply_fun Fibre.trans (f := f') (f' := f) F.inv (by simp [comm]) at h
  simp [Fibre.trans] at h
  exact h

lemma isLeast_lt_false {α β: Type}[Preorder α] [Preorder β]
  [IsWellOrder α (· < ·)] [IsWellOrder β (· < ·)] {f g : α ≃o β}
  {a : α} (ha : IsLeast {a | f a = g a}ᶜ a) (lt : f a < g a) : False := by
  set a' := g.symm (f a) with ha'
  apply_fun g at ha'
  simp at ha'
  have aux : f a' < g a' := by
    rwa [ha', OrderIso.lt_iff_lt f, ← OrderIso.lt_iff_lt g, ha']
  have : f a ≤ f a' := by rw [OrderIso.le_iff_le]; exact ha.2 aux.ne
  apply False.elim <| (lt_self_iff_false (f a')).mp (lt_of_lt_of_le aux (ha'.symm ▸ this))

-- use this : InitialSeg.ofIso
def _root_.OrderIso.toInitialSeg {α β: Type*} [Preorder α] [Preorder β] (f : α ≃o β) :
    InitialSeg (α := α) (β := β) (· < ·) (· < ·) where
  toFun := f
  inj' := f.injective
  map_rel_iff' := by simp only [Function.Embedding.coeFn_mk, OrderIso.lt_iff_lt, implies_true]
  init' := by
    intro _ b _
    use f.symm b
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, OrderIso.apply_symm_apply]

lemma initialSeg_of_isWellOrder_eq {α β: Type*} [Preorder α] [Preorder β] (f : α ≃o β) (a : α) :
    f a = f.toInitialSeg a := by
  rfl

lemma _root_.IsWellOrder.OrderIso_apply_eq (α β: Type*) [Preorder α] [Preorder β]
  [IsWellOrder α (· < ·)] [IsWellOrder β (· < ·)] (f g : α ≃o β) (a : α) :
    f a = g a := by
  rw [initialSeg_of_isWellOrder_eq, initialSeg_of_isWellOrder_eq]
  apply InitialSeg.eq

lemma _root_.IsWellOrder.OrderIso_eq (α β: Type*) [Preorder α] [Preorder β]
  [IsWellOrder α (· < ·)] [IsWellOrder β (· < ·)] (f g : α ≃o β) : f = g := by
  ext
  apply IsWellOrder.OrderIso_apply_eq

@[ext]
structure OrderIso (f : X ⟶ₒ Y) (f' : X' ⟶ₒ Y) extends Iso X X' where
  comm : f.1 = hom ≫ f'.1
  mono {y : Y.obj n} : Monotone $ Fibre.trans hom comm (y := y)

namespace OrderIso
variable {f : X ⟶ₒ Y} {f' : X' ⟶ₒ Y}

lemma comm_inv (F : OrderIso f f') :
    F.inv ≫ f.hom = f'.hom :=
  (Iso.inv_comp_eq _).mpr F.comm

lemma ext' (F G : OrderIso f f') (w : F.hom = G.hom) :
    F = G := by
  have := Iso.ext w
  ext1 <;> rw [this]

def fibreTrans (F : OrderIso f f') {n : SimplexCategoryᵒᵖ} {y : Y.obj n} :=
  Fibre.trans F.hom F.comm (y := y)

def fibreEquiv (F : OrderIso f f') {n : SimplexCategoryᵒᵖ} (y : Y.obj n) :
    ↑(f⁻¹ y) ≃ ↑(f'⁻¹ y) where
  toFun := Fibre.trans F.hom F.comm -- change to fibreTrans
  invFun := Fibre.trans F.inv F.comm_inv.symm
  left_inv := by intro; simp [Fibre.trans]
  right_inv := by intro; simp [Fibre.trans]

lemma strictMono (F : OrderIso f f') {y : Y.obj n} :
    StrictMono $ F.fibreTrans (y := y) :=
  F.mono.strictMono_of_injective (F.fibreEquiv _).injective

lemma lt_iff_lt (F : OrderIso f f') {n : SimplexCategoryᵒᵖ} {y : Y.obj n} (a b : f⁻¹ y) :
    a < b ↔ F.fibreTrans a < F.fibreTrans b :=
  F.strictMono.lt_iff_lt.symm

lemma le_iff_le (F : OrderIso f f') {n : SimplexCategoryᵒᵖ} {y : Y.obj n} (a b : f⁻¹ y) :
    a ≤ b ↔ F.fibreTrans a ≤ F.fibreTrans b :=
  F.strictMono.le_iff_le.symm

def symm {f : X ⟶ₒ Y} {f' : X' ⟶ₒ Y} (F : OrderIso f f') :
    OrderIso f' f := {
  toIso := F.toIso.symm
  comm := by erw [F.comm, ← Category.assoc, F.inv_hom_id_assoc]
  mono := by
    intro n y
    apply StrictMono.monotone
    intro a b hab
    rw [F.lt_iff_lt]
    convert hab
    <;> convert (F.fibreEquiv y).right_inv _
  }

@[simp]
lemma symm_hom {f : X ⟶ₒ Y} {f' : X' ⟶ₒ Y} (F : OrderIso f f') :
    F.symm.hom = F.inv := rfl

-- define that OrderIso gives an `OrderIso` between fibres
def FibreOrderIso {f : X ⟶ₒ Y} {g : X' ⟶ₒ Y} (F : OrderIso f g) {n : SimplexCategoryᵒᵖ} (y : Y.obj n) :
    (f⁻¹ y) ≃o (g⁻¹ y) where
  toEquiv := F.fibreEquiv y
  map_rel_iff' {_} {_} := F.strictMono.le_iff_le

-- the default ext for simplcial map is not easy to use

lemma subsingleton_OrderIso {f : X ⟶ₒ Y} {f' : X' ⟶ₒ Y} (F G : OrderIso f f') : F = G := by
  apply OrderIso.ext'
  ext n a: 2
  induction n using recop
  rename ℕ => n
  have aux1 : F.hom.app _ a = (F.FibreOrderIso (f.hom.app _ a)) ⟨a, by simp⟩ :=
    rfl
  have aux2 : G.hom.app _ a = (G.FibreOrderIso (f.hom.app _ a)) ⟨a, by simp⟩ :=
    rfl
  rw [aux1, aux2]
  -- change `F.hom.app _ a = (F.FibreOrderIso (f.hom.app _ a)) ⟨a, by simp⟩ =`
  --  `G.hom.app _ a = (G.FibreOrderIso (f.hom.app _ a)) ⟨a, by simp⟩`
  -- does not work now
  congr 1
  apply IsWellOrder.OrderIso_apply_eq _ _ _ _

-- should not be in the namespace `OrderIso`
def move {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) {y : Y.obj n} (x : f⁻¹ y) :
    f⁻¹ (Y.map φ y) :=
  ⟨X.map φ x, by
    simp; change (X.map φ ≫ _) _ = _
    rw [f.hom.naturality, types_comp_apply, x.2]⟩

lemma FibreOrderIso_move {X' X Y : SSet} {f : X ⟶ₒ Y} {g : X' ⟶ₒ Y} (F : OrderIso f g)
  {n m: SimplexCategoryᵒᵖ} {y : Y.obj n} {φ : n ⟶ m} (x : f⁻¹ y) :
    F.FibreOrderIso _ (OrderIso.move φ x) = OrderIso.move φ (F.FibreOrderIso _ x) := by
  simp [FibreOrderIso, fibreEquiv, Fibre.trans, move]
  change (X.map φ ≫ F.hom.app m) _ = _
  rw [F.hom.naturality]; rfl

variable (f f') in
structure Pieces where
  orderIso {n : SimplexCategoryᵒᵖ} (y : Y.obj n) : f⁻¹ y ≃o f'⁻¹ y
  compatible {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    {y : Y.obj n} (x : f⁻¹ y) :
      orderIso (Y.map φ y) (move φ x) = move φ (orderIso y x)

variable (P : Pieces f f')

lemma Pieces.compatible_val {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
  {y : Y.obj n} (x : f⁻¹ y) :
    (P.orderIso (Y.map φ y) (move φ x)).val = X'.map φ (P.orderIso y x) :=
  congrArg Subtype.val (P.compatible _ _)

lemma Pieces.symm_compatible {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
  {y : Y.obj n} (x : f'⁻¹ y) :
    (P.orderIso (Y.map φ y)).symm (move φ x) = move φ ((P.orderIso y).symm x) := by
  apply_fun P.orderIso _
  simp only [OrderIso.apply_symm_apply, P.compatible]

lemma Pieces.symm_compatible_val {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
  {y : Y.obj n} (x : f'⁻¹ y) :
    ((P.orderIso (Y.map φ y)).symm (move φ x)).val = X.map φ ((P.orderIso y).symm x) :=
  congrArg Subtype.val (P.symm_compatible _ _)

lemma Pieces.orderIso_congr {y y' : Y.obj n} (h : y = y')
  {x : f⁻¹ y} {x' : f⁻¹ y'} (h' : HEq x x'):
    (P.orderIso y x).val = ↑(P.orderIso y' x') := by
  cases h; cases h'; rfl

lemma congrTemp {y y' : Y.obj n} {x : X.obj n} (eq : y = y') {h} {h'} :
    HEq (⟨x, h⟩ : f⁻¹ y) (⟨x, h'⟩ : f⁻¹ y') := by
  cases eq; rfl

@[simp, simps]
def ofPiece.hom : X ⟶ X' where
  app := fun n x ↦ (P.orderIso (f.hom.app n x) ⟨x, rfl⟩).val
  naturality := by
    intro n m φ
    ext x; simp
    convert P.compatible_val φ ⟨x, rfl⟩ using 1
    have : f.hom.app m (X.map φ x) = Y.map φ (f.hom.app n x) := by
      change (X.map φ ≫ _) x = _
      rw [f.hom.naturality]; rfl
    apply P.orderIso_congr
    . exact this
    . apply congrTemp this

lemma Pieces.orderIso_symm_congr {y y' : Y.obj n} (h : y = y')
  {x : f'⁻¹ y} {x' : f'⁻¹ y'} (h' : HEq x x'):
    ((P.orderIso y).symm x).val = ↑((P.orderIso y').symm x') := by
  cases h; cases h'; rfl

@[simp, simps]
def ofPiece.inv : X' ⟶ X where
  app := fun n x ↦ ((P.orderIso (f'.hom.app n x)).symm ⟨x, rfl⟩).val
  naturality := by
    intro n m φ
    ext x; simp
    convert P.symm_compatible_val φ ⟨x, rfl⟩ using 1
    have : f'.hom.app m (X'.map φ x) = Y.map φ (f'.hom.app n x) := by
      change (X'.map φ ≫ _) x = _
      rw [f'.hom.naturality]; rfl
    apply P.orderIso_symm_congr
    . exact this
    . apply congrTemp this

lemma symm_apply_apply_of_eq {y y' : Y.obj n} {x : f⁻¹ y'} (eq : y = y') {h} :
    ((P.orderIso y).symm ⟨P.orderIso y' x, h⟩).val = x.val := by
  cases eq; simp

lemma apply_symm_apply_of_eq {y y' : Y.obj n} {x : f'⁻¹ y} (eq : y = y') {h} :
    ((P.orderIso y') ⟨(P.orderIso y).symm x, h⟩).val = x.val := by
  cases eq; simp

def ofPiece : OrderIso f f' where
  hom := ofPiece.hom P
  inv := ofPiece.inv P
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
    apply P.orderIso_congr x.2 (congrTemp x.2)

end OrderIso

end WellOrdered

noncomputable section UniversalSimplicialSet

variable {α : Cardinal.{u}} {X Y : SSet.{u}}  {reg : Cardinal.IsRegular α}

namespace WellOrdered

variable (α) in
structure SmallWO (Y : SSet.{u}) where
  of : SSet.{u}
  wo : of ⟶ₒ Y
  small : ∀ ⦃n⦄, ∀ y : Y.obj n, Cardinal.mk (wo⁻¹ y) < α

abbrev SmallWO.hom (f : SmallWO α Y) := f.wo.hom

def SmallWO.rel {α} (f g : SmallWO α Y) : Prop :=
  Nonempty (OrderIso f.2 g.2)

def SmallWO.rel_iseqv {α} : Equivalence (SmallWO.rel (Y := Y) (α := α)) where
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
  iseqv := SmallWO.rel_iseqv

def Ω_obj₀ (α) (Y) := Quotient (@Setoid_SmallWO Y α)

section Smallness
open Function

-- size issue here
-- use `Small` to circumvent this temporarily
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
  {n} (y : X.obj n) :
    Fibre S.toHom y ≃ Quotient.out ((equivShrink ↑(Iio α)).symm (S.fibre y)).val :=
  (Sigma.EquivFstPreimage _ (fun x ↦ ((equivShrink _).symm (S.fibre x)).1.out) y).symm

lemma SmallFibresWithStructures.cardinal_mk_fibre_to_hom_lt
  (S : SmallFibresWithStructures α X) {n} (y : X.obj n) :
    Cardinal.mk (Fibre S.toHom y) < α := by
  rw [Cardinal.mk_congr (S.FibreToHomEquiv y)]
  simp only [Cardinal.mk_out]
  exact ((equivShrink ↑(Iio α)).symm (S.fibre y)).2

@[simp]
def SmallFibresWithStructures.toWO (S : SmallFibresWithStructures α X) :
    S.toSSet ⟶ₒ X where
  hom := S.toHom
  ord {_ y} := LinearOrder.ofEquiv (S.order y) (S.FibreToHomEquiv y).symm
  isWellOrder :=
    LinearOrder.ofEquiv.isWellOrderOfIsWellOrder _ _ (S.isWellOrder _)

@[simp]
def SmallFibresWithStructures.toSmallWO (S : SmallFibresWithStructures α X) :
    SmallWO α X where
  wo := S.toWO
  small {_} _ := S.cardinal_mk_fibre_to_hom_lt _

variable (α X) in
def SmallFibresWithStructures.to (S : SmallFibresWithStructures α X) :
    Ω_obj₀ α X := ⟦S.toSmallWO⟧

def SmallWO.FibreToHomEquiv (a : SmallWO α X):
    Quotient.out ((equivShrink ↑(Iio α)).symm ((equivShrink ↑(Iio α))
      ⟨Cardinal.mk ↑(Fibre a.wo.hom x), a.small x⟩)).val ≃
        ↑(Fibre a.wo.hom x) := by
  simp only [Equiv.symm_apply_apply]
  apply Cardinal.outMkEquiv

lemma aux {a : SmallWO α X} {x y : X.obj n} (eq : x = y)
  {s : Quotient.out ((equivShrink ↑(Iio α)).symm ((equivShrink ↑(Iio α))
      ⟨Cardinal.mk ↑(Fibre a.wo.hom x), a.small x⟩)).val} {h} :
    HEq (a.FibreToHomEquiv.symm (⟨(a.FibreToHomEquiv s).val, h⟩ : Fibre a.wo.hom y)) s := by
  cases eq
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply, heq_eq_eq]

lemma aux' {a : SmallWO α X} {x y : X.obj n} (eq : x = y)
  {s : Fibre a.wo.hom x} {s' : Fibre a.wo.hom y} (eq' : HEq s s'):
    HEq (a.FibreToHomEquiv.symm s) (a.FibreToHomEquiv.symm s') := by
  cases eq
  cases eq'
  rfl

lemma aux'₂ {a : SmallWO α X} {x y : X.obj n} (eq : x = y)
  {s : Quotient.out ((equivShrink ↑(Iio α)).symm ((equivShrink ↑(Iio α))
      ⟨Cardinal.mk ↑(Fibre a.wo.hom x), a.small x⟩)).val}
  {s' : Quotient.out ((equivShrink ↑(Iio α)).symm ((equivShrink ↑(Iio α))
      ⟨Cardinal.mk ↑(Fibre a.wo.hom y), a.small y⟩)).val} (eq' : HEq s s'):
    HEq (a.FibreToHomEquiv s) (a.FibreToHomEquiv s') := by
  cases eq
  cases eq'
  rfl

lemma aux'' {a : SmallWO α X} {x x' : X.obj n} {b b' : a.of.obj n} {h} {h'}
  (eq : x = x') (eq' : b = b') :
    HEq (⟨b, h⟩ : Fibre a.wo.hom x) (⟨b', h'⟩ : Fibre a.wo.hom x') := by
  cases eq
  cases eq'
  rfl

@[simp]
def SmallWO.toSmallFibresWithStructures (a : SmallWO α X) :
    SmallFibresWithStructures α X where
  fibre {n} x := equivShrink _
      ⟨Cardinal.mk (a.wo.fibre x), a.small x⟩
  map {n m} φ x :=
    ⟨X.map φ x.fst, a.FibreToHomEquiv.symm ((Fibre.map φ (a.FibreToHomEquiv x.snd)))⟩
  map_nat {n m f} x := by simp
  map_id {n} := by
    ext x
    . simp
    . simp [Fibre.map]
      apply aux (FunctorToTypes.map_id_apply _ _).symm
  map_comp {n m k} φ ψ := by
    ext x
    . simp
    . simp [Fibre.map]
      apply aux' (FunctorToTypes.map_comp_apply _ _ _ _)
        (aux'' (FunctorToTypes.map_comp_apply _ _ _ _) rfl)
  order _ := LinearOrder.ofEquiv a.wo.ord a.FibreToHomEquiv.symm
  isWellOrder _ := LinearOrder.ofEquiv.isWellOrderOfIsWellOrder _ _ a.wo.isWellOrder

@[simp]
def SmallWO.toSmallFibresWithStructures_equivObj (a : SmallWO α X) (n : SimplexCategoryᵒᵖ) :
    (x : X.obj n) ×
      Quotient.out ((equivShrink ↑(Iio α)).symm ((equivShrink ↑(Iio α))
        ⟨Cardinal.mk ↑(Fibre a.wo.hom x), a.small _⟩)).val
          ≃ a.of.obj n where
  toFun s := (a.FibreToHomEquiv s.snd).val
  invFun x := ⟨a.hom.app _ x, a.FibreToHomEquiv.symm ⟨x, rfl⟩⟩
  left_inv s := by
    have : a.hom.app n (a.FibreToHomEquiv s.snd).val = s.fst := (a.FibreToHomEquiv s.snd).2
    ext; all_goals simp
    . exact this
    . apply aux this.symm
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
      have : a.hom.app n (a.of.map φ x) = X.map φ (a.hom.app m x) := by
        change (a.of.map φ ≫ _) x = _
        rw [a.hom.naturality]; rfl
      refine ⟨this, ?_⟩
      apply aux' this
      simp [Fibre.map]
      apply aux'' this rfl
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
    simp only [WellOrderedHom.fibre, SmallFibresWithStructures.toSmallWO,
      SmallFibresWithStructures.toSSet, SmallFibresWithStructures.toWO,
      SmallFibresWithStructures.toHom, SimplexCategory.len_mk, Iso]
    erw [NatTrans.vcomp_app]
    exact (a.FibreToHomEquiv x.snd).2.symm
  mono {n y} b₁ b₂ h:= by
    simp [Fibre.trans, Iso]
    erw [LinearOrder.ofEquiv_le_iff_le, Equiv.symm_symm,
         LinearOrder.ofEquiv_le_iff_le, Equiv.symm_symm] at h
    convert h
    . exact b₁.2
    . exact aux'₂ b₁.2 (cast_heq _ _).symm
    . exact b₂.2
    . exact aux'₂ b₂.2 (cast_heq _ _).symm

lemma SmallFibresWithStructures.surj : Surjective (SmallFibresWithStructures.to α X) := by
  apply Quotient.ind
  intro a
  use a.toSmallFibresWithStructures
  dsimp [SmallFibresWithStructures.to]
  erw [Quotient.eq]
  exact ⟨SmallWO.toSmallFibresWithStructures.OrderIso a⟩

instance : Small.{u, u + 1} (Ω_obj₀ α X) :=
  @small_of_surjective _ _ (by infer_instance) _ SmallFibresWithStructures.surj

end Smallness

variable (α Y) in
abbrev Ω_obj := Shrink (Ω_obj₀ α Y)

def Ω_obj.mk (a : SmallWO α Y) : Ω_obj α Y :=
   equivShrink (Ω_obj₀ α Y) ⟦a⟧

lemma Ω_obj.mk_eq_mk_iff_equiv (a b : SmallWO α Y) :
    Ω_obj.mk a = Ω_obj.mk b ↔ a ≈ b := by
  simp [mk]; exact Quotient.eq

lemma Ω_obj.mk_sound {a b : SmallWO α Y} :
    a ≈ b → Ω_obj.mk a = Ω_obj.mk b := by
  intro h
  simp only [mk, EmbeddingLike.apply_eq_iff_eq]
  apply Quotient.sound h

-- define the functor, which acts on morphisms as pullback
noncomputable section map
variable (a : SmallWO α Y) (f : Y' ⟶ Y)

def SmallWO.pullback :
    SmallWO α Y' where
  of := Limits.pullback a.wo.hom f
  wo := {
    hom := pullback.snd a.wo.hom f
    ord := IsPullback.WellOrderedHom (IsPullback.of_hasPullback a.wo.hom f) _
    isWellOrder := IsPullback.WellOrderedHom.isWellOrder _ _
  }
  small n y := by
    convert a.small (f.app _ y) using 1
    exact Quotient.sound ⟨(IsPullback.of_hasPullback a.wo.hom f).fibreEquiv y⟩

-- RelIso on fibres via pullback
def SmallWO.pullback_RelIso' {n} (y' : Y'.obj n):
    (a.pullback f).wo⁻¹ y' ≃o a.wo⁻¹ (f.app _ y') :=
  IsPullback.WellOrderedHom.OrderIso (IsPullback.of_hasPullback a.wo.hom f) y'

def SmallWO.pullback_RelIso {n} (y : Y.obj n) (y' : Y'.obj n)
  (h : f.app _ y' = y) :
    (a.pullback f).wo⁻¹ y' ≃o a.wo⁻¹ y :=
  (a.pullback_RelIso' f y').trans (RelIso.cast (by cases h; rfl) (by cases h; rfl))

lemma SmallWO.pullback_RelIso_move {n m} (y : Y.obj n) (y' : Y'.obj n) (h : f.app _ y' = y)
  (φ : n ⟶ m) (x : (a.pullback f).wo⁻¹ y') {h'}:
    a.pullback_RelIso f (Y.map φ y) (Y'.map φ y') h' (OrderIso.move φ x) =
  OrderIso.move φ (a.pullback_RelIso f y y' h x) := by
    cases h
    simp [pullback_RelIso, pullback_RelIso', IsPullback.WellOrderedHom.OrderIso,
          IsPullback.fibreEquiv, TypesPullbackPreimageEquiv, OrderIso.move,
          hom_naturality_apply]
    erw [hom_naturality_apply] -- this is weird

lemma SmallWO.pullback_RelIso_symm_move {n m} (y : Y.obj n) (y' : Y'.obj n) (h : f.app _ y' = y)
  (φ : n ⟶ m) (x : a.wo⁻¹ y) {h'}:
    (a.pullback_RelIso f (Y.map φ y) (Y'.map φ y') h').symm (OrderIso.move φ x) =
  OrderIso.move φ ((a.pullback_RelIso f y y' h).symm x) := by
    apply_fun (a.pullback_RelIso f (Y.map φ y) (Y'.map φ y') h')
    rw [a.pullback_RelIso_move _ _ _ h]
    simp only [OrderIso.apply_symm_apply]

lemma SmallWO.pullback_id :
    a.pullback (𝟙 Y) ≈ a := by
  have : IsIso (pullback.fst a.hom (𝟙 Y)) := by
    sorry -- `IsPullback.isIso_fst_of_mono` in latest version of Mathlib
  exact ⟨{
    toIso := asIso (pullback.fst a.wo.hom (𝟙 Y))
    comm := by simp [pullback.condition]; rfl
    mono := by
      intro _ y _ _ h
      rwa [IsPullback.WellOrderedHom.le_iff_le] at h
  }⟩

lemma SmallWO.pullback_comp {f : Z ⟶ Y} {g : W ⟶ Z} :
    (a.pullback f).pullback g ≈ a.pullback (g ≫ f):= by
  let is := IsPullback.of_hasPullback a.hom (g ≫ f)
  let is' := IsPullback.paste_horiz (IsPullback.of_hasPullback (pullback.snd a.hom f) g)
    (IsPullback.of_hasPullback a.hom f)
  exact ⟨{
    toIso := is'.isoIsPullback is
    comm := by erw [IsPullback.isoIsPullback_hom_snd]; rfl
    mono := by
      intro n y b c h
      rw [IsPullback.WellOrderedHom.le_iff_le,
          IsPullback.WellOrderedHom.le_iff_le] at h
      rw [IsPullback.WellOrderedHom.le_iff_le]
      convert h using 1
      all_goals
      simp [IsPullback.fibreEquiv, TypesPullbackPreimageEquiv, OrderIso.fibreTrans,
            Fibre.trans]
      change (_ ∘ _) _ = (_ ∘ _) _
      rw [← types_comp, ← types_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
          IsPullback.isoIsPullback_hom_fst]
      rfl
  }⟩

variable {f} in
lemma SmallWO.pullback_sound {a b : SmallWO α Y} :
    a ≈ b → a.pullback f ≈ b.pullback f
| ⟨h⟩ => ⟨{
    toIso := asIso (pullback.map a.hom f b.hom f h.hom (𝟙 _) (𝟙 _)
      (by simp [h.comm]) (by simp))
    comm := by simp; erw [pullback.lift_snd, Category.comp_id]; rfl
    mono := by
      intro n y c d hcd
      rw [IsPullback.WellOrderedHom.le_iff_le, h.le_iff_le] at hcd
      rw [IsPullback.WellOrderedHom.le_iff_le]
      convert hcd
      all_goals
      simp [IsPullback.fibreEquiv, TypesPullbackPreimageEquiv, OrderIso.fibreTrans,
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
lemma SmallWO.Ω_map_Ω_obj_mk :
  Ω_map α f (Ω_obj.mk a) =  Ω_obj.mk (a.pullback f) := by
    simp only [Ω_obj.mk, Ω_map, Shrink.rec, Equiv.symm_apply_apply, eq_rec_constant]
    erw [Quotient.lift_mk, Function.comp_apply]
    rfl

lemma Ω_map_id : Ω_map α (𝟙 Y) = 𝟙 (Ω_obj α Y) := by
  ext a; revert a
  apply Shrink.rec; apply Quotient.ind
  intro a
  simp only [types_id_apply, EmbeddingLike.apply_eq_iff_eq]
  erw [SmallWO.Ω_map_Ω_obj_mk]
  exact Ω_obj.mk_sound (SmallWO.pullback_id _)

lemma Ω_map_comp {f : Y ⟶ Y'} {g : Y' ⟶ Y''}:
    (Ω_map α g) ≫ (Ω_map α f) = Ω_map α (f ≫ g) := by
  ext a; revert a
  apply Shrink.rec; apply Quotient.ind
  intro a
  simp only [types_comp_apply, EmbeddingLike.apply_eq_iff_eq]
  erw [SmallWO.Ω_map_Ω_obj_mk, SmallWO.Ω_map_Ω_obj_mk, SmallWO.Ω_map_Ω_obj_mk]
  apply Ω_obj.mk_sound a.pullback_comp

end map

variable (α)

def Ω : SSetᵒᵖ ⥤ Type u where
  obj Y := Ω_obj α (unop Y)
  map f := Ω_map α (unop f)
  map_id Y := by simp; rw [← Ω_map_id]; congr -- rw does not work....
  map_comp f g:= by simp; rw [Ω_map_comp]; congr

section
open Function Classical
variable [UnivLE.{v, u}] {J : Type v} [Category.{w,v} J] {F : J ⥤ SSet.{u}ᵒᵖ}
  (c : Cone F) (hc : IsLimit c)

abbrev Ω.PreservesLimitHomToLimit :
    (Ω α).mapCone c ⟶ limit.cone (F ⋙ Ω α) where
  hom := limit.lift _ _
  w := limit.lift_π _

lemma Ω.PreservesLimitHomToLimit_hom_π (f : Ω_obj α (unop c.pt)) (j : J) :
    limit.π (F ⋙ Ω α) j (limit.lift (F ⋙ Ω α) ((Ω α).mapCone c) f) =
      (Ω α).map (c.π.app j) f :=
  congrFun (limit.lift_π ((Ω α).mapCone c) j) _

def Ω.auxExtPieceOrderIso' (f g : SmallWO α c.pt.unop)
  (h : (j : J) → (OrderIso (f.pullback (c.π.app j).unop).wo (g.pullback (c.π.app j).unop).wo))
  {n : SimplexCategoryᵒᵖ} (y : (unop c.pt).obj n)
  (j : J) (x : (F.obj j).unop.obj n) (hx : (c.π.app j).unop.app _ x = y):
    f.wo⁻¹ y ≃o g.wo⁻¹ y := by
  let r₁ := f.pullback_RelIso (c.π.app j).unop y x hx
  let r₂ := (h j).FibreOrderIso x
  let r₃ := g.pullback_RelIso (c.π.app j).unop y x hx
  exact (r₁.symm.trans r₂).trans r₃

variable {α c} in
omit [UnivLE.{v, u}] in
lemma Ω.auxExtPieceOrderIso'_ext {f g : SmallWO α c.pt.unop}
  {h : (j : J) → (OrderIso (f.pullback (c.π.app j).unop).wo (g.pullback (c.π.app j).unop).wo)}
  {n : SimplexCategoryᵒᵖ} {y : (unop c.pt).obj n}
  (j : J) (x : (F.obj j).unop.obj n) (hx : (c.π.app j).unop.app _ x = y)
  (j' : J) (x' : (F.obj j').unop.obj n) (hx' : (c.π.app j').unop.app _ x' = y) :
    auxExtPieceOrderIso' α c f g h y j x hx = auxExtPieceOrderIso' α c f g h y j' x' hx' :=
  IsWellOrder.OrderIso_eq _ _ _ _

#check Types.jointly_surjective
lemma Ω.jointly_surjective {n : SimplexCategoryᵒᵖ} (x : (unop c.pt).obj n) :
  ∃ (j : J) (y : (F.obj j).unop.obj n), (c.π.app j).unop.app _ y = x := sorry

def Ω.auxExtPieceOrderIso (f g : SmallWO α c.pt.unop)
  (h : (j : J) → (OrderIso (f.pullback (c.π.app j).unop).wo (g.pullback (c.π.app j).unop).wo))
  {n : SimplexCategoryᵒᵖ} (y : (unop c.pt).obj n) :
    f.wo⁻¹ y ≃o g.wo⁻¹ y := by
  let j := choose (jointly_surjective c y)
  let x := choose (choose_spec (jointly_surjective c y))
  let hx := choose_spec (choose_spec (jointly_surjective c y))
  exact auxExtPieceOrderIso' α c f g h y j x hx

def Ω.auxExtPiece (f g : SmallWO α c.pt.unop)
  (h : (j : J) → (OrderIso (f.pullback (c.π.app j).unop).wo (g.pullback (c.π.app j).unop).wo)):
    OrderIso.Pieces f.wo g.wo where
  orderIso := auxExtPieceOrderIso α c f g h
  compatible := by
    intro n m φ y y'
    let j := choose (jointly_surjective c y)
    let x := choose (choose_spec (jointly_surjective c y))
    let hx := choose_spec (choose_spec (jointly_surjective c y))
    let j' := choose (jointly_surjective c ((unop c.pt).map φ y))
    let x' := choose (choose_spec (jointly_surjective c ((unop c.pt).map φ y)))
    let hx' := choose_spec (choose_spec (jointly_surjective c ((unop c.pt).map φ y)))
    let x₂ := (F.obj j).unop.map φ x
    have hx₂ : (c.π.app j).unop.app m x₂ = c.pt.unop.map φ y := by
      change ((F.obj j).unop.map φ ≫ (c.π.app j).unop.app m) x = _
      rw [(c.π.app j).unop.naturality, ← hx]; rfl
    change auxExtPieceOrderIso' α c f g h _ j' x' hx' _ =
      OrderIso.move φ (auxExtPieceOrderIso' α c f g h _ j x hx y')
    rw [auxExtPieceOrderIso'_ext _ _ _ j x₂ hx₂]
    dsimp [auxExtPieceOrderIso']
    rw [f.pullback_RelIso_symm_move _ _ _ hx, OrderIso.FibreOrderIso_move,
        g.pullback_RelIso_move _ _ _]

def Ω.auxExt (f g : SmallWO α c.pt.unop)
  (h : ∀ j : J, f.pullback (c.π.app j).unop ≈ g.pullback (c.π.app j).unop) :
    OrderIso f.wo g.wo :=
  OrderIso.ofPiece (auxExtPiece α c f g (fun j ↦ choice (h j)))

lemma Ω.PreservesLimitHomToLimit_hom_injective :
    (limit.lift (F ⋙ Ω α) ((Ω α).mapCone c)).Injective := by
  apply Shrink.rec; apply Quotient.ind; intro f
  apply Shrink.rec; apply Quotient.ind; intro g h
  have (j) := congrArg (limit.π (F ⋙ Ω α) j) h
  simp [PreservesLimitHomToLimit_hom_π] at this
  refine Ω_obj.mk_sound ⟨auxExt α c f g ?_⟩
  intro j; specialize this j
  change (Ω α).map (c.π.app j) (Ω_obj.mk _) = (Ω α).map (c.π.app j) (Ω_obj.mk _) at this
  simp [Ω, Ω_obj.mk_eq_mk_iff_equiv] at this
  exact this

lemma Ω.PreservesLimitHomToLimit_hom_surjective :
    (limit.lift (F ⋙ Ω α) ((Ω α).mapCone c)).Surjective := sorry

instance : IsIso (Ω.PreservesLimitHomToLimit α c).hom :=
  (isIso_iff_bijective _).mpr ⟨Ω.PreservesLimitHomToLimit_hom_injective _ _,
        Ω.PreservesLimitHomToLimit_hom_surjective _ _⟩

instance : IsIso (Ω.PreservesLimitHomToLimit α c) := Cones.cone_iso_of_hom_iso _

instance Ω.PreservesLimit :
    PreservesLimit F (Ω α) where
  preserves {c} _ := IsLimit.ofIsoLimit (limit.isLimit _)
      (asIso (PreservesLimitHomToLimit α c)).symm

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
  erw [← yonedaEquiv_naturality (n := x.unop.unop.fst.unop.len) (m := y.unop.unop.fst.unop.len)]
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
  rw [← Quotient.eq]
  apply_fun equivShrink (Ω_obj₀ α _)
  change Ω_obj.mk _ = Ω_obj.mk _
  rw [← SmallWO.Ω_map_Ω_obj_mk]
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
  erw [SmallWO.Ω_map_Ω_obj_mk, ← SmallWO.Kan_iff_Ω_obj_mk_Kan, ← SmallWO.Kan_iff_Ω_obj_mk_Kan]
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
  rw [← Quotient.eq, Quotient.out_eq]
  apply_fun (equivShrink (Ω_obj₀ α (U α)))
  simp only [Equiv.apply_symm_apply, UniSmallWOKan₀,
      ← UniSmallWO.Ω_obj_mk, SmallWO.Ω_map_Ω_obj_mk]
  rfl

variable (α)
abbrev U' := (UniSmallWOKan α).of

abbrev UniWOKan : U' α ⟶ₒ U α := (UniSmallWOKan α).wo

variable {α}

lemma U.toW.simplex_comp_eq_toHom_val {k : ℕ} (σ : Δ[k] ⟶ U α):
    σ ≫ U.toW α = Ω.toHom (((U α).yonedaEquiv [k]) σ).val := by
  rw [← app_eq_val, yonedaEquiv_naturality', ← Ω.toObj.simplex, Ω.toHom_toObj]

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
  ⟨WellOrdered.UniSmallWOKan₀ α, UniSmallWOKan₀.Kan⟩

lemma factor_iff_forall_Kan (f : Y ⟶ W α) :
    (∃ φ, f = φ ≫ U.toW α) ↔ (∀ ⦃k⦄ (x : Y _[k]), (f.app _ x).Kan) := by
  constructor
  . intro ⟨φ, h⟩ k x
    rw [h, Ω_obj.Kan_iff_pullback_snd_toHom_Kan,
        yonedaEquiv_symm_naturality', ← Ω.toObj.simplex, Ω.toHom_toObj,
        ← Category.assoc, ← yonedaEquiv_symm_naturality'₂]
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
    rw [yonedaEquiv_symm_naturality', Ω_obj.Kan_iff_pullback_snd_toHom_Kan, ← Ω.toObj.simplex,
       Ω.toHom_toObj, ← pullback.rightCompIso_hom_comp_snd]
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
      SmallWO.Ω_map_Ω_obj_mk]

lemma UniSmallWOKan.universal' (g : SmallWO α X) (hg : g.Kan) :
    g ≈  (UniSmallWOKan α).pullback (Υ.toHom (Υ_obj.mk g hg)):= by
  rw [← Quotient.eq]
  apply_fun equivShrink (Ω_obj₀ α _)
  exact congrArg Subtype.val (universal g hg)

end WellOrdered
end UniversalSimplicialSet

end SSet
