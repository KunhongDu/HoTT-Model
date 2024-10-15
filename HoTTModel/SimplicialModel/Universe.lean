import HoTTModel.SSet.Fibrations
import HoTTModel.RepresentableBy
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality

-- This file aims to construct a universe in sSet
open Simplicial CategoryTheory Opposite Limits Functor Set

universe u

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

abbrev Fibre {n : ℕ} (y : Y _[n]) : Set (X _[n]) :=
  (f.app (op [n])) ⁻¹' {y}

def _root_.CategoryTheory.IsPullback.fibreEquiv {P X Y Z : SSet}
  {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (D : IsPullback fst snd f g) {n : ℕ} (y : Y _[n]) :
    Fibre snd y ≃ Fibre f (g.app _ y) :=
  CategoryTheory.TypesPullbackPreimageEquiv (IsPullback.map (ev n) D) _

end Fibre

section WellOrdered
variable {X Y : SSet.{u}} (f : X ⟶ Y)
-- decide to use PartialOrder -- Preorder doesn't have antisymmetric for `≤`
variable (X Y) in
structure WellOrderedHom where
  hom : X ⟶ Y
  ord {n : ℕ} {y : Y _[n]} : LinearOrder (Fibre hom y)
  well_ord {n : ℕ} {y : Y _[n]} : IsWellOrder _ ((ord (y := y)).lt)
-- ParitialOrder + WellOrder should be LinearOrder
-- but not show about how to define the instance so that
-- the defintion of relations are compatible
-- for now, use LinearOrder

abbrev WellOrderedHom.fibre (f : WellOrderedHom X Y) {n : ℕ} (y : Y _[n]) := Fibre f.hom y

-- why isn't wellOrder a class like partialOrder

attribute [instance] WellOrderedHom.ord WellOrderedHom.well_ord

notation X " ⟶ₒ " Y => WellOrderedHom X Y

infix:80 "⁻¹ " => WellOrderedHom.fibre
-- notation: f "⁻¹" y => ... gives wrong display on inforview

section Pullback_Fibre_WellOrdered
variable {P X Y Z : SSet} {h : P ⟶ X} {i : P ⟶ Y} {f : X ⟶ₒ Z} {g : Y ⟶ Z}
  (D : IsPullback h i f.hom g) {n : ℕ} (y : Y _[n])

noncomputable def IsPullback.WellOrderedHom  :
    LinearOrder (Fibre i y) where
      le a b := D.fibreEquiv y a ≤ D.fibreEquiv y b
      le_refl _ := le_refl _
      le_trans _ _ _ := le_trans
      le_antisymm _ _ h h' := by
        rw [← (D.fibreEquiv y).apply_eq_iff_eq]
        apply le_antisymm h h'
      le_total _ _ := le_total _ _
      decidableLE _ _ := LinearOrder.decidableLE _ _
      decidableEq a b := by
        rw [← (D.fibreEquiv y).apply_eq_iff_eq]
        apply LinearOrder.decidableEq _ _ -- this should be default??

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

def IsPullback.WellOrderedHom.isWellOrder :
    IsWellOrder _ (IsPullback.WellOrderedHom D y).lt :=
  (ltRelIso D y).toRelEmbedding.isWellOrder

--- you really should read the proof of
#check RelEmbedding.acc

end Pullback_Fibre_WellOrdered

def Fibre.trans {f : X ⟶ Y} {f' : X' ⟶ Y} (g : X ⟶ X')
    (comm : f = g ≫ f') {y : Y _[n]} (a : (Fibre f y)): (Fibre f' y) :=
  ⟨g.app _ a, comm.symm ▸ a.2⟩

-- can't find: nonempty set in a well order has a least element

lemma Fibre.eq_iff_trans_eq_of_iso {f : X ⟶ Y} {f' : X' ⟶ Y} (F : Iso X X') {y : Y _[n]}
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

lemma _root_.IsWellOrder.OrderIso_eq (α β: Type) [Preorder α] [Preorder β]
  [IsWellOrder α (· < ·)] [IsWellOrder β (· < ·)] (f g : α ≃o β) : f = g := by
  ext
  apply IsWellOrder.OrderIso_apply_eq

@[ext]
structure OrderIso (f : X ⟶ₒ Y) (f' : X' ⟶ₒ Y) extends Iso X X' where
  comm : f.1 = hom ≫ f'.1
  mono {y : Y _[n]} : Monotone $ Fibre.trans hom comm (y := y)

namespace OrderIso
variable {f : X ⟶ₒ Y} {f' : X' ⟶ₒ Y}

lemma comm_inv (F : OrderIso f f') :
    F.inv ≫ f.hom = f'.hom :=
  (Iso.inv_comp_eq _).mpr F.comm

lemma ext' (F G : OrderIso f f') (w : F.hom = G.hom) :
    F = G := by
  have := Iso.ext w
  ext1 <;> rw [this]

def fibreTrans (F : OrderIso f f') {n : ℕ} {y : Y _[n]} := Fibre.trans F.hom F.comm (y := y)

def fibreEquiv (F : OrderIso f f') {n : ℕ} (y : Y _[n]) :
    ↑(f⁻¹ y) ≃ ↑(f'⁻¹ y) where
  toFun := Fibre.trans F.hom F.comm -- change to fibreTrans
  invFun := Fibre.trans F.inv F.comm_inv.symm
  left_inv := by intro; simp [Fibre.trans]
  right_inv := by intro; simp [Fibre.trans]

lemma strictMono (F : OrderIso f f') {y : Y _[n]} :
    StrictMono $ F.fibreTrans (y := y) :=
  F.mono.strictMono_of_injective (F.fibreEquiv _).injective

lemma lt_iff_lt {F : OrderIso f f'} {n : ℕ} {y : Y _[n]} (a b : f⁻¹ y) :
    a < b ↔ F.fibreTrans a < F.fibreTrans b :=
  F.strictMono.lt_iff_lt.symm

lemma le_iff_le {F : OrderIso f f'} {n : ℕ} {y : Y _[n]} (a b : f⁻¹ y) :
    a ≤ b ↔ F.fibreTrans a ≤ F.fibreTrans b :=
  F.strictMono.le_iff_le.symm

def symm {f : X ⟶ₒ Y} {f' : X' ⟶ₒ Y} (F : OrderIso f f') : OrderIso f' f := {
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
def FibreOrderIso {f : X ⟶ₒ Y} {g : X' ⟶ₒ Y} (F : OrderIso f g) {n : ℕ} (y : Y _[n]) :
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

end OrderIso

end WellOrdered

noncomputable section UniversalSimplicialSet

variable {α : Cardinal.{u}} {X Y : SSet}  {reg : Cardinal.IsRegular α}

namespace WellOrdered

variable (α) in
structure SmallWO (Y : SSet) where
  of : SSet
  wo : of ⟶ₒ Y
  small : ∀ ⦃n⦄, ∀ y : Y _[n], Cardinal.mk (wo⁻¹ y) < α

abbrev SmallWO.hom (f : SmallWO α Y) := f.wo.hom

def SmallWO.rel {α} (f g : SmallWO α Y) : Prop :=
  Nonempty (OrderIso f.2 g.2)

-- this is really easy tho
def SmallWO.rel_iseqv {α} : Equivalence (SmallWO.rel (Y := Y) (α := α)) := sorry

instance Setoid_SmallWO {α} : Setoid (SmallWO α Y) where
  r := SmallWO.rel
  iseqv := SmallWO.rel_iseqv

def Ω_obj₀ (α) (Y) := Quotient (@Setoid_SmallWO Y α)

-- size issue here
-- use `Small` to circumvent this temporarily
instance : Small.{u, u + 1} (Ω_obj₀ α Y) := sorry

variable (α Y) in
abbrev Ω_obj := Shrink (Ω_obj₀ α Y)

def Ω_obj.mk (a : SmallWO α Y) : Ω_obj α Y :=
   equivShrink (Ω_obj₀ α Y) ⟦a⟧

lemma Ω_obj.mk_sound {a b : SmallWO α Y} :
    a ≈ b → Ω_obj.mk a = Ω_obj.mk b := by
  intro h
  simp only [mk, EmbeddingLike.apply_eq_iff_eq]
  apply Quotient.sound h

-- define the functor, which acts on morphisms as pullback
noncomputable section map
variable (f : Y' ⟶ Y)

def SmallWO.pullback (a : SmallWO α Y) :
    SmallWO α Y' where
  of := Limits.pullback a.wo.hom f
  wo := {
    hom := pullback.snd a.wo.hom f
    ord := IsPullback.WellOrderedHom (IsPullback.of_hasPullback a.wo.hom f) _
    well_ord := IsPullback.WellOrderedHom.isWellOrder _ _
  }
  small n y := by
    convert a.small (f.app _ y) using 1
    exact Quotient.sound ⟨(IsPullback.of_hasPullback a.wo.hom f).fibreEquiv y⟩

variable {f} in
lemma SmallWO.pullback_sound {a b : SmallWO α Y} :
    a ≈ b → SmallWO.pullback f a ≈ SmallWO.pullback f b := by
  sorry

variable (α) in
def Ω_map : Ω_obj α Y ⟶ Ω_obj α Y' :=
  Shrink.rec (Quotient.lift (Ω_obj.mk ∘ SmallWO.pullback f)
    (fun _ _ h ↦ Ω_obj.mk_sound (SmallWO.pullback_sound h)))

@[simp]
lemma SmallWO.Ω_map_Ω_obj_mk (a : SmallWO α Y) :
  Ω_map α f (Ω_obj.mk a) =  Ω_obj.mk (SmallWO.pullback f a) := by
    simp only [Ω_obj.mk, Ω_map, Shrink.rec, Equiv.symm_apply_apply, eq_rec_constant]
    erw [Quotient.lift_mk, Function.comp_apply]
    rfl

lemma Ω_map_id : Ω_map α (𝟙 Y) = 𝟙 (Ω_obj α Y) := sorry

lemma Ω_map_comp {f : Y ⟶ Y'} {g : Y' ⟶ Y''}:
    (Ω_map α g) ≫ (Ω_map α f) = Ω_map α (f ≫ g) := sorry

end map

variable (α)

def Ω : SSetᵒᵖ ⥤ Type u where
  obj Y := Ω_obj α (unop Y)
  map f := Ω_map α (unop f)
  map_id Y := by simp; rw [← Ω_map_id]; congr -- rw does not work....
  map_comp f g:= by simp; rw [Ω_map_comp]; congr

def W : SSet := standardSimplex.op ⋙ Ω α

instance Ω.PreservesLimitsOfSize [UnivLE.{v, u}] : PreservesLimitsOfSize.{w, v} (Ω α) := sorry

def Ω.Corepresentable : (Ω α).CorepresentableBy  (op (W α)) := sorry

def Ω.Corepresentable.app (X : SSet.{u}):
    (X ⟶ (W α)) ≃ (Ω α).obj (op X) :=
  Opposite.equivToOpposite.trans ((Ω.Corepresentable α).homEquiv (Y := op X))

variable {X : SSet.{u}} {α}

def toHom (a : (Ω α).obj (op X)) : X ⟶ W α := (Ω.Corepresentable.app α X).invFun a

def toObj (f : X ⟶ W α) : (Ω α).obj (op X) := (Ω.Corepresentable.app α X).toFun f

@[simp]
lemma toHom_toObj (f : X ⟶ W α) :
    toHom (toObj f) = f := (Ω.Corepresentable.app α X).left_inv _

@[simp]
lemma toObj_toHom (a : (Ω α).obj (op X)) :
    toObj (toHom a) = a := (Ω.Corepresentable.app α X).right_inv _

lemma toObj.simplex {n : ℕ} (f : Δ[n] ⟶ W α) :
    toObj f = yonedaEquiv _ _ f := sorry
-- this should follow from the explicit definition for the representation

variable (α)

abbrev UniSmallWO₀ := toObj (𝟙 (W α))

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
    g ≈ SmallWO.pullback (toHom (Ω_obj.mk g)) (UniSmallWO α) := by
  rw [← Quotient.eq]
  apply_fun equivShrink (Ω_obj₀ α _)
  change Ω_obj.mk _ = Ω_obj.mk _
  rw [← SmallWO.Ω_map_Ω_obj_mk]
  convert Ω.Corepresentable.universal (toHom (Ω_obj.mk g))
  . simp only [toObj_toHom]
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
    ∀ a : Ω_obj α Y, a.Kan ↔ (SmallWO.pullback (toHom a) (UniSmallWO α)).Kan := by
    apply Shrink.rec
    apply Quotient.ind
    intro a
    erw [← SmallWO.Kan_iff_Ω_obj_mk_Kan]
    exact Kan.sound_iff _ _ (UniSmallWO.universal a)

lemma Ω_obj.Kan_iff_pullback_snd_toHom_Kan (a : Ω_obj α Y) :
    a.Kan ↔ KanFibration (pullback.snd (UniSmallWO α).hom (toHom a)) := by
  rw [Kan_iff_pullback_toHom_Kan]; rfl

-- Greek `Υ`, not latin `Y`
variable (α) (Y) in
abbrev Υ_obj := {a : Ω_obj α Y // a.Kan}

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

abbrev UniSmallWOKan₀ := Ω_map α (U.toW α) (UniSmallWO₀ α)

abbrev UniSmallWOKan := Quotient.out $ (equivShrink (Ω_obj₀ α (U α))).symm (UniSmallWOKan₀ α)

variable {α}
lemma UniSmallWOKan₀.eq_toObj : UniSmallWOKan₀ α = toObj (U.toW α) :=
  (Ω.Corepresentable.universal _).symm

lemma UniSmallWOKan₀.toHom : toHom (UniSmallWOKan₀ α) = U.toW α := by
  rw [eq_toObj, toHom_toObj]

lemma UniSmallWOKan.Ω_obj_mk : Ω_obj.mk (UniSmallWOKan α) = UniSmallWOKan₀ α := by
  simp only [Ω_obj.mk, UniSmallWO, Quotient.out_eq, Equiv.apply_symm_apply]

lemma UniSmallWOKan.equiv_smallWO_pullback :
    UniSmallWOKan α ≈ SmallWO.pullback (U.toW α) (UniSmallWO α) := by
  rw [← Quotient.eq, Quotient.out_eq]
  apply_fun (equivShrink (Ω_obj₀ α (U α)))
  simp only [Equiv.apply_symm_apply, UniSmallWOKan₀,
      ← UniSmallWO.Ω_obj_mk, SmallWO.Ω_map_Ω_obj_mk]
  rfl

variable (α)
abbrev U' := (UniSmallWOKan α).of

abbrev UniWOKan : U' α ⟶ₒ U α := (UniSmallWOKan α).wo

variable {α}

lemma aux''' {k : ℕ} (x : U α _[k]) :
    x.val = (U.toW α).app _ x := by
  simp only [U.toW, FunctorToTypes.hcomp, NatTrans.id_app', FunctorToTypes.map_id_apply]
  rfl

lemma aux'' {k : ℕ} (σ : Δ[k] ⟶ U α):
    σ ≫ U.toW α = toHom (((U α).yonedaEquiv [k]) σ).val := by
  rw [aux''', yonedaEquiv_naturality', ← toObj.simplex, toHom_toObj]

lemma aux' {k : ℕ} (σ : Δ[k] ⟶ U α) :
    KanFibration (pullback.snd (UniWO α).hom (σ ≫ U.toW α)) := by
  have := (yonedaEquiv _ _ σ).property
  rwa [Ω_obj.Kan_iff_pullback_snd_toHom_Kan, ← aux''] at this

lemma aux : ∀ {k : ℕ} (σ : Δ[k] ⟶ U α),
    KanFibration (pullback.snd (UniWOKan α).hom σ) := by
  intro k σ
  have := aux' σ
  rw [← pullback.rightCompIso_hom_comp_snd] at this
  apply KanFibration.of_isIso_comp at this
  obtain ⟨h⟩ := UniSmallWOKan.equiv_smallWO_pullback (α := α)
  have comm : (UniWOKan α).hom =
    h.toIso.hom ≫ (pullback.snd (UniWO α).hom (U.toW α)) := h.comm
  rw [comm]
  rw [← pullback.leftCompIso_hom_comp_snd, ← Category.assoc]
  apply KanFibration.isIso_comp -- Lean has the instance that pullback.snd of iso is iso

instance UniWOKan.hom.KanFibration : KanFibration (UniWOKan α).hom :=
  KanFibration.of_forall_pullback_snd_KanFibration aux

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

lemma aux₂ (f : Y ⟶ W α) :
    (∃ φ, f = φ ≫ U.toW α) ↔ (∀ ⦃k⦄ (x : Y _[k]), (f.app _ x).Kan) := by
  constructor
  . intro ⟨φ, h⟩ k x
    rw [h, Ω_obj.Kan_iff_pullback_snd_toHom_Kan,
        yonedaEquiv_symm_naturality', ← toObj.simplex, toHom_toObj,
        ← Category.assoc, ← yonedaEquiv_symm_naturality'₂]
    apply aux'
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

lemma aux₂' (a : SmallWO α Y) :
    a.Kan ↔ ∃ φ, toHom (Ω_obj.mk a)  = φ ≫ U.toW α := by
  rw [SmallWO.Kan_iff_Ω_obj_mk_Kan, Ω_obj.Kan_iff_pullback_snd_toHom_Kan]
  constructor
  . rw [aux₂]; intro h k x
    rw [yonedaEquiv_symm_naturality', Ω_obj.Kan_iff_pullback_snd_toHom_Kan, ← toObj.simplex,
       toHom_toObj, ← pullback.rightCompIso_hom_comp_snd]
    apply KanFibration.isIso_comp' _ _ KanFibration.pullback_snd
  . intro ⟨φ, h⟩
    rw [h, ← pullback.rightCompIso_hom_comp_snd]
    apply KanFibration.isIso_comp' _ _ KanFibration.pullback_snd

example : ∀ a : Ω_obj α Y, a.Kan ↔ ∃ φ, toHom a  = φ ≫ U.toW α := by
  apply Shrink.rec
  apply Quotient.ind
  intro a
  convert aux₂' a
  exact (SmallWO.Kan_iff_Ω_obj_mk_Kan _).symm



end WellOrdered
end UniversalSimplicialSet

end SSet
