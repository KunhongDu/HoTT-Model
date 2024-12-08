import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import HoTTModel.Lemmas.Limits

/-
Almost copied from `https://github.com/sinhp/Poly/blob/master/Poly/LCCC/Basic.lean`
-/


namespace CategoryTheory

open Limits Over MonoidalCategory

universe v u

variable (C : Type u) [Category.{v, u} C] [HasFiniteWidePullbacks C]

class LocallyCartesianClosed where
  pushforward {X Y : C} (f : X ⟶ Y) : Over X ⥤ Over Y
  adj {X Y : C} (f : X ⟶ Y) : Over.pullback f ⊣ pushforward f

notation f"*" => Over.pullback f
notation "Π"f => LocallyCartesianClosed.pushforward f
notation "Σ"f => Over.map f

noncomputable instance (X : C) : ChosenFiniteProducts (Over X) :=
  ChosenFiniteProducts.ofFiniteProducts _

class OverCartesianClosed where
  over (X : C) : CartesianClosed (Over X)

attribute [instance] OverCartesianClosed.over

namespace LocallyCartesianClosed

noncomputable section
variable {C} {I : C} (f x : Over I)

def pullbackCompositionIsBinaryProduct [HasPullbacks C] :
    let pbleg1 : (Over.map f.hom).obj ((f.hom*).obj x) ⟶ f := homMk (pullback.snd _ _) rfl
    let pbleg2 : (Over.map f.hom).obj ((f.hom*).obj x) ⟶ x :=
    Over.homMk (pullback.fst _ _) (by simp [pullback.condition])
    IsLimit (BinaryFan.mk (pbleg1) (pbleg2)) := by
  fconstructor
  case lift =>
    intro s
    apply Over.homMk _ _
    · dsimp
      refine pullback.lift ?f.h ?f.k ?f.w
      case f.h => exact ((s.π.app ⟨ .right ⟩).left)
      case f.k => exact ((s.π.app ⟨ .left ⟩).left)
      case f.w => aesop_cat
    · simp
  case fac =>
    rintro s ⟨⟨l⟩|⟨r⟩⟩
    iterate {apply Over.OverMorphism.ext; simp}
  case uniq =>
    intro s m prf
    apply Over.OverMorphism.ext
    dsimp
    refine (pullback.hom_ext ?h.h₀ ?h.h₁)
    case h.h₀ => simpa [pullback.lift_fst] using (congr_arg CommaMorphism.left (prf ⟨ .right⟩))
    case h.h₁ => simpa [pullback.lift_snd] using (congr_arg CommaMorphism.left (prf ⟨ .left⟩))

def OverProdIso [HasFiniteWidePullbacks C] :
    (Σf.hom).obj ((f.hom*).obj x) ≅ f ⨯ x :=
  IsLimit.conePointUniqueUpToIso (pullbackCompositionIsBinaryProduct f x) (limit.isLimit _)

@[simp]
theorem triangle_hom_fst :
    let pbleg1 : (Over.map f.hom).obj ((f.hom*).obj x) ⟶ f := homMk (pullback.snd _ _) rfl
    (OverProdIso f x).hom ≫ prod.fst = pbleg1 :=
  IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct f x)
    (limit.isLimit _) ⟨WalkingPair.left⟩

@[simp]
theorem triangle_hom_snd :
    let pbleg2 : (Over.map f.hom).obj ((f.hom*).obj x) ⟶ x :=
    Over.homMk (pullback.fst _ _) (by simp [pullback.condition])
    (OverProdIso f x).hom ≫ prod.snd = pbleg2 :=
  IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct f x)
    (limit.isLimit _) ⟨WalkingPair.right⟩

@[simp]
theorem triangle_inv_fst :
    let pbleg1 : (Over.map f.hom).obj ((f.hom*).obj x) ⟶ f := homMk (pullback.snd _ _) rfl
    (OverProdIso f x).inv ≫ pbleg1 = prod.fst := by
  rw [Iso.inv_comp_eq, triangle_hom_fst]

@[simp]
theorem triangle_inv_snd :
    let pbleg2 : (Over.map f.hom).obj ((f.hom*).obj x) ⟶ x :=
    Over.homMk (pullback.fst _ _) (by simp [pullback.condition])
    (OverProdIso f x).inv ≫ pbleg2 = prod.snd := by
  rw [Iso.inv_comp_eq, triangle_hom_snd]

-- attribute [local instance] monoidalOfHasFiniteProducts
def NatOverProdIso [HasFiniteWidePullbacks C] {I : C} (f : Over I) :
    (f.hom*).comp (Over.map f.hom) ≅ MonoidalCategory.tensorLeft f := by
  fapply NatIso.ofComponents
  case app => exact fun _ ↦ OverProdIso f _
  case naturality =>
    intro x y u
    simp; ext1
    · simp only [Category.assoc, ChosenFiniteProducts.whiskerLeft_fst]
      change _ ≫ _ ≫ prod.fst = _ ≫ prod.fst
      rw [triangle_hom_fst, triangle_hom_fst]; ext; simp
    . simp only [Category.assoc, ChosenFiniteProducts.whiskerLeft_snd]
      rw [← Category.assoc _ _ u];
      change _ ≫ _ ≫ prod.snd = (_ ≫ prod.snd) ≫ u
      rw [triangle_hom_snd, triangle_hom_snd]; ext; simp

end

noncomputable section
variable {C} [OverCartesianClosed C] {X Y : C} (f : X ⟶ Y)

def pushforwardCospanLeg1 : (Over.mk (𝟙 Y)) ⟶ ((Over.mk f) ⟹ (Over.mk f)) :=
  CartesianClosed.curry prod.fst

def pushforwardCospanLeg2  (x : Over X) :
    ((Over.mk f) ⟹ ((Over.map f).obj x)) ⟶ ((Over.mk f) ⟹ (Over.mk f)) :=
  (((exp (Over.mk f)).map) (Over.homMk x.hom))

def pushforwardObj (x : Over X) : Over Y :=
  pullback (pushforwardCospanLeg1 f) (pushforwardCospanLeg2 f x)

def pushforwardCospanLeg2Map (x x' : Over X) (u : x ⟶ x') :
    ((exp (Over.mk f)).obj ((Over.map f).obj x)) ⟶ ((exp (Over.mk f)).obj ((Over.map f).obj x')) :=
  (exp (Over.mk f)).map ((Over.map f).map u)

def pushforwardMap (x x' : Over X) (u : x ⟶ x') :
    (pushforwardObj f x) ⟶ (pushforwardObj f x') := by
  refine pullback.map (pushforwardCospanLeg1 f) (pushforwardCospanLeg2 f x)
    (pushforwardCospanLeg1 f) (pushforwardCospanLeg2 f x') (𝟙 (Over.mk (𝟙 Y)))
      (pushforwardCospanLeg2Map f x x' u) (𝟙 (Over.mk f ⟹ Over.mk f))
    ?_ ?_
  · simp
  · unfold pushforwardCospanLeg2 pushforwardCospanLeg2Map
    simp only [Category.comp_id, ← (exp (Over.mk f)).map_comp]
    congr
    simp [map_obj_left, mk_left, map_map_left, homMk_left, w]

def pushforwardFunctor :
    (Over X) ⥤ (Over Y) where
  obj x := pushforwardObj f x
  map u := pushforwardMap f _ _ u
  map_id x := by
    apply pullback.hom_ext
    · unfold pushforwardMap
      simp
    · simp [pushforwardMap, pushforwardCospanLeg2Map]
      erw [Category.id_comp] -- FIXME: why is this needed
  map_comp := by
    apply fun x y z u v ↦ pullback.hom_ext _ _
    · unfold pushforwardMap
      simp
    · unfold pushforwardMap pushforwardCospanLeg2Map
      simp

def PushforwardObjToLeg (x : Over X) (y : Over Y) (u : (f*).obj y ⟶ x) :
    y ⟶ Over.mk f ⟹ (Over.map f).obj x :=
  CartesianClosed.curry ((OverProdIso (Over.mk f) y).inv ≫ (Over.map f).map u)

def PushforwardObjTo (x : Over X) (y : Over Y) (u : (f*).obj y ⟶ x) :
    y ⟶ (pushforwardFunctor f).obj x := by
  apply pullback.lift ((mkIdTerminal (X := Y)).from y) (PushforwardObjToLeg f x y u)
    ((CartesianClosed.uncurry_injective (A := Over.mk f)) _)
  unfold pushforwardCospanLeg1 PushforwardObjToLeg
  rw [CartesianClosed.uncurry_natural_left, CartesianClosed.uncurry_curry]
  simp [pushforwardCospanLeg2]
  rw [CartesianClosed.uncurry_natural_right, CartesianClosed.uncurry_curry]
  simp
  have conj : ((Over.map f).map u ≫ (homMk x.hom : (Over.map f).obj x ⟶ Over.mk f)) =
    (homMk ((f*).obj y).hom : (Over.map f).obj ((f*).obj y) ⟶ Over.mk f) :=
      OverMorphism.ext (by aesop_cat)
  erw [conj, triangle_inv_fst, ChosenFiniteProducts.whiskerLeft_fst]
  rfl

/- It's slightly easier to construct the transposed map f^*y ⟶ x from a cone over the pushforward
cospan.-/
-- attribute [local instance] monoidalOfHasFiniteProducts
def PushforwardObjUP (x : Over X) (y : Over Y) (v : y ⟶ ((Over.mk f) ⟹ ((Over.map f).obj x)))
  (w : ((mkIdTerminal (X := Y)).from y) ≫ (pushforwardCospanLeg1 f)
    = v ≫  (pushforwardCospanLeg2 f x)) :
    (f*).obj y ⟶ x := by
  unfold pushforwardCospanLeg2 at w
  unfold pushforwardCospanLeg1 at w
  have cw := Adjunction.homEquiv_naturality_right_square
    (F := MonoidalCategory.tensorLeft (Over.mk f))
    (adj := exp.adjunction (Over.mk f)) _ _ _ _ w
  unfold CartesianClosed.curry at cw
  simp at cw
  apply_fun CommaMorphism.left at cw
  refine homMk ((OverProdIso (Over.mk f) y).hom ≫ CartesianClosed.uncurry v).left ?_
  unfold CartesianClosed.uncurry
  dsimp at cw
  simp
  rw [← cw]
  convert congrArg CommaMorphism.left (triangle_hom_fst (Over.mk f) y)
  simp; erw [← Over.comp_left, ChosenFiniteProducts.whiskerLeft_fst]; rfl

-- The heart of the calculation that these constructions are inverses one way around,
-- checking that they recover the same cone leg over the pushforward cospan.
def pushforwardAdjRightInv (x : Over X) (y : Over Y)
    (v : y ⟶ ((Over.mk f) ⟹ ((Over.map f).obj x)))
    (w : ((mkIdTerminal (X := Y)).from y) ≫ (pushforwardCospanLeg1 f)
      = v ≫ (pushforwardCospanLeg2 f x)) :
    PushforwardObjToLeg f x y (PushforwardObjUP f x y v w) = v := by
  simp [PushforwardObjUP, PushforwardObjToLeg]
  rw [CartesianClosed.curry_eq_iff _ v]; ext; simp
  rw [← Over.comp_left_assoc, Iso.inv_hom_id, ← Over.comp_left, Category.id_comp]

-- The pushforward adjunction from cartesian closed slices.
def pushforwardAdj (f : X ⟶ Y) :
    f* ⊣ pushforwardFunctor f :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun y x =>
      { toFun := PushforwardObjTo f x y
        invFun := by
          intro v
          refine PushforwardObjUP f x y (v ≫ pullback.snd _ _) ?commute
          have w := v ≫= pullback.condition
          have lem : (v ≫ pullback.fst _ _) = mkIdTerminal.from y :=
            IsTerminal.hom_ext mkIdTerminal _ _
          rw [← lem, Category.assoc, Category.assoc, w]
        left_inv := by
          intro u
          ext
          simp [PushforwardObjUP, PushforwardObjTo, PushforwardObjToLeg]
        right_inv := by
          intro v
          apply pullback.hom_ext (IsTerminal.hom_ext mkIdTerminal _ _)
          let w : ((mkIdTerminal (X := Y)).from y) ≫ (pushforwardCospanLeg1 f) =
            (v ≫ pullback.snd _ _) ≫ (pushforwardCospanLeg2 f x) := by
            have w' := v ≫= pullback.condition
            rw [Category.assoc,
                ← (IsTerminal.hom_ext mkIdTerminal (v ≫ pullback.fst _ _) (mkIdTerminal.from y)),
                Category.assoc, w']
          have close := pushforwardAdjRightInv f x y (v ≫ pullback.snd _ _) w
          simp
          unfold PushforwardObjUP PushforwardObjTo PushforwardObjToLeg
          unfold PushforwardObjUP PushforwardObjToLeg at close
          simpa using close
      }
    homEquiv_naturality_left_symm := by
      intros y y' x h v
      unfold PushforwardObjUP
      ext
      simp
      rw [← Category.assoc _ _ (CartesianClosed.uncurry (v ≫ pullback.snd _ _)).left]
      have natiso := (NatOverProdIso (Over.mk f)).hom.naturality h
      unfold NatOverProdIso at natiso
      apply_fun CommaMorphism.left at natiso
      simp at natiso
      rw [natiso]
      simp
      rw [CartesianClosed.uncurry_natural_left]
      simp only [comp_left, map_obj_left]
    homEquiv_naturality_right := by
      intros y x x' u k
      simp
      unfold PushforwardObjTo
      apply pullback.hom_ext (IsTerminal.hom_ext mkIdTerminal _ _)
      unfold pushforwardFunctor
      rw [pullback.lift_snd]
      simp
      unfold pushforwardMap pullback.map
      rw [pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
      unfold PushforwardObjToLeg pushforwardCospanLeg2Map
      rw [← CartesianClosed.curry_natural_right, Category.assoc, (Over.map f).map_comp]
  }

end

noncomputable section

-- The main theorems
instance [OverCartesianClosed C] : LocallyCartesianClosed C where
  pushforward := pushforwardFunctor
  adj := pushforwardAdj

end
