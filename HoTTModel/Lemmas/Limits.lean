import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.IsConnected

namespace CategoryTheory

variable {C : Type u} [Category.{v, u} C]

namespace Limits

section UniqueToTerminal

-- not inferable???
def UniqueToTerminal {t X : C} (h : IsTerminal t) : Unique (X ⟶ t) := isTerminalEquivUnique _ t h _

lemma SubsingletonToTerminal {t X : C} (h : IsTerminal t) : Subsingleton (X ⟶ t) := by apply @Unique.instSubsingleton _ ((UniqueToTerminal) h)

end UniqueToTerminal

section ProdLiftUnique

lemma prod.lift_eq {X Y W : C} [HasBinaryProduct X Y] {f : W ⟶ X} {g : W ⟶ Y} {h : W ⟶ prod X Y}
(h₁ : h ≫ prod.fst = f) (h₂ : h ≫ prod.snd = g) : h = prod.lift f g:= by
  set lc : IsLimit (limit.cone (pair X Y)) := limit.isLimit _
  have := lc.uniq (BinaryFan.mk f g) h
  apply this
  intro j
  rcases j with ⟨left, right⟩
  <;> assumption

lemma prod.lift_uniq {X Y W : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) (h h' : W ⟶ prod X Y)
(h₁ : h ≫ prod.fst = f) (h₂ : h ≫ prod.snd = g) (h₁' : h' ≫ prod.fst = f) (h₂' : h' ≫ prod.snd = g) : h = h' :=
  Eq.trans (prod.lift_eq h₁ h₂) (prod.lift_eq h₁' h₂').symm

end ProdLiftUnique

section PullbackLiftUnique

-- This is pullback.hom_ext in MATHLIB
-- To be removed later
/-
` W → k → Y `
` ↓       ↓ `
` j       g `
` ↓       ↓ `
` X → f → Z `

and `W → l → t.pt` satisfying commutatativity => `l = lift`
-/

lemma PullbackCone.IsLimit.lift_eq {X Y Z: C} {f : X ⟶ Z} {g : Y ⟶ Z} {t : PullbackCone f g}
(ht : IsLimit t) {W: C} (j : W ⟶ X) (k : W ⟶ Y)  (w : j ≫ f = k ≫ g)
(l : W ⟶ t.pt) (h₁ : l ≫ t.fst = j) (h₂ : l ≫ t.snd = k) : l = PullbackCone.IsLimit.lift ht j k w := by
  apply ht.uniq (PullbackCone.mk _ _ w) l
  intro i
  match i with
  | none => simp; rw [← Category.assoc, h₁]
  | WalkingCospan.left => simp; exact h₁
  | WalkingCospan.right => simp; exact h₂

lemma PullbackCone.IsLimit.lift_uniq {X Y Z: C} {f : X ⟶ Z} {g : Y ⟶ Z} {t : PullbackCone f g}
(ht : IsLimit t) {W : C} (j : W ⟶ X) (k : W ⟶ Y) (w : j ≫ f = k ≫ g) (l l' : W ⟶ t.pt)
(h₁ : l ≫ t.fst = j) (h₂ : l ≫ t.snd = k)
(h₁' : l' ≫ t.fst = j) (h₂' : l' ≫ t.snd = k) : l = l' :=
  Eq.trans (PullbackCone.IsLimit.lift_eq ht j k w l h₁ h₂) (PullbackCone.IsLimit.lift_eq ht j k w l' h₁' h₂').symm

end PullbackLiftUnique

section PullbackWithEqToHom

def PullbackCone.IsLimit.pullback_eqToHom {X Y Z W : C} [Category C] {f : X ⟶ Y} {g : Z ⟶ W} (eq₁ : X = Z) (eq₂ : Y = W) (comm : f ≫ eqToHom eq₂ = eqToHom eq₁ ≫ g) : IsLimit <| PullbackCone.mk f (eqToHom eq₁) comm := by
  have eq_g : g = eqToHom eq₁.symm ≫ f ≫ eqToHom eq₂ := by simp [comm]
  have eq_f : f = eqToHom eq₁ ≫ g ≫ eqToHom eq₂.symm := by simp [eq_g]
  apply PullbackCone.isLimitAux'
  intro s
  use s.snd ≫ eqToHom eq₁.symm
  simp
  constructor
  simp only [eq_f, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← s.condition, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  intro _ _ h
  simp [← h]

end PullbackWithEqToHom


noncomputable section ProdTerminal
variable {C : Type*} [Category C] {X t : C} [HasBinaryProduct X t] (h : IsTerminal t)

@[simp]
def ProdTerminalHom := prod.lift (𝟙 X) (IsTerminal.from h X)

@[simp]
abbrev ProdTerminalInv : X ⨯ t ⟶ X := prod.fst

lemma ProdTerminalHom_inv_id : ProdTerminalHom h ≫ ProdTerminalInv = 𝟙 X := prod.lift_fst _ _

lemma ProdTerminalInv_hom_id : ProdTerminalInv ≫ ProdTerminalHom h = 𝟙 (X ⨯ t) := by
  apply prod.lift_uniq prod.fst (IsTerminal.from h _)
  <;> simp
  apply (SubsingletonToTerminal h).allEq

@[simp]
def IsoProdTerminal : X ≅ X ⨯ t where
  hom := ProdTerminalHom h
  inv := ProdTerminalInv
  hom_inv_id := ProdTerminalHom_inv_id h
  inv_hom_id := ProdTerminalInv_hom_id h

end ProdTerminal

noncomputable section TerminalProd
variable {C : Type*} [Category C] {X t : C} [HasBinaryProduct t X] (h : IsTerminal t)

@[simp]
def TerminalProdHom := prod.lift (IsTerminal.from h X) (𝟙 X)

@[simp]
abbrev TerminalProdInv : t ⨯ X ⟶ X := prod.snd

lemma TerminalProdHom_inv_id : TerminalProdHom h ≫ TerminalProdInv = 𝟙 X := prod.lift_snd _ _

lemma TerminalProdInv_hom_id : TerminalProdInv ≫ TerminalProdHom h = 𝟙 (t ⨯ X) := by
  apply prod.lift_uniq (IsTerminal.from h _) prod.snd
  <;> simp
  apply (SubsingletonToTerminal h).allEq

def IsoTerminalProd : X ≅ t ⨯ X where
  hom := TerminalProdHom h
  inv := TerminalProdInv
  hom_inv_id := TerminalProdHom_inv_id h
  inv_hom_id := TerminalProdInv_hom_id h

end TerminalProd

-- ⨯ is symmetic; has it been proved ???
noncomputable section PullbackRightComp

open Limits

variable {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ Y) (h : W ⟶ Z) [HasPullback f (h ≫ g)]
  [HasPullback f g] [HasPullback (pullback.snd f g) h]

def pullback.rightCompIso :
    pullback f (h ≫ g) ≅ pullback (snd f g) h :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit (cospan f (h ≫ g)))
    (pasteVertIsPullback (t₁ := pullback.cone f g) (t₂ := pullback.cone (pullback.snd f g) h)
      rfl (limit.isLimit _) (limit.isLimit _))

lemma pullback.rightCompIso_hom_comp_snd :
    (rightCompIso f g h).hom ≫ snd (snd f g) h = snd f (h ≫ g) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

lemma pullback.rightCompIso_hom_comp_fst :
    (rightCompIso f g h).hom ≫ fst (snd f g) h ≫ fst f g = fst f (h ≫ g) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

end PullbackRightComp

noncomputable section PullbackLeftComp

open Limits

variable {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ Y) (h : W ⟶ X) [HasPullback f g]
  [HasPullback (h ≫ f) g] [HasPullback h (pullback.fst f g)]

def pullback.leftCompIso :
    pullback (h ≫ f) g ≅ pullback h (fst f g) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit (cospan (h ≫ f) g))
    (pasteHorizIsPullback (t₂ := pullback.cone f g) (t₁ := pullback.cone h (pullback.fst f g))
      rfl (limit.isLimit _) (limit.isLimit _))

lemma pullback.leftCompIso_hom_comp_fst :
    (leftCompIso f g h).hom ≫ fst h (fst f g) = fst (h ≫ f) g :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

lemma pullback.leftCompIso_hom_comp_snd :
  (leftCompIso f g h).hom ≫ (snd h (fst f g)) ≫ snd f g = snd (h ≫ f) g :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

end PullbackLeftComp

end Limits

section Lift_from_CommSq_to_pullback

section
variable {X Y Z W X' Y' Z' W' : C}
  {fst : X ⟶ Y} {snd : X ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
  {fst' : X' ⟶ Y'} {snd' : X' ⟶ Z'} {f' : Y' ⟶ W'} {g' : Z' ⟶ W'}
  (is : CommSq fst snd f g) (is' : IsPullback fst' snd' f' g')
  (iY : Y ⟶ Y') (iZ : Z ⟶ Z') (iW : W ⟶ W')
  (hYW : iY ≫ f' = f ≫ iW) (hZW : iZ ≫ g' = g ≫ iW)

noncomputable def CommSq.liftIsPullback :
    X ⟶ X' :=
  is'.lift (fst ≫ iY) (snd ≫ iZ)
    (by simp only [Category.assoc]; rw [hYW, hZW, ← Category.assoc, is.w, Category.assoc])

lemma CommSq.liftIsPullback_fst :
    CommSq.liftIsPullback is is' iY iZ iW hYW hZW ≫ fst' = fst ≫ iY :=
  IsPullback.lift_fst _ _ _ _

lemma CommSq.liftIsPullback_snd :
    CommSq.liftIsPullback is is' iY iZ iW hYW hZW ≫ snd' = snd ≫ iZ :=
  IsPullback.lift_snd _ _ _ _

end

section

variable {X Y Z W X' Y' : C}
  {fst : X ⟶ Y} {snd : X ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
  {fst' : X' ⟶ Y'} {snd' : X' ⟶ Z} {f' : Y' ⟶ W}
  (is : CommSq fst snd f g) (is' : IsPullback fst' snd' f' g)
  (i : Y ⟶ Y') (hi : i ≫ f' = f)

-- along here indictes 'along' a mpa
noncomputable def CommSq.liftIsPullbackAlong :
    X ⟶ X' :=
  CommSq.liftIsPullback is is' i (𝟙 _) (𝟙 _) (by simp [hi]) (by simp)

@[simp, reassoc]
lemma CommSq.liftIsPullbackAlong_fst :
    liftIsPullbackAlong is is' i hi ≫ fst' = fst ≫ i :=
  is.liftIsPullback_fst is' _ _ _ _ _

@[simp, reassoc]
lemma CommSq.liftIsPullbackAlong_snd :
    liftIsPullbackAlong is is' i hi ≫ snd' = snd := by
  convert is.liftIsPullback_snd is' _ _ _ _ _
  simp only [Category.comp_id]

@[simp]
noncomputable def CommSq.liftIsPullbackAlong' (i : Over.mk f ⟶ Over.mk f') :
    Over.mk snd ⟶ Over.mk snd' :=
  Over.homMk (liftIsPullbackAlong is is' i.left (Over.w i)) (is.liftIsPullbackAlong_snd is' _ _)

end

section
variable {X Y Z W X' Z' : C}
  {fst : X ⟶ Y} {snd : X ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
  {fst' : X' ⟶ Y} {snd' : X' ⟶ Z'} {g' : Z' ⟶ W}
  (is : CommSq fst snd f g) (is' : IsPullback fst' snd' f g')
  (i : Z ⟶ Z') (hi : i ≫ g' = g)

noncomputable def CommSq.liftIsPullbackOf :
    X ⟶ X' :=
  CommSq.liftIsPullback is is' (𝟙 _) i (𝟙 _) (by simp) (by simp [hi])

@[simp, reassoc]
lemma CommSq.liftIsPullbackOf_fst :
    liftIsPullbackOf is is' i hi ≫ fst' = fst := by
  convert is.liftIsPullback_fst is' _ _ _ _ _
  simp only [Category.comp_id]

@[simp, reassoc]
lemma CommSq.liftIsPullbackOf_snd :
    liftIsPullbackOf is is' i hi ≫ snd' = snd ≫ i:=
  is.liftIsPullback_snd is' _ _ _ _ _

@[simp]
noncomputable def CommSq.liftIsPullbackOf' (i : Over.mk g ⟶ Over.mk g') :
    Over.mk fst ⟶ Over.mk fst' :=
  Over.homMk (liftIsPullbackOf is is' i.left (Over.w i)) (is.liftIsPullbackOf_fst is' _ _)

end

end Lift_from_CommSq_to_pullback

section Lift_between_two_pullbacks

/-
```
 X - fst → Y
 |         |
snd        f
 ↓         ↓
 Z -- g -→ W
```
-/
section
variable {X Y Z W X' Y' Z' W' : C}
  {fst : X ⟶ Y} {snd : X ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
  {fst' : X' ⟶ Y'} {snd' : X' ⟶ Z'} {f' : Y' ⟶ W'} {g' : Z' ⟶ W'}
  (is : IsPullback fst snd f g) (is' : IsPullback fst' snd' f' g')
  (iY : Y ⟶ Y') (iZ : Z ⟶ Z') (iW : W ⟶ W')
  (hYW : iY ≫ f' = f ≫ iW) (hZW : iZ ≫ g' = g ≫ iW)

noncomputable def IsPullback.liftIsPullback :
    X ⟶ X' := is.toCommSq.liftIsPullback is' iY iZ iW hYW hZW

lemma IsPullback.liftIsPullback_fst :
    IsPullback.liftIsPullback is is' iY iZ iW hYW hZW ≫ fst' = fst ≫ iY :=
  IsPullback.lift_fst _ _ _ _

lemma IsPullback.liftIsPullback_snd :
    IsPullback.liftIsPullback is is' iY iZ iW hYW hZW ≫ snd' = snd ≫ iZ :=
  IsPullback.lift_snd _ _ _ _

section

variable {X Y Z W X' Y' : C}
  {fst : X ⟶ Y} {snd : X ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
  {fst' : X' ⟶ Y'} {snd' : X' ⟶ Z} {f' : Y' ⟶ W}
  (is : IsPullback fst snd f g) (is' : IsPullback fst' snd' f' g)
  (i : Y ⟶ Y') (hi : i ≫ f' = f)

-- along here indictes 'along' a mpa
noncomputable def IsPullback.liftIsPullbackAlong :
    X ⟶ X' :=
  is.liftIsPullback is' i (𝟙 _) (𝟙 _) (by simp [hi]) (by simp)

@[simp, reassoc]
lemma IsPullback.liftIsPullbackAlong_fst :
    liftIsPullbackAlong is is' i hi ≫ fst' = fst ≫ i :=
  is.liftIsPullback_fst is' _ _ _ _ _

@[simp, reassoc]
lemma IsPullback.liftIsPullbackAlong_snd :
    liftIsPullbackAlong is is' i hi ≫ snd' = snd := by
  convert is.liftIsPullback_snd is' _ _ _ _ _
  simp only [Category.comp_id]

@[simp]
noncomputable def IsPullback.liftIsPullbackAlong' (i : Over.mk f ⟶ Over.mk f') :
    Over.mk snd ⟶ Over.mk snd' :=
  Over.homMk (liftIsPullbackAlong is is' i.left (Over.w i)) (is.liftIsPullbackAlong_snd is' _ _)

end

@[simp]
noncomputable def IsPullback.sectionSnd (i : W ⟶ Y) (hi : i ≫ f = 𝟙 _) :
    Z ⟶ X :=
  IsPullback.liftIsPullbackAlong (IsPullback.of_id_snd (f := g)) is i (by simp [hi])

@[simp, reassoc]
lemma IsPullback.sectionSnd_is_section :
    is.sectionSnd i hi ≫ snd = 𝟙 _ := by
  apply IsPullback.liftIsPullbackAlong_snd

@[simp]
noncomputable def IsPullback.sectionSnd' (i : Over.mk (𝟙 W) ⟶ Over.mk f) :
    Over.mk (𝟙 Z) ⟶ Over.mk snd :=
  Over.homMk (is.sectionSnd i.left (Over.w i)) is.sectionSnd_is_section

@[simp, reassoc]
lemma IsPullback.sectionSnd'_left_fst (i : Over.mk (𝟙 W) ⟶ Over.mk f) :
    (is.sectionSnd' i).left ≫ fst = g ≫ i.left := by
  simp only [Over.mk_left, sectionSnd', sectionSnd, Over.homMk_left, liftIsPullbackAlong_fst]

end
section
variable {X Y Z W X' Z' : C}
  {fst : X ⟶ Y} {snd : X ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
  {fst' : X' ⟶ Y} {snd' : X' ⟶ Z'} {g' : Z' ⟶ W}
  (is : IsPullback fst snd f g) (is' : IsPullback fst' snd' f g')
  (i : Z ⟶ Z') (hi : i ≫ g' = g)

noncomputable def IsPullback.liftIsPullbackOf :
    X ⟶ X' :=
  IsPullback.liftIsPullback is is' (𝟙 _) i (𝟙 _) (by simp) (by simp [hi])

@[simp]
lemma IsPullback.liftIsPullbackOf_fst :
    liftIsPullbackOf is is' i hi ≫ fst' = fst := by
  convert is.liftIsPullback_fst is' _ _ _ _ _
  simp only [Category.comp_id]

@[simp]
lemma IsPullback.liftIsPullbackOf_snd :
    liftIsPullbackOf is is' i hi ≫ snd' = snd ≫ i:=
  is.liftIsPullback_snd is' _ _ _ _ _

@[simp]
noncomputable def IsPullback.liftIsPullbackOf' (i : Over.mk g ⟶ Over.mk g') :
    Over.mk fst ⟶ Over.mk fst' :=
  Over.homMk (liftIsPullbackOf is is' i.left (Over.w i)) (is.liftIsPullbackOf_fst is' _ _)

end

end Lift_between_two_pullbacks

noncomputable section IsoPullback_OverMk

variable {α : Type u} [CategoryTheory.Category.{v, u} α]
  {P P' X Y Z : α} {fst : P ⟶ X} {snd : P ⟶ Y} {fst' : P' ⟶ X} {snd' : P' ⟶ Y}
  {f : X ⟶ Z} {g : Y ⟶ Z} (is : IsPullback fst snd f g) (is' : IsPullback fst' snd' f g)

def IsPullback.isoIsPullback_fst_overMk :
    Over.mk fst ≅ Over.mk fst' :=
  Over.isoMk (is.isoIsPullback _ _ is')

def IsPullback.isoIsPullback_snd_overMk :
    Over.mk snd ≅ Over.mk snd' :=
  Over.isoMk (is.isoIsPullback _ _ is')

open Limits

def IsPullback.isoPullback_fst_overMk [HasPullback f g] :
    Over.mk fst ≅ Over.mk (pullback.fst f g) :=
  is.isoIsPullback_fst_overMk (IsPullback.of_hasPullback _ _)

def IsPullback.isoPullback_snd_overMk [HasPullback f g] :
    Over.mk snd ≅ Over.mk (pullback.snd f g) :=
  is.isoIsPullback_snd_overMk (IsPullback.of_hasPullback _ _)

end IsoPullback_OverMk
end CategoryTheory

lemma NeZero.contradiction [NeZero 0] : False := by
  rwa [← neZero_zero_iff_false (α := ℕ)]

section

namespace CategoryTheory.Limits.Types

variable {J : Type v} [Category.{w, v} J]
  {F : J ⥤ Type u} (c : Cocone F) (hc : IsColimit c)

lemma app_eq_of_eqvGen (p q : Σ j, F.obj j) (h : Relation.EqvGen (Quot.Rel F) p q) :
    c.ι.app _ p.snd = c.ι.app _ q.snd := by
  induction h with
  | rel x y r =>
      obtain ⟨f ,hf⟩ := r
      rw [hf]
      change _ = (F.map f ≫ _) _
      rw [c.ι.naturality]
      rfl
  | refl x => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

variable [HasColimit F]
noncomputable def isColimitEquivQuot : c.pt ≃ Quot F :=
    (IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit F)).toEquiv.trans
      (colimitEquivQuot F)

@[simp]
lemma isColimitEquivQuot_symm_apply (j : J) (x : F.obj j) :
    (isColimitEquivQuot c hc).symm (Quot.mk _ ⟨j, x⟩) = c.ι.app j x := by
  simp [isColimitEquivQuot]
  exact congrFun (IsColimit.comp_coconePointUniqueUpToIso_inv hc _ _) x

@[simp]
lemma isColimitEquivQuot_apply (j : J) (x : F.obj j) :
    (isColimitEquivQuot c hc) (c.ι.app j x) = Quot.mk _ ⟨j, x⟩ := by
  apply (isColimitEquivQuot c hc).symm.injective
  simp

def isColimit_eq {j j' : J} {x : F.obj j} {x' : F.obj j'} (w : c.ι.app j x = c.ι.app j' x') :
    Relation.EqvGen (Quot.Rel F) ⟨j, x⟩ ⟨j', x'⟩ := by
  apply Quot.eq.1
  simpa using congr_arg (isColimitEquivQuot c hc) w

end CategoryTheory.Limits.Types
