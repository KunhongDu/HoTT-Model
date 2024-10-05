import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

open CategoryTheory
namespace CategoryTheory.Limits


variable {C : Type u} [Category.{v, u} C]


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
  simp only [← Category.assoc, ← s.condition, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
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
noncomputable section Pullback_comp

open Limits

variable {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ Y) (h : W ⟶ Z) [HasPullback f (h ≫ g)]
  [HasPullback f g] [HasPullback (pullback.snd f g) h]

def pullback.rightCompIso :
    pullback f (h ≫ g) ≅ pullback (pullback.snd f g) h := by
  exact IsLimit.conePointUniqueUpToIso (limit.isLimit (cospan f (h ≫ g)))
    (pasteVertIsPullback (t₁ := pullback.cone f g) (t₂ := pullback.cone (pullback.snd f g) h)
      rfl (limit.isLimit _) (limit.isLimit _))

lemma pullback.rightCompIso_hom_comp_snd :
    (pullback.rightCompIso f g h).hom ≫ pullback.snd (pullback.snd f g) h = pullback.snd f (h ≫ g) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

lemma pullback.rightCompIso_hom_comp_fst :
    (pullback.rightCompIso f g h).hom ≫ pullback.fst (pullback.snd f g) h ≫ pullback.fst f g =
      pullback.fst f (h ≫ g) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

end Pullback_comp
