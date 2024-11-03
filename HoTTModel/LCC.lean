import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Adjunction.Limits
import HoTTModel.Lemmas.Limits

namespace CategoryTheory

open Limits Over

universe v u

class LocallyCartesianClosed (C : Type u) [CategoryTheory.Category.{v, u} C]
    [CategoryTheory.Limits.HasPullbacks C] where
  DProd {X Y : C} (f : X ⟶ Y) : Over X ⥤ Over Y
  adj {X Y : C} (f : X ⟶ Y) : Over.pullback f ⊣ DProd f

namespace LocallyCartesianClosed

notation f"*" => Over.pullback f
notation "Π"f => DProd f
notation "Σ"f => Over.map f

noncomputable section
-- homEquiv between a chosen pullback and dependent product

namespace IsPullback
variable {α : Type u} [CategoryTheory.Category.{v, u} α] [CategoryTheory.Limits.HasPullbacks α]
  {A B C D E : α} {f : A ⟶ B} {fst : C ⟶ D} {snd : C ⟶ A} {g : D ⟶ B}
  (is : IsPullback fst snd g f)

def snd_isoPullback :
    Over.mk snd ≅ (f*).obj (Over.mk g) :=
  Over.isoMk is.isoPullback is.isoPullback_hom_snd

def snd_homEquiv (h : Over A) :
    (Over.mk snd ⟶ h) ≃ ((f*).obj (Over.mk g) ⟶ h) :=
  (snd_isoPullback is).homFromEquiv

lemma snd_homEquiv_naturality {h h' : Over A} (i : Over.mk snd ⟶ h) (j : h ⟶ h') :
    snd_homEquiv is h' (i ≫ j) =  snd_homEquiv is h i ≫ j := by
  simp only [snd_homEquiv, Iso.homFromEquiv_apply, Category.assoc]

variable [LocallyCartesianClosed α]

def adjEquiv (h : Over A) :
    (Over.mk snd ⟶ h) ≃ (Over.mk g ⟶ (Πf).obj h) :=
  (snd_homEquiv is h).trans ((adj f).homEquiv (Over.mk g) h)

lemma adjEquiv_naturality_right {h h' : Over A} (i : Over.mk snd ⟶ h) (j : h ⟶ h') :
    adjEquiv is h' (i ≫ j) = adjEquiv is h i ≫ (Πf).map j := by
  simp only [adjEquiv, Equiv.trans_apply]
  rw [snd_homEquiv_naturality is i j]
  exact Adjunction.homEquiv_naturality_right _ _ _

lemma adjEquiv_naturality_right_symm {h h' : Over A} (i : Over.mk g ⟶ (Πf).obj h) (j : h ⟶ h') :
    (adjEquiv is h').symm (i ≫ (Πf).map j) = (adjEquiv is h).symm i ≫ j := by
  simp only [Equiv.symm_apply_eq, adjEquiv_naturality_right,
    eq_self_iff_true, Equiv.apply_symm_apply]

section
/-
to be filled
-/
variable {C' D' : α} {fst' : C' ⟶ D'} {snd' : C' ⟶ A} {g' : D' ⟶ B}
  (is' : IsPullback fst' snd' g' f) (i : Over.mk g' ⟶ Over.mk g)
  {h : Over A} (j : Over.mk g ⟶ (Πf).obj h)

lemma adjEquiv_naturality_symm_left :
    is'.liftIsPullbackAlong' is i ≫ (adjEquiv is h).symm j = (adjEquiv is' h).symm (i ≫ j) := by
  dsimp [adjEquiv, snd_homEquiv]
  rw [← Adjunction.homEquiv_symm_id, ← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_left_symm, Category.comp_id, Category.comp_id,
      Adjunction.homEquiv_naturality_left_symm, ← Category.assoc, ← Category.assoc]
  congr 1; ext; simp [snd_isoPullback]; apply pullback.hom_ext
  <;> simp

end

section

variable {C' D' : α} {fst' : C' ⟶ D'} {snd' : C' ⟶ A} {g' : D' ⟶ B}
  (is' : IsPullback fst' snd' g' f) (i : Over.mk g' ⟶ Over.mk g)
  {h : Over A} (j : Over.mk g ⟶ (Πf).obj h)

lemma adjEquiv_naturality_symm_left' :
    is'.liftIsPullbackAlong' (IsPullback.of_hasPullback g f) i ≫
      ((adj f).homEquiv (Over.mk g) h).symm j = (adjEquiv is' h).symm (i ≫ j) := by
    dsimp [adjEquiv, snd_homEquiv]
    rw [← Adjunction.homEquiv_symm_id, ← Adjunction.homEquiv_naturality_left_symm,
        ← Adjunction.homEquiv_naturality_left_symm, Category.comp_id, Category.comp_id,
        Adjunction.homEquiv_naturality_left_symm, ← Category.assoc]
    congr 1; ext; simp [snd_isoPullback]; apply pullback.hom_ext
    <;> simp

end

end IsPullback
end

section
/-
Consider
` A -- j --> A'`
` |          | `
` f          f'`
` ↓          ↓ `
` B -- i --> B'`
` |          | `
` g          g'`
` ↓          ↓ `
` C -- h --> C `
` |          | `
` ↑          ↑ `
` |          | `
`ΠA -- ? --> ΠA'`
with the top two squares are pullback, can exhibit a pullback square down in the botto
-/

variable {α : Type u} [CategoryTheory.Category.{v, u} α]
   [CategoryTheory.Limits.HasPullbacks α] [LocallyCartesianClosed α]
  {A A' B B' C C' : α} {f : A ⟶ B} {g : B ⟶ C} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
  {h : C ⟶ C'} {i : B ⟶ B'} {j : A ⟶ A'}
  (is : IsPullback i g g' h) (is' : IsPullback j f f' i)

#check pullback ((Πg).obj (Over.mk f)).hom g

def DProd.isPullbackAux (is : IsPullback i g g' h)
  {E : α} (k : E ⟶ C):
    IsPullback (pullback.fst k g) (pullback.snd k g ≫ i) (k ≫ h) g' where
    w := by rw [← Category.assoc, pullback.condition, Category.assoc, Category.assoc, ← is.w]
    isLimit' := ⟨Limits.pasteHorizIsPullback (t₂ := is.flip.cone) rfl is.flip.isLimit
        (pullback.isLimit k g)⟩

noncomputable def DProd.trans₀ : (Σh).obj ((Πg).obj (Over.mk f)) ⟶ (Πg').obj (Over.mk f') := by
  apply (IsPullback.adjEquiv (isPullbackAux is ((Πg).obj (Over.mk f)).hom) (Over.mk f')).toFun
  refine Over.homMk (((adj g).counit.app (Over.mk f)).left ≫ j) ?_
  simp; erw [is'.w, ← Category.assoc, Over.w]; rfl

noncomputable def DProd.trans : ((Πg).obj (Over.mk f)).left ⟶ ((Πg').obj (Over.mk f')).left :=
  (DProd.trans₀ is is').left

/-
lemma DProd.isPullback_lift_aux {E : α} (k : E ⟶ ((Πg').obj (Over.mk f')).left) (k' : E ⟶ C) :
  k ≫ ((Πg').obj (Over.mk f')).hom = k' ≫ h ↔
    (IsPullback.adjEquiv (isPullbackAux is' k') (Over.mk k'))
-/

def DProd.isPullback :
    IsPullback (DProd.trans is is') ((Πg).obj (Over.mk f)).hom
      ((Πg').obj (Over.mk f')).hom h where
    w := by
      erw [Over.w]; rfl
    isLimit' := ⟨by
      sorry
    ⟩

end

noncomputable section PreservesColimit

/-

section Pullback_of_initial
open Limits

variable {X Y Z W: C}
  {fst : X ⟶ Y} {snd : X ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
  (is : IsPullback fst snd f g)

def fst_iso_of_isInitial (h : IsInitial Y) :
    X ≅ Y where
  hom := fst
  inv := h.to X
  hom_inv_id := by
    apply is.hom_ext
    . simp
    . simp only [Category.assoc, IsInitial.to_comp, Category.id_comp]
  inv_hom_id := h.hom_ext _ _

example (h : IsInitial Y) :
    IsInitial X :=
  h.ofIso (fst_iso_of_isInitial h).symm

end Pullback_of_initial-/

variable {α : Type u} [CategoryTheory.Category.{v, u} α]

def _root_.CategoryTheory.Over.IsInitialOfIsInitialLeft {X : α} (f : Over X) (hf : IsInitial f.left) :
    IsInitial f := by
  apply IsInitial.ofUniqueHom (fun g ↦ Over.homMk (hf.to g.left) (hf.hom_ext _ _))
  intro Y m
  ext; apply hf.hom_ext

lemma _root_.CategoryTheory.Over.IsInitial_hom_ext {X : α} {g h : Over X} (hg : IsInitial g)
  (γ γ' : g.left ⟶ h.left) :
    γ ≫ h.hom = g.hom → γ' ≫ h.hom = g.hom → γ = γ' := by
  intro h₁ h₂
  change (Over.homMk γ h₁ : g ⟶ h).left = (Over.homMk γ' h₂ : g ⟶ h).left
  congr 1
  apply hg.hom_ext

variable [CategoryTheory.Limits.HasPullbacks α] [LocallyCartesianClosed α] {X Y : α} (f : Y ⟶ X)

instance : PreservesColimitsOfSize (f*) :=
  (adj f).leftAdjointPreservesColimits

variable (g : Over X) (hg : IsInitial g)

def PullbackPreservesInitial: IsInitial ((f*).obj g) := IsInitial.isInitialObj (f*) g hg

def IsPullbackPreservesInitial {P X Y Z : α} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (is : IsPullback fst snd f g) (h : IsInitial (Over.mk f)) :
    IsInitial (Over.mk snd) :=
  (PullbackPreservesInitial g _ h).ofIso (is.isoPullback_snd_overMk).symm


end PreservesColimit

end LocallyCartesianClosed

end CategoryTheory
