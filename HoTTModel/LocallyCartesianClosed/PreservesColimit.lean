import HoTTModel.LocallyCartesianClosed.Basic

namespace CategoryTheory
open Limits Over
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

def Over.IsInitialOfIsInitialLeft {X : α} (f : Over X) (hf : IsInitial f.left) :
    IsInitial f := by
  apply IsInitial.ofUniqueHom (fun g ↦ Over.homMk (hf.to g.left) (hf.hom_ext _ _))
  intro Y m
  ext; apply hf.hom_ext

lemma Over.IsInitial_hom_ext {X : α} {g h : Over X} (hg : IsInitial g)
  (γ γ' : g.left ⟶ h.left) :
    γ ≫ h.hom = g.hom → γ' ≫ h.hom = g.hom → γ = γ' := by
  intro h₁ h₂
  change (Over.homMk γ h₁ : g ⟶ h).left = (Over.homMk γ' h₂ : g ⟶ h).left
  congr 1
  apply hg.hom_ext

namespace LocallyCartesianClosed
variable [CategoryTheory.Limits.HasFiniteWidePullbacks α] [LocallyCartesianClosed α] {X Y : α} (f : Y ⟶ X)

instance : PreservesColimitsOfSize (f*) :=
  (adj f).leftAdjointPreservesColimits

variable (g : Over X) (hg : IsInitial g)

def PullbackPreservesInitial: IsInitial ((f*).obj g) := IsInitial.isInitialObj (f*) g hg

def IsPullbackPreservesInitial {P X Y Z : α} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (is : IsPullback fst snd f g) (h : IsInitial (Over.mk f)) :
    IsInitial (Over.mk snd) :=
  (PullbackPreservesInitial g _ h).ofIso (is.isoPullback_snd_overMk).symm


end LocallyCartesianClosed
end PreservesColimit
