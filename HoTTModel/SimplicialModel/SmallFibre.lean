import HoTTModel.LocallyCartesianClosed.Presheaf
import HoTTModel.SimplicialModel.Universe

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

section
variable (α : Cardinal.{u})

section
namespace Cardinal

class Infinite : Prop where
  le : ℵ₀ ≤ α

class IsStrongLimitClass : Prop where
  is : α.IsStrongLimit

class IsRegularClass : Prop where
  is : α.IsRegular

-- later change everything to `ℵ₀ <`
class Uncountable : Prop where
  le : aleph 1 ≤ α

instance [α.Uncountable] : α.Infinite where
  le := by
    apply LE.le.trans _ Uncountable.le
    simp [← aleph_zero, aleph_le_aleph]

variable {α}

lemma alpeh0_lt_of_uncountable [α.Uncountable] :
    aleph0 < α := by
  apply lt_of_lt_of_le _ Uncountable.le
  rw [← aleph_zero, aleph_lt_aleph]
  simp only [zero_lt_one]

lemma prod_le_pow_of_le {ι : Type u₁} (f : ι → Cardinal.{u₂}) (α : Cardinal.{u₂})
  (h : ∀ i, f i ≤ α):
    prod f ≤ lift α ^ lift #ι := by
  rw [← Cardinal.prod_const]
  apply prod_le_prod
  simpa using h

lemma prod_le_iSup_pow_of_le {ι : Type u₁} (f : ι → Cardinal.{u₂}) (α : Cardinal.{u₂})
  (h : ∀ i, f i ≤ α):
    prod f ≤ lift (iSup f) ^ lift #ι := by
  rw [← Cardinal.prod_const]
  apply prod_le_prod
  intro i
  apply le_ciSup
  use α
  intro β h'
  cases h' with
  | intro _ h' => simpa [← h'] using (h _)

lemma pow_lt_of_isStrongLimit (h : α.IsStrongLimit) {β γ : Cardinal.{u}} (h₁ : β < α) (h₂ : γ < α) :
    β ^ γ < α := by
  rcases le_or_lt β γ with h' | h'
  rcases lt_or_le γ ℵ₀ with h'' | h''
  exact lt_of_lt_of_le (power_lt_aleph0 (lt_of_le_of_lt h' h'') h'') h.aleph0_le
  apply lt_of_le_of_lt _ (h.2 _ h₂)
  apply (power_le_power_right h').trans (by rw [power_self_eq h''])
  rcases lt_or_le β ℵ₀ with h'' | h''
  exact lt_of_lt_of_le (power_lt_aleph0 h'' (h'.trans h'')) h.aleph0_le
  rcases eq_or_ne β 0 with h''' | h'''
  simp [h''']
  apply lt_of_le_of_lt (zero_power_le _) (lt_of_lt_of_le one_lt_aleph0 h.aleph0_le)
  apply lt_of_le_of_lt _ (h.2 _ h₁)
  refine (power_le_power_left h''' h'.le).trans (by rw [power_self_eq h''])

lemma lt_uncountable_of_fintype [α.Uncountable] {A : Type u} [Fintype A] :
    Cardinal.mk A < α := by
  apply lt_of_lt_of_le _ Cardinal.Infinite.le
  rw [Cardinal.lt_aleph0_iff_finite]
  apply Finite.of_fintype

end Cardinal
end

namespace SSet
open CategoryTheory Simplicial Opposite Set standardSimplex Classical

noncomputable section


variable (α : Cardinal.{u}) {X Y : SSet.{u}}

def Fibre.preimage_eq_sigma_fibre (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ} (S : Set (Y.obj n)) :
    f.app n ⁻¹' S ≃ Σ y : S, Fibre f y.val where
  toFun x := ⟨⟨f.app n x, x.2⟩, ⟨x, rfl⟩⟩
  invFun x := ⟨x.2.1, by
    have : f.app _ x.2.1 = x.1 := x.2.2
    simp [this]⟩
  left_inv x := by simp
  right_inv x := by ext; simp; exact x.2.2; rfl

def SmallFibre  (f : X ⟶ Y) : Prop :=
  ∀ ⦃n⦄, ∀ y : Y.obj n, Cardinal.mk (Fibre f y) < α

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
