import Mathlib.SetTheory.Ordinal.Basic
import HoTTModel.SSet.Fibrations

noncomputable section
universe u v
variable (α : Type u) [Small.{v} α] [s : Setoid α]

instance Setoid.shrink : Setoid (Shrink α) where
  r x y := s.r ((equivShrink α).symm x) ((equivShrink α).symm y)
  iseqv := {
    refl := fun _ ↦ s.iseqv.refl _
    symm := s.iseqv.symm
    trans := s.iseqv.trans
  }

def Setoid.shrinkQuotientEquiv : Quotient s ≃ Quotient (Setoid.shrink α) where
  toFun := by
    apply Quotient.lift (fun a ↦ ⟦equivShrink α a⟧)
    intro _ _ h
    simp only [Quotient.eq]
    change s.r _ _
    simpa using h
  invFun := by
    apply Quotient.lift (fun a ↦ ⟦(equivShrink α).symm a⟧)
    intro _ _ h
    simpa only [Quotient.eq] using h
  left_inv := by
    apply Quotient.ind
    intro a
    simp only [Quotient.lift_mk, Equiv.symm_apply_apply]
  right_inv := by
    apply Quotient.ind
    intro a
    simp only [Quotient.lift_mk, Equiv.apply_symm_apply]

instance Small.setoid : Small.{v} (Quotient s) where
  equiv_small := ⟨Quotient (Setoid.shrink α), ⟨Setoid.shrinkQuotientEquiv α⟩⟩

end

noncomputable section
universe u
variable (α : Cardinal.{u})

def SmallSSet := {X : SSet.{u} // ∀ n, Cardinal.mk (X.obj n) < α}

def SmallSSet' := {f : ℕ → Type u // ∀ n, Cardinal.mk (f n) < α}

def SmallSSet'' := ℕ → Set.Iio α

instance : Small.{u} (SmallSSet'' α) := by
  apply small_Pi

instance SmallSSet'.setoid : Setoid (SmallSSet' α) := by
  dsimp [SmallSSet']; infer_instance

def SmallSSet'.quotientEquiv :
    Quotient (SmallSSet'.setoid α) ≃  SmallSSet'' α where
  toFun := by
    apply Quotient.lift (fun f n ↦ (⟨Cardinal.mk (f.1 n), f.2 n⟩ : Set.Iio α))
    intro _ _ h
    ext n
    obtain ⟨h⟩ := h n
    apply Cardinal.mk_congr h
  invFun := fun f ↦ ⟦⟨fun n ↦ Quotient.out (f n).1,
      fun n ↦ by simpa only [Cardinal.mk_out] using (f n).2⟩⟧
  left_inv := by
    apply Quotient.ind
    intro f; simp; intro n; simp
    rw [← Quotient.eq_mk_iff_out]
    rfl
  right_inv := by
    intro f
    simp only [Quotient.lift_mk, Cardinal.mk_out, Subtype.coe_eta]

instance : Small.{u} (Quotient (SmallSSet'.setoid α)) where
  equiv_small := ⟨_, ⟨(SmallSSet'.quotientEquiv α).trans (equivShrink (SmallSSet'' α))⟩⟩

end

noncomputable section
open CategoryTheory Function
universe u
variable (α : Cardinal.{u})

def SmallGroup := {X : Bundled Group.{u} // Cardinal.mk X.α < α}

instance (X : SmallGroup α) : Group X.1.1 := X.1.2

instance setoidSmallGroup : Setoid (SmallGroup α) where
  r X Y := Nonempty (X.1.1 ≃* Y.1.1)
  iseqv := sorry

def aux := (X : Shrink (Set.Iio α)) × (Group ((equivShrink _).symm X).1.out)

def func : aux α → Quotient (setoidSmallGroup α) := by
  intro ⟨X, G⟩
  apply Quotient.mk
  use @Bundled.of _ (((equivShrink _).symm X).1.out) G
  have := ((equivShrink _).symm X).2
  dsimp [Set.Iio] at this
  convert this
  change Cardinal.mk (Quotient.out _) = _
  simp only [Cardinal.mk_out]
  rfl

def GroupStrEquiv {X Y : Type u} [G : Group X] (h : X ≃ Y) :
    Group Y where
  mul a b := h (h.symm a * h.symm b)
  mul_assoc a b c := by
    change h (h.symm (h _) * _) = h (_ * h.symm (h _))
    simp only [Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq, mul_assoc]
  one := h 1
  one_mul a := by
    change h (h.symm (h 1) * h.symm a) = a
    simp only [Equiv.symm_apply_apply, one_mul, Equiv.apply_symm_apply]
  mul_one a := by
    change h (h.symm a * h.symm (h 1)) = a
    simp only [Equiv.symm_apply_apply, mul_one, Equiv.apply_symm_apply]
  inv a := h (h.symm a)⁻¹
  inv_mul_cancel a := by
    change h (h.symm (h (h.symm a)⁻¹) * h.symm a) = h 1
    simp only [Equiv.symm_apply_apply, inv_mul_cancel]

variable {α} in
def transfer' {X : SmallGroup α} {Y : Type u} (h : X.1.1 ≃ Y) :
    SmallGroup α :=
  ⟨@Bundled.of _ Y (GroupStrEquiv h), by
    have : Cardinal.mk X.1.1 = Cardinal.mk Y := by
      erw [Quotient.eq]
      exact ⟨h⟩
    erw [← this]; exact X.2⟩

variable {α} in
def transfer'MulEquiv (X : SmallGroup α) {Y : Type u} (h : X.1.1 ≃ Y) :
    X ≈ transfer' h := by
  change Nonempty _
  use h
  intro x y
  change h _ = h (h.symm (h _) * h.symm (h _))
  simp only [Equiv.symm_apply_apply]

def transfer (X : SmallGroup α) :
    X.1.1 ≃
      Quotient.out ((equivShrink (Set.Iio α)).symm (equivShrink (Set.Iio α)
        (⟨Cardinal.mk X.1.1, X.2⟩ : Set.Iio α))).1 := by
  erw [Equiv.symm_apply_apply]
  apply Cardinal.outMkEquiv.symm

instance (X : SmallGroup α) :
  Group (Quotient.out ((equivShrink (Set.Iio α)).symm (equivShrink (Set.Iio α)
    (⟨Cardinal.mk X.1.1, X.2⟩ : Set.Iio α))).1) := GroupStrEquiv (transfer α X)

lemma surj : Surjective (func α) := by
  apply Quotient.ind
  intro X
  use ⟨equivShrink _ ⟨Cardinal.mk X.1.1, X.2⟩, inferInstance⟩
  dsimp [func]
  simp only [Quotient.eq]
  symm
  convert transfer'MulEquiv X _

instance : Small.{u} (Quotient (setoidSmallGroup α)) :=
  @small_of_surjective _ _ (by infer_instance) _ (surj α)

end
