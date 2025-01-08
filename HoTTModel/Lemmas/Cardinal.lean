import Mathlib.SetTheory.Cardinal.Cofinality

section
variable (α : Cardinal.{u})

section
-- several lemmas about cardinals
-- introduce the property of cardinals as classes

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

lemma prod_lt_bound_pow_of_lt_of_lt {ι : Type u} (f : ι → Cardinal.{u}) (α : Cardinal.{u})
  (h₁ : α.IsStrongLimit) (h₂ : α.IsRegular) (h₃ : ∀ i, f i < α) (h₄ : #ι < α):
    prod f < α := by
  apply lt_of_le_of_lt
  apply prod_le_iSup_pow_of_le _ α (fun a ↦ (h₃ a).le)
  simp [lift_id]
  apply pow_lt_of_isStrongLimit h₁ _ h₄
  apply iSup_lt_lift_of_isRegular h₂ _ h₃
  simpa

lemma lt_uncountable_of_fintype [α.Uncountable] {A : Type u} [Fintype A] :
    Cardinal.mk A < α := by
  apply lt_of_lt_of_le _ Cardinal.Infinite.le
  rw [Cardinal.lt_aleph0_iff_finite]
  apply Finite.of_fintype

end Cardinal
end
