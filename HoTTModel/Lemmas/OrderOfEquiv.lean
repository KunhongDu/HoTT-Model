import Mathlib.Order.Hom.Basic

universe u

namespace LinearOrder

variable {A B : Type u} [ord : LinearOrder A] (h : A ≃ B)

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

lemma ofEquiv_le_iff_le :
    ∀ a b : B, (ofEquiv h).le a b ↔ h.symm a ≤ h.symm b := by
  intros; rfl

lemma ofEquiv_lt_iff_lt :
    ∀ a b : B, (ofEquiv h).lt a b ↔ h.symm a < h.symm b := by
  intro a b
  rw [(ofEquiv h).lt_iff_le_not_le, lt_iff_le_not_le,
      ofEquiv_le_iff_le, ofEquiv_le_iff_le]

noncomputable def ofEquiv.ltRelIso :
    RelIso ord.lt (ofEquiv h).lt where
  toEquiv := h
  map_rel_iff' {_ _} := by
    rw [ofEquiv_lt_iff_lt, h.symm_apply_apply, h.symm_apply_apply]

noncomputable def ofEquiv.OrderIso :
    @OrderIso A B _ (ofEquiv h).toLE where
  toEquiv := h
  map_rel_iff' {_ _} := by
    rw [ofEquiv_le_iff_le, h.symm_apply_apply, h.symm_apply_apply]

lemma ofEquiv.OrderIso_apply (a : A) :
  ofEquiv.OrderIso h a = h a := rfl

lemma ofEquiv.OrderIso_symm_apply (b : B) :
  @OrderIso.symm A B _ (ofEquiv h).toLE (ofEquiv.OrderIso h) b = h.symm b := rfl

def ofEquiv.isWellOrderOfIsWellOrder (_ : IsWellOrder A ord.lt) :
    IsWellOrder B (ofEquiv h).lt :=
  (ofEquiv.ltRelIso h).symm.toRelEmbedding.isWellOrder

end LinearOrder
