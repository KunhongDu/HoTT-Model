import Mathlib.Order.InitialSeg
import Mathlib.Order.Bounds.Basic

namespace IsWellOrder
variable {α β: Type*} [Preorder α] [Preorder β] (f : α ≃o β)

lemma OrderIso_apply_eq [IsWellOrder β (· < ·)] {f g : α ≃o β} (a : α) :
    f a = g a := by
  change f.toInitialSeg a = g.toInitialSeg a
  apply InitialSeg.eq

lemma OrderIso_ext [IsWellOrder β (· < ·)] (f g : α ≃o β) : f = g := by
  ext
  apply IsWellOrder.OrderIso_apply_eq

end IsWellOrder
