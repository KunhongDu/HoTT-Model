import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

open CategoryTheory CategoryTheory.Limits

class PreContextualCategory (α : Type*) where
  Cat : Category α
  gr : α → ℕ
  one : α
  one_gr : gr one = 0
  one_uniq {x} : gr x = 0 → x = one
  one_terminal : IsTerminal one
  ft : α → α
  ft_one : ft one = one
  ft_gr {n : ℕ} (x : α): gr x = n + 1 → gr (ft x) = n
  proj (x : α) : x ⟶ ft x

open PreContextualCategory

-- NR = not root -- maybe change `one` to `root`??
class NR {α : Type*} [PreContextualCategory α] (x : α) : Prop :=
  nr : gr x ≠ 0

lemma nr_of_NR {α : Type*} [PreContextualCategory α] (x : α) [h : NR x]: gr x ≠ 0 := h.nr

class ContextualCategory (α : Type*) extends PreContextualCategory α where
  pb {x y : α} [NR x] (f : y ⟶ ft x) : α
  pb_map {x y : α} [NR x] (f : y ⟶ ft x) : pb f ⟶ x
  gr_pb {x y : α} [NR x] {f : y ⟶ ft x} : gr (pb f) ≠ 0
  nr_pb {x y : α} [NR x] {f : y ⟶ ft x} : NR (pb f) := ⟨gr_pb⟩
  ft_pb {x y : α} [NR x] {f : y ⟶ ft x} : ft (pb f) = y
  comm {x y : α} [NR x] {f : y ⟶ ft x} :  (proj <| pb f) ≫ eqToHom (ft_pb (f := f)) ≫ f = (pb_map f) ≫ proj x
  is_pullback {x y : α} [NR x] {f : y ⟶ ft x} : IsLimit <| PullbackCone.mk  (proj (pb f)) (pb_map f) comm
  pullback_id_obj {x : α} [NR x]: pb (𝟙 (ft x)) = x
  pullback_id_map {x : α} [NR x] : eqToHom (@pullback_id_obj x).symm ≫ pb_map (𝟙 (ft x)) = 𝟙 x
  pullback_comp_obj {x y z : α} [NR x] {f : y ⟶ ft x} {g : z ⟶ y} : pb (g ≫ f) = pb (g ≫ eqToHom (ft_pb (f := f)).symm)
  pullback_comp_map {x y z : α} [NR x] {f : y ⟶ ft x} {g : z ⟶ y} : pb_map (g ≫ f) = eqToHom (pullback_comp_obj (f := f) (g := g)) ≫  pb_map (g ≫ eqToHom (ft_pb (f := f)).symm) ≫ pb_map f

attribute [instance] PreContextualCategory.Cat

namespace ContextualCategory

instance initOneContext {α : Type*} [ContextualCategory α] : One α where
  one := one

variable {α : Type*} [ContextualCategory α]

def Gr (n : ℕ) := {x : α // gr x = n}

variable {a : α} {n : ℕ}

def ProjChainComp (a : α) : (n : ℕ) → (a ⟶ ft^[n] a)
| 0 => 𝟙 a
| Nat.succ n => proj a ≫ ProjChainComp (ft a) n

structure nExt (a : α) (n : ℕ) where
  obj : α
  ft : ft^[n] obj = a
  gr : gr obj = gr a + n

instance nExt_not_root (hn : n ≠ 0) {e : nExt a n} : NR e.obj := ⟨
  by rw [e.gr, Nat.ne_zero_iff_zero_lt]; apply Nat.lt_add_left _ (Nat.zero_lt_of_ne_zero hn)⟩

lemma nExt_gr_le {e : nExt a n} : n ≤ gr e.obj := by
  rw [e.gr]
  apply Nat.le_add_left

lemma gr_ft_iterate : gr a = n + k → gr (ft^[k] a) = n := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => simp; exact fun h ↦ (ih (a := ft a)) ((ft_gr (n:= n + k) a) h)

lemma gr_ft_iterate' (h : k ≤ gr a) : gr a = gr (ft^[k] a) + k := by
  rw [gr_ft_iterate (Nat.sub_add_cancel h).symm, Nat.sub_add_cancel h]

def nExtProj {a : α} {n : ℕ} (e : nExt a n) : e.obj ⟶ a := ProjChainComp e.obj n ≫ eqToHom e.ft

notation "𝓅" e => nExtProj e

abbrev Ext (a : α) := nExt a 1

abbrev dExt (a : α) := nExt a 2

instance ext_not_root (b : Ext a) : NR b.obj := nExt_not_root (hn := Nat.one_ne_zero)

def indExtAbove (b : nExt a n) (i : Fin n) : nExt (ft^[i] b.obj) i where
  obj := b.obj
  ft := rfl
  gr := gr_ft_iterate' <| le_of_lt (lt_of_lt_of_le (Fin.is_lt i) nExt_gr_le)

def indExtBelow (b : nExt a n) (i : Fin n) : nExt a i where
  obj := ft^[n-i] b.obj
  ft := by simp only [← Function.iterate_add_apply, Fin.is_le', Nat.add_sub_cancel', b.ft]
  gr := by rw [← Nat.add_right_cancel_iff (n := n - ↑i), ← gr_ft_iterate' (le_trans (Nat.sub_le _ _) nExt_gr_le), b.gr, Nat.add_assoc, Nat.add_left_cancel_iff, Nat.add_comm, Nat.sub_add_cancel (le_of_lt (Fin.is_lt i))]

abbrev dExtBelow1 (b : dExt a) := indExtBelow b 1

abbrev dExtAbove1 (b : dExt a) := indExtAbove b 1

def nExtExt (b : nExt a n) (c : nExt b.obj m) : nExt a (n + m) where
  obj := c.obj
  ft := by rw [Function.iterate_add, Function.comp_apply, c.ft, b.ft]
  gr := by rw [c.gr, b.gr, Nat.add_assoc]

abbrev toDExt (b : Ext a) (c : Ext b.obj) : dExt a := nExtExt b c

def PullbackExt (b : Ext a) (f : c ⟶ a) : Ext c where
  obj := pb (f ≫ eqToHom b.ft.symm)
  ft := by simp only [Function.iterate_one]; rw [ft_pb]
  gr := by
    have : ft (pb (f ≫ eqToHom b.ft.symm)) = c := by rw [ft_pb]
    simp_rw [← this]
    exact gr_ft_iterate' (k := 1) <| Nat.succ_le_of_lt (Nat.ne_zero_iff_zero_lt.mp gr_pb)

abbrev Diag (b : Ext a) : b.obj ⟶ (PullbackExt b (𝓅 b)).obj := by
  apply Limits.PullbackCone.IsLimit.lift (is_pullback) (eqToHom ft_pb.symm) (𝟙 b.obj)
  simp only [Category.id_comp, eqToHom_trans_assoc, eqToHom_refl]
  simp only [nExtProj, Function.iterate_succ,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  simp only [ProjChainComp, Category.comp_id]

structure Section {a : α} (b : nExt a n) where
  map : a ⟶ b.obj
  is_section : (map ≫ 𝓅 b) = 𝟙 a

structure Over {a : α} (b : nExt a m) (c : nExt a n) where
  map : b.obj ⟶ c.obj
  comm : (map ≫ 𝓅 c) = 𝓅 b

structure Pi_type (α : Type*) [ContextualCategory α] where
  form (Γ : α) (Γ'' : dExt Γ): Ext Γ
  intro (Γ : α) (Γ'' : dExt Γ) (b : Section (dExtAbove1 Γ'')) : Section (form Γ Γ'')
  elim_tm (Γ : α) (Γ'' : dExt Γ) (k : Section (form Γ Γ'')) (a : Section (dExtBelow1 Γ'')) : Section Γ''
  elim_comm (Γ : α) (Γ'' : dExt Γ) (k : Section (form Γ Γ'')) (a : Section (dExtBelow1 Γ'')) : ((elim_tm Γ Γ'' k a).1 ≫ 𝓅(dExtAbove1 Γ'')) = a.map
  comp (Γ : α) (Γ'' : dExt Γ) (a : Section (dExtBelow1 Γ'')) (b : Section (dExtAbove1 Γ'')) : (elim_tm Γ Γ'' (intro Γ Γ'' b) a).map = a.map ≫ b.map
  -- stable

structure Sigma_type (α : Type*) [ContextualCategory α] where
  form (Γ : α) (Γ'' : dExt Γ): Ext Γ
  intro (Γ : α) (Γ'' : dExt Γ) : Over Γ'' (form Γ Γ'')
  elim_tm (Γ : α) (Γ'' : dExt Γ) (C : Ext (form Γ Γ'').obj) (d : Γ''.obj ⟶ C.obj) (hd : (d ≫ 𝓅 C) = (intro Γ Γ'').map) : Section C
  elim_comm  (Γ : α) (Γ'' : dExt Γ) (C : Ext (form Γ Γ'').obj) (d : Γ''.obj ⟶ C.obj) (hd : (d ≫ 𝓅 C) = (intro Γ Γ'').map) : (intro Γ Γ'').map ≫ (elim_tm Γ Γ'' C d hd).map = d
  -- stable

structure Id_type (α : Type*) [ContextualCategory α] where
  form (Γ : α) (Γ' : Ext Γ) : Ext (PullbackExt Γ' (𝓅 Γ')).obj
  elim_tm (Γ : α) (Γ' : Ext Γ) : Γ'.obj ⟶ (form Γ Γ').obj
  elim_comm (Γ : α) (Γ' : Ext Γ) : (elim_tm Γ Γ' ≫ 𝓅 (form Γ Γ')) = Diag Γ'
  comp_tm (Γ : α) (Γ' : Ext Γ) (C : Ext (form Γ Γ').obj) (d : Γ'.obj ⟶ C.obj) (hd : (d ≫ 𝓅 C) = elim_tm Γ Γ') : Section C
  comp_comm (Γ : α) (Γ' : Ext Γ) (C : Ext (form Γ Γ').obj) (d : Γ'.obj ⟶ C.obj) (hd : (d ≫ 𝓅 C) = elim_tm Γ Γ') : elim_tm Γ Γ' ≫ (comp_tm Γ Γ' C d hd).map = d

structure Zero_type (α : Type*) [ContextualCategory α] where
  form (Γ : α) : Ext Γ
  elim_tm {Γ : α} (Γ' : Ext (form Γ).obj) : Section Γ'

structure Unit_type (α : Type*) [ContextualCategory α] where
  form (Γ : α) : Ext Γ
  intro (Γ : α) : Section (form Γ)
  elim_tm {Γ : α} (Γ' : Ext (form Γ).obj) (d : Section (toDExt (form Γ) Γ')) (hd : (d.map ≫ 𝓅 Γ') = (intro Γ).map) : Section Γ'
  elim_comm {Γ : α} (Γ' : Ext (form Γ).obj) (d : Section (toDExt (form Γ) Γ')) (hd : (d.map ≫ 𝓅 Γ') = (intro Γ).map) : (intro Γ).map ≫ (elim_tm Γ' d hd).map = d.map
  --stable

structure Sum_type (α : Type*) [ContextualCategory α] where
  form (Γ : α) (Γ₁ Γ₂: Ext Γ) : Ext Γ
  intro₁ (Γ : α) (Γ₁ Γ₂: Ext Γ) : Γ₁.obj ⟶ (form Γ Γ₁ Γ₂).obj
  intro₂ (Γ : α) (Γ₁ Γ₂: Ext Γ) : Γ₂.obj ⟶ (form Γ Γ₁ Γ₂).obj
  elim_tm (Γ : α) (Γ₁ Γ₂: Ext Γ) (C : Ext (form Γ Γ₁ Γ₂).obj) (d₁ : Γ₁.obj ⟶ C.obj) (d₂ : Γ₂.obj ⟶ C.obj) (hd₁: (d₁ ≫ 𝓅 C) = intro₁ Γ Γ₁ Γ₂) (hd₂: (d₂ ≫ 𝓅 C) = intro₂ Γ Γ₁ Γ₂) : Section C
  elim_comm₁ (Γ : α) (Γ₁ Γ₂: Ext Γ) (C : Ext (form Γ Γ₁ Γ₂).obj) (d₁ : Γ₁.obj ⟶ C.obj) (d₂ : Γ₂.obj ⟶ C.obj) (hd₁: (d₁ ≫ 𝓅 C) = intro₁ Γ Γ₁ Γ₂) (hd₂: (d₂ ≫ 𝓅 C) = intro₂ Γ Γ₁ Γ₂) : intro₁ Γ Γ₁ Γ₂ ≫ (elim_tm Γ Γ₁ Γ₂ C d₁ d₂ hd₁ hd₂).map = d₁
  elim_comm₂ (Γ : α) (Γ₁ Γ₂: Ext Γ) (C : Ext (form Γ Γ₁ Γ₂).obj) (d₁ : Γ₁.obj ⟶ C.obj) (d₂ : Γ₂.obj ⟶ C.obj) (hd₁: (d₁ ≫ 𝓅 C) = intro₁ Γ Γ₁ Γ₂) (hd₂: (d₂ ≫ 𝓅 C) = intro₂ Γ Γ₁ Γ₂) : intro₂ Γ Γ₁ Γ₂ ≫ (elim_tm Γ Γ₁ Γ₂ C d₁ d₂ hd₁ hd₂).map = d₂
