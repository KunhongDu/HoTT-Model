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

lemma PreContextualCategory.nr_of_NR {α : Type*} [PreContextualCategory α] (x : α) [h : NR x] :
    gr x ≠ 0 := h.nr

def PreContextualCategory.nr (α : Type*) [PreContextualCategory α] := {x : α | NR x}

instance PreContextualCategory.nr.NR {α : Type*} [PreContextualCategory α] (x : nr α) :
    NR x.val := x.property

class ContextualCategory (α : Type*) extends PreContextualCategory α where
  pb {x y : α} [NR x] (f : y ⟶ ft x) : α
  pb_fst {x y : α} [NR x] (f : y ⟶ ft x) : pb f ⟶ x
  gr_pb {x y : α} [NR x] {f : y ⟶ ft x} : gr (pb f) ≠ 0
  nr_pb {x y : α} [NR x] {f : y ⟶ ft x} : NR (pb f) := ⟨gr_pb⟩
  ft_pb {x y : α} [NR x] {f : y ⟶ ft x} : ft (pb f) = y
  isPullback {x y : α} [NR x] (f : y ⟶ ft x) :
    IsPullback (pb_fst f) (proj (pb f) ≫ eqToHom ft_pb) (proj x) f
  pullback_id_obj {x : α} [NR x]: pb (𝟙 (ft x)) = x
  pullback_id_map {x : α} [NR x] :
    eqToHom (@pullback_id_obj x).symm ≫ pb_fst (𝟙 (ft x)) = 𝟙 x
  pullback_comp_obj {x y z : α} [NR x] {f : y ⟶ ft x} {g : z ⟶ y} :
    pb (g ≫ f) = pb (g ≫ eqToHom (ft_pb (f := f)).symm)
  pullback_comp_map {x y z : α} [NR x] {f : y ⟶ ft x} {g : z ⟶ y} :
    pb_fst (g ≫ f) =
      eqToHom pullback_comp_obj ≫ pb_fst (g ≫ eqToHom (ft_pb (f := f)).symm) ≫ pb_fst f

attribute [instance] PreContextualCategory.Cat

namespace ContextualCategory

variable {α : Type*} [ContextualCategory α]

def pb_snd {x y : α} [NR x]
  (f : y ⟶ ft x) : pb f ⟶ y := proj (pb f) ≫ eqToHom ft_pb

instance : One α where
  one := one

def Gr (n : ℕ) := {x : α // gr x = n}

variable {a : α} {n : ℕ}

/-
def ProjChainComp (a : α) : (n : ℕ) → (a ⟶ ft^[n] a)
| 0 => 𝟙 a
| n + 1 => proj a ≫ ProjChainComp (ft a) n

lemma ProjChainComp.zero (a : α) : ProjChainComp a 0 = 𝟙 a := rfl

lemma ProjChainComp.one (a : α) : ProjChainComp a 1 = proj a := by
  simp only [ProjChainComp, Category.comp_id]

structure Ext (a : α) (n : ℕ) where
  obj : α
  ft' : ft^[n] obj = a
  gr' : gr obj = gr a + n

lemma ExtNR (hn : n ≠ 0) {e : Ext a n} : NR e.obj := ⟨
  by rw [e.gr', Nat.ne_zero_iff_zero_lt]; apply Nat.lt_add_left _ (Nat.zero_lt_of_ne_zero hn)⟩

lemma Ext.gr_le {e : Ext a n} : n ≤ gr e.obj := by
  rw [e.gr']
  apply Nat.le_add_left

lemma gr_ft_iterate : gr a = n + k → gr (ft^[k] a) = n := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => simp; exact fun h ↦ (ih (a := ft a)) ((ft_gr (n:= n + k) a) h)

lemma gr_ft_iterate' (h : k ≤ gr a) : gr a = gr (ft^[k] a) + k := by
  rw [gr_ft_iterate (Nat.sub_add_cancel h).symm, Nat.sub_add_cancel h]

abbrev Ext.hom {a : α} {n : ℕ} (e : Ext a n) :
    e.obj ⟶ a := ProjChainComp e.obj n ≫ eqToHom e.ft'

abbrev Ext.proj {a : α} {n : ℕ} (e : Ext a n) :
    e.obj ⟶ ft^[n] e.obj := ProjChainComp e.obj n

lemma Ext.proj_eq_hom_comp {a : α} {n : ℕ} (e : Ext a n) :
    e.proj = e.hom ≫ eqToHom e.ft'.symm := by simp [hom]

abbrev Ext₁ (a : α) := Ext a 1

abbrev Ext₂ (a : α) := Ext a 2

instance Ext₁.NR (b : Ext₁ a) : NR b.obj := ExtNR Nat.one_ne_zero

def Ext.Above (b : Ext a n) (i : Fin n) : Ext (ft^[i] b.obj) i where
  obj := b.obj
  ft' := rfl
  gr' := gr_ft_iterate' <| le_of_lt (lt_of_lt_of_le (Fin.is_lt i) Ext.gr_le)

def Ext.Below (b : Ext a n) (i : Fin n) : Ext a i where
  obj := ft^[n-i] b.obj
  ft' := by simp only [← Function.iterate_add_apply, Fin.is_le', Nat.add_sub_cancel', b.ft']
  gr' := by rw [← Nat.add_right_cancel_iff (n := n - ↑i),
      ← gr_ft_iterate' (le_trans (Nat.sub_le _ _) Ext.gr_le),
      b.gr', Nat.add_assoc, Nat.add_left_cancel_iff,
      Nat.add_comm, Nat.sub_add_cancel (le_of_lt (Fin.is_lt i))]

abbrev Ext₂.Below (b : Ext₂ a) : Ext₁ a := Ext.Below b 1

abbrev Ext₂.Above (b : Ext₂ a) : Ext₁ (ft b.obj) := Ext.Above b 1

def Ext.concat (b : Ext a n) (c : Ext b.obj m) : Ext a (n + m) where
  obj := c.obj
  ft' := by rw [Function.iterate_add, Function.comp_apply, c.ft', b.ft']
  gr' := by rw [c.gr', b.gr', Nat.add_assoc]

abbrev Ext₂.mk (b : Ext₁ a) (c : Ext₁ b.obj) : Ext₂ a := Ext.concat b c

def Ext.pullback (b : Ext₁ a) (f : c ⟶ a) : Ext₁ c where
  obj := pb (f ≫ eqToHom b.ft'.symm)
  ft' := by simp only [Function.iterate_one, ft_pb]
  gr' := by
    convert gr_ft_iterate' (Nat.one_le_iff_ne_zero.mpr gr_pb)
    exact ft_pb.symm

noncomputable def Diag (b : Ext₁ a) :
    b.obj ⟶ (Ext.pullback b b.hom).obj :=
  (isPullback (b.hom ≫ eqToHom b.ft'.symm)).lift (𝟙 _) (𝟙 _) (by simp [← ProjChainComp.one])

abbrev Section {a : α} (b : Ext a n) := Over.mk (𝟙 a) ⟶ Over.mk b.hom
  /-hom : a ⟶ b.obj
  is_section : map ≫ b.hom = 𝟙 a-/

structure Ext.Hom {a : α} (b : Ext a m) (c : Ext a n) where
  hom : b.obj ⟶ c.obj
  comm : map ≫ c.hom = b.hom

-/

structure Ext (a : α) where
  obj : α
  ft' : ft obj = a
  gr' : gr obj = gr a + 1

instance ExtNR {e : Ext a} : NR e.obj := ⟨
  by rw [e.gr']; apply Nat.succ_ne_zero⟩

lemma Ext.one_le_gr {e : Ext a} : 1 ≤ gr e.obj := by
  rw [e.gr']
  apply Nat.le_add_left

lemma gr_ft_iterate : gr a = n + k → gr (ft^[k] a) = n := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => exact fun h ↦ (ih (a := ft a)) ((ft_gr (n:= n + k) a) h)

lemma gr_ft_iterate' (h : k ≤ gr a) : gr a = gr (ft^[k] a) + k := by
  rw [gr_ft_iterate (Nat.sub_add_cancel h).symm, Nat.sub_add_cancel h]

abbrev Ext.hom {a : α} (e : Ext a) :
    e.obj ⟶ a := proj e.obj ≫ eqToHom e.ft'

def Ext.pullback (b : Ext a) (f : c ⟶ a) : Ext c where
  obj := pb (f ≫ eqToHom b.ft'.symm)
  ft' := ft_pb
  gr' := by
    convert gr_ft_iterate' (Nat.one_le_iff_ne_zero.mpr gr_pb)
    exact ft_pb.symm

noncomputable def Diag (b : Ext a) :
    b.obj ⟶ (Ext.pullback b b.hom).obj :=
  (isPullback (b.hom ≫ eqToHom b.ft'.symm)).lift (𝟙 _) (𝟙 _) (by simp)

abbrev Section {a : α} (b : Ext a) := Over.mk (𝟙 a) ⟶ Over.mk b.hom
  /-hom : a ⟶ b.obj
  is_section : map ≫ b.hom = 𝟙 a-/

structure Pi_type (α : Type*) [ContextualCategory α] where
  form (Γ : α) (Γ'' : Ext₂ Γ): Ext₁ Γ
  intro (Γ : α) (Γ'' : Ext₂ Γ) (b : Section (Ext₂.Above Γ'')) : Section (form Γ Γ'')
  elim_tm (Γ : α) (Γ'' : Ext₂ Γ) (k : Section (form Γ Γ'')) (a : Section (Ext₂.Below Γ'')) : Section Γ''
  elim_comm (Γ : α) (Γ'' : Ext₂ Γ) (k : Section (form Γ Γ'')) (a : Section (Ext₂.Below Γ'')) :
    ((elim_tm Γ Γ'' k a).left ≫ (Ext₂.Above Γ'').hom) = a.left
  comp (Γ : α) (Γ'' : Ext₂ Γ) (a : Section (Ext₂.Below Γ'')) (b : Section (Ext₂.Above Γ'')) :
    (elim_tm Γ Γ'' (intro Γ Γ'' b) a).left = a.left ≫ b.left
  -- stable

structure Sigma_type (α : Type*) [ContextualCategory α] where
  form (Γ : α) (Γ'' : Ext₂ Γ): Ext₁ Γ
  intro (Γ : α) (Γ'' : Ext₂ Γ) : Γ''.Hom (form Γ Γ'')
  elim_tm (Γ : α) (Γ'' : Ext₂ Γ) (C : Ext₁ (form Γ Γ'').obj) (d : Γ''.obj ⟶ C.obj)
    (hd : d ≫ C.hom = (intro Γ Γ'').hom) : Section C
  elim_comm  (Γ : α) (Γ'' : Ext₂ Γ) (C : Ext₁ (form Γ Γ'').obj) (d : Γ''.obj ⟶ C.obj)
    (hd : d ≫ C.hom = (intro Γ Γ'').hom) : (intro Γ Γ'').hom ≫ (elim_tm Γ Γ'' C d hd).left = d
  -- stable

structure Id_type (α : Type*) [ContextualCategory α] where
  form (Γ : α) (Γ' : Ext₁ Γ) : Ext₁ (Ext.pullback Γ' (Γ'.hom)).obj
  elim_tm (Γ : α) (Γ' : Ext₁ Γ) : Γ'.obj ⟶ (form Γ Γ').obj
  elim_comm (Γ : α) (Γ' : Ext₁ Γ) : (elim_tm Γ Γ' ≫ (form Γ Γ').hom) = Diag Γ'
  comp_tm (Γ : α) (Γ' : Ext₁ Γ) (C : Ext₁ (form Γ Γ').obj) (d : Γ'.obj ⟶ C.obj)
    (hd : (d ≫ C.hom) = elim_tm Γ Γ') : Section C
  comp_comm (Γ : α) (Γ' : Ext₁ Γ) (C : Ext₁ (form Γ Γ').obj) (d : Γ'.obj ⟶ C.obj)
    (hd : (d ≫ C.hom) = elim_tm Γ Γ') : elim_tm Γ Γ' ≫ (comp_tm Γ Γ' C d hd).left = d

structure Zero_type (α : Type*) [ContextualCategory α] where
  form (Γ : α) : Ext₁ Γ
  elim_tm {Γ : α} (Γ' : Ext₁ (form Γ).obj) : Section Γ'

structure Unit_type (α : Type*) [ContextualCategory α] where
  form (Γ : α) : Ext₁ Γ
  intro (Γ : α) : Section (form Γ)
  elim_tm {Γ : α} (Γ' : Ext₁ (form Γ).obj)
    (d : Section (Ext₂.mk (form Γ) Γ')) (hd : d.left ≫ Γ'.hom = (intro Γ).left) : Section Γ'
  elim_comm {Γ : α} (Γ' : Ext₁ (form Γ).obj)
    (d : Section (Ext₂.mk (form Γ) Γ')) (hd : d.left ≫ Γ'.hom = (intro Γ).left) :
      (intro Γ).left ≫ (elim_tm Γ' d hd).left = d.left
  --stable

structure Sum_type (α : Type*) [ContextualCategory α] where
  form (Γ : α) (Γ₁ Γ₂: Ext₁ Γ) : Ext₁ Γ
  intro₁ (Γ : α) (Γ₁ Γ₂: Ext₁ Γ) : Γ₁.obj ⟶ (form Γ Γ₁ Γ₂).obj
  intro₂ (Γ : α) (Γ₁ Γ₂: Ext₁ Γ) : Γ₂.obj ⟶ (form Γ Γ₁ Γ₂).obj
  elim_tm (Γ : α) (Γ₁ Γ₂: Ext₁ Γ) (C : Ext₁ (form Γ Γ₁ Γ₂).obj) (d₁ : Γ₁.obj ⟶ C.obj) (d₂ : Γ₂.obj ⟶ C.obj)
    (hd₁: d₁ ≫ C.hom = intro₁ Γ Γ₁ Γ₂) (hd₂: d₂ ≫ C.hom = intro₂ Γ Γ₁ Γ₂) : Section C
  elim_comm₁ (Γ : α) (Γ₁ Γ₂: Ext₁ Γ) (C : Ext₁ (form Γ Γ₁ Γ₂).obj) (d₁ : Γ₁.obj ⟶ C.obj) (d₂ : Γ₂.obj ⟶ C.obj)
    (hd₁: d₁ ≫ C.hom = intro₁ Γ Γ₁ Γ₂) (hd₂: d₂ ≫ C.hom = intro₂ Γ Γ₁ Γ₂) :
      intro₁ Γ Γ₁ Γ₂ ≫ (elim_tm Γ Γ₁ Γ₂ C d₁ d₂ hd₁ hd₂).left = d₁
  elim_comm₂ (Γ : α) (Γ₁ Γ₂: Ext₁ Γ) (C : Ext₁ (form Γ Γ₁ Γ₂).obj) (d₁ : Γ₁.obj ⟶ C.obj) (d₂ : Γ₂.obj ⟶ C.obj)
    (hd₁: d₁ ≫ C.hom = intro₁ Γ Γ₁ Γ₂) (hd₂: d₂ ≫ C.hom = intro₂ Γ Γ₁ Γ₂) :
      intro₂ Γ Γ₁ Γ₂ ≫ (elim_tm Γ Γ₁ Γ₂ C d₁ d₂ hd₁ hd₂).left = d₂

end ContextualCategory
