import HoTTModel.Lemmas.Limits

open CategoryTheory CategoryTheory.Limits

universe u

class PreContextualCategory (α : Type u) extends Category α where
  gr : α → ℕ
  one : α
  one_gr : gr one = 0
  one_uniq {x : α} : gr x = 0 → x = one
  one_terminal : IsTerminal one
  ft : α → α
  ft_one : ft one = one
  ft_gr {n : ℕ} (x : α): gr x = n + 1 → gr (ft x) = n
  proj (x : α) : x ⟶ ft x

open PreContextualCategory

class PreContextualCategory.NR {α : Type u} [PreContextualCategory α] (x : α) : Prop where
  nr : gr x ≠ 0

class ContextualCategory (α : Type u) extends PreContextualCategory α where
  pb {x y : α} [NR x] (f : y ⟶ ft x) : α
  pb_fst {x y : α} [NR x] (f : y ⟶ ft x) : pb f ⟶ x
  gr_pb {x y : α} [NR x] {f : y ⟶ ft x} : gr (pb f) ≠ 0
  nr_pb {x y : α} [NR x] {f : y ⟶ ft x} : NR (pb f) := ⟨gr_pb⟩
  ft_pb {x y : α} [NR x] {f : y ⟶ ft x} : ft (pb f) = y
  isPullback {x y : α} [NR x] (f : y ⟶ ft x) :
    IsPullback (pb_fst f) (proj (pb f) ≫ eqToHom ft_pb) (proj x) f
  pullback_id_obj {x : α} [NR x]: pb (𝟙 (ft x)) = x
  pullback_id_map {x : α} [NR x] :
    HEq (pb_fst (𝟙 (ft x))) (𝟙 x)
  pullback_comp_obj {x y z : α} [NR x] {f : y ⟶ ft x} {g : z ⟶ y} :
    pb (g ≫ f) = pb (g ≫ eqToHom (ft_pb (f := f)).symm)
  pullback_comp_map {x y z : α} [NR x] {f : y ⟶ ft x} {g : z ⟶ y} :
    HEq (pb_fst (g ≫ f)) (pb_fst (g ≫ eqToHom ft_pb.symm) ≫ pb_fst f)

attribute [instance] ContextualCategory.nr_pb

namespace ContextualCategory

variable {α : Type u} [ContextualCategory α]

def pb_snd {x y : α} [NR x]
  (f : y ⟶ ft x) : pb f ⟶ y := proj (pb f) ≫ eqToHom ft_pb

instance : One α where
  one := one

def Gr (n : ℕ) := {x : α // gr x = n}

variable {a : α} {n : ℕ}

@[ext]
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

def Ext.hom {a : α} (e : Ext a) :
    e.obj ⟶ a := proj e.obj ≫ eqToHom e.ft'

def Ext.pullback (b : Ext a) (f : c ⟶ a) : Ext c where
  obj := pb (f ≫ eqToHom b.ft'.symm)
  ft' := ft_pb
  gr' := by
    convert gr_ft_iterate' (Nat.one_le_iff_ne_zero.mpr gr_pb)
    exact ft_pb.symm

lemma Ext.congrObj {a : α} {b b' : Ext a} (h : b = b') :
    b.obj = b'.obj := congrArg obj h

lemma Ext.congrHom {a : α} {b b' : Ext a} (h : b = b') :
    b.hom = (eqToHom (congrObj h)) ≫  b'.hom := by
  cases h; simp only [eqToHom_refl, Category.id_comp]

abbrev Ext.pullbackFst (b : Ext a) (f : c ⟶ a) := pb_fst (f ≫ eqToHom b.ft'.symm)

def Ext.pullbackIsPullback (b : Ext a) (f : c ⟶ a) :
    IsPullback (b.pullbackFst f) (b.pullback f).hom b.hom f := by
  apply (isPullback (f ≫ eqToHom b.ft'.symm)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (eqToIso b.ft')
  <;> simp [hom, pullback]

noncomputable def Diag (b : Ext a) :
    b.obj ⟶ (Ext.pullback b b.hom).obj :=
  (b.pullbackIsPullback b.hom).lift (𝟙 _) (𝟙 _) (by simp only [Category.id_comp])

abbrev Section {a : α} (b : Ext a) := Over.mk (𝟙 a) ⟶ Over.mk b.hom
  /-hom : a ⟶ b.obj
  is_section : map ≫ b.hom = 𝟙 a-/

noncomputable def Section.lift {b : Ext a} (f : c ⟶ a) (s : Section b) :
    Section (b.pullback f) :=
  (b.pullbackIsPullback f).sectionSnd' s

def Section.liftCommSq {b : Ext a} (f : c ⟶ a) (s : Section b) :
    CommSq f (s.lift f).left s.left (b.pullbackFst f) where
  w := by simp [lift]

def Section.ofEq {a : α} {b b' : Ext a} (s : Section b) (h : b = b') :
    Section b' := by
  refine Over.homMk (s.left ≫ eqToHom (Ext.congrObj h)) ?_
  cases h; simpa using s.w

/-
def Ext.PasteIsPullback {a : α} {b : Ext a} {c : Ext b.obj} {f : a' ⟶ a} :
  IsPullback (c.pullbackFst (b.pullbackFst f))
    ((c.pullback (b.pullbackFst f)).hom ≫ (b.pullback f).hom)
    (c.hom ≫ b.hom) f :=
  IsPullback.paste_vert (c.pullbackIsPullback _) (b.pullbackIsPullback _)
-/

structure Pi_type (α : Type u) [ContextualCategory α] where
  form {Γ : α} (A : Ext Γ) (B : Ext A.obj) : Ext Γ
  intro {Γ : α} (A : Ext Γ) (B : Ext A.obj) (b : Section B) : Section (form A B)
  elim {Γ : α} (A : Ext Γ) (B : Ext A.obj) (k : Section (form A B))
    (a : Section A) : Over.mk a.left ⟶ Over.mk B.hom
  compt {Γ : α} {A : Ext Γ} {B : Ext A.obj} (a : Section A)
    (b : Section B) : (elim A B (intro A B b) a).left = a.left ≫ b.left
  form_stable {Γ Γ' : α} (f : Γ' ⟶ Γ) (A : Ext Γ) (B : Ext A.obj) :
    (form A B).pullback f = form (A.pullback f) (B.pullback (A.pullbackFst f))
  intro_stable {Γ Γ' : α} (f : Γ' ⟶ Γ) {A : Ext Γ} (B : Ext A.obj) (b : Section B) :
    HEq ((intro A B b).lift f)
      (intro (A.pullback f) (B.pullback (A.pullbackFst f)) (b.lift (A.pullbackFst f)))
  elim_stable {Γ Γ' : α} (f : Γ' ⟶ Γ) (A : Ext Γ) (B : Ext A.obj)
    (k : Section (form A B)) (a : Section A) :
      elim (A.pullback f) (B.pullback (A.pullbackFst f)) ((k.lift f).ofEq (form_stable f A B))
        (a.lift f) = (a.liftCommSq f).liftIsPullbackAlong' (B.pullbackIsPullback (A.pullbackFst f))
          (elim A B k a)

structure Sigma_type (α : Type u) [ContextualCategory α] where
  form {Γ : α} {A : Ext Γ} (B : Ext A.obj) : Ext Γ
  intro {Γ : α} {A : Ext Γ} (B : Ext A.obj) : Over.mk (B.hom ≫ A.hom) ⟶ Over.mk (form B).hom
  elim_tm {Γ : α} {A : Ext Γ} {B : Ext A.obj} (C : Ext (form B).obj)
    (d : Over.mk (intro B).left ⟶ Over.mk C.hom) : Section C
  elim_comm  {Γ : α} {A : Ext Γ} {B : Ext A.obj} (C : Ext (form B).obj)
    (d : Over.mk (intro B).left ⟶ Over.mk C.hom) : (intro B).left ≫ (elim_tm C d).left = d.left


structure Id_type (α : Type u) [ContextualCategory α] where
  form {Γ : α} (A : Ext Γ) : Ext (Ext.pullback A A.hom).obj
  elim_tm {Γ : α} (A : Ext Γ) : A.obj ⟶ (form A).obj
  elim_comm {Γ : α} (A : Ext Γ) : elim_tm A ≫ (form A).hom = Diag A
  compt_tm {Γ : α} {A : Ext Γ} (C : Ext (form A).obj)
    (d : Over.mk (elim_tm A) ⟶ Over.mk C.hom ) : Section C
  compt_comm {Γ : α} {A : Ext Γ} (C : Ext (form A).obj)
    (d : Over.mk (elim_tm A) ⟶ Over.mk C.hom ) : elim_tm A ≫ (compt_tm C d).left = d.left

structure Empty_type (α : Type u) [ContextualCategory α] where
  form (Γ : α) : Ext Γ
  elim {Γ : α} (A : Ext (form Γ).obj) : Section A
  form_stable {Γ Γ' : α} (f : Γ' ⟶ Γ) : form Γ' = (form Γ).pullback f
  elim_stable {Γ Γ' : α} (A : Ext (form Γ).obj) (f : Γ' ⟶ Γ) :
    elim (Ext.pullback A (eqToHom (congrArg Ext.obj (form_stable f)) ≫ (Ext.pullbackFst (form Γ) f)))
      = (elim A).lift (eqToHom (congrArg Ext.obj (form_stable f)) ≫ Ext.pullbackFst (form Γ) f)

structure Unit_type (α : Type u) [ContextualCategory α] where
  form (Γ : α) : Ext Γ
  intro (Γ : α) : Section (form Γ)
  elim_tm {Γ : α} (A : Ext (form Γ).obj) (d : Over.mk (intro Γ).left ⟶ Over.mk A.hom) : Section A
  elim_comm {Γ : α} (A : Ext (form Γ).obj) (d : Over.mk (intro Γ).left ⟶ Over.mk A.hom) :
    (intro Γ).left ≫ (elim_tm A d).left = d.left
  form_stable {Γ Γ' : α} (f : Γ' ⟶ Γ) : form Γ' = (form Γ).pullback f
  intro_stable {Γ Γ' : α} (f : Γ' ⟶ Γ) :
    intro Γ' ≫ eqToHom (congrArg (fun f ↦ Over.mk f.hom) (form_stable f)) = (intro Γ).lift f

structure Sum_type (α : Type u) [ContextualCategory α] where
  form {Γ : α} (A B: Ext Γ) : Ext Γ
  introl {Γ : α} (A B: Ext Γ) : Over.mk A.hom ⟶ Over.mk (form A B).hom
  intror {Γ : α} (A B: Ext Γ) : Over.mk B.hom ⟶ Over.mk (form A B).hom
  elim_tm {Γ : α} {A B: Ext Γ} (C : Ext (form A B).obj)
    (d₁ : Over.mk (introl A B).left ⟶ Over.mk C.hom)
    (d₂ : Over.mk (intror A B).left ⟶ Over.mk C.hom) : Section C
  elim_comml {Γ : α} {A B: Ext Γ} (C : Ext (form A B).obj)
    (d₁ : Over.mk (introl A B).left ⟶ Over.mk C.hom)
    (d₂ : Over.mk (intror A B).left ⟶ Over.mk C.hom) :
      (introl A B).left ≫ (elim_tm C d₁ d₂).left = d₁.left
  elim_commr {Γ : α} {A B: Ext Γ} (C : Ext (form A B).obj)
    (d₁ : Over.mk (introl A B).left ⟶ Over.mk C.hom)
    (d₂ : Over.mk (intror A B).left ⟶ Over.mk C.hom) :
      (intror A B).left ≫ (elim_tm C d₁ d₂).left = d₂.left

end ContextualCategory
