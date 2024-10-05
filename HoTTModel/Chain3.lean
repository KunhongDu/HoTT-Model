import HoTTModel.TypeStructures
import HoTTModel.Lemmas.Limits
import Mathlib.Data.List.Basic

open ContextualCategory List CategoryTheory Limits

namespace Universe
variable {C : Type u} [CategoryTheory.Category.{v, u} C] {U : Universe C}

inductive Chain (U : Universe C) : C → C → Type (max u v)
| nil X : Chain U X X
| cons (Y : C) (g : Y ⟶ U.obj) (c : Chain U X Y)  : Chain U X (U.pb g)

open Chain
variable {X Y : C}

def toObj (_ : Chain U X Y) : C := Y

def tailObj (c : Chain U X Y) : C := by
  cases c with
  | nil => exact X
  | cons Y g c => exact Y

def tail (c : Chain U X Y) : Chain U X (tailObj c) := by
  cases c with
  | nil => exact nil X
  | cons Y g c => exact c

def toMap (c : Chain U X Y) : Y ⟶ tailObj c := by
  cases c with
  | nil => exact 𝟙 X
  | cons Y g c => exact U.pb_vmap g

def ne_nil (c : Chain U X Y) : Prop := by
  cases c with
  | nil => exact False
  | cons => exact True

def is_nil (c : Chain U X Y) : Prop := by
  cases c with
  | nil => exact True
  | cons => exact False

lemma ne_nil_iff_not_if_nil {c : Chain U X Y} : ne_nil c ↔ ¬ is_nil c := by
  cases c with
  | nil => simp [ne_nil, is_nil]
  | cons Y g c => simp [ne_nil, is_nil]

lemma is_nil_iff_not_ne_nil {c : Chain U X Y} : is_nil c ↔ ¬ ne_nil c := by
  cases c with
  | nil => simp [ne_nil, is_nil]
  | cons Y g c => simp [ne_nil, is_nil]

def tailMap (c : Chain U X Y) (h : ne_nil c) : tailObj c ⟶ U.obj := by
  cases c with
  | nil => exact False.elim h
  | cons Y g c => exact g

def length : {Y : C} → Chain U X Y → ℕ
| _, Chain.nil _ => 0
| _, Chain.cons _ _ c => length c + 1

section LengthLemma

lemma length_eq_zero_iff_is_nil {c : Chain U X Y} : is_nil c ↔ length c = 0  := by
  cases c with
  | nil => simp [length, is_nil]
  | cons Y g c => simp [is_nil, length]

lemma is_nil_of_length_eq_zero {c : Chain U X Y} (h : length c = 0) : is_nil c := by rwa [length_eq_zero_iff_is_nil]

lemma length_eq_zero_of_is_nil {c : Chain U X Y} (h : is_nil c) : length c = 0  := by rwa [← length_eq_zero_iff_is_nil]

lemma eq_of_length_eq_zero {c : Chain U X Y} (h : length c = 0) : Y = X := by
  cases c with
  | nil => rfl
  | cons Y g c => simp [length] at h

lemma heq_of_length_eq_zero {c : Chain U X Y} (h : length c = 0) : HEq c (Chain.nil (U:= U) X) := by
  cases c with
  | nil => rfl
  | cons Y g c => simp [length] at h

lemma length_tail {c : Chain U X Y} : length (tail c) = length c - 1 := by
  cases c <;> rfl

lemma length_tail' {c : Chain U X Y} : length c = n + 1 → length (tail c) = n := by intro h; rw [length_tail, h]; rfl

end LengthLemma

section Lemma

lemma tailMap_cons {g : Y ⟶ U.obj} (c : Chain U X Y) : tailMap (Chain.cons Y g c) (by simp [ne_nil]) = g := rfl

end Lemma

@[ext]
structure Chains (U : Universe C) (X : C) : Type (max u v) where
  dom : C
  chain : Chain U X dom

namespace Chains

section CategoryChains

structure Hom (c d : Chains U X) where
  hom : c.dom ⟶ d.dom

@[simp]
def id (c : Chains U X) : Hom c c where
  hom := 𝟙 c.dom

@[simp]
def comp {c d e : Chains U X} : Hom c d → Hom d e → Hom c e := fun x y ↦ ⟨x.hom ≫ y.hom⟩

instance CategoryChains : Category (Chains U X) where
  Hom := Hom
  id := id
  comp := comp

@[simp]
lemma comp_hom {c d e: Chains U X} {f : c ⟶ d} {g : d ⟶ e} : (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[simp]
lemma id_hom {c : Chains U X} : (𝟙 c : Hom c c).hom = 𝟙 c.dom := rfl

@[simp]
lemma eqToHom_hom {c d: Chains U X} (h : c = d): (eqToHom h).hom = eqToHom (congrArg dom h):= by cases h; simp

@[ext]
lemma hom_ext {c d : Chains U X} {f g : c ⟶ d} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  simp at h
  simp [h]

end CategoryChains

section PreContextualStructure

variable {c d : Chains U X}

@[simp]
def one : Chains U X where
  dom := X
  chain := Chain.nil X

@[simp]
def gr (c : Chains U X) : ℕ := length c.chain

lemma one_uniq {c : Chains U X} : gr c = 0 → c = one := by
  simp
  intro h
  ext
  simp [eq_of_length_eq_zero h]
  simp [heq_of_length_eq_zero h]

instance UniqueToTerminal (h : IsTerminal t) (X : Chains U t) : Unique (X ⟶ one) where
  default := ⟨(isTerminalEquivUnique _ t h _).default⟩
  uniq a := by ext; apply (isTerminalEquivUnique _ t h _).uniq

instance SubsingletonToTerminal (h : IsTerminal t) (X : Chains U t) : Subsingleton (X ⟶ one) := @Unique.instSubsingleton _ ((UniqueToTerminal) h X)

def one_terminal (h : IsTerminal t) : IsTerminal (@one _ _ U t) := by
  have (X : Chains U t) : X ⟶ one := ⟨IsTerminal.from h X.dom⟩
  apply IsTerminal.ofUniqueHom this
  intro X m
  apply (SubsingletonToTerminal h _).allEq

@[simp]
def ft (c : Chains U X) : Chains U X where
  dom := tailObj c.chain
  chain := tail c.chain

lemma ft_one : ft (@one _ _ U X) = one := by simp [tailObj, tail]

lemma ft_gr {n : ℕ} (c : Chains U X): gr c = n + 1 → gr (ft c) = n := length_tail'

def proj (c : Chains U X) : c ⟶ ft c := ⟨toMap c.chain⟩

class isTerminal (t : C) where
  is_terminal : IsTerminal t

def is_terminal (t : C) [h : isTerminal t] : IsTerminal t := h.is_terminal

@[simp]
instance instChainsPreContextualCategory [h : isTerminal t] : PreContextualCategory (Chains U t) where
  Cat := by infer_instance
  gr := gr
  one := one
  one_gr := by aesop
  one_uniq := one_uniq
  one_terminal := one_terminal h.is_terminal
  ft := ft
  ft_one := ft_one
  ft_gr := ft_gr
  proj := proj

end PreContextualStructure

section ContextualStructure

variable {t : C} [isTerminal t] {d : Chains U t}
{Y : C} {p : Y ⟶ U.obj} {c : Chain U t Y}

lemma ne_nil_of_NR [h : NR d] : ne_nil d.chain := by
  have := h.nr
  dsimp [gr] at this
  rwa [ne_nil_iff_not_if_nil, length_eq_zero_iff_is_nil]

-- maybe use cases as those below???
def ft_map (c : Chains U t) [NR c] : (ft c).dom ⟶ U.obj := tailMap c.chain ne_nil_of_NR

abbrev cons (Y : C) (g : Y ⟶ U.obj) (e : Chain U t Y) : Chains U t := ⟨U.pb g, Chain.cons Y g e⟩

instance : NR (cons Y p c) where
  nr := by simp [gr, length]

def pb_cons (f : d ⟶ ft (cons Y p c)) : Chains U t where
  dom := U.pb (f.hom ≫ p)
  chain := Chain.cons d.dom (f.hom ≫ p) d.chain

variable {f : d ⟶ ft (cons Y p c)}

lemma gr_pb_cons : gr (pb_cons f) ≠ 0 := by simp [length]

lemma ft_pb_cons: ft (pb_cons f) = d := rfl

lemma pb_map_cons_comm (f : d ⟶ ft (cons Y p c)) : (U.pb_vmap (f.hom ≫ p) ≫ f.hom) ≫ p = U.pb_hmap (f.hom ≫ p) ≫ U.map := by rw [← U.comm, Category.assoc]

def pb_map_cons (f : d ⟶ ft (cons Y p c)) : pb_cons f ⟶ (cons Y p c) where
  hom := PullbackCone.IsLimit.lift (is_pullback (self := U) (f := p)) (U.pb_vmap (f.hom ≫ p) ≫ f.hom) (U.pb_hmap (f.hom ≫ p)) (pb_map_cons_comm _)

lemma pb_map_cons_fst : (pb_map_cons f).hom ≫ U.pb_vmap p = U.pb_vmap (f.hom ≫ p) ≫ f.hom := by apply PullbackCone.IsLimit.lift_fst

lemma pb_map_cons_snd : (pb_map_cons f).hom ≫ U.pb_hmap p = U.pb_hmap (f.hom ≫ p) := by apply PullbackCone.IsLimit.lift_snd

lemma comm_cons : (proj <| pb_cons f) ≫ eqToHom (ft_pb_cons (f := f)) ≫ f = (pb_map_cons f) ≫ proj (cons Y p c) := by
  ext
  simp
  symm
  apply PullbackCone.IsLimit.lift_fst

lemma pullback_id_obj_cons : pb_cons (𝟙 (ft (cons Y p c))) = cons Y p c := by
  ext
  simp [pb_cons]
  simp [pb_cons, tail, tailObj]
  rw [Category.id_comp]

lemma Functor.eqToHom_comp_iff_heq {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {W : C} {X : C} {Y : C} (f : W ⟶ X) (g : Y ⟶ X) (h : W = Y) : eqToHom h ≫ g = f ↔ HEq g f := by
  cases h
  simp

lemma pb_map_cons_id_map : pb_map_cons (𝟙 (ft (cons Y p c))) = eqToHom pullback_id_obj_cons := by
  symm
  ext
  simp [pb_map_cons, tailObj]
  apply PullbackCone.IsLimit.lift_eq (is_pullback (self := U) (f := p)) (U.pb_vmap (𝟙 Y ≫ p)) (U.pb_hmap (𝟙 Y ≫ p)) (by rw [Category.id_comp, U.comm])
  <;> simp [Functor.eqToHom_comp_iff_heq]
  <;> rw [Category.id_comp]

lemma chain_cons_heq_of_heq {c : Chain U X Y} {c' : Chain U X Y'} {f : Y ⟶ U.obj} {f' : Y' ⟶ U.obj} (h₁ : HEq Y Y') (h₂ : HEq f f') (h₃ : HEq c c') : HEq (Chain.cons _ f c) (Chain.cons _ f' c') := by
  cases h₁
  cases h₂
  cases h₃
  rfl

lemma pullback_id_map_cons : eqToHom pullback_id_obj_cons.symm ≫ pb_map_cons (𝟙 (ft (cons Y p c))) = 𝟙 (cons Y p c) := by rw [pb_map_cons_id_map]; simp

lemma pullback_comp_obj_cons {g : e ⟶ d} : pb_cons (g ≫ f) = pb_cons (g ≫ eqToHom (ft_pb_cons (f := f)).symm) := by
  simp [pb_cons]
  apply chain_cons_heq_of_heq (by rfl) (by simp) (by rfl)

lemma aux_hmap_heq (f g : X ⟶ U.obj) (h : f = g) : HEq (U.pb_hmap f) (U.pb_hmap g) := by cases h; rfl

lemma aux_vmap_heq (f g : X ⟶ U.obj) (h : f = g) : HEq (U.pb_vmap f) (U.pb_vmap g) := by cases h; rfl

lemma pullback_comp_map_cons {g : e ⟶ d} : pb_map_cons (g ≫ f) = eqToHom (pullback_comp_obj_cons (f := f) (g := g)) ≫  pb_map_cons (g ≫ eqToHom (ft_pb_cons (f := f)).symm) ≫ pb_map_cons f := by
  symm
  ext
  apply PullbackCone.IsLimit.lift_eq (is_pullback (self := U) (f := p)) (U.pb_vmap ((g.hom ≫ f.hom) ≫ p) ≫ g.hom ≫ f.hom) (U.pb_hmap ((g.hom ≫ f.hom) ≫ p)) (by rw [← U.comm, Category.assoc _ _ p, Category.assoc _ _ p, ← Category.assoc])
  simp
  rw [pb_map_cons_fst, ← Category.assoc _ _ f.hom, pb_map_cons_fst]
  simp only [ft, comp_hom, id_hom, Category.comp_id, Category.assoc]
  rw [← Category.assoc]
  congr
  rw [Functor.eqToHom_comp_iff_heq]
  apply aux_vmap_heq
  simp
  rw [comp_hom]
  simp
  rw [pb_map_cons_snd, pb_map_cons_snd, Functor.eqToHom_comp_iff_heq]
  apply aux_hmap_heq
  rw [comp_hom]
  simp

def is_pullback_from {X Y Z W : Chains U t} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {i : Z ⟶ W} (comm : f ≫ h = g ≫ i) (is : IsLimit <| PullbackCone.mk (f := h.hom) (g := i.hom) f.hom g.hom (by rw [← comp_hom, comm, comp_hom])) : IsLimit <| PullbackCone.mk (C := Chains U t) f g comm := by
  apply PullbackCone.isLimitAux'
  intro s
  use ⟨PullbackCone.IsLimit.lift is s.fst.hom s.snd.hom (by rw [← comp_hom, s.condition, comp_hom])⟩
  simp
  constructor; ext; apply PullbackCone.IsLimit.lift_fst
  constructor; ext; apply PullbackCone.IsLimit.lift_snd
  intro m hm hm'
  ext; simp
  apply PullbackCone.IsLimit.lift_eq is s.fst.hom s.snd.hom
  -- something peculiar happens `(PullbackCone.fst s).hom ≫ h.hom = (PullbackCone.snd s).hom ≫ i.hom` proved automatically, but simp, aesop, aesop_cat all fail.
  simp; rw [← comp_hom, hm]
  simp; rw [← comp_hom, hm']


noncomputable def is_pullback_cons: IsLimit <| PullbackCone.mk (proj (pb_cons f)) (pb_map_cons f) comm_cons := by
  apply is_pullback_from
  have pb := Limits.leftSquareIsPullback (pb_map_cons f).hom (U.pb_hmap p) f.hom p (U.pb_vmap (f.hom ≫ p)) (U.pb_vmap p) U.map (PullbackCone.IsLimit.lift_fst _ _ _ _).symm U.comm U.is_pullback (by simp [pb_map_cons_snd]; apply U.is_pullback)
  simp [proj, pb_cons, toMap]
  convert pb
  <;> simp

#check Nat.rec

@[elab_as_elim]
def cases_cons {h : (c : Chains U t) → [NR c] → Sort w}
(h' : ∀ {Y p c}, h (cons Y p c)) (c : Chains U t) [NR c]: h c := by
  cases c with
  | mk X c =>
    cases c with
    | nil => rename _ => inst; have := inst.nr; simp [gr, length] at this
    | cons Y g c => exact h'

variable {c d : Chains U t} [NR c]

def pb (f : d ⟶ ft c) : Chains U t := cases_cons pb_cons c f

def pb_map (f : d ⟶ ft c) : pb f ⟶ c := cases_cons (h := fun c ↦ (f : d ⟶ ft c) → (pb f ⟶ c)) pb_map_cons c f

lemma gr_pb {f : d ⟶ ft c} : gr (pb f) ≠ 0 := cases_cons (h := fun c ↦ (f : d ⟶ ft c) → (gr (pb f) ≠ 0)) (fun _ ↦ gr_pb_cons) c f

instance NR_pb {f : d ⟶ ft c} : NR (pb f) := ⟨gr_pb⟩

lemma ft_pb {f : d ⟶ ft c} : ft (pb f) = d := cases_cons (h := fun c ↦ (f : d ⟶ ft c) → (ft (pb f) = d)) (fun _ ↦ ft_pb_cons) c f

lemma comm {f : d ⟶ ft c} : (proj <| pb f) ≫ eqToHom (ft_pb (f := f)) ≫ f = (pb_map f) ≫ proj c := cases_cons (h := fun c ↦ (f : d ⟶ ft c) → ((proj <| pb f) ≫ eqToHom (ft_pb (f := f)) ≫ f = (pb_map f) ≫ proj c)) (fun _ ↦ comm_cons) c f

lemma pullback_id_obj : pb (𝟙 (ft c)) = c := cases_cons (h := fun c ↦ pb (𝟙 (ft c)) = c) (fun {Y p c} ↦ @pullback_id_obj_cons C _ U t Y p c) c

lemma pullback_id_map : eqToHom (pullback_id_obj (c := c)).symm ≫ pb_map (𝟙 (ft c)) = 𝟙 c := cases_cons (h := fun c ↦ eqToHom (pullback_id_obj (c := c)).symm ≫ pb_map (𝟙 (ft c)) = 𝟙 c) (fun {Y p c} ↦ @pullback_id_map_cons C _ U t Y p c) c

lemma pullback_comp_obj {c d e : Chains U t} [NR c] {f : d ⟶ ft c} {g : e ⟶ d} : pb (g ≫ f) = pb (g ≫ eqToHom (ft_pb (f := f)).symm) := cases_cons (h := fun c ↦ {f : d ⟶ ft c} → {g : e ⟶ d} → pb (g ≫ f) = pb (g ≫ eqToHom (ft_pb (f := f)).symm)) (fun {Y p c f} ↦ @pullback_comp_obj_cons C _ U t d Y p c f e) c

lemma pullback_comp_map {c d e : Chains U t} [NR c] {f : d ⟶ ft c} {g : e ⟶ d} : pb_map (g ≫ f) = eqToHom (pullback_comp_obj (f := f) (g := g)) ≫  pb_map (g ≫ eqToHom (ft_pb (f := f)).symm) ≫ pb_map f := cases_cons (h := fun c ↦ {f : d ⟶ ft c} → {g : e ⟶ d} → pb_map (g ≫ f) = eqToHom (pullback_comp_obj (f := f) (g := g)) ≫  pb_map (g ≫ eqToHom (ft_pb (f := f)).symm) ≫ pb_map f) (fun {Y p c f} ↦ @pullback_comp_map_cons C _ U t d Y p c f e) c

noncomputable def is_pullback {f : d ⟶ ft c} : IsLimit <| PullbackCone.mk (proj (pb f)) (pb_map f) comm := cases_cons (h := fun c ↦ (f : d ⟶ ft c) → (IsLimit <| PullbackCone.mk (proj (pb f)) (pb_map f) comm )) (fun _ ↦ is_pullback_cons) c f

noncomputable instance instChainsContextualCategory : ContextualCategory (Chains U t) where
  pb := pb
  pb_map := pb_map
  gr_pb := gr_pb
  ft_pb := ft_pb
  comm := comm
  is_pullback := is_pullback
  pullback_id_obj := pullback_id_obj
  pullback_id_map := pullback_id_map
  pullback_comp_obj := pullback_comp_obj
  pullback_comp_map := pullback_comp_map

end ContextualStructure

section TypeStructures

variable {t : C} [isTerminal t] (Γ : Chains U t) (A : Ext Γ) (c d : Chains U t)

lemma ft_lalal (c d : Chains U t)  (h' : ft c = d) : d.dom = tailObj c.chain := by
  simp [ft] at h'
  rw [← h']

example (c d : Chains U t) (h : ne_nil c.chain) (h' : ft c = d) : d.dom ⟶ U.obj := by
  cases c with
  | mk Y c =>
    cases c with
    | nil => simp [ne_nil] at h
    | cons Y g c =>
        exact eqToHom (ft_lalal (cons Y g c) d h') ≫ g

example (c : Chains U t) (h : ne_nil c.chain) : (ft c).dom ⟶ U.obj := by
  cases c with
  | mk Y c =>
    cases c with
    | nil => simp [ne_nil] at h
    | cons Y g c => exact g




#exit
  cases c with
  | mk Y c =>
    cases c with
    | nil => simp [ne_nil] at h
    | cons Y g c =>
        simp [ft] at h'
        rw [← h']


example : Γ.dom ⟶ U.obj := by
  have := ft A.obj
  sorry



variable [HasPullbacks C] [LocallyCartesianClosed C] [HasBinaryProducts C]





#exit
def Pi_type (S : Pi_structure U) : Pi_type (Chains U t) where
  form Γ Γ'':= {
    obj := _
    ft := _
    gr := _
  }
  intro := sorry
  elim_tm := sorry
  elim_comm := sorry
  comp := sorry
