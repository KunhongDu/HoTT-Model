import Mathlib.Tactic
import HoTTModel.Universe
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

def Hom (c d : Chains U X) := c.dom ⟶ d.dom

@[simp]
def id (c : Chains U X) := 𝟙 (c.dom)

@[simp]
def comp {c d e : Chains U X} : Hom c d → Hom d e → Hom c e := @CategoryStruct.comp _ _ (c.dom) (d.dom) (e.dom)

instance CategoryChains : Category (Chains U X) where
  Hom := Hom
  id := id
  comp := comp

variable {c d : Chains U X}

def toObjHom (f : c ⟶ d) : c.dom ⟶ d.dom := f

lemma hom_def : (c ⟶ d) = (c.dom ⟶ d.dom) := rfl

@[simp]
lemma id_def : 𝟙 c = 𝟙 (c.dom) := rfl

lemma eqToHom_toObjHom (h : c = d) : eqToHom h = eqToHom (congrArg dom h) := rfl

@[simp]
lemma comp_def {f : c ⟶ d} {g : d ⟶ e} : f ≫ g = CategoryStruct.comp (obj := C) f g:= rfl

end CategoryChains

section PreContextualStructure

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

-- this is badly written
instance UniqueToTerminal (h : IsTerminal t) (X : Chains U t) : Unique (X ⟶ one) := isTerminalEquivUnique _ t h _

def one_terminal (h : IsTerminal t) : IsTerminal (@one _ _ U t) := by
  have (X : Chains U t) : X ⟶ one := IsTerminal.from h X.dom
  apply IsTerminal.ofUniqueHom this
  intro X m
  have : Subsingleton (X ⟶ one) := @Unique.instSubsingleton _ ((UniqueToTerminal) h X)
  apply Subsingleton.allEq

@[simp]
def ft (c : Chains U X) : Chains U X where
  dom := tailObj c.chain
  chain := tail c.chain

lemma ft_one : ft (@one _ _ U X) = one := by simp [tailObj, tail]

lemma ft_gr {n : ℕ} (c : Chains U X): gr c = n + 1 → gr (ft c) = n := length_tail'

def proj (c : Chains U X) : c ⟶ ft c := toMap c.chain

class isTerminal (t : C) where
  is_terminal : IsTerminal t

lemma is_terminal (t : C) [h : isTerminal t] : IsTerminal t := h.is_terminal

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

section ContextualStrucutre

variable {t : C} [isTerminal t] {c d : Chains U t}

lemma ne_nil_of_NR [h : NR c] : ne_nil c.chain := by
  have := h.nr
  dsimp [gr] at this
  rwa [ne_nil_iff_not_if_nil, length_eq_zero_iff_is_nil]

def ft_map (c : Chains U t) [NR c] : (ft c).dom ⟶ U.obj := tailMap c.chain ne_nil_of_NR

def pb [NR c] (f : d ⟶ ft c) : Chains U t where
  dom := U.pb (f ≫ ft_map c)
  chain := Chain.cons d.dom (f ≫ ft_map c) d.chain

lemma gr_pb [NR c] {f : d ⟶ ft c} : gr (pb f) ≠ 0 := by
  simp [gr, pb, length]

instance NR_pb [NR c] {f : d ⟶ ft c} : NR (pb f) := ⟨gr_pb⟩

lemma ft_pb [NR c] {f : d ⟶ ft c} : ft (pb f) = d := rfl

lemma pb_tailMap_eq (c : Chain U X Y) (h : ne_nil c) : U.pb (tailMap c h) = Y := by
  cases c with
  | nil => simp [ne_nil] at h
  | cons Y g c => rfl

lemma pb_ft_map_eq [NR c] : U.pb (ft_map c) = c.dom := pb_tailMap_eq _ _

lemma pb_map_aux_comm [NR c] (f : d ⟶ ft c) : toObjHom (proj (pb f) ≫ f) ≫ ft_map c = U.pb_hmap (f ≫ ft_map c) ≫ U.map := by
  simp only [ft, toObjHom, comp_def, Category.assoc]
  rw [← U.comm]
  apply congrArg _ rfl

def pb_map_aux [NR c] (f : d ⟶ ft c) : (pb f).dom ⟶ U.pb (ft_map c) := by
  apply PullbackCone.IsLimit.lift (@is_pullback _ _ U _ (ft_map c)) (proj (pb f) ≫ f) (U.pb_hmap (f ≫ ft_map c)) (pb_map_aux_comm f)

lemma pb_map_aux_fst [NR c] (f : d ⟶ ft c) : pb_map_aux f ≫ (U.pb_vmap (ft_map c)) = proj (pb f) ≫ f := by apply PullbackCone.IsLimit.lift_fst

lemma pb_map_aux_fst' [NR c] (f : d ⟶ ft c) : pb_map_aux f ≫ (U.pb_vmap (ft_map c)) = toObjHom (proj (pb f) ≫ f) := by apply PullbackCone.IsLimit.lift_fst

lemma pb_map_aux_fst'' [NR c] (f : d ⟶ ft c) : pb_map_aux f ≫ (U.pb_vmap (ft_map c)) = CategoryStruct.comp (obj := C) (proj (pb f)) f := pb_map_aux_fst _

lemma pb_map_aux_snd [NR c] (f : d ⟶ ft c) : pb_map_aux f ≫ (U.pb_hmap (ft_map c)) = (U.pb_hmap (f ≫ ft_map c)) := by apply PullbackCone.IsLimit.lift_snd

lemma pb_map_aux_id_obj [NR c] : (pb (𝟙 (ft c))).dom = U.pb (ft_map c) := by
  simp [pb]

-- these are badly writtern!!!

lemma Functor.eqToHom_comp_iff_heq {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {W : C} {X : C} {Y : C} (f : W ⟶ X) (g : Y ⟶ X) (h : W = Y) : eqToHom h ≫ g = f ↔ HEq g f := by
  cases h
  simp

lemma Functor.comp_eqToHom_iff_heq {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {W : C} {X : C} {Y : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X = Y) : f ≫ eqToHom h = g ↔ HEq f g := by
  cases h
  simp

lemma Functor.comp_eqToHom_comp_iff_heq {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {W X Y Z V: C} (f : X ⟶ Y) (g : W ⟶ Z) (h₁ : W = X) (h₂ : Y = V) (h₃ : Z = V) : eqToHom h₁ ≫ f ≫ eqToHom h₂ = g ≫ eqToHom h₃ ↔ HEq f g:= by
  cases h₁
  cases h₂
  cases h₃
  simp

lemma Functor.heq_iff_heq_comp_eqToHom {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {W W' X X' Y Y' : C} (f : W ⟶ X) (g : W' ⟶ Y) (h : X = X') (h' : Y = Y'): HEq f g ↔ HEq (f ≫ eqToHom h) (g ≫ eqToHom h') := by
  cases h
  cases h'
  simp

lemma test1 {c : Chain U X Y} (h : ne_nil c) : HEq (U.pb_vmap (tailMap c h)) (U.pb_vmap (𝟙 (tailObj c) ≫ tailMap c h)) := by
  cases c with
  | nil => simp [ne_nil] at h
  | cons c g Y => rw [Category.id_comp]

lemma test2 {c : Chain U X Y} (h : ne_nil c) : HEq (U.pb_hmap (tailMap c h)) (U.pb_hmap (𝟙 (tailObj c) ≫ tailMap c h)) := by
  cases c with
  | nil => simp [ne_nil] at h
  | cons c g Y => rw [Category.id_comp]

lemma pb_map_aux_id_map [NR c] : pb_map_aux (𝟙 (ft c)) = eqToHom pb_map_aux_id_obj := by
  symm
  have := PullbackCone.IsLimit.lift_eq (@is_pullback _ _ U _ (ft_map c)) (proj (pb (𝟙 (ft c))) ≫ (𝟙 (ft c))) (U.pb_hmap ((𝟙 (ft c)) ≫ ft_map c)) (pb_map_aux_comm _) (eqToHom pb_map_aux_id_obj)
  apply this
  simp [proj, pb, toMap, ft_map]
  -- why doesn't simp work???
  have : U.pb_vmap (𝟙 (tailObj c.chain) ≫ tailMap c.chain ne_nil_of_NR) ≫ 𝟙 (tailObj c.chain) = U.pb_vmap (𝟙 (tailObj c.chain) ≫ tailMap c.chain ne_nil_of_NR) := by simp only [Category.comp_id]
  -- rw [Category.id_comp] does not work here
  rw [this, Functor.eqToHom_comp_iff_heq]
  apply test1
  simp [proj, pb, toMap, ft_map]
  rw [Functor.eqToHom_comp_iff_heq]
  apply test2

lemma toMap_heq_pb_vmap {c : Chain U X Y} (h : ne_nil c) : eqToHom (pb_tailMap_eq c h) ≫ toMap c = U.pb_vmap (tailMap c h) := by
  cases c with
  | nil => simp [ne_nil] at h
  | cons Y g c => simp; rfl

def pb_map [NR c] (f : d ⟶ ft c) : pb f ⟶ c := by
  rw [hom_def]
  exact (pb_map_aux f) ≫ (eqToHom pb_ft_map_eq)

lemma comm {c d : Chains U t} [NR c] {f : d ⟶ ft c} : (proj <| pb f) ≫ eqToHom (ft_pb (f := f)) ≫ f = (pb_map f) ≫ proj c := by
  simp [pb_map]
  have : eqToHom pb_ft_map_eq ≫ proj c = (PullbackCone.mk (U.pb_vmap (ft_map c)) (U.pb_hmap (ft_map c)) U.comm).fst := toMap_heq_pb_vmap _
  rw [this]
  symm
  apply PullbackCone.IsLimit.lift_fst

lemma comm' {c d : Chains U t} [NR c] {f : d ⟶ ft c} : (proj <| pb f) ≫ eqToHom (ft_pb (f := f)) ≫ f = CategoryStruct.comp (obj := C) (pb_map f) (proj c) := comm

-- put these two somewhere before
lemma chain_split (c: Chain U X Y) (h : ne_nil c) : HEq c (Chain.cons _ (tailMap c h) (tail c)) := by
  cases c with
  | nil => simp [ne_nil] at h
  | cons Y g c => simp [tailObj, tailMap, tail]

lemma chain_cons_heq_of_heq {c : Chain U X Y} {c' : Chain U X Y'} {f : Y ⟶ U.obj} {f' : Y' ⟶ U.obj} (h₁ : HEq Y Y') (h₂ : HEq f f') (h₃ : HEq c c') : HEq (Chain.cons _ f c) (Chain.cons _ f' c') := by
  cases h₁
  cases h₂
  cases h₃
  rfl

lemma pullback_id_obj {c : Chains U t} [NR c]: pb (𝟙 (ft c)) = c := by
  ext
  simp [pb, ft_map]
  apply pb_tailMap_eq
  simp [pb]
  /-
  cases c
  dsimp
  case mk d c h =>
  -/
  apply HEq.symm <| HEq.trans (chain_split c.chain ne_nil_of_NR) (chain_cons_heq_of_heq (by rfl) (by simp [ft_map]) (by rfl))

lemma pullback_id_map {c : Chains U t} [NR c]: eqToHom (pullback_id_obj (c := c)).symm ≫ pb_map (𝟙 (ft c)) = 𝟙 c := by
  simp only [pb_map, eq_mpr_eq_cast, cast_eq, comp_def]
  rw [pb_map_aux_id_map, eqToHom_toObjHom]
  simp

lemma pullback_comp_obj {c d e : Chains U t} [NR c] {f : d ⟶ ft c} {g : e ⟶ d} : pb (g ≫ f) = pb (g ≫ eqToHom (ft_pb (f := f)).symm) := by
  simp
  ext
  simp [pb, ft_map, tailMap]
  simp [pb, ft_map]
  apply chain_cons_heq_of_heq (by rfl) (by simp [tailMap]) (by rfl)

lemma aux_hmap_heq (f g : X ⟶ U.obj) (h : f = g) : HEq (U.pb_hmap f) (U.pb_hmap g) := by cases h; rfl

lemma aux_vmap_heq (f g : X ⟶ U.obj) (h : f = g) : HEq (U.pb_vmap f) (U.pb_vmap g) := by cases h; rfl

lemma pullback_comp_map_aux {c d e : Chains U t} [NR c] {f : d ⟶ ft c} {g : e ⟶ d} : pb_map_aux (g ≫ f) = toObjHom (eqToHom (pullback_comp_obj (f := f) (g := g))) ≫ ((pb_map_aux (g ≫ eqToHom ft_pb.symm) ≫ eqToHom pb_ft_map_eq) ≫ pb_map_aux f) := by
  symm
  simp only [toObjHom]
  apply PullbackCone.IsLimit.lift_eq (@is_pullback _ _ U _ (ft_map c)) (proj (pb (g ≫ f)) ≫ (g ≫ f)) (U.pb_hmap ((g ≫ f) ≫ ft_map c)) (pb_map_aux_comm _) (toObjHom (eqToHom (pullback_comp_obj (f := f) (g := g))) ≫ ((pb_map_aux (g ≫ eqToHom ft_pb.symm) ≫ eqToHom pb_ft_map_eq) ≫ pb_map_aux f))
  simp only [toObjHom]
  simp only [ft, comp_def, PullbackCone.mk_pt, Category.comp_id,
    PullbackCone.mk_π_app, Category.assoc]
  rw [pb_map_aux_fst f]
  simp only [comp_def, eqToHom_toObjHom]
  /-
  have aux := pb_map_aux_fst' (g ≫ eqToHom (ft_pb (f := f)).symm)
  rw [aux] does not work!!! becuase `f` have type `d ⟶ ft c` not matched with `dom` definition
  -/
  have := congrArg (fun x ↦ x ≫ f) (pb_map_aux_fst (g ≫ eqToHom (ft_pb (f := f)).symm))
  have aux := congrArg (fun x ↦ eqToHom (pullback_comp_obj (f := f) (g := g)) ≫ x) this
  simp only [ft, id_def, comp_def, Category.assoc, Category.comp_id] at aux
  have : eqToHom pb_ft_map_eq ≫ proj (pb f) = U.pb_vmap (ft_map (pb f)) := by simp [proj, pb, toMap, ft_map, tailMap]
  rw [← Category.assoc (eqToHom pb_ft_map_eq) (proj (pb f)) f, this]
  -- rw [aux] again does not work
  apply Eq.trans aux
  have : eqToHom (pullback_comp_obj (f := f) (g := g)) ≫ proj (pb (g ≫ eqToHom (ft_pb (f := f)).symm) ) = proj (pb (g ≫ f)) := by
    simp [proj, pb, toMap, ft_map, tailMap_cons, eqToHom_toObjHom]
    rw [Functor.eqToHom_comp_iff_heq]
    apply aux_vmap_heq
    simp
  -- rw [this] does not work
  have := congrArg (fun x ↦ x ≫ (g ≫ f)) this
  simp only [ft, comp_def, id_def, Category.assoc] at this
  simp
  exact this

  -- second equality
  simp only [toObjHom, ft, comp_def, PullbackCone.mk_pt, id_def, Category.comp_id,
  PullbackCone.mk_π_app, Category.assoc]
  rw [pb_map_aux_snd f]
  have aux := congrArg (fun x ↦ toObjHom (eqToHom (pullback_comp_obj (f := f) (g := g))) ≫ x) (pb_map_aux_snd (g ≫ eqToHom (ft_pb (f := f)).symm))
  simp only [toObjHom] at aux
  simp
  apply Eq.trans aux
  simp only [pb, ft_map, tailMap_cons, eqToHom_toObjHom]
  rw [Functor.eqToHom_comp_iff_heq]
  apply aux_hmap_heq
  simp only [ft, eqToHom_refl, comp_def, Category.comp_id, Category.assoc]

lemma pullback_comp_map {c d e : Chains U t} [NR c] {f : d ⟶ ft c} {g : e ⟶ d} : pb_map (g ≫ f) = eqToHom (pullback_comp_obj (f := f) (g := g)) ≫  pb_map (g ≫ eqToHom (ft_pb (f := f)).symm) ≫ pb_map f := by
  have := pullback_comp_map_aux (f := f) (g := g)
  simp only [toObjHom] at this
  simp only [pb_map, eq_mpr_eq_cast, cast_eq]
  -- apply (fun x ↦ x ≫ eqToHom (pb_ft_map_eq (c := c))) at this does not work
  apply_fun (fun x ↦ x ≫ eqToHom (pb_ft_map_eq (c := c))) at this
  simp only [ft, comp_def] at this
  rw [Category.assoc, Category.assoc] at this
  -- rw does not work
  exact this

lemma is_pullback_aux {c d : Chains U t} [NR c] {f : d ⟶ ft c} : IsLimit <| PullbackCone.mk (C := C) (proj (pb f)) (pb_map_aux f) (pb_map_aux_fst _).symm := by
  apply Limits.leftSquareIsPullback _ (U.pb_hmap (ft_map c)) _ (ft_map c) _ _ U.map _ U.comm U.is_pullback
  simp_rw [pb_map_aux_snd]
  apply U.is_pullback

lemma test3 {c : Chain U X Y} (h : ne_nil c): HEq (U.pb_vmap (tailMap c h)) (toMap c) := by
  cases c with
  | nil => simp [ne_nil] at h
  | cons c g Y => rfl

lemma test4 {c : Chains U t} [NR c] : U.pb_vmap (ft_map c)= eqToHom pb_ft_map_eq ≫ proj c := by simp [proj, ft_map]; symm; rw [Functor.eqToHom_comp_iff_heq]; symm; apply test3 _

lemma is_pullback_from {X Y Z W : Chains U t} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {i : Z ⟶ W} (comm : f ≫ h = g ≫ i) (is : IsLimit <| PullbackCone.mk (C := C) f g comm) : IsLimit <| PullbackCone.mk (C := Chains U t) f g comm := sorry

lemma pullback_heq {X Y Z W : C} [Category C] {f : X ⟶ Y} {g g' : X ⟶ Z} {h h' : Y ⟶ W} {i : Z ⟶ W} (comm : f ≫ h = g ≫ i) (comm' : f ≫ h' = g' ≫ i) (eq₁ : g = g') (eq₂ : h = h') (is : IsLimit <| PullbackCone.mk (C := C) f g' comm') : IsLimit <| PullbackCone.mk f g comm := by
  cases eq₁
  cases eq₂
  exact is

noncomputable def is_pullback {c d : Chains U t} [NR c] {f : d ⟶ ft c} : IsLimit <| PullbackCone.mk (proj (pb f)) (pb_map f) comm := by
  apply is_pullback_from
  have pb₁ := Limits.bigSquareIsPullback (C := C) (pb_map_aux f) (eqToHom ((pb_ft_map_eq (c:=c)))) f (𝟙 (ft c)) (proj (pb f)) (U.pb_vmap _) (proj c) (by rw [pb_map_aux_fst]; rfl) (by simp; apply test4) (by apply PullbackCone.IsLimit.pullback_eqToHom _ (Eq.refl _)) is_pullback_aux

  have pb₂ := Limits.bigSquareIsPullback (C := C) (𝟙 (pb f)) (pb_map f) (𝟙 d) (f ≫ 𝟙 (ft c)) (proj (pb f)) (proj (pb f)) (proj c) (by simp) (by simp; rw [← comm']; simp) pb₁ (by apply PullbackCone.IsLimit.pullback_eqToHom (Eq.refl _) (Eq.refl _))

  have pb₃ := pullback_heq (C := C) (f := proj (pb f)) (g := pb_map f) (g' := 𝟙 (pb f) ≫ pb_map_aux f ≫ eqToHom ((pb_ft_map_eq (c:=c)))) (h := 𝟙 (ft (pb f)) ≫ f) (h' := 𝟙 d ≫ f ≫ 𝟙 (ft c)) (i := proj c) comm (by simp; rw [Category.id_comp (obj := C) f, ← pb_map_aux_fst'', test4]) (by simp [pb_map]) (by simp; rw [Category.id_comp (obj := C) f]) pb₂

  exact pb₃

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

end ContextualStrucutre
