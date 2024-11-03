import HoTTModel.TypeStructures
import HoTTModel.Contextual

open ContextualCategory CategoryTheory Limits

namespace Universe
variable {C : Type u} [CategoryTheory.Category.{v, u} C] {U : Universe C}

inductive Chain (U : Universe C) : C → C → Type (max u v)
| nil X : U.Chain X X
| cons (Y : C) (g : Y ⟶ U.down) (c : U.Chain X Y)  : U.Chain X (U.pt g)

namespace Chain
variable {X Y : C}

def obj (_ : U.Chain X Y) : C := Y

def tailObj : U.Chain X Y → C
| nil _ => X
| cons Y _ _ => Y

def tail : (c : U.Chain X Y) → U.Chain X c.tailObj
| nil _ => nil X
| cons _ _ c => c

def proj : (c : U.Chain X Y) → (Y ⟶ tailObj c)
| nil _ => 𝟙 X
| cons _ g _ => U.snd g

@[simp]
def ne_nil : U.Chain X Y → Prop
| nil _ => False
| cons _ _ _ => True

@[simp]
abbrev is_nil (c : U.Chain X Y) : Prop := ¬ c.ne_nil

lemma ne_nil_iff_not_is_nil {c : U.Chain X Y} : c.ne_nil ↔ ¬ c.is_nil := by
  simp only [not_not]

lemma is_nil_iff_not_ne_nil {c : U.Chain X Y} : c.is_nil ↔ ¬ c.ne_nil := by rfl

lemma ne_nil.cons {c : U.Chain X Y} : (cons Y g c).ne_nil := by simp [ne_nil]

def tailHom : (c : U.Chain X Y) → (h : c.ne_nil) → (c.tailObj ⟶ U.down)
| nil _, h => False.elim h
| cons _ g _, _ => g

def length : {Y : C} → U.Chain X Y → ℕ
| _, nil _ => 0
| _, cons _ _ c => c.length + 1

section LengthLemma

lemma is_nil_iff_length_eq_zero {c : U.Chain X Y} : c.is_nil ↔ c.length = 0  := by
  cases c with
  | nil => simp only [is_nil, ne_nil, not_false_eq_true, length]
  | cons _ _ _ => simp [is_nil, length]

lemma ne_nil_iff_length_ne_zero {c : U.Chain X Y} : c.ne_nil ↔ c.length ≠ 0  := by
  simp only [ne_eq, ← is_nil_iff_length_eq_zero, ne_nil_iff_not_is_nil]

lemma is_nil.of_length_eq_zero {c : U.Chain X Y} (h : length c = 0) : c.is_nil := by
  rwa [is_nil_iff_length_eq_zero]

lemma length_eq_zero_of_is_nil {c : U.Chain X Y} (h : is_nil c) : length c = 0  := by
  rwa [← is_nil_iff_length_eq_zero]

lemma eq_of_length_eq_zero {c : U.Chain X Y} (h : length c = 0) :
    Y = X := by
  cases c with
  | nil => rfl
  | cons Y g c => simp [length] at h

lemma heq_of_length_eq_zero {c : U.Chain X Y} (h : length c = 0) :
    HEq c (Chain.nil (U:= U) X) := by
  cases c with
  | nil => rfl
  | cons Y g c => simp [length] at h

lemma length_tail {c : U.Chain X Y} :
    length (tail c) = length c - 1 := by
  cases c <;> rfl

lemma length_tail' {c : U.Chain X Y} :
    length c = n + 1 → length (tail c) = n := by
  intro h; rw [length_tail, h]; rfl

end LengthLemma

section Lemma

lemma tailHom_cons {g : Y ⟶ U.down} (c : U.Chain X Y) :
  (Chain.cons Y g c).tailHom (by simp) = g := rfl

end Lemma

end Chain

@[ext]
structure Chains (U : Universe C) (X : C) : Type (max u v) where
  dom : C
  chain : U.Chain X dom

@[simp]
def Chain.toChains (c : U.Chain X Y) : U.Chains X where
  dom := Y
  chain := c

namespace Chains

open Chain

section CategoryChains

structure Hom (c d : U.Chains X) where
  hom : c.dom ⟶ d.dom

@[simp]
def id (c : U.Chains X) : Hom c c where
  hom := 𝟙 c.dom

@[simp]
def comp {c d e : U.Chains X} :
    Hom c d → Hom d e → Hom c e :=
  fun x y ↦ ⟨x.hom ≫ y.hom⟩

instance CategoryChains : Category (U.Chains X) where
  Hom := Hom
  id := id
  comp := comp

@[simp]
lemma comp_hom {c d e: U.Chains X} {f : c ⟶ d} {g : d ⟶ e} :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[simp]
lemma id_hom {c : U.Chains X} :
    (𝟙 c : Hom c c).hom = 𝟙 c.dom :=
  rfl

@[simp]
lemma eqToHom_hom {c d: U.Chains X} (h : c = d):
    (eqToHom h).hom = eqToHom (congrArg dom h):= by
  cases h; simp

@[ext]
lemma hom_ext {c d : U.Chains X} {f g : c ⟶ d} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  simp at h
  simp [h]

end CategoryChains

section PreContextualStructure

variable {X : C} {c d : U.Chains X}

@[simp]
def one : U.Chains X := (Chain.nil X).toChains

@[simp]
def gr (c : U.Chains X) : ℕ := c.chain.length

lemma one_uniq {c : U.Chains X} : gr c = 0 → c = one := by
  simp
  intro h
  ext
  simp [eq_of_length_eq_zero h]
  simp [heq_of_length_eq_zero h]

class isTerminal (t : C) where
  is_terminal : IsTerminal t

def is_terminal (t : C) [h : isTerminal t] :
    IsTerminal t :=
  h.is_terminal

instance UniqueToTerminal [h : isTerminal t] (X : U.Chains t) :
    Unique (X ⟶ one) where
  default := ⟨(isTerminalEquivUnique _ t h.1 _).default⟩
  uniq a := by ext; apply (isTerminalEquivUnique _ t h.1 _).uniq

def one_terminal [isTerminal t] : IsTerminal (@one _ _ U t) :=
  IsTerminal.ofUniqueHom (fun _ ↦ default) (fun _ ↦ Unique.uniq _)

@[simp]
def ft (c : U.Chains X) : U.Chains X where
  dom := c.chain.tailObj
  chain := c.chain.tail

lemma ft_one : ft (@one _ _ U X) = one :=
  by simp [tailObj, Chain.tail]

lemma ft_gr {n : ℕ} (c : U.Chains X) :
    gr c = n + 1 → gr (ft c) = n :=
  length_tail'

def proj (c : U.Chains X) : c ⟶ ft c :=
  ⟨c.chain.proj⟩

@[simp]
instance instChainsPreContextualCategory [isTerminal t] :
    PreContextualCategory (U.Chains t) where
  Cat := by infer_instance
  gr := gr
  one := one
  one_gr := by aesop
  one_uniq := one_uniq
  one_terminal := one_terminal
  ft := ft
  ft_one := ft_one
  ft_gr := ft_gr
  proj := proj

end PreContextualStructure

section ContextualStructure

variable {t : C} [isTerminal t] {d : U.Chains t}
  {Y : C} {p : Y ⟶ U.down} {c : U.Chain t Y}

lemma ne_nil_of_NR [h : NR d] : ne_nil d.chain := by
  rw [ne_nil_iff_not_is_nil, is_nil_iff_length_eq_zero]
  exact h.nr

-- maybe use cases as those below???
def ft_hom (c : U.Chains t) [NR c] : (ft c).dom ⟶ U.down :=
  c.chain.tailHom ne_nil_of_NR

def cons (Y : C) (g : Y ⟶ U.down) (e : U.Chain t Y) : U.Chains t :=
  ⟨U.pt g, Chain.cons Y g e⟩

def cons' (d : U.Chains t) (g : d.dom ⟶ U.down) := cons _ g d.chain

omit [isTerminal t] in
@[simp]
lemma ft_cons' {g : d.dom ⟶ U.down} : (d.cons' g).ft = d := by
  simp [cons', cons, tailObj, tail]

instance : NR (cons Y p c) where
  nr := by simp [gr, length]

def pb_cons (f : d ⟶ ft (cons Y p c)) : U.Chains t where
  dom := U.pt (f.hom ≫ p)
  chain := Chain.cons d.dom (f.hom ≫ p) d.chain

variable {f : d ⟶ ft (cons Y p c)}

-- note `ft (cons Y p c) = c.toChains` definitionally

omit [isTerminal t] in
lemma gr_pb_cons_ne_zero : gr (pb_cons f) ≠ 0 := by simp [length]

omit [isTerminal t] in
lemma ft_pb_cons: ft (pb_cons f) = d := rfl

omit [isTerminal t] in
lemma pb_map_cons_comm (f : d ⟶ ft (cons Y p c)) :
    U.fst (f.hom ≫ p) ≫ U.hom = (U.snd (f.hom ≫ p) ≫ f.hom) ≫ p :=
  by rw [U.comm, Category.assoc]

noncomputable def pb_map_cons (f : d ⟶ ft (cons Y p c)) : pb_cons f ⟶ (cons Y p c) where
  hom := (U.isPullback p).lift (U.fst (f.hom ≫ p)) (U.snd (f.hom ≫ p) ≫ f.hom)
    (pb_map_cons_comm _)

omit [isTerminal t] in
lemma pb_map_cons_fst : (pb_map_cons f).hom ≫ U.fst p = U.fst (f.hom ≫ p) :=
  (U.isPullback p).lift_fst _ _ _

omit [isTerminal t] in
lemma pb_map_cons_snd : (pb_map_cons f).hom ≫ U.snd p = U.snd (f.hom ≫ p) ≫ f.hom :=
  (U.isPullback p).lift_snd _ _ _

omit [isTerminal t] in
lemma comm_cons :
  (pb_map_cons f) ≫ proj (cons Y p c) = ((proj <| pb_cons f) ≫ eqToHom (ft_pb_cons (f := f))) ≫ f := by
  ext; simp
  apply PullbackCone.IsLimit.lift_snd _ _ _ _

omit [isTerminal t] in
lemma pullback_id_obj_cons : pb_cons (𝟙 (ft (cons Y p c))) = cons Y p c := by
  ext
  . simp [pb_cons]; rfl
  . simp [pb_cons, cons, tail, tailObj]; rw [Category.id_comp]

lemma _root_.CategoryTheory.eqToHom_comp_iff_heq {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C]
  {W : C} {X : C} {Y : C} (f : W ⟶ X) (g : Y ⟶ X) (h : W = Y) :
    eqToHom h ≫ g = f ↔ HEq g f := by
  cases h
  simp

omit [isTerminal t] in
lemma pb_map_cons_id_map :
    pb_map_cons (𝟙 (ft (cons Y p c))) = eqToHom pullback_id_obj_cons := by
  symm; ext
  simp [pb_map_cons, cons, tailObj]
  apply (U.isPullback p).hom_ext
  all_goals simp [eqToHom_comp_iff_heq]; congr; simp only [Category.id_comp]

omit [isTerminal t] in
lemma pullback_id_map_cons :
    eqToHom pullback_id_obj_cons.symm ≫ pb_map_cons (𝟙 (ft (cons Y p c))) = 𝟙 (cons Y p c) := by
  rw [pb_map_cons_id_map]; simp

omit [isTerminal t] in
lemma pullback_comp_obj_cons {g : e ⟶ d} :
    pb_cons (g ≫ f) = pb_cons (g ≫ eqToHom (ft_pb_cons (f := f)).symm) := by
  simp [pb_cons]
  congr 1; simp only [Category.assoc, Category.comp_id]

omit [isTerminal t] in
lemma pullback_comp_map_cons {g : e ⟶ d} :
    pb_map_cons (g ≫ f) =
      eqToHom (pullback_comp_obj_cons (f := f) (g := g)) ≫
        pb_map_cons (g ≫ eqToHom (ft_pb_cons (f := f)).symm) ≫ pb_map_cons f := by
  ext
  apply (U.isPullback p).hom_ext
  . simp
    rw [pb_map_cons_fst, pb_map_cons_fst, pb_map_cons_fst, ← Category.comp_id (eqToHom _ ≫ _),
        ← eqToHom_refl U.up (Eq.refl U.up), Category.assoc, conj_eqToHom_iff_heq _ _ _ (Eq.refl _)]
    congr 1; simp
  . simp
    rw [pb_map_cons_snd, pb_map_cons_snd, ← Category.assoc _ _ f.hom, pb_map_cons_snd,
        ← Category.comp_id (_ ≫ f.hom), ← eqToHom_refl (dom _) (Eq.refl _),
        conj_eqToHom_iff_heq _ _ _ (Eq.refl _)]
    simp
    congr 1
    . simp only [pb_cons, Category.assoc, Category.comp_id]
    . congr 1; simp only [Category.assoc, Category.comp_id]

def is_pullback_from {X Y Z W : U.Chains t} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {i : Z ⟶ W}
  (is : IsPullback f.hom g.hom h.hom i.hom) :
    IsPullback f g h i where
  w := by ext; simp [is.w]
  isLimit' := ⟨by
      apply PullbackCone.isLimitAux'; intro s
      use ⟨is.lift s.fst.hom s.snd.hom (by rw [← comp_hom, s.condition, comp_hom])⟩
      simp
      constructor; ext; apply PullbackCone.IsLimit.lift_fst
      constructor; ext; apply PullbackCone.IsLimit.lift_snd
      intro m hm hm'
      ext; simp
      apply is.hom_ext
      . simp; rw [← comp_hom, hm]
      . simp; rw [← comp_hom, hm']
    ⟩

noncomputable def is_pullback_cons:
    IsPullback (pb_map_cons f) ((pb_cons f).proj ≫ eqToHom (ft_pb_cons (f := f)))
      (proj (cons Y p c)) f := is_pullback_from {
  w := by change (pb_map_cons f ≫ _).hom = ((proj _ ≫ _) ≫ _).hom; rw [comm_cons]
  isLimit' := ⟨by
    apply topSquareIsPullback _ rfl (U.isPullback p).isLimit
    convert (U.isPullback (f.hom ≫ p) ).isLimit
    simp [PullbackCone.pasteVert, pb_map_cons]
    rfl
    ⟩}

@[elab_as_elim]
def cases_cons {h : (c : U.Chains t) → [NR c] → Sort w}
  (h' : ∀ {Y p c}, h (cons Y p c)) (c : U.Chains t) [NR c]:
    h c := by
  cases c with
  | mk X c =>
    cases c with
    | nil => rename _ => inst; have := inst.nr; simp [gr, length] at this
    | cons Y g c => exact h'

variable {c d : U.Chains t} [NR c]

def pb (f : d ⟶ ft c) :
    U.Chains t :=
  cases_cons pb_cons c f

noncomputable def pb_fst (f : d ⟶ ft c) :
    pb f ⟶ c :=
  cases_cons (h := fun c ↦ (f : d ⟶ ft c) → (pb f ⟶ c)) pb_map_cons c f

lemma gr_pb {f : d ⟶ ft c} :
    gr (pb f) ≠ 0 :=
  cases_cons (h := fun c ↦ (f : d ⟶ ft c) → (gr (pb f) ≠ 0)) (fun _ ↦ gr_pb_cons_ne_zero) c f

instance NR_pb {f : d ⟶ ft c} :
    NR (pb f) := ⟨gr_pb⟩

lemma ft_pb {f : d ⟶ ft c} :
    ft (pb f) = d :=
  cases_cons (h := fun c ↦ (f : d ⟶ ft c) → (ft (pb f) = d)) (fun _ ↦ ft_pb_cons) c f

/-
lemma comm {f : d ⟶ ft c} :
    (proj <| pb f) ≫ eqToHom (ft_pb (f := f)) ≫ f = (pb_fst f) ≫ proj c :=
  cases_cons (h := fun c ↦ (f : d ⟶ ft c) → ((proj <| pb f) ≫
    eqToHom (ft_pb (f := f)) ≫ f = (pb_fst f) ≫ proj c)) (fun _ ↦ comm_cons) c f-/

lemma pullback_id_obj :
    pb (𝟙 (ft c)) = c :=
  cases_cons (h := fun c ↦ pb (𝟙 (ft c)) = c) (fun {Y p c} ↦ @pullback_id_obj_cons C _ U t Y p c) c

lemma pullback_id_map :
    eqToHom (pullback_id_obj (c := c)).symm ≫ pb_fst (𝟙 (ft c)) = 𝟙 c :=
  cases_cons (h := fun c ↦ eqToHom (pullback_id_obj (c := c)).symm ≫ pb_fst (𝟙 (ft c)) = 𝟙 c)
    (fun {Y p c} ↦ @pullback_id_map_cons C _ U t Y p c) c

lemma pullback_comp_obj {c d e : U.Chains t} [NR c] {f : d ⟶ ft c} {g : e ⟶ d} :
    pb (g ≫ f) = pb (g ≫ eqToHom (ft_pb (f := f)).symm) :=
  cases_cons (h := fun c ↦ {f : d ⟶ ft c} → {g : e ⟶ d} → pb (g ≫ f) =
    pb (g ≫ eqToHom (ft_pb (f := f)).symm))
      (fun {Y p c f} ↦ @pullback_comp_obj_cons C _ U t d Y p c f e) c

lemma pullback_comp_map {c d e : U.Chains t} [NR c] {f : d ⟶ ft c} {g : e ⟶ d} :
    pb_fst (g ≫ f) = eqToHom (pullback_comp_obj (f := f) (g := g)) ≫
      pb_fst (g ≫ eqToHom (ft_pb (f := f)).symm) ≫ pb_fst f :=
  cases_cons (h := fun c ↦ {f : d ⟶ ft c} → {g : e ⟶ d} → pb_fst (g ≫ f) =
    eqToHom (pullback_comp_obj (f := f) (g := g)) ≫
      pb_fst (g ≫ eqToHom (ft_pb (f := f)).symm) ≫ pb_fst f)
      (fun {Y p c f} ↦ @pullback_comp_map_cons C _ U t d Y p c f e) c

noncomputable def is_pullback (f : d ⟶ ft c) :
    IsPullback (pb_fst f) (proj (pb f) ≫ eqToHom ft_pb) (proj c) f :=
  cases_cons
    (h := fun c ↦ (f : d ⟶ ft c) → (IsPullback (pb_fst f) (proj (pb f) ≫ eqToHom ft_pb) (proj c) f))
    (fun _ ↦ is_pullback_cons) c f

noncomputable instance instChainsContextualCategory : ContextualCategory (U.Chains t) where
  pb := pb
  pb_fst := pb_fst
  gr_pb := gr_pb
  ft_pb := ft_pb
  isPullback := is_pullback
  pullback_id_obj := pullback_id_obj
  pullback_id_map := pullback_id_map
  pullback_comp_obj := pullback_comp_obj
  pullback_comp_map := pullback_comp_map

end ContextualStructure

section TypeStructures

variable {t : C} [isTerminal t] (Γ : U.Chains t)

abbrev Ext := ContextualCategory.Ext Γ

namespace Ext
section
variable (A : Ext Γ)

-- `Ext` is not nil
lemma obj_chain_ne_nil : A.obj.chain.ne_nil := ne_nil_of_NR

-- `Ext` defines tailHom
@[simp]
def tailHom := A.obj.chain.tailHom A.obj_chain_ne_nil

abbrev proj' : A.obj.dom ⟶ A.obj.ft.dom := (proj A.obj).hom

end

def mk (c : U.Chain t Y) (h : ft ⟨_, c⟩ = Γ) (h' : ne_nil c): Ext Γ where
  obj := ⟨_, c⟩
  ft' := h
  gr' := by
    change c.length = gr _ + _
    rw [ne_nil_iff_length_ne_zero] at h'
    apply Nat.succ_pred_eq_of_ne_zero at h'
    have := h ▸ ft_gr ⟨_, c⟩ h'.symm
    rwa [this, eq_comm]

def rec (F : Ext Γ → Sort*)
  (h : ∀ (Y) (c : U.Chain t Y) (h h'), F (Ext.mk Γ c h h')) (c : Ext Γ) :
    F c := by
  cases c with
  | mk c _ gr' =>
    apply h
    change c.chain.length = _ at gr'
    rw [ne_nil_iff_length_ne_zero, gr']
    apply Nat.succ_ne_zero

def rec' (F : Ext Γ → Sort*)
  (h : ∀ (g : Γ.dom ⟶ U.down) (c : U.Chain t Γ.dom) h,
    F (Ext.mk Γ (Chain.cons Γ.dom g c) h ne_nil.cons)) (c : Ext Γ) :
    F c := by
  induction c using Ext.rec with
  | h Y c h' h'' =>
      cases c with
    | nil => simp at h''
    | cons Y g c =>
        cases h'; apply h

def mk' (g : Γ.dom ⟶ U.down) : Ext Γ where
  obj := cons' Γ g
  ft' := ft_cons'
  gr' := rfl

def rec'' (F : Ext Γ → Sort*)
  (h : ∀ g , F (Ext.mk' Γ g)) (c : Ext Γ) :
    F c := by
  induction c using Ext.rec' with
  | h g c h' =>
    convert h g
    simp [mk, mk', cons, cons']
    simp [ft, tail, tailObj] at h'
    apply_fun Chains.chain at h'
    exact h'

variable (A : Ext Γ)

variable {Γ} in
/--
```
mk Γ → U.up
↓       ↓
Γ → U.down
```
-/
def mk'.isPullback (g : Γ.dom ⟶ U.down) :
    IsPullback (U.fst g) (mk' Γ g).hom.hom U.hom g := by
  convert U.isPullback g
  simp only [Ext.hom, comp_hom, eqToHom_refl, id_hom, Category.comp_id]
  -- just rewrite this;; it's no good
  rfl

/--
```
A === U.pt ---→ U.up
       |          |
       ↓          ↓
       ft A --→  U.down
```
-/
lemma obj_eq_pt : A.obj.dom = U.pt A.tailHom := by
  induction A using Ext.rec'' with
  | h g => rfl

def fst : A.obj.dom ⟶ U.up :=
  eqToHom A.obj_eq_pt ≫ U.fst A.tailHom

def ft_eq : A.obj.ft.dom = Γ.dom := by simp only [← A.ft']; rfl

def proj : A.obj.dom ⟶ Γ.dom := A.obj.proj.hom ≫ eqToHom A.ft_eq

-- Better name???
def gen : Γ.dom ⟶ U.down := eqToHom (A.ft_eq).symm ≫ A.tailHom

/--
```
A === U.pt ---→ U.up
|       |          |
↓       ↓          ↓
Γ ===  ft A --→  U.down
```
-/
lemma isPullback :
    IsPullback A.fst A.hom.hom U.hom A.gen := by
  induction A using Ext.rec'' with
  | h g =>
      simp [mk', fst, Ext.hom, gen]
      convert U.isPullback _

lemma isPullbackLeft {X : C} (f : Γ.dom ⟶ X) (g : X ⟶ U.down) :
    IsPullback ((mk'.isPullback (f ≫ g)).liftIsPullbackOf (U.isPullback g) f rfl)
      (mk' Γ (f ≫ g)).hom.hom (U.snd g) f := by
  apply IsPullback.of_right _ _ (U.isPullback g)
  . convert mk'.isPullback (f ≫ g)
    simp only [IsPullback.liftIsPullbackOf_fst]
  . simp only [IsPullback.liftIsPullbackOf_snd]

end Ext
-- say we want to define the interpretation function from TT for CC.
-- the initial data is `⊢ B`, which should correponds to `Ext 1`
-- so indeed, `A : Ext Γ` is the data to start with

/-
variable {Γ} in
/--
  Equivalence bewteen homs in the over category and sections.
-/
noncomputable def Section.equiv {n} (A : Ext Γ n) :
    (Over.mk (𝟙 Γ.dom) ⟶ Over.mk A.hom.hom) ≃ Section A where
  toFun f := by
    apply Over.homMk (Hom.mk f.left) _
    ext; simp only [comp_hom]
    erw [Over.w f]; rfl
  invFun s := by
    apply Over.homMk s.left.hom _
    change (s.left ≫ A.hom).hom = _
    erw [Over.w s]; rfl
  left_inv := by intro f; rfl
  right_inv := by intro s; rfl


variable {Γ} in
/--
A section of `Ext` in chain defines a section in the original category.
-/
noncomputable def Section.toHom {n} {A : Ext Γ n} :=
  ⇑(Section.equiv A).symm

variable {Γ} in
/--
A section of `Ext` in chain from a section in the original category.
-/
noncomputable abbrev Section.ofHom {n} {A : Ext Γ n} :=
  ⇑(Section.equiv A)
-/

variable {Γ} in
/--
  Equivalence bewteen homs in the over category and sections.
-/
noncomputable def Section.equiv (A : Ext Γ) :
    (Over.mk (𝟙 Γ.dom) ⟶ Over.mk A.hom.hom) ≃ Section A where
  toFun f := by
    apply Over.homMk (Hom.mk f.left) _
    ext; simp only [comp_hom]
    erw [Over.w f]; rfl
  invFun s := by
    apply Over.homMk s.left.hom _
    change (s.left ≫ A.hom).hom = _
    erw [Over.w s]; rfl
  left_inv := by intro f; rfl
  right_inv := by intro s; rfl


variable {Γ} in
/--
A section of `Ext` in chain defines a section in the original category.
-/
noncomputable abbrev Section.toHom {A : Ext Γ} :=
  ⇑(Section.equiv A).symm

variable {Γ} in
/--
A section of `Ext` in chain from a section in the original category.
-/
noncomputable abbrev Section.ofHom {A : Ext Γ} :=
  ⇑(Section.equiv A)

noncomputable section

open Pi

namespace Pi
open LocallyCartesianClosed

variable [HasPullbacks C] [LocallyCartesianClosed C] [HasBinaryProducts C]

variable (S : Pi.Structure U) {Γ} {A : Γ.Ext} (B : A.obj.Ext)

def form : Γ.Ext :=
  Ext.mk' Γ (IsPullback.form₀ A.isPullback B.isPullback ≫ S.hom)

variable (b : Section B)

def ProdIsoPullbackDProd : (ΠA.hom.hom).obj (Over.mk B.hom.hom) ≅
    ((IsPullback.form₀ A.isPullback B.isPullback)*).obj ((Π(Gen₁.snd U)).obj (Gen₂.snd' U)) :=
  IsPullback.snd_isoPullback $ DProd.isPullback (IsPullback.form₁.isPullback A.isPullback B.isPullback)
  (IsPullback.form₂.isPullback A.isPullback B.isPullback)

def transfer :
    (ΠA.hom.hom).obj (Over.mk B.hom.hom) ≅ Over.mk (Ext.hom (form S B)).hom :=
  (ProdIsoPullbackDProd B) ≪≫ (((IsPullback.form₀ A.isPullback B.isPullback)*).mapIso S.iso) ≪≫
  (U.pullbackSnd'_isoPullback_snd' S.hom  _).symm ≪≫
  (U.isoOverSnd (Ext.mk'.isPullback (IsPullback.form₀ A.isPullback B.isPullback ≫ S.hom))).symm

variable {B}
def intro : Section (form S B) :=
  Section.ofHom $ IsPullback.adjEquiv (IsPullback.of_id_snd (f := A.hom.hom)) (Over.mk B.hom.hom)
    (Section.toHom b) ≫ (transfer S B).hom

variable (f : Section (form S B)) (a : Section A)

def reduce : Over.mk (𝟙 Γ.dom) ⟶ (ΠA.hom.hom).obj (Over.mk B.hom.hom) :=
  Section.toHom f ≫ (transfer S B).inv

lemma reduce_intro : reduce S (intro S b) =
  IsPullback.adjEquiv (IsPullback.of_id_snd (f := A.hom.hom)) (Over.mk B.hom.hom)
    (Section.toHom b) := by
  simp [reduce, intro]

def elim :
    Over.mk a.left ⟶ Over.mk B.hom := by
  refine Over.homMk (Hom.mk ?_) ?_
  exact (Section.toHom a).left ≫
    ((IsPullback.of_hasPullback ((ΠA.hom.hom).obj (Over.mk B.hom.hom)).hom A.hom.hom).sectionSnd'
    (reduce S f) ≫ (adj A.hom.hom).counit.app (Over.mk B.hom.hom)).left
  ext; simp only [Over.mk_left, Over.comp_left, Over.homMk_left,
    Over.mk_hom, comp_hom, Category.assoc]
  erw [Over.w, Over.w, Over.mk_hom, Category.comp_id]
  rfl

lemma compt (a : Section A) (b : Section B) :
    (elim S (intro S b) a).left = a.left ≫ b.left := by
  ext; simp
  change _ = (Section.toHom a).left ≫ (Section.toHom b).left
  dsimp only [elim, Over.homMk_left]
  simp_rw [reduce_intro]
  congr
  rw [← Adjunction.homEquiv_symm_id]
  convert IsPullback.adjEquiv_naturality_symm_left'
    (IsPullback.of_id_snd (f := A.hom.hom))
    ((IsPullback.adjEquiv _ (Over.mk (Ext.hom B).hom)) (Section.toHom b)) (𝟙 _)
  simp only [Functor.id, Category.comp_id, Equiv.symm_apply_apply]

end Pi

variable [HasPullbacks C] [LocallyCartesianClosed C] [HasBinaryProducts C] in
open Pi in
def Pi_type (S : Pi.Structure U) : Pi_type (U.Chains t) where
  form B := form S B
  intro b := intro S b
  elim f a := elim S f a
  compt a b := compt S a b

section
-- maybe it would be good to rewrite every isterminal to hasterminal
-- and use the classical terminal throughout
variable [HasPullbacks C] [LocallyCartesianClosed C] [HasTerminal C] (S : Empty.Structure U)

namespace Empty

variable (Γ : U.Chains (⊤_ C))

instance : isTerminal (⊤_ C) where
  is_terminal := terminalIsTerminal

def form : Ext Γ :=
  Ext.mk' Γ (terminal.from Γ.dom ≫ S.map)

open LocallyCartesianClosed

def form.obj_dom_isInitial' : IsInitial (Over.mk (form S Γ).hom.hom) :=
  IsPullbackPreservesInitial (Ext.isPullbackLeft Γ (terminal.from Γ.dom) S.map) S.is_initial

def form.obj_dom_isInitial : IsInitial (Over.mk (form S Γ).hom) := by
  apply IsInitial.ofUniqueHom _ _
  . intro Y
    apply Over.homMk (Hom.mk ((form.obj_dom_isInitial' S Γ).to (Over.mk Y.hom.hom)).left) _
    ext; simp; erw [Over.w]; rfl
  . intro Y m
    ext; simp
    set m' : Over.mk (form S Γ).hom.hom ⟶ Over.mk Y.hom.hom := by
      apply Over.homMk m.left.hom (by simp; erw [← comp_hom, Over.w]; rfl)
    change m'.left = _
    congr
    apply (form.obj_dom_isInitial' S Γ).hom_ext

variable {Γ}

def elim₀ (A : Ext (form S Γ).obj) :
    (Over.mk (𝟙 (form S Γ).obj)).left ⟶ (Over.mk (Ext.hom A)).left :=
   ((form.obj_dom_isInitial S Γ).to (Over.mk (A.hom ≫ (form S Γ).hom))).left

def elim (A : Ext (form S Γ).obj) : Section A := by
  apply Over.homMk (elim₀ S A) _
  dsimp
  set e : Over.mk (form S Γ).hom ⟶ Over.mk (form S Γ).hom := by
    refine Over.homMk (elim₀ S A ≫ A.hom) ?_
    simp; apply Over.w
  change e.left = (𝟙 Over.mk (form S Γ).hom).left
  congr
  apply (form.obj_dom_isInitial S Γ).hom_ext

omit [HasPullbacks C] [LocallyCartesianClosed C] in
lemma form_stable {Γ Γ' : U.Chains (⊤_ C)} (f : Γ' ⟶ Γ) :
    form S Γ' = Ext.pullback (form S Γ) f := by
  ext
  all_goals
  simp only [Ext.pullback, form, Ext.mk', Chains.cons', cons, ContextualCategory.pb, pb, cases_cons,
      pb_cons]
  rw [← Category.assoc]
  congr 2
  apply terminal.hom_ext

variable {Γ Γ' : U.Chains (⊤_ C)} (f : Γ' ⟶ Γ)

lemma elim_stable {Γ Γ' : U.Chains (⊤_ C)} (A : Ext (form S Γ).obj) (f : Γ' ⟶ Γ) :
  elim S (Ext.pullback A (eqToHom (congrArg Ext.obj (form_stable S f)) ≫ ((form S Γ).pullbackFst f)))
      = (elim S A).lift (eqToHom (congrArg Ext.obj (form_stable S f)) ≫ (form S Γ).pullbackFst f) := by
  ext : 1
  set e := elim S _
  apply Over.IsInitial_hom_ext (form.obj_dom_isInitial S Γ')
  . simp; rw [← Category.assoc]
    change (e.left ≫ _) ≫ _ = _
    erw [Over.w]
    simp only [Over.mk_left, Over.mk_hom, Category.id_comp]
  . simp; erw [← Category.assoc, Over.w]
    simp only [Over.mk_hom, Category.id_comp]

end Empty

open Empty in
def Empty_type (S : Empty.Structure U) : Empty_type (U.Chains (⊤_ C)) where
  form := form S
  elim := elim S
  form_stable := form_stable S
  elim_stable := elim_stable S

end

section

def aux {C : Type*} [Category C] {P X Y Z : C}
  {fst : P ⟶ X} {snd : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y} [IsIso f] (is : IsPullback fst snd f g) :
    P ≅ Z where
  hom := snd
  inv := is.sectionSnd (inv f) (IsIso.inv_hom_id _)
  hom_inv_id := by
    apply is.hom_ext
    . simp; rw [← Category.assoc, ← is.w]; simp
    . simp
  inv_hom_id := by simp

variable [HasTerminal C] (S : Unit.Structure U)

namespace Unit

variable (Γ : U.Chains (⊤_ C))

def form : Ext Γ :=
  Ext.mk' Γ (terminal.from Γ.dom ≫ S.map)

instance : IsIso (U.snd S.map) where
  out := by
    use S.iso.inv.left
    constructor
    . have := Over.w S.iso.hom
      simp at this
      simp only [← this, ← Over.comp_left, S.iso.hom_inv_id, Over.id_left, Over.mk_left]
    . exact Over.w S.iso.inv

def intro' : Over.mk (𝟙 _) ≅ Over.mk (form S Γ).hom where
  hom := Section.ofHom $ Over.homMk (aux (Ext.isPullbackLeft Γ (terminal.from Γ.dom) S.map)).inv
    (Iso.inv_hom_id _)
  inv := Over.homMk (form S Γ).hom
  hom_inv_id := by
    ext
    simp [Section.ofHom, Section.equiv]
    exact (aux _).inv_hom_id
  inv_hom_id := by
    ext
    simp [Section.ofHom, Section.equiv]
    exact (aux _).hom_inv_id

def intro : Section (form S Γ) := (intro' S Γ).hom

def intro'Left : (form S Γ).obj ≅ Γ where
  hom := (form S Γ).hom
  inv := (intro' S Γ).hom.left
  hom_inv_id := by
    change (Over.homMk (form S Γ).hom : Over.mk (Ext.hom (form S Γ)) ⟶ Over.mk (𝟙 Γ)).left ≫ _ = _
    erw [← Over.comp_left, (intro' S Γ).inv_hom_id]
    rfl
  inv_hom_id := by
    change _ ≫ (Over.homMk (form S Γ).hom : Over.mk (Ext.hom (form S Γ)) ⟶ Over.mk (𝟙 Γ)).left = _
    erw [← Over.comp_left, (intro' S Γ).hom_inv_id]
    rfl

instance : IsIso (intro S Γ) := by dsimp [intro]; infer_instance

instance : IsIso (form S Γ).hom := by change IsIso (intro'Left _ _).hom; infer_instance

variable {Γ} (A : Ext (form S Γ).obj) (d : Over.mk (intro S Γ).left ⟶ Over.mk A.hom)

def elim_tm : Section A := by
  refine Over.homMk ((intro' S Γ).inv.left ≫ d.left) ?_
  simp; erw [Over.w d]; simp only [Over.mk_left, Over.mk_hom, ← Over.comp_left]
  erw [Iso.inv_hom_id]
  rfl

lemma elim_comm : (intro S Γ).left ≫ (elim_tm S A d).left = d.left := by
  ext
  simp only [Over.mk_left, elim_tm, Over.homMk_left, comp_hom, ← Category.assoc]
  change (intro S Γ ≫ _).left.hom ≫ _ =  _
  erw [(intro' S Γ).hom_inv_id]
  simp only [Over.mk_left, Over.id_left, id_hom, Category.id_comp]

lemma form_stable {Γ'} (f : Γ' ⟶ Γ) : form S Γ' = (form S Γ).pullback f := by
  ext
  all_goals
  simp only [Ext.pullback, form, Ext.mk', Chains.cons', cons, ContextualCategory.pb, pb, cases_cons,
        pb_cons]
  rw [← Category.assoc]
  congr 2
  apply terminal.hom_ext

lemma aux' {A B : Ext Γ} (eq : A = B) : A.hom = eqToHom (congrArg Ext.obj eq) ≫ B.hom := by
  cases eq
  simp only [eqToHom_refl, Category.id_comp]

example {A B : Ext Γ} (eq : A.obj = B.obj) : A.hom = eqToHom eq ≫ B.hom := by
  cases B
  cases eq
  simp only [eqToHom_refl, Category.id_comp]

lemma intro_stable {Γ'} (f : Γ' ⟶ Γ) :
    intro S Γ' ≫ eqToHom (congrArg (fun f ↦ Over.mk f.hom) (form_stable S f))
      = (intro S Γ).lift f := by
  change (intro' S Γ').hom ≫ _ = _
  rw [← Iso.eq_inv_comp]
  dsimp [intro']
  ext : 1
  simp
  have : (form S Γ').hom  =
    eqToHom (congrArg Ext.obj $ form_stable S f) ≫ ((form S Γ).pullback f).hom := by
      apply aux' (form_stable S f)
  simp only [this, Category.assoc, aux, Category.comp_id]
  dsimp only [Section.lift, IsPullback.sectionSnd', Over.homMk_left]
  conv => left; rw [← Category.comp_id (eqToHom _)]
  congr
  convert ((aux $ (form S Γ).pullbackIsPullback f).hom_inv_id).symm
  simp [aux]
  congr
  apply (IsIso.inv_eq_of_hom_inv_id (intro'Left _ _).hom_inv_id).symm



end Unit
end
