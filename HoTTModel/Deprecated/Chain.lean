import HoTTModel.Universe
import Mathlib.Data.List.Basic

open ContextualCategory List CategoryTheory Limits

namespace Universe
variable {α : Type u} [CategoryTheory.Category.{v, u} α] {U : Universe α}

abbrev MorU (U : Universe α) := Σ x : α, x ⟶ U.obj

def Pb (X : α) : List (MorU U) → α
| [] => X
| cons a _ => U.pb a.snd

@[simp]
lemma pb_empty {X : α} : Pb X ([] : List (MorU U)) = X := rfl

lemma pb_ne_nil (X : List (MorU U)) (hX : X ≠ []): Pb t X = U.pb (head X hX).snd := by
  match X with
  | [] => simp at hX
  | a :: s => rfl

@[simp]
def Formed (X : α) : List (MorU U) → Prop
| [] => True
| cons a s => a.fst = Pb X s ∧ Formed X s

lemma ne_nil_formed (X : List (MorU U)) (hX : X ≠ []) (h : Formed t X) : (head X hX).fst = Pb t (tail X) := by
  match X with
  | [] => simp at hX
  | a :: s => simp [Formed]; exact h.1

@[ext]
structure Chain (U : Universe α) (X : α) where
  obj : List (MorU U)
  well_formed : Formed X obj

namespace Chain
@[simp]
def Hom (X Y : Chain U t) := Pb t X.obj ⟶ Pb t Y.obj

@[simp]
def id (X : Chain U t) := 𝟙 (Pb t X.obj)

@[simp]
def comp {X Y Z : Chain U t} : Hom X Y → Hom Y Z → Hom X Z := @CategoryStruct.comp _ _ (Pb t X.obj) (Pb t Y.obj) (Pb t Z.obj)

instance CategoryChain : Category (Chain U t) where
  Hom := Hom
  id := id
  comp := comp

@[simp]
lemma HomDef (X Y : Chain U t) : (X ⟶ Y) = (Pb t X.obj ⟶ Pb t Y.obj) := rfl

@[simp]
lemma CategoryChain.id {X : Chain U t}: 𝟙 X = 𝟙 (Pb t X.obj) := rfl

section ContextualStrucutre

@[simp]
def one : Chain U t where
  obj := []
  well_formed := by simp;

@[simp]
def gr (X : Chain U t) : ℕ := length X.obj

def one_uniq {X : Chain U t} : gr X = 0 → X = (@one _ _ U t) := by intro h; ext1; simp only [one]; rw [← length_eq_zero]; exact h

-- this is badly written
instance UniqueToTerminal (h : IsTerminal t) (X : Chain U t) : Unique (X ⟶ one) := by
  simp only [HomDef, one, pb_empty]
  apply isTerminalEquivUnique _ t h

def one_terminal (h : IsTerminal t) : IsTerminal (@one _ _ U t) := by
  have (X : Chain U t) : X ⟶ one := IsTerminal.from h (Pb t X.obj)
  apply IsTerminal.ofUniqueHom this
  intro X m
  have : Subsingleton (X ⟶ one) := @Unique.instSubsingleton _ (UniqueToTerminal h X)
  apply Subsingleton.allEq

abbrev ft' : List (MorU U) → List (MorU U) := drop 1

lemma ft'_formed : (X : List (MorU U)) → (h : Formed t X) → Formed t (ft' X)
| [], _ => by simp
| cons a s, h => by simp only [ft', drop_one, tail_cons]; exact h.2

lemma formed_head : (X : List (MorU U)) → (h : Formed t X) → (h' : X ≠ []) →  (head X h').fst = Pb t (ft' X)
| [], _, _ => by contradiction
| cons a s, h, _ => by simp only [head_cons, drop_succ_cons, drop_zero]; exact h.1

lemma formed_head' (X : Chain U t) (h' : X.obj ≠ []) : (head X.1 h').fst = Pb t (ft' X.1) := formed_head X.1 X.2 _

def ft (X : Chain U t) : Chain U t where
  obj := ft' X.obj
  well_formed := by apply ft'_formed _ X.well_formed

lemma ft_obj {X : Chain U t} : (ft X).obj = ft' X.obj := rfl

def ft_one : ft (@one _ _ U t) = one := by ext1; simp only [ft, one, drop_nil]

def ft_gr {n : ℕ} (X : Chain U t): gr X = n + 1 → gr (ft X) = n := by
  simp only [gr, ft, ft', drop_one, length_tail]
  intro h
  simp only [h, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]

def proj' : (X : List (MorU U)) → (h : Formed t X) → (Pb t X ⟶ Pb t (ft' X))
| [], _ => 𝟙 t
| cons a _, h => U.pb_vmap a.snd ≫ eqToHom h.1

def proj (X : Chain U t) : X ⟶ ft X := proj' X.obj X.well_formed

class isTerminal (t : α) where
  is_terminal : IsTerminal t

lemma is_terminal (t : α) [h : isTerminal t] : IsTerminal t := h.is_terminal
/-
noncomputable instance instChainPreContextualCategory [isTerminal t] : PreContextualCategory (Chain U t) where
  Cat := by infer_instance
  gr := gr
  one := one
  one_gr := by simp
  one_uniq := one_uniq
  one_terminal := one_terminal (is_terminal t)
  ft := ft
  ft_one := ft_one
  ft_gr := ft_gr
  proj := proj
-/

@[simp]
instance instChainPreContextualCategory [h : isTerminal t] : PreContextualCategory (Chain U t) where
  Cat := by infer_instance
  gr := gr
  one := one
  one_gr := by simp
  one_uniq := one_uniq
  one_terminal := one_terminal h.is_terminal
  ft := ft
  ft_one := ft_one
  ft_gr := ft_gr
  proj := proj

variable {t : α} [isTerminal t]

lemma ne_nil_of_NR {X : Chain U t} [h : NR X] : X.obj ≠ [] := by
  have := h.nr
  dsimp [gr] at this
  rwa [← List.length_pos_iff_ne_nil, ← Nat.ne_zero_iff_zero_lt]

def pb' {X Y : Chain U t} [NR X] (f : Y ⟶ ft X) : MorU U :=
  ⟨Pb t Y.obj, f ≫ eqToHom (formed_head' X ne_nil_of_NR).symm ≫ (head X.obj ne_nil_of_NR).snd⟩

lemma pb'_fst {X Y : Chain U t} [NR X] {f : Y ⟶ ft X} : (pb' f).fst = Pb t Y.obj := rfl

def pb {X Y : Chain U t} [NR X] (f : Y ⟶ ft X) : Chain U t where
  obj := pb' f :: Y.obj
  well_formed := by simp [Formed]; exact ⟨pb'_fst, Y.2⟩

lemma gr_pb {X Y : Chain U t} [NR X] {f : Y ⟶ ft X} : gr (pb f) ≠ 0 := by
  simp only [gr, pb, length_cons, ne_eq, Nat.succ_ne_zero, not_false_eq_true]

lemma ft_pb  {X Y : Chain U t} [NR X] {f : Y ⟶ ft X} : ft (pb f) = Y := by ext1; simp [ft, pb]

notation g" ● "f => (fun x ↦ x ≫ g) f

def pb_map_comm_aux {X Y : Chain U t} [NR X] (f : Y ⟶ ft X) :
  ((pb' f).snd ● proj (pb f)) = U.pb_hmap ((pb' f).snd) ≫ U.map := by
    rw [← U.comm]
    apply congrArg (fun x ↦ x ≫ _)
    simp [proj, proj', pb]

def head_map (X : Chain U t) [NR X] : Pb t (ft X).obj ⟶ U.obj :=
  eqToHom (formed_head' X _).symm ≫ (head X.obj ne_nil_of_NR).snd

lemma congrFunAux {s : α} {f : (t : α) → ((t ⟶ s) → α)} {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  simp

lemma pb_head_map (X : Chain U t) [NR X] : U.pb (head_map X) = Pb t X.obj := by
  rw [pb_ne_nil (t:= t) X.obj]
  have eq : Pb t (ft X).obj = (head X.obj ne_nil_of_NR).fst := by rw [formed_head' X _, ft_obj]
  simp [head_map]
  apply congr_heq _
  rw [← Functor.conj_eqToHom_iff_heq]
  simp
  exact eq
  rfl
  apply congrFunAux eq

def pb_map_aux {X Y : Chain U t} [NR X] (f : Y ⟶ ft X) : Pb t (pb f).obj ⟶ U.pb (head_map X) := by
  apply PullbackCone.IsLimit.lift (@is_pullback _ _ U _ (head_map X)) (proj (pb f) ≫ f) (U.pb_hmap ((pb' f).snd))
  rw [← pb_map_comm_aux]
  simp
  apply congrArg
  simp [head_map, pb']

def pb_map {X Y : Chain U t} [NR X] (f : Y ⟶ ft X) : pb f ⟶ X := by
  rw [HomDef]
  exact pb_map_aux f ≫ eqToHom (pb_head_map X)

lemma ChainComp {X Y Z : Chain U t} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = comp f g := rfl

lemma comm {X Y : Chain U t} [NR X] {f : Y ⟶ ft X} : (pb_map f) ≫ proj X = (proj <| pb f) ≫ eqToHom (ft_pb (f := f)) ≫ f := by
  simp [pb_map, ChainComp, pb_map_aux]
  have : eqToHom (pb_head_map X) ≫ proj X = (PullbackCone.mk (U.pb_vmap (head_map X)) (U.pb_hmap (head_map X)) U.comm).fst := by
    simp [head_map]
    sorry
    --- rewrite head_map and proj (they should match!!)
  rw [this]
  apply PullbackCone.IsLimit.lift_fst

lemma split {X : Chain U t} [NR X] : X.obj = (head X.obj ne_nil_of_NR) :: (ft X).obj := by
  dsimp [ft, ft']
  rw [List.drop_one, List.head_cons_tail]

/-
Universe.Chain.formed_head'.{u, v} {α : Type u} [inst✝ : Category.{v, u} α] {U : Universe α} {t : α} (X : Chain U t)
  (h' : X.obj ≠ []) : (head X.obj h').fst = Pb t (ft' X.obj)
-/
#check formed_head'

lemma heq_comp (x y z : α) (f : y ⟶ z) (eq : x = y) : HEq (eqToHom eq ≫ f) f := by
  cases eq
  simp

lemma pullback_id_obj {X : Chain U t} [NR X]: pb (𝟙 (ft X)) = X := by
  ext1
  have : X.obj = (head X.obj ne_nil_of_NR) :: (ft X).obj := split
  rw [this]
  dsimp [pb, pb']
  apply congrArg (fun x ↦ x :: _)
  ext1
  simp only [ft_obj]
  rw [formed_head']
  simp
  apply heq_comp

#exit
instance instChainContextualCategory : ContextualCategory (Chain U t) where
  pb := pb
  pb_map := pb_map
  gr_pb := gr_pb
  ft_pb := ft_pb
  comm := sorry
  is_pullback := sorry
  pullback_id_obj := sorry
  pullback_id_map := sorry
  pullback_comp_obj := sorry
  pullback_comp_map := sorry



end ContextualStrucutre

end Chain

end Universe
