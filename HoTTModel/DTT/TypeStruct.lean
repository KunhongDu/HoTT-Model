import HoTTModel.DTT.SynCat
import HoTTModel.ContextualFunctor
import Mathlib.Data.Part

open PureTypeSystem ContextualCategory PreContextualCategory CategoryTheory
/-
namespace ContextualCategory

variable (S : Specification) (α : Type u) [ContextualCategory.{u, v} α]

structure PTSSort  where
  form (Γ : α) {s₁ s₂ : S.sort} (h : S.ax s₁ s₂) : Ext Γ

variable {S α} in
class PreservesSort {β : Type u₂} [ContextualCategory.{u₂, v₂} β] (F : α ⥤ β)
    [Contextual F] (Ax₁ : PTSSort S α) (Ax₂ : PTSSort S β) where
  form_map (Γ : α) {s₁ s₂ : S.sort} (h : S.ax s₁ s₂) :
    (Ax₁.form Γ h).map F = Ax₂.form (F.obj Γ) h

end ContextualCategory

namespace PureTypeSystem

noncomputable section
namespace QCtx

def PTSSort (S : Specification) : PTSSort S (QCtx S) where
  form Γ {s₁ s₂} h := {
    obj := ⟦PCtx.cons [Γ]ᵣ _ ⟨wf.cons _ _ _ (typing.sort [Γ]ᵣ _ _ h (Ctx.wf' _))⟩⟧
    ft' := by
      rw [← Quotient.out_equiv_out]
      exact ⟨ft_mk_cons_rep_betac _ _ _⟩
    gr' := by
      simp [gr]
      rw [(Ctx.mk_rep_betac _).length_eq]
      simp [PCtx.cons]
  }

end QCtx
-/
noncomputable section Λ

inductive ΛSort : Type 0
| star : ΛSort
| cube : ΛSort

notation "⋆" => ΛSort.star
notation "□" => ΛSort.cube

inductive ΛAx : ΛSort → ΛSort → Prop
| ax :  ΛAx ⋆ □

inductive ΛRel : ΛSort → ΛSort → ΛSort → Prop
| rel :  ΛRel ⋆ ⋆ ⋆

def Λ : Specification where
  sort := ΛSort
  ax := ΛAx
  rel := ΛRel

lemma false_of_cube_typing {Γ : PCtx Λ} {A : PTerm Λ}:
    ∀ (_ : Γ ⊢ !□ : A), False
| .conv _ _ _ _ _ _ h₂ _ => false_of_cube_typing h₂

lemma false_of_cube_cons_wf {Γ : PCtx Λ} :
    ∀ (_ : ((!□) :: Γ) ⊢ ⬝), False
| h => false_of_cube_typing h.typing_of_cons

lemma of_lift_eq_sort {S : Specification} {s : S.sort} {i : ℕ}:
    ∀ {a : PTerm S} , (a ↑ i) = (!s) → a = !s
| .sort s', h => by simpa using h

@[simp]
lemma lift_eq_sort_iff {S : Specification} {s : S.sort} {i : ℕ} {a : PTerm S} :
    (a ↑ i) = (!s) ↔ a = !s :=
  ⟨of_lift_eq_sort, by intro h; simp [h]⟩

lemma of_susbt_eq_sort {S : Specification} {s : S.sort}:
    ∀ {B a : PTerm S}, B{a} = (!s) → (B = (#0) ∧ a = !s) ∨ (B = !s)
| .var 0, a, h => by simp at h; simp [h]
| .var (i + 1), a, h => by simp at h
| .sort s', a, h => by simp at h; simp [h]

lemma eq_star_of_typing_cube' {Γ : PCtx Λ} {A s : PTerm Λ} (hs : s = !□):
    ∀ (_ : Γ ⊢ A : s), A = !⋆
| .var _ _ _ _ _ => by sorry
| .sort _ _ _ ΛAx.ax _ => rfl
| .conv _ _ _ _ □ h₁ h₂ h₃ => by
  cases hs; apply False.elim (false_of_cube_typing h₃)
| .conv _ _ _ _ ⋆ h₁ h₂ h₃ => by
  cases hs; apply False.elim (false_of_cube_typing h₃)
| .app _ f A B a h₁ h₂ => by
  -- hs => B = !□ or a = !□
  -- h₁ => rel _ _ □ => False or h₂ => False
    sorry

lemma eq_star_of_typing_cube {Γ : PCtx Λ} {A : PTerm Λ}:
    ∀ (_ : Γ ⊢ A : !□), A = !⋆
| h => eq_star_of_typing_cube' rfl h

lemma false_of_star_betac_cube :
    (!⋆ : PTerm Λ) ≃β (!□) → False := by
  intro h; simpa using h.eq_of_sort_betac_sort

lemma false_of_star_typing_of_betac {Γ : PCtx Λ} {s : PTerm Λ} (hs : s ≃β !⋆):
    ∀ (_ : Γ ⊢ !⋆ : s), False
| .conv _ _ _ _ _ h₁ h₂ _ => by
  apply false_of_star_typing_of_betac (h₁.trans _ _ _ hs) h₂
| .sort _ _ _ ΛAx.ax _ => false_of_star_betac_cube hs.symm

lemma false_of_star_typing_star {Γ : PCtx Λ} :
    (Γ ⊢ !⋆ : !⋆) → False :=
  false_of_star_typing_of_betac (betac.refl _)

lemma false_of_star_typing_of_betac' {Γ : PCtx Λ} {t : PTerm Λ}
    (ht : t ≃β !⋆) (h : Γ ⊢ t : !⋆) : False :=
  false_of_star_typing_star $ subject_reduction h (betar_of_betac_sort ht)

lemma eq_of_typing_sort {Γ : PCtx Λ} {A : PTerm Λ} :
    ∀ {s₁ s₂ : Λ.sort} (_ : Γ ⊢ A : !s₁) (_ : Γ ⊢ A : !s₂), s₁ = s₂
| ⋆, ⋆, _, _ => rfl
| □, □, _, _ => rfl
| □, ⋆, h₁, h₂ => by
  cases eq_star_of_typing_cube h₁
  apply False.elim (false_of_star_typing_star h₂)
| ⋆, □, h₁, h₂ => by
  cases eq_star_of_typing_cube h₂
  apply False.elim (false_of_star_typing_star h₁)

def term_betac_typing_sort {Γ : PCtx Λ} {A B : PTerm Λ} (h₁ : A ≃β B) :
  ∀ {s₁ s₂ : Λ.sort} (h₂ : Γ ⊢ B : !s₁) (h₃ : Γ ⊢ A : !s₂), Γ ⊢ B : !s₂
| ⋆, ⋆, h₂, h₃ => h₂
| ⋆, □, h₂, h₃ => by
  cases eq_star_of_typing_cube h₃
  apply False.elim (false_of_star_typing_of_betac' h₁.symm h₂)
| □, ⋆, h₂, h₃ => by
  cases eq_star_of_typing_cube h₂
  apply False.elim (false_of_star_typing_of_betac' h₁ h₃)
| □, □, h₂, h₃ => h₂
alias subject_conversion := term_betac_typing_sort

namespace Λ

open ContextualCategory

section Basic

variable (α : Type u) [ContextualCategory α]

-- this can be defined for all specifications
class SortMarker where
  sort {Γ : α} (A : Ext Γ) : Λ.sort

open SortMarker

variable [SortMarker α]

variable {α}

class IsStar {Γ : α} (A : Ext Γ) where
  sort_eq : sort A = ⋆

class IsCube {Γ : α} (A : Ext Γ) where
  sort_eq : sort A = □

attribute [simp] IsStar.sort_eq IsCube.sort_eq

class PreservesSort {β : Type u₂} [ContextualCategory.{u₂, v₂} β] [SortMarker β]
  (F : α ⥤ β) [Contextual F] where
  sort_map {Γ : α} (A : Ext Γ) : sort (A.map F) = sort A

attribute [simp] PreservesSort.sort_map

variable (α) in
class Ax where
  form (Γ : α) : Ext Γ
  isCube (Γ : α) : IsCube (form Γ)
  intro (Γ : α) (A : Ext Γ) [IsStar A] : Section (form Γ)

attribute [instance] Ax.isCube

class PreservesAx {β : Type u₂} [ContextualCategory.{u₂, v₂} β] [SortMarker β]
  (F : α ⥤ β) [Contextual F] [Ax α] [Ax β] where
  form_map (Γ : α) : (Ax.form Γ).map F = Ax.form (F.obj Γ)

def _root_.ContextualCategory.Ext.fromAbove (Γ : α) (n : ℕ) (h : n + 1 ≤ gr Γ) :
    Ext (ft^[n + 1] Γ) where
  obj := ft^[n] Γ
  ft' := by rw [Nat.add_comm n, Function.iterate_add]; rfl
  gr' := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm, Nat.add_comm n, ← Nat.add_assoc] at hk
    rw [gr_ft_iterate hk, gr_ft_iterate]
    rwa [Nat.add_comm n, ← Nat.add_assoc]

structure IsCubeFromAbove (Γ : α) (n : ℕ) : Prop where
  le : n + 1 ≤ gr Γ
  is : IsCube (Ext.fromAbove Γ n le)

variable (α)

class El where
  form (Γ : α) (n : ℕ) (h : IsCubeFromAbove Γ n) : Ext Γ
  isStar (Γ : α) (n : ℕ) (h : IsCubeFromAbove Γ n) : IsStar (form Γ n h)

class IsStarStable where
  sort_eq {Γ Γ' : α} (A : Ext Γ) (f : Γ' ⟶ Γ) :
    sort A = ⋆ → sort (A.pullback f) = ⋆

instance [IsStarStable α] {Γ Γ' : α} (A : Ext Γ) (f : Γ' ⟶ Γ) [IsStar A] :
    IsStar (A.pullback f) :=
  ⟨IsStarStable.sort_eq A f IsStar.sort_eq⟩

/-
structure Pi [IsStarStable α] where
  form {Γ : α} (A : Ext Γ) [IsStar A] (B : Ext A.obj) [IsStar B]: Ext Γ
  intro {Γ : α} (A : Ext Γ) [IsStar A] (B : Ext A.obj) [IsStar B] (b : Section B) :
    Section (form A B)
  elim {Γ : α} (A : Ext Γ) [IsStar A] (B : Ext A.obj) [IsStar B]
    (k : Section (form A B)) (a : Section A) :
      Over.mk a.left ⟶ Over.mk B.hom
  compt {Γ : α} {A : Ext Γ} [IsStar A] {B : Ext A.obj} [IsStar B]
    (a : Section A) (b : Section B) :
      (elim A B (intro A B b) a).left = a.left ≫ b.left
  form_stable {Γ Γ' : α} (f : Γ' ⟶ Γ) (A : Ext Γ) [IsStar A]
    (B : Ext A.obj) [IsStar B] :
      (form A B).pullback f = form (A.pullback f) (B.pullback (A.pullbackFst f))
  intro_stable {Γ Γ' : α} (f : Γ' ⟶ Γ) {A : Ext Γ} [IsStar A]
    (B : Ext A.obj) [IsStar B] (b : Section B) :
      HEq ((intro A B b).lift f)
        (intro (A.pullback f) (B.pullback (A.pullbackFst f)) (b.lift (A.pullbackFst f)))
  elim_stable {Γ Γ' : α} (f : Γ' ⟶ Γ) (A : Ext Γ) [IsStar A] (B : Ext A.obj) [IsStar B]
    (k : Section (form A B)) (a : Section A) :
      elim (A.pullback f) (B.pullback (A.pullbackFst f)) ((k.lift f).ofEq (form_stable f A B))
        (a.lift f) = (a.liftCommSq f).liftIsPullbackAlong' (B.pullbackIsPullback (A.pullbackFst f))
          (elim A B k a)
-/

class Pi [IsStarStable α] where
  form {Γ : α} (A : Ext Γ) [IsStar A] (B : Ext A.obj) [IsStar B] : Ext Γ
  form_isStar {Γ : α} (A : Ext Γ) [IsStar A] (B : Ext A.obj) [IsStar B] : IsStar (form A B)
  intro {Γ : α} (A : Ext Γ) [IsStar A] (B : Ext A.obj) [IsStar B] (b : Section B) :
    Section (form A B)
  elim {Γ : α} (A : Ext Γ) [IsStar A] (B : Ext A.obj) [IsStar B]
    (k : Section (form A B)) (a : Section A) :
      Section (Ext.pullback B a.left)
  compt {Γ : α} {A : Ext Γ} [IsStar A] {B : Ext A.obj} [IsStar B]
    (a : Section A) (b : Section B) :
      elim A B (intro A B b) a = b.lift a.left
  form_stable {Γ Γ' : α} (f : Γ' ⟶ Γ) (A : Ext Γ) [IsStar A]
    (B : Ext A.obj) [IsStar B] :
      (form A B).pullback f = form (A.pullback f) (B.pullback (A.pullbackFst f))
  intro_stable {Γ Γ' : α} (f : Γ' ⟶ Γ) {A : Ext Γ} [IsStar A]
    (B : Ext A.obj) [IsStar B] (b : Section B) :
      HEq ((intro A B b).lift f)
        (intro (A.pullback f) (B.pullback (A.pullbackFst f)) (b.lift (A.pullbackFst f)))
  elim_stable {Γ Γ' : α} (f : Γ' ⟶ Γ) (A : Ext Γ) [IsStar A] (B : Ext A.obj) [IsStar B]
    (k : Section (form A B)) (a : Section A) :
      HEq ((elim A B k a).lift f)
        (elim (A.pullback f) (B.pullback (A.pullbackFst f))
          ((k.lift f).ofEq (form_stable f A B)) (a.lift f))

attribute [instance] Pi.form_isStar

variable {α}
@[simp]
def _root_.ContextualCategory.Ext.cast {A A' : α} (eq : A = A') (B : Ext A) :
    Ext A' :=
  (congrArg Ext eq) ▸ B

instance IsStar.cast {A A' : α} (eq : A = A') (B : Ext A) [IsStar B] :
    IsStar (B.cast eq) := by
  cases eq; simp; infer_instance

def Pi.form_cast [IsStarStable α] (P : Pi α) {Γ A' : α} (A : Ext Γ)
  [IsStar A] (eq : A' = A.obj) (B : Ext A') [IsStar B] :
    Ext Γ :=
  P.form A (B.cast eq)

structure Ext.prop₁ (A B : α) : Prop where
  ft : ft B = A
  gr : gr B = gr A + 1

def Ext.mkProp₁ {A B : α} (p : Ext.prop₁ A B) :
    Ext A where
  obj := B
  ft' := p.1
  gr' := p.2

structure Ext.prop₂ (A B : α) : Prop where
  ft : ft B = A
  gr : gr B = gr A + 1
  isStar : IsStar (Ext.mk _ ft gr)

def Ext.prop₂.toProp₁ {A B : α} (p : Ext.prop₂ A B) :
    Ext.prop₁ A B where
  ft := p.1
  gr := p.2

def Ext.mkProp₂ {A B : α} (p : Ext.prop₂ A B) :
    Ext A where
  obj := B
  ft' := p.1
  gr' := p.2

lemma El.formProp₂ {E : El α} {Γ : α} {n : ℕ} {h : IsCubeFromAbove Γ n} :
    Ext.prop₂ Γ (E.form Γ n h).obj where
  ft := (E.form Γ n h).ft'
  gr := (E.form Γ n h).gr'
  isStar := E.isStar _ _ _

instance {A B : α} {p : Ext.prop₂ A B} :
  IsStar (Ext.mkProp₂ p) := p.3

end Basic

open QCtx SortMarker


instance : SortMarker (QCtx Λ) where
  sort A := (Ext.head_cons_wf A).sort_of_cons

section Typing

variable {Γ : QCtx Λ} {A : Γ.Ext}

lemma sort_eq_of_typing {s : Λ.sort} (h : [Γ]ᵣ ⊢ A.head : !s) :
    sort A = s :=
  eq_of_typing_sort (Ext.head_cons_wf A).typing_of_cons h

def typing_of_sort_mk {T : PTerm Λ} {h : Nonempty (T :: [Γ]ᵣ ⊢ ⬝)} {s : Λ.sort}
  (h' : sort (QCtx.Ext.mk T h) = s) :
    [Γ]ᵣ ⊢ T : !s := by
  sorry

def head_pullback_mk_betac {Γ' : QCtx Λ} (f : Γ' ⟶ Γ)
  (T : PTerm Λ) (h : Nonempty (T :: [Γ]ᵣ ⊢ ⬝)) :
    Ext.head (Ext.pullback (QCtx.Ext.mk T h) f) ≃β simulSubst T 0 [f]ᵣ := by
  sorry

variable (A) in
def head_typing_star [IsStar A] :
    [Γ]ᵣ ⊢ A.head : !⋆ := by
  convert (Ext.head_cons_wf A).typing_of_cons
  apply (IsStar.sort_eq (A := A)).symm

variable (A) in
def head_cons_head_typing_star [IsStar A] (B : A.obj.Ext) [IsStar B] :
    A.head :: [Γ]ᵣ ⊢ B.head : !⋆ := by
  sorry

instance : IsStarStable (QCtx Λ) where
  sort_eq {Γ Γ'} A f h₁ := by
    induction A using QCtx.Ext.rec with
    | h T h =>
      apply sort_eq_of_typing
      apply subject_conversion (head_pullback_mk_betac f T h).symm
        (Ext.head_cons_wf _).typing_of_cons
      rw [← simulSubst_sort (n := 0) (Γ := [f]ᵣ)]
      apply simulSubst_typing (append_typing (Ctx.wf' _) (typing_of_sort_mk h₁))
        (isMor'_isMor f.is)

variable (A) [IsStar A] (B : A.obj.Ext) [IsStar B]

def pi_head_typing :
    [Γ]ᵣ ⊢ Π.(A.head) B.head : !⋆ := by
  apply typing.pi [Γ]ᵣ A.head B.head _ _ _ ΛRel.rel (head_typing_star A)
  apply ctx_betac_typing (head_typing_star B) (wf.cons _ _ _ (head_typing_star A))
  rw [← A.head_cons_tail]
  apply A.tail_betac.of_tail_of_eq

def form : Γ.Ext :=
  QCtx.Ext.mk _ ⟨wf.cons _ _ _ (pi_head_typing A B)⟩

def form_head_betac :
    (form A B).head ≃β (Π.(A.head) B.head) := by
  sorry

instance : IsStar (form A B) where
  sort_eq := by
    apply sort_eq_of_typing
    apply subject_conversion (form_head_betac A B).symm (form A B).head_cons_wf.typing_of_cons
    apply pi_head_typing

variable (b : Section B)

def intro : Section (form A B) := by
  let r : A.head :: [Γ]ᵣ ⊢ b.head : B.head := by
    apply ctx_betac_typing b.typing A.head_cons_wf
    rw [← A.head_cons_tail]
    apply A.tail_betac.of_tail_of_eq
  apply Ext.SectionMk _ _ (typing.conv _ _ _ _ _ (form_head_betac A B).symm
    (typing.abs [Γ]ᵣ A.head _ B.head _ _ _ ΛRel.rel (head_typing_star A)
    (head_cons_head_typing_star A B) r) (form A B).head_cons_wf.typing_of_cons)

variable {A} in
def head_pullback_betac (a : Section A) :
    Ext.head (Ext.pullback B a.left) ≃β B.head{a.head} := sorry

variable {A B} in
def section_form_typing (k : Section (form A B)) :
    [Γ]ᵣ ⊢ k.head : Π.A.head B.head :=
  typing.conv _ _ _ _ _ (form_head_betac A B) k.typing
    (typing.pi [Γ]ᵣ A.head B.head _ _ ⋆ ΛRel.rel (head_typing_star A)
      (head_cons_head_typing_star A B))

def elim (k : Section (form A B)) (a : Section A) :
    Section (Ext.pullback B a.left) := by
  apply Ext.SectionMk
  dsimp
  apply typing.conv _ _ _ _ _ (head_pullback_betac B a).symm
  apply typing.app _ _ _ _ _ (section_form_typing k) a.typing
  apply (Ext.head_cons_wf (Ext.pullback B a.left)).typing_of_cons

lemma compt (a : Section A) (b : Section B) :
    elim A B (intro A B b) a = b.lift a.left := by
  sorry -- simply,   `(λA.b) ⬝ a →β b{a}`

end Typing

section Stability

variable {Γ Δ : QCtx Λ} (f : Δ ⟶ Γ) (A : Γ.Ext) [IsStar A] (B : A.obj.Ext) [IsStar B]

lemma form_stable :
    (form A B).pullback f = form (A.pullback f) (B.pullback (A.pullbackFst f)) := by
  sorry

#check simulSubst_pi -- => form_stable
#check simulSubst_abs -- => intro_stable
-- elim_stable is a little tricky...

end Stability

section Functor

variable {α : Type u₁} [ContextualCategory.{u₁, v₁} α] [SortMarker α] [IsStarStable α] [Ax α]
  {β : Type u₂} [ContextualCategory.{u₂, v₂} β] [SortMarker β] [IsStarStable β] [Ax β]

instance (F : α ⥤ β) [Contextual F] [PreservesSort F]
  {Γ : α} {A : Ext Γ} [IsStar A] :
    IsStar (Ext.map F A) where
  sort_eq := by simp only [PreservesSort.sort_map, IsStar.sort_eq]

class PreservesPi [Pi α] [Pi β] (F : α ⥤ β) [Contextual F] [PreservesSort F] where
  form_map {Γ : α} (A : Ext Γ) [IsStar A] (B : Ext A.obj) [IsStar B]:
    (Pi.form A B).map F = Pi.form (A.map F) (B.map F)
  intro_map {Γ : α} (A : Ext Γ) [IsStar A] (B : Ext A.obj) [IsStar B] (b : Section B) :
    HEq ((Pi.intro A B b).map F) (Pi.intro (A.map F) (B.map F) (b.map F))
  elim_map {Γ : α} (A : Ext Γ) [IsStar A] (B : Ext A.obj) [IsStar B]
    (k : Section (Pi.form A B)) (a : Section A) :
      HEq ((Pi.elim A B k a).map F)
        (Pi.elim (A.map F) (B.map F) ((k.map F).ofEq (form_map A B)) (a.map F))

end Functor

section Initial

open ContextualCategory Classical

variable {α : Type u₁} [ContextualCategory.{u₁, v₁} α] [SortMarker α] [IsStarStable α]
  [Ax α] [El α] [Pi α]
/-
def obj₀ {Γ : PCtx Λ} : ∀ (_ : Γ ⊢ ⬝), α
| .nil => one
| .cons Γ A □ h => (Ax.form (obj₀ h.wf) ΛAx.ax).obj
| .cons Γ A ⋆ h => sorry

variable (α) in
structure StarExt where
  obj : α
  ext : Ext obj
  isStar : IsStar ext

attribute [instance] StarExt.isStar

def obj₀_star {Γ : PCtx Λ} {A s: PTerm Λ} (hs : s ≃β !⋆) :
    ∀ (_ : Γ ⊢ A : s), StarExt α
| (typing.conv Γ A s s' □ h₁ h₂ h₃) => obj₀_star (h₁.trans _ _ _ hs) h₂
| (typing.conv Γ A s s' ⋆ h₁ h₂ h₃) => False.elim (false_of_star_typing_of_betac' hs h₃)
| (typing.app _ _ _ _ _ _ _) => by sorry -- false
| (typing.abs Γ A b B _ _ _ ΛRel.rel h₁ h₂ h₃) => by sorry -- false
| (typing.pi Γ A B _ _ _ ΛRel.rel h₁ h₂) => {
    obj := (obj₀_star (betac.refl (!⋆)) h₁).obj
    ext := by sorry
    isStar := sorry
  }
| (typing.sort _ _ _ ΛAx.ax _) => by sorry -- false
| (typing.var _ _ _ _ _) => by sorry

structure DExt (x : α) where
  obj : α
  ft' : ft (ft obj) = x
  gr' : gr (obj) = gr x + 2

attribute [simp] DExt.ft' DExt.gr'

@[reducible]
def DExt.mid {x : α} (A : DExt x) : α := ft (A.obj)

def DExt.up {x : α} (A : DExt x) :
    Ext A.mid where
  obj := A.obj
  ft' := rfl
  gr' := by simp [ft_gr]

def DExt.down {x : α} (A : DExt x) :
    Ext x where
  obj := A.mid
  ft' := by simp
  gr' := by simp [ft_gr]

class DExt.isStar {x : α} (A : DExt x) where
  up : IsStar A.up
  down : IsStar A.down

attribute [instance] DExt.isStar.up DExt.isStar.down

structure DExtStar (x : α) where
  ext : DExt x
  isStar : ext.isStar

abbrev DExtStar.up {x : α} (A : DExtStar x) := A.ext.up

abbrev DExtStar.down {x : α} (A : DExtStar x) := A.ext.down

attribute [instance] DExtStar.isStar

def Pi.optionForm {Γ : α} :
    Option (DExtStar Γ) → Option (Ext Γ) :=
  Option.map (fun D ↦ P.form D.down D.up)

def Pi.optionFormObj {Γ : α} :
    Option (DExtStar Γ) → Option α :=
  fun x ↦ Option.map Ext.obj (P.optionForm x)
-/
/-
variable (α) in
structure StarExt where
  obj : α
  ext : Ext obj
  isStar : IsStar ext := by infer_instance

def Pi.starExtMkForm (P : Pi α) {Γ : α} (A : Ext Γ) [IsStar A]
  (B : Ext A.obj) [IsStar B] :
    StarExt α where
  ext := P.form A B

attribute [instance] StarExt.isStar

def obj₀_star {Γ : PCtx Λ} {A s: PTerm Λ} (hs : s ≃β !⋆) :
    ∀ (_ : Γ ⊢ A : s), Part (StarExt α)
| (typing.conv Γ A s s' □ h₁ h₂ h₃) => obj₀_star (h₁.trans _ _ _ hs) h₂
| (typing.conv Γ A s s' ⋆ h₁ h₂ h₃) => False.elim (false_of_star_typing_of_betac' hs h₃)
| (typing.app _ _ _ _ _ _ _) => by sorry -- false
| (typing.abs Γ A b B _ _ _ ΛRel.rel h₁ h₂ h₃) => by sorry -- false
| (typing.pi Γ A B _ _ _ ΛRel.rel h₁ h₂) => do
    let eA ← obj₀_star hs h₁
    let eB ← obj₀_star hs h₂
    ⟨eB.obj = eA.ext.obj, fun p ↦ P.starExtMkForm eA.ext (eB.ext.cast p)⟩
| (typing.sort _ _ _ ΛAx.ax _) => by sorry -- false
| (typing.var _ _ _ _ _) => by sorry
-/

variable (α) in
def prePartInterp (Γ : Part α) : PTerm Λ → Part α
| .var n => do
  let iΓ ← Γ
  ⟨IsCubeFromAbove iΓ n, fun p ↦ (El.form iΓ n p).obj⟩
| .sort ⋆ => do (Ax.form (← Γ)).obj
| .sort □ => Part.none
| .app _ _ => Part.none
| .abs _ _ => Part.none
| .pi A B => do
  let iA ← prePartInterp Γ A
  let iB ← prePartInterp iA B
  ⟨Ext.prop₂ (← Γ) iA ∧ Ext.prop₂ iA iB, fun p ↦ (Pi.form (Ext.mkProp₂ p.1) (Ext.mkProp₂ p.2)).obj⟩

variable (α) in
def partInterp : PCtx Λ → Part α
| [] => Part.some one
| A :: Γ => prePartInterp α (partInterp Γ) A

def Ext.partProp₂ (A B : Part α) : Part Prop :=
  ⟨A.Dom ∧ B.Dom, fun h ↦ Ext.prop₂ (A.get h.1) (B.get h.2)⟩

lemma prePartInterp_extProp₂ {Γ : Part α} (hΓ : Γ.Dom) :
  ∀ {A : PTerm Λ} (ne : A ≠ !⋆) (hA : (prePartInterp α Γ A).Dom),
    Ext.prop₂ (Γ.get hΓ) ((prePartInterp α Γ A).get hA)
| .var n, _, h => by
  induction Γ using Part.induction_on with
  | hnone => cases hΓ
  | hsome Γ =>
    simp [prePartInterp]
    apply El.formProp₂
| .sort ⋆, h, _ => False.elim (h rfl)
| .pi A B, _, h => by
  let iA := prePartInterp α Γ A
  let iB := prePartInterp α iA B
  induction Γ using Part.induction_on with
  | hnone => cases hΓ
  | hsome Γ =>
    simp [prePartInterp] at h
    simp
    -- change ∃ (h : iA.Dom), _ at h
    sorry

lemma prePartInterp_extProp₁ {Γ : Part α} (hΓ : Γ.Dom) :
  ∀ {A : PTerm Λ} (hA : (prePartInterp α Γ A).Dom),
    Ext.prop₁ (Γ.get hΓ) ((prePartInterp α Γ A).get hA)
| .var n, _ => (prePartInterp_extProp₂ _ (by simp) _).toProp₁
| .sort ⋆, _ => by
  induction Γ using Part.induction_on with
  | hnone => cases hΓ
  | hsome Γ =>
    simp [prePartInterp]
    exact ⟨(Ax.form Γ).2, (Ax.form Γ).3⟩
| .pi A B, h => (prePartInterp_extProp₂ _ (by simp) _).toProp₁

def pi_inversion {Γ : PCtx Λ} {A B s : PTerm Λ} :
    ∀ (_ : Γ ⊢ Π.A B : !⋆), (Γ ⊢ A : !⋆) × ((A :: Γ) ⊢ B : !⋆)
| .pi _ A B ⋆ ⋆ _ h₁ h₂ h₃ => ⟨h₂, h₃⟩
| .conv _ _ _ _ □ _ _ _ => sorry
| .conv Γ _ s _ ⋆ h₁ h₂ h₃ => by cases false_of_star_typing_star h₃

def pi_cons_inversion {Γ : PCtx Λ} {A B : PTerm Λ} :
    ∀ (_ : (Π.A B :: Γ) ⊢ ⬝), ((A :: Γ) ⊢ ⬝) × ((B :: A :: Γ) ⊢ ⬝) := sorry

/-
mutual
lemma total_wf {Γ : PCtx Λ} : ∀ (_ : Γ ⊢ ⬝), (partInterp Ax E P Γ).Dom
| .nil => trivial
| .cons Γ A □ h => by
  cases eq_star_of_typing_cube h
  simp [partInterp, prePartInterp]
  apply total_wf h.wf
| .cons Γ A ⋆ h => by apply total_cons_wf (betac.refl _) h

lemma total_cons_wf {Γ : PCtx Λ} {A s : PTerm Λ} (hs : s ≃β !⋆):
  ∀ (_ : Γ ⊢ A : s), (partInterp Ax E P (A :: Γ)).Dom
| .var _ _ n h₁ h₂ => by
  simp [partInterp, prePartInterp]
  use total_wf h₁
  sorry
| .sort _ _ _ ΛAx.ax h => by
  simp [partInterp, prePartInterp]
  exact total_wf h
| .pi _ A B _ _ _ ΛRel.rel h₁ h₂ => by
  simp [partInterp, prePartInterp]
  sorry
| .app _ _ _ _ _ _ _ => sorry
| .abs _ _ _ _ _ _ _ ΛRel.rel _ _ _ => sorry
| .conv _ _ _ _ _ _ _ _ => sorry

end
-/

lemma total_cons_wf {Γ : PCtx Λ} (h : (partInterp α Γ).Dom) :
  ∀ {A : PTerm Λ} (_ : (A :: Γ) ⊢ ⬝), (partInterp α (A :: Γ)).Dom
| .var n, h' => by
  simp [partInterp, prePartInterp]
  use h
  sorry
| .sort ⋆, h' => by simpa [partInterp, prePartInterp]
| .sort □, h' => sorry
| .app A B, h' => sorry
| .abs A B, h' => sorry
| .pi A B, h' => by
  simp [partInterp, prePartInterp]
  use total_cons_wf h (pi_cons_inversion h').1
  constructor
  . exact ⟨h, prePartInterp_extProp₂ _ sorry _⟩
  . exact ⟨total_cons_wf (total_cons_wf h (pi_cons_inversion h').1) (pi_cons_inversion h').2,
      prePartInterp_extProp₂ _ sorry _⟩

lemma total_wf {Γ : PCtx Λ} : ∀ (_ : Γ ⊢ ⬝), (partInterp α Γ).Dom
| .nil => trivial
| .cons Γ A _ h => total_cons_wf (total_wf h.wf) (wf.cons _ _ _ h)

lemma testpi1 {Γ : Part α} (hΓ : Γ.Dom) :
    ∀ {A B : PTerm Λ} (h : (prePartInterp α Γ (Π.A B)).Dom),
  (prePartInterp α Γ A).Dom := sorry

lemma testpi2 {Γ : Part α} (hΓ : Γ.Dom) :
    ∀ {A B : PTerm Λ} (h : (prePartInterp α Γ (Π.A B)).Dom),
  (prePartInterp α (prePartInterp α Γ A) B).Dom := sorry

lemma testpi {Γ : Part α} (hΓ : Γ.Dom) :
    ∀ {A B : PTerm Λ} (h : (prePartInterp α Γ (Π.A B)).Dom) (hA : A ≠ !⋆) (hB : B ≠ !⋆),
  (prePartInterp α Γ (Π.A B)).get h =
    (Pi.form (Ext.mkProp₂ (prePartInterp_extProp₂ hΓ hA (testpi1 hΓ h)))
      (Ext.mkProp₂ (prePartInterp_extProp₂ (testpi1 hΓ h) hB (testpi2 hΓ h)))).obj := sorry

lemma prePartInterp_betac_aux {Γ Γ' : Part α} (hΓ : Γ.Dom) (hΓ' : Γ'.Dom) (eq : Γ = Γ'):
    ∀ {A B : PTerm Λ} (_ : A ≃β B)
    (_ : (prePartInterp α Γ A).Dom) (_ : (prePartInterp α Γ' B).Dom),
      prePartInterp α Γ A = prePartInterp α Γ' B
| .sort □, _, _ , h, _ => by simp [prePartInterp] at h
| .app A B, _, _ , h, _ => by simp [prePartInterp] at h
| .abs A B, _, _ , h, _ => by simp [prePartInterp] at h
| _, .sort □, _ , _, h => by simp [prePartInterp] at h
| _, .app A B, _ , _, h => by simp [prePartInterp] at h
| _, .abs A B, _ , _, h => by simp [prePartInterp] at h
| .pi A B, .pi A' B', h, h₁, h₂ => by
  have aux₁ : prePartInterp α Γ A = prePartInterp α Γ' A' :=
    prePartInterp_betac_aux hΓ hΓ' eq (pi_inj h).1 (testpi1 hΓ h₁) (testpi1 hΓ' h₂)
  have aux₂ : prePartInterp α (prePartInterp α Γ A) B =
      prePartInterp α (prePartInterp α Γ' A') B' :=
    prePartInterp_betac_aux (testpi1 hΓ h₁) (testpi1 hΓ' h₂) aux₁ (pi_inj h).2
      (testpi2 hΓ h₁) (testpi2 hΓ' h₂)
  apply Part.ext'
  simp only [h₁, h₂]
  intros
  rw [testpi hΓ h₁ sorry sorry, testpi hΓ' h₂ sorry sorry]
  -- write a lemma for the following...
  congr 2
  . congr 2
  . congr 1
    . congr 1
    . congr 1
    . sorry -- this is funny but easy
  . congr 1
    . congr 1
    . congr 3
    . sorry -- this is funny but easy
  . congr 1
    . congr 1
      . congr 1
      . congr 1
        . congr 1
        . congr 1
        . sorry
    . congr 1 -- this is funny but easy
    . sorry
  . sorry
| .pi _ _, .sort ⋆, _ , _, _ => sorry -- false by betac
| .pi _ _, .var _, _ , _, _ => sorry -- false by betac
| .sort ⋆, .pi _ _, _ , _, _ => sorry -- false by betac
| .sort ⋆, .sort ⋆, _ , _, _ => by congr
| .sort ⋆, .var _, _ , _, _ => sorry -- false by betac
| .var _, .pi _ _, _ , _, _ => sorry -- false by betac
| .var _, .sort ⋆, _ , _, _ => sorry -- false by betac
| .var n, .var n', h , _, _ => by
  congr
  sorry

lemma prePartInterp_betac {Γ : Part α} (hΓ : Γ.Dom) {A B : PTerm Λ} :
    ∀ (_ : A ≃β B) (_ : (prePartInterp α Γ A).Dom) (_ : (prePartInterp α Γ B).Dom),
      prePartInterp α Γ A = prePartInterp α Γ B
| h₁, h₂, h₃ => prePartInterp_betac_aux hΓ hΓ rfl h₁ h₂ h₃

lemma partInterp_betac : ∀ {Γ Δ : PCtx Λ} (_ : Γ ⊢ ⬝) (_ : Δ ⊢ ⬝) (_ : Γ ≃β Δ),
  partInterp α Γ = partInterp α Δ
| [], [], _, _, _ => rfl
| _ :: _, [], _, _, h => by simpa using h.length_eq
| [], _ :: _, _, _,  h => by simpa using h.length_eq
| A :: Γ, B :: Δ, h₁, h₂, h => by
  simp [partInterp]
  rw [partInterp_betac h₁.typing_of_cons.wf h₂.typing_of_cons.wf h.tail]
  apply prePartInterp_betac (total_wf h₂.typing_of_cons.wf) h.head
  apply total_cons_wf (total_wf h₂.typing_of_cons.wf)
    (ctx_betac_wf_cons h₁ h₂.typing_of_cons.wf h.tail)
  apply total_cons_wf (total_wf h₂.typing_of_cons.wf) h₂

variable (α)

def interp (Γ : Ctx Λ) : α :=
  (partInterp α Γ.ctx).get (total_wf Γ.wf')

def interpExt (Γ : Ctx Λ) (A : PTerm Λ) (h : Nonempty (A :: Γ.ctx ⊢ ⬝)) :
    Ext (interp α Γ) := by
  apply Ext.mkProp₁
  apply prePartInterp_extProp₁
  apply total_cons_wf (total_wf (choice h).typing_of_cons.wf) (choice h)

@[simp]
lemma interpExt_obj : (interpExt α Γ A h).obj = interp α (Γ.cons A h) := rfl

instance (Γ : Ctx Λ) {A B : PTerm Λ} (h : Nonempty (Π.A B :: Γ.ctx ⊢ ⬝)) :
  IsStar (interpExt α Γ _ h) := sorry

def interpTmS (Γ : Ctx Λ) (A : PTerm Λ) (a : PTerm Λ) :
  ∀ (_ : Γ.ctx ⊢ a : A) (h : Nonempty (A :: Γ.ctx ⊢ ⬝)),  Section (interpExt α Γ A h)
| .var _ _ n h₁ h₂, h => by sorry -- diagnal???
| .sort _ _ _ ΛAx.ax h', h => by sorry -- false
| .pi _ A B _ _ _ ΛRel.rel h₁ h₂, h =>
  Ax.intro _ (interpExt α _ _ ⟨wf.cons _ _ _ (typing.pi _ _ _ _ _ _ ΛRel.rel h₁ h₂)⟩)
| .abs _ A b B _ _ _ ΛRel.rel h₁ h₂ h₃, h => by
  change Section (Pi.form _ _)
  apply Pi.intro
  convert interpTmS (Γ.cons A ⟨h₃.wf⟩) B b h₃ ⟨wf.cons _ _ _ h₂⟩
  ext; simp [Ext.mkProp₂, Ext.mkProp₁, interpExt]; rfl --???
| .app _ f A B a h₂ h₃, h => by
  have aux₁ : Nonempty (A :: Γ.ctx ⊢ ⬝) := sorry
  have aux₂ : Nonempty (B :: A :: Γ.ctx ⊢ ⬝) := sorry
  let ia := interpTmS _ _ _ h₃ aux₁
  let ext := interpExt α (Γ.cons A aux₁) B aux₂
  have : IsStar ext := sorry
  have : IsStar (interpExt α Γ A aux₁) := sorry
  have : interpExt α Γ (B{a}) h = ext.pullback ia.left := sorry
  rw [this]
  apply Pi.elim
  convert interpTmS _ _ _ h₂ sorry
  congr 1
  ext; simp [Ext.mkProp₂, ext, Ext.mkProp₁, interpExt]; rfl
| .conv _ a A B s h₁ h₂ h₃, h => by
  have aux : Nonempty (A :: Γ.ctx ⊢ ⬝ ) := sorry -- need typing correct
  have : interpExt α Γ B h = interpExt α Γ A aux := by
    ext; simp [interp]; congr 1
    apply partInterp_betac (Ctx.wf' _) (Ctx.wf' _) h₁.of_head_of_eq.symm
  convert interpTmS _ _ _ h₂ aux using 1





end Initial
end Λ

end Λ
