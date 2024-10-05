import Mathlib.AlgebraicTopology.SimplicialSet
import HoTTModel.Lemmas.Fin

section SemiSimplexCategory

open CategoryTheory

def SemiSimplexCategory :=
  ℕ

namespace SemiSimplexCategory

section

def mk (n : ℕ) : SemiSimplexCategory :=
  n

scoped[SemiSimplicial] notation "⟦" n "⟧" => SemiSimplexCategory.mk n

def len (n : SemiSimplexCategory) : ℕ :=
  n

@[ext]
theorem ext (a b : SemiSimplexCategory) : a.len = b.len → a = b :=
  id

attribute [irreducible] SemiSimplexCategory

open SemiSimplicial

@[simp]
theorem len_mk (n : ℕ) : ⟦n⟧.len = n :=
  rfl

@[simp]
theorem mk_len (n : SemiSimplexCategory) : (⟦n.len⟧ : SemiSimplexCategory) = n :=
  rfl

protected def rec {F : SemiSimplexCategory → Sort*} (h : ∀ n : ℕ, F ⟦n⟧) : ∀ X, F X := fun n =>
  h n.len

protected def Hom (a b : SemiSimplexCategory) :=
  Fin (a.len + 1) ↪o Fin (b.len + 1)

namespace Hom

/-- Make a morphism in `SemiSimplexCategory` from a monotone map of `Fin`'s. -/
def mk {a b : SemiSimplexCategory} (f : Fin (a.len + 1) ↪o Fin (b.len + 1)) :
  SemiSimplexCategory.Hom a b := f

/-- Recover the monotone map from a morphism in the simplex category. -/
def toOrderEmbedding {a b : SemiSimplexCategory} (f : SemiSimplexCategory.Hom a b) :
    Fin (a.len + 1) ↪o Fin (b.len + 1) := f

theorem ext' {a b : SemiSimplexCategory} (f g : SemiSimplexCategory.Hom a b) :
    f.toOrderEmbedding = g.toOrderEmbedding → f = g := id

attribute [irreducible] SemiSimplexCategory.Hom

@[simp]
theorem mk_toOrderEmbedding {a b : SemiSimplexCategory} (f : SemiSimplexCategory.Hom a b) : mk f.toOrderEmbedding = f :=
  rfl

@[simp]
theorem toOrderEmbedding_mk {a b : SemiSimplexCategory} (f : Fin (a.len + 1) ↪o Fin (b.len + 1)) :
    (mk f).toOrderEmbedding = f :=
  rfl

theorem mk_toOrderEmbedding_apply {a b : SemiSimplexCategory} (f : Fin (a.len + 1) ↪o Fin (b.len + 1))
    (i : Fin (a.len + 1)) : (mk f).toOrderEmbedding i = f i :=
  rfl

/-- Identity morphisms of `SemiSimplexCategory`. -/
@[simp]
def id (a : SemiSimplexCategory) : SemiSimplexCategory.Hom a a :=
  mk (RelEmbedding.refl _)

/-- Composition of morphisms of `SemiSimplexCategory`. -/
@[simp]
def comp {a b c : SemiSimplexCategory} (f : SemiSimplexCategory.Hom b c) (g : SemiSimplexCategory.Hom a b) :
    SemiSimplexCategory.Hom a c :=
  mk <| g.toOrderEmbedding.trans f.toOrderEmbedding

end Hom

instance smallCategory : SmallCategory.{0} SemiSimplexCategory where
  Hom n m := SemiSimplexCategory.Hom n m
  id m := SemiSimplexCategory.Hom.id _
  comp f g := SemiSimplexCategory.Hom.comp g f
  id_comp _ := by apply Hom.ext'; ext; simp -- ehh
  comp_id _ := by apply Hom.ext'; ext; simp
  assoc _ _ _ := by apply Hom.ext'; ext; simp

@[simp]
lemma id_toOrderEmbedding (a : SemiSimplexCategory) :
    Hom.toOrderEmbedding (𝟙 a) = (RelEmbedding.refl _) := rfl

@[simp]
lemma comp_toOrderEmbedding {a b c: SemiSimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).toOrderEmbedding = f.toOrderEmbedding.trans g.toOrderEmbedding := rfl

-- Porting note: added because `Hom.ext'` is not triggered automatically
@[ext]
theorem Hom.ext {a b : SemiSimplexCategory} (f g : a ⟶ b) :
    f.toOrderEmbedding = g.toOrderEmbedding → f = g :=
  Hom.ext' _ _

-- `const` deleted. Don't see any use of it.

/-- Make a morphism `⟦n⟧ ⟶ [m]` from a monotone map between fin's.
This is useful for constructing morphisms between `⟦n⟧` directly
without identifying `n` with `⟦n⟧.len`.
-/
@[simp]
def mkHom {n m : ℕ} (f : Fin (n + 1) ↪o Fin (m + 1)) : (⟦n⟧ : SemiSimplexCategory) ⟶ ⟦m⟧ :=
  SemiSimplexCategory.Hom.mk f

theorem hom_zero_zero (f : (⟦0⟧ : SemiSimplexCategory) ⟶ ⟦0⟧) : f = 𝟙 _ := by
  ext
  simp only [Fin.coe_fin_one, id_toOrderEmbedding, RelEmbedding.refl_apply]

end

open SemiSimplicial

def δ {n} (i : Fin (n + 2)) : (⟦n⟧ : SemiSimplexCategory) ⟶ ⟦n + 1⟧ :=
  mkHom (Fin.succAboveOrderEmb i)

theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    δ i ≫ δ j.succ = δ j ≫ δ (Fin.castSucc i) := by
  ext k
  dsimp [δ, Fin.succAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;> · simp at * <;> omega

theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    δ i ≫ δ j =
      δ (j.pred fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) ≫
        δ (Fin.castSucc i) := by
  rw [← δ_comp_δ]
  · rw [Fin.succ_pred]
  · simpa only [Fin.le_iff_val_le_val, ← Nat.lt_succ_iff, Nat.succ_eq_add_one, ← Fin.val_succ,
      j.succ_pred, Fin.lt_iff_val_lt_val] using H

theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ δ j.succ =
      δ j ≫ δ i := by
  rw [δ_comp_δ]
  · rfl
  · exact H

@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} : δ i ≫ δ (Fin.castSucc i) = δ i ≫ δ i.succ :=
  (δ_comp_δ (le_refl i)).symm

@[reassoc]
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i) :
    δ i ≫ δ j = δ i ≫ δ i.succ := by
  subst H
  rw [δ_comp_δ_self]

theorem Hom.le  {m n : ℕ} (f : (⟦m⟧ : SemiSimplexCategory) ⟶ ⟦n⟧) : m ≤ n :=
  (Fin.le_image_of_StrictMono f.toOrderEmbedding.strictMono
    (Fin.last _)).trans (Fin.le_last _)

theorem degeneracy_map_empty_of_lt {m n : ℕ} (h : n < m) :
  IsEmpty ((⟦m⟧ : SemiSimplexCategory) ⟶ ⟦n⟧) := by
    contrapose! h; simp at h
    obtain ⟨f⟩ := h
    apply Hom.le f

section Concrete

instance : ConcreteCategory.{0} SemiSimplexCategory where
  forget :=
    { obj := fun i => Fin (i.len + 1)
      map := fun f => f.toOrderEmbedding }
  forget_faithful := ⟨fun h => by ext : 2; dsimp at h; rw [h]⟩

end Concrete

section Mono

instance mono {n m : SemiSimplexCategory} {f : n ⟶ m} : Mono f where
  right_cancellation {Z} g h H:= by
    ext x
    apply_fun fun f ↦ (Hom.toOrderEmbedding f) x at H
    simp at H
    rw [H]

end Mono

end SemiSimplexCategory

end SemiSimplexCategory

section SemiSimplicialObject

open CategoryTheory CategoryTheory.Limits -- is it used??

universe v u v' u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

def SemiSimplicialObject :=
  SemiSimplexCategoryᵒᵖ ⥤ C

@[simps!]
instance : Category (SemiSimplicialObject C) := by
  dsimp only [SemiSimplicialObject]
  infer_instance

scoped[SemiSimplicial]
  notation3:1000 X " _⟦" n "⟧" =>
    (X : CategoryTheory.SemiSimplicialObject _).obj (Opposite.op (SemiSimplexCategory.mk n))

section Limits
open SemiSimplicial

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SemiSimplicialObject C) := by
  dsimp [SemiSimplicialObject]
  infer_instance

instance [HasLimits C] : HasLimits (SemiSimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SemiSimplicialObject C) := by
  dsimp [SemiSimplicialObject]
  infer_instance

instance [HasColimits C] : HasColimits (SemiSimplicialObject C) :=
  ⟨inferInstance⟩

end Limits

section Hom

namespace SemiSimplicialObject
open SemiSimplicial Opposite

variable {C}

@[ext]
lemma hom_ext {X Y : SemiSimplicialObject C} (f g : X ⟶ Y)
    (h : ∀ (n : SemiSimplexCategoryᵒᵖ), f.app n = g.app n) : f = g :=
  NatTrans.ext _ _ (by ext; apply h)

lemma hom_ext' {X Y : SemiSimplicialObject C} (f g : X ⟶ Y)
    (h : ∀ n : ℕ, f.app  (op ⟦n⟧ : SemiSimplexCategoryᵒᵖ) = g.app (op ⟦n⟧)) : f = g :=
  NatTrans.ext _ _ (by ext n; exact h n.unop.len)

variable (X : SemiSimplicialObject C)

def δ {n} (i : Fin (n + 2)) : X _⟦n + 1⟧ ⟶ X _⟦n⟧ :=
  X.map (SemiSimplexCategory.δ i).op

def eqToIso {n m : ℕ} (h : n = m) : X _⟦n⟧ ≅ X _⟦m⟧ :=
  X.mapIso (CategoryTheory.eqToIso (by congr))

@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ j.succ ≫ X.δ i = X.δ (Fin.castSucc i) ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SemiSimplexCategory.δ_comp_δ H]

@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ j ≫ X.δ i =
      X.δ (Fin.castSucc i) ≫
        X.δ (j.pred fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SemiSimplexCategory.δ_comp_δ' H]

@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    X.δ j.succ ≫ X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) =
      X.δ i ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SemiSimplexCategory.δ_comp_δ'' H]

/-- The special case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ (Fin.castSucc i) ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SemiSimplexCategory.δ_comp_δ_self]

@[reassoc]
theorem δ_comp_δ_self' {n} {j : Fin (n + 3)} {i : Fin (n + 2)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  subst H
  rw [δ_comp_δ_self]

variable (C) in
@[simps!]
def whiskering (D : Type*) [Category D] :
    (C ⥤ D) ⥤ SemiSimplicialObject C ⥤ SemiSimplicialObject D :=
  whiskeringRight _ _ _

end SemiSimplicialObject

end Hom

end CategoryTheory

end SemiSimplicialObject

section SemiSSet

universe v u

open CategoryTheory CategoryTheory.Limits

open Simplicial

def SemiSSet : Type (u + 1) :=
  SemiSimplicialObject (Type u)

namespace SemiSSet

instance largeCategory : LargeCategory SemiSSet := by
  dsimp only [SemiSSet]
  infer_instance

instance hasLimits : HasLimits SemiSSet := by
  dsimp only [SemiSSet]
  infer_instance

instance hasColimits : HasColimits SemiSSet := by
  dsimp only [SemiSSet]
  infer_instance

@[ext]
lemma hom_ext {X Y : SemiSSet} {f g : X ⟶ Y} (w : ∀ n, f.app n = g.app n) : f = g :=
  SemiSimplicialObject.hom_ext _ _ w

/-- The ulift functor `SemiSSet.{u} ⥤ SemiSSet.{max u v}` on simplicial sets. -/
def uliftFunctor : SemiSSet.{u} ⥤ SemiSSet.{max u v} :=
  (SemiSimplicialObject.whiskering _ _).obj CategoryTheory.uliftFunctor.{v, u}

def standardSemiSimplex : SemiSimplexCategory ⥤ SemiSSet.{u} :=
  yoneda ⋙ uliftFunctor

scoped[SemiSimplicial] notation3 "Δ⟦" n "⟧" =>
  SemiSSet.standardSemiSimplex.obj (SemiSimplexCategory.mk n)

open SemiSimplicial

instance : Inhabited SemiSSet :=
  ⟨Δ⟦0⟧⟩

namespace standardSemiSimplex

open Finset Opposite SemiSimplexCategory

@[simp]
lemma map_id (n : SemiSimplexCategory) :
    (SemiSSet.standardSemiSimplex.map
      (SemiSimplexCategory.Hom.mk (RelEmbedding.refl _) : n ⟶ n)) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- Simplices of the standard simplex identify to morphisms in `SimplexCategory`. -/
def objEquiv (n : SemiSimplexCategory) (m : SemiSimplexCategoryᵒᵖ) :
    (standardSemiSimplex.{u}.obj n).obj m ≃ (m.unop ⟶ n) :=
  Equiv.ulift.{u, 0}

/-- Constructor for simplices of the standard simplex which takes a `OrderHom` as an input. -/
abbrev objMk {n : SemiSimplexCategory} {m : SemiSimplexCategoryᵒᵖ}
    (f : Fin (m.unop.len + 1) ↪o Fin (n.len + 1)) :
    (standardSemiSimplex.{u}.obj n).obj m :=
  (objEquiv _ _).symm (Hom.mk f)

lemma map_apply {m₁ m₂ : SemiSimplexCategoryᵒᵖ} (f : m₁ ⟶ m₂) {n : SemiSimplexCategory}
    (x : (standardSemiSimplex.{u}.obj n).obj m₁) :
    (standardSemiSimplex.{u}.obj n).map f x = (objEquiv _ _).symm (f.unop ≫ (objEquiv _ _) x) := by
  rfl

/-- The canonical bijection `(standardSimplex.obj n ⟶ X) ≃ X.obj (op n)`. -/
def _root_.SemiSSet.yonedaEquiv (X : SemiSSet.{u}) (n : SemiSimplexCategory) :
    (standardSemiSimplex.obj n ⟶ X) ≃ X.obj (op n) :=
  yonedaCompUliftFunctorEquiv X n

end standardSemiSimplex

end SemiSSet

end SemiSSet

section Functor_SimplexCategory

open CategoryTheory SemiSimplicial Simplicial SimplexCategory

def SemiSimplexCategory.toSimplexCategory : SemiSimplexCategory ⥤ SimplexCategory where
  obj n := [n.len]
  map {m n} f := SimplexCategory.Hom.mk f.toOrderEmbedding.toOrderHom

namespace SSet

def Functor.toSemiSSet : SSet ⥤ SemiSSet :=
  (whiskeringLeft _ _ _).obj SemiSimplexCategory.toSimplexCategory.op

def toSemiSSet : SSet → SemiSSet := Functor.toSemiSSet.obj

lemma toSemiSSet_eq_comp {X : SSet} :
    X.toSemiSSet = SemiSimplexCategory.toSimplexCategory.op ⋙ X :=
  rfl

end SSet
