import HoTTModel.ModelCategory.Basics
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

namespace CategoryTheory
open Limits ModelStructure Functor

universe u₁ v₁ u₂ v₂
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

def Functor.MorphismPropertyImp  (F : C ⥤ D)
  (P : MorphismProperty C) (Q : MorphismProperty D) : Prop :=
  ∀ {X Y : C} {f : X ⟶ Y}, P f → Q (F.map f)

section

-- Adjunction and FunctorialWeakFactorSys

variable {F : C ⥤ D} {G : D ⥤ C}
  {P₁ P₂ : MorphismProperty C} {Q₁ Q₂: MorphismProperty D}

lemma Adjunction.right_imp_of_left_imp (adj : F ⊣ G) (S₁ : FunctorialWeakFactorSys P₁ P₂)
  (S₂ : FunctorialWeakFactorSys Q₁ Q₂) (h : F.MorphismPropertyImp P₁ Q₁):
    G.MorphismPropertyImp Q₂ P₂ := by
  intro X Y f hf
  simp_rw [S₁.right_fork_left, ← adj.hasLiftingProperty_iff]
  rw [S₂.right_fork_left] at hf
  exact fun g hg ↦ hf _ (h hg)

end

variable [HasLimits C] [HasColimits C] [ModelStructure C]
  [HasLimits D] [HasColimits D] [ModelStructure D]
  (F : C ⥤ D) (G : D ⥤ C)

class PreserveCofibAcyCofib : Prop where
  cofib : F.MorphismPropertyImp cofib cofib
  acyCofib : F.MorphismPropertyImp acyCofib acyCofib

class LeftQuillen extends IsLeftAdjoint F, PreserveCofibAcyCofib F

class PreserveFibAcyFib : Prop where
  fib : F.MorphismPropertyImp fib fib
  acyFib : F.MorphismPropertyImp acyFib acyFib

class RightQuillen extends IsRightAdjoint F, PreserveFibAcyFib F

-- do it in a general way...
variable {F G} in
lemma Adjunction.right_PreserveFibAcyFib_of_left_preserveFibAcyCofib
  (adj : F ⊣ G) (_ : PreserveCofibAcyCofib F) :
    PreserveFibAcyFib G where
  fib := adj.right_imp_of_left_imp fibWfs fibWfs PreserveCofibAcyCofib.acyCofib
  acyFib := adj.right_imp_of_left_imp cofibWfs cofibWfs PreserveCofibAcyCofib.cofib

lemma Adjunction.left_preserveFibAcyCofib_of_right_PreserveFibAcyFib
  (adj : F ⊣ G) (_ : PreserveFibAcyFib G) :
    PreserveCofibAcyCofib F := sorry

structure QuillenAdjuction extends F ⊣ G where
  preserveCofibAcyCofib : PreserveCofibAcyCofib F

lemma QuillenAdjuction.preserveFibAcyCofib (adj : QuillenAdjuction F G) :
    PreserveFibAcyFib G :=
  adj.toAdjunction.right_PreserveFibAcyFib_of_left_preserveFibAcyCofib
    adj.preserveCofibAcyCofib

def Adjuction.QuillenAdjuctionMkOfPreserveFibAcyFib (adj : F ⊣ G)
  (P : PreserveFibAcyFib G):
    QuillenAdjuction F G where
  toAdjunction := adj
  preserveCofibAcyCofib := adj.left_preserveFibAcyCofib_of_right_PreserveFibAcyFib P
