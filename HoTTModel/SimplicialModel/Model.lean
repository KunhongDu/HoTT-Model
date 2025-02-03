import HoTTModel.SimplicialModel.Universe
import HoTTModel.LocallyCartesianClosed.Presheaf
import HoTTModel.ContextualCategory.Chain

-- define a universe

namespace SSet
open CategoryTheory Limits Simplicial Universe Opposite

noncomputable section

universe u

variable (α : Cardinal.{u})

def Uni : Universe SSet.{u} where
  up := U' α
  down := U α
  hom := (UniWOKan α).hom
  isPullback f := IsPullback.of_hasPullback (UniWOKan α).hom f

def Model : Type (u + 1) := Chains (Uni α) Δ[0]

instance : KanFibration (Uni α).hom := UniSmallWOKan.Kan

instance : KanFibration (Pi.gen₁_snd (Uni α)) :=
  KanFibration.IsPullback_snd ((Uni α).isPullback _)

instance : KanFibration (Pi.gen₂_snd (Uni α)) :=
  KanFibration.IsPullback_snd ((Uni α).isPullback _)

instance : KanFibration (Pi.gen₂_snd' (Uni α)).hom :=
  inferInstanceAs (KanFibration (Pi.gen₂_snd (Uni α)))

-- this follows from a general result
instance : KanFibration (((Π(Pi.gen₁_snd (Uni α))).obj (Pi.gen₂_snd' (Uni α))).hom) := sorry

variable [α.IsRegularClass] [α.Uncountable] [α.IsStrongLimitClass]

def Pi.SmallWO : SmallWO α (Pi.obj (Uni α)) where
  wo := toWO ((Π(Pi.gen₁_snd (Uni α))).obj (Pi.gen₂_snd' (Uni α))).hom
  small := by
    apply SmallFibre.stableUnderPushforward
    <;> apply SmallFibre.stableUnderPullback (UniSmallWOKan α).small ((Uni α).isPullback _)

lemma Pi.SmallWO_Kan : (SmallWO α).Kan := by
  dsimp [SmallWO, SmallWO.Kan, SmallWO.hom, toWO]
  infer_instance

def Pi.Υ_obj : (Υ α).obj (op (Pi.obj (Uni α))) := by
    apply Υ_obj.mk (Pi.SmallWO α) (SmallWO_Kan _)

def Pi : Pi.Structure (Uni α) where
  hom := Υ.toHom (Pi.Υ_obj α)
  iso := (UniSmallWOKan.universal (Pi.SmallWO α) (Pi.SmallWO_Kan _)).some.toOverIso

instance : Chains.isTerminal Δ[0] where
  is_terminal := Δ0_is_terminal

def Pi_type := Chains.Pi_type (t := Δ[0]) (Pi α)

end
