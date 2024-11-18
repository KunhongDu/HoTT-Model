import HoTTModel.SSet.Lemmas

open CategoryTheory Simplicial Limits SimplexCategory Function Opposite Classical

noncomputable section

namespace SSet

variable {C : Type*} [Category C]

variable {X Y : SSet}

class KanFibration (p : X ⟶ Y) : Prop where
  lift : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄ {f} {g} (D : CommSq f (hornInclusion n i) p g),
    Nonempty D.LiftStruct

def KanFibration.LiftStruct {p : X ⟶ Y} [KanFibration p] {n} {i} {f} {g}
(D : CommSq f (hornInclusion n i) p g) : D.LiftStruct := choice (KanFibration.lift D)

-- this is a general statement
namespace KanFibration
open standardSimplex
lemma iff_is_KanComplex (X : SSet) :
  KanFibration X.toΔ0 ↔ X.KanComplex := by
  constructor
  . intro h; constructor; intro n i σ₀
    have D : CommSq σ₀ (hornInclusion n i) X.toΔ0 (Δ[n]).toΔ0 := ⟨unique_toΔ0 _ _⟩
    set L := LiftStruct D
    exact ⟨L.l, L.fac_left.symm⟩
  . intro h; constructor; intro n i f g D
    rcases KanComplex.hornFilling f with ⟨σ, hσ⟩
    use σ; exact hσ.symm; apply unique_toΔ0

lemma of_isIso (p : X ⟶ Y) [IsIso p] : KanFibration p := ⟨by
  intro n i f g D
  use (g ≫ inv p)
  rw [← Category.assoc, IsIso.comp_inv_eq, D.w]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  ⟩

instance (p : X ⟶ Y) [IsIso p] : KanFibration p := of_isIso p

-- TODO : retract

lemma IsPullback_snd {W X Y Z : SSet} {fst : W ⟶ X} {snd : W ⟶ Y}
  {f : X ⟶ Z} {g : Y ⟶ Z} (P : IsPullback fst snd f g) [KanFibration f] :
    KanFibration snd := ⟨by
  intro n i h h' D
  have D' : CommSq (h ≫ fst) (hornInclusion _ _) f (h' ≫ g) :=
    ⟨by rw [Category.assoc, P.w, ← Category.assoc, D.w, Category.assoc]⟩
  use P.lift (LiftStruct D').l h' (LiftStruct _).fac_right
  . apply P.hom_ext
    . simp only [Category.assoc, IsPullback.lift_fst, (LiftStruct _).fac_left]
    . simp only [Category.assoc, IsPullback.lift_snd, D.w]
  . simp only [IsPullback.lift_snd]⟩

instance pullback_snd {f : X ⟶ Z} {g : Y ⟶ Z} [KanFibration f] :
    KanFibration (pullback.snd f g) :=
  IsPullback_snd (IsPullback.of_hasPullback f g)

lemma pullback_snd' {f : X ⟶ Z} {g : Y ⟶ Z} (_ : KanFibration f) :
    KanFibration (pullback.snd f g) :=
  IsPullback_snd (IsPullback.of_hasPullback f g)

lemma IsPullback_fst {W X Y Z : SSet} {fst : W ⟶ X} {snd : W ⟶ Y}
  {f : X ⟶ Z} {g : Y ⟶ Z} (P : IsPullback fst snd f g) [KanFibration g] :
    KanFibration fst := ⟨(IsPullback_snd P.flip).lift⟩

instance pullback_fst {f : X ⟶ Z} {g : Y ⟶ Z} [KanFibration g] :
    KanFibration (pullback.fst f g) :=
  IsPullback_fst (IsPullback.of_hasPullback f g)

lemma pullback_fst' {f : X ⟶ Z} {g : Y ⟶ Z} (_ : KanFibration g) :
    KanFibration (pullback.fst f g) :=
  IsPullback_fst (IsPullback.of_hasPullback f g)

lemma of_forall_pullback_snd_KanFibration {f : X ⟶ S}
  (h : ∀ {k}, ∀ σ : Δ[k] ⟶ S, KanFibration (pullback.snd f σ)) :
    KanFibration f := ⟨by
      intro n i g g' D
      specialize h g'
      have D' : CommSq (pullback.lift (f := f) (g := g') g (hornInclusion _ _) D.w)
        (hornInclusion _ _) (pullback.snd _ _) (𝟙 _) := ⟨by simp⟩
      use (LiftStruct D').l ≫ pullback.fst _ _
      . rw [← Category.assoc, (LiftStruct D').fac_left, pullback.lift_fst]
      . rw [Category.assoc, pullback.condition, ← Category.assoc,
            (LiftStruct D').fac_right, Category.id_comp]
    ⟩

lemma comp (p : X ⟶ Y) [KanFibration p] (q : Y ⟶ Z) [KanFibration q] :
  KanFibration (p ≫ q) := ⟨by
    intro n i f g D
    have D₁ : CommSq (f ≫ p) (hornInclusion n i) q g := ⟨by simp [D.w]⟩
    have D₂ : CommSq f (hornInclusion n i) p (LiftStruct D₁).l :=
      ⟨(LiftStruct _).fac_left.symm⟩
    use (LiftStruct D₂).l
    exact (LiftStruct D₂).fac_left
    rw [← Category.assoc, (LiftStruct _).fac_right, (LiftStruct _).fac_right]⟩

lemma isIso_comp {X Y Z : SSet} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [KanFibration g] :
    KanFibration (f ≫ g) := comp _ _

lemma comp_isIso {X Y Z : SSet} (f : X ⟶ Y) [KanFibration f] (g : Y ⟶ Z) [IsIso g]:
    KanFibration (f ≫ g) := comp _ _

lemma isIso_comp' {X Y Z : SSet} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) (_ : KanFibration g) :
    KanFibration (f ≫ g) := comp _ _

lemma comp_isIso' {X Y Z : SSet} (f : X ⟶ Y) (_ : KanFibration f) (g : Y ⟶ Z) [IsIso g]:
    KanFibration (f ≫ g) := comp _ _

lemma of_isIso_comp {X Y Z : SSet} (f : X ⟶ Y) [IsIso f]
  (g : Y ⟶ Z) (h : KanFibration (f ≫ g)) :
    KanFibration g := by
  rw [← Category.id_comp g, ← IsIso.inv_hom_id f, Category.assoc]
  apply isIso_comp

lemma of_comp_isIso {X Y Z : SSet} (f : X ⟶ Y)
  (g : Y ⟶ Z)  [IsIso g] (h : KanFibration (f ≫ g)):
    KanFibration f := by
  rw [← Category.comp_id f, ← IsIso.hom_inv_id g, ← Category.assoc]
  apply comp_isIso

-- toDo, rw hg to Epi or sujective???
lemma of_pullback_snd_KanFibration_of_surjective {W X Y Z : SSet} {fst : W ⟶ X} {snd : W ⟶ Y}
  {f : X ⟶ Z} {g : Y ⟶ Z} (P : IsPullback fst snd f g) [KanFibration snd]
  (hg : ∀ {k}, ∀ σ : Δ[k] ⟶ Z, ∃ σ' : Δ[k] ⟶ Y, σ' ≫ g = σ) :
    KanFibration f := by
  apply of_forall_pullback_snd_KanFibration
  intro k σ
  obtain ⟨σ', hσ⟩ := hg σ
  rw [← hσ]
  have : KanFibration (pullback.snd f g) := by
    set φ := IsLimit.conePointUniqueUpToIso P.isLimit (limit.isLimit (cospan f g))
    have : φ.hom ≫ pullback.snd f g = snd :=
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
    rw [← Iso.eq_inv_comp] at this
    rw [this]
    apply isIso_comp
  rw [← pullback.rightCompIso_hom_comp_snd]
  apply isIso_comp

-- TODO : KanFib : to KanCpx

-- TrivialKanFibration aka Acyclic ...
-- avoid using weak equivalence / simplicial homotopy group

class TrivialKanFibration (p : X ⟶ Y) : Prop where
  lift : ∀ ⦃n : ℕ⦄ {f} {g} (D : CommSq f p (boundaryInclusion n) g), Nonempty D.LiftStruct

#exit
-- minimal fibration

def ProdΔ0 : X ≅ prod X Δ[0] := prod_terminal_iso Δ0_is_terminal

def inc₀ : X ⟶ prod X Δ[1] := ProdΔ0.hom ≫ (prod.lift prod.fst <| prod.snd ≫ standardSimplex.map (δ 1))

def inc₁ : X ⟶ prod X Δ[1] := ProdΔ0.hom ≫ (prod.lift prod.fst <| prod.snd ≫ standardSimplex.map (δ 0))

structure FibrewiseHomotopy {X Y : SSet} (p : X ⟶ Y) (e e' : Δ[n] ⟶ X) where
  bound : (boundaryInclusion n) ≫ e = (boundaryInclusion n) ≫ e'
  comp : e ≫ p = e' ≫ p
  htp : prod Δ[n] Δ[1] ⟶ X
  res₀ : inc₀ ≫ htp = e
  res₁ : inc₁ ≫ htp = e'

class KanFibration.Minimal (p : X ⟶ Y) [KanFibration p] : Prop where
  eq_of : ∀ ⦃n : ℕ⦄ (e e' : Δ[n] ⟶ X), (FibrewiseHomotopy p e e') → e = e'



open KanFibration

structure FactorMiniTrivial (p : X ⟶ Y) [KanFibration p] where
  mid : SSet
  to_mid : X ⟶ mid
  kan₁ : KanFibration to_mid
  mini : Minimal to_mid
  from_mid : mid ⟶ Y
  tri : TrivialKanFibration from_mid

class Cofibration (f : X ⟶ Y) : Prop :=
  inj : ∀ ⦃n : ℕ⦄, Injective (f.app (op [n]))

end SSet
end
