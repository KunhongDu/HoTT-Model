import Mathlib.CategoryTheory.Closed.Cartesian
import HoTTModel.SSet.Lemmas -- remove this line later

noncomputable section

open CategoryTheory Category Limits MonoidalCategory Simplicial SSet
     standardSimplex Opposite
/-
/-
instance : MonoidalCategory (Type u) where
  tensorObj X Y := X × Y
  whiskerLeft _ _ _ f a := ⟨a.1, f a.2⟩
  whiskerRight f _ a := ⟨f a.1, a.2⟩
  tensorHom f g a := ⟨f a.1, g a.2⟩
  tensorUnit := PUnit
  associator X Y Z := {
    hom := fun a ↦ ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
    inv := fun a ↦ ⟨⟨a.1, a.2.1⟩, a.2.2⟩
  }
  leftUnitor X := {
    hom := fun a ↦ a.2
    inv := fun a ↦ ⟨PUnit.unit, a⟩
  }
  rightUnitor X :={
    hom := fun a ↦ a.1
    inv := fun a ↦ ⟨a, PUnit.unit⟩
  }
-/
noncomputable instance : MonoidalCategory (Type u) :=
  monoidalOfHasFiniteProducts (Type u)

/-
synthesized type class instance is not definitionally equal to iHomression inferred by typing rules, synthesized
  instMonoidalCategoryType_hoTTModel
inferred
  monoidalOfHasFiniteProducts Type
-/
#synth HasLimitsOfSize Type

def iHom (X : Type) : Type ⥤ Type where
  obj Y := X → Y
  map f := fun g ↦ f ∘ g

def Adj (X : Type) : tensorLeft X ⊣ iHom X where
  homEquiv X' Y :={
    toFun := by
      simp [iHom]
      intro f x' x

    invFun := _
    left_inv := _
    right_inv := _
  }
  unit := _
  counit := _
  homEquiv_unit := _
  homEquiv_counit := _


noncomputable instance (X : Type) : iHomonentiable X where
  rightAdj := iHom X
  adj := Adj X
-/

namespace SSet
universe u

instance : MonoidalCategory SSet :=
  monoidalOfHasFiniteProducts SSet

-- well instance for `HasLimits SSet.{u}` hasn't been installed lol
/--
  `X.iHom Y` is the internal hom in SSet, whose simplices are `X ⨯ Δ[n] → Y`
-/
def iHom (X Y : SSet) : SSet where
  obj n := X ⨯ Δ[n.unop.len] ⟶ Y
  map {m n} φ := fun g ↦ X ◁ standardSimplex.map φ.unop ≫ g

variable (X : SSet)

def iHomFunctor : SSet ⥤ SSet where
  obj := iHom X
  map {X' Y} f := {
    app := fun _ g ↦ g ≫ f
    naturality := by aesop_cat
  }

/--
  `X.exp Y := Y.iHom X`
-/
def exp (X Y : SSet) : SSet := Y.iHom X

def expFunctor : SSetᵒᵖ ⥤ SSet where
  obj := fun Y ↦ X.exp Y.unop
  map {Y Y'} f :={
    app := fun _ g ↦ prod.map f.unop (𝟙 _) ≫ g
    naturality := by
      intros; ext; simp [exp, iHom]
  }
  map_id := by
    intro Y; ext; simp only [SimplexCategory.mk_len, unop_id, prod.map_id_id, id_comp]; rfl
  map_comp := by
    intro _ _ _ _ _
    apply NatTrans.ext
    ext : 1; erw [NatTrans.vcomp_app]
    ext; simp

-- adjEquiv between `X ⨯ - ⊣ X.ihom -`
variable (Y Z: SSet)

def adjEquiv_toFun : (X ⨯ Y ⟶ Z) → (Y ⟶ (X.iHom Z)) :=
  fun f ↦ {
    app := fun _ y ↦ X ◁ (Y.yonedaEquiv _).symm y ≫ f
    naturality := by
      apply recop
      intro m
      apply recop
      intro n φ
      ext y
      simp [iHomFunctor, iHom]
      congr
      apply_fun (Y.yonedaEquiv _)
      convert Y.yonedaEquiv_naturality ((Y.yonedaEquiv _).symm y) φ.unop
      simp only [Equiv.apply_symm_apply]
      rfl
  }

def adjEquiv_invFun : (Y ⟶ X.iHom Z) → (X ⨯ Y ⟶ Z) :=
  fun f ↦ {
    app := fun _ x ↦
      prod.mapping (f.app _ $ ((@prod.snd SSet).app _ x))
        ((@prod.fst SSet).app _ x) ((yonedaEquiv _ _) (𝟙 _))
    naturality := by
      intro m n φ
      ext x
      simp
      rw [← prod.mapping.naturality, hom_naturality_apply, hom_naturality_apply,
          hom_naturality_apply] -- I would like repeat to do this
      apply prod.mapping.functoriality
  }

def adjEquiv :((tensorLeft X).obj Y ⟶ Z) ≃ (Y ⟶ X.iHomFunctor.obj Z) where
  toFun := adjEquiv_toFun _ _ _
  invFun := adjEquiv_invFun _ _ _
  left_inv := by
    intro f
    ext k x
    cases k using recop
    simp [adjEquiv_invFun, adjEquiv_toFun, prod.mapping]
    simp [yonedaEquiv_symm_naturality'₂, yonedaEquiv_symm_naturality']
    congr
    apply prod.hom_ext
    <;> simp
  right_inv := by
    intro f
    ext k y
    cases k using recop
    rename ℕ => k
    simp [adjEquiv_toFun]
    apply NatTrans.ext
    ext l x
    cases l using recop
    rename ℕ => l
    erw [NatTrans.vcomp_app]
    simp [adjEquiv_invFun, prod.mapping]
    rw [yonedaEquiv_symm_naturality', yonedaEquiv_symm_naturality',
        yonedaEquiv_symm_naturality' (f.app _ _)]
    simp
    rw [yonedaEquiv_symm_naturality' (prod.snd (X := X))]
    simp
    rw [yonedaEquiv_symm_naturality' f]
    simp
    -- `Δ[l] → X ⨯ Δ[k] → Δ[k] → Y → X.iHom Z` vs (under yoneda)
    -- `X × Δ[l] → X × Δ[k] → Z` with
    -- the first given by `(𝟙, Δ[l] → X × Δ[k] → Δ[k])`
    -- the second given by `Δ[k] → Y → X.iHom Z` then yoneda
    -- the point is any `Δ[l] → Δ[k]` in lhs and rhs is given by some `[l] → [k]`
    have : ((X.iHomFunctor.obj Z).yonedaEquiv [l])
      (((X ⨯ Δ[k]).yonedaEquiv [l]).symm x ≫ prod.snd ≫ (Y.yonedaEquiv [k]).symm y ≫ f) =
        prod.map (𝟙 X) ((yonedaEquiv _ _).symm x ≫ prod.snd) ≫
          (X.iHomFunctor.obj Z).yonedaEquiv _ ((Y.yonedaEquiv [k]).symm y ≫ f) := by
        rw [← Category.assoc _ prod.snd]
        obtain ⟨φ, hφ⟩ := exists_eq_standardSimplex_map
          (((X ⨯ Δ[k]).yonedaEquiv [l]).symm x ≫ prod.snd)
        rw [hφ]
        exact (yonedaEquiv_naturality _ _ _).symm
    simp [this]
    -- make it a lemma lol
    have : prod.lift (((X ⨯ Δ[k]).yonedaEquiv [l]).symm x ≫ prod.fst)
      (((X ⨯ Δ[k]).yonedaEquiv [l]).symm x ≫ prod.snd) =
        ((X ⨯ Δ[k]).yonedaEquiv [l]).symm x := by
        apply prod.hom_ext <;> simp
    rw [this, yonedaEquiv_symm_naturality']

def unit : 𝟭 SSet ⟶ tensorLeft X ⋙ X.iHomFunctor where
  app Y := {
    app := fun _ y ↦  prod.map (𝟙 _) ((yonedaEquiv _ _).symm y)
    naturality := by
      intro n m φ
      ext k
      simp
      apply prod.hom_ext
      . simp [iHomFunctor, iHom]
      . simp [iHomFunctor, iHom]; congr
        exact Y.yonedaEquiv_symm_naturality₂ (m := m.unop.len) (n := n.unop.len) k φ.unop
  }
  naturality := by
    intro Y Z f
    ext n y
    cases n using recop
    erw [NatTrans.vcomp_app, NatTrans.vcomp_app]
    simp [iHomFunctor, iHom]
    rw [Y.yonedaEquiv_symm_naturality'₂]

def counit : X.iHomFunctor ⋙ tensorLeft X ⟶ 𝟭 SSet where
  app Y :={
    app := fun n x ↦ prod.mapping ((@prod.snd SSet).app _ x) ((@prod.fst SSet).app _ x)
      ((yonedaEquiv _ _) (𝟙 _))
    naturality := by
      intro n m φ; ext x; simp
      rw [hom_naturality_apply, hom_naturality_apply, ← prod.mapping.naturality]
      apply prod.mapping.functoriality _ (𝟙 _) (standardSimplex.map φ.unop)
  }
  naturality := by
    intro Y Z f; ext k x
    erw [NatTrans.vcomp_app, NatTrans.vcomp_app]; simp
    rw [← prod.mapping.functoriality']
    congr
    . change ((prod.map (𝟙 X) (X.iHomFunctor.map f)) ≫ prod.snd).app k _ = _
      simp only [prod.map_snd]; rfl
    . change ((prod.map (𝟙 X) (X.iHomFunctor.map f)) ≫ prod.fst).app k _ = _
      simp only [prod.map_fst, comp_id]

def adjCoreHomEquivUnitCounit : Adjunction.CoreHomEquivUnitCounit (tensorLeft X) X.iHomFunctor where
  homEquiv := X.adjEquiv
  unit := X.unit
  counit := X.counit
  homEquiv_unit := rfl
  homEquiv_counit := by
    intro Y Z f
    ext k x
    erw [NatTrans.vcomp_app]
    simp [adjEquiv, adjEquiv_invFun, counit]
    congr
    . change (_ ≫ f).app _ _ = (prod.map (𝟙 X) f ≫ _).app _ _
      simp only [prod.map_snd]
    . change _ = (prod.map (𝟙 X) f ≫ _).app _ _
      simp only [prod.map_fst, comp_id]

def adj := Adjunction.mk' X.adjCoreHomEquivUnitCounit

instance : Exponentiable X where
  rightAdj := X.iHomFunctor
  adj := X.adj

lemma adjEquiv_naturality_left_symm {X Y K L : SSet} (i : L ⟶ K) (f : K ⟶ X.exp Y) :
    (Y.adjEquiv _ _).symm (i ≫ f) = Y ◁ i ≫ ((Y.adjEquiv _ _).symm f) := by
  have : Y.adjEquiv = Y.adj.homEquiv :=
    (Adjunction.mk'_homEquiv Y.adjCoreHomEquivUnitCounit).symm
  rw [this] -- I think erw should unfold this!! But it does not!
  exact Y.adj.homEquiv_naturality_left_symm i f

lemma adjEquiv_naturality_left_symm' {X Y K L : SSet} (i : L ⟶ K) (f : K ⟶ X.exp Y) :
    i ≫ f = (Y.adjEquiv _ _) (Y ◁ i ≫ ((Y.adjEquiv _ _).symm f)) := by
  apply_fun (Y.adjEquiv _ _).symm
  simp; apply adjEquiv_naturality_left_symm

lemma adjEquiv_naturality_symm {X Y K L : SSet} (i : L ⟶ K) (f : Y ⟶ X.exp K) :
    (L.adjEquiv _ _).symm (f ≫ X.expFunctor.map (op i)) =
      i ▷ Y ≫ ((K.adjEquiv Y X).symm f) := by
  sorry

lemma yonedaEquiv_eq_adjEquiv_invFun (X Y : SSet) {n : ℕ} :
    ⇑((Y.iHom X).yonedaEquiv [n]) =  (Y.adjEquiv Δ[n] X).invFun := by
  ext f; apply NatTrans.ext
  ext k y
  cases k using recop
  rename ℕ => k
  simp [adjEquiv, adjEquiv_invFun, prod.mapping]
  rw [yonedaEquiv_symm_naturality', yonedaEquiv_symm_naturality'₂,
      yonedaEquiv_symm_naturality']
  obtain ⟨φ, hφ⟩ := exists_eq_standardSimplex_map
    ((Δ[n].yonedaEquiv _).symm $ (@prod.snd SSet).app _ y)
  erw [hφ, ← yonedaEquiv_naturality]
  congr 1
  change _ = _ ≫ _ ≫ _
  rw [← Category.assoc]
  congr 1; apply prod.hom_ext
  . simp
  . simp; rw [← hφ, yonedaEquiv_symm_naturality'₂]

lemma adjEquiv_yonedaEquiv_apply {X Y : SSet} (f : Δ[n] ⟶ Y.iHom X) :
    (Y.adjEquiv _ _) (yonedaEquiv _ _ f) = f := by
  convert (Y.adjEquiv _ _).right_inv f
  exact yonedaEquiv_eq_adjEquiv_invFun _ _

lemma yonedaEquiv_symm_adjEquiv_symm_apply {X Y : SSet} (f : Δ[n] ⟶ Y.iHom X) :
    (yonedaEquiv _ _).symm ((Y.adjEquiv _ _).symm f) = f := by
  apply_fun yonedaEquiv _ _
  apply_fun Y.adjEquiv _ _
  simp; exact (adjEquiv_yonedaEquiv_apply f).symm

lemma yonedaEquiv_adjEquiv_apply {X Y : SSet} (x : (Y.iHom X).obj n) :
    yonedaEquiv _ _ (Y.adjEquiv _ _ x) = x := by
  convert (Y.adjEquiv _ _).left_inv x
  exact yonedaEquiv_eq_adjEquiv_invFun _ _

lemma adjEquiv_symm_yonedaEquiv_symm_apply {X Y : SSet} (x : (Y.iHom X).obj n) :
    (Y.adjEquiv _ _).symm ((yonedaEquiv _ _ ).symm x) = x := by
  apply_fun Y.adjEquiv _ _
  apply_fun yonedaEquiv _ _
  simp; exact (yonedaEquiv_adjEquiv_apply x).symm

end SSet



end
