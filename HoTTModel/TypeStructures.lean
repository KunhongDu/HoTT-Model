import HoTTModel.LocallyCartesianClosed.ChosenPullbacks
import HoTTModel.Universe

noncomputable section

open CategoryTheory Limits List LocallyCartesianClosed

variable {C : Type u} [CategoryTheory.Category.{v, u} C]
-- binary product follows from pullback + terminal object, but I'll assume this instance for now

namespace Universe
variable (U : Universe C)
set_option linter.unusedSectionVars false

section
variable [HasFiniteWidePullbacks C] [LocallyCartesianClosed C] {X : C} (f : X ⟶ U.down)
/-
@[simp]
def isoPullback :
    U.pt f ≅ pullback U.hom f :=
  (U.isPullback f).isoPullback

@[simp]
def isoPullback_flip :
    U.pt f ≅ pullback f U.hom :=
  (U.isPullback f).flip.isoPullback

def isoPullback.map :
    Over (U.pt f) ⥤ Over (pullback U.hom f) :=
  Over.map (U.isoPullback f).hom

def isoPullback.map_inv :
    Over (pullback U.hom f) ⥤  Over (U.pt f) :=
  Over.map (U.isoPullback f).inv

section
variable {X Y: C} {fst : Y ⟶ U.up} {snd : Y ⟶ X} {f : X ⟶ U.down}
  (is : IsPullback fst snd U.hom f)

@[simp]
def isoIsPullback : Y ≅ U.pt f :=
  is.isoIsPullback _ _ (U.isPullback f)

@[simp]
def isoOverSnd :
    Over.mk snd ≅ U.snd' f :=
  Over.isoMk ((is.isoIsPullback _ _ (U.isPullback f)))

@[simp]
def isoOverFst :
    Over.mk fst ≅ U.fst' f :=
  Over.isoMk (is.isoIsPullback _ _ (U.isPullback f))

end

section
-- pullback along universe

@[simp]
def fst'_isoPullback :
    U.fst' f ≅  (U.hom*).obj (Over.mk f) :=
  Over.isoMk (U.isoPullback_flip f) (U.isPullback f).flip.isoPullback_hom_snd

@[simps]
def pullback_map : Over U.down ⥤ Over U.up where
  obj f := U.fst' f.hom
  map {f g} h := (U.fst'_isoPullback f.hom).hom ≫ (U.hom)*.map h ≫
      (U.fst'_isoPullback g.hom).inv
  map_id f := by
    ext; simp [fst'_isoPullback, isoPullback_flip]
    apply (U.isPullback f.hom).flip.hom_ext
    <;> simp [Universe.isoPullback]
  map_comp f g := by ext; simp

variable {U} in
lemma pullback_map.map_left_eq_lift {X Y : Over U.down} (f : X ⟶ Y) :
    (U.pullback_map.map f).left =
      (U.isPullback Y.hom).lift (U.fst X.hom) (U.snd X.hom ≫ f.left)
        (by simp only [(U.isPullback X.hom).w, Category.assoc, Over.w]) := by
  apply (U.isPullback Y.hom).hom_ext
  <;> simp [fst'_isoPullback, isoPullback_flip]

@[simp, reassoc]
lemma pullback_map.map_fst {X Y : Over U.down} (f : X ⟶ Y) :
    (U.pullback_map.map f).left ≫ U.fst Y.hom = U.fst X.hom := by
  simp [fst'_isoPullback, isoPullback_flip]

def pullback_map.upperSquareIsPullback {X Y : Over U.down} (f : X ⟶ Y) :
    IsPullback (U.pullback_map.map f).left (U.snd X.hom) (U.snd Y.hom) f.left := by
  apply IsPullback.of_right _ _ (U.isPullback Y.hom)
  . convert U.isPullback X.hom
    . simp [fst'_isoPullback, isoPullback_flip]
    . exact Over.w f
  . rw [map_left_eq_lift, IsPullback.lift_snd]

def pullback_mapIsoPullback : U.pullback_map ≅ Over.pullback U.hom where
  hom :={
    app := fun f ↦ (U.fst'_isoPullback f.hom).hom
    naturality := by intros; simp
  }
  inv := {
    app := fun f ↦ (U.fst'_isoPullback f.hom).inv
    naturality := by intros; simp
  }
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

def pullback_adj := (adj U.hom).ofNatIsoLeft U.pullback_mapIsoPullback.symm

abbrev pullback_adjEquiv := U.pullback_adj.homEquiv

lemma pullback_adj.homEquiv_naturality_right
  {X : Over U.down} {Y Y' : Over U.up} (f : U.pullback_map.obj X ⟶ Y) (g : Y ⟶ Y') :
    (U.pullback_adj.homEquiv X Y') (f ≫ g) = (U.pullback_adj.homEquiv X Y) f ≫ (ΠU.hom).map g :=
  U.pullback_adj.homEquiv_naturality_right f g

lemma pullback_adj.homEquiv_naturality_right_symm
  {X : Over U.down} {Y Y' : Over U.up} (f : X ⟶ (ΠU.hom).obj Y) (g : Y ⟶ Y') :
    (U.pullback_adj.homEquiv X Y').symm (f ≫ (ΠU.hom).map g) =
      (U.pullback_adj.homEquiv X Y).symm f ≫ g :=
  U.pullback_adj.homEquiv_naturality_right_symm f g

end
/-
def fst_homEquiv (g : Over U.up) :
    (U.fst' f ⟶ g) ≃ ((U.hom*).obj (Over.mk f) ⟶ g) :=
  (U.fst'_isoPullback f).homFromEquiv


variable {f} in
lemma fst_homEquiv_naturality {g h : Over U.up} (i : U.fst' f ⟶ g) (j : g ⟶ h) :
    U.fst_homEquiv f h (i ≫ j) =  U.fst_homEquiv f g i ≫ j := by
  simp only [fst_homEquiv, Iso.homFromEquiv_apply, Category.assoc]

def fst_adjEquiv (g : Over U.up) :
    (U.fst' f ⟶ g) ≃ ((Over.mk f) ⟶ (Π(U.hom)).obj g) :=
  (U.fst_homEquiv f g).trans ((adj U.hom).homEquiv (Over.mk f) g)

lemma fst_adjEquiv_naturality {g h : Over U.up} (i : U.fst' f ⟶ g) (j : g ⟶ h) :
    U.fst_adjEquiv f h (i ≫ j) = U.fst_adjEquiv f g i ≫ (Π(U.hom)).map j := by
  simp only [fst_adjEquiv, Equiv.trans_apply]
  rw [U.fst_homEquiv_naturality i j]
  exact Adjunction.homEquiv_naturality_right _ _ _

lemma fst_adjEquiv_naturality_symm {g h : Over U.up} (i : Over.mk f ⟶ (Π(U.hom)).obj g)
  (j : g ⟶ h) :
    (U.fst_adjEquiv f h).symm (i ≫ (Π(U.hom)).map j) = (U.fst_adjEquiv f _).symm i ≫ j := by
  simp only [Equiv.symm_apply_eq, fst_adjEquiv_naturality,
    eq_self_iff_true, Equiv.apply_symm_apply]

-/

/-
section snd
-- pullback of universe

def snd'_isoPullback :
    U.snd' f ≅  (f*).obj U.over :=
  Over.isoMk (U.isoPullback f) (U.isPullback f).isoPullback_hom_snd

def snd_homEquiv (g : Over X) :
    (U.snd' f ⟶ g) ≃ ((f*).obj U.over ⟶ g) :=
  (U.snd'_isoPullback f).homFromEquiv

variable {f} in
lemma snd_homEquiv_naturality {g h : Over X} (i : U.snd' f ⟶ g) (j : g ⟶ h) :
    U.snd_homEquiv f h (i ≫ j) =  U.snd_homEquiv f g i ≫ j := by
  simp only [snd_homEquiv, Iso.homFromEquiv_apply, Category.assoc]

def snd_adjEquiv (g : Over X) :
    (U.snd' f ⟶ g) ≃ (U.over ⟶ (Πf).obj g) :=
  (U.snd_homEquiv f g).trans ((adj f).homEquiv U.over g)

lemma snd_adjEquiv_naturality {g h : Over X} (i : U.snd' f ⟶ g) (j : g ⟶ h) :
    U.snd_adjEquiv f h (i ≫ j) = U.snd_adjEquiv f g i ≫ (Πf).map j := by
  simp only [snd_adjEquiv, Equiv.trans_apply]
  rw [U.snd_homEquiv_naturality i j]
  exact Adjunction.homEquiv_naturality_right _ _ _

lemma snd_adjEquiv_naturality_symm {g h : Over X} (i : U.over ⟶ (Πf).obj g) (j : g ⟶ h) :
    (U.snd_adjEquiv f h).symm (i ≫ (Πf).map j) = (U.snd_adjEquiv f _).symm i ≫ j := by
  simp only [Equiv.symm_apply_eq, snd_adjEquiv_naturality,
    eq_self_iff_true, Equiv.apply_symm_apply]

end snd
-/

section
-- pullback as a functor along
/-
`   pt → U.up  `
`    ↓      ↓   `
`Y → X → U.down`
-/

variable {Y : C} (g : Y ⟶ X)

def isPullbackComp :
    IsPullback ((U.isPullback f).lift (U.fst (g ≫ f)) (U.snd (g ≫ f) ≫ g) (by simp [U.comm]))
      (U.snd (g ≫ f)) (U.snd f) g := by
  apply IsPullback.of_right (t := U.isPullback f)
  . convert U.isPullback (g ≫ f)
    simp only [IsPullback.lift_fst]
  . simp only [IsPullback.lift_snd]

def pullbackSnd'_isoPullback :
    U.pt (g ≫ f) ≅  pullback (U.snd f) g :=
  (U.isPullbackComp f g).isoPullback

def pullbackSnd'_isoPullback_snd' :
    U.snd' (g ≫ f) ≅  (g*).obj (U.snd' f) :=
  Over.isoMk (U.pullbackSnd'_isoPullback f g) (U.isPullbackComp f g).isoPullback_hom_snd

end
-/
namespace Pi
variable [HasBinaryProducts C] {t : C} (ht : IsTerminal t)

abbrev op := (Π(U.hom)).obj U.proj₂'

abbrev obj := (op U).left

abbrev hom : obj U ⟶ U.down := (op U).hom

abbrev gen₁ : C := U.pt (hom U)

abbrev gen₁_fst : gen₁ U ⟶ U.up := U.fst (hom U)

abbrev gen₁_snd : gen₁ U ⟶ obj U := U.snd (hom U)

abbrev gen₁_fst' : Over U.up := U.fst' (hom U)

abbrev gen₁_snd' : Over (obj U) := U.snd' (hom U)

abbrev gen₂_hom₀ : gen₁_fst' U ⟶ U.proj₂' :=
  (IsPullback.adjEquiv (U.isPullback (hom U)).flip _).symm (𝟙 _)

lemma gen₂_hom₀_comp_prod_snd :
    (gen₂_hom₀ U).left ≫ prod.snd = gen₁_fst U :=
  Over.w (gen₂_hom₀ U)

abbrev gen₂_hom : gen₁ U ⟶ U.down := (gen₂_hom₀ U).left ≫ U.proj₁

abbrev gen₂_hom' : Over U.down := Over.mk (gen₂_hom U)

abbrev Gen₂ : C := U.pt (gen₂_hom U)

abbrev gen₂_fst : Gen₂ U ⟶ U.up := U.fst (gen₂_hom U)

abbrev gen₂_snd : Gen₂ U ⟶ gen₁ U := U.snd (gen₂_hom U)

abbrev gen₂_fst' : Over U.up := U.fst' (gen₂_hom U)

abbrev gen₂_snd' : Over (gen₁ U) := U.snd' (gen₂_hom U)

structure Structure where
  hom : (op U).left ⟶ U.down
  iso : (Π(gen₁_snd U)).obj (gen₂_snd' U) ≅ U.snd' hom

abbrev Structure.fst (S : Structure U) : ((Π(gen₁_snd U)).obj (gen₂_snd' U)).left ⟶ U.up :=
  S.iso.hom.left ≫ U.fst S.hom

lemma Structure.isPullback (S : Structure U) :
    IsPullback S.fst ((Π(gen₁_snd U)).obj (gen₂_snd' U)).hom U.hom S.hom := by
  apply (U.isPullback S.hom).of_iso ((Over.forget _).mapIso S.iso.symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  all_goals simp [fst]
  rw [← Over.comp_left_assoc, Iso.inv_hom_id, Over.id_left, Category.id_comp]

-- the iso means, we would later need to do pullback along `gen₁_snd`
-- but since the `gen₁_snd` is a pullback of the universe
-- we can choose the pullbacks as ones along compositions!!!!

section
/-
variable {U} {Γ A : C} (δ : Γ ⟶ U.down) (δ' : U.pt δ ⟶ U.down)

def form₀' : Over.mk δ ⟶ op U :=
  IsPullback.adjEquiv (U.isPullback δ).flip _ (Over.homMk (prod.lift δ' (U.fst δ)))

abbrev form₀ : Γ ⟶ obj U := (form₀' δ δ').left

lemma form₀_comp_hom : form₀ δ δ' ≫ hom U = δ := by
  simp only [Over.w, Over.mk_hom]

def form₁' : U.fst' δ ⟶ gen₁_fst' U := by
  apply

abbrev form₁ : U.pt δ ⟶ gen₁ U := (form₁' δ δ').left

lemma form₁'_comp_Gen₂hom₀ :
    form₁' δ δ' ≫ gen₂_hom₀ U = Over.homMk (prod.lift δ' (U.fst δ)) := by
  erw [← U.pullback_adj.homEquiv_counit]
  simp [form₀', Equiv.symm_apply_apply]

@[reassoc]
lemma form₁_comp_Gen₂hom₀_left :
    form₁ δ δ' ≫ (gen₂_hom₀ U).left = prod.lift δ' (U.fst δ) :=
  congrArg CommaMorphism.left (form₁'_comp_Gen₂hom₀ δ δ')

lemma form₁_comp_Gen₂hom :
    form₁ δ δ' ≫ gen₂_hom U = δ' := by
  simp [gen₂_hom, ← Category.assoc, form₁_comp_Gen₂hom₀_left]

lemma form₁_comp_fst :
    form₁ δ δ' ≫ gen₁_fst U = U.fst δ := by
  rw [← gen₂_hom₀_comp_prod_snd, form₁_comp_Gen₂hom₀_left_assoc, prod.lift_snd]

abbrev form₁'' : Over.mk δ' ⟶ gen₂_hom' U :=
  Over.homMk (form₁ δ δ') (form₁_comp_Gen₂hom _ _)

def form₂' : U.fst' δ' ⟶ gen₂_fst' U := U.pullback_map.map (form₁'' δ δ')

abbrev form₂ : U.pt δ' ⟶ Gen₂ U := (form₂' δ δ').left

lemma form₂_comp_fst :
    form₂ δ δ' ≫ U.fst (gen₂_hom U) = U.fst δ' :=
  pullback_map.map_fst _ _

def form₁.isPullback :
    IsPullback (form₁ δ δ') (U.snd δ) (gen₁_snd U) (form₀ δ δ') :=
  pullback_map.upperSquareIsPullback _ (form₀' δ δ')

def form₂.isPullback :
    IsPullback (form₂ δ δ') (U.snd δ') (gen₂_snd U) (form₁ δ δ') :=
  pullback_map.upperSquareIsPullback _ (form₁'' δ δ')

lemma form₀'_ext₁ (f : Over.mk δ ⟶ op U)
  (hf : (U.pullback_map.map f).left ≫ gen₂_hom U = δ') :
    f = form₀' δ δ' := by
  simp [form₀']
  apply_fun (U.pullback_adjEquiv _ _).symm
  rw [U.pullback_adj.homEquiv_counit]
  ext; apply Limits.prod.hom_ext
  . simp [← hf]
  . have : (U.pullback_map.map f).left ≫ (gen₂_hom₀ U).left ≫ prod.snd = U.fst δ := by
      simp only [pullback_map.map_left_eq_lift, gen₂_hom₀_comp_prod_snd,
        Over.mk_hom, IsPullback.lift_fst]
    simp; conv_rhs => rw [← this]
    simp

end
-/

variable {U} {Γ A B : C} {δ : Γ ⟶ U.down} {γ : A ⟶ U.up} {π : A ⟶ Γ}
  {δ' : A ⟶ U.down} {γ' : B ⟶ U.up} {π' : B ⟶ A}
  (is : IsPullback γ π U.hom δ) (is' : IsPullback γ' π' U.hom δ')

/-
def pullbackAux : IsPullback γ' (π' ≫ (U.isoIsPullback is).hom) U.hom
  ((U.isoIsPullback is).inv ≫ δ') := by
  apply is'.of_iso (Iso.refl _) (Iso.refl _) (U.isoIsPullback is) (Iso.refl _)
  <;> simp
-/
def form₀' (_ : IsPullback γ' π' U.hom δ') : Over.mk δ ⟶ op U :=
  IsPullback.adjEquiv is.flip _ (Over.homMk (prod.lift δ' γ))

abbrev form₀ : Γ ⟶ obj U := (form₀' is is').left

lemma form₀_comp_hom : form₀ is is' ≫ hom U = δ := by
  simp only [Over.w, Over.mk_hom]

def form₁' : Over.mk γ ⟶ gen₁_fst' U :=
  is.flip.liftIsPullbackAlong' (U.isPullback (hom U)).flip (form₀' is is')

abbrev form₁ : A ⟶ gen₁ U := (form₁' is is').left

lemma form₁'_comp_gen₂hom₀ :
    form₁' is is' ≫ gen₂_hom₀ U = Over.homMk (prod.lift δ' γ) := by
  simp only [form₁', gen₂_hom₀]
  rw [IsPullback.adjEquiv_naturality_symm_left, Category.comp_id]
  simp [form₀', Equiv.symm_apply_apply]

@[simp, reassoc]
lemma form₁_comp_gen₂hom₀_left :
    form₁ is is' ≫ (gen₂_hom₀ U).left = prod.lift δ' γ :=
  congrArg CommaMorphism.left (form₁'_comp_gen₂hom₀ is is')

@[simp]
lemma form₁_comp_Gen₂hom :
    form₁ is is' ≫ gen₂_hom U = δ' := by
  simp [gen₂_hom, ← Category.assoc, form₁_comp_gen₂hom₀_left]

@[simp]
lemma form₁_comp_fst :
    form₁ is is' ≫ gen₁_fst U = γ := by
  rw [← gen₂_hom₀_comp_prod_snd, form₁_comp_gen₂hom₀_left_assoc, prod.lift_snd]

@[simp]
lemma form₁_comp_snd :
    form₁ is is' ≫ gen₁_snd U = π ≫ form₀ is is' := by
  simp [form₁, form₁']

def form₁'' : Over.mk δ' ⟶ Over.mk (gen₂_hom U) :=
  Over.homMk (form₁ is is') (form₁_comp_Gen₂hom is is')

def form₂' : Over.mk γ' ⟶ gen₂_fst' U :=
  is'.flip.liftIsPullbackAlong' (U.isPullback (gen₂_hom U)).flip (form₁'' is is')

abbrev form₂ : B ⟶ Gen₂ U := (form₂' is is').left

@[simp]
lemma form₂_comp_fst :
    form₂ is is' ≫ gen₂_fst U = γ' := by
  simp [form₂, form₂', Pi.form₂_comp_fst]

@[simp]
lemma form₂_comp_snd :
    form₂ is is' ≫ gen₂_snd U = π' ≫ form₁ is is' := by
  simp [form₂, form₂', form₁'']

def form₁_isPullback :
    IsPullback (form₁ is is') π (gen₁_snd U) (form₀ is is') := by
  apply IsPullback.of_right _ (form₁_comp_snd is is') (U.isPullback (hom U))
  simpa using is

def form₂_isPullback :
    IsPullback (form₂ is is') π' (gen₂_snd U) (form₁ is is') := by
  apply IsPullback.of_right _ (form₂_comp_snd is is') (U.isPullback (gen₂_hom U))
  simpa using is'

variable {is is'}
/-
lemma form₀'_ext₁ (f : Over.mk δ ⟶ op U)
  (hf : (U.isoIsPullback is).hom ≫ (U.pullback_map.map f).left ≫ gen₂_hom U = δ'):
    f = form₀' is is' := by
  apply Pi.form₀'_ext₁
  simp only [prod.lift_fst, ← hf, Iso.inv_hom_id_assoc, Category.assoc]
-/

lemma form₀'_ext (f : Over.mk δ ⟶ op U)
  (hf : (is.flip.liftIsPullbackAlong' (U.isPullback (hom U)).flip f).left ≫ gen₂_hom U = δ') :
    f = form₀' is is' := by
  simp [form₀']
  apply_fun (IsPullback.adjEquiv is.flip U.proj₂').symm
  rw [Equiv.symm_apply_apply, ← Category.comp_id f,
      ← IsPullback.adjEquiv_naturality_symm_left (U.isPullback _).flip]
  ext; apply Limits.prod.hom_ext
  . simpa using hf
  . /-have : (U.pullback_map.map f).left ≫ (gen₂_hom₀ U).left ≫ prod.snd = U.fst δ := by
      simp only [pullback_map.map_left_eq_lift, gen₂_hom₀_comp_prod_snd,
        Over.mk_hom, IsPullback.lift_fst]
    simp; conv_rhs => rw [← this]
    simp-/
    simp; erw [gen₂_hom₀_comp_prod_snd, IsPullback.liftIsPullbackAlong_snd]

/-
lemma form₀_ext₁ (f : Γ ⟶ obj U)
  (hf₁ : f ≫ hom U = δ) (hf₂ : (U.isoIsPullback is).hom ≫
    (U.pullback_map.map (Over.homMk f hf₁ : Over.mk δ ⟶ op U)).left ≫ gen₂_hom U = δ') :
    f = form₀ is is' := by
  change (Over.homMk f hf₁ : Over.mk δ ⟶ op U).left = (form₀' is is').left
  rw [form₀'_ext₁ _ hf₂]
-/

lemma form₀_ext (f : Γ ⟶ obj U)
  (hf₁ : f ≫ hom U = δ) (hf₂ : (is.flip.liftIsPullbackAlong' (U.isPullback (hom U)).flip
    (Over.homMk f hf₁ : Over.mk δ ⟶ op U)).left ≫ gen₂_hom U = δ') :
    f = form₀ is is' := by
  change (Over.homMk f hf₁ : Over.mk δ ⟶ op U).left = (form₀' is is').left
  rw [form₀'_ext _ hf₂]

end
end Pi
end
/-
abbrev Sigma_object := (Π(U.map)).obj (Over.mk (Proj₂ U))

abbrev Sigma_objectProj : (Pi_object U).left ⟶ U.obj := (Pi_object U).hom

abbrev Sigma_AGen : C := U.pb (Pi_object U).hom

abbrev Sigma_AGenVMap : Sigma_AGen U ⟶ (Pi_object U).left := U.pb_vmap (Pi_object U).hom

abbrev Sigma_BGen : C := U.pb (Sigma_AGenVMap U ≫ Sigma_objectProj U)

abbrev Sigma_BGenVMap : Sigma_BGen U ⟶ Sigma_AGen U := U.pb_vmap (Sigma_AGenVMap U ≫ Sigma_objectProj U)

structure Sigma_structure where
  map : (Sigma_object U).left ⟶ U.obj
  eq : (Σ(Pi_AGenVMap U)).obj (Over.mk (Pi_BGenVMap U)) ≅ Over.mk (U.pb_vmap map)

abbrev Id_object : C := U.pb U.map

abbrev Id_map : Id_object U ⟶ U.obj := U.pb_vmap U.map ≫ U.map

abbrev Id_diag : U.obj' ⟶ Id_object U := Limits.PullbackCone.IsLimit.lift (U.is_pullback) (𝟙 U.obj') (𝟙 U.obj') rfl

structure Id_structure where
  map : Id_object U ⟶ U.obj
  refl : U.obj' ⟶ U.pb (Id_map U)
  comm : refl ≫ U.pb_vmap (Id_map U) = Id_diag U


variable (map : prod U.obj U.obj ⟶ U.obj)

-- not sure about `HasBinaryCoproducts C` or `HasBinaryCoproduct xxx yyy`
abbrev CoprodProj [HasBinaryCoproducts C] : C := coprod (U.pb <| @prod.fst _ _ U.obj U.obj _) (U.pb <| @prod.snd _ _ U.obj U.obj _)

abbrev CoprojProjMap [HasBinaryCoproducts C] : CoprodProj U ⟶ prod U.obj U.obj :=  coprod.desc (U.pb_vmap _) (U.pb_vmap _)

structure Coproduct_structure [HasBinaryCoproducts C] where
  map : prod U.obj U.obj ⟶ U.obj
  eq :  CategoryTheory.Over.mk (CoprojProjMap U) ≅ Over.mk (U.pb_vmap map)

-- 1. a chosen initial or 2. initial as an extra property?
structure Zero_structure where
  map : t ⟶ U.obj
  eq : IsInitial (U.pb map : C)

structure Unit_structure where
  map : t ⟶ U.obj
  eq : IsTerminal (U.pb map : C)

-- internal universe
structure InternalUniverse where
  op : t ⟶ U.obj
  map : U.pb op ⟶ U.obj

def ofInternalUniverse {U} (I : @InternalUniverse C _ t U) : Universe C where
  obj := U.pb I.uni
  obj' := U.pb I.map
  map := U.pb_vmap I.map
  pb f := U.pb (f ≫ I.map)
  pb_vmap f := U.pb_vmap (f ≫ I.map)
  pb_hmap f := Limits.PullbackCone.IsLimit.lift U.is_pullback (U.pb_vmap (f ≫ I.map) ≫ f) (U.pb_hmap (f ≫ I.map)) (by rw [← U.comm]; simp)
  comm {X} {f} := by
    simp
    have : U.pb_vmap I.map = PullbackCone.fst (PullbackCone.mk (U.pb_vmap I.map) (U.pb_hmap I.map) (by rw [← U.comm])) := rfl
    simp_rw [this, PullbackCone.IsLimit.lift_fst]
    -- exact (@PullbackCone.IsLimit.lift_fst _ _ _ _ _ _ _ (PullbackCone.mk (U.pb_vmap I.map) (U.pb_hmap I.map) U.comm) U.is_pullback _ (U.pb_vmap (f ≫ I.map) ≫ f) (U.pb_hmap (f ≫ I.map)) (by rw [← U.comm]; simp)).symm
  is_pullback {X} {f} := by
    apply CategoryTheory.Limits.leftSquareIsPullback (Limits.PullbackCone.IsLimit.lift U.is_pullback (U.pb_vmap (f ≫ I.map) ≫ f) (U.pb_hmap (f ≫ I.map)) (by rw [← U.comm]; simp)) (U.pb_hmap I.map) f I.map (U.pb_vmap (f ≫ I.map)) (U.pb_vmap I.map) U.map _ U.comm U.is_pullback
    have : U.pb_hmap (f ≫ I.map) = PullbackCone.IsLimit.lift U.is_pullback (U.pb_vmap (f ≫ I.map) ≫ f) (U.pb_hmap (f ≫ I.map)) (by rw [← U.comm]; simp) ≫ U.pb_hmap I.map := by
      have : U.pb_hmap I.map = PullbackCone.snd (PullbackCone.mk (U.pb_vmap I.map) (U.pb_hmap I.map) (by rw [← U.comm])) := rfl
      simp_rw [this, PullbackCone.IsLimit.lift_snd]
    simp_rw [← this]
    apply U.is_pullback

namespace InternalUniverse

variable (I : @InternalUniverse C _ t U)

structure ClosedUnderPi (U_Pi : Pi_structure U) where
  Pi : Pi_structure (ofInternalUniverse I)
  comm : Pi.map ≫ I.map = Pi.map ≫ I.map -- don't know how to construt the functoriality mathematically...

end InternalUniverse

end Universe
-/

namespace Empty

variable [HasTerminal C]

-- 1. a chosen initial or 2. initial as an extra property?
structure Structure where
  map : ⊤_ C ⟶ U.down
  is_initial : IsInitial (Over.mk (U.snd map))

end Empty

namespace Unit

variable [HasTerminal C]

-- 1. a chosen initial or 2. initial as an extra property?
structure Structure where
  map : ⊤_ C ⟶ U.down
  iso : U.snd' map ≅ Over.mk (𝟙 _)

end Unit
