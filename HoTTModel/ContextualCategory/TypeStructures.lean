import HoTTModel.LocallyCartesianClosed.ChosenPullbacks
import HoTTModel.ContextualCategory.Universe

noncomputable section

open CategoryTheory Limits List LocallyCartesianClosed

variable {C : Type u} [CategoryTheory.Category.{v, u} C]

namespace Universe
variable (U : Universe C)
set_option linter.unusedSectionVars false

section
variable [HasFiniteWidePullbacks C] [LocallyCartesianClosed C] {X : C} (f : X ⟶ U.down)

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

variable {U} {Γ A B : C} {δ : Γ ⟶ U.down} {γ : A ⟶ U.up} {π : A ⟶ Γ}
  {δ' : A ⟶ U.down} {γ' : B ⟶ U.up} {π' : B ⟶ A}
  (is : IsPullback γ π U.hom δ) (is' : IsPullback γ' π' U.hom δ')

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

lemma form₀'_ext (f : Over.mk δ ⟶ op U)
  (hf : (is.flip.liftIsPullbackAlong' (U.isPullback (hom U)).flip f).left ≫ gen₂_hom U = δ') :
    f = form₀' is is' := by
  simp [form₀']
  apply_fun (IsPullback.adjEquiv is.flip U.proj₂').symm
  rw [Equiv.symm_apply_apply, ← Category.comp_id f,
      ← IsPullback.adjEquiv_naturality_symm_left (U.isPullback _).flip]
  ext; apply Limits.prod.hom_ext
  . simpa using hf
  . simp; erw [gen₂_hom₀_comp_prod_snd, IsPullback.liftIsPullbackAlong_snd]

lemma form₀_ext (f : Γ ⟶ obj U)
  (hf₁ : f ≫ hom U = δ) (hf₂ : (is.flip.liftIsPullbackAlong' (U.isPullback (hom U)).flip
    (Over.homMk f hf₁ : Over.mk δ ⟶ op U)).left ≫ gen₂_hom U = δ') :
    f = form₀ is is' := by
  change (Over.homMk f hf₁ : Over.mk δ ⟶ op U).left = (form₀' is is').left
  rw [form₀'_ext _ hf₂]

end
end Pi
end
