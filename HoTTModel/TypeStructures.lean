import HoTTModel.LocallyCartesionClosed
import HoTTModel.Universe
import HoTTModel.Lemmas.Limits

noncomputable section

open CategoryTheory Limits List ContextualCategory LocallyCartesianClosed

variable {C : Type u} [CategoryTheory.Category.{v, u} C] [HasPullbacks C] [LocallyCartesianClosed C] [HasBinaryProducts C] {t : C} (ht : IsTerminal t)

-- binary product follows from pullback + terminal object, but I'll assume this instance for now

namespace Universe

variable (U : Universe C)

namespace Pi

abbrev Op := (Π(U.map)).obj (CategoryTheory.Over.mk U.Proj₂)

abbrev Obj := (Op U).left

abbrev Hom : Obj U ⟶ U.obj := (Op U).hom

abbrev AGen : C := U.pt (Op U).hom

abbrev AGenFst : AGen U ⟶ U.obj' := U.fst (Hom U)

abbrev AGenSnd : AGen U ⟶ Obj U := U.snd (Hom U)

abbrev BGenHom : AGen U ⟶ U.obj := ((LocallyCartesianClosed.isLimit_equiv (U.pullback (Hom U)).flip (Over.mk U.Proj₂)).invFun (𝟙 _)).left ≫ U.Proj₁

abbrev BGen : C := U.pt (BGenHom U)

abbrev BGenFst : BGen U ⟶ U.obj' := U.fst (BGenHom U)

abbrev BGenSnd : BGen U ⟶ AGen U := U.snd (BGenHom U)

structure Structure where
  map : (Op U).left ⟶ U.obj
  Eq : (Π(AGenSnd U)).obj (Over.mk (BGenSnd U)) ≅ Over.mk (U.snd map)

-- want to prove def 1.4.1 KLV
-- for the symbols below, see a scipt paper with `TTPI` in right upper corner
variable {U : Universe C} {Γ A B : C}
{f : Γ ⟶ U.obj} {g : A ⟶ U.obj'} {h : A ⟶ Γ} (pb : IsPullback g h U.map f)
{f' : A ⟶ U.obj} {g' : B ⟶ U.obj'} {h' : B ⟶ A} (is' : IsPullback g' h' U.map f')

def ind_f' (f' : A ⟶ U.obj) : Over.mk f ⟶ Op U := (LocallyCartesianClosed.isLimit_equiv pb.flip (Over.mk U.Proj₂)).toFun <| Over.homMk (U := Over.mk g) (V := Over.mk U.Proj₂) (prod.lift f' g) (by simp)

def ind_f (f' : A ⟶ U.obj) : Γ ⟶ Obj U := (ind_f' pb f').left

-- better write a lift for all pullback, edit aux2 and isLimit_equiv in the other file

abbrev aux {X Y Z Z' W W': C} {f : X ⟶ Y}  {g : Z ⟶ Y} {g' : Z' ⟶ Y}
{u : W ⟶ Z} {u' : W' ⟶ Z'} {v : W ⟶ X} {v' : W' ⟶ X}
(pb : IsPullback u v g f) (pb' : IsPullback u' v' g' f)
(i : Over.mk g ⟶ Over.mk g') : W ⟶ W' := PullbackCone.IsLimit.lift pb'.isLimit (u ≫ i.left) v (by simp [← pb.w]; congr; exact Over.w i)

abbrev aux_fst {X Y Z Z' W W': C} {f : X ⟶ Y}  {g : Z ⟶ Y} {g' : Z' ⟶ Y}
{u : W ⟶ Z} {u' : W' ⟶ Z'} {v : W ⟶ X} {v' : W' ⟶ X}
(pb : IsPullback u v g f) (pb' : IsPullback u' v' g' f)
(i : Over.mk g ⟶ Over.mk g') : (aux pb pb' i) ≫ u' = u ≫ i.left := CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst _ _ _ _

abbrev aux_snd {X Y Z Z' W W': C} {f : X ⟶ Y}  {g : Z ⟶ Y} {g' : Z' ⟶ Y}
{u : W ⟶ Z} {u' : W' ⟶ Z'} {v : W ⟶ X} {v' : W' ⟶ X}
(pb : IsPullback u v g f) (pb' : IsPullback u' v' g' f)
(i : Over.mk g ⟶ Over.mk g') : (aux pb pb' i) ≫ v' = v := CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd _ _ _ _

-- several comm condition on aux

def ind_g (f' : A ⟶ U.obj) : A ⟶ AGen U := aux pb.flip (U.pullback (Hom U)).flip (ind_f' pb f')

lemma ind_comm' (f' : A ⟶ U.obj) : (ind_g pb f') ≫ AGenSnd U = h ≫ (ind_f pb f') := aux_fst pb.flip _ _

lemma eq_g : (ind_g pb f') ≫ AGenFst U = g := aux_snd pb.flip _ _

lemma eq_f : (ind_f pb f') ≫ Hom U = f := by simp [ind_f]

def Limits.leftSquareIsPullback' {C : Type u} [Category.{v, u} C] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
  (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (i₃ : X₃ ⟶ Y₃)
  (h₁ : f₁ ≫ i₂ = i₁ ≫ g₁) (h₂ : f₂ ≫ i₃ = i₂ ≫ g₂) (H : IsLimit (PullbackCone.mk f₂ i₂ h₂))
  (H' : IsLimit (PullbackCone.mk (f₁ ≫ f₂) i₁ (show (f₁ ≫ f₂) ≫ i₃ = i₁ ≫ g₁ ≫ g₂  by
            rw [← Category.assoc, ← h₁, Category.assoc, h₂, Category.assoc]))) : IsLimit (PullbackCone.mk f₁ i₁ h₁) := by
  apply PullbackCone.isLimitOfFlip
  apply leftSquareIsPullback f₁ f₂ g₁ g₂ i₁ i₂ i₃ h₁.symm h₂.symm
  apply PullbackCone.isLimitOfFlip
  apply H
  apply PullbackCone.isLimitOfFlip
  apply H'

abbrev aux2 {X Y Z W : C} {f f' : X ⟶ Y}  {g g': Z ⟶ Y} {fst fst' : W ⟶ X} {snd snd' : W ⟶ Z}
(comm : fst ≫ f = snd ≫ g) (h : IsLimit <| PullbackCone.mk _ _ comm) (h₁ : f' = f) (h₂ : g' = g)
(h₃ : fst' = fst) (h₄ : snd' = snd) : IsLimit <| PullbackCone.mk _ _ (show (fst' ≫ f' = snd' ≫ g') by rw [h₁, h₂, h₃, h₄, comm]) := by
  convert h

def ispb : IsLimit <| PullbackCone.mk _ _ (ind_comm' pb f') := by
  apply Limits.leftSquareIsPullback' (ind_g pb f') (AGenFst U) (ind_f pb f') (Hom U) h (AGenSnd U) U.map _ _ _ _
  apply (U.pullback _).w
  apply (U.pullback _).isLimit
  simp_rw [eq_g]
  apply aux2 pb.w pb.isLimit rfl (eq_f _) rfl rfl
  -- covert does not work here, it worked before though

#check (IsPullback.Iso_of_pullback pb).hom ≫ ind_g pb f'
#check (IsPullback.Iso_of_pullback (U.pullback (Hom U))).inv
#check ((U.map*).map (ind_f' pb f')).left
#simp => ((U.map*).obj (CategoryTheory.Over.mk f)).left ⟶ ((U.map*).obj (Op U)).left
#check (IsPullback.Iso_of_pullback pb.flip).hom ≫ ind_g pb f' ≫ (IsPullback.Iso_of_pullback (U.pullback (Hom U)).flip).inv


-- proved!!!!
lemma auxxx : ind_g pb f' = (IsPullback.Iso_of_pullback pb.flip).inv ≫ ((U.map*).map (ind_f' pb f')).left ≫ (IsPullback.Iso_of_pullback (U.pullback (Hom U)).flip).hom := by
  dsimp [ind_g, aux]
  symm
  have := h ≫ (ind_f' pb f').left
  apply Limits.PullbackCone.IsLimit.lift_eq (U.pullback (Hom U)).flip.isLimit (h ≫ (ind_f' pb f').left) g ?_ ((IsPullback.Iso_of_pullback pb.flip).inv ≫ ((U.map*).map (ind_f' pb f')).left ≫ (IsPullback.Iso_of_pullback (U.pullback (Hom U)).flip).hom) ?_ ?_
  simp [pb.w]
  rw [Category.assoc, Iso.inv_comp_eq, ← Category.assoc _ h, IsPullback.Iso_of_pullback_hom_fst]
  rw [Category.assoc]
  simp
  simp only [IsPullback.Iso_of_pullback_hom_fst, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
  simp
  rw [IsPullback.Iso_of_pullback_hom_snd]
  simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.comp_id]
  rw [IsPullback.Iso_of_pullback_inv_snd]


#check (IsPullback.Iso_of_pullback pb).hom ≫ prod.lift f' g
#check ((U.map*).map (ind_f' pb f') ≫ (adj U.map).counit.app (CategoryTheory.Over.mk U.Proj₂)).left
#simp => ((U.map*).obj (CategoryTheory.Over.mk f)).left ⟶
  ((𝟭 (CategoryTheory.Over U.obj')).obj (CategoryTheory.Over.mk U.Proj₂)).left

lemma llala : ((U.map*).map (ind_f' pb f') ≫ (adj U.map).counit.app (CategoryTheory.Over.mk U.Proj₂)).left = (IsPullback.Iso_of_pullback pb.flip).hom ≫ prod.lift f' g := by
  rw [← Adjunction.homEquiv_counit]
  dsimp [ind_f', isLimit_equiv]
  simp

-- for the proof find TTP2
lemma aaa : ind_g pb f' ≫ ((isLimit_equiv (U.pullback (Hom U)).flip (Over.mk <| U.Proj₂)).invFun (𝟙 _)).left = prod.lift f' g := by
  simp [isLimit_equiv]
  simp only [auxxx, Category.assoc, Iso.hom_inv_id_assoc, ← Over.comp_left, llala, prod.comp_lift, Iso.inv_hom_id_assoc]

example : ind_g pb f' ≫ (BGenHom U) = f' := by
  simp only [BGenHom, ← Category.assoc, aaa, limit.lift_π, BinaryFan.mk_fst]


-- solve the hardest part....
-- maybe should work in Over throughout...

end Pi




#exit
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
  Op : t ⟶ U.obj
  map : U.pb Op ⟶ U.obj

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
