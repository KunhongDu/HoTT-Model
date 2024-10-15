/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Yoneda
-- Copied from https://github.com/leanprover-community/mathlib4/blob/9d4865df7a1250d29103d7b552678999859afaa6/Mathlib/CategoryTheory/Yoneda.lean#L157-L161

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

universe v v₁ u₁ u₂

open Opposite

namespace Functor

/-- The data which expresses that a functor `F : Cᵒᵖ ⥤ Type v` is representable by `Y : C`. -/
structure RepresentableBy (F : Cᵒᵖ ⥤ Type v) (Y : C) where
  /-- the natural bijection `(X ⟶ Y) ≃ F.obj (op X)`. -/
  homEquiv {X : C} : (X ⟶ Y) ≃ F.obj (op X)
  homEquiv_comp {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y) :
    homEquiv (f ≫ g) = F.map f.op (homEquiv g)

/-- If `F ≅ F'`, and `F` is representable, then `F'` is representable. -/
def RepresentableBy.ofIso {F F' : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y) (e' : F ≅ F') :
    F'.RepresentableBy Y where
  homEquiv {X} := e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {X X'} f g := by
    dsimp
    rw [e.homEquiv_comp]
    apply congr_fun (e'.hom.naturality f.op)

/-- The data which expresses that a functor `F : C ⥤ Type v` is corepresentable by `X : C`. -/
structure CorepresentableBy (F : C ⥤ Type v) (X : C) where
  /-- the natural bijection `(X ⟶ Y) ≃ F.obj Y`. -/
  homEquiv {Y : C} : (X ⟶ Y) ≃ F.obj Y
  homEquiv_comp {Y Y' : C} (g : Y ⟶ Y') (f : X ⟶ Y) :
    homEquiv (f ≫ g) = F.map g (homEquiv f)

/-- If `F ≅ F'`, and `F` is corepresentable, then `F'` is corepresentable. -/
def CorepresentableBy.ofIso {F F' : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X)
    (e' : F ≅ F') :
    F'.CorepresentableBy X where
  homEquiv {X} := e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {Y Y'} g f := by
    dsimp
    rw [e.homEquiv_comp]
    apply congr_fun (e'.hom.naturality g)

lemma RepresentableBy.homEquiv_eq {F : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y)
    {X : C} (f : X ⟶ Y) :
    e.homEquiv f = F.map f.op (e.homEquiv (𝟙 Y)) := by
  conv_lhs => rw [← Category.comp_id f, e.homEquiv_comp]

lemma CorepresentableBy.homEquiv_eq {F : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X)
    {Y : C} (f : X ⟶ Y) :
    e.homEquiv f = F.map f (e.homEquiv (𝟙 X)) := by
  conv_lhs => rw [← Category.id_comp f, e.homEquiv_comp]

@[ext]
lemma RepresentableBy.ext {F : Cᵒᵖ ⥤ Type v} {Y : C} {e e' : F.RepresentableBy Y}
    (h : e.homEquiv (𝟙 Y) = e'.homEquiv (𝟙 Y)) : e = e' := by
  have : ∀ {X : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f ↦ by
    rw [e.homEquiv_eq, e'.homEquiv_eq, h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

@[ext]
lemma CorepresentableBy.ext {F : C ⥤ Type v} {X : C} {e e' : F.CorepresentableBy X}
    (h : e.homEquiv (𝟙 X) = e'.homEquiv (𝟙 X)) : e = e' := by
  have : ∀ {Y : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f ↦ by
    rw [e.homEquiv_eq, e'.homEquiv_eq, h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

/-- The obvious bijection `F.RepresentableBy Y ≃ (yoneda.obj Y ≅ F)`
when `F : Cᵒᵖ ⥤ Type v₁` and `[Category.{v₁} C]`. -/
def representableByEquiv {F : Cᵒᵖ ⥤ Type v₁} {Y : C} :
    F.RepresentableBy Y ≃ (yoneda.obj Y ≅ F) where
  toFun r := NatIso.ofComponents (fun _ ↦ r.homEquiv.toIso) (fun {X X'} f ↦ by
    ext g
    simp [r.homEquiv_comp])
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g ↦ congr_fun (e.hom.naturality f.op) g }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The isomorphism `yoneda.obj Y ≅ F` induced by `e : F.RepresentableBy Y`. -/
def RepresentableBy.toIso {F : Cᵒᵖ ⥤ Type v₁} {Y : C} (e : F.RepresentableBy Y) :
    yoneda.obj Y ≅ F :=
  representableByEquiv e

/-- The obvious bijection `F.CorepresentableBy X ≃ (yoneda.obj Y ≅ F)`
when `F : C ⥤ Type v₁` and `[Category.{v₁} C]`. -/
def corepresentableByEquiv {F : C ⥤ Type v₁} {X : C} :
    F.CorepresentableBy X ≃ (coyoneda.obj (op X) ≅ F) where
  toFun r := NatIso.ofComponents (fun _ ↦ r.homEquiv.toIso) (fun {X X'} f ↦ by
    ext g
    simp [r.homEquiv_comp])
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g ↦ congr_fun (e.hom.naturality f) g }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The isomorphism `coyoneda.obj (op X) ≅ F` induced by `e : F.CorepresentableBy X`. -/
def CorepresentableBy.toIso {F : C ⥤ Type v₁} {X : C} (e : F.CorepresentableBy X) :
    coyoneda.obj (op X) ≅ F :=
  corepresentableByEquiv e

/-- A functor `F : Cᵒᵖ ⥤ Type v` is representable if there is oan bject `Y` with a structure
`F.RepresentableBy Y`, i.e. there is a natural bijection `(X ⟶ Y) ≃ F.obj (op X)`,
which may also be rephrased as a natural isomorphism `yoneda.obj X ≅ F` when `Category.{v} C`.

See <https://stacks.math.columbia.edu/tag/001Q>.
-/
class IsRepresentable (F : Cᵒᵖ ⥤ Type v) : Prop where
  has_representation : ∃ (Y : C), Nonempty (F.RepresentableBy Y)

-- @[deprecated (since := "2024-10-03")] alias Representable := IsRepresentable

lemma RepresentableBy.isRepresentable {F : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y) :
    F.IsRepresentable where
  has_representation := ⟨Y, ⟨e⟩⟩

/-- Alternative constructure for `F.IsRepresentable`, which takes as an input an
isomorphism `yoneda.obj X ≅ F`. -/
lemma IsRepresentable.mk' {F : Cᵒᵖ ⥤ Type v₁} {X : C} (e : yoneda.obj X ≅ F) :
    F.IsRepresentable :=
  (representableByEquiv.symm e).isRepresentable

instance {X : C} : IsRepresentable (yoneda.obj X) :=
  IsRepresentable.mk' (Iso.refl _)

/-- A functor `F : C ⥤ Type v₁` is corepresentable if there is object `X` so `F ≅ coyoneda.obj X`.

See <https://stacks.math.columbia.edu/tag/001Q>.
-/
class IsCorepresentable (F : C ⥤ Type v) : Prop where
  has_corepresentation : ∃ (X : C), Nonempty (F.CorepresentableBy X)

-- @[deprecated (since := "2024-10-03")] alias Corepresentable := IsCorepresentable

lemma CorepresentableBy.isCorepresentable {F : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X) :
    F.IsCorepresentable where
  has_corepresentation := ⟨X, ⟨e⟩⟩

/-- Alternative constructure for `F.IsCorepresentable`, which takes as an input an
isomorphism `coyoneda.obj (op X) ≅ F`. -/
lemma IsCorepresentable.mk' {F : C ⥤ Type v₁} {X : C} (e : coyoneda.obj (op X) ≅ F) :
    F.IsCorepresentable :=
  (corepresentableByEquiv.symm e).isCorepresentable

instance {X : Cᵒᵖ} : IsCorepresentable (coyoneda.obj X) :=
  IsCorepresentable.mk' (Iso.refl _)

-- the following already exists
/-
-- instance : corepresentable (𝟭 (Type v₁)) :=
-- corepresentable_of_nat_iso (op punit) coyoneda.punit_iso
section Representable

variable (F : Cᵒᵖ ⥤ Type v) [hF : F.IsRepresentable]

/-- The representing object for the representable functor `F`. -/
noncomputable def reprX : C :=
  hF.has_representation.choose

/-- A chosen term in `F.RepresentableBy (reprX F)` when `F.IsRepresentable` holds. -/
noncomputable def representableBy : F.RepresentableBy F.reprX :=
  hF.has_representation.choose_spec.some

/-- The representing element for the representable functor `F`, sometimes called the universal
element of the functor.
-/
noncomputable def reprx : F.obj (op F.reprX) :=
  F.representableBy.homEquiv (𝟙 _)

/-- An isomorphism between a representable `F` and a functor of the
form `C(-, F.reprX)`.  Note the components `F.reprW.app X`
definitionally have type `(X.unop ⟶ F.reprX) ≅ F.obj X`.
-/
noncomputable def reprW (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable] :
    yoneda.obj F.reprX ≅ F := F.representableBy.toIso

theorem reprW_hom_app (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable]
    (X : Cᵒᵖ) (f : unop X ⟶ F.reprX) :
    F.reprW.hom.app X f = F.map f.op F.reprx := by
  apply RepresentableBy.homEquiv_eq

end Representable

section Corepresentable

variable (F : C ⥤ Type v) [hF : F.IsCorepresentable]

/-- The representing object for the corepresentable functor `F`. -/
noncomputable def coreprX : C :=
  hF.has_corepresentation.choose

/-- A chosen term in `F.CorepresentableBy (coreprX F)` when `F.IsCorepresentable` holds. -/
noncomputable def corepresentableBy : F.CorepresentableBy F.coreprX :=
  hF.has_corepresentation.choose_spec.some

/-- The representing element for the corepresentable functor `F`, sometimes called the universal
element of the functor.
-/
noncomputable def coreprx : F.obj F.coreprX :=
  F.corepresentableBy.homEquiv (𝟙 _)

/-- An isomorphism between a corepresentable `F` and a functor of the form
`C(F.corepr X, -)`. Note the components `F.coreprW.app X`
definitionally have type `F.corepr_X ⟶ X ≅ F.obj X`.
-/
noncomputable def coreprW (F : C ⥤ Type v₁) [F.IsCorepresentable] :
    coyoneda.obj (op F.coreprX) ≅ F :=
  F.corepresentableBy.toIso

theorem coreprW_hom_app (F : C ⥤ Type v₁) [F.IsCorepresentable] (X : C) (f : F.coreprX ⟶ X) :
    F.coreprW.hom.app X f = F.map f F.coreprx := by
  apply CorepresentableBy.homEquiv_eq

end Corepresentable

end Functor

theorem isRepresentable_of_natIso (F : Cᵒᵖ ⥤ Type v₁) {G} (i : F ≅ G) [F.IsRepresentable] :
    G.IsRepresentable :=
  (F.representableBy.ofIso i).isRepresentable

theorem corepresentable_of_natIso (F : C ⥤ Type v₁) {G} (i : F ≅ G) [F.IsCorepresentable] :
    G.IsCorepresentable :=
  (F.corepresentableBy.ofIso i).isCorepresentable

instance : Functor.IsCorepresentable (𝟭 (Type v₁)) :=
  corepresentable_of_natIso (coyoneda.obj (op PUnit)) Coyoneda.punitIso

open Opposite

variable (C)

-- We need to help typeclass inference with some awkward universe levels here.
instance prodCategoryInstance1 : Category ((Cᵒᵖ ⥤ Type v₁) × Cᵒᵖ) :=
  CategoryTheory.prod.{max u₁ v₁, v₁} (Cᵒᵖ ⥤ Type v₁) Cᵒᵖ

instance prodCategoryInstance2 : Category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) :=
  CategoryTheory.prod.{v₁, max u₁ v₁} Cᵒᵖ (Cᵒᵖ ⥤ Type v₁)

open Yoneda

section YonedaLemma

variable {C}

/-- We have a type-level equivalence between natural transformations from the yoneda embedding
and elements of `F.obj X`, without any universe switching.
-/
def yonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type v₁} : (yoneda.obj X ⟶ F) ≃ F.obj (op X) where
  toFun η := η.app (op X) (𝟙 X)
  invFun ξ := { app := fun _ f ↦ F.map f.op ξ }
  left_inv := by
    intro η
    ext Y f
    dsimp
    rw [← FunctorToTypes.naturality]
    simp
  right_inv := by intro ξ; simp

theorem yonedaEquiv_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) :
    yonedaEquiv f = f.app (op X) (𝟙 X) :=
  rfl

@[simp]
theorem yonedaEquiv_symm_app_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) : (yonedaEquiv.symm x).app Y f = F.map f.op x :=
  rfl

/-- See also `yonedaEquiv_naturality'` for a more general version. -/
lemma yonedaEquiv_naturality {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.map g.op (yonedaEquiv f) = yonedaEquiv (yoneda.map g ≫ f) := by
  change (f.app (op X) ≫ F.map g.op) (𝟙 X) = f.app (op Y) (𝟙 Y ≫ g)
  rw [← f.naturality]
  dsimp
  simp

/-- Variant of `yonedaEquiv_naturality` with general `g`. This is technically strictly more general
    than `yonedaEquiv_naturality`, but `yonedaEquiv_naturality` is sometimes preferable because it
    can avoid the "motive is not type correct" error. -/
lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.map g (yonedaEquiv f) = yonedaEquiv (yoneda.map g.unop ≫ f) :=
  yonedaEquiv_naturality _ _

lemma yonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ Type v₁} (α : yoneda.obj X ⟶ F) (β : F ⟶ G) :
    yonedaEquiv (α ≫ β) = β.app _ (yonedaEquiv α) :=
  rfl

lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : yonedaEquiv (yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

/-- See also `map_yonedaEquiv'` for a more general version. -/
lemma map_yonedaEquiv {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.map g.op (yonedaEquiv f) = f.app (op Y) g := by
  rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- Variant of `map_yonedaEquiv` with general `g`. This is technically strictly more general
    than `map_yonedaEquiv`, but `map_yonedaEquiv` is sometimes preferable because it
    can avoid the "motive is not type correct" error. -/
lemma map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.map g (yonedaEquiv f) = f.app Y g.unop := by
  rw [yonedaEquiv_naturality', yonedaEquiv_comp, yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type v₁} (t : F.obj X) :
    yonedaEquiv.symm (F.map f t) = yoneda.map f.unop ≫ yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `yoneda.obj X ⟶ P` agree. -/
lemma hom_ext_yoneda {P Q : Cᵒᵖ ⥤ Type v₁} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (yonedaEquiv) (h _ (yonedaEquiv.symm x))

variable (C)

/-- The "Yoneda evaluation" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
def yonedaEvaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  evaluationUncurried Cᵒᵖ (Type v₁) ⋙ uliftFunctor

@[simp]
theorem yonedaEvaluation_map_down (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (yonedaEvaluation C).obj P) :
    ((yonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

/-- The "Yoneda pairing" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `yoneda.op.obj X ⟶ F`, functorially in both `X` and `F`.
-/
def yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  Functor.prod yoneda.op (𝟭 (Cᵒᵖ ⥤ Type v₁)) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)

-- Porting note (#5229): we need to provide this `@[ext]` lemma separately,
-- as `ext` will not look through the definition.
@[ext]
lemma yonedaPairingExt {X : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)} {x y : (yonedaPairing C).obj X}
    (w : ∀ Y, x.app Y = y.app Y) : x = y :=
  NatTrans.ext (funext w)

@[simp]
theorem yonedaPairing_map (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (β : (yonedaPairing C).obj P) :
    (yonedaPairing C).map α β = yoneda.map α.1.unop ≫ β ≫ α.2 :=
  rfl

universe w in
variable {C} in
/-- A bijection `(yoneda.obj X ⋙ uliftFunctor ⟶ F) ≃ F.obj (op X)` which is a variant
of `yonedaEquiv` with heterogeneous universes. -/
def yonedaCompUliftFunctorEquiv (F : Cᵒᵖ ⥤ Type max v₁ w) (X : C) :
    (yoneda.obj X ⋙ uliftFunctor ⟶ F) ≃ F.obj (op X) where
  toFun φ := φ.app (op X) (ULift.up (𝟙 _))
  invFun f :=
    { app := fun _ x => F.map (ULift.down x).op f }
  left_inv φ := by
    ext Y f
    dsimp
    rw [← FunctorToTypes.naturality]
    dsimp
    rw [Category.comp_id]
    rfl
  right_inv f := by aesop_cat

/-- The Yoneda lemma asserts that the Yoneda pairing
`(X : Cᵒᵖ, F : Cᵒᵖ ⥤ Type) ↦ (yoneda.obj (unop X) ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`.

See <https://stacks.math.columbia.edu/tag/001P>.
-/
def yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso (yonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : yoneda.obj X.unop ⟶ F)
        apply ULift.ext
        simp only [Functor.prod_obj, Functor.id_obj, types_comp_apply, yonedaEvaluation_map_down]
        erw [Equiv.ulift_symm_down, Equiv.ulift_symm_down]
        dsimp [yonedaEquiv]
        simp [← FunctorToTypes.naturality])

variable {C}

/- Porting note: this used to be two calls to `tidy` -/
/-- The curried version of yoneda lemma when `C` is small. -/
def curriedYonedaLemma {C : Type u₁} [SmallCategory C] :
    (yoneda.op ⋙ coyoneda : Cᵒᵖ ⥤ (Cᵒᵖ ⥤ Type u₁) ⥤ Type u₁) ≅ evaluation Cᵒᵖ (Type u₁) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso yonedaEquiv)) (by
    intro X Y f
    ext a b
    dsimp [yonedaEquiv]
    simp [← FunctorToTypes.naturality])

/-- The curried version of the Yoneda lemma. -/
def largeCurriedYonedaLemma {C : Type u₁} [Category.{v₁} C] :
    yoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| yonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using yonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (yonedaEquiv_naturality _ _).symm)

/-- Version of the Yoneda lemma where the presheaf is fixed but the argument varies. -/
def yonedaOpCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type v₁) :
    yoneda.op ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁} :=
  isoWhiskerRight largeCurriedYonedaLemma ((evaluation _ _).obj P)

/-- The curried version of yoneda lemma when `C` is small. -/
def curriedYonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft Cᵒᵖ (Cᵒᵖ ⥤ Type u₁)ᵒᵖ (Type u₁)).obj yoneda.op
      ≅ 𝟭 (Cᵒᵖ ⥤ Type u₁) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso yonedaEquiv) (by
    intro X Y f
    ext a
    dsimp [yonedaEquiv]
    simp [← FunctorToTypes.naturality]))

lemma isIso_of_yoneda_map_bijective {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f)) :
    IsIso f := by
  obtain ⟨g, hg : g ≫ f = 𝟙 Y⟩ := (hf Y).2 (𝟙 Y)
  exact ⟨g, (hf _).1 (by aesop_cat), hg⟩

end YonedaLemma

section CoyonedaLemma

variable {C}

/-- We have a type-level equivalence between natural transformations from the coyoneda embedding
and elements of `F.obj X.unop`, without any universe switching.
-/
def coyonedaEquiv {X : C} {F : C ⥤ Type v₁} : (coyoneda.obj (op X) ⟶ F) ≃ F.obj X where
  toFun η := η.app X (𝟙 X)
  invFun ξ := { app := fun _ x ↦ F.map x ξ }
  left_inv := fun η ↦ by
    ext Y (x : X ⟶ Y)
    dsimp
    rw [← FunctorToTypes.naturality]
    simp
  right_inv := by intro ξ; simp

theorem coyonedaEquiv_apply {X : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F) :
    coyonedaEquiv f = f.app X (𝟙 X) :=
  rfl

@[simp]
theorem coyonedaEquiv_symm_app_apply {X : C} {F : C ⥤ Type v₁} (x : F.obj X) (Y : C)
    (f : X ⟶ Y) : (coyonedaEquiv.symm x).app Y f = F.map f x :=
  rfl

lemma coyonedaEquiv_naturality {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
    (g : X ⟶ Y) : F.map g (coyonedaEquiv f) = coyonedaEquiv (coyoneda.map g.op ≫ f) := by
  change (f.app X ≫ F.map g) (𝟙 X) = f.app Y (g ≫ 𝟙 Y)
  rw [← f.naturality]
  dsimp
  simp

lemma coyonedaEquiv_comp {X : C} {F G : C ⥤ Type v₁} (α : coyoneda.obj (op X) ⟶ F) (β : F ⟶ G) :
    coyonedaEquiv (α ≫ β) = β.app _ (coyonedaEquiv α) := by
  rfl

lemma coyonedaEquiv_coyoneda_map {X Y : C} (f : X ⟶ Y) :
    coyonedaEquiv (coyoneda.map f.op) = f := by
  rw [coyonedaEquiv_apply]
  simp

lemma map_coyonedaEquiv {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
    (g : X ⟶ Y) : F.map g (coyonedaEquiv f) = f.app Y g := by
  rw [coyonedaEquiv_naturality, coyonedaEquiv_comp, coyonedaEquiv_coyoneda_map]

lemma coyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type v₁} (t : F.obj X) :
    coyonedaEquiv.symm (F.map f t) = coyoneda.map f.op ≫ coyonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := coyonedaEquiv.surjective t
  simp [coyonedaEquiv_naturality u f]

variable (C)

/-- The "Coyoneda evaluation" functor, which sends `X : C` and `F : C ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
def coyonedaEvaluation : C × (C ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  evaluationUncurried C (Type v₁) ⋙ uliftFunctor

@[simp]
theorem coyonedaEvaluation_map_down (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (coyonedaEvaluation C).obj P) :
    ((coyonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

/-- The "Coyoneda pairing" functor, which sends `X : C` and `F : C ⥤ Type`
to `coyoneda.rightOp.obj X ⟶ F`, functorially in both `X` and `F`.
-/
def coyonedaPairing : C × (C ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  Functor.prod coyoneda.rightOp (𝟭 (C ⥤ Type v₁)) ⋙ Functor.hom (C ⥤ Type v₁)

-- Porting note (#5229): we need to provide this `@[ext]` lemma separately,
-- as `ext` will not look through the definition.
@[ext]
lemma coyonedaPairingExt {X : C × (C ⥤ Type v₁)} {x y : (coyonedaPairing C).obj X}
    (w : ∀ Y, x.app Y = y.app Y) : x = y :=
  NatTrans.ext (funext w)

@[simp]
theorem coyonedaPairing_map (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q) (β : (coyonedaPairing C).obj P) :
    (coyonedaPairing C).map α β = coyoneda.map α.1.op ≫ β ≫ α.2 :=
  rfl

universe w in
variable {C} in
/-- A bijection `(coyoneda.obj X ⋙ uliftFunctor ⟶ F) ≃ F.obj (unop X)` which is a variant
of `coyonedaEquiv` with heterogeneous universes. -/
def coyonedaCompUliftFunctorEquiv (F : C ⥤ Type max v₁ w) (X : Cᵒᵖ) :
    (coyoneda.obj X ⋙ uliftFunctor ⟶ F) ≃ F.obj X.unop where
  toFun φ := φ.app X.unop (ULift.up (𝟙 _))
  invFun f :=
    { app := fun _ x => F.map (ULift.down x) f }
  left_inv φ := by
    ext Y f
    dsimp
    rw [← FunctorToTypes.naturality]
    dsimp
    rw [Category.id_comp]
    rfl
  right_inv f := by aesop_cat

/-- The Coyoneda lemma asserts that the Coyoneda pairing
`(X : C, F : C ⥤ Type) ↦ (coyoneda.obj X ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`.

See <https://stacks.math.columbia.edu/tag/001P>.
-/
def coyonedaLemma : coyonedaPairing C ≅ coyonedaEvaluation C :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso (coyonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : coyoneda.obj (op X) ⟶ F)
        apply ULift.ext
        simp only [Functor.prod_obj, Functor.id_obj, types_comp_apply, coyonedaEvaluation_map_down]
        erw [Equiv.ulift_symm_down, Equiv.ulift_symm_down]
        simp [coyonedaEquiv, ← FunctorToTypes.naturality])

variable {C}

/- Porting note: this used to be two calls to `tidy` -/
/-- The curried version of coyoneda lemma when `C` is small. -/
def curriedCoyonedaLemma {C : Type u₁} [SmallCategory C] :
    coyoneda.rightOp ⋙ coyoneda ≅ evaluation C (Type u₁) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso coyonedaEquiv)) (by
    intro X Y f
    ext a b
    simp [coyonedaEquiv, ← FunctorToTypes.naturality])

/-- The curried version of the Coyoneda lemma. -/
def largeCurriedCoyonedaLemma {C : Type u₁} [Category.{v₁} C] :
    (coyoneda.rightOp ⋙ coyoneda) ≅
      evaluation C (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| coyonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using coyonedaEquiv_comp _ _))
    (by
      intro Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (coyonedaEquiv_naturality _ _).symm)

/-- Version of the Coyoneda lemma where the presheaf is fixed but the argument varies. -/
def coyonedaCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : C ⥤ Type v₁) :
    coyoneda.rightOp ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁} :=
  isoWhiskerRight largeCurriedCoyonedaLemma ((evaluation _ _).obj P)

/-- The curried version of coyoneda lemma when `C` is small. -/
def curriedCoyonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft C (C ⥤ Type u₁)ᵒᵖ (Type u₁)).obj coyoneda.rightOp
      ≅ 𝟭 (C ⥤ Type u₁) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso coyonedaEquiv) (by
    intro X Y f
    ext a
    simp [coyonedaEquiv, ← FunctorToTypes.naturality]))

lemma isIso_of_coyoneda_map_bijective {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (T : C), Function.Bijective (fun (x : Y ⟶ T) => f ≫ x)) :
    IsIso f := by
  obtain ⟨g, hg : f ≫ g = 𝟙 X⟩ := (hf X).2 (𝟙 X)
  refine ⟨g, hg, (hf _).1 ?_⟩
  simp only [Category.comp_id, ← Category.assoc, hg, Category.id_comp]

end CoyonedaLemma

section

variable {C}
variable {D : Type*} [Category.{v₁} D] (F : C ⥤ D)

/-- The natural transformation `yoneda.obj X ⟶ F.op ⋙ yoneda.obj (F.obj X)`
when `F : C ⥤ D` and `X : C`. -/
def yonedaMap (X : C) : yoneda.obj X ⟶ F.op ⋙ yoneda.obj (F.obj X) where
  app _ f := F.map f

@[simp]
lemma yonedaMap_app_apply {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y) :
    (yonedaMap F Y).app X f = F.map f := rfl
-/
end Functor

end CategoryTheory