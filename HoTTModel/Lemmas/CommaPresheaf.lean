/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.Tactic.CategoryTheory.Elementwise
import HoTTModel.Lemmas.YonedaULift

/-!
This is a almost copy of [Mathlib.CategoryTheory.Comma.Presheaf.Basic]
(https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/Presheaf/Basic.html),
where we replace every `Cᵒᵖ ⥤ Type v` to `Cᵒᵖ ⥤ Type max v w` and corresponding lemmas,
so that it applies to `SSet.{u} = SimplexCategoryᵒᵖ ⥤ Type max 0 u`.

Notice they are not collary of each other, since `ULift.{0,0}` in Lean is not a definitional equality.
The relation is more comparable to lemmas of `Add` and `Mul`.

# Computation of `Over A` for a presheaf `A`

Let `A : Cᵒᵖ ⥤ Type max v w` be a presheaf. In this file, we construct an equivalence
`e : Over A ≌ (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w` and show that there is a quasi-commutative
diagram

```
CostructuredArrow yonedaULift A      ⥤      Over A

                             ⇘           ⥥

                               PSh(CostructuredArrow yonedaULift A)
```

where the top arrow is the forgetful functor forgetting the yonedaULift-costructure, the right arrow is
the aforementioned equivalence and the diagonal arrow is the yonedaULift embedding.

In the notation of Kashiwara-Schapira, the type of the equivalence is written `C^ₐ ≌ Cₐ^`, where
`·ₐ` is `CostructuredArrow` (with the functor `S` being either the identity or the yonedaULift
embedding) and `^` is taking presheaves. The equivalence is a key ingredient in various results in
Kashiwara-Schapira.

The proof is somewhat long and technical, in part due to the construction inherently involving a
sigma type which comes with the usual DTT issues. However, a user of this result should not need
to interact with the actual construction, the mere existence of the equivalence and the commutative
triangle should generally be sufficient.

## Main results
* `overEquivPresheafCostructuredArrow`:
  the equivalence `Over A ≌ (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w`
* `CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow`: the natural isomorphism
  `CostructuredArrow.toOver yonedaULift A ⋙ (overEquivPresheafCostructuredArrow A).functor ≅ yonedaULift`

## Implementation details

The proof needs to introduce "correction terms" in various places in order to overcome DTT issues,
and these need to be canceled against each other when appropriate. It is important to deal with
these in a structured manner, otherwise you get large goals containing many correction terms which
are very tedious to manipulate. We avoid this blowup by carefully controlling which definitions
`(d)simp` is allowed to unfold and stating many lemmas explicitly before they are required. This
leads to manageable goals containing only a small number of correction terms. Generally, we use
the form `F.map (eqToHom _)` for these correction terms and try to push them as far outside as
possible.

## Future work
* If needed, it should be possible to show that the equivalence is natural in `A`.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Lemma 1.4.12

## Tags
presheaf, over category, coyoneda

-/

namespace CategoryTheory.YonedaULift

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type max v w}

namespace OverPresheafAux

attribute [local simp] FunctorToTypes.naturality

/-! ### Construction of the forward functor `Over A ⥤ (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w` -/

/-- Via the yonedaULift lemma, `u : F.obj (op X)` defines a natural transformation `yonedaULift.obj X ⟶ F`
    and via the element `η.app (op X) u` also a morphism `yonedaULift.obj X ⟶ A`. This structure
    witnesses the fact that these morphisms from a commutative triangle with `η : F ⟶ A`, i.e.,
    that `yonedaULift.obj X ⟶ F` lifts to a morphism in `Over A`. -/
structure MakesOverArrow {F : Cᵒᵖ ⥤ Type max v w} (η : F ⟶ A) {X : C} (s : yonedaULift.obj X ⟶ A)
    (u : F.obj (op X)) : Prop where
  app : η.app (op X) u = yonedaULiftEquiv s

namespace MakesOverArrow

/-- "Functoriality" of `MakesOverArrow η s` in `η`. -/
lemma map₁ {F G : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {μ : G ⟶ A} {ε : F ⟶ G}
    (hε : ε ≫ μ = η) {X : C} {s : yonedaULift.obj X ⟶ A} {u : F.obj (op X)}
    (h : MakesOverArrow η s u) : MakesOverArrow μ s (ε.app _ u) :=
  ⟨by rw [← elementwise_of% NatTrans.comp_app ε μ, hε, h.app]⟩

/-- "Functoriality of `MakesOverArrow η s` in `s`. -/
lemma map₂ {F : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
    {s : yonedaULift.obj X ⟶ A} {t : yonedaULift.obj Y ⟶ A} (hst : yonedaULift.map f ≫ t = s)
    {u : F.obj (op Y)} (h : MakesOverArrow η t u) : MakesOverArrow η s (F.map f.op u) :=
  ⟨by rw [elementwise_of% η.naturality, h.app, yonedaULiftEquiv_naturality, hst]⟩

lemma of_arrow {F : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {X : C} {s : yonedaULift.obj X ⟶ A}
    {f : yonedaULift.obj X ⟶ F} (hf : f ≫ η = s) : MakesOverArrow η s (yonedaULiftEquiv f) :=
  ⟨hf ▸ rfl⟩

lemma of_yoneda_arrow {Y : C} {η : yonedaULift.obj Y ⟶ A} {X : C} {s : yonedaULift.obj X ⟶ A} {f : X ⟶ Y}
    (hf : yonedaULift.map f ≫ η = s) : MakesOverArrow η s (ULift.up f) := by
  simpa only [yonedaULiftEquiv_yonedaULift_apply f] using of_arrow hf

end MakesOverArrow

/-- This is equivalent to the type `Over.mk s ⟶ Over.mk η`, but that lives in the wrong universe.
    However, if `F = yonedaULift.obj Y` for some `Y`, then (using that the yonedaULift embedding is fully
    faithful) we get a good statement, see `OverArrow.costructuredArrowIso`. -/
def OverArrows {F : Cᵒᵖ ⥤ Type max v w} (η : F ⟶ A) {X : C} (s : yonedaULift.obj X ⟶ A) : Type max v w :=
  Subtype (MakesOverArrow η s)

namespace OverArrows

/-- Since `OverArrows η s` can be thought of to contain certain morphisms `yonedaULift.obj X ⟶ F`, the
    yonedaULift lemma yields elements `F.obj (op X)`. -/
def val {F : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {X : C} {s : yonedaULift.obj X ⟶ A} :
    OverArrows η s → F.obj (op X) :=
  Subtype.val

@[simp]
lemma val_mk {F : Cᵒᵖ ⥤ Type max v w} (η : F ⟶ A) {X : C} (s : yonedaULift.obj X ⟶ A) (u : F.obj (op X))
    (h : MakesOverArrow η s u) : val ⟨u, h⟩ = u :=
  rfl

@[ext]
lemma ext {F : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {X : C} {s : yonedaULift.obj X ⟶ A}
    {u v : OverArrows η s} : u.val = v.val → u = v :=
  Subtype.ext

/-- The defining property of `OverArrows.val`. -/
lemma app_val {F : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {X : C} {s : yonedaULift.obj X ⟶ A}
    (p : OverArrows η s) : η.app (op X) p.val = yonedaULiftEquiv s :=
  p.prop.app

/-- In the special case `F = yonedaULift.obj Y`, the element `p.val` for `p : OverArrows η s` is itself
    a morphism `X ⟶ Y`. -/
@[simp]
lemma map_val {Y : C} {η : yonedaULift.obj Y ⟶ A} {X : C} {s : yonedaULift.obj X ⟶ A}
    (p : OverArrows η s) : yonedaULift.map (ULift.down p.val) ≫ η = s := by
  rw [← yonedaULiftEquiv.injective.eq_iff, yonedaULiftEquiv_comp, yonedaULiftEquiv_yonedaULift_apply]
  simp only [unop_op]; exact p.app_val

/-- Functoriality of `OverArrows η s` in `η`. -/
def map₁ {F G : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {μ : G ⟶ A} {X : C} {s : yonedaULift.obj X ⟶ A}
    (u : OverArrows η s) (ε : F ⟶ G) (hε : ε ≫ μ = η) : OverArrows μ s :=
  ⟨ε.app _ u.val, MakesOverArrow.map₁ hε u.2⟩

@[simp]
lemma map₁_val {F G : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {μ : G ⟶ A} {X : C}
    (s : yonedaULift.obj X ⟶ A) (u : OverArrows η s) (ε : F ⟶ G) (hε : ε ≫ μ = η) :
    (u.map₁ ε hε).val = ε.app _ u.val :=
  rfl

/-- Functoriality of `OverArrows η s` in `s`. -/
def map₂ {F : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {X Y : C} {s : yonedaULift.obj X ⟶ A}
    {t : yonedaULift.obj Y ⟶ A} (u : OverArrows η t) (f : X ⟶ Y) (hst : yonedaULift.map f ≫ t = s) :
    OverArrows η s :=
  ⟨F.map f.op u.val, MakesOverArrow.map₂ f hst u.2⟩

@[simp]
lemma map₂_val {F : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
    {s : yonedaULift.obj X ⟶ A} {t : yonedaULift.obj Y ⟶ A} (hst : yonedaULift.map f ≫ t = s)
    (u : OverArrows η t) : (u.map₂ f hst).val = F.map f.op u.val :=
  rfl

@[simp]
lemma map₁_map₂ {F G : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
    (hε : ε ≫ μ = η) {X Y : C} {s : yonedaULift.obj X ⟶ A} {t : yonedaULift.obj Y ⟶ A} (f : X ⟶ Y)
    (hf : yonedaULift.map f ≫ t = s) (u : OverArrows η t) :
    (u.map₁ ε hε).map₂ f hf = (u.map₂ f hf).map₁ ε hε :=
  OverArrows.ext <| (elementwise_of% (ε.naturality f.op).symm) u.val

/-- Construct an element of `OverArrows η s` with `F = yonedaULift.obj Y` from a suitable morphism
    `f : X ⟶ Y`. -/
def yonedaArrow {Y : C} {η : yonedaULift.obj Y ⟶ A} {X : C} {s : yonedaULift.obj X ⟶ A} (f : X ⟶ Y)
    (hf : yonedaULift.map f ≫ η = s) : OverArrows η s :=
  ⟨ULift.up f, .of_yoneda_arrow hf⟩

@[simp]
lemma yonedaArrow_val {Y : C} {η : yonedaULift.obj Y ⟶ A} {X : C} {s : yonedaULift.obj X ⟶ A} {f : X ⟶ Y}
    (hf : yonedaULift.map f ≫ η = s) : (yonedaArrow f hf).val = ULift.up f :=
  rfl

/-- If `η` is also `yonedaULift`-costructured, then `OverArrows η s` is just morphisms of costructured
    arrows. -/
def costructuredArrowIso (s t : CostructuredArrow yonedaULift A) :
    OverArrows s.hom t.hom ≅ ULift (t ⟶ s) where
  hom p := ULift.up (CostructuredArrow.homMk p.val.down (by aesop_cat))
  inv f := yonedaArrow f.down.left f.down.w

end OverArrows

/-- This is basically just `yonedaULift.obj η : (Over A)ᵒᵖ ⥤ Type (max u v)` restricted along the
    forgetful functor `CostructuredArrow yonedaULift A ⥤ Over A`, but done in a way that we land in a
    smaller universe. -/
@[simps]
def restrictedYonedaObj {F : Cᵒᵖ ⥤ Type max v w} (η : F ⟶ A) :
    (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w where
  obj s := OverArrows η s.unop.hom
  map f u := u.map₂ f.unop.left f.unop.w

/-- Functoriality of `restrictedYonedaObj η` in `η`. -/
@[simps]
def restrictedYonedaObjMap₁ {F G : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
    (hε : ε ≫ μ = η) : restrictedYonedaObj η ⟶ restrictedYonedaObj μ where
  app _ u := u.map₁ ε hε

/-- This is basically just `yonedaULift : Over A ⥤ (Over A)ᵒᵖ ⥤ Type (max u v)` restricted in the second
    argument along the forgetful functor `CostructuredArrow yonedaULift A ⥤ Over A`, but done in a way
    that we land in a smaller universe.

    This is one direction of the equivalence we're constructing. -/
@[simps]
def restrictedYoneda (A : Cᵒᵖ ⥤ Type max v w) : Over A ⥤ (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w where
  obj η := restrictedYonedaObj η.hom
  map ε := restrictedYonedaObjMap₁ ε.left ε.w

/-- Further restricting the functor
    `restrictedYoneda : Over A ⥤ (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w` along the forgetful
    functor in the first argument recovers the yonedaULift embedding
    `CostructuredArrow yonedaULift A ⥤ (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w`. This basically follows
    from the fact that the yonedaULift embedding on `C` is fully faithful. -/
def toOverYonedaCompRestrictedYoneda (A : Cᵒᵖ ⥤ Type max v w) :
    CostructuredArrow.toOver yonedaULift A ⋙ restrictedYoneda A ≅ yonedaULift :=
  NatIso.ofComponents
    (fun s => NatIso.ofComponents (fun _ => OverArrows.costructuredArrowIso _ _) (by aesop_cat))
    (by aesop_cat)

/-! ### Construction of the backward functor `((CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w) ⥤ Over A` -/

/-- This lemma will be key to establishing good simp normal forms. -/
lemma map_mkPrecomp_eqToHom {F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w} {X Y : C} {f : X ⟶ Y}
    {g g' : yonedaULift.obj Y ⟶ A} (h : g = g') {x : F.obj (op (CostructuredArrow.mk g'))} :
    F.map (CostructuredArrow.mkPrecomp g f).op (F.map (eqToHom (by rw [h])) x) =
      F.map (eqToHom (by rw [h])) (F.map (CostructuredArrow.mkPrecomp g' f).op x) := by
  aesop_cat

attribute [local simp] map_mkPrecomp_eqToHom

/-- To give an object of `Over A`, we will in particular need a presheaf `Cᵒᵖ ⥤ Type max v w`. This is the
    definition of that presheaf on objects.

    We would prefer to think of this sigma type to be indexed by natural transformations
    `yonedaULift.obj X ⟶ A` instead of `A.obj (op X)`. These are equivalent by the yonedaULift lemma, but
    we cannot use the former because that type lives in the wrong universe. Hence, we will provide
    a lot of API that will enable us to pretend that we are really indexing over
    `yonedaULift.obj X ⟶ A`. -/
def YonedaCollection (F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w) (X : C) : Type max v w :=
  Σ s : A.obj (op X), F.obj (op (CostructuredArrow.mk (yonedaULiftEquiv.symm s)))

namespace YonedaCollection

variable {F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w} {X : C}

/-- Given a costructured arrow `s : yonedaULift.obj X ⟶ A` and an element `x : F.obj s`, construct
    an element of `YonedaCollection F X`. -/
def mk (s : yonedaULift.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : YonedaCollection F X :=
  ⟨yonedaULiftEquiv s, F.map (eqToHom <| by rw [Equiv.symm_apply_apply]) x⟩

/-- Access the first component of an element of `YonedaCollection F X`. -/
def fst (p : YonedaCollection F X) : yonedaULift.obj X ⟶ A :=
  yonedaULiftEquiv.symm p.1

/-- Access the second component of an element of `YonedaCollection F X`. -/
def snd (p : YonedaCollection F X) : F.obj (op (CostructuredArrow.mk p.fst)) :=
  p.2

/-- This is a definition because it will be helpful to be able to control precisely when this
    definition is unfolded. -/
def yonedaEquivFst (p : YonedaCollection F X) : A.obj (op X) :=
  yonedaULiftEquiv p.fst

lemma yonedaEquivFst_eq (p : YonedaCollection F X) : p.yonedaEquivFst = yonedaULiftEquiv p.fst :=
  rfl

@[simp]
lemma mk_fst (s : yonedaULift.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : (mk s x).fst = s :=
  Equiv.apply_symm_apply _ _

@[simp]
lemma mk_snd (s : yonedaULift.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) :
    (mk s x).snd = F.map (eqToHom <| by rw [YonedaCollection.mk_fst]) x :=
  rfl

@[ext (iff := false)]
lemma ext {p q : YonedaCollection F X} (h : p.fst = q.fst)
    (h' : F.map (eqToHom <| by rw [h]) q.snd = p.snd) : p = q := by
  rcases p with ⟨p, p'⟩
  rcases q with ⟨q, q'⟩
  obtain rfl : p = q := yonedaULiftEquiv.symm.injective h
  exact Sigma.ext rfl (by simpa [snd] using h'.symm)

/-- Functoriality of `YonedaCollection F X` in `F`. -/
def map₁ {G : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w} (η : F ⟶ G) :
    YonedaCollection F X → YonedaCollection G X :=
  fun p => YonedaCollection.mk p.fst (η.app _ p.snd)

@[simp]
lemma map₁_fst {G : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w} (η : F ⟶ G)
    (p : YonedaCollection F X) : (YonedaCollection.map₁ η p).fst = p.fst := by
  simp [map₁]

@[simp]
lemma map₁_yonedaEquivFst {G : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w} (η : F ⟶ G)
    (p : YonedaCollection F X) :
    (YonedaCollection.map₁ η p).yonedaEquivFst = p.yonedaEquivFst := by
  simp only [YonedaCollection.yonedaEquivFst_eq, map₁_fst]

@[simp]
lemma map₁_snd {G : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w} (η : F ⟶ G)
    (p : YonedaCollection F X) : (YonedaCollection.map₁ η p).snd =
      G.map (eqToHom (by rw [YonedaCollection.map₁_fst])) (η.app _ p.snd) := by
  simp [map₁]

/-- Functoriality of `YonedaCollection F X` in `X`. -/
def map₂ (F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w) {Y : C} (f : X ⟶ Y)
    (p : YonedaCollection F Y) : YonedaCollection F X :=
  YonedaCollection.mk (yonedaULift.map f ≫ p.fst) <| F.map (CostructuredArrow.mkPrecomp p.fst f).op p.snd

@[simp]
lemma map₂_fst {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).fst = yonedaULift.map f ≫ p.fst := by
  simp [map₂]

@[simp]
lemma map₂_yonedaEquivFst {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).yonedaEquivFst = A.map f.op p.yonedaEquivFst := by
  simp only [YonedaCollection.yonedaEquivFst_eq, map₂_fst, yonedaULiftEquiv_naturality]

@[simp]
lemma map₂_snd {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).snd = F.map ((CostructuredArrow.mkPrecomp p.fst f).op ≫
      eqToHom (by rw [YonedaCollection.map₂_fst f])) p.snd := by
  simp [map₂]

attribute [local simp] CostructuredArrow.mkPrecomp_id CostructuredArrow.mkPrecomp_comp

@[simp]
lemma map₁_id : YonedaCollection.map₁ (𝟙 F) (X := X) = id := by
  aesop_cat

@[simp]
lemma map₁_comp {G H : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w} (η : F ⟶ G) (μ : G ⟶ H) :
    YonedaCollection.map₁ (η ≫ μ) (X := X) =
      YonedaCollection.map₁ μ (X := X) ∘ YonedaCollection.map₁ η (X := X) := by
  ext; all_goals simp

@[simp]
lemma map₂_id : YonedaCollection.map₂ F (𝟙 X) = id := by
  ext; all_goals simp

@[simp]
lemma map₂_comp {Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    YonedaCollection.map₂ F (f ≫ g) = YonedaCollection.map₂ F f ∘ YonedaCollection.map₂ F g := by
  ext; all_goals simp

@[simp]
lemma map₁_map₂ {G : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w} (η : F ⟶ G) {Y : C} (f : X ⟶ Y)
    (p : YonedaCollection F Y) :
    YonedaCollection.map₂ G f (YonedaCollection.map₁ η p) =
      YonedaCollection.map₁ η (YonedaCollection.map₂ F f p) := by
  ext; all_goals simp

end YonedaCollection

/-- Given `F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w`, this is the presheaf that is given by
    `YonedaCollection F X` on objects. -/
@[simps]
def yonedaCollectionPresheaf (A : Cᵒᵖ ⥤ Type max v w) (F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w) :
    Cᵒᵖ ⥤ Type max v w where
  obj X := YonedaCollection F X.unop
  map f := YonedaCollection.map₂ F f.unop

/-- Functoriality of `yonedaCollectionPresheaf A F` in `F`. -/
@[simps]
def yonedaCollectionPresheafMap₁ {F G : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w} (η : F ⟶ G) :
    yonedaCollectionPresheaf A F ⟶ yonedaCollectionPresheaf A G where
  app _ := YonedaCollection.map₁ η
  naturality := by
    intros
    ext
    simp

/-- This is the functor `F ↦ X ↦ YonedaCollection F X`. -/
@[simps]
def yonedaCollectionFunctor (A : Cᵒᵖ ⥤ Type max v w) :
    ((CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w) ⥤ Cᵒᵖ ⥤ Type max v w where
  obj := yonedaCollectionPresheaf A
  map η := yonedaCollectionPresheafMap₁ η

/-- The yonedaULift lemma yields a natural transformation `yonedaCollectionPresheaf A F ⟶ A`. -/
@[simps]
def yonedaCollectionPresheafToA (F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w) :
    yonedaCollectionPresheaf A F ⟶ A where
  app _ := YonedaCollection.yonedaEquivFst

/-- This is the reverse direction of the equivalence we're constructing. -/
@[simps! obj map]
def costructuredArrowPresheafToOver (A : Cᵒᵖ ⥤ Type max v w) :
    ((CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w) ⥤ Over A :=
  (yonedaCollectionFunctor A).toOver _ (yonedaCollectionPresheafToA) (by aesop_cat)

section unit

/-! ### Construction of the unit -/

/-- Forward direction of the unit. -/
def unitForward {F : Cᵒᵖ ⥤ Type max v w} (η : F ⟶ A) (X : C) :
    YonedaCollection (restrictedYonedaObj η) X → F.obj (op X) :=
  fun p => p.snd.val

@[simp]
lemma unitForward_naturality₁ {F G : Cᵒᵖ ⥤ Type max v w} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
    (hε : ε ≫ μ = η) (X : C) (p : YonedaCollection (restrictedYonedaObj η) X) :
    unitForward μ X (p.map₁ (restrictedYonedaObjMap₁ ε hε)) = ε.app _ (unitForward η X p) := by
  simp [unitForward]

@[simp]
lemma unitForward_naturality₂ {F : Cᵒᵖ ⥤ Type max v w} (η : F ⟶ A) (X Y : C) (f : X ⟶ Y)
    (p : YonedaCollection (restrictedYonedaObj η) Y) :
    unitForward η X (YonedaCollection.map₂ (restrictedYonedaObj η) f p) =
      F.map f.op (unitForward η Y p) := by
  simp [unitForward]

@[simp]
lemma app_unitForward {F : Cᵒᵖ ⥤ Type max v w} (η : F ⟶ A) (X : Cᵒᵖ)
    (p : YonedaCollection (restrictedYonedaObj η) X.unop) :
    η.app X (unitForward η X.unop p) = p.yonedaEquivFst := by
  simpa [unitForward] using p.snd.app_val

/-- Backward direction of the unit. -/
def unitBackward {F : Cᵒᵖ ⥤ Type max v w} (η : F ⟶ A) (X : C) :
    F.obj (op X) → YonedaCollection (restrictedYonedaObj η) X :=
  fun x => YonedaCollection.mk (yonedaULiftEquiv.symm (η.app _ x)) ⟨x, ⟨by aesop_cat⟩⟩

lemma unitForward_unitBackward {F : Cᵒᵖ ⥤ Type max v w} (η : F ⟶ A) (X : C) :
    unitForward η X ∘ unitBackward η X = id :=
  funext fun x => by simp [unitForward, unitBackward]

lemma unitBackward_unitForward {F : Cᵒᵖ ⥤ Type max v w} (η : F ⟶ A) (X : C) :
    unitBackward η X ∘ unitForward η X = id := by
  refine funext fun p => YonedaCollection.ext ?_ (OverArrows.ext ?_)
  · convert congrArg yonedaULiftEquiv.symm p.snd.app_val
    simp [unitForward, unitBackward]
    erw [Equiv.symm_apply_apply]
    rfl
  · simp [unitForward, unitBackward]

/-- Intermediate stage of assembling the unit. -/
@[simps]
def unitAuxAuxAux {F : Cᵒᵖ ⥤ Type max v w} (η : F ⟶ A) (X : C) :
    YonedaCollection (restrictedYonedaObj η) X ≅ F.obj (op X) where
  hom := unitForward η X
  inv := unitBackward η X
  hom_inv_id := unitBackward_unitForward η X
  inv_hom_id := unitForward_unitBackward η X

/-- Intermediate stage of assembling the unit. -/
@[simps!]
def unitAuxAux {F : Cᵒᵖ ⥤ Type max v w} (η : F ⟶ A) :
    yonedaCollectionPresheaf A (restrictedYonedaObj η) ≅ F :=
  NatIso.ofComponents (fun X => unitAuxAuxAux η X.unop) (by aesop_cat)

/-- Intermediate stage of assembling the unit. -/
@[simps! hom]
def unitAux (η : Over A) : (restrictedYoneda A ⋙ costructuredArrowPresheafToOver A).obj η ≅ η :=
  Over.isoMk (unitAuxAux η.hom) (by aesop_cat)

/-- The unit of the equivalence we're constructing. -/
def unit (A : Cᵒᵖ ⥤ Type max v w) : 𝟭 (Over A) ≅ restrictedYoneda A ⋙ costructuredArrowPresheafToOver A :=
  Iso.symm <| NatIso.ofComponents unitAux (by aesop_cat)

end unit

/-! ### Construction of the counit -/

section counit

variable {F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w} {X : C}

@[simp]
lemma OverArrows.yonedaCollectionPresheafToA_val_fst (s : yonedaULift.obj X ⟶ A)
    (p : OverArrows (yonedaCollectionPresheafToA F) s) : p.val.fst = s := by
  simpa [YonedaCollection.yonedaEquivFst_eq] using p.app_val

/-- Forward direction of the counit. -/
def counitForward (F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w) (s : CostructuredArrow yonedaULift A) :
    F.obj (op s) → OverArrows (yonedaCollectionPresheafToA F) s.hom :=
  fun x => ⟨YonedaCollection.mk s.hom x, ⟨by simp [YonedaCollection.yonedaEquivFst_eq]⟩⟩

lemma counitForward_val_fst (s : CostructuredArrow yonedaULift A) (x : F.obj (op s)) :
    (counitForward F s x).val.fst = s.hom := by
  simp

@[simp]
lemma counitForward_val_snd (s : CostructuredArrow yonedaULift A) (x : F.obj (op s)) :
    (counitForward F s x).val.snd = F.map (eqToHom (by simp [← CostructuredArrow.eq_mk])) x :=
  YonedaCollection.mk_snd _ _

@[simp]
lemma counitForward_naturality₁ {G : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w} (η : F ⟶ G)
    (s : (CostructuredArrow yonedaULift A)ᵒᵖ) (x : F.obj s) : counitForward G s.unop (η.app s x) =
      OverArrows.map₁ (counitForward F s.unop x) (yonedaCollectionPresheafMap₁ η) (by aesop_cat) :=
  OverArrows.ext <| YonedaCollection.ext (by simp) (by simp)

@[simp]
lemma counitForward_naturality₂ (s t : (CostructuredArrow yonedaULift A)ᵒᵖ) (f : t ⟶ s) (x : F.obj t) :
    counitForward F s.unop (F.map f x) =
      OverArrows.map₂ (counitForward F t.unop x) f.unop.left (by simp) := by
  refine OverArrows.ext <| YonedaCollection.ext (by simp) ?_
  have : (CostructuredArrow.mkPrecomp t.unop.hom f.unop.left).op =
      f ≫ eqToHom (by simp [← CostructuredArrow.eq_mk]) := by
    apply Quiver.Hom.unop_inj
    aesop_cat
  aesop_cat

/-- Backward direction of the counit. -/
def counitBackward (F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w) (s : CostructuredArrow yonedaULift A) :
    OverArrows (yonedaCollectionPresheafToA F) s.hom → F.obj (op s) :=
  fun p => F.map (eqToHom (by simp [← CostructuredArrow.eq_mk])) p.val.snd

lemma counitForward_counitBackward (F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w)
    (s : CostructuredArrow yonedaULift A) : counitForward F s ∘ counitBackward F s = id :=
  funext fun p => OverArrows.ext <| YonedaCollection.ext (by simp) (by simp [counitBackward])

lemma counitBackward_counitForward (F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w)
    (s : CostructuredArrow yonedaULift A) : counitBackward F s ∘ counitForward F s = id :=
  funext fun x => by simp [counitBackward]

/-- Intermediate stage of assembling the counit. -/
@[simps]
def counitAuxAux (F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w) (s : CostructuredArrow yonedaULift A) :
    F.obj (op s) ≅ OverArrows (yonedaCollectionPresheafToA F) s.hom where
  hom := counitForward F s
  inv := counitBackward F s
  hom_inv_id := counitBackward_counitForward F s
  inv_hom_id := counitForward_counitBackward F s

/-- Intermediate stage of assembling the counit. -/
@[simps! hom]
def counitAux (F : (CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w) :
    F ≅ restrictedYonedaObj (yonedaCollectionPresheafToA F) :=
  NatIso.ofComponents (fun s => counitAuxAux F s.unop) (by aesop_cat)

/-- The counit of the equivalence we're constructing. -/
def counit (A : Cᵒᵖ ⥤ Type max v w) : (costructuredArrowPresheafToOver A ⋙ restrictedYoneda A) ≅ 𝟭 _ :=
  Iso.symm <| NatIso.ofComponents counitAux (by aesop_cat)

end counit

end OverPresheafAux

open OverPresheafAux

/-- If `A : Cᵒᵖ ⥤ Type max v w` is a presheaf, then we have an equivalence between presheaves lying over
    `A` and the category of presheaves on `CostructuredArrow yonedaULift A`. There is a quasicommutative
    triangle involving this equivalence, see
    `CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow`.

    This is Lemma 1.4.12 in [Kashiwara2006]. -/
def overEquivPresheafCostructuredArrow (A : Cᵒᵖ ⥤ Type max v w) :
    Over A ≌ ((CostructuredArrow yonedaULift A)ᵒᵖ ⥤ Type max v w) :=
  .mk (restrictedYoneda A) (costructuredArrowPresheafToOver A) (unit A) (counit A)
