import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
/-
GOAL :
A complete API for simplices, boundaries, and horns.
As an example, we should have a function that constructs
from a non-surjective order preserving function `Fin n → Fin n`
a morphism `Δ[n] ⟶ ∂Δ[n]`.

Also, API for comparing maps.
-/

open CategoryTheory Simplicial Limits SimplexCategory Function Opposite Classical SSet
open standardSimplex SimplicialObject

-- clean this later

@[ext]
lemma standardSimplex.ext (x y : Δ[m].obj n) (h : asOrderHom x = asOrderHom y) : x = y := by
  apply (objEquiv _ _).injective
  dsimp [objEquiv, Equiv.ulift]
  ext a
  dsimp [asOrderHom] at h
  rw [h]

instance unique_Δ0 : Unique (Δ[0].obj m) where
  default := const 0 0 m
  uniq := by intro a; ext; simp

-- namespace

def toObj (f : Δ[n] ⟶ X) : X _[n] := (yonedaEquiv _ _) f

def toHom {X : SSet} (x : X _[n]) : Δ[n] ⟶ X := (yonedaEquiv _ _).symm x

-- wierd that it's not in mathlib
-- name?
@[simp]
lemma asOrderHom_objMk (f : Fin (m + 1) →o Fin (n + 1)) : asOrderHom (objMk f) = f := rfl

-- `Δ[n]`

-- vertice
example {n: ℕ} (i : Fin (n + 1)): Δ[n] _[0] := objMk ⟨fun _ ↦ i, by simp [Monotone]⟩

-- face
example {n: ℕ} (i : Fin (n + 2)) : Δ[n + 1] _[n] :=
  objMk (Fin.succAboveOrderEmb i).toOrderHom

-- Basically, map from `Δ[n]` = n-simplex via Yoneda

example {n : ℕ} (f : Fin (n + 1) →o Fin (n + 1)) (hf : ¬ (f : _ → _).Surjective) :
  Δ[n] ⟶ ∂Δ[n] := toHom ⟨objMk f, hf⟩

-- face
example {n: ℕ} (i : Fin (n + 2)) : ∂Δ[n + 1] _[n] where
  val := objMk (Fin.succAboveOrderEmb i).toOrderHom
  property := by simp [Surjective]


section Horn
-- make a morphism from a horn
-- how to do this??? realize `Λ[2,1]` as pushouts???

def face' (n : ℕ) (i j : Fin (n+2)) (h : j ≠ i) : Δ[n] ⟶ Λ[n+1, i] :=
  toHom (horn.face i j h)

example : Δ[0].obj (op [0]):= objMk OrderHom.id

example (f g : Δ[0] ⟶ X)
(h : f.app (op [0]) (objMk OrderHom.id) = g.app (op [0]) (objMk OrderHom.id) ) : f = g := by
  sorry

#check (Δ[0]).map (δ (0 : Fin 2)).op
#check (standardSimplex.map (δ (0 : Fin 2)))

-- how to make [-] not refer to list??
def test (n : ℕ) : (op <| SimplexCategory.mk 0) ⟶ (op [n]) :=
  (mkHom ⟨fun _ ↦ 0, by simp only [Monotone, le_refl, implies_true]⟩).op

example (f : Δ[0] ⟶ X) (n : ℕ) :
(Δ[0]).map (test n) ≫  f.app (op [n]) = f.app (op [0]) ≫ X.map (test n) := by
  apply f.naturality

example (n : ℕ) (a : Δ[0] _[n]) : a = Δ[0].map (test n) (objMk OrderHom.id) := by
  ext; simp only [len_mk, Fin.coe_fin_one]

@[ext]
lemma hom_ext' {X Y : SSet} {f g : X ⟶ Y} (w : ∀ n, f.app (op [n]) = g.app (op [n]))
  : f = g := by
    apply SSet.hom_ext
    intro n
    cases n with
    | op n =>
      induction n using SimplexCategory.rec
      apply w

lemma test2 (f : Δ[0] ⟶ X) (a : Δ[0] _[n]) :
 f.app (op [n]) a = (f.app (op [0]) ≫ X.map (test n)) (objMk OrderHom.id) := by
  rw [← f.naturality]
  simp; congr!; ext; simp

lemma test3 (f g : Δ[0] ⟶ X) (h : f.app (op [0]) = g.app (op [0]) ) : f = g := by
  apply hom_ext'
  intro n
  ext a
  rw [test2, test2, h]

lemma test4 (f g : Δ[0] ⟶ X) (h : f.app (op [0]) default = g.app (op [0]) default) :
  f = g := by
  apply hom_ext'
  intro n
  ext a
  have h : f.app (op [0]) = g.app (op [0]) := by ext a; rw [Unique.eq_default a, h]
  rw [test2, test2, h]

def aux : IsPushout (standardSimplex.map (δ 0)) (standardSimplex.map (δ 1))
(face' 1 1 2 (Fin.ne_of_val_ne (by norm_num))) (face' 1 1 0 (by norm_num)) where
  w := by apply test4; rfl -- what happened???????; `rfl` is much more powerful than I expect
  isColimit' := sorry

-- functorCategoryHasColimitsOfShape


-- record `f - 0 , 1` ` g - 1 , 2`; define maps according to its image???
example {X : SSet} (f g : X _[1]) :
  Λ[2,1] _[1] ⟶ X _[1] := by
    rintro ⟨a, ha⟩

-- suffices to define on the nondeg simplex

#exit
example (f g : Δ[1] ⟶ X)
(h : standardSimplex.map (δ 0) ≫ f = standardSimplex.map (δ 1) ≫ g) : Λ[2,1] ⟶ X where
  app := by
    apply Opposite.rec; apply SimplexCategory.rec
    intro n a
    set a' := choose <| (standardSimplex.objEquiv _ _).symm.surjective a.1

  naturality := _
