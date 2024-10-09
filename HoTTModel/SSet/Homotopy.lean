import HoTTModel.SSet.BoundaryHorn
import HoTTModel.SSet.Exponent
import HoTTModel.SSet.Fibrations

noncomputable section

namespace SSet
open CategoryTheory Simplicial Limits SimplexCategory Function Opposite Classical
open standardSimplex SimplicialObject Fin Prod
variable {X Y : SSet}

structure Homotopy (f g : X ⟶ Y) where
  htp : X ⨯ Δ[1] ⟶ Y
  left : left ≫ htp = f
  right : right ≫ htp = g

notation f " ≃ " g => Homotopy f g

-- maybe just def??
def Homotopic (f g : X ⟶ Y) : Prop := Nonempty (f ≃ g)

structure HomotopyRel (f g : X ⟶ Y) (i : Z ⟶ X)  extends f ≃ g where
  -- res : i ≫ f = i ≫ g
  rel : prod.map i (𝟙 _) ≫ htp = prod.fst ≫ (i ≫ g)

def HomotopicRel (f g : X ⟶ Y) (i : Z ⟶ X) : Prop := Nonempty (HomotopyRel f g i)

lemma HomotopyRel.res_eq  {f g : X ⟶ Y} {i : Z ⟶ X} (h :HomotopyRel f g i) :
    i ≫ f = i ≫ g := by
  have : i ≫ left = left ≫ prod.map i (𝟙 _) := by
    simp [left]
    congr 1
    . simp [Prod.left, IsoProdΔ0, IsoProdTerminal]
    . rw [← Category.assoc _ _ (standardSimplex.map _), ← Category.assoc _ _ (standardSimplex.map _),
          ← Category.assoc _ prod.snd _]
      congr 1
      simp [IsoProdΔ0, IsoProdTerminal]
  -- so it is true!!!
  apply_fun fun y ↦ y ≫ h.htp at this
  simp [h.rel, h.left] at this
  simp [← Category.assoc, left_comp_prod_fst] at this
  exact this

lemma HomotopyRel.rel' {f g : X ⟶ Y} {i : Z ⟶ X} (h : HomotopyRel f g i) :
    prod.map i (𝟙 _) ≫ h.htp = prod.fst ≫ (i ≫ f) :=
  h.res_eq ▸ h.rel

lemma Homotopic.of_homotopicRel {f g : X ⟶ Y} {i : Z ⟶ X} :
    HomotopicRel f g i → Homotopic f g :=
  fun ⟨h⟩ ↦ ⟨h.toHomotopy⟩

structure FibrewiseHomotopy (f g : X ⟶ Y) (p : Y ⟶ Z) extends f ≃ g where
  fibrewise : (h : f ≫ p = g ≫ p) → prod.fst ≫ f ≫ p = htp ≫ p

--lemma FibrewiseHomotopy.fibrewise' (F : FibrewiseHomotopy f g p) (h : f ≫ p = g ≫ p):
--  prod.fst ≫ g ≫ p = F.htp ≫ p := by
--    rw [← h]; exact F.fibrewise h

def FibrewiseHomotopic (f g : X ⟶ Y) (p : Y ⟶ Z) : Prop := Nonempty (FibrewiseHomotopy f g p)

structure FibrewiseHomotopyRel (f g : X ⟶ Y) (p : Y ⟶ Z) (i : Z ⟶ X)
extends FibrewiseHomotopy f g p, HomotopyRel f g i

def FibrewiseHomotopicRel (f g : X ⟶ Y) (p : Y ⟶ Z) (i : Z ⟶ X): Prop :=
  Nonempty (FibrewiseHomotopyRel f g p i)

-- put it in another file + add extends Kan Fib
/-class MinimalFibration (p : X ⟶ Y) where
  minimal : ∀ {n: ℕ} {f g : Δ[n] ⟶ X} {p : X ⟶ Y},
    {res : (boundaryInclusion n) ≫ f = (boundaryInclusion n) ≫ g} → {h : f ≫ p = g ≫ p} →
    FibrewiseHomotopic f g p res h → f = g
-/

-- basic property of homotopy
-- No use at all

def Homotopy.Refl (f : X ⟶ Y) : f ≃ f where
  htp := prod.fst ≫ f
  left := by simp only [← Category.assoc, left_comp_prod_fst, Category.id_comp]
  right := by simp only [← Category.assoc, right_comp_prod_fst, Category.id_comp]

lemma homotopic_refl (f : X ⟶ Y) : Homotopic f f := ⟨Homotopy.Refl f⟩


-- put this in antoher file
section KanComplex

-- put it somewhere else, not in this section

-- name convetions : 0-simplex = vertice; 1-simplex = edge

lemma Homotopy.vertice_eq {S : SSet} {x y : Δ[0] ⟶ S} (h : x ≃ y) :
    x = standardSimplex.map (δ 1) ≫ IsoΔ0Prod.hom ≫ h.htp ∧
      y = standardSimplex.map (δ 0) ≫ IsoΔ0Prod.hom ≫ h.htp := by
  simp only [← h.left, ← h.right, ← Category.assoc]
  constructor
  . congr; simp [Prod.left, IsoProdΔ0, IsoProdTerminal, IsoΔ0Prod, IsoTerminalProd]
  . congr; simp [Prod.right, IsoProdΔ0, IsoProdTerminal, IsoΔ0Prod, IsoTerminalProd]

lemma vertice_homotopic_iff_exist_edge {S : SSet} (x y : Δ[0] ⟶ S) :
  Homotopic x y ↔ ∃ v : Δ[1] ⟶ S, x = standardSimplex.map (δ 1) ≫ v ∧
    y = standardSimplex.map (δ 0) ≫ v := by
  constructor
  . rintro ⟨h⟩
    use IsoΔ0Prod.hom ≫ h.htp
    exact h.vertice_eq
  . rintro ⟨v, ⟨hvx, hvy⟩⟩
    use IsoΔ0Prod.inv ≫ v
    simp [left, IsoProdΔ0, IsoProdTerminal, IsoΔ0Prod, IsoTerminalProd, hvx]
    simp [right, IsoProdΔ0, IsoProdTerminal, IsoΔ0Prod, IsoTerminalProd, hvy]


lemma vertice_homotopic_iff_exist_edge' {S : SSet} (x y : Δ[0] ⟶ S) :
    Homotopic x y ↔ ∃ v : S _[1], (yonedaEquiv _ _) x = S.map (δ 1).op v ∧
    (yonedaEquiv _ _) y = S.map (δ 0).op v := by
  rw [vertice_homotopic_iff_exist_edge]
  constructor
  . rintro ⟨v, ⟨h₁, h₂⟩⟩
    use (yonedaEquiv _ _) v
    apply_fun (yonedaEquiv _ _) at h₁ h₂
    constructor
    convert h₁
    apply yonedaCompUliftFunctorEquiv_naturality (F := S)
    convert h₂
    apply yonedaCompUliftFunctorEquiv_naturality (F := S)
  . rintro ⟨v, ⟨h₁, h₂⟩⟩
    use (yonedaEquiv _ _).symm v
    constructor
    <;> apply_fun S.yonedaEquiv _
    <;> assumption

lemma aux_fin2' (i : Fin 2) :
     i = 0 ∨ i = 1 := by
  cases i with
  | mk i hi =>
      simpa [← Fin.val_eq_val, ← Nat.le_one_iff_eq_zero_or_eq_one, ← Nat.lt_succ_iff]

lemma aux_fin2 {i j : Fin 2} :
    i < j → i = 0 ∧ j = 1 := by
  intro h
  rcases aux_fin2' i with hi | hi
  rcases aux_fin2' j with hj | hj
  . simp [hi, hj] at h
  . exact ⟨hi, hj⟩
  rcases aux_fin2' j with hj | hj
  <;> simp [hi, hj] at h

lemma ext_hom_Δ0 (f g : Δ[0] ⟶ S) :
    f.app (op [0]) default = g.app (op [0]) default → f = g := by
  intro h
  apply hom_generator_ext standardSimplexGenerator
  intro x hx
  rcases hx
  convert h
  <;> apply Subsingleton.allEq

def VecticeHomotopicEquivOfKanComplex (S : SSet) [KanComplex S] :
    Equivalence (fun x y : Δ[0] ⟶ S ↦ Homotopic x y) where
      refl := homotopic_refl
      symm {x y} := by
        rw [vertice_homotopic_iff_exist_edge', vertice_homotopic_iff_exist_edge]
        intro ⟨v, hv⟩
        set v₁ := S.map (σ 0).op (S.yonedaEquiv _ y)
        set w := horn.HomMk ![v, v₁] 2
          (by
            intro i j hij
            cases (aux_fin2 hij).1
            cases (aux_fin2 hij).2
            simp
            simp only [v₁, ← FunctorToTypes.map_comp_apply, ← op_comp]
            erw [SimplexCategory.δ_comp_σ_self' (i := 0) (H := rfl), ← hv.2]
            simp
          )
        obtain ⟨w', hw⟩ := KanComplex.hornFilling w
        use (standardSimplex.map (δ 2)) ≫ w'
        constructor
        . apply_fun (fun u ↦ (standardSimplex.map (δ 1)) ≫ (yonedaEquiv _ _).symm
            (horn.face' (n := 1) 2 1 (by simp [← val_eq_val])) ≫ u) at hw
          convert hw using 1
          . have : (1 : Fin 3) = (2 : Fin 3).succAbove (1 : Fin 2) := by rfl
            simp [w, this, horn.face_comp_HomMk, v₁]
            rw [yonedaEquiv_naturality, Equiv.symm_apply_apply,
                ← Category.assoc, ← Functor.map_comp,
                SimplexCategory.δ_comp_σ_succ' _ _ (by simp only [succ_zero_eq_one])]
            simp only [CategoryTheory.Functor.map_id, Category.id_comp]
          . rw [← Category.assoc, ← Category.assoc _ _ (_ ≫ w'), ← Category.assoc _ _ w']
            congr! 1
            apply_fun yonedaEquiv _ _
            ext : 1
            simp [← yonedaEquiv_naturality', hornInclusion, horn.face', Face,
                  asOrderHom_objMk]
            ext : 1
            change (2 : Fin 3).succAbove ∘ (1 : Fin 2).succAbove =
              (1 : Fin 3).succAbove ∘ (1 : Fin 2).succAbove
            convert succAbove_succAbove_comm_of_castSucc_lt (1 : Fin 2) 2 (by simp)
        . apply_fun (fun u ↦ (standardSimplex.map (δ 1)) ≫ (yonedaEquiv _ _).symm
            (horn.face' (n := 1) 2 0 (by simp [← val_eq_val])) ≫ u) at hw
          convert hw using 1
          . have : (0 : Fin 3) = (2 : Fin 3).succAbove (0 : Fin 2) := by rfl
            simp [w, this, horn.face_comp_HomMk]
            apply_fun S.yonedaEquiv _
            exact hv.1
          . rw [← Category.assoc, ← Category.assoc _ _ (_ ≫ w'), ← Category.assoc _ _ w']
            congr! 1
            apply_fun yonedaEquiv _ _
            ext : 1
            simp [← yonedaEquiv_naturality', hornInclusion, horn.face', Face,
                  asOrderHom_objMk]
            ext : 1
            change (2 : Fin 3).succAbove ∘ (0 : Fin 2).succAbove =
              (0 : Fin 3).succAbove ∘ (1 : Fin 2).succAbove
            convert succAbove_succAbove_comm_of_castSucc_lt (0 : Fin 2) 2 (by simp)
      trans {x y z} := by
        rw [vertice_homotopic_iff_exist_edge', vertice_homotopic_iff_exist_edge']
        intro ⟨v, hv⟩ ⟨v', hv'⟩
        set w := horn.HomMk ![v', v] 1
          (by
            intro i j hij
            cases (aux_fin2 hij).1
            cases (aux_fin2 hij).2
            exact hv'.1.symm.trans hv.2
          )
        rw [vertice_homotopic_iff_exist_edge]
        obtain ⟨w', hw⟩ := KanComplex.hornFilling w
        use (standardSimplex.map (δ 1)) ≫ w'
        constructor
        . apply_fun (fun u ↦ (standardSimplex.map (δ 1)) ≫ (yonedaEquiv _ _).symm
            (horn.face' (n := 1) 1 2 (by simp [← val_eq_val])) ≫ u) at hw
          convert hw using 1
          . have {h} {h'}: horn.face' 1 (2 : Fin 3) h
              = horn.face' 1 ((1 : Fin 3).succAbove (1 : Fin 2)) h' := by rfl
            simp [w]
            erw [this, horn.face_comp_HomMk]
            apply_fun S.yonedaEquiv _
            exact hv.1
          . rw [← Category.assoc, ← Category.assoc _ _ (_ ≫ w'), ← Category.assoc _ _ w']
            congr! 1
            apply_fun yonedaEquiv _ _
            ext : 1
            simp [← yonedaEquiv_naturality', hornInclusion, horn.face', Face,
                  asOrderHom_objMk]
            ext : 1
            change (1 : Fin 3).succAbove ∘ (1 : Fin 2).succAbove =
              (2 : Fin 3).succAbove ∘ (1 : Fin 2).succAbove
            exact (succAbove_succAbove_comm_of_castSucc_lt (1 : Fin 2) 2 (by simp)).symm
        . apply_fun (fun u ↦ (standardSimplex.map (δ 0)) ≫ (yonedaEquiv _ _).symm
            (horn.face' (n := 1) 1 0 (by simp [← val_eq_val])) ≫ u) at hw
          convert hw using 1
          have : (0 : Fin 3) = (1 : Fin 3).succAbove (0 : Fin 2) := by rfl
          simp [w, this, horn.face_comp_HomMk]
          apply_fun S.yonedaEquiv _
          exact hv'.2

def empty : SSet where
  obj _ := PEmpty
  map _ := PEmpty.elim

def empty.homTo (X : SSet) : empty ⟶ X where
  app n := PEmpty.elim
  naturality := by
    intro _ _ _; funext x
    apply PEmpty.elim x

-- To prove HomotopicRelEquivOfKanComplex

-- 1. `f ≃ g rel L ↔ f₀ ≃ g₀` in the fibre of `X.exp K → X.exp L`
-- where `f₀` is `K → K ⨯ Δ[0] → X`

-- maybe i need fibre

def fibre {X Y : SSet} (f : X ⟶ Y) (y : Y _[0]) := pullback f ((Y.yonedaEquiv _).symm y)

def fibre.hom {X Y : SSet} (f : X ⟶ Y) (y : Y _[0]) :
    fibre f y ⟶ X := pullback.fst _ _

def fibre.CommSq {X Y : SSet} (f : X ⟶ Y) (y : Y _[0]) :
    IsPullback (fibre.hom f y) (pullback.snd _ _) f ((Y.yonedaEquiv _).symm y)  where
      w := pullback.condition
      isLimit' := ⟨pullbackIsPullback _ _⟩

-- this one is hard
instance inst1 [KanComplex X] (i : L ⟶ K) :
    KanFibration (X.expFunctor.map i.op) :=
  sorry

instance {X Y : SSet} (f : X ⟶ Y) [KanFibration f] (y : Y _[0]) :
    KanComplex (fibre f y) := by
  rw [← KanFibration.iff_is_KanComplex]
  have : (fibre f y).toΔ0 = pullback.snd f ((Y.yonedaEquiv _).symm y) :=
    unique_toΔ0 _ _
  rw [this]
  infer_instance

def fibre.lift {X K L: SSet} [KanComplex X] (f : K ⟶ X) (h : L ⟶ X) (i : L ⟶ K)  (H : h = i ≫ f)
  := IsPullback.lift (fibre.CommSq (X.expFunctor.map i.op) (IsoProdΔ0.inv ≫ h))
  ((yonedaEquiv _ _).symm (IsoProdΔ0.inv ≫ f)) (𝟙 _) (by
    simp [H]
    apply_fun yonedaEquiv _ _
    simp [← yonedaEquiv_naturality', expFunctor, IsoProdΔ0, IsoProdTerminal]
  )

lemma _root_.CategoryTheory.IsPullback.comp_lift {C : Type u₁}
  [CategoryTheory.Category.{v₁, u₁} C] {P X Y Z : C}
  {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (hP : CategoryTheory.IsPullback fst snd f g)
  {W : C} {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g) {Q : C} {l : Q ⟶ W} :
    l ≫ hP.lift _ _ w = hP.lift (l ≫ h) (l ≫ k) (by simp only [Category.assoc, w]) := by
  apply hP.hom_ext <;> simp

open MonoidalCategory in
lemma homotopicRel_iff_homotopic_lift {X K L: SSet} [KanComplex X] (f g : K ⟶ X)  (i : L ⟶ K) :
    HomotopicRel f g i ↔ (i ≫ f = i ≫ g ∧ ((h : i ≫ f = i ≫ g) →
      Homotopic (fibre.lift f (i ≫ f) i rfl) (fibre.lift g (i ≫ f) i h))) := by
  constructor
  . intro ⟨h⟩
    constructor
    . exact h.res_eq
    . intro h'
      rw [vertice_homotopic_iff_exist_edge]
      use IsPullback.lift (fibre.CommSq (X.expFunctor.map i.op) (IsoProdΔ0.inv ≫ (i ≫ f)))
          (K.adjEquiv _ _ h.htp) Δ[1].toΔ0 (by
              apply_fun (adjEquiv _ _ _).symm
              erw [h', adjEquiv_naturality_symm, adjEquiv_naturality_left_symm']
              simp; erw [adjEquiv_symm_yonedaEquiv_symm_apply]
              simp [IsoProdΔ0, IsoProdTerminal]
              exact h.rel
          )
      constructor
      . apply pullback.hom_ext
        . erw [IsPullback.lift_fst, IsPullback.comp_lift, IsPullback.lift_fst,
              ← yonedaEquiv_symm_naturality₂]
          simp [← h.left, expFunctor, exp, iHom]
          rw [← Category.assoc]; congr 1
          apply prod.hom_ext
          <;> simp [left]
        . apply unique_toΔ0
      . apply pullback.hom_ext
        . erw [IsPullback.lift_fst, IsPullback.comp_lift, IsPullback.lift_fst,
              ← yonedaEquiv_symm_naturality₂]
          simp [← h.right, expFunctor, exp, iHom]
          rw [← Category.assoc]; congr 1
          apply prod.hom_ext
          <;> simp [right]
        . apply unique_toΔ0
  . intro ⟨h₁, h₂⟩
    specialize h₂ h₁
    cases h₂ with
    | intro h₂ =>
      constructor
      apply HomotopyRel.mk ?_ _
      use (K.adjEquiv _ _).invFun (IsoΔ0Prod.hom ≫ h₂.htp ≫ fibre.hom _ _)
      . rw [← cancel_epi (@IsoProdΔ0 K).inv]
        have : IsoProdΔ0.inv ≫ left = K ◁ (standardSimplex.map (δ 1)) := by
          simp [IsoProdΔ0, left]; apply prod.hom_ext <;> simp
        rw [← Category.assoc, this]
        change (K.iHom X).map (δ 1).op _ = _
        rw [yonedaEquiv_symm_naturality]
        erw [yonedaEquiv_symm_adjEquiv_symm_apply, ← Category.assoc _ h₂.htp,
            ← Category.assoc, ← h₂.vertice_eq.1, IsPullback.lift_fst, Equiv.apply_symm_apply]
      . rw [← cancel_epi (@IsoProdΔ0 K).inv]
        have : IsoProdΔ0.inv ≫ right = K ◁ (standardSimplex.map (δ 0)) := by
          simp [IsoProdΔ0, right]; apply prod.hom_ext <;> simp
        rw [← Category.assoc, this]
        change (K.iHom X).map (δ 0).op _ = _
        rw [yonedaEquiv_symm_naturality]
        erw [yonedaEquiv_symm_adjEquiv_symm_apply, ← Category.assoc _ h₂.htp, ← Category.assoc, ← h₂.vertice_eq.2,
             IsPullback.lift_fst, Equiv.apply_symm_apply]
      . erw [← adjEquiv_naturality_symm, Category.assoc, Category.assoc,
             CategoryTheory.Limits.pullback.condition]
        rw [← Category.assoc _ h₂.htp, ← Category.assoc]
        have : (IsoΔ0Prod.hom ≫ h₂.htp) ≫ pullback.snd _ _ = default := Unique.uniq _ _
        erw [this, adjEquiv_naturality_left_symm' default]
        simp
        erw [adjEquiv_symm_yonedaEquiv_symm_apply, h₁]
        simp [IsoProdΔ0, IsoProdTerminal]

def HomotopicRelEquivOfKanComplex (X K : SSet) {L} (i : L ⟶ K) [KanComplex X] :
    Equivalence (fun f g : K ⟶ X ↦ HomotopicRel f g i) where
      refl f := by
        rw [homotopicRel_iff_homotopic_lift]
        constructor
        . rfl
        . exact fun _ ↦ (VecticeHomotopicEquivOfKanComplex _).refl _
      symm {f g} H := by
        rw [homotopicRel_iff_homotopic_lift] at H ⊢
        constructor
        . exact H.1.symm
        . intro _
          convert (VecticeHomotopicEquivOfKanComplex _).symm (H.2 H.1)
      trans {f g h} H₁ H₂ := by
        rw [homotopicRel_iff_homotopic_lift] at H₁ H₂ ⊢
        constructor
        . exact H₁.1.trans H₂.1
        . intro _
          apply (VecticeHomotopicEquivOfKanComplex _).trans (H₁.2 H₁.1)
          convert H₂.2 H₂.1 using 3
          exact H₁.1

lemma homotopic_iff_homotopicRel_empty (X K : SSet) (f g : K ⟶ X) :
    Homotopic f g ↔ HomotopicRel f g (empty.homTo _) := by
  constructor
  . intro ⟨h⟩; use h; ext n x
    apply PEmpty.elim (yonedaEquiv _ _ $ (yonedaEquiv _ _).symm x ≫ prod.fst)
  . apply Homotopic.of_homotopicRel

def HomotopicEquivOfKanComplex (X K : SSet) [KanComplex X] :
    Equivalence (fun f g : K ⟶ X ↦ Homotopic f g) := by
  simp only [homotopic_iff_homotopicRel_empty]
  apply HomotopicRelEquivOfKanComplex

class MinimalKanComplex (S : SSet) extends KanComplex S where
  minimal : ∀ {n : ℕ} {x y : Δ[n] ⟶ S}, HomotopicRel x y (boundaryInclusion n) → x = y

end KanComplex

section SimplicialHomotopyGroup

@[simp]
def fixed (n : ℕ) [NeZero n] (X : SSet) (v : Δ[0] ⟶ X) :=
  {x : Δ[n] ⟶ X | ∂Δ[n].toΔ0 ≫ v = boundaryInclusion n ≫ x}

lemma aux123 (i : Fin (n + 2)) (x : Δ[n + 1] ⟶ X) :
    standardSimplex.map (δ i) ≫ x
      = boundary.face.hom i ≫ boundaryInclusion _ ≫ x :=
  sorry

lemma fixed.mem_iff (n : ℕ) (X : SSet) (v : Δ[0] ⟶ X) (x : Δ[n + 1] ⟶ X) :
    x ∈ fixed (n + 1) X v ↔ ∀ j, standardSimplex.map (δ j) ≫ x = Δ[n].toΔ0 ≫ v := by
  sorry

lemma fixed.δ_comp_eq (x: fixed (n + 1) X v) :
    ∀ i : Fin (n + 2), standardSimplex.map (δ i) ≫ x.val =
      Δ[n].toΔ0 ≫ v := by
  intro i
  rw [aux123, ← x.property, ← Category.assoc]
  congr 1 -- LEAN automatically infer the instance of `unique to Δ[0]`

lemma fixed.δ_comp_eq_δ_comp (x y: fixed (n + 1) X v) :
    ∀ i j : Fin (n + 2), standardSimplex.map (δ i) ≫ x.val =
      standardSimplex.map (δ j) ≫ y.val := by
  intro _ _
  rw [fixed.δ_comp_eq, fixed.δ_comp_eq]

def fixed.homotopicRelEquivOfKanComplex (n : ℕ) [NeZero n] (X : SSet) [KanComplex X] (v : Δ[0] ⟶ X) :
    Equivalence (fun f g : fixed n X v ↦ HomotopicRel f.val g.val (boundaryInclusion n)) where
      refl f := (HomotopicRelEquivOfKanComplex _ _ _).refl f.val
      symm := (HomotopicRelEquivOfKanComplex _ _ _).symm
      trans := (HomotopicRelEquivOfKanComplex _ _ _).trans

instance Hom.setoid (X : SSet) [KanComplex X] :
    Setoid (Δ[n] ⟶ X) where
      r f g:= Homotopic f g
      iseqv := HomotopicEquivOfKanComplex _ _

instance fixed.setoid (n : ℕ) [NeZero n] (X : SSet) [KanComplex X] (v : Δ[0] ⟶ X) :
    Setoid (fixed n X v) where
      r f g:= HomotopicRel f.val g.val (boundaryInclusion n)
      iseqv := fixed.homotopicRelEquivOfKanComplex _ _ _

instance fixed.hasEquiv (n : ℕ) [NeZero n] (X : SSet) [KanComplex X] (v : Δ[0] ⟶ X) :
    HasEquiv (fixed n X v) := instHasEquivOfSetoid

section multiplication

noncomputable def fixed.mul₀ [KanComplex X] (x y : fixed (n + 1) X v) :
    Λ[n + 2, ⟨n + 1, by linarith⟩] ⟶ X := by
  apply horn.HomMk' ?_ _ _
  exact fun i ↦ if i.val = n then x.val
    else (if i.val = n + 1 then y.val
      else Δ[n + 1].toΔ0 ≫ v)
  intro i j hij
  split_ifs with hi hj
  . exact fixed.δ_comp_eq_δ_comp _ _ _ _
  . exact fixed.δ_comp_eq_δ_comp _ _ _ _
  . rw [fixed.δ_comp_eq, ← Category.assoc]; congr 1
  . exact fixed.δ_comp_eq_δ_comp _ _ _ _
  . exact fixed.δ_comp_eq_δ_comp _ _ _ _
  . rw [fixed.δ_comp_eq, ← Category.assoc]; congr 1
  . rw [fixed.δ_comp_eq, ← Category.assoc]; congr 1
  . rw [fixed.δ_comp_eq, ← Category.assoc]; congr 1
  . rw [← Category.assoc, ← Category.assoc]; congr 1

lemma fixed.mul₀_spec [KanComplex X] (x y : fixed (n + 1) X v) (i):
    (horn.face'.hom _ _ (succAbove_ne _ i)) ≫ fixed.mul₀ x y
      = if i.val = n then x.val
          else (if i.val = n + 1 then y.val
            else Δ[n + 1].toΔ0 ≫ v) := by
  simp only [mul₀, horn.HomMk_spec', horn.face'.hom]

def fixed.mul₁ [KanComplex X] (x y : fixed (n + 1) X v) :
    Δ[n + 2] ⟶ X := choose (KanComplex.hornFilling $ mul₀ x y)

def fixed.mul₁_spec [KanComplex X] (x y : fixed (n + 1) X v) :
    mul₀ x y = hornInclusion (n + 2) ⟨n + 1, _⟩ ≫ fixed.mul₁ x y :=
  choose_spec (KanComplex.hornFilling $ mul₀ x y)

lemma fixed.mul₁_spec'_aux [KanComplex X] (x y : fixed (n + 1) X v) (f : Δ[n + 2] ⟶ X)
  (hf : mul₀ x y = hornInclusion (n + 2) ⟨n + 1, _⟩ ≫ f) (i) :
    standardSimplex.map (SimplexCategory.δ ((⟨n + 1, by linarith⟩ : Fin (n + 3)).succAbove i)) ≫ f
      = if i.val = n then x.val
        else (if i.val = n + 1 then y.val
          else Δ[n + 1].toΔ0 ≫ v) := by
  have : standardSimplex.map (SimplexCategory.δ ((⟨n + 1, by linarith⟩ : Fin (n + 3)).succAbove i)) =
    (Λ[n + 1 + 1, ⟨n + 1, by linarith⟩].yonedaEquiv [n + 1]).symm
      (horn.face' _ _ (succAbove_ne _ i))
       ≫ hornInclusion (n + 2) ⟨n + 1, _⟩ :=
      sorry
  erw [this, Category.assoc, ← hf, fixed.mul₀_spec]

lemma fixed.mul₁_spec' [KanComplex X] (x y : fixed (n + 1) X v) (i) :
    standardSimplex.map (SimplexCategory.δ ((⟨n + 1, by linarith⟩ : Fin (n + 3)).succAbove i)) ≫
        fixed.mul₁ x y
      = if i.val = n then x.val
        else (if i.val = n + 1 then y.val
          else Δ[n + 1].toΔ0 ≫ v) :=
    fixed.mul₁_spec'_aux _ _ _ (fixed.mul₁_spec _ _) _

lemma fixed.mul₁_spec'_eq_or_of_neq_aux [KanComplex X] (x y : fixed (n + 1) X v) (f : Δ[n + 2] ⟶ X)
  (hf : mul₀ x y = hornInclusion (n + 2) ⟨n + 1, _⟩ ≫ f) {i} (hi : i.val ≠ n + 1) :
    standardSimplex.map (SimplexCategory.δ i) ≫ f = x.val ∨
    standardSimplex.map (SimplexCategory.δ i) ≫ f = y.val ∨
    standardSimplex.map (SimplexCategory.δ i) ≫ f = Δ[n + 1].toΔ0 ≫ v := by
  obtain ⟨j, hj⟩  := (exists_succAbove_eq_iff (x := ⟨n + 1, by linarith⟩) (y := i)).mpr
    (by simpa [← val_eq_val])
  cases hj
  rw [fixed.mul₁_spec'_aux _ _ _ hf]
  split_ifs
  <;> simp

lemma fixed.mul₁_spec'_eq_or_of_neq [KanComplex X] (x y : fixed (n + 1) X v) {i}
  (hi : i.val ≠ n + 1) :
    standardSimplex.map (SimplexCategory.δ i) ≫ fixed.mul₁ x y = x.val ∨
    standardSimplex.map (SimplexCategory.δ i) ≫ fixed.mul₁ x y = y.val ∨
    standardSimplex.map (SimplexCategory.δ i) ≫ fixed.mul₁ x y = Δ[n + 1].toΔ0 ≫ v := by
  obtain ⟨j, hj⟩  := (exists_succAbove_eq_iff (x := ⟨n + 1, by linarith⟩) (y := i)).mpr
    (by simpa [← val_eq_val])
  cases hj
  rw [fixed.mul₁_spec']
  split_ifs
  <;> simp

def fixed.mulOfHornFilling [KanComplex X] {x y : fixed (n + 1) X v}
  (f : Δ[n + 2] ⟶ X) (hf : mul₀ x y = hornInclusion (n + 2) ⟨n + 1, _⟩ ≫ f) :
    fixed (n + 1) X v :=
  ⟨standardSimplex.map (δ ⟨n + 1, by linarith⟩) ≫ f, by
    rw [fixed.mem_iff]
    intro j
    rw [← Category.assoc, ← Functor.map_comp]
    rcases eq_or_ne j.val (n + 1) with h | h
    . rw [SimplexCategory.δ_comp_δ_self' (by simp [← val_eq_val, eq_comm]; exact h)]; simp
      rcases fixed.mul₁_spec'_eq_or_of_neq_aux _ _ (i := j.succ) _ hf (by simp [h])
        with (h | (h | h))
      repeat' rw [h, fixed.δ_comp_eq]
      rw [h, ← Category.assoc]; congr 1
    . rw [SimplexCategory.δ_comp_δ' (Fin.val_lt_last (by rwa [ne_eq, ← val_eq_val]))]; simp
      rcases fixed.mul₁_spec'_eq_or_of_neq_aux _ _ (i := j.castSucc) _ hf (by simp [h])
        with (h | (h | h))
      repeat' rw [h, fixed.δ_comp_eq]
      rw [h, ← Category.assoc]; congr 1
    ⟩

def fixed.mul [KanComplex X] (x y : fixed (n + 1) X v) : fixed (n + 1) X v :=
  fixed.mulOfHornFilling (fixed.mul₁ x y) (fixed.mul₁_spec _ _)

-- this one is hard!!!
lemma fixed.mulOfHornFilling_unique_up_to_equiv [KanComplex X] {x x' y y': fixed (n + 1) X v}
  (hx : x ≈ x') (hy : y ≈ y') (f f' : Δ[n + 2] ⟶ X)
  (hf : mul₀ x y = hornInclusion (n + 2) ⟨n + 1, _⟩ ≫ f)
  (hf' : mul₀ x' y' = hornInclusion (n + 2) ⟨n + 1, _⟩ ≫ f'):
    fixed.mulOfHornFilling f hf ≈ fixed.mulOfHornFilling f' hf' := by
  sorry

lemma fixed.mul_unique_up_to_equiv_of_equiv [KanComplex X] {x x' y y': fixed (n + 1) X v}
  (hx : x ≈ x') (hy : y ≈ y') :
    fixed.mul x y ≈ fixed.mul x' y' :=
  fixed.mulOfHornFilling_unique_up_to_equiv hx hy _ _ _ _

lemma fixed.mul_unique_up_to_equiv [KanComplex X] (x y : fixed (n + 1) X v)
  (f : Δ[n + 2] ⟶ X) (hf : mul₀ x y = hornInclusion (n + 2) ⟨n + 1, _⟩ ≫ f) :
    fixed.mul x y ≈ fixed.mulOfHornFilling f hf :=
  fixed.mulOfHornFilling_unique_up_to_equiv (Setoid.refl _) (Setoid.refl _) _ _ _ _

instance fixed.inst_mul : {n : ℕ} → [NeZero n] → {X : SSet} → [KanComplex X] → {v : Δ[0] ⟶ X} →
    Mul (fixed n X v)
| 0, h, _, _, _ => by simp at h
| n + 1, _, _, _, _ => ⟨fixed.mul⟩

lemma aux_fin_succAbove_iff (n k : ℕ) (j : Fin (n + k + 1)):
    ((⟨n + 1, by linarith⟩ : Fin (n + k + 2)).succAbove j).val = n ↔ ↑j = n:= by
  change _ = (⟨n, by linarith⟩ : Fin (n + k + 2)).val ↔
    _ = (⟨n, by linarith⟩ : Fin (n + k + 1)).val
  rw [val_eq_val, val_eq_val]
  have (n k) : ((⟨n + 1, by linarith⟩ : Fin (n + k + 2)).succAbove ⟨n, by linarith⟩)
    = ⟨n, by linarith⟩ := by
      rw [succAbove_of_castSucc_lt _ _ (by simp [lt_iff_val_lt_val])]; simp
  constructor
  intro h; rw [← this] at h; apply succAbove_right_injective h
  intro h; rw [h, this]

lemma aux_fin_succAbove_iff' (n k : ℕ) (j : Fin (n + k + 2)):
    ((⟨n + 1, by linarith⟩ : Fin (n + k + 3)).succAbove j).val = n + 2 ↔ ↑j = n + 1:= by
  change _ = (⟨n + 2, by linarith⟩ : Fin (n + k + 3)).val ↔
    _ = (⟨n + 1, by linarith⟩ : Fin (n + k + 2)).val
  rw [val_eq_val, val_eq_val]
  have (n k) : ((⟨n + 1, by linarith⟩ : Fin (n + k + 3)).succAbove ⟨n + 1, by linarith⟩)
    = ⟨n + 2, by linarith⟩ := by
      rw [succAbove_of_lt_succ _ _ (by simp [lt_iff_val_lt_val])]; simp
  constructor
  intro h; rw [← this] at h; apply succAbove_right_injective h
  intro h; rw [h, this]

lemma fixed.mul_equiv_iff [KanComplex X] (x y z : fixed (n + 1) X v) :
    x * y ≈ z ↔ ∃ w : Δ[n + 2] ⟶ X, ∀ j, standardSimplex.map (δ j) ≫ w =
      if j.val = n then x.val
        else (if j.val = n + 1 then z.val
          else if j.val = n + 2 then y.val
            else Δ[n + 1].toΔ0 ≫ v) := by
  constructor
  . sorry
  . intro ⟨w, hw⟩
    have : mul₀ x y = hornInclusion (n + 2) ⟨n + 1, by linarith⟩ ≫ w := by
      apply horn.hom_ext'
      intro j hj
      obtain ⟨j, hj⟩ := exists_succAbove_eq_iff.mpr hj
      cases hj
      rw [mul₀_spec, ← Category.assoc, horn.face'.hom_comp_boundaryInclusion, hw]
      have : (((⟨n + 1, by linarith⟩ : Fin (n + 3)).succAbove j).val = n + 1) ↔ False :=
        ⟨by simp [← val_eq_val] at hj; exact hj, False.elim⟩
      simp only [this, ↓reduceIte]
      congr 1
      . simp [aux_fin_succAbove_iff]
      . congr 1
        simp [aux_fin_succAbove_iff' n 0]
    have : z = fixed.mulOfHornFilling (x := x) (y := y) w this := by
      ext : 1
      dsimp [mulOfHornFilling]
      convert (hw ⟨n + 1, by linarith⟩).symm
      simp only [add_right_eq_self, one_ne_zero, ↓reduceIte]
    rw [this]
    apply fixed.mul_unique_up_to_equiv


lemma fixed.mul_sound {n : ℕ} [NeZero n] {X : SSet} [KanComplex X] {v : Δ[0] ⟶ X}
  {x x' y y' : fixed n X v} :
    x ≈ x' → y ≈ y' → x * y ≈ x' * y' := by
  cases n with
  | zero => apply False.elim; rwa [← neZero_zero_iff_false (α := ℕ)]
  | succ n => apply fixed.mul_unique_up_to_equiv_of_equiv

instance fixed.inst_one {n : ℕ} [NeZero n] {X : SSet} [KanComplex X] {v : Δ[0] ⟶ X} :
    One (fixed n X v) := ⟨⟨Δ[n].toΔ0 ≫ v, rfl⟩⟩

lemma fixed.equiv_one_iff [KanComplex X] (x : fixed (n + 1) X v) :
  x ≈ 1 ↔ ∃ w : Δ[n + 2] ⟶ X, ∀ j, standardSimplex.map (δ j) ≫ w =
    if j = last _ then x.val else Δ[n + 1].toΔ0 ≫ v := sorry
  -- maybe it would be nice to name Δ[n + 1].toΔ0 ≫ v something like a 1?

lemma fixed.mul₀_one [KanComplex X] (x : fixed (n + 1) X v) :
  mul₀ x 1 = hornInclusion (n + 2) ⟨n + 1, _⟩ ≫
    (standardSimplex.map (σ ⟨n, by linarith⟩) ≫ x.val) := by
  apply horn.hom_ext'
  intro j hj
  obtain ⟨i, hi⟩ := exists_succAbove_eq_iff.mpr hj
  cases hi
  rw [← Category.assoc, horn.face'.hom_comp_boundaryInclusion, fixed.mul₀_spec,
      ← Category.assoc, ← Functor.map_comp]
  split_ifs with h h'
  . rw [δ_comp_σ_self', CategoryTheory.Functor.map_id, Category.id_comp]
    simp [← h]; rw [succAbove_of_succ_le _ _ (by simp [le_iff_val_le_val])]
  . rw [δ_comp_σ_of_gt']; simp
    rw [fixed.δ_comp_eq, ← Category.assoc]
    congr 1
    simp [h', lt_iff_val_lt_val, succAbove_of_lt_succ]
  . have aux : i.val < n := sorry
    have : (⟨n, by linarith⟩ : Fin (n + 2)) = ((⟨n, by linarith⟩ : Fin (n + 2)).pred sorry).succ :=
      sorry
    rw [succAbove_of_succ_le, this, δ_comp_σ_of_le]; simp
    rw [fixed.δ_comp_eq, ← Category.assoc]
    congr 1
    exact Nat.le_sub_one_of_lt aux
    simp [le_iff_val_le_val]; exact aux.le

lemma fixed.one_mul₀ [KanComplex X] (x : fixed (n + 1) X v) :
  mul₀ 1 x = hornInclusion (n + 2) ⟨n + 1, _⟩ ≫
    (standardSimplex.map (σ ⟨n + 1, by linarith⟩) ≫ x.val) := by
  apply horn.hom_ext'
  intro j hj
  obtain ⟨i, hi⟩ := exists_succAbove_eq_iff.mpr hj
  cases hi
  rw [← Category.assoc, horn.face'.hom_comp_boundaryInclusion, fixed.mul₀_spec,
      ← Category.assoc, ← Functor.map_comp]
  have : (⟨n + 1, by linarith⟩ : Fin (n + 2)) = ((⟨n + 1, by linarith⟩ : Fin (n + 2)).pred sorry).succ :=
      sorry
  split_ifs with h h'
  . rw [succAbove_of_succ_le, this, δ_comp_σ_of_le]; simp
    rw [fixed.δ_comp_eq, ← Category.assoc]
    congr 1
    repeat' simp [le_iff_val_le_val, h]
  . rw [δ_comp_σ_succ', CategoryTheory.Functor.map_id, Category.id_comp]
    simp [← h']; rw [succAbove_of_le_castSucc _ _ (by simp [le_iff_val_le_val])]
  . have aux : i.val < n := sorry
    rw [succAbove_of_succ_le, this, δ_comp_σ_of_le]; simp
    rw [fixed.δ_comp_eq, ← Category.assoc]
    congr 1
    repeat' simp [le_iff_val_le_val]; exact aux.le

end multiplication

section inverse

variable {n : ℕ} {X : SSet} {v : Δ[0] ⟶ X} (x : fixed (n + 1) X v)

def fixed.inv₀ : Λ[n + 2, last _] ⟶ X := by
  apply horn.HomMk' ?_ _ _
  exact fun i ↦ if i.val = n then x.val else Δ[n + 1].toΔ0 ≫ v
  intro i j hij
  split_ifs with h h'
  repeat' exact fixed.δ_comp_eq_δ_comp _ _ _ _
  repeat' rw [fixed.δ_comp_eq, ← Category.assoc]; congr 1
  rw [← Category.assoc, ← Category.assoc]; congr 1

lemma fixed.inv₀_spec (i : Fin (n + 2)):
    (horn.face'.hom _ _ (succAbove_ne _ i)) ≫ fixed.inv₀ x
      = if i.val = n then x.val else Δ[n + 1].toΔ0 ≫ v := by
  simp only [inv₀, horn.HomMk_spec', horn.face'.hom]

variable [KanComplex X] -- how to put this variable before the others???
def fixed.inv₁ : Δ[n + 2] ⟶ X :=
  choose (KanComplex.hornFilling (inv₀ x))

lemma fixed.inv₁_spec :
    inv₀ x = hornInclusion (n + 2) (last (n + 2)) ≫ inv₁ x :=
  choose_spec (KanComplex.hornFilling (inv₀ x))

lemma fixed.inv₁_spec' (i : Fin (n + 2)) :
    standardSimplex.map (SimplexCategory.δ i.castSucc) ≫ inv₁ x =
      if i.val = n then x.val else Δ[n + 1].toΔ0 ≫ v
    := by
  rw [← horn.face'.hom_comp_boundaryInclusion (h := (castSucc_lt_last  _).ne),
      Category.assoc, ← inv₁_spec]
  convert fixed.inv₀_spec x i using 3
  simp only [succAbove_last]

lemma fixed.inv₁_spec'_eq_or_of_neq (i : Fin (n + 2)) :
    standardSimplex.map (SimplexCategory.δ i.castSucc) ≫ fixed.inv₁ x = x.val ∨
    standardSimplex.map (SimplexCategory.δ i.castSucc) ≫ fixed.inv₁ x = Δ[n + 1].toΔ0 ≫ v := by
  rw [fixed.inv₁_spec']
  split_ifs
  <;> simp

def fixed.inv₂ : Δ[n + 1] ⟶ X := standardSimplex.map (δ (last _)) ≫ inv₁ x

def fixed.inv {n : ℕ} {X : SSet} [X.KanComplex] {v : Δ[0] ⟶ X} (x : fixed (n + 1) X v) :
    fixed (n + 1) X v :=
  ⟨fixed.inv₂ x, by
    rw [fixed.mem_iff]
    intro j; dsimp [inv₂]
    rw [← Category.assoc, ← Functor.map_comp, δ_comp_δ' (castSucc_lt_last _)]; simp
    rcases fixed.inv₁_spec'_eq_or_of_neq x j with hj | hj
    . rw [hj, fixed.δ_comp_eq x]
    . rw [hj, ← Category.assoc]; congr 1⟩

instance fixed.inst_inv : {n : ℕ} → [NeZero n] → {X : SSet}→ [KanComplex X] → {v : Δ[0] ⟶ X} →
    Inv (fixed n X v)
| 0, h, _, _, _ => by simp at h
| n + 1, _, _, _, _ => ⟨fixed.inv⟩

lemma mul_inv_cancel_aux₁ {n : ℕ} {X : SSet} [X.KanComplex] {v : Δ[0] ⟶ X} (x : fixed (n + 1) X v) :
    fixed.mul₀ x x⁻¹ = hornInclusion (n + 2) ⟨n + 1, by linarith⟩ ≫ fixed.inv₁ x := by
  apply horn.hom_ext'
  intro j h
  obtain ⟨j, hj⟩ := exists_succAbove_eq_iff.mpr h
  cases hj
  rw [← Category.assoc, horn.face'.hom_comp_boundaryInclusion, fixed.mul₀_spec]
  split_ifs with h h'
  . rw [succAbove_of_castSucc_lt _ _ (by simp [lt_iff_val_lt_val, h]), fixed.inv₁_spec']; simp [h]
  . rw [succAbove_of_lt_succ _ _ (by simp [lt_iff_val_lt_val, h'])]
    have : j.succ = last _ := by rw [← val_eq_val]; simpa
    rw [this]; rfl
  . rw [succAbove_of_castSucc_lt, fixed.inv₁_spec']; simp [h]
    exact (Nat.lt_succ.mp j.2).lt_of_ne h'

lemma mul_inv_cancel_aux₂ {n : ℕ} {X : SSet} [X.KanComplex] {v : Δ[0] ⟶ X}
  (x : fixed (n + 1) X v) :
    fixed.mulOfHornFilling (x := x) (y := x⁻¹) (fixed.inv₁ x) (mul_inv_cancel_aux₁ _) = 1 := by
  ext : 1
  dsimp [fixed.mulOfHornFilling]
  have : (⟨n + 1, by linarith⟩ : Fin (n + 3)) = (⟨n + 1, by linarith⟩ : Fin (n + 2)).castSucc := by
    simp only [castSucc_mk]
  rw [this, fixed.inv₁_spec']
  simp only [add_right_eq_self]; rfl

lemma mul_inv_cancel {n : ℕ} {X : SSet} [X.KanComplex] {v : Δ[0] ⟶ X} (x : fixed (n + 1) X v) :
    x * x⁻¹ ≈ 1 := by
  rw [← mul_inv_cancel_aux₂]
  apply fixed.mul_unique_up_to_equiv

end inverse

def HomotopyGroup (n : ℕ) [NeZero n] (X : SSet) [KanComplex X] (v : Δ[0] ⟶ X) : Type _ :=
  Quotient (fixed.setoid n X v)

def HomotopyClass₀ (X : SSet) [KanComplex X] : Type _ :=
  Quotient (Hom.setoid (n := 0) X)

namespace HomotopyGroup

variable (n : ℕ) [NeZero n] (X : SSet) [KanComplex X] (v : Δ[0] ⟶ X)

instance : Inhabited (HomotopyGroup n X v) := ⟨by
  apply Quotient.mk'
  use Δ[n].toΔ0 ≫ v
  dsimp
  rw [← Category.assoc]; congr
  ⟩

section multiplication
def mul_right (x : fixed n X v) :
  (HomotopyGroup n X v) → (HomotopyGroup n X v) :=
    Quotient.lift (fun y ↦ Quotient.mk' (x * y))
      (fun _ _ h ↦ Quotient.sound (fixed.mul_sound (Setoid.refl _) h))

def mul :
    (HomotopyGroup n X v) → (HomotopyGroup n X v) → (HomotopyGroup n X v) := by
  apply Quotient.lift (mul_right n X v)
  intro _ _ hab; dsimp [mul_right]
  congr! 1; funext _
  apply Quotient.sound (fixed.mul_sound hab (Setoid.refl _))

def inv : HomotopyGroup n X v → HomotopyGroup n X v := by
  apply Quotient.lift (fun x ↦ Quotient.mk' x⁻¹)
    sorry

variable {n X v}
instance inst_mul :
    Mul (HomotopyGroup n X v) := ⟨mul n X v⟩

---????
instance inst_mul' :
    Mul (Quotient (fixed.setoid n X v)) := ⟨mul n X v⟩

instance inst_one :
    One (HomotopyGroup n X v) := ⟨Quotient.mk' 1⟩

instance inst_inv : Inv (HomotopyGroup n X v) := ⟨inv n X v⟩

lemma mul_def (a b : fixed n X v) :
    (⟦a * b⟧ : HomotopyGroup n X v) = ⟦a⟧ * ⟦b⟧ := rfl

lemma mul_assoc :
    ∀ (a b c : HomotopyGroup n X v), a * b * c = a * (b * c) := by
  sorry

lemma one_mul :
    ∀ (a : HomotopyGroup n X v), 1 * a = a := by
  cases n
  . apply False.elim; rwa [← neZero_zero_iff_false (α := ℕ)] -- this is bad!!!
  . apply Quotient.ind
    rename ℕ => n
    intro a
    change ⟦1 * a⟧ = ⟦a⟧
    simp only [Quotient.eq]
    apply Setoid.trans (fixed.mul_unique_up_to_equiv _ _ _ (fixed.one_mul₀ a))
    convert Setoid.refl _
    ext : 1
    dsimp [fixed.mulOfHornFilling]
    rw [← Category.assoc, ← Functor.map_comp, δ_comp_σ_self',
        CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [castSucc_mk]

lemma mul_one :
    ∀ (a : HomotopyGroup n X v), a * 1 = a := by
  cases n
  . apply False.elim; rwa [← neZero_zero_iff_false (α := ℕ)] -- this is bad!!!
  . apply Quotient.ind
    rename ℕ => n
    intro a
    change ⟦a * 1⟧ = ⟦a⟧
    simp only [Quotient.eq]
    apply Setoid.trans (fixed.mul_unique_up_to_equiv _ _ _ (fixed.mul₀_one a))
    convert Setoid.refl _
    ext : 1
    dsimp [fixed.mulOfHornFilling]
    rw [← Category.assoc, ← Functor.map_comp, δ_comp_σ_succ',
        CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [succ_mk, Nat.succ_eq_add_one]

lemma mul_inv_cancel :
    ∀ (a : HomotopyGroup n X v), a * a⁻¹ = 1 := by
  cases n
  . apply False.elim; rwa [← neZero_zero_iff_false (α := ℕ)] -- this is bad!!!
  . apply Quotient.ind
    rename ℕ => n
    intro a
    change ⟦a * a⁻¹⟧ = ⟦1⟧
    simp only [Quotient.eq]
    apply mul_inv_cancel

instance inst_monoid : Monoid (HomotopyGroup n X v) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one

instance inst_group : Group (HomotopyGroup n X v) where
  inv_mul_cancel := by
    intro a
    have h₁ : a⁻¹* (a⁻¹)⁻¹ = 1 := mul_inv_cancel _
    have h₂ : a = (a⁻¹)⁻¹ := left_inv_eq_right_inv (mul_inv_cancel _) h₁
    rw [← h₁, ← h₂]

end multiplication

end HomotopyGroup

section functor

variable (n : ℕ) [NeZero n] {X Y : SSet} [KanComplex X] [KanComplex Y]
  (f : X ⟶ Y) {x : Δ[0] ⟶ X} {y : Δ[0] ⟶ Y} (hf : x ≫ f = y)

def HomotopyGroup.map_toFun₀ : fixed n X x → HomotopyGroup n Y y := by
  match n with
  | 0 => sorry
  | succ n =>
      intro ⟨a, ha⟩
      apply Quotient.mk'
      use a ≫ f
      rw [fixed.mem_iff] at ha ⊢
      intro j
      rw [← Category.assoc, ha, Category.assoc, hf]

def HomotopyGroup.map : HomotopyGroup n X x →* HomotopyGroup n Y y where
  toFun := by
    apply Quotient.lift (HomotopyGroup.map_toFun₀ )


  map_one' := _
  map_mul' := _




end functor

end SimplicialHomotopyGroup


end SSet
end
