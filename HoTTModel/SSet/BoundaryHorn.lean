import HoTTModel.SSet.Degenerates

namespace SSet
open CategoryTheory Simplicial Limits SimplexCategory Function Opposite Classical
open standardSimplex Fin Set

section Edge
variable (i : Fin (n + 2)) (j : Fin (n + 3))

def Edge :
    Δ[n + 2] _[n] :=
  objMk (j.succAboveOrderEmb.toOrderHom.comp i.succAboveOrderEmb.toOrderHom)

def Edge.hom : Δ[n] ⟶ Δ[n + 2] := standardSimplex.map (δ i) ≫ standardSimplex.map (δ j)

lemma Edge.hom_eq_yonedaEquiv :
    Edge.hom i j = (yonedaEquiv _ _).symm (Edge i j) := rfl

def boundary.edge :
    ∂Δ[n + 2] _[n] :=
  ⟨Edge i j, by
    simp [asOrderHom_objMk, Edge, OrderHom.comp]
    apply (not_imp_not.mpr Surjective.of_comp)
    simp [Surjective]⟩

def boundary.edge.hom : Δ[n] ⟶ ∂Δ[n + 2] := (yonedaEquiv _ _).symm (boundary.edge i j)

def horn.edge' {k} (i : Fin (n + 2)) (j : Fin (n + 3)) :
    Λ[n + 2, k] _[n] :=
  ⟨Edge i j, by
    simp [asOrderHom_objMk, Edge, OrderHom.comp]
    by_contra h
    apply_fun Set.toFinset at h
    apply_fun Finset.card at h
    simp at h
    have := h ▸ Finset.card_insert_le _ _
    erw [Finset.card_image_of_injective _
        (Injective.comp j.succAboveOrderEmb.inj' i.succAboveOrderEmb.inj')] at this
    simp at this⟩

def horn.edge'_hom {k} (i : Fin (n + 2)) (j : Fin (n + 3)) :
    Δ[n] ⟶ Λ[n + 2, k] := (yonedaEquiv _ _).symm (horn.edge' i j)

-- put it somewhere else
lemma _root_.Fin.range_succAbove_succAbove_of_castSucc_lt (i : Fin (n + 1)) (j : Fin (n + 2))
  (hij : i.castSucc < j) :
    range (j.succAbove ∘ i.succAbove) = {i.castSucc, j}ᶜ := by
  simp only [range_comp, range_succAbove, compl_eq_univ_diff,
             image_diff succAbove_right_injective, image_univ,
             range_succAbove, image_singleton, diff_diff,
             union_comm {j}]
  congr
  rw [succAbove_of_castSucc_lt _ _ hij]

lemma Edge.range_asOrderHom_of_castSucc_lt (hij : i.castSucc < j):
    range (asOrderHom $ Edge i j) = {i.castSucc, j}ᶜ :=
  range_succAbove_succAbove_of_castSucc_lt i j hij

end Edge

section Face

variable (i : Fin (n + 2))

def Face : Δ[n + 1] _[n] :=
    objMk i.succAboveOrderEmb.toOrderHom

def Face.hom : Δ[n] ⟶ Δ[n + 1] := standardSimplex.map (δ i)

lemma Face.hom_eq_yonedaEquiv :
    Face.hom i = (yonedaEquiv _ _).symm (Face i) := rfl

def boundary.face : ∂Δ[n + 1] _[n] :=
  ⟨Face i, by
    simp [asOrderHom_objMk, Face, OrderHom.comp, Surjective]⟩

def boundary.face.hom : Δ[n] ⟶ ∂Δ[n + 1] := (yonedaEquiv _ _).symm (boundary.face i)

lemma boundary.face.hom_comp_boundaryInclusion :
    face.hom i ≫ boundaryInclusion (n + 1) = standardSimplex.map (δ i) := rfl

def horn.face' (j: Fin (n + 2)) (h : j ≠ i):
    Λ[n + 1, i] _[n] :=
  ⟨Face j, by
    -- make it a simp lemma
    have : asOrderHom (objMk j.succAboveOrderEmb.toOrderHom)
      = j.succAboveOrderEmb.toOrderHom := rfl
    erw [this]
    simp [insert_eq_of_mem, ne_univ_iff_exists_not_mem, Surjective]
    exact h⟩

def horn.face'.hom (j : Fin (n + 2)) (h : j ≠ i) :
    Δ[n] ⟶ Λ[n + 1, i] := (yonedaEquiv _ _).symm (horn.face' i j h)

lemma horn.face'.hom_comp_boundaryInclusion :
    face'.hom i j h ≫ hornInclusion (n + 1) i = standardSimplex.map (δ j) := rfl

end Face

section Degenerate

lemma nondegenerate_face (i : Fin (n + 2)) :
    Nondegenerate (X := Δ[n + 1]) (Face i) :=
  (Nondegenerate.iff_StrictMono _).mpr i.succAboveOrderEmb.strictMono

lemma exists_face_of_nondegenerate (x : Δ[n + 1] _[n]) :
    Nondegenerate x → ∃ i, x = Face i := by
  rw [Nondegenerate.iff_StrictMono]
  intro h
  use toFace (OrderEmbedding.ofStrictMono _ h) 0
  ext : 2
  simp [Face, asOrderHom_objMk]
  exact (toFace.function (OrderEmbedding.ofStrictMono _ h)).symm

lemma Face.range_asOrderHom (i : Fin (n + 2)) :
    range (asOrderHom (Face i)) = {i}ᶜ := range_succAbove i

lemma Edge.Nondegenerate (i : Fin (n + 2)) (j : Fin (n + 3)) :
    Nondegenerate (Edge i j) := by
  rw [Nondegenerate.iff_StrictMono]
  apply StrictMono.comp j.succAboveOrderEmb.strictMono i.succAboveOrderEmb.strictMono

end Degenerate

section Generator

def boundaryGenerator (n : ℕ) : Generator ∂Δ[n + 1] where
  carrier := {⟨n, boundary.face i⟩ | i : Fin (n + 2)}
  connect := by
    intro ⟨k, ⟨y, hy⟩⟩
    simp only [Surjective, len_mk, not_forall, not_exists] at hy
    obtain ⟨i, hi⟩ := hy
    simp only [len_mk, mem_setOf_eq, exists_exists_eq_and]
    use i
    simp only [connect, boundary, Subtype.mk.injEq]
    use op (factor_δ (objEquiv _ _ y) i)
    apply_fun objEquiv _ _
    convert (factor_δ_spec (objEquiv _ _ y) i hi).symm

def hornGenerator (n : ℕ) (j) : Generator Λ[n + 1, j] where
  carrier := {⟨n, horn.face' j i.val i.property⟩| i : { i : Fin (n + 2) // i ≠ j}}
  connect := by
    intro ⟨k, ⟨y, hy⟩⟩
    rw [ne_univ_iff_exists_not_mem] at hy
    simp at hy
    obtain ⟨i, ⟨hi₁, hi₂⟩⟩ := hy
    simp only [len_mk, mem_setOf_eq, exists_exists_eq_and]
    use ⟨i, hi₁⟩
    simp only [connect, horn, Subtype.mk.injEq]
    use op (factor_δ (objEquiv _ _ y) i)
    apply_fun objEquiv _ _
    convert (factor_δ_spec (objEquiv _ _ y) i hi₂).symm

end Generator

section HomExt

lemma boundary.hom_ext (f g : ∂Δ[n + 1] ⟶ X) :
    (∀ i, face.hom i ≫ f = face.hom i ≫ g) → f = g := by
  intro h
  apply hom_generator_ext (boundaryGenerator _)
  intro x ⟨i, hi⟩
  cases hi
  apply_fun (yonedaEquiv _ _).symm
  erw [yonedaEquiv_symm_naturality'₂, yonedaEquiv_symm_naturality'₂, h i]
  rfl

lemma horn.hom_ext' (f g : Λ[n + 1, i] ⟶ X) :
    (∀ j h, face'.hom i j h ≫ f = face'.hom i j h ≫ g) → f = g := by
  intro h
  apply hom_generator_ext (hornGenerator _ _)
  intro x ⟨⟨k, hki⟩, hi⟩
  cases hi
  apply_fun (yonedaEquiv _ _).symm
  erw [yonedaEquiv_symm_naturality'₂, yonedaEquiv_symm_naturality'₂, h k hki]
  rfl

end HomExt

section HomMk

lemma test_aux2 (i j : Fin (n + 3)) (hij : i < j) :
  Edge (i.castPred (ne_last_of_lt hij)) j
    = Δ[n + 2].map (δ (j.pred (ne_zero_of_lt hij))).op (Face i) := by
  apply standardSimplex.ext
  simp [Face, map_apply, Edge, δ, asOrderHom_objMk]
  erw [asOrderHom_objMk]
  ext : 1
  simp [Hom.toOrderHom_mk (a := [n + 1]) (b := [n + 2]) (i.succAboveOrderEmb.toOrderHom),
        Hom.toOrderHom_mk (a := [n]) (b := [n + 1]) (j.pred _).succAboveOrderEmb.toOrderHom]
  ext k : 1
  simp [succAboveOrderEmb_apply, OrderEmbedding.toOrderHom, DFunLike.coe]
  by_cases hk : k.castSucc < i.castPred (ne_last_of_lt hij)
  . rw [succAbove_of_castSucc_lt _ _ hk, succAbove_of_castSucc_lt _ _
          (by rw [lt_iff_val_lt_val]; apply (lt_iff_val_lt_val.mp hk).trans hij)]
    rw [succAbove_of_castSucc_lt _ k
          (lt_of_lt_of_le hk (by rw [le_pred_iff]; simpa [le_iff_val_le_val, Nat.succ_le_iff])),
        succAbove_of_castSucc_lt _ _ (by rwa [lt_iff_val_lt_val] at hk ⊢)]
  . rw [not_lt] at hk
    by_cases hk' : k.succ.castSucc < j
    rw [succAbove_of_le_castSucc _ k hk, succAbove_of_castSucc_lt _ _ hk',
        succAbove_of_castSucc_lt _ k ((lt_pred_iff _).mpr hk'),
        succAbove_of_le_castSucc _ _ (by rwa [le_iff_val_le_val] at hk ⊢)]
    rfl
    . rw [not_lt] at hk'
      rw [succAbove_of_le_castSucc _ k hk, succAbove_of_le_castSucc _ _ hk',
          succAbove_of_le_castSucc _ k ((pred_le_iff _).mpr hk'),
          succAbove_of_le_castSucc _ _ (hij.le.trans hk')]

example (i j : Fin (n + 3)) (hij : i < j) :
  Edge (i.castPred (ne_last_of_lt hij)) j
    = Δ[n + 2].map (δ (i.castPred (ne_last_of_lt hij))).op (Face j) := by
  rfl

-- simplify this;;; the first prop in `∧`-sequnece  is useless
lemma test_aux3 (i j : Fin (n + 3)) (hij : i < j) (z : Δ[n + 2] _[k]) (φ₁) (φ₂) :
    z = Δ[n + 2].map φ₁ (Face i) →
      z = Δ[n + 2].map φ₂ (Face j) →
      ∃ φ, z = Δ[n + 2].map φ (Edge (i.castPred (ne_last_of_lt hij)) j) ∧
              (φ₁ = (δ (j.pred (ne_zero_of_lt hij))).op ≫ φ) ∧
                 (φ₂ = (δ (i.castPred (ne_last_of_lt hij))).op ≫ φ) := by
  intro hi hj
  have aux1 :=
    (connect_iff_range_subset ⟨n + 1, Face i⟩ ⟨_, z⟩).mp ⟨φ₁, hi⟩
  have aux2 :=
    (connect_iff_range_subset ⟨n + 1, Face j⟩ ⟨_, z⟩).mp ⟨φ₂, hj⟩
  simp [asOrderHom_objMk] at aux1 aux2
  erw [Fin.range_succAbove] at aux1 aux2
  obtain ⟨φ, hφ⟩ : Δ[n + 2].connect ⟨_, (Edge (i.castPred (ne_last_of_lt hij)) j)⟩ ⟨_ ,z⟩ := by
    rw [connect_iff_range_subset]
    simp [Edge, asOrderHom_objMk]
    convert subset_inter aux1 aux2
    convert range_succAbove_succAbove_of_castSucc_lt (i.castPred (ne_last_of_lt hij)) j hij using 1
    rw [← compl_inj_iff, compl_compl, ← union_eq_compl_compl_inter_compl]
    rfl
  use φ
  constructor
  . exact hφ
  . constructor
    . apply test_aux1 _ (nondegenerate_face i)
      simp only [FunctorToTypes.map_comp_apply]
      erw [← hi, ← test_aux2 _ _ hij]
      exact hφ
    . apply test_aux1 _ (nondegenerate_face j)
      simp only [FunctorToTypes.map_comp_apply]
      erw [← hj]
      exact hφ

variable {Y : SSet}

lemma test_aux4 (f : {k : ℕ} → (boundaryGenerator (n + 1)).carrier.level k → Y _[k]) :
    CompatibleOn _ f {⟨n, boundary.edge i j⟩ | (i : Fin (n + 2)) (j : Fin (n + 3))}
      → Compatible _ f := by
    intro h
    intro ⟨⟨n₁, x⟩, ⟨i, hi⟩⟩ ⟨⟨n₂, y⟩, ⟨j, hj⟩⟩ z φ₁ φ₂ hφ₁ hφ₂
    simp; simp at φ₁ φ₂
    cases hi; cases hj
    dsimp [boundary] at hφ₁ hφ₂
    by_cases hij : i = j
    . cases hij
      have : φ₁ = φ₂ := by
        apply test_aux1 _ (nondegenerate_face i)
        apply_fun Subtype.val at hφ₁ hφ₂
        exact hφ₁.symm.trans hφ₂
      rw [this]
    . rcases lt_or_gt_of_ne hij with hij | hij
      . obtain ⟨ψ, ⟨_, hψ₂⟩⟩ := test_aux3 _ _ hij _ _ _
          (congrArg Subtype.val hφ₁) (congrArg Subtype.val hφ₂)
        rw [hψ₂.1, hψ₂.2]
        simp only [FunctorToTypes.map_comp_apply]
        congr! 1
        exact h ⟨⟨_, boundary.face i⟩, by simp [boundaryGenerator]⟩
          ⟨⟨_, boundary.face j⟩, by simp [boundaryGenerator]⟩
          ⟨_, boundary.edge (i.castPred (ne_last_of_lt hij)) j⟩
          ⟨_, _, rfl⟩
          (δ (j.pred (ne_zero_of_lt hij))).op
          (δ (i.castPred (ne_last_of_lt hij))).op
          (by simp [boundary.edge, boundary.face, boundary]; apply test_aux2 _ _ hij)
          rfl
      . --- how to simplify this kind of symmetric proof??
        obtain ⟨ψ, ⟨_, hψ₂⟩⟩ := test_aux3 _ _ hij _ _ _
          (congrArg Subtype.val hφ₂) (congrArg Subtype.val hφ₁)
        rw [hψ₂.1, hψ₂.2]
        simp only [FunctorToTypes.map_comp_apply]
        congr! 1
        symm
        exact h ⟨⟨_, boundary.face j⟩, by simp [boundaryGenerator]⟩
          ⟨⟨_, boundary.face i⟩, by simp [boundaryGenerator]⟩
          ⟨_, boundary.edge (j.castPred (ne_last_of_lt hij)) i⟩
          ⟨_, _, rfl⟩
          (δ (i.pred (ne_zero_of_lt hij))).op
          (δ (j.castPred (ne_last_of_lt hij))).op
          (by simp [boundary.edge, boundary.face, boundary]; apply test_aux2 _ _ hij)
          rfl

-- extend the map on boundary along the faces

lemma boundary.face.injective : Injective (boundary.face (n := n)) := by
  intro i j hij
  apply_fun fun x ↦ ⇑(asOrderHom (Subtype.val x)) at hij
  simp only [face, Face, asOrderHom_objMk] at hij
  apply succAbove_left_injective hij

-- this is interesting
noncomputable def equiv_test : Fin (n + 2) ≃ (boundaryGenerator n).carrier.level n where
  toFun i := ⟨boundary.face i, ⟨i, rfl⟩⟩
  invFun x := by
    have : ∃ i, boundary.face i = x.1 := by
      obtain ⟨i, hi⟩ := x.2
      exact ⟨i, heq_eq_eq _ _ ▸ (Sigma.mk.inj_iff.mp hi).2⟩
    exact (choose this)
  left_inv := by
    simp only [LeftInverse]
    intro i
    apply boundary.face.injective
    have := choose_spec
      (⟨boundary.face i, ⟨i, rfl⟩⟩ : (boundaryGenerator n).carrier.level n).property
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
    rw [this]
  right_inv := by
    simp [Function.RightInverse, LeftInverse]
    intro x hx
    have : ∃ i, boundary.face i = x := by
      obtain ⟨i, hi⟩ := hx
      exact ⟨i, heq_eq_eq _ _ ▸ (Sigma.mk.inj_iff.mp hi).2⟩
    exact choose_spec this

noncomputable def CompatibleFun.boundaryMkFun {n : ℕ} (f : Fin (n + 2) → Y _[n]) :
    {k : ℕ} → (boundaryGenerator n).carrier.level k → Y _[k] := by
  intro k x
  have := x.2
  dsimp [boundaryGenerator, level] at this
  simp only [Sigma.mk.inj_iff, exists_and_left] at this
  cases this.1
  exact f (equiv_test.invFun x)

lemma CompatibleFun.boundaryMkFun_eq (f : Fin (n + 2) → Y _[n]) {h}:
    (CompatibleFun.boundaryMkFun f) ⟨boundary.face i, h⟩ = f i := by
  dsimp [boundaryMkFun]
  congr
  apply equiv_test.left_inv

lemma test_aux5 (k) (i : Fin (n + 2)) (j : Fin (n + 3)) (hij : i.castSucc < j) (φ):
    Edge i j = Δ[n + 2].map φ (Face k) → k = i.castSucc ∨ k = j := by
  intro h
  apply range_subset_of_connect at h
  rw [Face.range_asOrderHom, Edge.range_asOrderHom_of_castSucc_lt _ _ hij,
      compl_subset_compl] at h
  simp only [singleton_subset_iff, mem_insert_iff, mem_singleton_iff] at h
  exact h

lemma test_aux5'' (x : Δ[n + 2] _[n + 1]) (hx : Nondegenerate x) (i : Fin (n + 2)) (j : Fin (n + 3))
  (hij : i.castSucc < j) (φ):
    Edge i j = Δ[n + 2].map φ x → x = Face i.castSucc ∨ x = Face j := by
  intro h
  obtain ⟨k, hk⟩ := exists_face_of_nondegenerate x hx
  cases hk
  apply test_aux5 _ _ _ hij at h
  cases h
  <;> rename Eq _ _ => h
  <;> simp [h]

lemma succAbove_succAbove_comm_of_castSucc_lt (i : Fin (n + 1)) (j : Fin (n + 2))
  (h : i.castSucc < j) :
    j.succAbove ∘ i.succAbove = i.castSucc.succAbove ∘ (j.pred (ne_zero_of_lt h)).succAbove :=
  sorry

lemma succAbove_succAbove_comm_of_lt_succ (i : Fin (n + 1)) (j : Fin (n + 2))
  (h : j < i.succ) :
    j.succAbove ∘ i.succAbove = i.succ.succAbove ∘ (j.castPred (ne_last_of_lt h)).succAbove :=
  sorry

-- corrolary of the next lemma
lemma test_aux5' (i : Fin (n + 2)) (j : Fin (n + 3))
  (hij : i.castSucc < j) (φ):
    Edge i j = Δ[n + 2].map φ (Face i.castSucc) → φ = (δ (j.pred (ne_zero_of_lt hij))).op := by
  intro h
  simp [map_apply, Edge, Face] at h
  apply Quiver.Hom.unop_inj
  ext : 2
  apply_fun fun f ↦ ⇑(Hom.toOrderHom f) at h
  simp at h
  simp [δ]
  erw [succAbove_succAbove_comm_of_castSucc_lt _ _ hij] at h
  apply Function.Injective.comp_left i.castSucc.succAboveOrderEmb.inj' h.symm

lemma test_aux5'rev (i : Fin (n + 2)) (j : Fin (n + 3)) (φ):
    Edge i j = Δ[n + 2].map φ (Face j) → φ = (δ i).op := by
  intro h
  simp [map_apply, Edge, Face] at h
  apply Quiver.Hom.unop_inj
  ext : 2
  apply_fun fun f ↦ ⇑(Hom.toOrderHom f) at h
  simp at h
  simp [δ]
  apply Function.Injective.comp_left j.succAboveOrderEmb.inj' h.symm

lemma test_aux6 (i : Fin (n + 2)) (j : Fin (n + 3)) :
  Edge i j = Edge (if h : i.castSucc < j then i else
    (j.castPred (ne_last_of_lt (lt_of_le_of_lt (not_lt.mp h) (castSucc_lt_succ _)))))
    (if i.castSucc < j then j else i.succ) := by
  split_ifs with h
  . rfl
  . simp [Edge]
    ext : 2
    apply succAbove_succAbove_comm_of_lt_succ _ _
      ((lt_of_le_of_lt (not_lt.mp h) (castSucc_lt_succ _)))

lemma test_aux7 (i : Fin (n + 2)) (j : Fin (n + 3)) :
    (if h : i.castSucc < j then i else
      (j.castPred (ne_last_of_lt (lt_of_le_of_lt (not_lt.mp h) (castSucc_lt_succ _))))).castSucc
      < (if i.castSucc < j then j else i.succ) := by
  split_ifs with h
  . exact h
  . exact ((lt_of_le_of_lt (not_lt.mp h) (castSucc_lt_succ _)))

lemma test_aux8 [Preorder α] {a b c d : α} (h : a < b) (h' : c < d) :
    (a = c ∨ a = d) → (b = c ∨ b = d) → a = c ∧ b = d := by
  rintro (h₁ | h₁) (h₂ | h₂)
  . rw [h₁, h₂, lt_self_iff_false] at h; trivial
  . exact ⟨h₁, h₂⟩
  . rw [h₁, h₂] at h; apply False.elim ((lt_self_iff_false _).mp (h.trans h'))
  . rw [h₁, h₂, lt_self_iff_false] at h; trivial

-- for zero cases, we don't need `h`... how to intergrate the two cases?
noncomputable def CompatibleFun.boundaryMk {n : ℕ} (f : Fin (n + 3) → Y _[n + 1])
  (h : ∀ i j : Fin (n + 3), (hij : i < j) →
    Y.map (δ (j.pred (ne_zero_of_lt hij))).op (f i) =
      Y.map (δ (i.castPred (ne_last_of_lt hij))).op (f j)):
    CompatibleFun (boundaryGenerator (n + 1)).carrier Y where
  func := boundaryMkFun f
  compatible := by
    apply test_aux4
    intro ⟨x, ⟨xk, hxk⟩⟩ ⟨y, ⟨yk, hyk⟩⟩  z ⟨i, j, hij⟩ φ₁ φ₂ hφ₁ hφ₂
    cases hij; cases hxk; cases hyk
    simp at φ₁ φ₂; simp [boundary, boundary.edge, boundary.face] at hφ₁ hφ₂
    simp [CompatibleFun.boundaryMkFun_eq]
    by_cases hxy : xk = yk
    . cases hxy; congr!
      apply test_aux1 _ _ _ _ _ (hφ₁.symm.trans hφ₂)
      exact nondegenerate_face _
    . rw [test_aux6] at hφ₁ hφ₂
      rcases lt_or_gt_of_ne hxy with hxy | hxy
      . have := test_aux8 hxy (test_aux7 i j) (test_aux5 _ _ _ (test_aux7 _ _) _ hφ₁)
          (test_aux5 _ _ _ (test_aux7 _ _) _ hφ₂)
        rw [← this.2] at hφ₁ hφ₂
        rw [this.1] at hφ₁ hxy ⊢
        convert h _ _ hxy
        apply test_aux5' _ _ hxy _ hφ₁
        apply test_aux5'rev _ _ _ hφ₂
      . have := test_aux8 hxy (test_aux7 i j) (test_aux5 _ _ _ (test_aux7 _ _) _ hφ₂)
          (test_aux5 _ _ _ (test_aux7 _ _) _ hφ₁)
        rw [← this.2] at hφ₁ hφ₂
        rw [this.1] at hxy hφ₂ ⊢
        symm
        convert h _ _ hxy
        apply test_aux5' _ _ hxy _ hφ₂
        apply test_aux5'rev _ _ _ hφ₁


noncomputable def boundary.HomMk  {n : ℕ} (f : Fin (n + 3) → Y _[n + 1])
  (h : ∀ i j : Fin (n + 3), (hij : i < j) →
    Y.map (δ (j.pred (ne_zero_of_lt hij))).op (f i) =
      Y.map (δ (i.castPred (ne_last_of_lt hij))).op (f j)) :
    ∂Δ[n + 2] ⟶ Y := Extend (boundaryGenerator (n + 1)) (CompatibleFun.boundaryMk f h)

noncomputable def CompatibleFun.boundaryMkZero (a b : Y _[0]) :
    CompatibleFun (boundaryGenerator 0).carrier Y where
  func := boundaryMkFun ![a, b]
  compatible := by
    intro ⟨x, ⟨xk, hxk⟩⟩ ⟨y, ⟨yk, hyk⟩⟩ z φ₁ φ₂ h₁ h₂
    cases hxk; cases hyk
    by_cases hxy : xk = yk
    . cases hxy; congr!
      simp at φ₁ φ₂
      apply Quiver.Hom.unop_inj
      ext; simp only [coe_fin_one]
    . apply_fun Subtype.val at h₁ h₂
      apply range_subset_of_connect at h₁
      apply range_subset_of_connect at h₂
      simp [boundary, boundary.face, Face, asOrderHom_objMk] at h₁ h₂
      erw [range_succAbove] at h₁ h₂
      have : range ⇑(asOrderHom z.snd.val) = ∅ := by
        apply eq_empty_of_subset_empty
        convert subset_inter h₁ h₂
        rw [← compl_inj_iff, compl_empty, ← union_eq_compl_compl_inter_compl, eq_comm,
            ← toFinset_inj]
        apply Finset.eq_univ_of_card
        simp only [union_singleton, toFinset_insert, toFinset_singleton,
          Fintype.card_fin]
        rw [Finset.card_insert_of_not_mem (by simpa [Finset.mem_singleton, eq_comm]),
            Finset.card_singleton]
      simp only [range_eq_empty_iff, not_isEmpty_of_nonempty] at this

noncomputable def boundary.HomMkZero (a b : Y _[0]) :
    ∂Δ[1] ⟶ Y := Extend _ (CompatibleFun.boundaryMkZero a b)

lemma test2_aux1 (f : {k : ℕ} → (hornGenerator (n + 1) l).carrier.level k → Y _[k]) :
    CompatibleOn _ f {⟨n, horn.edge' i j⟩ | (i : Fin (n + 2)) (j : Fin (n + 3))}
      → Compatible _ f := by
    intro h
    intro ⟨⟨n₁, x⟩, ⟨⟨i, hi₀⟩, hi⟩⟩ ⟨⟨n₂, y⟩, ⟨⟨j, hj₀⟩, hj⟩⟩ z φ₁ φ₂ hφ₁ hφ₂
    simp; simp at φ₁ φ₂
    cases hi; cases hj
    dsimp [horn] at hφ₁ hφ₂
    by_cases hij : i = j
    . cases hij
      have : φ₁ = φ₂ := by
        apply test_aux1 _ (nondegenerate_face i)
        apply_fun Subtype.val at hφ₁ hφ₂
        exact hφ₁.symm.trans hφ₂
      rw [this]
    . rcases lt_or_gt_of_ne hij with hij | hij
      . obtain ⟨ψ, ⟨_, hψ₂⟩⟩ := test_aux3 _ _ hij _ _ _
          (congrArg Subtype.val hφ₁) (congrArg Subtype.val hφ₂)
        rw [hψ₂.1, hψ₂.2]
        simp only [FunctorToTypes.map_comp_apply]
        congr! 1
        exact h ⟨⟨_, horn.face' l i hi₀⟩, ⟨⟨i, hi₀⟩, rfl⟩⟩
          ⟨⟨_, horn.face' l j hj₀⟩, ⟨⟨j, hj₀⟩, rfl⟩⟩
          ⟨_, horn.edge' (i.castPred (ne_last_of_lt hij)) j⟩
          ⟨_, _, rfl⟩
          (δ (j.pred (ne_zero_of_lt hij))).op
          (δ (i.castPred (ne_last_of_lt hij))).op
          (by simp [horn.edge', horn.face', horn]; apply test_aux2 _ _ hij)
          rfl
      . --- how to simplify this kind of symmetric proof??
        obtain ⟨ψ, ⟨_, hψ₂⟩⟩ := test_aux3 _ _ hij _ _ _
          (congrArg Subtype.val hφ₂) (congrArg Subtype.val hφ₁)
        rw [hψ₂.1, hψ₂.2]
        simp only [FunctorToTypes.map_comp_apply]
        congr! 1
        symm
        exact h ⟨⟨_, horn.face' l j hj₀⟩, ⟨⟨j, hj₀⟩, rfl⟩⟩
          ⟨⟨_, horn.face' l i hi₀⟩, ⟨⟨i, hi₀⟩, rfl⟩⟩
          ⟨_, horn.edge' (j.castPred (ne_last_of_lt hij)) i⟩
          ⟨_, _, rfl⟩
          (δ (i.pred (ne_zero_of_lt hij))).op
          (δ (j.castPred (ne_last_of_lt hij))).op
          (by simp [horn.edge', horn.face', horn]; apply test_aux2 _ _ hij)
          rfl

lemma horn.face'.injective :
    ∀ j i i' : Fin (n + 2), ∀ h h', horn.face' j i h =  horn.face' j i' h' → i = i' := by
  intro _ _ _ _ _ hij
  apply_fun fun x ↦ ⇑(asOrderHom (Subtype.val x)) at hij
  simp only [face, Face, asOrderHom_objMk] at hij
  apply succAbove_left_injective hij

noncomputable def equiv_test2 : Fin (n + 1) ≃ (hornGenerator n j).carrier.level n where
  toFun i := ⟨horn.face' j _ (succAbove_ne j i), ⟨⟨_, succAbove_ne j i⟩, rfl⟩⟩
  invFun x := by
    have : ∃ i, horn.face' j _ (succAbove_ne j i) = x.1 := by
      obtain ⟨⟨i', hi'₀⟩, hi'⟩ := x.2
      obtain ⟨i, hi⟩ := exists_succAbove_eq_iff.mpr hi'₀
      use i
      convert (heq_eq_eq _ _ ▸ (Sigma.mk.inj_iff.mp hi').2)
    exact (choose this)
  left_inv := by
    simp only [LeftInverse]
    intro i
    apply succAbove_right_injective (p := j)
    apply horn.face'.injective (j := j) _ _ (succAbove_ne j _) (succAbove_ne j _)
    exact choose_spec
      (⟨i, rfl⟩ : ∃ i', horn.face' j _ (succAbove_ne j i') = horn.face' j _ (succAbove_ne j i) )
  right_inv := by
    simp [Function.RightInverse, LeftInverse]
    intro x hx
    have : ∃ i, horn.face' j _ (succAbove_ne j i) = x := by
      obtain ⟨⟨i', hi'₀⟩, hi'⟩ := hx
      obtain ⟨i, hi⟩ := exists_succAbove_eq_iff.mpr hi'₀
      use i
      convert (heq_eq_eq _ _ ▸ (Sigma.mk.inj_iff.mp hi').2)
    exact (choose_spec this)

noncomputable def CompatibleFun.hornMkFun {n : ℕ} (f : Fin (n + 1) → Y _[n]) (j):
    {k : ℕ} → (hornGenerator n j).carrier.level k → Y _[k] := by
  intro k x
  have := x.2
  dsimp [hornGenerator, level] at this
  simp only [Sigma.mk.inj_iff, exists_and_left] at this
  cases this.1
  exact f (equiv_test2.invFun x)

lemma CompatibleFun.hornMkFun_eq (f : Fin (n + 1) → Y _[n])
    (j : Fin (n + 2)) (i : Fin (n + 1)) {h} :
  (CompatibleFun.hornMkFun f j) ⟨horn.face' j _ (succAbove_ne j i), h⟩ = f i := by
  dsimp [horn.face', hornMkFun]
  congr
  exact equiv_test2.left_inv i

noncomputable def CompatibleFun.hornMk {n : ℕ} (f : Fin (n + 2) → Y _[n + 1]) (k : Fin (n + 3))
  (h : ∀ i j : Fin (n + 2), (hij : i < j) →
    Y.map (δ ((k.succAbove j).pred
      (ne_zero_of_lt (strictMono_succAbove _ hij)))).op (f i)
      = Y.map (δ ((k.succAbove i).castPred
        (ne_last_of_lt (strictMono_succAbove _ hij)))).op (f j)) :
    CompatibleFun (hornGenerator (n + 1) k).carrier Y where
      func := CompatibleFun.hornMkFun f k
      compatible := by
        apply test2_aux1
        intro ⟨x, ⟨⟨xk, hxk₀⟩, hxk⟩⟩ ⟨y, ⟨⟨yk, hyk₀⟩, hyk⟩⟩ z ⟨i, j, hij⟩ φ₁ φ₂ h₁ h₂
        obtain ⟨xk, hxk₀⟩ := exists_succAbove_eq_iff.mpr hxk₀
        obtain ⟨yk, hyk₀⟩ := exists_succAbove_eq_iff.mpr hyk₀
        cases hxk₀; cases hyk₀; cases hxk; cases hyk; cases hij
        simp [horn.face', horn, ← Subtype.val_inj] at h₁ h₂
        simp at φ₁ φ₂
        simp [CompatibleFun.hornMkFun_eq]
        by_cases hxy : xk = yk
        . cases hxy; congr!
          apply test_aux1 _ _ _ _ _ (h₁.symm.trans h₂)
          exact nondegenerate_face _
        . simp [horn.edge'] at h₁ h₂; rw [test_aux6] at h₁ h₂
          rcases lt_or_gt_of_ne hxy with hxy | hxy
          . have hxy' := strictMono_succAbove k hxy
            have := test_aux8 hxy' (test_aux7 i j) (test_aux5 _ _ _ (test_aux7 _ _) _ h₁)
              (test_aux5 _ _ _ (test_aux7 _ _) _ h₂)
            rw [← this.2] at h₁ h₂
            rw [this.1] at hxy' h₁
            convert h _ _ hxy
            apply test_aux5' _ _ hxy' _ h₁
            simp [this.1]
            apply test_aux5'rev _ _ _ h₂
          . have hxy' := strictMono_succAbove k hxy
            have := test_aux8 hxy' (test_aux7 i j) (test_aux5 _ _ _ (test_aux7 _ _) _ h₂)
              (test_aux5 _ _ _ (test_aux7 _ _) _ h₁)
            rw [← this.2] at h₁ h₂
            rw [this.1] at hxy' h₂
            symm
            convert h _ _ hxy
            apply test_aux5' _ _ hxy' _ h₂
            simp [this.1]
            apply test_aux5'rev _ _ _ h₁

noncomputable def horn.HomMk {n : ℕ} (f : Fin (n + 2) → Y _[n + 1]) (k : Fin (n + 3))
  (h : ∀ i j : Fin (n + 2), (hij : i < j) →
    Y.map (δ ((k.succAbove j).pred
      (ne_zero_of_lt (strictMono_succAbove _ hij)))).op (f i)
      = Y.map (δ ((k.succAbove i).castPred
        (ne_last_of_lt (strictMono_succAbove _ hij)))).op (f j)) :
    Λ[n + 2, k] ⟶ Y := Extend (hornGenerator (n + 1) k) (CompatibleFun.hornMk f k h)

lemma horn.HomMk_spec {n : ℕ} (f : Fin (n + 2) → Y _[n + 1]) (k : Fin (n + 3)) {l} {h} :
    (HomMk f k h).app _ (horn.face' k _ (succAbove_ne k l)) = f l := by
  dsimp [HomMk]
  convert Extend.spec (hornGenerator (n + 1) k) (CompatibleFun.hornMk f k h)
    (horn.face' k _ (succAbove_ne k l)) ⟨⟨_, succAbove_ne k l⟩, rfl⟩
  exact (CompatibleFun.hornMkFun_eq _ _ _).symm

lemma horn.face_comp_HomMk {n : ℕ} (f : Fin (n + 2) → Y _[n + 1]) (k : Fin (n + 3)) {l} {h} :
    (yonedaEquiv _ _).symm (horn.face' k _ (succAbove_ne k l)) ≫ horn.HomMk f k h
      = (yonedaEquiv _ _).symm (f l) := by
  apply_fun Y.yonedaEquiv _
  convert HomMk_spec f k -- lhs is solved by rfl as they're definitionally equal
  simp only [Equiv.apply_symm_apply]

noncomputable def horn.HomMk' {n : ℕ} (f : Fin (n + 2) → (Δ[n + 1] ⟶ Y)) (k : Fin (n + 3))
  (h : ∀ i j : Fin (n + 2), (hij : i < j) →
    standardSimplex.map (δ ((k.succAbove j).pred
      (ne_zero_of_lt (strictMono_succAbove _ hij)))) ≫ (f i)
      = standardSimplex.map (δ ((k.succAbove i).castPred
        (ne_last_of_lt (strictMono_succAbove _ hij)))) ≫ (f j)) :
    Λ[n + 2, k] ⟶ Y := by
  apply Extend (hornGenerator (n + 1) k)
    (CompatibleFun.hornMk (fun i ↦ yonedaEquiv _ _ (f i)) k
      (by simpa only [yonedaEquiv_symm_naturality, Equiv.symm_apply_apply,
        EmbeddingLike.apply_eq_iff_eq]))

lemma horn.HomMk_spec' {n : ℕ} (f : Fin (n + 2) → (Δ[n + 1] ⟶ Y)) (k : Fin (n + 3)) {l} {h} :
    (yonedaEquiv _ _).symm (horn.face' k _ (succAbove_ne k l)) ≫ HomMk' f k h = f l := by
  apply_fun yonedaEquiv _ _
  convert horn.HomMk_spec _ _

noncomputable def CompatibleFun.hornMkZero (a : Y _[0]) (k : Fin 2) :
    CompatibleFun (hornGenerator 0 k).carrier Y where
      func := hornMkFun ![a] k
      compatible := by
        intro ⟨x, ⟨⟨xk, hxk₀⟩, hxk⟩⟩ ⟨y, ⟨⟨yk, hyk₀⟩, hyk⟩⟩ z φ₁ φ₂ h₁ h₂
        have : ¬ xk = yk → 3 ≤ Fintype.card (Fin 2) := by
          intro h
          convert Finset.card_le_univ {k, xk, yk}
          rw [Finset.card_insert_of_not_mem (by simp only [Finset.mem_insert,
                  Finset.mem_singleton, not_or]; exact ⟨hxk₀.symm, hyk₀.symm⟩),
              Finset.card_insert_of_not_mem (by simp only [Finset.mem_singleton]; exact h),
              Finset.card_singleton]
        simp at this
        simp [horn.face', horn, ← Subtype.val_inj] at h₁ h₂
        cases hxk; cases hyk; cases this
        congr!
        apply test_aux1 _ _ _ _ _ (h₁.symm.trans h₂)
        exact nondegenerate_face _

noncomputable def horn.HomMkZero  (a : Y _[0]) (k : Fin 2) :
  Λ[1, k] ⟶ Y := Extend (hornGenerator 0 k) (CompatibleFun.hornMkZero a k)

end HomMk


end SSet
