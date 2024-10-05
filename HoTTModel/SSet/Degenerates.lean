import HoTTModel.SSet.FaceDegeneracy
import HoTTModel.SSet.Lemmas
import Mathlib.Data.Nat.Lattice

open CategoryTheory Simplicial Limits SimplexCategory Function Opposite Classical SSet
open standardSimplex Set Fin

-- put it somewhere else
@[ext]
lemma standardSimplex.ext (x y : Δ[m].obj n) (h : asOrderHom x = asOrderHom y) : x = y := by
  apply (objEquiv _ _).injective
  dsimp [objEquiv, Equiv.ulift]
  ext a
  dsimp [asOrderHom] at h
  rw [h]

section Degenerate
namespace SSet

variable {X : SSet} {n : ℕ} (x : X _[n])

def Degenerate : {n : ℕ} → (x : X _[n]) → Prop
| 0, _ => False
| _ + 1, x => ∃ i, x ∈ range (X.map (σ i).op)

@[simp]
def Nondegenerate : Prop := ¬ Degenerate x

@[simp]
lemma Degenerate.vertice (x : X _[0]) :
  ¬ Degenerate x := by simp only [Degenerate, not_false_eq_true]

lemma Degenerate.eq_zero {x : X _[k]} : k = 0 → ¬ Degenerate x := by
  cases k; simp; simp

@[simp]
lemma Degenerate.succ {x : X _[n + 1]} :
  Degenerate x ↔ ∃ i, x ∈ range (X.map (σ i).op) := by simp only [Degenerate]

def Degenerates (X : SSet) := { ⟨_, x⟩ : Σ n : ℕ, X _[n] | Degenerate x}

def Nondegenerates (X : SSet) := { ⟨_, x⟩ : Σ n : ℕ, X _[n] | Nondegenerate x}

-- temporary name
def Unbordant : Prop := ∀ y i, x = X.map (δ i).op y → Degenerate y

def Bordant : Prop := ¬ Unbordant x

def Unbordants (X : SSet) := { ⟨_, x⟩ : Σ n : ℕ, X _[n] | Unbordant x}

def Bordants (X : SSet) := { ⟨_, x⟩ : Σ n : ℕ, X _[n] | Bordant x}

def NondegUnbord (X : SSet) := { ⟨_, x⟩ : Σ n : ℕ, X _[n] | Nondegenerate x ∧ Unbordant x}

end SSet
end Degenerate

section Lemma
namespace SSet

variable {X : SSet} {n : ℕ} (x : X _[n])

lemma _root_.Fin.Monotone.exists_eq_of_le {f : Fin (m + 1) → Fin n} (hf : Monotone f) :
    n ≤ m → ∃ i : Fin m, f i.castSucc = f i.succ := by
  intro h; contrapose! h
  apply StrictMono.le (hf.strictMono_of_injective (injective_of_lt_imp_ne _))
  intro i j hij
  apply (lt_of_lt_of_le
    ((hf (castSucc_lt_succ i).le).lt_of_ne (h <| i.castPred (ne_last_of_lt hij)))
    (hf (castSucc_lt_iff_succ_le.mp hij))).ne

lemma degenerate_iff_mem_range :
    Degenerate x ↔
  ∃ m, ∃ φ : ([n] : SimplexCategory) ⟶ [m], m < n ∧ x ∈ range (X.map φ.op) := by
  cases n with
  | zero => simp
  | succ n =>
    constructor
    . rintro ⟨i, hi⟩
      exact ⟨n, ⟨σ i, ⟨by norm_num, hi⟩⟩⟩
    . rintro ⟨m, ⟨φ, ⟨h₁, ⟨y, hy⟩⟩⟩⟩
      obtain ⟨i, hi⟩ :
        ∃ i : Fin (n + 1), φ.toOrderHom i.castSucc = φ.toOrderHom i.succ := by
          apply Monotone.exists_eq_of_le φ.toOrderHom.monotone'
          norm_num; rwa [← Nat.lt_succ_iff]
      have : φ = (σ i) ≫ (δ i.castSucc) ≫ φ := by
        ext j; simp [δ, σ]
        by_cases hj : j < i.castSucc
        . congr
          rw [succAbove_castSucc_of_lt _ _ (by
              rwa [predAbove_of_le_castSucc _ _ hj.le, castPred_lt_iff]),
            predAbove_of_lt_succ _ _ (hj.trans (castSucc_lt_succ _)),
            castSucc_castPred _ (ne_last_of_lt hj)]
        . by_cases hj' : j = i.castSucc
          . simp only [hj', predAbove_castSucc_self, succAbove_castSucc_self]
            congr 1
          . simp only [not_lt] at hj
            have hj := lt_of_le_of_ne hj (by rwa [eq_comm] at hj')
            congr
            rw [predAbove_of_castSucc_lt _ _ hj, succAbove_of_le_castSucc _ _ (by
                simpa only [castSucc_le_castSucc_iff, Fin.le_pred_iff]),
              succ_pred]
            -- have : (i.castSucc < j) = (i.succ ≤ j) := rfl -- ha???
      use i
      rw [this] at hy
      simp only [op_comp, Category.assoc, FunctorToTypes.map_comp_apply] at hy
      exact ⟨_, hy⟩

end SSet
end Lemma

section Lemma
namespace SSet

variable {X : SSet} {n : ℕ} (x : X _[n])

lemma Degenerate.iff_exists_asOrderHom (x : Δ[n] _[k]) :
  Degenerate x ↔ ∃ i : Fin k, asOrderHom x i.castSucc = asOrderHom x i.succ := by
  cases k with
  | zero => simp only [Degenerate.vertice, IsEmpty.exists_iff]
  | succ k =>
      constructor
      . rintro ⟨i, ⟨y, hy⟩⟩
        use i
        simp [← hy]
        have (j : Fin _): (asOrderHom (Δ[n].map (σ i).op y)) j
          = (asOrderHom y) ((σ i).toOrderHom j):= rfl -- okay...
        erw [this i.castSucc, this i.succ]
        congr 1
        simp [σ]
      . intro h
        obtain ⟨i, hi⟩ := h
        use i, (Δ[n].map (δ i).op x)
        apply_fun (objEquiv _ _)
        ext j; simp [map_apply, δ, σ]
        by_cases hj : j = i.castSucc
        . simp [hj]; congr 1
          convert hi.symm
        . rw [succAbove_predAbove hj]

-- can be simplified now
lemma Nondegenerate.iff_StrictMono (x : Δ[n] _[k]) :
  Nondegenerate x ↔ StrictMono (asOrderHom x) := by
  cases k with
  | zero => simp; intro i j h; simp [Subsingleton.allEq i j] at h
  | succ k =>
      simp only [Nondegenerate, Degenerate.iff_exists_asOrderHom, not_exists]
      constructor
      . intro h i j hij
        apply ((asOrderHom x).monotone' hij.le).lt_of_ne
        contrapose! h
        use ⟨i.1, val_lt_last (ne_last_of_lt hij)⟩
        apply le_antisymm ((asOrderHom x).monotone' (Fin.castSucc_lt_succ _).le)
        simp only [succ_mk, castSucc_mk, h]
        apply (asOrderHom x).monotone'
          <| le_iff_val_le_val.mp (Nat.succ_le_of_lt (lt_iff_val_lt_val.mp hij))
      . intro h _
        apply h.injective.ne (castSucc_lt_succ _).ne

lemma Nondegenerate.iff_injective (x : Δ[n] _[k]) :
  Nondegenerate x ↔ Injective (asOrderHom x) := by
  cases k with
  | zero => simp [Injective]; intros; apply Subsingleton.allEq
  | succ k =>
      rw [Nondegenerate.iff_StrictMono]
      apply (asOrderHom x).monotone'.strictMono_iff_injective

lemma aux1' (x : Δ[n] _[k]) : Nondegenerate x → k ≤ n := by
  intro h
  cases k with
  | zero => simp
  | succ k =>
    rw [Nondegenerate.iff_StrictMono] at h
    apply le_trans (Fin.le_image_of_StrictMono h (last _)) (Nat.lt_succ.mp (is_lt _))

lemma aux1 (x : Δ[n] _[k]) : n < k → Degenerate x := by
  rw [← not_imp_not, not_lt]
  apply aux1'

example (x : Δ[n] _[k]) : n ≤ k → Unbordant x := by
  intro h _ _ _
  apply aux1 _  (Nat.lt_succ.mpr h)

example (x : Δ[n] _[k]) : Degenerate x → Unbordant x := by
  intro h y i h'
  cases k with
  | zero => simp at h
  | succ k =>
      rw [Degenerate.iff_exists_asOrderHom] at h ⊢
      obtain ⟨j, hj⟩ := h
      rw [h'] at hj
      have (j : Fin _): (asOrderHom (Δ[n].map (δ i).op y)) j
          = (asOrderHom y) ((δ i).toOrderHom j):= rfl -- okay...
      erw [this _, this j.succ] at hj
      by_cases hij : i ≤ j.castSucc.castSucc
      . use j.succ
        convert hj using 2
        . simp [δ, ← succ_castSucc, succAbove_of_le_castSucc _ _ hij]
        . simp [δ, succAbove_of_le_castSucc _ _ <|
            hij.trans (castSucc_le_castSucc_iff.mpr (castSucc_lt_succ _).le)]
      . use j.castSucc
        simp only [not_le] at hij
        by_cases hij' : j.succ.castSucc < i
        convert hj using 2
        . simp [δ, succAbove_of_castSucc_lt _ _ hij]
        . simp [δ, succ_castSucc, succAbove_of_castSucc_lt _ _ hij']
        apply le_antisymm <| (asOrderHom _).monotone' (castSucc_lt_succ _).le
        rw [succ_castSucc]
        convert (asOrderHom y).monotone' (castSucc_lt_succ _).le using 1
        convert hj using 2
        . simp [δ, succAbove_of_castSucc_lt _ _ hij]
        . simp [δ, succAbove_of_le_castSucc _ _ (le_of_not_lt hij')]

lemma temp1 (f : ℕ → Type*) (P : {n : ℕ} → f n → Prop) (R : (n : ℕ) × f n → (n : ℕ) × f n → Prop)
(hR : Transitive R) (hR' : Reflexive R) (h₀ : ∀ {k}, ∀ {x : f k}, (k = 0) → P x)
(h : ∀ {n k}, n = k + 1 →  (x : f (n) ) → (P x ∨ (∃ y : f k, R ⟨_ , y⟩ ⟨n , x⟩) ))
{n : ℕ} (x : f n): ∃ k, ∃ (y : f k), P y ∧ R  ⟨_, y⟩ ⟨_, x⟩ := by
    set S := {k | ∃ (y : f k), R ⟨_, y⟩ ⟨_, x⟩}
    use (sInf S)
    obtain ⟨y, hy⟩ : (sInf S) ∈ S := by
      apply Nat.sInf_mem
      exact ⟨n, ⟨x, (hR' _)⟩⟩
    rcases (sInf S).eq_zero_or_eq_succ_pred with (hs | hs)
    exact ⟨y, ⟨h₀ hs, hy⟩⟩
    use y
    by_cases hy' : P y
    exact ⟨hy', hy⟩
    exfalso
    have := h hs y
    simp [hy'] at this
    obtain ⟨y', hy'⟩ := this
    have : (sInf S).pred ∈ S := ⟨y', hR hy' hy⟩
    apply (Nat.sInf_le this).not_lt (Nat.pred_lt _)
    rw [hs]
    apply Nat.succ_ne_zero

lemma temp2 (f : ℕ → Type*) (P : {n : ℕ} → f n → Prop) (R : (n : ℕ) × f n → (n : ℕ) × f n → Prop) :
(∀ n : ℕ, ∀ x : f (n + 1), (P x ∨ (∃ y : f n, R ⟨_ , y⟩ ⟨_ , x⟩) ))
↔ ∀ {n k}, n = k + 1 →  (x : f (n) ) → (P x ∨ (∃ y : f k, R ⟨_ , y⟩ ⟨n , x⟩)) := by
  constructor
  . intro h n k hnk x
    specialize h k
    rw [← hnk] at h
    exact h x
  . intro h n x
    apply h (by rfl)

def connect (X : SSet) := fun y : (n : ℕ) × X _[n] ↦ fun x : (n : ℕ) × X _[n] ↦
    ∃ φ, x.2 = X.map φ y.2

lemma connect.transitive (X : SSet) :
    Transitive X.connect := by
  intro x y z ⟨φ₁, h₁⟩ ⟨φ₂, h₂⟩
  use φ₁ ≫ φ₂
  simp [h₁, h₂]

def R' (X : SSet) := fun y : (n : ℕ) × X _[n] ↦ fun x : (n : ℕ) × X _[n] ↦
    ∃ φ : ([x.fst] : SimplexCategory) ⟶ [y.fst],
  (⇑φ.toOrderHom).Surjective ∧ x.2 = X.map φ.op y.2

lemma haha' (x : X _[n]) : ∃ k : ℕ, ∃ y : X _[k], Nondegenerate y ∧ R' X ⟨_, y⟩ ⟨_, x⟩ := by
  apply temp1
  . intro x y z ⟨φ₁, h₁⟩ ⟨φ₂, h₂⟩
    use φ₂ ≫ φ₁
    constructor
    . simp only [comp_toOrderHom, OrderHom.comp_coe]
      exact h₁.1.comp h₂.1
    . simp [h₂.2, h₁.2]
  . intro x
    use (𝟙 _)
    simp [Surjective]
  . intro _ _ h; apply Degenerate.eq_zero h
  . rw [← temp2]
    intro n x
    simp only [Decidable.or_iff_not_imp_left, Nondegenerate, Degenerate.succ, mem_range, not_exists, not_forall, Decidable.not_not]
    rintro ⟨i, ⟨y, hy⟩⟩
    use y, (σ i)
    constructor
    . simp [σ]
      intro j
      by_cases hj : j ≤ i
      use j.castSucc
      rw [predAbove_castSucc_of_le _ _ hj]
      use j.succ
      rw [predAbove_succ_of_le _ _ (lt_of_not_le hj).le]
    . exact hy.symm

-- uniqeness
example (x : X _[n]) (y z : (n : ℕ) × X _[n] ) (hy : Nondegenerate y.2) (hz : Nondegenerate z.2):
    X.connect y ⟨_, x⟩ →  X.connect z ⟨_, x⟩ → y = z := by
  intro h₁ h₂
  sorry

-- Generators of a SSet

structure Generator (X : SSet) where
  carrier : Set ((n : ℕ) × X _[n])
  connect : ∀ y, ∃ x ∈ carrier, X.connect x y

def isGenerator {X : SSet} (S : Set ((n : ℕ) × X _[n])) : Prop :=
  ∀ y, ∃ x ∈ S, X.connect x y

def isGenerator.MkGenerator {X : SSet} (S : Set ((n : ℕ) × X _[n])) (h : isGenerator S):
  Generator X where
    carrier := S
    connect := h

lemma exists_nondegenerates_connect {X : SSet} {n : ℕ} (x : X _[n]) :
    ∃ k : ℕ, ∃ y : X _[k], Nondegenerate y ∧ X.connect ⟨_, y⟩ ⟨_, x⟩ := by
  apply temp1 (hR := connect.transitive _)
  . intro x; use (𝟙 _); simp
  . intro _ _ h; apply Degenerate.eq_zero h
  . rw [← temp2]
    intro n x
    simp [Decidable.or_iff_not_imp_left, Nondegenerates, Degenerate.succ]
    rintro i y hy
    exact ⟨y, ⟨(σ i).op, hy.symm⟩⟩

lemma Nondegenerates.isGenerator (X : SSet) :
    isGenerator X.Nondegenerates := by
  intro y
  simp only [Sigma.exists]
  apply exists_nondegenerates_connect

def app (f : X ⟶ Y) (x : X _[n]) := f.app _ x

infix:55 " ~ " => app

lemma hom_ext' (f g : X ⟶ Y) :
    (∀ n, ∀ x : X _[n], f ~ x = g ~ x) → f = g := by
  intro h
  apply NatTrans.ext; apply funext; apply Opposite.rec; apply SimplexCategory.rec
  intro n; ext x
  exact h n x

lemma hom_generator_ext {f g : X ⟶ Y} (G : X.Generator) (h : ∀ x ∈ G.carrier, f ~ x.2 = g ~ x.2) :
    f = g := by
  apply hom_ext'
  intro n x
  obtain ⟨y, ⟨hy₁, ⟨φ, hy₂⟩⟩⟩ := G.connect ⟨_, x⟩
  have (h : X ⟶ Y) : (h ~ x) = Y.map φ (h ~ y.2) := by
    simp at hy₂
    rw [hy₂]
    have this₁ : h ~ (X.map φ y.2) = (X.map φ ≫ h.app _) y.2 := rfl
    have this₂ : Y.map φ (h ~ y.2) = (h.app _ ≫ Y.map φ) y.2 := rfl
    -- need better api for natural trans lol
    rw [this₁, this₂, h.naturality]
  rw [this, this, h _ (by apply hy₁)]

-- `objMk OrderHom.id` connects to all the nondegenerates

lemma connect_to_standardSimplex (x : Δ[n] _[k]) :
    Δ[n].connect ⟨n, objMk OrderHom.id⟩ ⟨k, x⟩ := by
  use op (Hom.mk (asOrderHom x))
  apply standardSimplex.ext
  ext i : 2
  simp [map_apply]
  rfl

def standardSimplexGenerator : Generator Δ[n] where
  carrier := {⟨n, objMk OrderHom.id⟩}
  connect := by
    rintro ⟨k, y⟩
    use ⟨n, objMk OrderHom.id⟩
    simp only [mem_singleton_iff, true_and]
    apply connect_to_standardSimplex

def _root_.Set.level.{u} {X : (n : ℕ) → Type u} (S : Set ((n : ℕ) × X n)) (n : ℕ) :
    Set (X n) := {x | ⟨n, x⟩ ∈ S}

/-
-- try to calculate the generator of SSubset given a generator of a SSet, but no result, give up.
def _root_.Set.level.{u} {X : (n : ℕ) → Type u} (S : Set ((n : ℕ) × X n)) (n : ℕ) :
    Set (X n) := {x | ⟨n, x⟩ ∈ S}

def SSubsetMk.{u} (X : SSet.{u}) (P : {m : _} → X.obj m → Prop)
  (h : ∀ {m₁ m₂} {f : m₁ ⟶ m₂} {x : X.obj m₁}, P x → P (X.map f x)) :
    SSet.{u} where
      obj m := {a : X.obj m // P a}
      map {m₁ m₂} f a := ⟨X.map f a.val, h a.property⟩

structure SSubset.{u} (X : SSet.{u}) where
  prop : {m : _} → X.obj m → Prop
  isClosed : ∀ {m₁ m₂} {f : m₁ ⟶ m₂} {x : X.obj m₁}, prop x → prop (X.map f x)

def SSubset.SSet {X : SSet.{u}} (S : SSubset X) := SSubsetMk X S.prop S.isClosed
-/

variable {Y : SSet}

def Compatible (S : Set ((n : ℕ) × X _[n])) (f : {n : ℕ} → S.level n → Y _[n]) :
    Prop :=
  ∀ x y : S, ∀ (z : (n : ℕ) × X _[n]), ∀ φ₁ φ₂, z.2 = X.map φ₁ x.1.2 → z.2 = X.map φ₂ y.1.2
    → Y.map φ₁ (f ⟨x.1.2, x.2⟩) = Y.map φ₂ (f ⟨y.1.2, y.2⟩)

def CompatibleOn (S : Set ((n : ℕ) × X _[n])) (f : {n : ℕ} → S.level n → Y _[n])
  (T : Set ((n : ℕ) × X _[n])) :
    Prop :=
  ∀ x y : S, ∀ z ∈ T, ∀ φ₁ φ₂, z.2 = X.map φ₁ x.1.2 → z.2 = X.map φ₂ y.1.2
    → Y.map φ₁ (f ⟨x.1.2, x.2⟩) = Y.map φ₂ (f ⟨y.1.2, y.2⟩)

structure CompatibleFun (S : Set ((n : ℕ) × X _[n])) (Y : SSet) where
  func : {n : ℕ} → S.level n → Y _[n]
  compatible : Compatible S func

noncomputable def Extend (S : X.Generator) (f : CompatibleFun S.carrier Y):
    X ⟶ Y where
  app m := by
    cases m with
    | op m =>
      induction m using SimplexCategory.rec
      intro x
      set y := choose <| S.connect ⟨_, x⟩
      have hy := choose_spec <| S.connect ⟨_, x⟩
      exact Y.map (choose hy.2) (f.1 ⟨y.2, hy.1⟩)
  naturality m₁ m₂ φ := by
    cases m₁ with
    | op m₁ =>
      cases m₂ with
      | op m₂ =>
        induction m₁ using SimplexCategory.rec
        induction m₂ using SimplexCategory.rec
        ext x
        dsimp only [SimplexCategory.rec, len_mk, types_comp_apply]
        set y := choose <| S.connect ⟨_, x⟩
        obtain ⟨hy, hy_⟩ := choose_spec <| S.connect ⟨_, x⟩
        set ψ := choose hy_
        have hψ := choose_spec hy_
        set y' := choose <| S.connect ⟨_, X.map φ x⟩
        obtain ⟨hy', hy'_⟩ := choose_spec <| S.connect ⟨_, X.map φ x⟩
        set ψ' := choose hy'_
        have hψ' := choose_spec hy'_
        simp at hψ hψ'
        have := f.2 ⟨y, hy⟩ ⟨y', hy'⟩ ⟨_, X.map φ x⟩ (ψ ≫ φ) ψ' (by simp; rw [hψ]) hψ'
        simp at this
        exact this.symm

lemma Extend.spec (S : X.Generator) (f : CompatibleFun S.carrier Y) (x : X _[n])
  (hx : ⟨n, x⟩ ∈ S.carrier) :
    (Extend S f).app _ x = f.func ⟨x, hx⟩ := by
  simp [Extend, SimplexCategory.rec]
  set y := choose <| S.connect ⟨_, x⟩
  obtain ⟨hy, hy_⟩ := choose_spec <| S.connect ⟨_, x⟩
  set ψ := choose hy_
  have hψ := choose_spec hy_
  convert f.2 ⟨y, hy⟩ ⟨⟨_, x⟩, hx⟩ ⟨_, x⟩ ψ (𝟙 _) hψ (by simp)
  simp only [FunctorToTypes.map_id_apply]

lemma test_aux1 (x : Δ[n].obj k) (hx : Nondegenerate (n := k.unop.len) x) :
    ∀ k' (φ₁ : k ⟶ k') φ₂,
      (Δ[n].map φ₁ x = Δ[n].map φ₂ x → φ₁ = φ₂) := by
    intro k' φ₁ φ₂ h
    apply_fun unop using Quiver.Hom.unop_inj
    simp [map_apply] at h
    have : Mono ((objEquiv [n] k) x) := by
      rw [SimplexCategory.mono_iff_injective]
      exact ((Nondegenerate.iff_StrictMono _).mp hx).injective
    rwa [cancel_mono] at h

-- a crucial one

noncomputable def lalala (f : Fin (n + 1) →o Fin m) (g : Fin k →o Fin m) (h : range g ⊆ range f) :
  Fin k →o Fin (n + 1) where
    toFun i := sSup {j | f j = g i}
    monotone' i j hij := by
      rcases eq_or_lt_of_le (g.monotone hij) with hij | hij
      simp only [hij]; apply le_refl
      simp only [mem_setOf_eq]
      apply sSup_le_sSup_of_forall_exists_le
      intro l hl
      obtain ⟨l', hl'⟩ := h ⟨j, rfl⟩
      exact ⟨l', hl', (f.monotone.reflect_lt (hl'.symm ▸ hl.symm ▸ hij)).le⟩

lemma lalala_spec (f : Fin (n + 1) →o Fin m) (g : Fin k →o Fin m) (h : range g ⊆ range f) :
    g = f ∘ lalala f g h := by
  ext i : 1
  simp [lalala]
  have : sSup {j | f j = g i} ∈ {j | f j = g i} := by
    apply Nonempty.csSup_mem
    exact h ⟨i, rfl⟩
    rw [← finite_coe_iff]
    apply Subtype.finite
  exact this.symm

lemma _root_.Fin.exists_OrderHom_comp_iff_range_subset {n m k} (f : Fin n →o Fin m) (g : Fin k →o Fin m) :
    (∃ h : Fin k →o Fin n, g = f ∘ h) ↔ range g ⊆ range f := by
  constructor
  . rw [range_subset_range_iff_exists_comp]
    exact fun ⟨h, hh⟩ ↦ ⟨⇑h, hh⟩
  . cases n with
  | zero =>
      cases k with
      | zero => intro; use OrderHom.id; ext i; exact i.elim0
      | succ => simp only [Matrix.range_empty]; intro h; apply False.elim $ h ⟨0, rfl⟩
  | succ n =>
      intro h
      exact ⟨lalala f g h, lalala_spec _ _ h⟩

lemma connect_iff_range_subset (x y: (k : ℕ) × Δ[n] _[k]) :
    Δ[n].connect x y ↔ range (asOrderHom y.2) ⊆ range (asOrderHom x.2) := by
  rw [← exists_OrderHom_comp_iff_range_subset]
  simp [connect, map_apply]
  constructor
  . intro ⟨φ, hφ⟩
    use (φ.unop).toOrderHom
    apply_fun fun x ↦ ⇑(asOrderHom x) at hφ
    exact hφ
  . intro ⟨h, hh⟩
    use op (Hom.mk h)
    apply standardSimplex.ext
    ext : 1
    exact hh

lemma range_subset_of_connect (x : Δ[n] _[k]) (y : Δ[n] _[k']) (φ):
    y = Δ[n].map φ x → range (asOrderHom y) ⊆ range (asOrderHom x) := by
  intro h
  exact (connect_iff_range_subset ⟨k, x⟩ ⟨k', y⟩).mp ⟨φ, h⟩

-- l = i.castPred
-- l' = j

end SSet
end Lemma

/-
namespace SSet.Hom

variable {X : SSet} {n : ℕ} (x : Δ[n] ⟶ X)

def Degenerate : Prop := SSet.Degenerate ((yonedaEquiv X _) x)

def Nondegenerate : Prop := ¬ Degenerate x

end SSet.Hom
-/
