import HoTTModel.LocallyCartesianClosed.Basic

namespace CategoryTheory.LocallyCartesianClosed

open Limits Over
noncomputable section
-- homEquiv between a chosen pullback and dependent product

namespace IsPullback
variable {α : Type u} [CategoryTheory.Category.{v, u} α] [CategoryTheory.Limits.HasPullbacks α]
  {A B C D E : α} {f : A ⟶ B} {fst : C ⟶ D} {snd : C ⟶ A} {g : D ⟶ B}
  (is : IsPullback fst snd g f)

def snd_isoPullback :
    Over.mk snd ≅ (f*).obj (Over.mk g) :=
  Over.isoMk is.isoPullback is.isoPullback_hom_snd

def snd_homEquiv (h : Over A) :
    (Over.mk snd ⟶ h) ≃ ((f*).obj (Over.mk g) ⟶ h) :=
  (snd_isoPullback is).homFromEquiv

lemma snd_homEquiv_naturality {h h' : Over A} (i : Over.mk snd ⟶ h) (j : h ⟶ h') :
    snd_homEquiv is h' (i ≫ j) =  snd_homEquiv is h i ≫ j := by
  simp only [snd_homEquiv, Iso.homFromEquiv_apply, Category.assoc]

variable [HasFiniteWidePullbacks α] [LocallyCartesianClosed α]

def adjEquiv (h : Over A) :
    (Over.mk snd ⟶ h) ≃ (Over.mk g ⟶ (Πf).obj h) :=
  (snd_homEquiv is h).trans ((adj f).homEquiv (Over.mk g) h)

variable (f g) in
def adjEquiv_ofHasPullback := IsPullback.adjEquiv (IsPullback.of_hasPullback g f)

lemma adjEquiv_naturality_right {h h' : Over A} (i : Over.mk snd ⟶ h) (j : h ⟶ h') :
    adjEquiv is h' (i ≫ j) = adjEquiv is h i ≫ (Πf).map j := by
  simp only [adjEquiv, Equiv.trans_apply]
  rw [snd_homEquiv_naturality is i j]
  exact Adjunction.homEquiv_naturality_right _ _ _

lemma adjEquiv_naturality_right_symm {h h' : Over A} (i : Over.mk g ⟶ (Πf).obj h) (j : h ⟶ h') :
    (adjEquiv is h').symm (i ≫ (Πf).map j) = (adjEquiv is h).symm i ≫ j := by
  simp only [Equiv.symm_apply_eq, adjEquiv_naturality_right,
    eq_self_iff_true, Equiv.apply_symm_apply]

section
/-
to be filled
-/
variable {C' D' : α} {fst' : C' ⟶ D'} {snd' : C' ⟶ A} {g' : D' ⟶ B}
  (is' : IsPullback fst' snd' g' f) (i : Over.mk g' ⟶ Over.mk g)
  {h : Over A}

lemma adjEquiv_naturality_symm_left (j : Over.mk g ⟶ (Πf).obj h) :
    is'.liftIsPullbackAlong' is i ≫ (adjEquiv is h).symm j = (adjEquiv is' h).symm (i ≫ j) := by
  dsimp [adjEquiv, snd_homEquiv]
  rw [Adjunction.homEquiv_naturality_left_symm, ← Category.assoc, ← Category.assoc]
  congr 1; ext; simp [snd_isoPullback]; apply pullback.hom_ext
  <;> simp

lemma adjEquiv_ofHasPullback_naturality_map_symm_left (j : Over.mk g ⟶ (Πf).obj h) :
    (f*).map i ≫ (adjEquiv_ofHasPullback f g _).symm j =
      (adjEquiv_ofHasPullback f g' _).symm (i ≫ j) := by
  -- todo; put it somewhere else
  have : (f*).map i = (IsPullback.of_hasPullback g' f).liftIsPullbackAlong'
    (IsPullback.of_hasPullback g f) i := by
      ext
      apply (IsPullback.of_hasPullback g f).hom_ext
      <;> simp
  rw [this]
  apply adjEquiv_naturality_symm_left

lemma adjEquiv_naturality_left (j : Over.mk snd ⟶ h):
    adjEquiv is' h (is'.liftIsPullbackAlong' is i ≫ j) = i ≫ adjEquiv is h j := by
  apply_fun (adjEquiv is' h).symm
  convert adjEquiv_naturality_symm_left is is' i _
  simp

end

section

variable {C' D' : α} {fst' : C' ⟶ D'} {snd' : C' ⟶ A} {g' : D' ⟶ B}
  (is' : IsPullback fst' snd' g' f) (i : Over.mk g' ⟶ Over.mk g)
  {h : Over A} (j : Over.mk g ⟶ (Πf).obj h)

lemma adjEquiv_naturality_symm_left' :
    is'.liftIsPullbackAlong' (IsPullback.of_hasPullback g f) i ≫
      ((adj f).homEquiv (Over.mk g) h).symm j = (adjEquiv is' h).symm (i ≫ j) := by
    dsimp [adjEquiv, snd_homEquiv]
    rw [Adjunction.homEquiv_naturality_left_symm, ← Category.assoc]
    congr 1; ext; simp [snd_isoPullback]; apply pullback.hom_ext
    <;> simp

end

end IsPullback
end

noncomputable section
/-
Consider
` A -- i --> A'`
` |          | `
` f          f'`
` ↓          ↓ `
` B -- j --> B'`
` |          | `
` g          g'`
` ↓          ↓ `
` C -- k --> C `
` |          | `
` ↑          ↑ `
` |          | `
`ΠA -- ? --> ΠA'`
with the top two squares are pullback, can exhibit a pullback square down in the botto
-/

variable {α : Type u} [CategoryTheory.Category.{v, u} α]
   [CategoryTheory.Limits.HasPullbacks α] [HasFiniteWidePullbacks α] [LocallyCartesianClosed α]
  {A A' B B' C C' : α} {f : A ⟶ B} {g : B ⟶ C} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
  {k : C ⟶ C'} {j : B ⟶ B'} {i : A ⟶ A'}
  (is : IsPullback j g g' k) (comm : CommSq i f f' j) -- (is : IsPullback i g g' h)

#check pullback ((Πg).obj (Over.mk f)).hom g

/-
def pushforward.isPullbackPaste {E : α} (h : E ⟶ C) :
    IsPullback (pullback.fst h g) (pullback.snd h g ≫ j) (h ≫ k) g' :=
  IsPullback.paste_vert (IsPullback.of_hasPullback _ _) is.flip
-/

def pushforward.trans₀ :
    (Σk).obj ((Πg).obj (Over.mk f)) ⟶ (Πg').obj (Over.mk f') := by
  refine IsPullback.adjEquiv
    (IsPullback.paste_vert (IsPullback.of_hasPullback ((Πg).obj (Over.mk f)).hom g) is.flip)
    (Over.mk f') ?_
  refine Over.homMk (((IsPullback.adjEquiv_ofHasPullback g ((Πg).obj (Over.mk f)).hom _).symm
    (𝟙 _)).left ≫ i) ?_
  simp; erw [comm.w, ← Category.assoc, Over.w]; rfl

abbrev pushforward.trans :
    ((Πg).obj (Over.mk f)).left ⟶ ((Πg').obj (Over.mk f')).left :=
  (pushforward.trans₀ is comm).left

/-
lemma pushforward.isPullback_lift_aux {E : α} (k : E ⟶ ((Πg').obj (Over.mk f')).left) (k' : E ⟶ C) :
  k ≫ ((Πg').obj (Over.mk f')).hom = k' ≫ h ↔
    (IsPullback.adjEquiv (isPullbackAux is' k') (Over.mk k'))
-/

variable (is' : IsPullback i f f' j) (t : PullbackCone ((Πg').obj (Over.mk f')).hom k)
def pushforward.isPullbackLift₀ :
    Over.mk t.snd ⟶ (Πg).obj (Over.mk f) := by
  let v := (IsPullback.adjEquiv
    (IsPullback.paste_vert (IsPullback.of_hasPullback t.snd g) is.flip)
    _).symm (Over.homMk t.fst t.condition)
  exact IsPullback.adjEquiv_ofHasPullback g t.snd _
    $ Over.homMk (is'.lift v.left (pullback.snd t.snd g) (Over.w v)) (is'.lift_snd _ _ _)

abbrev pushforward.isPullbackLift :
    t.pt ⟶ ((Πg).obj (Over.mk f)).left :=
  (isPullbackLift₀ is is' t).left

-- some bad `simp` lemmas are added... and this proof is bad
lemma pushforward.isPullbackLift_fst :
    isPullbackLift is is' t ≫ (pushforward.trans is is'.toCommSq) = t.fst := by
  simp only [trans, trans₀]
  let t' : Over.mk (t.snd ≫ k) ⟶ ((Πg').obj (Over.mk f')) := Over.homMk t.fst t.condition
  let lift := (Σk).map (isPullbackLift₀ is is' t)
  change lift.left ≫ _ =  t'.left
  rw [← comp_left]; congr
  let is₀ := IsPullback.paste_vert (IsPullback.of_hasPullback t.snd g) is.flip
  let is₁ := IsPullback.paste_vert
    (IsPullback.of_hasPullback ((Πg).obj (Over.mk f)).hom g) is.flip
  rw [← IsPullback.adjEquiv_naturality_left is₁ is₀]
  let φ := (g*).map (isPullbackLift₀ is is' t)
  have : (Σj).map φ = is₀.liftIsPullbackAlong' is₁ ((Σk).map (isPullbackLift₀ is is' t)) := by
    ext; simp only [comp_left, map_map_left, φ, IsPullback.liftIsPullbackAlong', Over.pullback,
        homMk_left]
    apply is₁.hom_ext
    simp only [IsPullback.liftIsPullbackAlong_fst, pullback.lift_fst]; rfl
    simp only [IsPullback.liftIsPullbackAlong_snd, pullback.lift_snd_assoc]; rfl
  rw [← this]
  apply_fun (IsPullback.adjEquiv is₀ (Over.mk f')).symm
  simp only [Equiv.symm_apply_apply]
  ext; simp only [comp_left, map_map_left, homMk_left, φ, ← Category.assoc]
  rw [← comp_left, IsPullback.adjEquiv_ofHasPullback_naturality_map_symm_left,
      Category.comp_id]
  simp only [isPullbackLift₀, Equiv.symm_apply_apply, homMk_left, is'.lift_fst]

def pushforward.isPullback :
    IsPullback (trans is is'.toCommSq) ((Πg).obj (Over.mk f)).hom
      ((Πg').obj (Over.mk f')).hom k where
    w := by simp
    isLimit' := ⟨by
      apply PullbackCone.isLimitAux _ (isPullbackLift is is')
      . intro; apply isPullbackLift_fst
      . intro; exact Over.w _
      . intro s w h
        change (Over.homMk w (h WalkingCospan.right)).left = (isPullbackLift₀ is is' s).left
        congr 1
        apply_fun (IsPullback.adjEquiv_ofHasPullback g s.snd _).symm
        simp only [isPullbackLift₀, Equiv.symm_apply_apply]
        let w₀ : Over.mk s.snd ⟶ ((Πg).obj (Over.mk f)) := homMk w (h WalkingCospan.right)
        let w' := (IsPullback.adjEquiv_ofHasPullback g s.snd (Over.mk f)).symm w₀
        ext; simp only [homMk_left]
        apply is'.hom_ext
        . let i' : Over.mk (f ≫ j) ⟶ Over.mk f' := Over.homMk i is'.w
          let is₀ := IsPullback.paste_vert (IsPullback.of_hasPullback s.snd g) is.flip
          let is₁ := IsPullback.paste_vert
            (IsPullback.of_hasPullback ((Πg).obj (Over.mk f)).hom g) is.flip
          have : (Σk).map w₀ ≫ (trans₀ is is'.toCommSq) = Over.homMk s.fst s.condition := by
            ext; exact h WalkingCospan.left
          change ((Σj).map w').left ≫ i'.left = _
          rw [IsPullback.lift_fst, ← comp_left]
          congr 1
          rw [← (IsPullback.adjEquiv is₀ (Over.mk f')).apply_eq_iff_eq_symm_apply, ← this]
          dsimp only [trans₀]
          rw [← IsPullback.adjEquiv_naturality_left is₁ is₀]
          congr 1; ext
          simp only [comp_left, homMk_left, map_map_left, i', ← Category.assoc, w']
          congr 1
          have : (is₀.liftIsPullbackAlong' is₁ ((Σk).map w₀)).left =
            ((g*).map w₀).left := by
              apply is₁.hom_ext
              . simp only [IsPullback.liftIsPullbackAlong', homMk_left, Over.pullback]
                rw [is₀.liftIsPullbackAlong_fst, pullback.lift_fst]; rfl
              . simp only [IsPullback.liftIsPullbackAlong', homMk_left, Over.pullback]
                rw [is₀.liftIsPullbackAlong_snd, pullback.lift_snd_assoc]; rfl
          rw [this, ← comp_left, IsPullback.adjEquiv_ofHasPullback_naturality_map_symm_left,
              Category.comp_id]
        . erw [Over.w, IsPullback.lift_snd]; rfl
    ⟩

end
