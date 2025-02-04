import HoTTModel.LocallyCartesianClosed.Basic
import HoTTModel.Lemmas.HEq

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

@[reassoc]
lemma adjEquiv_naturality_right {h h' : Over A} (i : Over.mk snd ⟶ h) (j : h ⟶ h') :
    adjEquiv is h' (i ≫ j) = adjEquiv is h i ≫ (Πf).map j := by
  simp only [adjEquiv, Equiv.trans_apply]
  rw [snd_homEquiv_naturality is i j]
  exact Adjunction.homEquiv_naturality_right _ _ _

@[reassoc]
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

@[reassoc]
lemma adjEquiv_naturality_symm_left (j : Over.mk g ⟶ (Πf).obj h) :
    is'.liftIsPullbackAlong' is i ≫ (adjEquiv is h).symm j = (adjEquiv is' h).symm (i ≫ j) := by
  dsimp [adjEquiv, snd_homEquiv]
  rw [Adjunction.homEquiv_naturality_left_symm, ← Category.assoc, ← Category.assoc]
  congr 1; ext; simp [snd_isoPullback]; apply pullback.hom_ext
  <;> simp

@[reassoc]
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

@[reassoc]
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

@[reassoc]
lemma adjEquiv_naturality_symm_left' :
    is'.liftIsPullbackAlong' (IsPullback.of_hasPullback g f) i ≫
      ((adj f).homEquiv (Over.mk g) h).symm j = (adjEquiv is' h).symm (i ≫ j) := by
    dsimp [adjEquiv, snd_homEquiv]
    rw [Adjunction.homEquiv_naturality_left_symm, ← Category.assoc]
    congr 1; ext; simp [snd_isoPullback]; apply pullback.hom_ext
    <;> simp

end

section

-- eq on `g` gives `heq`

variable {g' : D ⟶ B} (eq : g = g')

def adjEquiv_eqToHom_comp_isPullback :
  IsPullback fst snd g' f  := by
  cases eq; exact is

lemma adjEquiv_eqToHom_comp (h : Over A) (j : Over.mk snd ⟶ h):
  HEq (adjEquiv is h j) (adjEquiv (adjEquiv_eqToHom_comp_isPullback is eq) h j) := by
  cases eq
  rfl

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
  [HasFiniteWidePullbacks α] [LocallyCartesianClosed α]
  {A A' B B' C C' : α} {f : A ⟶ B} {g : B ⟶ C} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
  {k : C ⟶ C'} {j : B ⟶ B'} {i : A ⟶ A'}
  (is : IsPullback j g g' k) (comm : CommSq i f f' j)

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

variable {E : Over C} {q : E ⟶ ((Πg).obj (Over.mk f))}

lemma pushforward.comp_trans₀ :
  (Σk).map q ≫ pushforward.trans₀ is comm = IsPullback.adjEquiv
    ((IsPullback.of_hasPullback E.hom g).paste_vert is.flip) _
    ((Σj).map (((g*).map q) ≫
    (IsPullback.adjEquiv_ofHasPullback g ((Πg).obj (Over.mk f)).hom _).symm (𝟙 _)) ≫
    (homMk i comm.w : Over.mk (f ≫ j) ⟶ Over.mk f')) := by
  let is₀ := (IsPullback.of_hasPullback E.hom g).paste_vert is.flip
  let is₁ := IsPullback.paste_vert
    (IsPullback.of_hasPullback ((Πg).obj (Over.mk f)).hom g) is.flip
  apply_fun (IsPullback.adjEquiv is₀ (Over.mk f')).symm
  simp only [Equiv.symm_apply_apply, trans₀]
  rw [← IsPullback.adjEquiv_naturality_left is₁ is₀]
  ext; simp;
  congr 1
  apply is₁.hom_ext
  <;> simp

lemma pushforward.comp_trans₀' {F : α} {l : F ⟶ E.left} {m : F ⟶ B}
  (is' : IsPullback l m E.hom g) :
  (Σk).map q ≫ pushforward.trans₀ is comm = IsPullback.adjEquiv (is'.paste_vert is.flip) _
      ((Σj).map ((is'.liftIsPullbackAlong'
      (IsPullback.of_hasPullback ((Πg).obj (Over.mk f)).hom g) q) ≫
      (IsPullback.adjEquiv_ofHasPullback g ((Πg).obj (Over.mk f)).hom _).symm (𝟙 _)) ≫
      (homMk i comm.w : Over.mk (f ≫ j) ⟶ Over.mk f')) := by
  let is₀ := is'.paste_vert is.flip
  let is₁ := IsPullback.paste_vert
    (IsPullback.of_hasPullback ((Πg).obj (Over.mk f)).hom g) is.flip
  apply_fun (IsPullback.adjEquiv is₀ (Over.mk f')).symm
  simp only [Equiv.symm_apply_apply, trans₀]
  rw [← IsPullback.adjEquiv_naturality_left is₁ is₀]
  ext; simp;
  congr 1
  apply is₁.hom_ext
  <;> simp
  rw [IsPullback.liftIsPullbackAlong_snd_assoc]

section

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

attribute [-simp] PullbackCone.π_app_right

lemma pushforward.isPullbackLift_fst :
    isPullbackLift is is' t ≫ (pushforward.trans is is'.toCommSq) = t.fst := by
  simp [trans]
  let t' : Over.mk (t.snd ≫ k) ⟶ ((Πg').obj (Over.mk f')) := Over.homMk t.fst t.condition
  let lift := (Σk).map (isPullbackLift₀ is is' t)
  change lift.left ≫ _ =  t'.left
  rw [← comp_left, pushforward.comp_trans₀]; congr
  apply_fun (IsPullback.adjEquiv
    (IsPullback.paste_vert (IsPullback.of_hasPullback _ g) is.flip) (Over.mk f')).symm
  rw [Equiv.symm_apply_apply]
  ext; simp only [comp_left, map_map_left, t', homMk_left, ← Category.assoc]
  rw [← comp_left, IsPullback.adjEquiv_ofHasPullback_naturality_map_symm_left,
      Category.comp_id]
  simp [isPullbackLift₀, Equiv.symm_apply_apply, homMk_left, is'.lift_fst]

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

section
variable (is' : IsPullback i f f' j) {D D' E E' : α} {d : D ⟶ D'} {p : D ⟶ C} {p' : D' ⟶ C'}
  {q : E ⟶ B} {q' : E' ⟶ B'} {t : E ⟶ D} {t' : E' ⟶ D'}
  (is₁ : IsPullback t q p g) (is₂ : IsPullback t' q' p' g') (comm : CommSq d p p' k)

abbrev pushforward.liftAux :
    E ⟶ E' :=
  (is₁.paste_vert is.flip).liftIsPullbackAlong is₂ d comm.w

abbrev pushforward.liftAux' :
    Over.mk (q ≫ j) ⟶ Over.mk q' :=
  (is₁.paste_vert is.flip).liftIsPullbackAlong' is₂ (Over.homMk d comm.w)

def pushforward.commSqAux :
    CommSq (liftAux is is₁ is₂ comm) q q' j where
  w := by simp

lemma pushforward.adj_symm_comp (b : Over.mk p' ⟶ (Πg').obj (Over.mk f')) :
  ((IsPullback.adjEquiv is₁ _).symm
    (comm.liftIsPullbackAlong' (pushforward.isPullback is is') b)).left ≫ i =
    liftAux is is₁ is₂ comm ≫ ((IsPullback.adjEquiv is₂ (Over.mk f')).symm b).left := by
  let bk := (Σk).map (comm.liftIsPullbackAlong' (pushforward.isPullback is is') b)
  let b' := is₁.liftIsPullbackAlong' (IsPullback.of_hasPullback ((Πg).obj (Over.mk f)).hom g)
    (comm.liftIsPullbackAlong' (pushforward.isPullback is is') b)
  let d' : Over.mk (p ≫ k) ⟶ Over.mk p' := Over.homMk d comm.w
  let cj := (Σj).map ((IsPullback.adjEquiv is₁ _).symm
    (comm.liftIsPullbackAlong' (pushforward.isPullback is is') b))
  let cj' := (is₁.paste_vert is.flip).liftIsPullbackAlong'
    ((IsPullback.of_hasPullback ((Πg).obj (Over.mk f)).hom g).paste_vert is.flip) bk
  let i' : Over.mk (f ≫ j) ⟶ Over.mk f' := Over.homMk i is'.w
  let counitj := (Σj).map
    ((IsPullback.adjEquiv_ofHasPullback g ((Πg).obj (Over.mk f)).hom _).symm (𝟙 _))
  have aux₀ : (Σj).map b' = cj' := by
    ext; simp [cj', b']
    apply ((IsPullback.of_hasPullback ((Πg).obj (Over.mk f)).hom g).paste_vert is.flip).hom_ext
    . simp [bk]
    . simp [bk]; rw [← Category.assoc, IsPullback.liftIsPullbackAlong_snd]
  have aux₁ : cj = cj' ≫ counitj := by
    simp [counitj, ← aux₀, cj]
    erw [← Functor.map_comp, IsPullback.adjEquiv_naturality_symm_left, Category.comp_id]
    rfl
  have aux₂ : d' ≫ b = bk ≫ trans₀ is is'.toCommSq := by ext; simp [d', bk]
  change cj.left ≫ i'.left = (liftAux' is is₁ is₂ comm).left ≫ _
  rw [← comp_left, ← comp_left, IsPullback.adjEquiv_naturality_symm_left, aux₁, aux₂,
    Category.assoc]
  congr
  apply_fun (IsPullback.adjEquiv (is₁.paste_vert is.flip) (Over.mk f'))
  rw [Equiv.apply_symm_apply, IsPullback.adjEquiv_naturality_left]; rfl

lemma pushforward.adj_symm_lift_eq_lift_adj_symm (b : Over.mk p' ⟶ (Πg').obj (Over.mk f')) :
  (IsPullback.adjEquiv is₁ _).symm
    (comm.liftIsPullbackAlong' (pushforward.isPullback is is') b) =
      (pushforward.commSqAux is is₁ is₂ comm).liftIsPullbackAlong' is'
        ((IsPullback.adjEquiv is₂ _).symm b) := by
  ext; apply is'.hom_ext
  . simp; apply pushforward.adj_symm_comp (is' := is')
  . simpa using Over.w _

lemma pushforward.adj_lift_eq_lift_adj (a : Over.mk q' ⟶ Over.mk f') :
    comm.liftIsPullbackAlong' (pushforward.isPullback is is') (IsPullback.adjEquiv is₂ _ a) =
      IsPullback.adjEquiv is₁ _
        ((pushforward.commSqAux is is₁ is₂ comm).liftIsPullbackAlong' is' a) := by
  apply_fun (IsPullback.adjEquiv is₁ _).symm
  convert adj_symm_lift_eq_lift_adj_symm is is' is₁ is₂ comm (IsPullback.adjEquiv is₂ _ a)
  simp only [Equiv.symm_apply_apply]

end

section
/-
Consider
` A -- i --> A'-- i' --> A''`
` |          |            | `
` f          f'          f''`
` ↓          ↓            ↓ `
` B -- j --> B' -- j' --> B''`
` |          |            | `
` g          g'          g''`
` ↓          ↓            ↓`
` C -- k --> C' -- k' --> C'' `
` |          |            |`
` ↑          ↑            ↑`
` |          |            |`
`ΠA -------> ΠA'-------> ΠA''`
-/

variable {A'' B'' C'' : α} {f'' : A'' ⟶ B''} {g'' : B'' ⟶ C''}
  {i' : A' ⟶ A''} {j' : B' ⟶ B''} {k' : C' ⟶ C''}
  (is' : IsPullback j' g' g'' k') (comm' : CommSq i' f' f'' j')

@[reassoc]
lemma pushforward.trans_comp :
    pushforward.trans is comm ≫ pushforward.trans is' comm' =
      pushforward.trans (is.paste_horiz is') (comm.horiz_comp comm') := by
  have eq : (Σk').obj ((Σk).obj ((Πg).obj (Over.mk f))) =
    (Σk ≫ k').obj ((Πg).obj (Over.mk f)) := by
      rw [mapComp_eq]; rfl
  let is₁ := (IsPullback.of_hasPullback ((Πg).obj (Over.mk f)).hom g).paste_vert is.flip
  let is₂ := is₁.paste_vert is'.flip
  have eq : (((Πg).obj (Over.mk f)).hom ≫ k) ≫ k' = ((Πg).obj (Over.mk f)).hom ≫ k ≫ k' := by
    simp
  let is₂' := IsPullback.adjEquiv_eqToHom_comp_isPullback is₂ eq
  let is₂'' := (IsPullback.of_hasPullback ((Πg).obj (Over.mk f)).hom g).paste_vert
    (is.flip.paste_vert is'.flip)
  let l := is₂'.liftIsPullbackAlong' is₂'' (𝟙 _)
  have : l.left = 𝟙 _ := by
    apply is₂''.hom_ext
    <;> simp [l]
  simp only [trans]
  change ((Σk').map (trans₀ is comm)).left ≫ _ = _
  rw [← comp_left]
  congr 1
  rw [comp_trans₀' _ _ is₁]
  let ev := (IsPullback.adjEquiv_ofHasPullback g ((Πg).obj (Over.mk f)).hom _).symm (𝟙 _)
  let evj' := (Σ(j ≫ j')).map ev
  let ev' := (IsPullback.adjEquiv_ofHasPullback g' ((Πg').obj (Over.mk f')).hom _).symm (𝟙 _)
  let i_ : Over.mk (f ≫ j ≫ j') ⟶ Over.mk (f' ≫ j') := Over.homMk i (by simp [comm.w_assoc])
  have aux : (Σj').map ((is₁.liftIsPullbackAlong'
    (IsPullback.of_hasPullback ((Πg').obj (Over.mk f')).hom g') (trans₀ is comm)) ≫ ev') =
      l ≫ evj' ≫ i_ := by
    erw [IsPullback.adjEquiv_naturality_symm_left]
    rw [Category.comp_id]
    ext
    simp [comp_left, this, trans₀]; rfl
  refine HEq.trans ((IsPullback.adjEquiv_eqToHom_comp is₂ eq) _ _) ?_
  simp_rw [aux, Category.assoc]
  rw [IsPullback.adjEquiv_naturality_left]
  simp
  rfl
end
end
