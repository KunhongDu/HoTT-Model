import HoTTModel.DTT.PTS
import HoTTModel.ContextualCategory.Contextual

namespace PureTypeSystem

open Classical CategoryTheory Limits

noncomputable section TermModel

@[ext]
structure Ctx (S : Specification) where
  ctx : PCtx S
  wf : Nonempty (ctx ⊢ ⬝)

def PCtx.cons (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)) : Ctx S where
  ctx := A :: Γ
  wf := h

def Ctx.cons (Γ : Ctx S) (A : PTerm S) (h : Nonempty (A :: Γ.ctx ⊢ ⬝)) : Ctx S :=
  Γ.ctx.cons A h

namespace Ctx

def wf' (Γ : Ctx S) : Γ.ctx ⊢ ⬝ := choice Γ.wf

def betac (Γ Δ : Ctx S) : Prop := Nonempty (Γ.ctx ≃β Δ.ctx)

lemma betac.equivalence :
    Equivalence (betac (S := S)) where
  refl Γ := ⟨PCtx.betac.refl Γ.ctx⟩
  symm := by intro _ _ ⟨h₁⟩; exact ⟨h₁.symm⟩
  trans := by intro _ _ _ ⟨h₁⟩ ⟨h₂⟩; exact ⟨h₁.trans _ _ _ h₂⟩

instance setoid (S : Specification) : Setoid (Ctx S) where
  iseqv := betac.equivalence

abbrev nil : Ctx S := ⟨[], ⟨wf.nil⟩⟩

lemma eq_nil_of_equiv_nil {Γ : Ctx S} :
    Γ ≈ nil → Γ = nil := by
  intro ⟨h⟩; ext
  simpa using h.length_eq

def tail : (Γ : Ctx S) → Ctx S
| .mk [] _ => nil
| .mk (_ :: Γ) h => ⟨Γ, ⟨wf_of_cons (choice h)⟩⟩

@[simp]
lemma tail_eq_list_tail : ∀ (Γ : Ctx S), Γ.tail.ctx = Γ.ctx.tail
| .mk [] _ => rfl
| .mk (_ :: _) _ => rfl

lemma tail_sound {Γ Δ : Ctx S} : (h : Γ ≈ Δ) → Γ.tail ≈ Δ.tail := by
  intro ⟨h⟩
  constructor
  simpa using h.tail'

@[simp]
lemma nil_tail : (nil : Ctx S).tail = nil := rfl

end Ctx

def QCtx (S : Specification) := Quotient (Ctx.setoid S)

notation:1024 "[" Γ "]ᵣ"=> Ctx.ctx (Quotient.out Γ)

section

lemma Ctx.mk_out_equiv (Γ : Ctx S) : (⟦Γ⟧ : QCtx S).out ≈ Γ :=
  Quotient.mk_out _

def Ctx.mk_rep_betac (Γ : Ctx S) : [(⟦Γ⟧ : QCtx S)]ᵣ ≃β Γ.ctx :=
  choice Γ.mk_out_equiv

lemma QCtx.out_mk_eq (Γ : QCtx S) : ⟦(⟨[Γ]ᵣ, Γ.out.wf⟩ : Ctx S)⟧ = Γ :=
  Quotient.out_eq Γ

end

namespace QCtx

def wf (Γ : QCtx S) : [Γ]ᵣ ⊢ ⬝ := choice Γ.out.wf

section Contextual

structure hom₀ (Γ Δ : Ctx S) where
  seq : PCtx S
  is : Nonempty (isMor Γ.ctx Δ.ctx seq)

def hom₀.is' {Γ Δ : Ctx S} (f : hom₀ Γ Δ) :
    isMor Γ.ctx Δ.ctx f.seq :=
  choice f.is

def _root_.PureTypeSystem.Ctx.proj : (Γ : Ctx S) → hom₀ Γ Γ.tail
| .mk [] _ => ⟨[], ⟨isMor.nil⟩⟩
| .mk (_ :: Γ) h => {
  seq := id₀ 1 Γ
  is := ⟨id₀_isMor (isTrunc.succ _ (isTrunc.zero _)) (choice h)⟩
}

namespace hom₀

def betac {Γ Δ : Ctx S} (γ δ : hom₀ Γ Δ) : Prop := Nonempty (γ.seq ≃β δ.seq)

lemma betac.equivalence :
    Equivalence (@betac _ Γ Δ) where
  refl δ := ⟨PCtx.betac.refl δ.seq⟩
  symm := by intro _ _ ⟨h₁⟩; exact ⟨h₁.symm⟩
  trans := by intro _ _ _ ⟨h₁⟩ ⟨h₂⟩; exact ⟨h₁.trans _ _ _ h₂⟩

instance setoid (Γ Δ : Ctx S) : Setoid (hom₀ Γ Δ) where
  iseqv := betac.equivalence

end hom₀

def hom (Γ Δ : QCtx S) : Type _ := Quotient (hom₀.setoid Γ.out Δ.out)

notation:1024 "[" γ "]ᵣ" => hom₀.seq (Quotient.out γ)

lemma hom₀.mk_out_equiv {Γ Δ : QCtx S} (δ : hom₀ Γ.out Δ.out) : (⟦δ⟧ : hom _ _).out ≈ δ :=
  Quotient.mk_out _

def hom₀.mk_rep_betac {Γ Δ : QCtx S} (δ : hom₀ Γ.out Δ.out) : [(⟦δ⟧ : hom _ _)]ᵣ ≃β δ.seq :=
  choice δ.mk_out_equiv

lemma hom.out_mk_eq {Γ Δ : QCtx S} (δ : hom Γ Δ) : ⟦(⟨[δ]ᵣ, δ.out.is⟩ : hom₀ _ _)⟧ = δ :=
  Quotient.out_eq δ

def hom.is (γ : hom Γ Δ) : isMor [Γ]ᵣ [Δ]ᵣ [γ]ᵣ := choice γ.out.is

protected def id₀ (Γ : QCtx S) : hom₀ Γ.out Γ.out where
  seq := id₀ 0 [Γ]ᵣ
  is := ⟨id_isMor _ Γ.wf⟩

protected def id (Γ : QCtx S) : hom Γ Γ := ⟦Γ.id₀⟧

def id_rep_betac (Γ : QCtx S) : [Γ.id]ᵣ ≃β (id [Γ]ᵣ) :=
  hom₀.mk_rep_betac _

def comp₀ {Γ Δ Θ : QCtx S} (γ : hom Γ Δ) (δ : hom Δ Θ) :
    hom₀ Γ.out Θ.out :=
  { seq := pcomp [γ]ᵣ [δ]ᵣ
    is := ⟨pcomp_isMor Γ.wf Θ.wf γ.is δ.is⟩
  }

def comp {Γ Δ Θ : QCtx S} (γ : hom Γ Δ) (δ : hom Δ Θ) :
    hom Γ Θ := ⟦comp₀ γ δ⟧

def comp_rep_betac {Γ Δ Θ : QCtx S} (γ : hom Γ Δ) (δ : hom Δ Θ) :
    [comp γ δ]ᵣ ≃β pcomp [γ]ᵣ [δ]ᵣ :=
  (hom₀.mk_rep_betac _).trans _ _ _ (PCtx.betac.refl _)

-- todo : simplify the proof using `comp_rep_betac`
instance : Category (QCtx S) where
  Hom := hom
  id := QCtx.id
  comp := comp
  id_comp {Γ Δ} f := by
    rw [← Quotient.out_equiv_out]
    constructor
    simp [comp]
    refine (hom₀.mk_rep_betac _).trans _ _ _ ((pcomp_betac₁ Γ.id_rep_betac).trans _ _ _ ?_)
    rw [id_pcomp f.is]
    apply PCtx.betac.refl _
  comp_id {Γ Δ} f := by
    rw [← Quotient.out_equiv_out]
    constructor
    simp [comp]
    refine (hom₀.mk_rep_betac _).trans _ _ _ ((pcomp_betac₂ Δ.id_rep_betac).trans _ _ _ ?_)
    rw [pcomp_id f.is]
    apply PCtx.betac.refl _
  assoc {Γ Δ Θ Κ} f g h := by
    rw [← Quotient.out_equiv_out]
    constructor
    refine (hom₀.mk_rep_betac _).trans _ _ _
      ((pcomp_betac₁ (hom₀.mk_rep_betac _)).trans _ _ _ ?_)
    refine PCtx.betac.trans _ _ _ ?_ (hom₀.mk_rep_betac _).symm
    refine PCtx.betac.trans _ _ _ ?_ (pcomp_betac₂ (hom₀.mk_rep_betac _)).symm
    simp only [comp₀]
    rw [pcomp_pcomp f.is g.is h.is]
    apply PCtx.betac.refl _

instance : Category (Quotient (Ctx.setoid S)) := QCtx.instCategory

def betac_of_heq {A B A' B' : QCtx S} {f : A ⟶ B} {g : A' ⟶ B'}
  (h₁ : HEq A A') (h₂ : HEq B B') (h₃ : HEq f g) :
    [f]ᵣ ≃β [g]ᵣ := by
  cases h₁; cases h₂
  simp at h₃
  rw [← Quotient.out_equiv_out] at h₃
  exact choice h₃

def comp_eqToHom_rep_betac {A B B' : QCtx S} {f : A ⟶ B} {eq : B = B'} :
    [f ≫ eqToHom eq]ᵣ ≃β [f]ᵣ := by
  apply betac_of_heq (by rfl) (by simpa using eq.symm)
  simp only [comp_eqToHom_heq_iff, heq_eq_eq]

def one : QCtx S := ⟦Ctx.nil⟧

@[simp]
lemma one_rep_length : [(one : QCtx S)]ᵣ.length = 0 :=
  Ctx.nil.mk_rep_betac.length_eq

@[simp]
lemma one_rep : [(one : QCtx S)]ᵣ = [] := by
  rw [← List.length_eq_zero]
  apply one_rep_length

lemma eq_one_iff_rep_length_eq_zero (Γ : QCtx S) :
    Γ = one ↔ [Γ]ᵣ.length = 0 := by
  constructor
  . intro h; simp only [h, one_rep, List.length_nil]
  . intro h
    rw [← Γ.out_mk_eq]
    simp at h
    simp [h, one]

def hom_one (Γ : QCtx S) : Γ ⟶ one := by
  apply Quotient.mk' {
    seq := []
    is := ⟨by simpa using isMor.nil⟩
  }

lemma hom.eq_iff_nonempty_rep_betac {Γ Δ : QCtx S} {γ δ : Γ ⟶ Δ} :
    γ = δ ↔  Nonempty ([γ]ᵣ ≃β [δ]ᵣ) := by
  rw [← Quotient.out_equiv_out]
  rfl

@[simp]
lemma hom_one_rep_eq_nil (Γ : QCtx S) (h : Γ ⟶ one) : [h]ᵣ = [] := by
  obtain ⟨is⟩ := h.out.is
  simp at is
  exact is.of_nil

lemma hom_one_uniq (Γ : QCtx S) (h : Γ ⟶ one) : h = Γ.hom_one := by
  rw [hom.eq_iff_nonempty_rep_betac]
  simp
  exact ⟨PCtx.betac.refl _⟩

def ft (Γ : QCtx S) : QCtx S := ⟦Γ.out.tail⟧

def ft_rep_betac_rep_tail (Γ : QCtx S) :
    [Γ.ft]ᵣ ≃β [Γ]ᵣ.tail := by
  rw [← Γ.out.tail_eq_list_tail]
  exact Γ.out.tail.mk_rep_betac

def ft_mk_cons_rep_betac (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)) :
    [ft ⟦Γ.cons A h⟧]ᵣ ≃β Γ :=
  (ft_rep_betac_rep_tail ⟦Γ.cons A h⟧).trans _ _ _
    ((Γ.cons A h).mk_rep_betac.tail')

@[simp]
lemma ft_cons_eq (Γ : QCtx S) (A : PTerm S) (h : Nonempty (A :: [Γ]ᵣ ⊢ ⬝)) :
    ft ⟦[Γ]ᵣ.cons A h⟧ = Γ := by
  rw [← Quotient.out_equiv_out]
  exact ⟨by apply ft_mk_cons_rep_betac⟩

def proj₀ (Γ : Ctx S) : hom ⟦Γ⟧ (ft ⟦Γ⟧) := Quotient.mk' {
  seq := id₀ 1 Γ.ctx.tail
  is := ⟨isMor_betac Γ.wf' (Ctx.wf' _) (Ctx.wf' _) Γ.mk_rep_betac.symm
      ((Γ.mk_rep_betac.tail'.symm).trans _ _ _ (ft_rep_betac_rep_tail _).symm)
      (id₀_isMor_tail Γ.wf')⟩
}

lemma hom_heq_of_betac {Γ Γ' Δ Δ' : QCtx S} (h₁ : Γ = Γ') (h₂ : Δ = Δ')
  {f : Γ ⟶ Δ} {g : Γ' ⟶ Δ'} (h₃ : [f]ᵣ ≃β [g]ᵣ) :
    HEq f g := by
  cases h₁; cases h₂
  simp; rw [← Quotient.out_equiv_out]
  exact ⟨h₃⟩

lemma proj₀_sound (Γ Δ : Ctx S) (h : Γ ≈ Δ) : HEq (proj₀ Γ) (proj₀ Δ) := by
  apply hom_heq_of_betac (Quotient.sound h) (congrArg _ (Quotient.sound h))
  refine ((hom₀.mk_rep_betac _).trans _ _ _ ?_).trans _ _ _ ((hom₀.mk_rep_betac _).symm)
  simp only [Ctx.tail_eq_list_tail, id₀]
  convert PCtx.betac.refl _ using 2
  simp [(choice h).length_eq]

def proj (Γ : QCtx S) : Γ ⟶ Γ.ft :=
  Quotient.hrecOn (motive := fun Γ : QCtx S ↦ Γ ⟶ Γ.ft) _ _ proj₀_sound

@[simp]
lemma proj_spec (Γ : Ctx S) : proj ⟦Γ⟧ = proj₀ Γ := rfl

instance instPreContextualCategory : PreContextualCategory (QCtx S) where
  gr Γ := [Γ]ᵣ.length
  one := one
  one_gr := one_rep_length
  one_uniq := by intros; rwa [eq_one_iff_rep_length_eq_zero]
  one_terminal := IsTerminal.ofUniqueHom (fun Γ ↦ hom_one Γ) hom_one_uniq
  ft := ft
  ft_one := by
    simp [one, ft, Quotient.sound (Ctx.tail_sound (Ctx.nil.mk_out_equiv))]
  ft_gr := by
    intro n Γ h
    simp at h ⊢
    rw [Γ.ft_rep_betac_rep_tail.length_eq, List.length_tail, h,
      Nat.add_one_sub_one]
  proj := proj

open PreContextualCategory

lemma false_of_NR_one (h : NR (one : QCtx S)) : False := by
  have := h.nr
  erw [one_gr] at this
  trivial

instance (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)) :
    @NR _ instPreContextualCategory ⟦Γ.cons A h⟧ where
  nr := by simp only [gr]; rw [(Γ.cons A h).mk_rep_betac.length_eq]; simp [PCtx.cons]

lemma NR_cons_iff_true (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)) :
    @NR _ instPreContextualCategory ⟦Γ.cons A h⟧ ↔ True := by
  simp only [iff_true]; infer_instance

lemma NR_cons_iff_true' (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)) :
    @NR _ instPreContextualCategory ⟦{ctx := A :: Γ, wf := h}⟧ ↔ True := by
  apply NR_cons_iff_true _ _ h

def cases_cons' {motive : (Γ : Ctx S) → [@NR _ instPreContextualCategory ⟦Γ⟧] → Sort w}
  (h : ∀ (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)), motive (Γ.cons A h)) :
    ∀ (Γ : Ctx S) [@NR _ instPreContextualCategory ⟦Γ⟧], motive Γ
| .mk [] _, h => by simpa using false_of_NR_one h
| .mk (A :: Γ) h₀, h₁ => h Γ A  h₀

lemma auxheq {α β : Sort u} {a : α} {b : β} (h : HEq a b) :
    HEq α β := by
  cases h; rfl

lemma heq_prop_ext (A B : Prop) (U : A → Sort u) (F : (a : A) → U a)
  (V : B → Sort u) (G : (b : B) → V b) (a : A) (b : B) (h : HEq (F a) (G b)) :
    HEq F G := by
  have h₀ : A ↔ B :=
    ⟨fun _ ↦ b, fun _ ↦ a⟩
  simp only [← eq_iff_iff] at h₀
  cases h₀
  have : a = b := rfl
  cases this
  have h' : HEq (U a) (V a) := by
    apply auxheq h
  simp at h'
  have : U = V := by ext; exact h'
  cases this
  simp at h ⊢
  ext; exact h

lemma cases_cons_aux {motive : (Γ : QCtx S) → [NR Γ] → Sort w}
  (h : ∀ (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)), motive ⟦Γ.cons A h⟧)
  (h' : ∀ (Γ Δ : PCtx S) (A B : PTerm S) (h₁ : Nonempty (A :: Γ ⊢ ⬝))
    (h₂ : Nonempty (B :: Δ ⊢ ⬝)), Γ.cons A h₁ ≈ Δ.cons B h₂ → HEq (h Γ A h₁) (h Δ B h₂)) :
  ∀ (Γ Δ : Ctx S), Γ ≈ Δ →
    HEq (@cases_cons' S (fun x ↦ @motive ⟦x⟧) h Γ) (@cases_cons' S (fun x ↦ @motive ⟦x⟧) h Δ)
| .mk [] _, b, h₁ => by cases Ctx.eq_nil_of_equiv_nil (Setoid.symm h₁); rfl
| a, .mk [] _, h₁ => by cases Ctx.eq_nil_of_equiv_nil h₁; rfl
| .mk (A :: Γ) h₀, .mk (B :: Δ) h₁, h₂ => by
  apply heq_prop_ext
  apply h' Γ Δ A B h₀ h₁ h₂

@[elab_as_elim]
def cases_cons {motive : (Γ : QCtx S) → [NR Γ] → Sort w}
  (h : ∀ (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)), motive ⟦Γ.cons A h⟧)
  (h' : ∀ (Γ Δ : PCtx S) (A B : PTerm S) (h₁ : Nonempty (A :: Γ ⊢ ⬝))
    (h₂ : Nonempty (B :: Δ ⊢ ⬝)), Γ.cons A h₁ ≈ Δ.cons B h₂ → HEq (h Γ A h₁) (h Δ B h₂))
  (Γ : QCtx S) [NR Γ] :
    motive Γ :=
  Quotient.hrecOn (motive := fun Γ : QCtx S ↦ ([NR Γ] → motive Γ)) _ (cases_cons' h)
    (cases_cons_aux h h')

/-
-- interesting..
lemma cases_cons_spec {motive : (Γ : QCtx S) → [NR Γ] → Sort w}
  (h : ∀ (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)), motive ⟦Γ.cons A h⟧)
  (h' : ∀ (Γ Δ : PCtx S) (A B : PTerm S) (h₁ : Nonempty (A :: Γ ⊢ ⬝))
    (h₂ : Nonempty (B :: Δ ⊢ ⬝)), Γ.cons A h₁ ≈ Δ.cons B h₂ → HEq (h Γ A h₁) (h Δ B h₂))
  (Γ : PCtx S) (A : PTerm S) (hΓ : Nonempty (A :: Γ ⊢ ⬝)) :
    (@cases_cons S motive h h' ⟦Γ.cons A hΓ⟧ _) = h Γ A hΓ := rfl
-/

def cases_cons_prop {motive : (Γ : QCtx S) → [NR Γ] → Prop}
  (h : ∀ (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)), motive ⟦Γ.cons A h⟧)
  (Γ : QCtx S) [NR Γ] :
    motive Γ :=
  Quotient.ind (motive := fun Γ : QCtx S ↦ ([NR Γ] → motive Γ)) (cases_cons' h) Γ

def simulSubst_cons_wf {Δ : QCtx S} {Γ : PCtx S} {A : PTerm S}
  {h : Nonempty (A :: Γ ⊢ ⬝)} (f : Δ ⟶ ft ⟦Γ.cons A h⟧) :
    simulSubst A 0 [f]ᵣ :: [Δ]ᵣ ⊢ ⬝ := by
  apply simulSubst_wf _ ((isMor'_of_isMor f.is).append A)
  simp; rw [← List.cons_append]
  apply append_wf Δ.wf
    (ctx_betac_wf_cons (choice h) (wf _) (ft_mk_cons_rep_betac _ _ _).symm)

def pb_cons₀ (Δ : QCtx S) (Γ : PCtx S) (A : PTerm S)
  (h : Nonempty (A :: Γ ⊢ ⬝)) (f : Δ ⟶ ft ⟦Γ.cons A h⟧) :
    Ctx S where
  ctx := simulSubst A 0 [f]ᵣ :: [Δ]ᵣ
  wf := ⟨simulSubst_cons_wf f⟩

def pb_cons (Δ : QCtx S) (Γ : PCtx S) (A : PTerm S)
  (h : Nonempty (A :: Γ ⊢ ⬝)) (f : Δ ⟶ ft ⟦Γ.cons A h⟧) :
    QCtx S :=
  ⟦pb_cons₀ Δ Γ A h f⟧

def pb_cons_rep_betac {Δ : QCtx S} {Γ : PCtx S} {A : PTerm S}
  {h : Nonempty (A :: Γ ⊢ ⬝)} (f : Δ ⟶ ft ⟦Γ.cons A h⟧) :
    [Δ.pb_cons Γ A h f]ᵣ ≃β simulSubst A 0 [f]ᵣ :: [Δ]ᵣ :=
  Ctx.mk_rep_betac _

lemma heq_aux_func {A B : Sort u} {C : Sort v} (f : A → C) (g : B → C) (h : A = B)
  (h' : ∀ (a : A) (b : B), HEq a b → f a = g b) :
    HEq f g := by
  cases h
  simp
  ext c
  apply h'
  rfl

lemma pb_cons_sound_aux {Δ : QCtx S} {Γ Γ' : PCtx S} {A A' : PTerm S}
  {h : Nonempty (A :: Γ ⊢ ⬝)} {h' : Nonempty (A' :: Γ' ⊢ ⬝)} (eqv : Γ.cons A h ≈ Γ'.cons A' h')
  (f : Δ ⟶ ft ⟦Γ.cons A h⟧) (f' : Δ ⟶ ft ⟦Γ'.cons A' h'⟧) (hf : HEq f f') :
    Δ.pb_cons Γ A h f = Δ.pb_cons Γ' A' h' f' := by
  rw [← Quotient.out_equiv_out]
  constructor
  simp [pb_cons]
  refine (Ctx.mk_rep_betac _).trans _ _ _ ?_
  refine PCtx.betac.trans _ _ _ ?_ (Ctx.mk_rep_betac _).symm
  simp [pb_cons₀]
  apply betac.of_head_of_eq
  apply simulSubst_betac (choice eqv).head
  apply betac_of_heq (HEq.refl _) _ hf
  congr 1; apply Quotient.sound eqv

lemma pb_cons_sound (Δ : QCtx S) (Γ Γ' : PCtx S) (A A' : PTerm S)
  (h : Nonempty (A :: Γ ⊢ ⬝)) (h' : Nonempty (A' :: Γ' ⊢ ⬝)) (eqv : Γ.cons A h ≈ Γ'.cons A' h') :
    HEq (Δ.pb_cons Γ A h) (Δ.pb_cons Γ' A' h') := by
  apply heq_aux_func
  . congr 2; apply Quotient.sound eqv
  . apply pb_cons_sound_aux eqv

def pb {Γ Δ : QCtx S} [NR Γ] : (f : Δ ⟶ Γ.ft) → QCtx S :=
  cases_cons (pb_cons Δ) (pb_cons_sound Δ) Γ

@[simp]
lemma pb_spec {Δ : QCtx S} {Γ : PCtx S} {A : PTerm S}
  {h : Nonempty (A :: Γ ⊢ ⬝)} {f : Δ ⟶ ft ⟦Γ.cons A h⟧} :
    pb f = Δ.pb_cons Γ A h f := rfl

/-
-- error :
def pb {Γ Δ : QCtx S} [NR Γ] (f : Δ ⟶ Γ.ft) : QCtx S :=
  cases_cons (pb_cons Δ) (pb_cons_sound Δ) Γ
-/

def pb_fst_cons₀ (Δ : QCtx S) (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝))
    (f : Δ ⟶ ft ⟦Γ.cons A h⟧) : hom₀ (Δ.pb_cons Γ A h f).out (⟦Γ.cons A h⟧ : QCtx S).out where
  seq := (#0) :: [f]ᵣ.lift 1 0
  is := ⟨by
    have : ((simulSubst A 0 [f]ᵣ) ↑ 1) = simulSubst A 0 ([f]ᵣ ↑↑ 1):= by
      apply simulSubst_lift
      simp [← f.is.length_eq, (ft_mk_cons_rep_betac _ _ _).length_eq]
      apply lift_inv_of_typing (exists_of_cons' (choice h)).snd
    apply isMor_betac (Ctx.wf' _) (wf _) (Ctx.wf' _) (Ctx.mk_rep_betac _).symm
      (Ctx.mk_rep_betac _).symm
    apply isMor.cons
    apply isMor.weakening_cons (Δ.pb_cons₀ Γ A h f).wf' (wf_of_cons (choice h))
    apply isMor_betac₂ (wf _) (ft_mk_cons_rep_betac _ _ _) (wf_of_cons (choice h)) f.is
    simp [pb_cons₀]
    rw [← this]; apply (weakening_cons_typing (Δ.pb_cons₀ Γ A h f).wf').snd
    rw [← this]; apply typing.var _ _ _ (Ctx.wf' _) ⟨_, rfl, isItem.zero _⟩⟩

def pb_fst_cons (Δ : QCtx S) (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝))
  (f : Δ ⟶ ft ⟦Γ.cons A h⟧) :
    Δ.pb_cons Γ A h f ⟶ ⟦Γ.cons A h⟧ := ⟦Δ.pb_fst_cons₀ Γ A h f⟧

lemma heq_aux_dep_func {A B : Sort u} {φ : A → Sort v} {ψ : B → Sort v}
  (f : (a : A) → φ a) (g : (b : B) → ψ b) (h₁ : A = B) (h₂ : HEq φ ψ)
  (h₃ : ∀ (a : A) (b : B), HEq a b → HEq (f a) (g b)) :
    HEq f g := by
  cases h₁; cases h₂
  simp; ext c
  simpa using h₃ c c (by rfl)

lemma pb_fst_cons_sound (Δ : QCtx S) (Γ Γ' : PCtx S) (A A' : PTerm S)
  (h : Nonempty (A :: Γ ⊢ ⬝)) (h' : Nonempty (A' :: Γ' ⊢ ⬝)) (eqv : Γ.cons A h ≈ Γ'.cons A' h'):
    HEq (Δ.pb_fst_cons Γ A h) (Δ.pb_fst_cons Γ' A' h') := by
  apply heq_aux_dep_func
  . rw [Quotient.sound eqv]
  . apply heq_aux_func
    . rw [Quotient.sound eqv]
    . intro f g hfg
      rw [Quotient.sound eqv]
      congr 1
      apply pb_cons_sound_aux eqv _ _ hfg
  . intro f g hfg
    apply hom_heq_of_betac (pb_cons_sound_aux eqv _ _ hfg) (Quotient.sound eqv)
    refine ((hom₀.mk_rep_betac _).trans _ _ _ ?_).trans _ _ _ (hom₀.mk_rep_betac _).symm
    exact (betac_of_heq (by rfl) (by rw [Quotient.sound eqv]) hfg).lift.of_tail_of_eq

def pb_fst {Γ Δ : QCtx S} [NR Γ] : (f : Δ ⟶ Γ.ft) → (pb f ⟶ Γ) := by
  apply cases_cons (motive := fun (x : QCtx S) [NR x] ↦ (f : Δ ⟶ x.ft) → (pb f ⟶ x))
    Δ.pb_fst_cons Δ.pb_fst_cons_sound

@[simp]
lemma pb_fst_spec {Δ : QCtx S} {Γ : PCtx S} {A : PTerm S}
  {h : Nonempty (A :: Γ ⊢ ⬝)} {f : Δ ⟶ ft ⟦Γ.cons A h⟧} :
    pb_fst f = Δ.pb_fst_cons Γ A h f := rfl

lemma gr_pb_cons (Δ : QCtx S) (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝))
  (f : Δ ⟶ ft ⟦Γ.cons A h⟧) :
    gr (Δ.pb_cons Γ A h f) ≠ 0 := by
  simp only [gr, pb_cons]
  rw [(Ctx.mk_rep_betac _).length_eq]
  simp [pb_cons₀]

lemma gr_pb {Γ Δ : QCtx S} [NR Γ] {f : Δ ⟶ Γ.ft} :
  gr (pb f) ≠ 0 :=
  cases_cons_prop (motive := fun (x : QCtx S) [NR x] ↦ {f : Δ ⟶ ft x} → gr (pb f) ≠ 0)
    (gr_pb_cons Δ) Γ

lemma ft_pb_cons (Δ : QCtx S) (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝))
  (f : Δ ⟶ ft ⟦Γ.cons A h⟧) :
    (Δ.pb_cons Γ A h f).ft = Δ := by
  rw [← Quotient.out_equiv_out]
  exact ⟨(ft_rep_betac_rep_tail _).trans _ _ _ (Ctx.mk_rep_betac _).tail'⟩

lemma ft_pb {Γ Δ : QCtx S} [NR Γ] {f : Δ ⟶ Γ.ft} :
  ft (pb f) = Δ :=
  cases_cons_prop (motive := fun (x : QCtx S) [NR x] ↦ {f : Δ ⟶ ft x} → ft (pb f) = Δ)
    (ft_pb_cons Δ) Γ


section

namespace isPullback_cons

variable {Δ : QCtx S} {Γ : PCtx S} {A : PTerm S}
  {h : Nonempty (A :: Γ ⊢ ⬝)} (f : Δ ⟶ ⟦Γ.cons A h⟧)

def rep_not_nil: [f]ᵣ ≠ [] := by
  apply List.ne_nil_of_length_eq_add_one (n := Γ.length)
  rw [← f.is.length_eq, (Ctx.mk_rep_betac _).length_eq]
  simp only [PCtx.cons, List.length_cons]

def tail : PCtx S := [f]ᵣ.tail

def head : PTerm S := [f]ᵣ.head (rep_not_nil f)

def head_cons_tail : head f :: tail f = [f]ᵣ :=
  List.head_cons_tail _ (rep_not_nil f)

variable {f : Δ ⟶ ft ⟦Γ.cons A h⟧} (s : PullbackCone (proj ⟦Γ.cons A h⟧) f)

def fst_isMor : isMor [s.pt]ᵣ  (A :: Γ) (head s.fst :: tail s.fst) := by
  rw [head_cons_tail]
  exact isMor_betac₂ (wf _) (Ctx.mk_rep_betac _) (choice h) s.fst.is

def tail_fst_betac (m : Δ ⟶ ⟦Γ.cons A h⟧) :
    tail m ≃β pcomp [m]ᵣ [proj ⟦Γ.cons A h⟧]ᵣ := by
  refine PCtx.betac.trans _ _ _ ?_ (pcomp_betac₂ (hom₀.mk_rep_betac _).symm)
  have : id₀ 1 Γ = id₀ 1 (tail m) := by
    simp only [id₀, tail, PCtx.cons, List.length_tail, ← m.is.length_eq,
    (Ctx.mk_rep_betac _).length_eq, List.length_cons, Nat.add_one_sub_one]
  simp [PCtx.cons, this]
  rw [pcomp_id₀_aux]
  apply PCtx.betac.refl
  rw [← head_cons_tail]
  apply isTrunc.succ _ (isTrunc.zero _)

def condition_betac : pcomp [s.fst]ᵣ [proj ⟦Γ.cons A h⟧]ᵣ ≃β pcomp [s.snd]ᵣ [f]ᵣ :=
  (((comp_rep_betac _ _).symm).trans _ _ _
    (choice (Quotient.out_equiv_out.mpr s.condition))).trans _ _ _ (comp_rep_betac _ _)

def simulSubst_tail_betac :
    simulSubst A 0 (tail s.fst) ≃β simulSubst (simulSubst A 0 [f]ᵣ) 0 [s.snd]ᵣ := by
  refine ((tail_fst_betac _).trans _ _ _ (condition_betac s)).simulSubst.trans _ _ _ ?_
  rw [simulSubst_pcomp _ s.snd.is f.is (isTrunc.zero _)]
  apply betac.refl _
  apply lift_inv_of_cons_wf
    ((ctx_betac_wf_cons (choice h) (wf _) (ft_mk_cons_rep_betac _ _ _).symm))

def append_pt_typing_sort :
    Σt, List.append [Δ]ᵣ [s.pt]ᵣ ⊢ simulSubst A 0 [f]ᵣ : !t := by
  apply exists_of_cons'
  erw [← List.cons_append]
  apply append_wf s.pt.wf (simulSubst_cons_wf _)

def lift₀ : hom₀ s.pt.out (Δ.pb_cons Γ A h f).out where
  seq := head s.fst :: [s.snd]ᵣ
  is := ⟨by
    have := simulSubst_typing (append_pt_typing_sort s).2 (isMor'_of_isMor s.snd.is)
    simp at this
    apply isMor_betac₂ (wf _) (pb_cons_rep_betac f).symm (wf _)
    apply isMor.cons s.snd.is
    exact this
    exact typing.conv _ _ _ _ _ (simulSubst_tail_betac _) (fst_isMor s).typing_of_cons this
    ⟩

def lift : s.pt ⟶ (Δ.pb_cons Γ A h f) := ⟦lift₀ s⟧

def head_lift_betac :
    head (lift s) ≃β head s.fst := by
  have := hom₀.mk_rep_betac (lift₀ s)
  rw [← head_cons_tail] at this
  exact this.head

def tail_lift_betac :
    tail (lift s) ≃β [s.snd]ᵣ := by
  have := hom₀.mk_rep_betac (lift₀ s)
  rw [← head_cons_tail] at this
  exact this.tail

lemma lift_comp_fst : lift s ≫ Δ.pb_fst_cons Γ A h f = s.fst := by
  rw [← Quotient.out_equiv_out]
  constructor
  refine (comp_rep_betac _ _).trans _ _ _
    ((pcomp_betac (hom₀.mk_rep_betac _) (hom₀.mk_rep_betac _)).trans _ _ _ ?_)
  simp [lift₀, pb_fst_cons₀, pcomp, ← head_cons_tail]
  apply betac.of_head_of_tail
  . rw [simulSubst_var_of_lt (by simp)]
    simp [subst]; apply betac.refl
  . refine PCtx.betac.trans _ _ _ ?_ ((tail_fst_betac _).trans _ _ _ (condition_betac _)).symm
    rw [cons_pcomp_lift_one]
    apply PCtx.betac.refl

lemma lift_comp_snd :
    lift s ≫ (proj (Δ.pb_cons Γ A h f) ≫ eqToHom (Δ.ft_pb_cons Γ A h f)) = s.snd := by
  rw [← Quotient.out_equiv_out]
  constructor
  refine (comp_rep_betac _ _).trans _ _ _
    ((pcomp_betac (hom₀.mk_rep_betac _)
      (comp_eqToHom_rep_betac.trans _ _ _ (hom₀.mk_rep_betac _))).trans _ _ _ ?_)
  simp [lift₀, pb_cons₀]
  have : id₀ 1 [Δ]ᵣ = id₀ 1 [s.snd]ᵣ := by
    simp only [id₀, tail, PCtx.cons, List.length_tail, ← s.snd.is.length_eq,
    (Ctx.mk_rep_betac _).length_eq, List.length_cons, Nat.add_one_sub_one]
  rw [this, pcomp_id₀_aux (isTrunc.succ _ (isTrunc.zero _))]
  apply PCtx.betac.refl

lemma lift_uniq (m : s.pt ⟶ Δ.pb_cons Γ A h f)
  (h₁ : m ≫ Δ.pb_fst_cons Γ A h f = s.fst)
  (h₂ : m ≫ (proj (Δ.pb_cons Γ A h f) ≫ eqToHom (Δ.ft_pb_cons Γ A h f)) = s.snd) :
    m = lift s := by
  rw [← Quotient.out_equiv_out]
  constructor
  rw [← head_cons_tail, ← head_cons_tail]
  apply betac.of_head_of_tail
  . apply Quotient.out_equiv_out.mpr at h₁
    have r := ((pcomp_betac₂ (hom₀.mk_rep_betac _)).symm).trans _ _ _
      (((comp_rep_betac _ _).symm).trans _ _ _ (choice h₁))
    simp [pb_fst_cons₀, pcomp] at r
    rw [← head_cons_tail s.fst] at r
    convert r.head.trans _ _ _ (head_lift_betac s).symm
    . rw [← head_cons_tail m, simulSubst_var_of_isTrunc (isTrunc.zero _)]
  . apply Quotient.out_equiv_out.mpr at h₂
    exact ((tail_fst_betac m).trans _ _ _
      (((pcomp_betac₂ comp_eqToHom_rep_betac).symm).trans _ _ _
      (((comp_rep_betac _ _).symm).trans _ _ _ (choice h₂)))).trans _ _ _
      (tail_lift_betac _).symm

end isPullback_cons
end

lemma isPullback_cons (Δ : QCtx S) (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝))
  (f : Δ ⟶ ft ⟦Γ.cons A h⟧) :
    IsPullback (Δ.pb_fst_cons Γ A h f)
      (proj (Δ.pb_cons Γ A h f) ≫ eqToHom (Δ.ft_pb_cons Γ A h f))
      (proj ⟦Γ.cons A h⟧) f where
  w := by
    rw [← Quotient.out_equiv_out]
    constructor
    simp only [pb_fst_cons, pb_cons, pb_fst_cons₀, proj_spec]
    refine (hom₀.mk_rep_betac _).trans _ _ _
      ((pcomp_betac (hom₀.mk_rep_betac _) (hom₀.mk_rep_betac _)).trans _ _ _ ?_)
    apply PCtx.betac.symm
    refine (hom₀.mk_rep_betac _).trans _ _ _
      ((pcomp_betac₁ (comp_eqToHom_rep_betac.trans _ _ _ (hom₀.mk_rep_betac _))).trans _ _ _ ?_)
    simp only [PCtx.cons, List.tail_cons, comp₀, pb_cons₀]
    rw [pcomp_id₀ (isTrunc.succ _ (isTrunc.zero _)), id₀_pcomp (lift_inv_of_isMor f.is)]
    exact PCtx.betac.refl _
    rw [PCtx.lift_length, ← f.is.length_eq, (ft_mk_cons_rep_betac _ _ _).length_eq]
  isLimit' := ⟨PullbackCone.isLimitAux _ isPullback_cons.lift
      isPullback_cons.lift_comp_fst isPullback_cons.lift_comp_snd
        (fun _ _ hyp ↦ isPullback_cons.lift_uniq _ _
          (hyp WalkingCospan.left) (hyp WalkingCospan.right))⟩

lemma isPullback {Γ Δ : QCtx S} [NR Γ] (f : Δ ⟶ Γ.ft) :
    IsPullback (pb_fst f) (proj (pb f) ≫ eqToHom ft_pb) (proj Γ) f :=
  cases_cons_prop (motive := fun (x : QCtx S) [NR x] ↦ {f : Δ ⟶ ft x} →
      IsPullback (pb_fst f) (proj (pb f) ≫ eqToHom ft_pb) (proj x) f) Δ.isPullback_cons Γ

lemma pullback_id_obj_cons (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)) :
    pb_cons _ Γ A h (𝟙 _) = ⟦Γ.cons A h⟧ := by
  apply Quotient.sound
  constructor
  apply betac.of_head_of_tail _ (ft_mk_cons_rep_betac Γ A h)
  refine (id_rep_betac _).simulSubst.trans _ _ _ ?_
  simp [id, id₀]
  erw [(ft_mk_cons_rep_betac Γ _ _).length_eq, simulSubst_id_of_cons_wf (choice h)]
  apply betac.refl _

lemma pullback_id_obj {Γ : QCtx S} [NR Γ] :
    pb (𝟙 (ft Γ)) = Γ :=
  cases_cons_prop (motive := fun (x : QCtx S) [NR x] ↦ pb (𝟙 (ft x)) = x) pullback_id_obj_cons Γ

variable (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)) (x : QCtx S)

lemma pullback_id_map_cons (Γ : PCtx S) (A : PTerm S) (h : Nonempty (A :: Γ ⊢ ⬝)) :
  HEq (pb_fst (𝟙 (ft ⟦Γ.cons A h⟧))) (𝟙 (⟦Γ.cons A h⟧ : QCtx S)) := by
  apply hom_heq_of_betac (pullback_id_obj_cons Γ A h) rfl
  simp [pb_fst_cons]
  refine ((hom₀.mk_rep_betac _).trans _ _ _ ?_).trans _ _ _ (id_rep_betac _).symm
  simp [pb_fst_cons₀]
  refine (PCtx.betac.of_tail_of_eq (id_rep_betac _).lift).trans _ _ _ ?_
  simp [id, id₀]
  rw [(ft_mk_cons_rep_betac Γ _ _).length_eq, (Ctx.mk_rep_betac _).length_eq]
  simp only [idN, zero_add]
  rw [idN_lift (by simp)]
  apply PCtx.betac.refl _

lemma pullback_id_map {Γ : QCtx S} [NR Γ] :
    HEq (pb_fst (𝟙 (ft Γ))) (𝟙 Γ) :=
  cases_cons_prop (motive := fun (x : QCtx S) [NR x] ↦
    (HEq (pb_fst (𝟙 (ft x))) (𝟙 x))) pullback_id_map_cons Γ

instance NR_pb {Δ Γ : QCtx S} [NR Γ] {f : Δ ⟶ ft Γ} :
    NR (pb f) := ⟨gr_pb⟩

lemma pullback_comp_obj_cons (Δ Θ : QCtx S) (Γ : PCtx S) (A : PTerm S)
  (h : Nonempty (A :: Γ ⊢ ⬝)) (f : Δ ⟶ ft ⟦Γ.cons A h⟧) (g : Θ ⟶ Δ) :
    pb (g ≫ f) = pb (g ≫ eqToHom (ft_pb (f := f).symm)) := by
  apply Quotient.sound
  constructor
  apply betac.of_head_of_eq
  rw [← simulSubst_pcomp (lift_inv_of_cons_wf (choice h)) (hom.is _) _ (isTrunc.zero _)]
  apply PCtx.betac.simulSubst
  refine (hom₀.mk_rep_betac _).trans _ _ _ ?_
  simp [comp₀]
  apply pcomp_betac₁ $ betac_of_heq (by rfl) (by simp [ft_pb_cons])
    (by simp only [heq_comp_eqToHom_iff, heq_eq_eq])
  rw [ft_pb]
  apply isMor_betac₂ (Ctx.wf' _) (ft_mk_cons_rep_betac Γ A h) (wf_of_cons (choice h)) f.is

lemma pullback_comp_obj {Γ Δ Θ : QCtx S} [NR Γ] {f : Δ ⟶ ft Γ} {g : Θ ⟶ Δ} :
    pb (g ≫ f) = pb (g ≫ eqToHom (ft_pb (f := f)).symm) :=
  cases_cons_prop (motive := fun (x : QCtx S) [NR x] ↦ {f : Δ ⟶ ft x} → {g : Θ ⟶ Δ} →
    pb (g ≫ f) = pb (g ≫ eqToHom (ft_pb (f := f)).symm)) (pullback_comp_obj_cons Δ Θ) Γ

lemma pullback_comp_map_cons (Δ Θ : QCtx S) (Γ : PCtx S) (A : PTerm S)
  (h : Nonempty (A :: Γ ⊢ ⬝)) (f : Δ ⟶ ft ⟦Γ.cons A h⟧) (g : Θ ⟶ Δ) :
    HEq (pb_fst (g ≫ f)) (pb_fst (g ≫ eqToHom ft_pb.symm) ≫ pb_fst f) := by
  symm; apply hom_heq_of_betac pullback_comp_obj.symm rfl
  refine ((hom₀.mk_rep_betac _).trans _ _ _ ?_).trans _ _ _ (hom₀.mk_rep_betac _).symm
  refine (pcomp_betac (hom₀.mk_rep_betac _) (hom₀.mk_rep_betac _)).trans _ _ _ ?_
  simp [pb_fst_cons₀]
  let r :  [g ≫ eqToHom (ft_pb (f := f)).symm]ᵣ ≃β [g]ᵣ := by
    apply betac_of_heq (by rfl) (by simp; apply ft_pb_cons)
    simp only [comp_eqToHom_heq_iff, heq_eq_eq]
  refine (pcomp_betac₁ r.lift.of_tail_of_eq).trans _ _ _ ?_
  rw [zero_cons_pcomp_zero_cons]
  refine (PCtx.betac.trans _ _ _ ?_ (hom₀.mk_rep_betac _).symm).lift.of_tail_of_eq
  apply PCtx.betac.refl _
  rw [← g.is.length_eq]
  apply lift_inv_of_isMor f.is

lemma pullback_comp_map {Γ Δ Θ : QCtx S} [NR Γ] {f : Δ ⟶ ft Γ} {g : Θ ⟶ Δ} :
    HEq (pb_fst (g ≫ f)) (pb_fst (g ≫ eqToHom ft_pb.symm) ≫ pb_fst f) :=
  cases_cons_prop (motive := fun (x : QCtx S) [NR x] ↦ {f : Δ ⟶ ft x} → {g : Θ ⟶ Δ} →
    HEq (pb_fst (g ≫ f)) (pb_fst (g ≫ eqToHom ft_pb.symm) ≫ pb_fst f))
      (pullback_comp_map_cons Δ Θ) Γ

instance : ContextualCategory (QCtx S) where
  pb := pb
  pb_fst := pb_fst
  gr_pb := gr_pb
  ft_pb := ft_pb
  isPullback := isPullback
  pullback_id_obj := pullback_id_obj
  pullback_id_map := pullback_id_map
  pullback_comp_obj := pullback_comp_obj
  pullback_comp_map := pullback_comp_map

@[simp]
lemma gr_eq {Γ : QCtx S} :
    PreContextualCategory.gr Γ = [Γ]ᵣ.length := rfl

@[simp]
lemma one_eq :
    PreContextualCategory.one (α := QCtx S) = one := rfl

@[simp]
lemma ft_eq {Γ : QCtx S} :
    PreContextualCategory.ft Γ = ft Γ := rfl

@[simp]
lemma proj_eq {Γ : QCtx S} :
    PreContextualCategory.proj Γ = proj Γ := rfl

@[simp]
lemma pb_eq {Γ Δ : QCtx S} [NR Γ] (f : Δ ⟶ Γ.ft) :
    ContextualCategory.pb f = pb f := rfl

@[simp]
lemma pb_fst_eq {Γ Δ : QCtx S} [NR Γ] (f : Δ ⟶ Γ.ft) :
    ContextualCategory.pb_fst f = pb_fst f := rfl

end Contextual
