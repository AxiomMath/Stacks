module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.ClosureCompactification
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonComp
public import StacksFrontier.CategoryTheory.Adjunction.RightAdjointBaseChangeVerticalPasting

/-!
# The upper shriek functors form a pseudo functor

Draft.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-! ### Vertical pasting of the comparisons of composite derived pullbacks -/

section VPaste

variable {X' M' Y' X M Y : Scheme.{u}} (t : X' ⟶ X) (m : M' ⟶ M) (s : Y' ⟶ Y) (f₁ : X ⟶ M)
  (f₂ : M ⟶ Y) (f₁' : X' ⟶ M') (f₂' : M' ⟶ Y')

/-- The diagram chase behind `derivedPullbackSquare_vpaste_app`, with every morphism a
variable. -/
private theorem vpaste_chase {C C' : Type*} [Category C] [Category C'] (F : C' ⥤ C)
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ : C} {P₁ P₂ P₃ P₄ : C'}
    {A : O₁ ⟶ O₂} {Ew : O₂ ⟶ O₃} {Pi : O₁ ⟶ F.obj P₁} {P : F.obj P₁ ⟶ O₁} {B : P₁ ⟶ P₂}
    {E₂ : P₂ ⟶ P₃} {Ci : P₃ ⟶ P₄} {Cf : P₄ ⟶ P₃} {D : F.obj P₄ ⟶ O₅} {E₁ : O₅ ⟶ O₆}
    {Ti : O₆ ⟶ O₇} {T : O₇ ⟶ O₆} {g : O₇ ⟶ O₈} {T' : O₈ ⟶ O₃} {X₁ : O₆ ⟶ O₃}
    {X₂ : O₅ ⟶ O₄} {E' : O₄ ⟶ O₃} {C₂ : F.obj P₃ ⟶ O₄} {C₃ : F.obj P₂ ⟶ O₂} {E'' : O₂ ⟶ O₄}
    (a₁ : T ≫ X₁ = g ≫ T') (hT : Ti ≫ T = 𝟙 _) (e₁ : X₂ ≫ E' = E₁ ≫ X₁)
    (a₂ : D ≫ X₂ = F.map Cf ≫ C₂) (hC : Ci ≫ Cf = 𝟙 _) (e₂ : F.map E₂ ≫ C₂ = C₃ ≫ E'')
    (a₃ : P ≫ A = F.map B ≫ C₃) (hP : Pi ≫ P = 𝟙 _) (hE : E'' ≫ E' = Ew) :
    A ≫ Ew = Pi ≫ F.map (B ≫ E₂ ≫ Ci) ≫ D ≫ E₁ ≫ Ti ≫ g ≫ T' := by
  rw [← a₁, reassoc_of% hT, ← e₁, reassoc_of% a₂, F.map_comp, F.map_comp, Category.assoc,
    Category.assoc, ← F.map_comp_assoc Ci, hC, F.map_id, Category.id_comp, reassoc_of% e₂,
    ← reassoc_of% a₃, reassoc_of% hP, hE]

/-- **Vertical pasting of the comparisons of composite derived pullbacks around two commutative
squares**, in the ambient spelling: the comparison around the outer rectangle along the composites
`f₁ ≫ f₂` and `f₁' ≫ f₂'` is the pasting of the comparisons of the two squares. -/
theorem derivedPullbackSquare_vpaste_app (w₁ : t ≫ f₁ = f₁' ≫ m) (w₂ : m ≫ f₂ = f₂' ≫ s)
    (w : t ≫ (f₁ ≫ f₂) = (f₁' ≫ f₂') ≫ s) (K : DerivedCategory Y.Modules) :
    (derivedPullbackCompIso (f₁' ≫ f₂') s).hom.app K ≫
        eqToHom (congrArg (fun h : X' ⟶ Y => (derivedPullback h).obj K) w.symm) ≫
        (derivedPullbackCompIso t (f₁ ≫ f₂)).inv.app K =
      (derivedPullbackCompIso f₁' f₂').inv.app ((derivedPullback s).obj K) ≫
        (derivedPullback f₁').map ((derivedPullbackCompIso f₂' s).hom.app K ≫
          eqToHom (congrArg (fun h : M' ⟶ Y => (derivedPullback h).obj K) w₂.symm) ≫
          (derivedPullbackCompIso m f₂).inv.app K) ≫
        (derivedPullbackCompIso f₁' m).hom.app ((derivedPullback f₂).obj K) ≫
        eqToHom (congrArg (fun h : X' ⟶ M => (derivedPullback h).obj ((derivedPullback f₂).obj K))
          w₁.symm) ≫
        (derivedPullbackCompIso t f₁).inv.app ((derivedPullback f₂).obj K) ≫
        (derivedPullback t).map ((derivedPullbackCompIso f₁ f₂).hom.app K) := by
  rw [← cancel_mono ((derivedPullbackCompIso t (f₁ ≫ f₂)).hom.app K)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact vpaste_chase (derivedPullback f₁')
    (derivedPullbackCompIso_assoc_app t f₁ f₂ K) (Iso.inv_hom_id_app _ _)
    (derivedPullbackCompIso_hom_app_eqToHom_left f₂ w₁.symm K)
    (derivedPullbackCompIso_assoc_app f₁' m f₂ K) (Iso.inv_hom_id_app _ _)
    (map_eqToHom_derivedPullbackCompIso_hom_app f₁' w₂.symm K)
    (derivedPullbackCompIso_assoc_app f₁' f₂' s K) (Iso.inv_hom_id_app _ _)
    (eqToHom_trans _ _)

/-- **Vertical pasting of the comparisons of composite derived pullbacks on `D_QCoh`**: for two
commutative squares placed one above the other, the comparison around the outer square along the
composites `f₁ ≫ f₂` and `f₁' ≫ f₂'` is the pasting of the two inner ones. -/
theorem quasiCoherentPullbackComparisonVPaste (w₁ : t ≫ f₁ = f₁' ≫ m) (w₂ : m ≫ f₂ = f₂' ≫ s)
    (w : t ≫ (f₁ ≫ f₂) = (f₁' ≫ f₂') ≫ s) :
    Stacks.CategoryTheory.BaseChange.PullbackComparisonVPaste
      (Lf := quasiCoherentDerivedPullback' f₂) (Lh := quasiCoherentDerivedPullback' f₁)
      (Lo := quasiCoherentDerivedPullback' (f₁ ≫ f₂))
      (Lf' := quasiCoherentDerivedPullback' f₂') (Lh' := quasiCoherentDerivedPullback' f₁')
      (Lo' := quasiCoherentDerivedPullback' (f₁' ≫ f₂'))
      (Lg := quasiCoherentDerivedPullback' s) (Lg' := quasiCoherentDerivedPullback' m)
      (Lk := quasiCoherentDerivedPullback' t)
      (quasiCoherentDerivedPullbackCompIso f₂' s)
      (quasiCoherentDerivedPullbackCompIso m f₂ ≪≫ quasiCoherentDerivedPullbackCongr w₂)
      (quasiCoherentDerivedPullbackCompIso f₁' m)
      (quasiCoherentDerivedPullbackCompIso t f₁ ≪≫ quasiCoherentDerivedPullbackCongr w₁)
      (quasiCoherentDerivedPullbackCompIso (f₁' ≫ f₂') s)
      (quasiCoherentDerivedPullbackCompIso t (f₁ ≫ f₂) ≪≫ quasiCoherentDerivedPullbackCongr w)
      (quasiCoherentDerivedPullbackCompIso f₁ f₂)
      (quasiCoherentDerivedPullbackCompIso f₁' f₂') := by
  intro K
  apply ObjectProperty.hom_ext
  have h := derivedPullbackSquare_vpaste_app t m s f₁ f₂ f₁' f₂' w₁ w₂ w K.obj
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom, Iso.trans_inv,
    quasiCoherentDerivedPullback_map_hom, quasiCoherentDerivedPullbackCompIso_hom_app_hom,
    quasiCoherentDerivedPullbackCompIso_inv_app_hom, quasiCoherentDerivedPullbackCongr_inv_app_hom,
    Functor.map_comp, Category.assoc] at h ⊢
  exact h

end VPaste

/-! ### Coherence of the composition isomorphisms -/

section Coherence

open Stacks.CategoryTheory.BaseChange

/-- **The cocycle identity of [Stacks, Tag 0D5S] on `D_QCoh`.** -/
theorem quasiCoherentDerivedPullbackCompIso_assoc {X M₁ M₂ Y : Scheme.{u}} (f₁ : X ⟶ M₁)
    (f₂ : M₁ ⟶ M₂) (f₃ : M₂ ⟶ Y) (K : quasiCoherentDerivedCategory Y) :
    (quasiCoherentDerivedPullback' f₁).map ((quasiCoherentDerivedPullbackCompIso f₂ f₃).hom.app K) ≫
        (quasiCoherentDerivedPullbackCompIso f₁ (f₂ ≫ f₃)).hom.app K =
      (quasiCoherentDerivedPullbackCompIso f₁ f₂).hom.app
          ((quasiCoherentDerivedPullback' f₃).obj K) ≫
        (quasiCoherentDerivedPullbackCompIso (f₁ ≫ f₂) f₃).hom.app K := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, quasiCoherentDerivedPullback_map_hom,
    quasiCoherentDerivedPullbackCompIso_hom_app_hom]
  exact (derivedPullbackCompIso_assoc_app f₁ f₂ f₃ K.obj).symm

variable {X M₁ M₂ Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace M₁]
  [QuasiSeparatedSpace M₁] [CompactSpace M₂] [QuasiSeparatedSpace M₂] [CompactSpace Y]
  [QuasiSeparatedSpace Y] (f₁ : X ⟶ M₁) (f₂ : M₁ ⟶ M₂) (f₃ : M₂ ⟶ Y)

/-- **Associativity of the composition isomorphisms of derived direct image on `D_QCoh`**,
conjugate to [Stacks, Tag 0D5S]. -/
theorem quasiCoherentDerivedPushforwardCompIso_assoc (K : quasiCoherentDerivedCategory X) :
    (quasiCoherentDerivedPushforward f₃
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f₃)).map
        ((quasiCoherentDerivedPushforwardCompIso f₁ f₂
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
        (quasiCoherentDerivedPushforwardCompIso (f₁ ≫ f₂) f₃
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K =
      (quasiCoherentDerivedPushforwardCompIso f₂ f₃
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app
          ((quasiCoherentDerivedPushforward f₁
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f₁)).obj K) ≫
        (quasiCoherentDerivedPushforwardCompIso f₁ (f₂ ≫ f₃)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K :=
  counitCompatible_assoc (map_quasiCoherentDerivedPushforwardCompIso_comp_counit f₂ f₃)
    (map_quasiCoherentDerivedPushforwardCompIso_comp_counit f₁ f₂)
    (map_quasiCoherentDerivedPushforwardCompIso_comp_counit f₁ (f₂ ≫ f₃))
    (map_quasiCoherentDerivedPushforwardCompIso_comp_counit (f₁ ≫ f₂) f₃)
    (quasiCoherentDerivedPullbackCompIso_assoc f₁ f₂ f₃) K

/-- **Associativity of the composition isomorphisms of twisted inverse images**: the two
identifications of `a_{f₁ ≫ f₂ ≫ f₃}` with `a_{f₃} ⋙ a_{f₂} ⋙ a_{f₁}` agree. -/
theorem twistedInverseImageCompIso_assoc (K : quasiCoherentDerivedCategory Y) :
    (twistedInverseImage f₁ (isQuasicoherent_homology_derivedPushforward_of_qcqs f₁)).map
        ((twistedInverseImageCompIso f₂ f₃ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app K) ≫
        (twistedInverseImageCompIso f₁ (f₂ ≫ f₃)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app K =
      (twistedInverseImageCompIso f₁ f₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app
          ((twistedInverseImage f₃
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f₃)).obj K) ≫
        (twistedInverseImageCompIso (f₁ ≫ f₂) f₃
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app K :=
  counitCompatible_assoc (map_twistedInverseImageCompIso_inv_comp_counit f₁ f₂)
    (map_twistedInverseImageCompIso_inv_comp_counit f₂ f₃)
    (map_twistedInverseImageCompIso_inv_comp_counit (f₁ ≫ f₂) f₃)
    (map_twistedInverseImageCompIso_inv_comp_counit f₁ (f₂ ≫ f₃))
    (quasiCoherentDerivedPushforwardCompIso_assoc f₁ f₂ f₃) K

/-! ### Unit constraints -/

private lemma unit_chase₁ {C : Type*} [Category C] {A B C' D E : C} {x : A ⟶ B} {ci : B ⟶ C'}
    {c : C' ⟶ B} {m : C' ⟶ E} {y : E ⟶ D} {ea eb : B ⟶ D} {ec : A ⟶ E} [Mono y]
    (hc : ci ≫ c = 𝟙 _) (E₁ : m ≫ y = c ≫ ea) (E₂ : x ≫ eb = ec ≫ y) (hab : ea = eb) :
    x ≫ ci ≫ m = ec := by
  rw [← cancel_mono y, Category.assoc, Category.assoc, E₁, reassoc_of% hc, hab, E₂]

private lemma unit_chase₂ {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ : C} {y₀ : O₁ ⟶ O₂}
    {x : O₂ ⟶ O₃} {ci : O₃ ⟶ O₄} {fq : O₄ ⟶ O₅} {e : O₂ ⟶ O₅} {fc : O₁ ⟶ O₄} {c : O₄ ⟶ O₃}
    (A : y₀ ≫ x = fc ≫ c) (B : x ≫ ci ≫ fq = e) (hc : c ≫ ci = 𝟙 _) : y₀ ≫ e = fc ≫ fq := by
  rw [← B, reassoc_of% A, reassoc_of% hc]

/-- A residual identification in the right unit law for derived pullback. -/
theorem derivedPullbackCompIso_comp_id_aux {X Z : Scheme.{u}} (d : X ⟶ Z)
    (M : DerivedCategory Z.Modules) :
    (derivedPullbackCompIso (d ≫ 𝟙 Z) (𝟙 Z)).hom.app M ≫
        (derivedPullbackCompIso d (𝟙 Z ≫ 𝟙 Z)).inv.app M ≫
        (derivedPullback d).map
          (eqToHom (congrArg (fun h : Z ⟶ Z => (derivedPullback h).obj M) (Category.id_comp _))) =
      eqToHom (congrArg (fun h : X ⟶ Z => (derivedPullback h).obj ((derivedPullback (𝟙 Z)).obj M))
        (Category.comp_id d)) :=
  unit_chase₁ (Iso.inv_hom_id_app _ _)
    (map_eqToHom_derivedPullbackCompIso_hom_app d (Category.id_comp (𝟙 Z)) M)
    (derivedPullbackCompIso_hom_app_eqToHom_left (𝟙 Z) (Category.comp_id d) M) rfl

/-- **The right unit law for derived pullback on `D_QCoh`**: `L𝟙^* ⋙ Ld^* ≅ L(d ≫ 𝟙)^* = Ld^*` is
`Ld^*` of the identification `Stacks.Duality.quasiCoherentDerivedPullbackIdIsoOfComp` of `L𝟙^*`
with the identity. -/
theorem quasiCoherentDerivedPullbackCompIso_comp_id {X Z : Scheme.{u}} (d : X ⟶ Z)
    (N : quasiCoherentDerivedCategory Z) :
    (quasiCoherentDerivedPullbackCompIso d (𝟙 Z)).hom.app N ≫
        (quasiCoherentDerivedPullbackCongr (Category.comp_id d)).hom.app N =
      (quasiCoherentDerivedPullback' d).map
        ((quasiCoherentDerivedPullbackIdIsoOfComp Z).hom.app N) := by
  set P := quasiCoherentDerivedPullback' (𝟙 Z)
  set iL := quasiCoherentDerivedPullbackIdIsoOfComp Z
  have hP : ∀ N : quasiCoherentDerivedCategory Z, iL.hom.app (P.obj N) = P.map (iL.hom.app N) := by
    intro N
    rw [← cancel_mono (iL.hom.app N)]
    exact (iL.hom.naturality (iL.hom.app N)).symm
  have key : ∀ N : quasiCoherentDerivedCategory Z,
      (quasiCoherentDerivedPullbackCompIso d (𝟙 Z)).hom.app (P.obj N) ≫
        (quasiCoherentDerivedPullbackCongr (Category.comp_id d)).hom.app (P.obj N) =
      (quasiCoherentDerivedPullback' d).map (iL.hom.app (P.obj N)) := by
    intro N
    have hc : P.map (iL.hom.app N) = (quasiCoherentDerivedPullbackCompIso (𝟙 Z) (𝟙 Z)).hom.app N ≫
        (quasiCoherentDerivedPullbackCongr (Category.id_comp (𝟙 Z))).hom.app N :=
      Functor.FullyFaithful.map_preimage ((Functor.FullyFaithful.id _).ofIso
        (quasiCoherentDerivedPullbackIdIso Z (isQuasicoherent_homology_derivedPullback' _)).symm)
        ((quasiCoherentDerivedPullbackCompIso (𝟙 Z) (𝟙 Z) ≪≫
          quasiCoherentDerivedPullbackCongr (Category.id_comp _)).hom.app N)
    rw [hP, hc]
    apply ObjectProperty.hom_ext
    have A := derivedPullbackCompIso_assoc_app d (𝟙 Z) (𝟙 Z) N.obj
    have B := derivedPullbackCompIso_comp_id_aux d N.obj
    simp only [ObjectProperty.FullSubcategory.comp_hom, quasiCoherentDerivedPullback_map_hom,
      quasiCoherentDerivedPullbackCompIso_hom_app_hom,
      quasiCoherentDerivedPullbackCongr_hom_app_hom, Functor.map_comp]
    exact unit_chase₂ A B (Iso.hom_inv_id_app _ _)
  have nat₁ : (quasiCoherentDerivedPullback' d).map (P.map (iL.hom.app N)) ≫
      (quasiCoherentDerivedPullbackCompIso d (𝟙 Z)).hom.app N ≫
        (quasiCoherentDerivedPullbackCongr (Category.comp_id d)).hom.app N =
      (quasiCoherentDerivedPullbackCompIso d (𝟙 Z)).hom.app (P.obj N) ≫
        (quasiCoherentDerivedPullbackCongr (Category.comp_id d)).hom.app (P.obj N) ≫
        (quasiCoherentDerivedPullback' d).map (iL.hom.app N) := by
    have := (quasiCoherentDerivedPullbackCompIso d (𝟙 Z) ≪≫
      quasiCoherentDerivedPullbackCongr (Category.comp_id d)).hom.naturality (iL.hom.app N)
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.comp_map, Category.assoc,
      Functor.id_obj] at this
    exact this
  rw [← cancel_epi ((quasiCoherentDerivedPullback' d).map (P.map (iL.hom.app N))), nat₁,
    reassoc_of% (key N), hP N]

section UnitQcqs

variable {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Z]
  [QuasiSeparatedSpace Z]

variable (Z) in
/-- The isomorphism `R(𝟙_Z)_* ≅ 𝟭` on `D_QCoh(Z)`, conjugate to
`Stacks.Duality.quasiCoherentDerivedPullbackIdIsoOfComp`. -/
abbrev quasiCoherentDerivedPushforwardIdIsoOfComp :
    quasiCoherentDerivedPushforward (𝟙 Z) (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ≅
      𝟭 (quasiCoherentDerivedCategory Z) :=
  Adjunction.rightAdjointUniq
    ((quasiCoherentDerivedAdjunction (𝟙 Z) (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).ofNatIsoLeft
      (quasiCoherentDerivedPullbackIdIsoOfComp Z)) Adjunction.id

/-- The comparison of `adj.ofNatIsoLeft e` with the identity adjunction, at `x`, is the inverse of
`e` followed by the counit of `adj`. -/
private theorem rightAdjointUniq_ofNatIsoLeft_id_hom_app {C : Type*} [Category C] {L G : C ⥤ C}
    (adj : L ⊣ G) (e : L ≅ 𝟭 C) (x : C) :
    (Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) Adjunction.id).hom.app x =
      e.inv.app (G.obj x) ≫ adj.counit.app x := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit (adj.ofNatIsoLeft e) Adjunction.id x
  rw [Adjunction.ofNatIsoLeft_counit] at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.id_map, Adjunction.id_counit,
    NatTrans.id_app, Functor.id_obj] at h
  exact (Category.comp_id _).symm.trans h

variable (Z) in
omit [QuasiSeparatedSpace Z] in
/-- The component of `quasiCoherentDerivedPushforwardIdIsoOfComp Z` at `x` is the inverse of
`quasiCoherentDerivedPullbackIdIsoOfComp Z` at `R(𝟙_Z)_* x` followed by the counit at `x`. -/
theorem quasiCoherentDerivedPushforwardIdIsoOfComp_hom_app (x : quasiCoherentDerivedCategory Z) :
    (quasiCoherentDerivedPushforwardIdIsoOfComp Z).hom.app x =
      (quasiCoherentDerivedPullbackIdIsoOfComp Z).inv.app
          ((quasiCoherentDerivedPushforward (𝟙 Z)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj x) ≫
        (quasiCoherentDerivedAdjunction (𝟙 Z) (isQuasicoherent_homology_derivedPullback' _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).counit.app x :=
  rightAdjointUniq_ofNatIsoLeft_id_hom_app _ _ x

variable (Z) in
/-- The component of `twistedInverseImageIdIsoOfComp Z` at `x` is the inverse of
`quasiCoherentDerivedPushforwardIdIsoOfComp Z` at `(𝟙_Z)^× x` followed by the counit of
`twistedInverseImageAdjunction (𝟙 Z)` at `x`. -/
theorem twistedInverseImageIdIsoOfComp_hom_app (x : quasiCoherentDerivedCategory Z) :
    (twistedInverseImageIdIsoOfComp Z).hom.app x =
      (quasiCoherentDerivedPushforwardIdIsoOfComp Z).inv.app
          ((twistedInverseImage (𝟙 Z)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj x) ≫
        (twistedInverseImageAdjunction (𝟙 Z)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).counit.app x :=
  rightAdjointUniq_ofNatIsoLeft_id_hom_app _ _ x

/-- `Rg₂_*` of the transport `Rg₁_* ≅ Rg₂_*` along `g₁ = g₂`, against the counits. -/
theorem quasiCoherentDerivedPushforwardCongr_counit {g₁ g₂ : X ⟶ Z} (e : g₁ = g₂)
    (M : quasiCoherentDerivedCategory X) :
    (quasiCoherentDerivedPullback' g₂).map ((quasiCoherentDerivedPushforwardCongr e
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app M) ≫
      (quasiCoherentDerivedAdjunction g₂ (isQuasicoherent_homology_derivedPullback' _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).counit.app M =
    (quasiCoherentDerivedPullbackCongr e).inv.app _ ≫
      (quasiCoherentDerivedAdjunction g₁ (isQuasicoherent_homology_derivedPullback' _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).counit.app M := by
  subst e
  have h : (quasiCoherentDerivedPullbackCongr (rfl : g₁ = g₁)).inv = 𝟙 _ := by ext; rfl
  simp [quasiCoherentDerivedPushforwardCongr, h]

/-- `a_{g₂}`-side transport along `g₁ = g₂`, against the counits. -/
theorem twistedInverseImageCongr_counit {g₁ g₂ : X ⟶ Z} (e : g₁ = g₂)
    (M : quasiCoherentDerivedCategory Z) :
    (quasiCoherentDerivedPushforward g₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
        ((twistedInverseImageCongr e (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app M) ≫
      (twistedInverseImageAdjunction g₂
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).counit.app M =
    (quasiCoherentDerivedPushforwardCongr e
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app _ ≫
      (twistedInverseImageAdjunction g₁
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).counit.app M := by
  subst e
  simp [quasiCoherentDerivedPushforwardCongr, twistedInverseImageCongr]

variable (d : X ⟶ Z)

/-- **The left unit law for derived direct image on `D_QCoh`**. -/
theorem quasiCoherentDerivedPushforwardCompIso_id_comp (Y : quasiCoherentDerivedCategory X) :
    (quasiCoherentDerivedPushforwardCompIso (𝟙 X) d
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app Y ≫
      (quasiCoherentDerivedPushforwardCongr (Category.id_comp d)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app Y =
    (quasiCoherentDerivedPushforward d (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
      ((quasiCoherentDerivedPushforwardIdIsoOfComp X).hom.app Y) :=
  Stacks.CategoryTheory.BaseChange.counitCompatible_unit_right
    (quasiCoherentDerivedPushforwardIdIsoOfComp_hom_app X)
    (map_quasiCoherentDerivedPushforwardCompIso_comp_counit (𝟙 X) d)
    (quasiCoherentDerivedPushforwardCongr_counit (Category.id_comp d))
    (fun N => by
      have h := quasiCoherentDerivedPullbackCompIso_inv_app_comp_idIsoOfComp d N
      rw [← cancel_epi ((quasiCoherentDerivedPullbackCompIso (𝟙 X) d).inv.app N),
        Iso.inv_hom_id_app_assoc]
      apply ObjectProperty.hom_ext
      rw [h]
      rfl) Y

/-- **The right unit law for derived direct image on `D_QCoh`**. -/
theorem quasiCoherentDerivedPushforwardCompIso_comp_id (Y : quasiCoherentDerivedCategory X) :
    (quasiCoherentDerivedPushforwardCompIso d (𝟙 Z)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app Y ≫
      (quasiCoherentDerivedPushforwardCongr (Category.comp_id d)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app Y =
    (quasiCoherentDerivedPushforwardIdIsoOfComp Z).hom.app
      ((quasiCoherentDerivedPushforward d
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj Y) :=
  Stacks.CategoryTheory.BaseChange.counitCompatible_unit_left
    (quasiCoherentDerivedPushforwardIdIsoOfComp_hom_app Z)
    (map_quasiCoherentDerivedPushforwardCompIso_comp_counit d (𝟙 Z))
    (quasiCoherentDerivedPushforwardCongr_counit (Category.comp_id d))
    (quasiCoherentDerivedPullbackCompIso_comp_id d) Y

/-- **The left unit law for twisted inverse images**: `a_{𝟙 ≫ d} ≅ a_d ⋙ a_𝟙 ≅ a_d` is the
transport along `𝟙 ≫ d = d`. -/
theorem twistedInverseImageCompIso_id_comp (Y : quasiCoherentDerivedCategory Z) :
    (twistedInverseImageCompIso (𝟙 X) d (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app Y ≫
      (twistedInverseImageCongr (Category.id_comp d)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app Y =
    (twistedInverseImageIdIsoOfComp X).hom.app
      ((twistedInverseImage d (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj Y) :=
  Stacks.CategoryTheory.BaseChange.counitCompatible_unit_left
    (twistedInverseImageIdIsoOfComp_hom_app X)
    (map_twistedInverseImageCompIso_inv_comp_counit (𝟙 X) d)
    (twistedInverseImageCongr_counit (Category.id_comp d))
    (quasiCoherentDerivedPushforwardCompIso_id_comp d) Y

/-- **The right unit law for twisted inverse images**: `a_{d ≫ 𝟙} ≅ a_𝟙 ⋙ a_d ≅ a_d` is the
transport along `d ≫ 𝟙 = d`. -/
theorem twistedInverseImageCompIso_comp_id (Y : quasiCoherentDerivedCategory Z) :
    (twistedInverseImageCompIso d (𝟙 Z) (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app Y ≫
      (twistedInverseImageCongr (Category.comp_id d)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app Y =
    (twistedInverseImage d (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
      ((twistedInverseImageIdIsoOfComp Z).hom.app Y) :=
  Stacks.CategoryTheory.BaseChange.counitCompatible_unit_right
    (twistedInverseImageIdIsoOfComp_hom_app Z)
    (map_twistedInverseImageCompIso_inv_comp_counit d (𝟙 Z))
    (twistedInverseImageCongr_counit (Category.comp_id d))
    (quasiCoherentDerivedPushforwardCompIso_comp_id d) Y

end UnitQcqs

private lemma hom_comp_hom_of_inv_comp_inv {C : Type*} [Category C] {a b c d : C} (α : a ≅ b)
    (β : b ≅ c) (γ : a ≅ d) (δ : d ≅ c) (h : β.inv ≫ α.inv = δ.inv ≫ γ.inv) :
    α.hom ≫ β.hom = γ.hom ≫ δ.hom := by
  have e : (α ≪≫ β).symm = (γ ≪≫ δ).symm := Iso.ext h
  simpa using congrArg (fun i => i.symm.hom) e

/-- Associativity of the composition isomorphisms of twisted inverse images, in the form
`a_{(f₁ ≫ f₂) ≫ f₃} ≅ a_{f₃} ⋙ a_{f₁ ≫ f₂} ≅ a_{f₃} ⋙ a_{f₂} ⋙ a_{f₁}`. -/
theorem twistedInverseImageCompIso_assoc_hom {X M₁ M₂ Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace M₁] [QuasiSeparatedSpace M₁] [CompactSpace M₂]
    [QuasiSeparatedSpace M₂] [CompactSpace Y] [QuasiSeparatedSpace Y] (f₁ : X ⟶ M₁)
    (f₂ : M₁ ⟶ M₂) (f₃ : M₂ ⟶ Y) (K : quasiCoherentDerivedCategory Y) :
    (twistedInverseImageCompIso (f₁ ≫ f₂) f₃
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
      (twistedInverseImageCompIso f₁ f₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app
        ((twistedInverseImage f₃ (isQuasicoherent_homology_derivedPushforward_of_qcqs f₃)).obj K) =
    (twistedInverseImageCompIso f₁ (f₂ ≫ f₃)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
      (twistedInverseImage f₁ (isQuasicoherent_homology_derivedPushforward_of_qcqs f₁)).map
        ((twistedInverseImageCompIso f₂ f₃ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) := by
  have hA := twistedInverseImageCompIso_assoc f₁ f₂ f₃ K
  exact hom_comp_hom_of_inv_comp_inv
    ((twistedInverseImageCompIso (f₁ ≫ f₂) f₃
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).app K)
    ((twistedInverseImageCompIso f₁ f₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).app _)
    ((twistedInverseImageCompIso f₁ (f₂ ≫ f₃)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).app K)
    (δ := (twistedInverseImage f₁ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).mapIso
      ((twistedInverseImageCompIso f₂ f₃ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).app K)) hA.symm

end Coherence

section CongrQcqs

variable {A B C : Scheme.{u}} [CompactSpace A] [QuasiSeparatedSpace A] [CompactSpace B]
  [QuasiSeparatedSpace B] [CompactSpace C] [QuasiSeparatedSpace C]

/-- Transports of twisted inverse images compose. -/
theorem twistedInverseImageCongr_trans {a₁ a₂ a₃ : A ⟶ C} (e₁ : a₁ = a₂) (e₂ : a₂ = a₃)
    (K : quasiCoherentDerivedCategory C) :
    (twistedInverseImageCongr e₁ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
      (twistedInverseImageCongr e₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K =
    (twistedInverseImageCongr (e₁.trans e₂) (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K := by
  subst e₁ e₂
  simp [twistedInverseImageCongr]

/-- The inverse of a transport is the transport back. -/
theorem twistedInverseImageCongr_inv {a₁ a₂ : A ⟶ C} (e : a₁ = a₂)
    (K : quasiCoherentDerivedCategory C) :
    (twistedInverseImageCongr e (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app K =
    (twistedInverseImageCongr e.symm (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K := by
  subst e
  simp [twistedInverseImageCongr]

/-- `a_{g ≫ f} ≅ a_f ⋙ a_g` is natural in `g` with respect to transports. -/
theorem twistedInverseImageCompIso_congr_left {g g' : A ⟶ B} (f : B ⟶ C) (e : g = g')
    (K : quasiCoherentDerivedCategory C) :
    (twistedInverseImageCompIso g f (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
      (twistedInverseImageCongr e (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) =
    (twistedInverseImageCongr (congrArg (· ≫ f) e)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
      (twistedInverseImageCompIso g' f (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K := by
  subst e
  simp [twistedInverseImageCongr]

/-- `a_{g ≫ f} ≅ a_f ⋙ a_g` is natural in `f` with respect to transports. -/
theorem twistedInverseImageCompIso_congr_right (g : A ⟶ B) {f f' : B ⟶ C} (e : f = f')
    (K : quasiCoherentDerivedCategory C) :
    (twistedInverseImageCompIso g f (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
      (twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
        ((twistedInverseImageCongr e (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) =
    (twistedInverseImageCongr (congrArg (g ≫ ·) e)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
      (twistedInverseImageCompIso g f' (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K := by
  subst e
  simp [twistedInverseImageCongr]

/-- A transport along `a = a` is the identity. -/
theorem twistedInverseImageCongr_self {a : A ⟶ C} (e : a = a) :
    (twistedInverseImageCongr e (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)) = Iso.refl _ := rfl

end CongrQcqs


/-! ### The base change map along an open immersion -/

section OpenBaseChange

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] (t : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (s : Y' ⟶ Y)
  [IsOpenImmersion s] (sq : IsPullback t f' f s)

/-- **The base change map `a_f ⋙ Lt^* ⟶ Ls^* ⋙ a_{f'}` of the twisted inverse images** for a
cartesian square with `s : Y' ⟶ Y` an open immersion, built with derived pullback: the map of
[Stacks, Tag 0A9L] read through `Lt^*` and `Ls^*`
(`Stacks.Duality.rightAdjointBaseChange_app_eq_twistedInverseImageRestrictionMap`). -/
def openBaseChange :
    twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ⋙
        quasiCoherentDerivedPullback' t ⟶
      quasiCoherentDerivedPullback' s ⋙
        twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f') :=
  haveI := isIso_rightAdjointSquare_of_isOpenImmersion t f' f s sq
  (Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
    (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
    (quasiCoherentDerivedAdjunction s (isQuasicoherent_homology_derivedPullback' s)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs s))
    (quasiCoherentDerivedAdjunction t (isQuasicoherent_homology_derivedPullback' t)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs t))
    (quasiCoherentDerivedPullbackCompIso f' s)
    (quasiCoherentDerivedPullbackCompIso t f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (twistedInverseImageAdjunction f'
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')))

end OpenBaseChange

section OpenBaseChangeVPaste

variable {X' M' Y' X M Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace M'] [QuasiSeparatedSpace M'] [CompactSpace M]
  [QuasiSeparatedSpace M] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] (t : X' ⟶ X) (m : M' ⟶ M) (s : Y' ⟶ Y) (f₁ : X ⟶ M)
  (f₂ : M ⟶ Y) (f₁' : X' ⟶ M') (f₂' : M' ⟶ Y') [IsOpenImmersion m] [IsOpenImmersion s]
  (sq₁ : IsPullback t f₁' f₁ m) (sq₂ : IsPullback m f₂' f₂ s)
  (sq : IsPullback t (f₁' ≫ f₂') (f₁ ≫ f₂) s)

/-- **Vertical pasting of the base change maps along open immersions** ([Stacks, Tag 0ATR]):
for `f = f₁ ≫ f₂`, the base change map of the outer square is `a_f ≅ a_{f₂} ⋙ a_{f₁}`, then that
of the upper square at `a_{f₂} K`, then `a_{f₁'}` of that of the lower square, then
`a_{f₂'} ⋙ a_{f₁'} ≅ a_{f'}`. -/
theorem openBaseChange_app_vpaste (K : quasiCoherentDerivedCategory Y) :
    (openBaseChange t (f₁' ≫ f₂') (f₁ ≫ f₂) s sq).app K =
      (quasiCoherentDerivedPullback' t).map
          ((twistedInverseImageCompIso f₁ f₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
        (openBaseChange t f₁' f₁ m sq₁).app
          ((twistedInverseImage f₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≫
        (twistedInverseImage f₁' (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
          ((openBaseChange m f₂' f₂ s sq₂).app K) ≫
        (twistedInverseImageCompIso f₁' f₂' (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app
          ((quasiCoherentDerivedPullback' s).obj K) := by
  have := isIso_twoSquare_of_isOpenImmersion t f₁' f₁ m sq₁
  have := isIso_twoSquare_of_isOpenImmersion m f₂' f₂ s sq₂
  have := isIso_twoSquare_of_isOpenImmersion t (f₁' ≫ f₂') (f₁ ≫ f₂) s sq
  exact Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange_app_eq_of_vpaste
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (quasiCoherentPullbackComparisonVPaste t m s f₁ f₂ f₁' f₂' sq₁.w sq₂.w sq.w)
    (map_quasiCoherentDerivedPushforwardCompIso_comp_counit f₁ f₂)
    (map_quasiCoherentDerivedPushforwardCompIso_comp_counit f₁' f₂')
    (map_twistedInverseImageCompIso_inv_comp_counit f₁ f₂)
    (map_twistedInverseImageCompIso_inv_comp_counit f₁' f₂') K

end OpenBaseChangeVPaste

section OpenBaseChangeHPaste

variable {U' V' X' Y' X Y : Scheme.{u}} [CompactSpace U'] [QuasiSeparatedSpace U']
  [CompactSpace V'] [QuasiSeparatedSpace V'] [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (j' : U' ⟶ X') (f'' : U' ⟶ V') (j : V' ⟶ Y') (p : U' ⟶ X) (q : V' ⟶ Y) [IsOpenImmersion g]
  [IsOpenImmersion j] [IsOpenImmersion q] (sq₁ : IsPullback g' f' f g)
  (sq₂ : IsPullback j' f'' f' j) (sqO : IsPullback p f'' f q) (hp : j' ≫ g' = p) (hq : j ≫ g = q)

/-- **Horizontal pasting of the base change maps along open immersions** ([Stacks, Tag 0ATQ]):
the base change map of the outer rectangle is that of the right square followed by that of the
left square, conjugated by the composition isomorphisms of derived pullback. -/
theorem openBaseChange_app_hpaste (K : quasiCoherentDerivedCategory Y) :
    (openBaseChange p f'' f q sqO).app K =
      (quasiCoherentDerivedPullbackCompIso j' g' ≪≫ quasiCoherentDerivedPullbackCongr hp).inv.app
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≫
        (quasiCoherentDerivedPullback' j').map ((openBaseChange g' f' f g sq₁).app K) ≫
        (openBaseChange j' f'' f' j sq₂).app ((quasiCoherentDerivedPullback' g).obj K) ≫
        (twistedInverseImage f'' (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
          ((quasiCoherentDerivedPullbackCongr hq.symm ≪≫
            (quasiCoherentDerivedPullbackCompIso j g).symm).inv.app K) := by
  have : IsOpenImmersion g' := MorphismProperty.of_isPullback sq₁.flip inferInstance
  have := isIso_twoSquare_of_isOpenImmersion g' f' f g sq₁
  have := isIso_twoSquare_of_isOpenImmersion j' f'' f' j sq₂
  have := isIso_twoSquare_of_isOpenImmersion p f'' f q sqO
  exact Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange_app_eq_of_paste _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _
    (quasiCoherentPullbackComparisonPaste g' f' f g j' f'' j p q sq₁.w sq₂.w sqO.w hp hq) K

end OpenBaseChangeHPaste

section OpenBaseChangeCongr

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] (t : X' ⟶ X) (f : X ⟶ Y) (s : Y' ⟶ Y) [IsOpenImmersion s]

/-- The base change map along an open immersion depends on the left vertical morphism only up to
the transport of twisted inverse images. -/
theorem openBaseChange_app_congr {f' f'' : X' ⟶ Y'} (e : f' = f'') (sq : IsPullback t f' f s)
    (sq' : IsPullback t f'' f s) (K : quasiCoherentDerivedCategory Y) :
    (openBaseChange t f'' f s sq').app K =
      (openBaseChange t f' f s sq).app K ≫
        (twistedInverseImageCongr e (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app
          ((quasiCoherentDerivedPullback' s).obj K) := by
  subst e
  simp [twistedInverseImageCongr]

/-- The base change map along an open immersion depends on both vertical morphisms only up to
the transports of twisted inverse images. -/
theorem openBaseChange_app_congr₂ {f₁ f₂ : X ⟶ Y} {f₁' f₂' : X' ⟶ Y'} (e : f₁ = f₂)
    (e' : f₁' = f₂') (sq₁ : IsPullback t f₁' f₁ s) (sq₂ : IsPullback t f₂' f₂ s)
    (K : quasiCoherentDerivedCategory Y) :
    (openBaseChange t f₂' f₂ s sq₂).app K =
      (quasiCoherentDerivedPullback' t).map
          ((twistedInverseImageCongr e (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app K) ≫
        (openBaseChange t f₁' f₁ s sq₁).app K ≫
        (twistedInverseImageCongr e' (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app
          ((quasiCoherentDerivedPullback' s).obj K) := by
  subst e e'
  simp [twistedInverseImageCongr]

end OpenBaseChangeCongr

/-! ### The transformations attached to morphisms of compactifications -/

section Alpha

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y : FTS S} (f : X ⟶ Y)

/-- `α_g` through the base change map `Stacks.Duality.openBaseChange`. -/
theorem upperShriekCompactificationMap_app_eq_openBaseChange
    (c₁ c₂ : CompactificationOf (Over.mk f.left)) (g : c₁.space ⟶ c₂.space)
    (hg : g ≫ c₂.toBase = c₁.toBase) (sq : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion)
    (K : quasiCoherentDerivedCategory Y.left) :
    (upperShriekCompactificationMap f c₁ c₂ g hg sq).app K =
      (quasiCoherentDerivedPullback' c₁.immersion).map
          ((twistedInverseImageCongr hg.symm (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
          (twistedInverseImageCompIso g c₂.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
        (openBaseChange c₁.immersion (𝟙 X.left) g c₂.immersion sq).app
          ((twistedInverseImage c₂.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≫
        (twistedInverseImageIdIsoOfComp X.left).hom.app _ :=
  upperShriekCompactificationMap_app_eq f c₁ c₂ g hg sq K

/-- `α_g` depends on the morphism `g` alone. -/
theorem upperShriekCompactificationMap_congr {c₁ c₂ : CompactificationOf (Over.mk f.left)}
    {g g' : c₁.space ⟶ c₂.space} (e : g = g') (hg : g ≫ c₂.toBase = c₁.toBase)
    (sq : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion)
    (hg' : g' ≫ c₂.toBase = c₁.toBase)
    (sq' : IsPullback c₁.immersion (𝟙 X.left) g' c₂.immersion) :
    upperShriekCompactificationMap f c₁ c₂ g hg sq =
      upperShriekCompactificationMap f c₁ c₂ g' hg' sq' := by
  subst e; rfl

/-- The transport `a_{p₀} ≅ a_{p₁} ⋙ a_h ≅ a_{p₂} ⋙ a_g ⋙ a_h` is the transport through
`a_{h ≫ g}`. -/
theorem twistedInverseImageCongr_compIso_assoc {A B C D : Scheme.{u}} [CompactSpace A]
    [QuasiSeparatedSpace A] [CompactSpace B] [QuasiSeparatedSpace B] [CompactSpace C]
    [QuasiSeparatedSpace C] [CompactSpace D] [QuasiSeparatedSpace D] (h : A ⟶ B) (g : B ⟶ C)
    (p₂ : C ⟶ D) {p₁ : B ⟶ D} {p₀ : A ⟶ D} (e₁ : g ≫ p₂ = p₁) (e₀ : h ≫ p₁ = p₀)
    (e : (h ≫ g) ≫ p₂ = p₀) (K : quasiCoherentDerivedCategory D) :
    ((twistedInverseImageCongr e.symm (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
        (twistedInverseImageCompIso (h ≫ g) p₂
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
      (twistedInverseImageCompIso h g (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app
        ((twistedInverseImage p₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) =
    ((twistedInverseImageCongr e₀.symm (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
        (twistedInverseImageCompIso h p₁ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
      (twistedInverseImage h (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
        ((twistedInverseImageCongr e₁.symm (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
        (twistedInverseImageCompIso g p₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) := by
  subst e₁ e₀
  simp only [twistedInverseImageCongr, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  refine Eq.trans (congrArg (· ≫ _) (Category.id_comp _)) ?_
  exact twistedInverseImageCompIso_assoc_hom h g p₂ K

omit [CompactSpace S] [QuasiSeparatedSpace S] in
private lemma alpha_comp_chase {C D₀ D₁ : Type*} [Category C] [Category D₀] [Category D₁]
    (F : D₀ ⥤ C) (H : D₁ ⥤ D₀) (L : D₁ ⥤ C) (G : C ⥤ C) (ι : G ⟶ 𝟭 C)
    {P₀ P₁ P₂ P₃ : D₀} {Q₀ Q₁ Q₂ : D₁} {E₂ W : C}
    {A₁ : P₀ ⟶ P₁} {A₂ : P₁ ⟶ P₂} {A₃ : P₂ ⟶ H.obj Q₂} {a : P₀ ⟶ P₃} {b : P₃ ⟶ H.obj Q₀}
    {xa : Q₀ ⟶ Q₁} {xb : Q₁ ⟶ Q₂} {Bh : F.obj (H.obj Q₂) ⟶ G.obj (L.obj Q₂)}
    {Bh₀ : F.obj (H.obj Q₀) ⟶ G.obj (L.obj Q₀)} {Bg : L.obj Q₂ ⟶ G.obj E₂}
    {Ti : G.obj (G.obj E₂) ⟶ W} {Cg : W ⟶ G.obj E₂}
    (F4 : A₁ ≫ A₂ ≫ A₃ = a ≫ b ≫ H.map xa ≫ H.map xb)
    (F3 : F.map (H.map (xa ≫ xb)) ≫ Bh = Bh₀ ≫ G.map (L.map (xa ≫ xb)))
    (F1 : Ti ≫ Cg = ι.app (G.obj E₂)) :
    F.map A₁ ≫ F.map A₂ ≫ F.map A₃ ≫ Bh ≫ G.map Bg ≫ Ti ≫ Cg ≫ ι.app E₂ =
      (F.map a ≫ F.map b ≫ Bh₀ ≫ ι.app (L.obj Q₀)) ≫ L.map xa ≫ L.map xb ≫ Bg ≫ ι.app E₂ := by
  have hι := ι.naturality (L.map (xa ≫ xb) ≫ Bg)
  simp only [Functor.id_map] at hι
  calc F.map A₁ ≫ F.map A₂ ≫ F.map A₃ ≫ Bh ≫ G.map Bg ≫ Ti ≫ Cg ≫ ι.app E₂
      = F.map (A₁ ≫ A₂ ≫ A₃) ≫ Bh ≫ G.map Bg ≫ ι.app (G.obj E₂) ≫ ι.app E₂ := by
        rw [reassoc_of% F1]
        simp
    _ = F.map a ≫ F.map b ≫ (F.map (H.map (xa ≫ xb)) ≫ Bh) ≫ G.map Bg ≫
          ι.app (G.obj E₂) ≫ ι.app E₂ := by
        rw [F4]
        simp
    _ = _ := by
        rw [F3, Category.assoc, ← G.map_comp_assoc, reassoc_of% hι]
        simp

/-- **`α` is functorial in the morphism of compactifications**: for `h : X̄₀ ⟶ X̄₁` and
`g : X̄₁ ⟶ X̄₂`, `α_{h ≫ g} = α_h ≫ α_g`. -/
theorem upperShriekCompactificationMap_comp (c₀ c₁ c₂ : CompactificationOf (Over.mk f.left))
    (h : c₀.space ⟶ c₁.space) (g : c₁.space ⟶ c₂.space) (hh : h ≫ c₁.toBase = c₀.toBase)
    (hg : g ≫ c₂.toBase = c₁.toBase) (sq₀₁ : IsPullback c₀.immersion (𝟙 X.left) h c₁.immersion)
    (sq₁₂ : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion)
    (hhg : (h ≫ g) ≫ c₂.toBase = c₀.toBase)
    (sq₀₂ : IsPullback c₀.immersion (𝟙 X.left) (h ≫ g) c₂.immersion) :
    upperShriekCompactificationMap f c₀ c₂ (h ≫ g) hhg sq₀₂ =
      upperShriekCompactificationMap f c₀ c₁ h hh sq₀₁ ≫
        upperShriekCompactificationMap f c₁ c₂ g hg sq₁₂ := by
  refine NatTrans.ext (funext fun K => ?_)
  have sqv : IsPullback c₀.immersion (𝟙 X.left ≫ 𝟙 X.left) (h ≫ g) c₂.immersion := by
    simpa using sq₀₂
  rw [NatTrans.comp_app, upperShriekCompactificationMap_app_eq_openBaseChange,
    upperShriekCompactificationMap_app_eq_openBaseChange,
    upperShriekCompactificationMap_app_eq_openBaseChange,
    openBaseChange_app_congr c₀.immersion (h ≫ g) c₂.immersion (Category.id_comp (𝟙 X.left)) sqv
      sq₀₂,
    openBaseChange_app_vpaste c₀.immersion c₁.immersion c₂.immersion h g (𝟙 X.left) (𝟙 X.left)
      sq₀₁ sq₁₂ sqv]
  simp only [Category.assoc, Functor.map_comp]
  have F4 := twistedInverseImageCongr_compIso_assoc h g c₂.toBase hg hh hhg K
  simp only [Category.assoc, Functor.map_comp] at F4
  exact alpha_comp_chase (quasiCoherentDerivedPullback' c₀.immersion)
    (twistedInverseImage h (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedPullback' c₁.immersion)
    (twistedInverseImage (𝟙 X.left) (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (twistedInverseImageIdIsoOfComp X.left).hom F4
    ((openBaseChange c₀.immersion (𝟙 X.left) h c₁.immersion sq₀₁).naturality _)
    (twistedInverseImageCompIso_id_comp (𝟙 X.left) _)



end Alpha

/-! ### The isomorphisms between the upper shriek functors of two compactifications -/

section Dominating

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [IsNoetherian S] {X Y : FTS S}
  (f : X ⟶ Y)

/-- `α_{h ≫ g} = α_h ≫ α_g` on `D⁺_QCoh`. -/
theorem upperShriekCompactificationIso_trans (c₀ c₁ c₂ : CompactificationOf (Over.mk f.left))
    (h : c₀.space ⟶ c₁.space) (g : c₁.space ⟶ c₂.space) [IsProper h] [IsProper g]
    [IsProper (h ≫ g)] (hh : h ≫ c₁.toBase = c₀.toBase) (hg : g ≫ c₂.toBase = c₁.toBase)
    (sq₀₁ : IsPullback c₀.immersion (𝟙 X.left) h c₁.immersion)
    (sq₁₂ : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion)
    (hhg : (h ≫ g) ≫ c₂.toBase = c₀.toBase)
    (sq₀₂ : IsPullback c₀.immersion (𝟙 X.left) (h ≫ g) c₂.immersion) :
    upperShriekCompactificationIso f c₀ c₂ (h ≫ g) hhg sq₀₂ =
      upperShriekCompactificationIso f c₀ c₁ h hh sq₀₁ ≪≫
        upperShriekCompactificationIso f c₁ c₂ g hg sq₁₂ := by
  refine Iso.ext (NatTrans.ext (funext fun K => ObjectProperty.hom_ext _ ?_))
  simp only [Iso.trans_hom, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]
  exact congrArg (fun τ => τ.app K.obj)
    (upperShriekCompactificationMap_comp f c₀ c₁ c₂ h g hh hg sq₀₁ sq₁₂ hhg sq₀₂)

/-- `α_g` on `D⁺_QCoh` depends on the morphism `g` alone. -/
theorem upperShriekCompactificationIso_congr {c₁ c₂ : CompactificationOf (Over.mk f.left)}
    {g g' : c₁.space ⟶ c₂.space} [IsProper g] [IsProper g'] (e : g = g')
    (hg : g ≫ c₂.toBase = c₁.toBase) (sq : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion)
    (hg' : g' ≫ c₂.toBase = c₁.toBase)
    (sq' : IsPullback c₁.immersion (𝟙 X.left) g' c₂.immersion) :
    upperShriekCompactificationIso f c₁ c₂ g hg sq =
      upperShriekCompactificationIso f c₁ c₂ g' hg' sq' := by
  subst e; rfl

variable (W : CompactificationOf (Over.mk f.left))

/-- The closure of `X` in a compactification, as a compactification. -/
abbrev closureCompactification : CompactificationOf (Over.mk f.left) :=
  CompactificationOf.ofClosedInOpen f W.toBase W.immersion (𝟙 X.left)
    (by rw [Category.id_comp, immersion_comp_toBase])

/-- The closed immersion of the closure of `X` into the compactification. -/
abbrev closureι : (closureCompactification f W).space ⟶ W.space :=
  (CompactificationOf.closedInOpenImmersion W.immersion (𝟙 X.left)).imageι

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The closed immersion `closureι f W` commutes with the structure morphisms to `Y`. -/
theorem closureι_toBase : closureι f W ≫ W.toBase = (closureCompactification f W).toBase := rfl

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The immersion of `X` into its closure is the pullback of `W.immersion` along `closureι f W`. -/
theorem isPullback_closureι :
    IsPullback (closureCompactification f W).immersion (𝟙 X.left) (closureι f W) W.immersion :=
  CompactificationOf.isPullback_closedInOpen W.immersion (𝟙 X.left)

/-- The closed immersion of the closure into the compactification is proper. -/
instance : IsProper (closureι f W) := by dsimp [closureι]; infer_instance

omit [CompactSpace S] [QuasiSeparatedSpace S] [AlgebraicGeometry.IsNoetherian S] in
private lemma isPullback_of_id_id {A B D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ D}
    (h : IsPullback a (𝟙 A ≫ 𝟙 A) b c) : IsPullback a (𝟙 A) b c := by
  simpa using h

omit [CompactSpace S] [QuasiSeparatedSpace S] [AlgebraicGeometry.IsNoetherian S] in
/-- A morphism between compactifications of `X` over `Y` is proper. -/
theorem isProper_of_comp_toBase {c₁ c₂ : CompactificationOf (Over.mk f.left)}
    (g : c₁.space ⟶ c₂.space) (hg : g ≫ c₂.toBase = c₁.toBase) : IsProper g := by
  have : IsProper (g ≫ c₂.toBase) := by rw [hg]; infer_instance
  exact IsProper.of_comp g c₂.toBase

/-- Two factorizations `a ≫ b = a' ≫ b'` of a morphism of compactifications give the same
composite of the isomorphisms `α`. -/
private theorem upperShriekCompactificationIso_trans_eq {S : Scheme.{u}} [QuasiSeparatedSpace S]
    [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y) {c₀ c₁ c₂ c₃ : CompactificationOf (Over.mk f.left)}
    (a : c₀.space ⟶ c₁.space) (b : c₁.space ⟶ c₃.space) (a' : c₀.space ⟶ c₂.space)
    (b' : c₂.space ⟶ c₃.space) [IsProper a] [IsProper b] [IsProper a'] [IsProper b']
    (e : a ≫ b = a' ≫ b') (ha : a ≫ c₁.toBase = c₀.toBase) (hb : b ≫ c₃.toBase = c₁.toBase)
    (ha' : a' ≫ c₂.toBase = c₀.toBase) (hb' : b' ≫ c₃.toBase = c₂.toBase)
    (sqa : IsPullback c₀.immersion (𝟙 X.left) a c₁.immersion)
    (sqb : IsPullback c₁.immersion (𝟙 X.left) b c₃.immersion)
    (sqa' : IsPullback c₀.immersion (𝟙 X.left) a' c₂.immersion)
    (sqb' : IsPullback c₂.immersion (𝟙 X.left) b' c₃.immersion) :
    upperShriekCompactificationIso f c₀ c₁ a ha sqa ≪≫
        upperShriekCompactificationIso f c₁ c₃ b hb sqb =
      upperShriekCompactificationIso f c₀ c₂ a' ha' sqa' ≪≫
        upperShriekCompactificationIso f c₂ c₃ b' hb' sqb' := by
  have hab : (a ≫ b) ≫ c₃.toBase = c₀.toBase := by rw [Category.assoc, hb, ha]
  have hab' : (a' ≫ b') ≫ c₃.toBase = c₀.toBase := by rw [Category.assoc, hb', ha']
  rw [← upperShriekCompactificationIso_trans f c₀ c₁ c₃ a b ha hb sqa sqb hab
      (isPullback_of_id_id (sqa.paste_vert sqb)),
    ← upperShriekCompactificationIso_trans f c₀ c₂ c₃ a' b' ha' hb' sqa' sqb' hab'
      (isPullback_of_id_id (sqa'.paste_vert sqb'))]
  exact upperShriekCompactificationIso_congr f e hab _ hab' _

/-- **The isomorphism between the upper shriek functors of two compactifications is computed by
any compactification dominating both**: for morphisms `u₁ : W ⟶ X̄₁` and `u₂ : W ⟶ X̄₂` of
compactifications with `u_i⁻¹(X) = X`, the isomorphism `f^!_{X̄₁} ≅ f^!_{X̄₂}` of
[Stacks, Tag 0AA0] is `α_{u₁}⁻¹ ≫ α_{u₂}`. -/
theorem upperShriekPlusIso_eq_of_span (c₁ c₂ : CompactificationOf (Over.mk f.left))
    (u₁ : W.space ⟶ c₁.space) (u₂ : W.space ⟶ c₂.space) [IsProper u₁] [IsProper u₂]
    (hu₁ : u₁ ≫ c₁.toBase = W.toBase) (hu₂ : u₂ ≫ c₂.toBase = W.toBase)
    (sq₁ : IsPullback W.immersion (𝟙 X.left) u₁ c₁.immersion)
    (sq₂ : IsPullback W.immersion (𝟙 X.left) u₂ c₂.immersion) :
    DominatingCompactification.upperShriekPlusIso f c₁ c₂ =
      (upperShriekCompactificationIso f W c₁ u₁ hu₁ sq₁).symm ≪≫
        upperShriekCompactificationIso f W c₂ u₂ hu₂ sq₂ := by
  have hl : (𝟙 X.left ≫ W.immersion) ≫ pullback.lift u₁ u₂ (by rw [hu₁, hu₂]) =
      𝟙 X.left ≫ DominatingCompactification.graph f c₁ c₂ := by
    apply pullback.hom_ext
    · simp only [Category.id_comp, Category.assoc, pullback.lift_fst, GraphClosure.graph_fst]
      simpa using sq₁.w
    · simp only [Category.id_comp, Category.assoc, pullback.lift_snd, GraphClosure.graph_snd]
      simpa using sq₂.w
  obtain ⟨v, hv₁, hv₂, hvi⟩ : ∃ v : (closureCompactification f W).space ⟶
      (DominatingCompactification.compactification f c₁ c₂).space,
      v ≫ DominatingCompactification.fst f c₁ c₂ = closureι f W ≫ u₁ ∧
      v ≫ DominatingCompactification.snd f c₁ c₂ = closureι f W ≫ u₂ ∧
      (closureCompactification f W).immersion ≫ v =
        𝟙 X.left ≫ (DominatingCompactification.compactification f c₁ c₂).immersion :=
    ⟨Scheme.Hom.imageMap _ (DominatingCompactification.graph f c₁ c₂) (𝟙 X.left)
      (pullback.lift u₁ u₂ (by rw [hu₁, hu₂])) hl,
      (Scheme.Hom.imageMap_imageι_assoc _ _ _ _ hl _).trans
        (congrArg (fun t => _ ≫ t) (pullback.lift_fst _ _ _)),
      (Scheme.Hom.imageMap_imageι_assoc _ _ _ _ hl _).trans
        (congrArg (fun t => _ ≫ t) (pullback.lift_snd _ _ _)),
      Scheme.Hom.toImage_imageMap _ _ _ _ hl⟩
  have hv : v ≫ (DominatingCompactification.compactification f c₁ c₂).toBase =
      (closureCompactification f W).toBase := by
    have h := congrArg (· ≫ c₁.toBase) hv₁
    simp only [Category.assoc, hu₁] at h
    exact h
  have : IsProper v := isProper_of_comp_toBase f v hv
  have : IsProper (X := (DominatingCompactification.compactification f c₁ c₂).space)
      (DominatingCompactification.fst f c₁ c₂) :=
    (inferInstance : IsProper (DominatingCompactification.fst f c₁ c₂))
  have : IsProper (X := (DominatingCompactification.compactification f c₁ c₂).space)
      (DominatingCompactification.snd f c₁ c₂) :=
    (inferInstance : IsProper (DominatingCompactification.snd f c₁ c₂))
  have sqv : IsPullback (closureCompactification f W).immersion (𝟙 X.left) v
      (DominatingCompactification.compactification f c₁ c₂).immersion := by
    refine IsPullback.of_bot (h₃₁ := c₁.immersion) (v₂₁ := 𝟙 X.left)
      (v₂₂ := DominatingCompactification.fst f c₁ c₂) ?_
      hvi (DominatingCompactification.isPullback_fst f c₁ c₂)
    rw [hv₁]
    exact (isPullback_closureι f W).paste_vert sq₁
  have A₁ := upperShriekCompactificationIso_trans_eq f v (DominatingCompactification.fst f c₁ c₂)
    (closureι f W) u₁ hv₁ hv rfl rfl hu₁ sqv (DominatingCompactification.isPullback_fst f c₁ c₂)
    (isPullback_closureι f W) sq₁
  have A₂ := upperShriekCompactificationIso_trans_eq f v (DominatingCompactification.snd f c₁ c₂)
    (closureι f W) u₂ hv₂ hv (DominatingCompactification.fst_comp_toBase f c₁ c₂).symm rfl hu₂
    sqv (DominatingCompactification.isPullback_snd f c₁ c₂) (isPullback_closureι f W) sq₂
  calc DominatingCompactification.upperShriekPlusIso f c₁ c₂
      = (upperShriekCompactificationIso f (closureCompactification f W)
              (DominatingCompactification.compactification f c₁ c₂) v hv sqv ≪≫
          upperShriekCompactificationIso f (DominatingCompactification.compactification f c₁ c₂) c₁
            (DominatingCompactification.fst f c₁ c₂) rfl
            (DominatingCompactification.isPullback_fst f c₁ c₂)).symm ≪≫
        (upperShriekCompactificationIso f (closureCompactification f W)
              (DominatingCompactification.compactification f c₁ c₂) v hv sqv ≪≫
          upperShriekCompactificationIso f (DominatingCompactification.compactification f c₁ c₂) c₂
            (DominatingCompactification.snd f c₁ c₂)
            (DominatingCompactification.fst_comp_toBase f c₁ c₂).symm
            (DominatingCompactification.isPullback_snd f c₁ c₂)) := by
        rw [Iso.trans_symm, Iso.trans_assoc, Iso.symm_self_id_assoc]
        rfl
    _ = _ := by
        rw [A₁, A₂]
        simp

end Dominating

/-! ### The coherence underlying the naturality of the composition comparison -/



variable {Q₁ Q₂ Y : Scheme.{u}} [CompactSpace Q₁] [QuasiSeparatedSpace Q₁]
  [CompactSpace Q₂] [QuasiSeparatedSpace Q₂] [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- The right unit law for twisted inverse images, read through transports:
`a_{rQ} ≅ a_{rQ ≫ 𝟙} ≅ a_𝟙 ⋙ a_{rQ}` followed by `a_{rQ}(a_𝟙 ≅ 𝟭)` is the transport. -/
theorem twistedInverseImageCompIso_comp_id_congr (rQ₁ : Q₁ ⟶ Y) {p : Q₁ ⟶ Y} (e : p = rQ₁ ≫ 𝟙 Y)
    (e' : p = rQ₁) (M : quasiCoherentDerivedCategory Y) :
    (twistedInverseImageCompIso rQ₁ (𝟙 Y) (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app M ≫
      (twistedInverseImageCongr e (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app M =
    (twistedInverseImage rQ₁ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
        ((twistedInverseImageIdIsoOfComp Y).hom.app M) ≫
      (twistedInverseImageCongr e'.symm (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app M := by
  rw [← twistedInverseImageCompIso_comp_id rQ₁ M, Category.assoc, twistedInverseImageCongr_inv,
    twistedInverseImageCongr_trans]

private lemma square_congr_chase {C : Type*} [Category C] {O0 O1 O1' O2 O3 O4 O5 O6 O7 O8 : C}
    {c₁ : O0 ⟶ O1} {Aφ : O1 ⟶ O2} {m : O2 ⟶ O3} {Ai : O3 ⟶ O4} {ch : O4 ⟶ O5} {Arψ : O5 ⟶ O6}
    {X₁ : O1 ⟶ O4} {Ah : O4 ⟶ O3} {cc : O1 ⟶ O1'} {X₃ : O1' ⟶ O5} {Y₁ : O1' ⟶ O8}
    {Y₂ : O8 ⟶ O6} {B : O0 ⟶ O7} {c₃ : O7 ⟶ O8} {cc' : O0 ⟶ O1'}
    (A1 : X₁ ≫ Ah = Aφ ≫ m) (hi : Ah ≫ Ai = 𝟙 _) (C1 : X₁ ≫ ch = cc ≫ X₃)
    (A2 : X₃ ≫ Arψ = Y₁ ≫ Y₂) (C2 : B ≫ c₃ = cc' ≫ Y₁) (hc : c₁ ≫ cc = cc') :
    c₁ ≫ Aφ ≫ m ≫ Ai ≫ ch ≫ Arψ = B ≫ c₃ ≫ Y₂ := by
  rw [← reassoc_of% A1, reassoc_of% hi, reassoc_of% C1, A2, reassoc_of% C2, reassoc_of% hc]

variable {R₁ R₂ B₁ B₂ Z : Scheme.{u}} [CompactSpace R₁] [QuasiSeparatedSpace R₁]
  [CompactSpace R₂] [QuasiSeparatedSpace R₂] [CompactSpace B₁] [QuasiSeparatedSpace B₁]
  [CompactSpace B₂] [QuasiSeparatedSpace B₂] [CompactSpace Z] [QuasiSeparatedSpace Z] in
/-- For a commutative square `φ ≫ r₂ = r₁ ≫ ψ` over `ψ ≫ q₂ = q₁`, the two identifications of
`a_{r₁ ≫ q₁}` with `a_{q₂} ⋙ a_ψ ⋙ a_{r₁}`, through `φ` and through `ψ`, agree. -/
theorem twistedInverseImageCompIso_square_congr (r₁ : R₁ ⟶ B₁) (q₁ : B₁ ⟶ Z) (r₂ : R₂ ⟶ B₂)
    (q₂ : B₂ ⟶ Z) (ψ : B₁ ⟶ B₂) (φ : R₁ ⟶ R₂) (hψ : ψ ≫ q₂ = q₁) (hφ : φ ≫ r₂ = r₁ ≫ ψ)
    (e₀ : r₁ ≫ q₁ = φ ≫ r₂ ≫ q₂) (K : quasiCoherentDerivedCategory Z) :
    (twistedInverseImageCongr e₀ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
      (twistedInverseImageCompIso φ (r₂ ≫ q₂)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
      (twistedInverseImage φ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
        ((twistedInverseImageCompIso r₂ q₂
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
      (twistedInverseImageCompIso φ r₂
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).inv.app
        ((twistedInverseImage q₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≫
      (twistedInverseImageCongr hφ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app
        ((twistedInverseImage q₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≫
      (twistedInverseImageCompIso r₁ ψ
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app
        ((twistedInverseImage q₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) =
    (twistedInverseImageCompIso r₁ q₁
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
      (twistedInverseImage r₁ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
        ((twistedInverseImageCongr hψ.symm (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
      (twistedInverseImage r₁ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
        ((twistedInverseImageCompIso ψ q₂
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) :=
  square_congr_chase (twistedInverseImageCompIso_assoc_hom φ r₂ q₂ K)
    (Iso.hom_inv_id_app _ _) (twistedInverseImageCompIso_congr_left q₂ hφ K)
    (twistedInverseImageCompIso_assoc_hom r₁ ψ q₂ K)
    (twistedInverseImageCompIso_congr_right r₁ hψ.symm K)
    ((twistedInverseImageCongr_trans _ _ K).trans rfl)

private lemma core_chase {C : Type*} [Category C] {P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13
    P14 P15 P16 P17 P18 P19 P20 : C}
    {x₁ : P0 ⟶ P1} {x₂ : P1 ⟶ P2} {bF : P2 ⟶ P3} {g₁ : P3 ⟶ P4} {g₂ : P4 ⟶ P5}
    {x₃ : P2 ⟶ P6} {bF' : P6 ⟶ P4} {bFB : P7 ⟶ P8} {y₁ : P7 ⟶ P6} {ai : P5 ⟶ P8}
    {y₁' : P6 ⟶ P7} {ah : P8 ⟶ P5} {bCD : P20 ⟶ P9} {z₁ : P20 ⟶ P7} {ce : P8 ⟶ P9}
    {z₁' : P7 ⟶ P20} {ce' : P9 ⟶ P8} {w₁ : P20 ⟶ P10} {bC' : P10 ⟶ P11} {d : P11 ⟶ P12}
    {aq : P12 ⟶ P9} {b : P0 ⟶ P13} {bC : P13 ⟶ P14} {t₁ : P14 ⟶ P15} {t₂ : P15 ⟶ P16}
    {gw : P16 ⟶ P5} {hw' : P14 ⟶ P17} {t₁' : P17 ⟶ P8} {h₁ : P14 ⟶ P18} {h₂ : P18 ⟶ P11}
    {hι : P12 ⟶ P17} {k₁ : P13 ⟶ P19} {k₂ : P19 ⟶ P10}
    (N1 : x₃ ≫ bF' = bF ≫ g₁) (V1 : bFB = y₁ ≫ bF' ≫ g₂ ≫ ai) (hy : y₁' ≫ y₁ = 𝟙 _)
    (hai : ai ≫ ah = 𝟙 _) (Cg : bCD = z₁ ≫ bFB ≫ ce) (hz : z₁' ≫ z₁ = 𝟙 _)
    (hce : ce ≫ ce' = 𝟙 _) (V2 : bCD = w₁ ≫ bC' ≫ d ≫ aq)
    (NT : hw' ≫ t₁' ≫ ah = t₁ ≫ t₂ ≫ gw) (hw : hw' = h₁ ≫ h₂ ≫ d ≫ hι)
    (NC : k₁ ≫ k₂ ≫ bC' = bC ≫ h₁ ≫ h₂)
    (ha : x₁ ≫ x₂ ≫ x₃ ≫ y₁' ≫ z₁' ≫ w₁ = b ≫ k₁ ≫ k₂) (hb : aq ≫ ce' = hι ≫ t₁') :
    x₁ ≫ x₂ ≫ bF ≫ g₁ ≫ g₂ = b ≫ bC ≫ t₁ ≫ t₂ ≫ gw := by
  have e1 : bF' ≫ g₂ = y₁' ≫ bFB ≫ ah := by
    rw [V1]
    simp only [Category.assoc, hai, Category.comp_id, reassoc_of% hy]
  have e2 : bFB = z₁' ≫ bCD ≫ ce' := by
    rw [Cg]
    simp only [Category.assoc, hce, Category.comp_id, reassoc_of% hz]
  rw [← NT, hw, ← reassoc_of% N1, e1, e2, V2]
  simp only [Category.assoc]
  rw [reassoc_of% hb, reassoc_of% ha, ← reassoc_of% NC]

private lemma outer_chase {C D D' D₁ D₂ : Type*} [Category C] [Category D] [Category D']
    [Category D₁] [Category D₂] (G : C ⥤ C) (ι : G ⟶ 𝟭 C) (L : D ⥤ C) (Fq : D' ⥤ D)
    (L₂ : D' ⥤ C) (βA : Fq ⋙ L ⟶ L₂ ⋙ G) (Lu₁ : D₁ ⥤ C) (Lv₁ : D₁ ⥤ D) (P₁ : Lu₁ ≅ Lv₁ ⋙ L)
    (Lu₂ : D₂ ⥤ C) (Lv₂ : D₂ ⥤ D') (P₂ : Lu₂ ≅ Lv₂ ⋙ L₂)
    {A0 A1 A2 B : D₁} {M N' : D₂} {V W : D'} {E7 E8 : D}
    {x₁ : A0 ⟶ A1} {x₂ : A1 ⟶ A2} {y : M ⟶ N'} {z : Lv₂.obj N' ⟶ W}
    {βE : Lu₁.obj A2 ⟶ G.obj (Lu₂.obj M)} {sF : Lv₁.obj A2 ⟶ Fq.obj (Lv₂.obj M)}
    {b : A0 ⟶ B} {l₂ : Lv₁.obj B ⟶ E7} {l₃ : E7 ⟶ E8} {l₄ : E8 ⟶ Fq.obj V} {w : V ⟶ W}
    (HP : βE = P₁.hom.app A2 ≫ L.map sF ≫ βA.app (Lv₂.obj M) ≫ G.map (P₂.inv.app M))
    (Hcore : Lv₁.map x₁ ≫ Lv₁.map x₂ ≫ sF ≫ Fq.map (Lv₂.map y) ≫ Fq.map z =
      Lv₁.map b ≫ l₂ ≫ l₃ ≫ l₄ ≫ Fq.map w) :
    (Lu₁.map x₁ ≫ Lu₁.map x₂ ≫ βE ≫ ι.app (Lu₂.obj M)) ≫ Lu₂.map y ≫ P₂.hom.app N' ≫ L₂.map z =
      Lu₁.map b ≫ P₁.hom.app B ≫ L.map l₂ ≫
        (L.map l₃ ≫ L.map l₄ ≫ βA.app V ≫ ι.app (L₂.obj V)) ≫ L₂.map w := by
  have n1 := ι.naturality (Lu₂.map y ≫ P₂.hom.app N' ≫ L₂.map z)
  have n2 := ι.naturality (L₂.map w)
  have n3 := P₂.hom.naturality y
  have n4 := βA.naturality (Lv₂.map y ≫ z)
  have n5 := βA.naturality w
  have n6 := P₁.hom.naturality (x₁ ≫ x₂)
  have n7 := P₁.hom.naturality b
  have H := congrArg L.map Hcore
  simp only [Functor.id_map, Functor.comp_map, Functor.map_comp,
    Category.assoc] at n1 n2 n3 n4 n5 n6 n7 H
  simp only [Category.assoc, HP]
  have n3' : (P₂.inv.app M ≫ Lu₂.map y) ≫ P₂.hom.app N' = L₂.map (Lv₂.map y) := by
    rw [Category.assoc, n3, Iso.inv_hom_id_app_assoc]
  rw [← n1, ← n2, ← reassoc_of% n5, ← G.map_comp_assoc, ← G.map_comp_assoc,
    n3', ← reassoc_of% n4, reassoc_of% n6, reassoc_of% n7, ← reassoc_of% H]

section NaturalityCore

variable {Q₁ R₁ Q₂ R₂ Y B₁ B₂ Z : Scheme.{u}} [CompactSpace Q₁] [QuasiSeparatedSpace Q₁]
  [CompactSpace R₁] [QuasiSeparatedSpace R₁] [CompactSpace Q₂] [QuasiSeparatedSpace Q₂]
  [CompactSpace R₂] [QuasiSeparatedSpace R₂] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace B₁] [QuasiSeparatedSpace B₁] [CompactSpace B₂] [QuasiSeparatedSpace B₂]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  (v₁ : Q₁ ⟶ R₁) (rQ₁ : Q₁ ⟶ Y) (r₁ : R₁ ⟶ B₁) (j₁ : Y ⟶ B₁) (q₁ : B₁ ⟶ Z)
  (v₂ : Q₂ ⟶ R₂) (rQ₂ : Q₂ ⟶ Y) (r₂ : R₂ ⟶ B₂) (j₂ : Y ⟶ B₂) (q₂ : B₂ ⟶ Z)
  (ψ : B₁ ⟶ B₂) (φ : R₁ ⟶ R₂) (φQ : Q₁ ⟶ Q₂)
  [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion v₂]
  (sq₁ : IsPullback v₁ rQ₁ r₁ j₁) (sq₂ : IsPullback v₂ rQ₂ r₂ j₂)
  (sqψ : IsPullback j₁ (𝟙 Y) ψ j₂) (sqF : IsPullback v₁ φQ φ v₂)
  (hψ : ψ ≫ q₂ = q₁) (hφ : φ ≫ r₂ = r₁ ≫ ψ) (hφQr : φQ ≫ rQ₂ = rQ₁)
  (e₀ : r₁ ≫ q₁ = φ ≫ r₂ ≫ q₂)

include sq₁ sq₂ sqψ sqF hψ hφ hφQr in
/-- **The cube identity behind the naturality of the composition comparison** (the proof of
[Stacks, Tag 0ATX]): on the open `Q₁ ⊆ R₁`, the base change maps of the squares `Q₁ ⊆ R₁` over
`Q₂ ⊆ R₂` and `Q₂ ⊆ R₂` over `Y ⊆ Ȳ₂` compose to those of `Q₁ ⊆ R₁` over `Y ⊆ Ȳ₁` and
`Y ⊆ Ȳ₁` over `Y ⊆ Ȳ₂`, up to the composition isomorphisms of twisted inverse images. -/
theorem compHom_naturality_core (K : quasiCoherentDerivedCategory Z) :
    (quasiCoherentDerivedPullback' v₁).map
        ((twistedInverseImageCongr e₀ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
      (quasiCoherentDerivedPullback' v₁).map
        ((twistedInverseImageCompIso φ (r₂ ≫ q₂)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
      (openBaseChange v₁ φQ φ v₂ sqF).app
        ((twistedInverseImage (r₂ ≫ q₂)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≫
      (twistedInverseImage φQ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
        ((quasiCoherentDerivedPullback' v₂).map
          ((twistedInverseImageCompIso r₂ q₂
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K)) ≫
      (twistedInverseImage φQ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
        ((openBaseChange v₂ rQ₂ r₂ j₂ sq₂).app
          ((twistedInverseImage q₂
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) =
    (quasiCoherentDerivedPullback' v₁).map
        ((twistedInverseImageCompIso r₁ q₁
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
      (openBaseChange v₁ rQ₁ r₁ j₁ sq₁).app
        ((twistedInverseImage q₁ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≫
      (twistedInverseImageCongr hφQr.symm (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app
        ((quasiCoherentDerivedPullback' j₁).obj
          ((twistedInverseImage q₁
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≫
      (twistedInverseImageCompIso φQ rQ₂
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app
        ((quasiCoherentDerivedPullback' j₁).obj
          ((twistedInverseImage q₁
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≫
      (twistedInverseImage φQ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
        ((twistedInverseImage rQ₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
          ((quasiCoherentDerivedPullback' j₁).map
            ((twistedInverseImageCongr hψ.symm
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
          (quasiCoherentDerivedPullback' j₁).map
            ((twistedInverseImageCompIso ψ q₂
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
          (openBaseChange j₁ (𝟙 Y) ψ j₂ sqψ).app
            ((twistedInverseImage q₂
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≫
          (twistedInverseImageIdIsoOfComp Y).hom.app
            ((quasiCoherentDerivedPullback' j₂).obj
              ((twistedInverseImage q₂
                (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)))) := by
  have hFB := sqF.paste_vert sq₂
  have hCD := sq₁.paste_vert sqψ
  have N1 := (openBaseChange v₁ φQ φ v₂ sqF).naturality
    ((twistedInverseImageCompIso r₂ q₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K)
  simp only [Functor.comp_map] at N1
  have V1 := openBaseChange_app_vpaste v₁ v₂ j₂ φ r₂ φQ rQ₂ sqF sq₂ hFB
    ((twistedInverseImage q₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)
  have V2 := openBaseChange_app_vpaste v₁ j₁ j₂ r₁ ψ rQ₁ (𝟙 Y) sq₁ sqψ hCD
    ((twistedInverseImage q₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)
  have Cg := openBaseChange_app_congr₂ v₁ j₂ hφ (hφQr.trans (Category.comp_id rQ₁).symm) hFB hCD
    ((twistedInverseImage q₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)
  have NT := (twistedInverseImageCongr hφQr.symm
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ≪≫
    twistedInverseImageCompIso φQ rQ₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.naturality
    ((quasiCoherentDerivedPullback' j₁).map
        ((twistedInverseImageCongr hψ.symm (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
      (quasiCoherentDerivedPullback' j₁).map
        ((twistedInverseImageCompIso ψ q₂
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
      (openBaseChange j₁ (𝟙 Y) ψ j₂ sqψ).app
        ((twistedInverseImage q₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≫
      (twistedInverseImageIdIsoOfComp Y).hom.app
        ((quasiCoherentDerivedPullback' j₂).obj
          ((twistedInverseImage q₂ (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.comp_map, Category.assoc] at NT
  have NC := (openBaseChange v₁ rQ₁ r₁ j₁ sq₁).naturality
    ((twistedInverseImageCongr hψ.symm (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
      (twistedInverseImageCompIso ψ q₂
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at NC
  have ha := congrArg (quasiCoherentDerivedPullback' v₁).map
    (twistedInverseImageCompIso_square_congr r₁ q₁ r₂ q₂ ψ φ hψ hφ e₀ K)
  simp only [Functor.map_comp] at ha
  exact core_chase N1 V1
    (by rw [← Functor.map_comp, Iso.inv_hom_id_app]; exact CategoryTheory.Functor.map_id _ _)
    (Iso.inv_hom_id_app _ _) Cg
    (by rw [← Functor.map_comp, Iso.hom_inv_id_app]; exact CategoryTheory.Functor.map_id _ _)
    (Iso.hom_inv_id_app _ _) V2 NT (by simp only [Functor.map_comp]) NC ha
    (twistedInverseImageCompIso_comp_id_congr rQ₁ _ hφQr _)

end NaturalityCore


/-! ### Nested compactifications and the composition comparison -/

/-- **A compactification of `X` over a compactification of `Y`**: for `f : X ⟶ Y`, `g : Y ⟶ Z`
and a compactification `Y ⊆ Ȳ` of `g`, a scheme `R` proper over `Ȳ` containing `X` as an open
with `X ⟶ R ⟶ Ȳ = X ⟶ Y ⟶ Ȳ`, together with an open `Q ⊆ R` which is the inverse image of `Y`
and contains `X`. This is the configuration in which the proof of [Stacks, Tag 0ATX] computes
the comparison `(g ∘ f)^! ⟶ f^! ∘ g^!`. -/
structure NestedCompactification {S : Scheme.{u}} {X Y Z : FTS S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cg : CompactificationOf (Over.mk g.left)) where
  /-- The ambient scheme, proper over `Ȳ`. -/
  R : Scheme.{u}
  /-- The proper morphism `R ⟶ Ȳ`. -/
  r : R ⟶ cg.space
  [isProper_r : IsProper r]
  /-- The open immersion `X ⟶ R`. -/
  u : X.left ⟶ R
  [isOpenImmersion_u : IsOpenImmersion u]
  u_r : u ≫ r = f.left ≫ cg.immersion
  /-- The inverse image of `Y`. -/
  Q : Scheme.{u}
  /-- The open immersion `Q ⟶ R`. -/
  v : Q ⟶ R
  [isOpenImmersion_v : IsOpenImmersion v]
  /-- The morphism `Q ⟶ Y`. -/
  rQ : Q ⟶ Y.left
  isPullback : IsPullback v rQ r cg.immersion
  /-- The open immersion `X ⟶ Q`. -/
  uQ : X.left ⟶ Q
  uQ_v : uQ ≫ v = u
  uQ_rQ : uQ ≫ rQ = f.left

namespace NestedCompactification

attribute [instance] isProper_r isOpenImmersion_u isOpenImmersion_v

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y Z : FTS S} {f : X ⟶ Y}
  {g : Y ⟶ Z} {cg : CompactificationOf (Over.mk g.left)} (N : NestedCompactification f g cg)

/-- The scheme `R` is quasi-compact. -/
instance : CompactSpace N.R := QuasiCompact.compactSpace_of_compactSpace N.r

/-- The scheme `R` is quasi-separated. -/
instance : QuasiSeparatedSpace N.R := quasiSeparatedSpace_of_quasiSeparated N.r

/-- The morphism `rQ : Q ⟶ Y`, a base change of `r`, is proper. -/
instance : IsProper N.rQ := MorphismProperty.of_isPullback N.isPullback inferInstance

/-- The scheme `Q` is quasi-compact. -/
instance : CompactSpace N.Q := QuasiCompact.compactSpace_of_compactSpace N.rQ

/-- The scheme `Q` is quasi-separated. -/
instance : QuasiSeparatedSpace N.Q := quasiSeparatedSpace_of_quasiSeparated N.rQ

/-- The morphism `uQ : X ⟶ Q` is an open immersion. -/
instance : IsOpenImmersion N.uQ := by
  have : IsOpenImmersion (N.uQ ≫ N.v) := by rw [N.uQ_v]; infer_instance
  exact IsOpenImmersion.of_comp N.uQ N.v

/-- `R` as a compactification of `X` over `Z`. -/
def compFG : CompactificationOf (Over.mk (f ≫ g).left) :=
  ⟨StructuredArrow.mk (Y := Over.mk (N.r ≫ cg.toBase))
      (Over.homMk N.u (by
        simp only [Over.mk_left, Over.mk_hom, Functor.id_obj]
        rw [← Category.assoc, N.u_r, Category.assoc, immersion_comp_toBase g cg]
        rfl)),
    ⟨(inferInstance : IsOpenImmersion N.u), (inferInstance : IsProper (N.r ≫ cg.toBase))⟩⟩

/-- `Q` as a compactification of `X` over `Y`. -/
def compF : CompactificationOf (Over.mk f.left) :=
  ⟨StructuredArrow.mk (Y := Over.mk N.rQ) (Over.homMk N.uQ N.uQ_rQ),
    ⟨(inferInstance : IsOpenImmersion N.uQ), (inferInstance : IsProper N.rQ)⟩⟩

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The space of `N.compFG` is `R`. -/
@[simp] theorem compFG_space : N.compFG.space = N.R := rfl
omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The immersion of `N.compFG` is `u`. -/
@[simp] theorem compFG_immersion : N.compFG.immersion = N.u := rfl
omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The structure morphism of `N.compFG` is `r ≫ cg.toBase`. -/
@[simp] theorem compFG_toBase : N.compFG.toBase = N.r ≫ cg.toBase := rfl
omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The space of `N.compF` is `Q`. -/
@[simp] theorem compF_space : N.compF.space = N.Q := rfl
omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The immersion of `N.compF` is `uQ`. -/
@[simp] theorem compF_immersion : N.compF.immersion = N.uQ := rfl
omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The structure morphism of `N.compF` is `rQ`. -/
@[simp] theorem compF_toBase : N.compF.toBase = N.rQ := rfl

/-- `Lu^* ≅ Lv^* ⋙ LuQ^*`. -/
abbrev pullbackIso : quasiCoherentDerivedPullback' N.u ≅
    quasiCoherentDerivedPullback' N.v ⋙ quasiCoherentDerivedPullback' N.uQ :=
  quasiCoherentDerivedPullbackCongr N.uQ_v.symm ≪≫
    (quasiCoherentDerivedPullbackCompIso N.uQ N.v).symm

/-- **The comparison `(g ∘ f)^! ⟶ f^! ∘ g^!` attached to a nested compactification**: `L u^*` of
`a_{R/Z} ≅ a_{R/Ȳ} ∘ a_{Ȳ/Z}`, the identification `Lu^* ≅ Lv^* ⋙ LuQ^*`, and `LuQ^*` of the base
change map of [Stacks, Tag 0A9L] for the square `Q ⊆ R` over `Y ⊆ Ȳ`. -/
def compHom :
    twistedInverseImage (N.r ≫ cg.toBase) (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⋙
        quasiCoherentDerivedPullback' N.u ⟶
      (twistedInverseImage cg.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⋙
        quasiCoherentDerivedPullback' cg.immersion) ⋙
      (twistedInverseImage N.rQ (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⋙
        quasiCoherentDerivedPullback' N.uQ) :=
  Functor.whiskerRight (twistedInverseImageCompIso N.r cg.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom
      (quasiCoherentDerivedPullback' N.u) ≫
    Functor.whiskerLeft _ N.pullbackIso.hom ≫ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.associator _ _ _).inv ≫
    Functor.whiskerLeft _ (Functor.whiskerRight (openBaseChange N.v N.rQ N.r cg.immersion
      N.isPullback) (quasiCoherentDerivedPullback' N.uQ)) ≫
    Functor.whiskerLeft _ (Functor.associator _ _ _).hom ≫ (Functor.associator _ _ _).inv

/-- The component of `N.compHom` at `K`, as the composite of its three constituent maps. -/
theorem compHom_app (K : quasiCoherentDerivedCategory Z.left) :
    N.compHom.app K = (quasiCoherentDerivedPullback' N.u).map
      ((twistedInverseImageCompIso N.r cg.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
    N.pullbackIso.hom.app ((twistedInverseImage N.r
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj ((twistedInverseImage cg.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≫
    (quasiCoherentDerivedPullback' N.uQ).map ((openBaseChange N.v N.rQ N.r cg.immersion
      N.isPullback).app ((twistedInverseImage cg.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) := by
  simp [compHom]

section Naturality

variable {cg₁ cg₂ : CompactificationOf (Over.mk g.left)} (N₁ : NestedCompactification f g cg₁)
  (N₂ : NestedCompactification f g cg₂) (ψ : cg₁.space ⟶ cg₂.space)
  (hψ : ψ ≫ cg₂.toBase = cg₁.toBase) (sqψ : IsPullback cg₁.immersion (𝟙 Y.left) ψ cg₂.immersion)
  (φ : N₁.R ⟶ N₂.R) (hφ : φ ≫ N₂.r = N₁.r ≫ ψ) (sqφ : IsPullback N₁.u (𝟙 X.left) φ N₂.u)
  (φQ : N₁.Q ⟶ N₂.Q) (hφQv : φQ ≫ N₂.v = N₁.v ≫ φ) (hφQr : φQ ≫ N₂.rQ = N₁.rQ)
  (sqφQ : IsPullback N₁.uQ (𝟙 X.left) φQ N₂.uQ)

include hψ hφ in
omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- A morphism `φ : R₁ ⟶ R₂` over `ψ` commutes with the structure morphisms of `compFG` to `Z`. -/
theorem hφfg : φ ≫ N₂.compFG.toBase = N₁.compFG.toBase := by
  simp only [compFG_toBase]
  rw [reassoc_of% hφ, hψ]

include hφQv in
/-- The comparison `compHom` is compatible with the maps induced by morphisms of nested
compactifications: `compHom` of `N₂` after the map for `compFG` equals `compHom` of `N₁` followed
by the maps for `compF` and for `cg₁ ⟶ cg₂`. -/
theorem compHom_naturality (K : quasiCoherentDerivedCategory Z.left) :
    (upperShriekCompactificationMap (f ≫ g) N₁.compFG N₂.compFG φ (hφfg N₁ N₂ ψ hψ φ hφ)
        sqφ).app K ≫ N₂.compHom.app K =
      N₁.compHom.app K ≫
        (upperShriekCompactificationMap f N₁.compF N₂.compF φQ hφQr sqφQ).app
          ((upperShriek g cg₁).obj K) ≫
        (upperShriek f N₂.compF).map
          ((upperShriekCompactificationMap g cg₁ cg₂ ψ hψ sqψ).app K) := by
  have e₁ := upperShriekCompactificationMap_app_eq_openBaseChange (f ≫ g) N₁.compFG N₂.compFG φ
    (hφfg N₁ N₂ ψ hψ φ hφ) sqφ K
  have e₂ := upperShriekCompactificationMap_app_eq_openBaseChange f N₁.compF N₂.compF φQ hφQr
    sqφQ ((upperShriek g cg₁).obj K)
  have e₃ := upperShriekCompactificationMap_app_eq_openBaseChange g cg₁ cg₂ ψ hψ sqψ K
  refine (congrArg (· ≫ N₂.compHom.app K) e₁).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => N₁.compHom.app K ≫ t ≫ _) e₂).symm
  refine Eq.trans ?_ (congrArg (fun t => N₁.compHom.app K ≫ _ ≫
    (upperShriek f N₂.compF).map t) e₃).symm
  have sqF : IsPullback N₁.v φQ φ N₂.v := by
    refine IsPullback.of_bot ?_ hφQv.symm N₂.isPullback
    rw [hφQr, hφ]
    simpa using N₁.isPullback.paste_vert sqψ
  rw [compHom_app, compHom_app]
  simp only [compFG_immersion, compF_immersion, Functor.map_comp, Category.assoc]
  exact outer_chase _ (twistedInverseImageIdIsoOfComp X.left).hom
    (quasiCoherentDerivedPullback' N₁.uQ)
    _ (quasiCoherentDerivedPullback' N₂.uQ) (openBaseChange N₁.uQ (𝟙 X.left) φQ N₂.uQ sqφQ)
    (quasiCoherentDerivedPullback' N₁.u) (quasiCoherentDerivedPullback' N₁.v) N₁.pullbackIso
    (quasiCoherentDerivedPullback' N₂.u) (quasiCoherentDerivedPullback' N₂.v) N₂.pullbackIso
    (openBaseChange_app_hpaste N₁.v φQ φ N₂.v N₁.uQ (𝟙 X.left) N₂.uQ N₁.u N₂.u sqF sqφQ sqφ
      N₁.uQ_v N₂.uQ_v _)
    (compHom_naturality_core N₁.v N₁.rQ N₁.r cg₁.immersion cg₁.toBase N₂.v N₂.rQ N₂.r
      cg₂.immersion cg₂.toBase ψ φ φQ N₁.isPullback N₂.isPullback sqψ sqF hψ hφ hφQr
      (hφfg N₁ N₂ ψ hψ φ hφ).symm K)

end Naturality

end NestedCompactification

end Stacks.Duality

end
