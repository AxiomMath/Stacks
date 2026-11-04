module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteType.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteType.SchemeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.LocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae

/-!
# Flattening by blowing up over a base represented by a scheme

Let `A` be an algebraic space isomorphic to the space of a quasi-compact and quasi-separated
scheme `Q`, let `f : X ⟶ A` be of finite type and quasi-separated and let `U ⊆ A` be a
quasi-compact open subspace over which `f` is flat and locally of finite presentation.  Then
there is a `U`-admissible blowup of `A` along which the strict transform of `X` is flat and
locally of finite presentation.

## Main results

* `AlgebraicGeometry.Space.exists_opens_eq_openSubspaceOfPoints`: open subspaces of the space of a
  scheme come from opens of the scheme.
* `AlgebraicGeometry.Space.prop_morphismRestrict_of_holdsOnEveryEtaleChart`: a property of the
  base change of a morphism to the space of a scheme over an open, read on an étale chart.
* `AlgebraicGeometry.Space.flattensByBlowup_of_iso`: flattening is invariant under an
  isomorphism of the base.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_pullback_snd_comp_iso`: the base change over
  an open subspace crosses an isomorphism of the base.
* `AlgebraicGeometry.Space.flattensByBlowup_of_iso_schemeSpace`: flattening by blowing up over a
  base isomorphic to the space of a quasi-compact and quasi-separated scheme.

## References

* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Every open subspace of the algebraic space of a scheme is cut out by an open of the
scheme**: it is the open subspace of the points over that open. -/
theorem exists_opens_eq_openSubspaceOfPoints (Q : BigFppfOver B S hS)
    (U : Subfunctor (yoneda.obj Q)) (hU : IsOpenSubspace B S hS U) :
    ∃ O : ((BigFppfOver.toScheme B S hS).obj Q).Opens,
      U = openSubspaceOfPoints B S hS (yoneda.obj Q) (pointsToScheme B S hS Q ⁻¹' O) := by
  have hW := isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2
  obtain ⟨V, hV, hmem⟩ := (isOpen_yoneda_iff_isSchemeOpen B S hS Q _).1 hW
  refine ⟨⟨V, hV⟩, ?_⟩
  have hWeq : Set.range (pointsMap B S hS U.toFunctor U.ι) =
      pointsToScheme B S hS Q ⁻¹' V := by
    ext w
    induction w using Quot.ind with
    | mk p => exact hmem p
  have hO := isOpenSubspace_openSubspaceOfPoints_preimage_pointsToScheme Q ⟨V, hV⟩
  refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS hO ?_)
    (le_of_range_pointsMap_ι_subset B S hS hU ?_) <;>
    rw [range_pointsMap_ι_openSubspaceOfPoints, hWeq] <;> rfl


/-- The yoneda image of the inclusion of an open of a scheme is a monomorphism. -/
private theorem mono_yoneda_map_openSubHom (Q : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj Q).Opens) : Mono (yoneda.map (openSubHom Q O)) := by
  have : Mono (openSubHom Q O) := (BigFppfOver.toScheme B S hS).mono_of_mono_map (by
    rw [toScheme_map_openSubHom B S hS]
    exact inferInstanceAs (Mono O.ι))
  exact Functor.map_mono yoneda _

/-- **A property of the base change over an open of a morphism to the space of a scheme, read on
an étale chart.**  Let `f : X ⟶ h_Q` be a morphism of algebraic spaces whose base change over the
open subspace cut out by an open `O ⊆ Q` has a property `P` (étale local on source and target,
stable under composition, satisfied by étale morphisms), and let `u : h_V ⟶ X` be an étale chart
with `u ≫ f = h_g`.  Then the restriction `g|_O : g⁻¹(O) ⟶ O` has `P`. -/
theorem prop_morphismRestrict_of_holdsOnEveryEtaleChart {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hcomp : ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (c : G ⟶ H),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G → IsAlgebraicSpace B S hS H →
        HoldsOnEveryEtaleChart B S hS P a → HoldsOnEveryEtaleChart B S hS P c →
          HoldsOnEveryEtaleChart B S hS P (a ≫ c))
    (hetale : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G), IsEtale B S hS a →
      HoldsOnEveryEtaleChart B S hS P a)
    {Q : BigFppfOver B S hS} (O : ((BigFppfOver.toScheme B S hS).obj Q).Opens)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ yoneda.obj Q)
    (hf : HoldsOnEveryEtaleChart B S hS P (pullback.snd f (openSubspaceOfPoints B S hS
      (yoneda.obj Q) (pointsToScheme B S hS Q ⁻¹' (O : Set _))).ι))
    {V : BigFppfOver B S hS} (u : yoneda.obj V ⟶ X) (hu : IsEtale B S hS u) (g : V ⟶ Q)
    (hg : u ≫ f = yoneda.map g) :
    P ((BigFppfOver.toScheme B S hS).map g ∣_ O) := by
  set U := openSubspaceOfPoints B S hS (yoneda.obj Q) (pointsToScheme B S hS Q ⁻¹' (O : Set _))
  have hQ := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Q
  have hUo : IsOpenSubspace B S hS U :=
    isOpenSubspace_openSubspaceOfPoints_preimage_pointsToScheme Q O
  have hUr : U = Subfunctor.range (yoneda.map (openSubHom Q O)) :=
    openSubspaceOfPoints_preimage_pointsToScheme Q O
  let t : yoneda.obj (openSub Q O) ⟶ U.toFunctor :=
    Subfunctor.lift (yoneda.map (openSubHom Q O)) hUr.ge
  have ht : t ≫ U.ι = yoneda.map (openSubHom Q O) := Subfunctor.lift_ι _ _
  have := mono_yoneda_map_openSubHom (B := B) (hS := hS) Q O
  have : Mono t := mono_of_mono_fac ht
  have : Epi t := by
    rw [NatTrans.epi_iff_epi_app]
    intro T
    rw [epi_iff_surjective]
    rintro ⟨x, hx⟩
    rw [hUr] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩
  have : IsIso t := isIso_of_mono_of_epi t
  set h := openSubHomOfRestrict g O
  let a := yoneda.map (openSubHom V ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O)) ≫ u
  have ha : a ≫ f = (yoneda.map h ≫ t) ≫ U.ι := by
    rw [Category.assoc, Category.assoc, ht, hg, ← Functor.map_comp, ← Functor.map_comp,
      openSubHomOfRestrict_comp_openSubHom]
  let â := pullback.lift a (yoneda.map h ≫ t) ha
  have hâ : IsEtale B S hS â := by
    have : Mono (pullback.fst f U.ι) := pullback.fst_of_mono
    refine isEtale_of_comp_mono B S hS â (pullback.fst f U.ι) ?_
    rw [pullback.lift_fst]
    exact isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((presheaf_yoneda_map_etale_iff B S hS _).2 (etale_toScheme_map_openSubHom B S hS V _))) hu
  have hpb := isAlgebraicSpace_pullback B S hS f U.ι hX hUo.1 hQ
  have hV' := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS
    (openSub V ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O))
  have hO' := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (openSub Q O)
  have h1 : HoldsOnEveryEtaleChart B S hS P (yoneda.map h ≫ t) := by
    rw [← pullback.lift_snd a (yoneda.map h ≫ t) ha]
    exact hcomp _ _ hV' hpb hUo.1 (hetale _ hâ) hf
  have h2 : HoldsOnEveryEtaleChart B S hS P (yoneda.map h) := by
    rw [show yoneda.map h = (yoneda.map h ≫ t) ≫ inv t by simp]
    exact hcomp _ _ hV' hUo.1 hO' h1 (hetale _ (isEtale_of_isIso B S hS _))
  exact (holdsOnEveryEtaleChart_yoneda_map_iff B S hS hP h).1 h2

/-- **Being flattened by a blowup is invariant under an isomorphism of the base.** -/
theorem flattensByBlowup_of_iso {A A₂ X : AlgebraicSpaces B S hS} (e : A ≅ A₂) (f : X ⟶ A)
    (U : OpenSubspaces B S hS A.1) (U₂ : OpenSubspaces B S hS A₂.1)
    (hU : U.1 = U₂.1.preimage e.hom.hom) (h : FlattensByBlowup (f ≫ e.hom) U₂) :
    FlattensByBlowup f U := by
  obtain ⟨A', b₂, Z₂, hfp, hdisj, hb₂, hfl, hlfp⟩ := h
  have hsq : IsPullback (b₂ ≫ e.inv) (𝟙 A') e.hom b₂ :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hb := isBlowupAlong_preimage_of_isPullback_of_isFlat
    (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS e.hom.hom)) hb₂ hsq
  refine ⟨A', b₂ ≫ e.inv, preimageClosedSubspace e.hom Z₂,
    isFinitePresentation_ι_preimage e.hom Z₂ hfp, ?_, hb, ?_⟩
  · have h1 := range_pointsMap_preimage_ι B S hS e.hom.hom U₂.1
    have h2 := range_pointsMap_preimage_ι B S hS e.hom.hom Z₂.1
    show Disjoint (Set.range (pointsMap B S hS U.1.toFunctor U.1.ι))
      (Set.range (pointsMap B S hS (Z₂.1.preimage e.hom.hom).toFunctor
        (Z₂.1.preimage e.hom.hom).ι))
    rw [hU, h1, h2]
    exact hdisj.preimage _
  · have hE : (preimageClosedSubspace e.hom Z₂).1.preimage (b₂ ≫ e.inv).hom =
        Z₂.1.preimage b₂.hom := by
      show (Z₂.1.preimage e.hom.hom).preimage (b₂.hom ≫ e.inv.hom) = _
      rw [← Subfunctor.preimage_comp, Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
        e.inv_hom_id]
      simp
    have : Mono e.inv.hom := inferInstance
    exact isFlat_and_isLocallyOfFinitePresentation_strictTransform_of_etaleCover f
      (b₂ ≫ e.inv) (f ≫ e.hom) b₂ e.inv (𝟙 X : X ⟶ X) (isEtale_of_isIso B S hS (𝟙 X.1))
      (isSurjective_id B S hS X.1) (by simp) rfl (preimageClosedSubspace (b₂ ≫ e.inv)
        (preimageClosedSubspace e.hom Z₂)) hb.isPullbackDefined
      (by change IsFlat B S hS (strictTransformSpaceToBlowUp B S hS (f ≫ e.hom) b₂
            ((preimageClosedSubspace e.hom Z₂).1.preimage (b₂ ≫ e.inv).hom)).hom
          rw [hE]; exact hfl)
      (by change IsLocallyOfFinitePresentation B S hS (strictTransformSpaceToBlowUp B S hS
            (f ≫ e.hom) b₂ ((preimageClosedSubspace e.hom Z₂).1.preimage (b₂ ≫ e.inv).hom)).hom
          rw [hE]; exact hlfp)

/-- **The restriction over an open subspace crosses an isomorphism of the base.**  If the base
change of `f : X ⟶ A` over `U ⊆ A` has a property `P` stable under composition and satisfied by
étale morphisms, so does the base change of `f ≫ e.hom` over the corresponding open `e(U)`. -/
theorem holdsOnEveryEtaleChart_pullback_snd_comp_iso {P : MorphismProperty Scheme.{u}}
    (hcomp : ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (c : G ⟶ H),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G → IsAlgebraicSpace B S hS H →
        HoldsOnEveryEtaleChart B S hS P a → HoldsOnEveryEtaleChart B S hS P c →
          HoldsOnEveryEtaleChart B S hS P (a ≫ c))
    (hetale : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G), IsEtale B S hS a →
      HoldsOnEveryEtaleChart B S hS P a)
    {X A A₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hA : IsAlgebraicSpace B S hS A) (hA₂ : IsAlgebraicSpace B S hS A₂) (f : X ⟶ A)
    (e : A ≅ A₂) (U : Subfunctor A) (hU : IsOpenSubspace B S hS U)
    (h : HoldsOnEveryEtaleChart B S hS P (pullback.snd f U.ι)) :
    HoldsOnEveryEtaleChart B S hS P (pullback.snd (f ≫ e.hom) (U.preimage e.inv).ι) := by
  have hV : IsOpenSubspace B S hS (U.preimage e.inv) :=
    isOpenSubspace_preimage B S hS e.inv U hA hA₂ hU
  have hsq := Subfunctor.isPullback_preimage e.inv U
  have : IsIso (U.fromPreimage e.inv) := hsq.isIso_fst_of_isIso
  have hψ : U.ι ≫ e.hom = inv (U.fromPreimage e.inv) ≫ (U.preimage e.inv).ι := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hsq.w, Category.assoc, e.inv_hom_id,
      Category.comp_id]
  have h2 : IsPullback U.ι (inv (U.fromPreimage e.inv)) e.hom (U.preimage e.inv).ι :=
    IsPullback.of_vert_isIso ⟨hψ⟩
  have hP1 := (IsPullback.of_hasPullback f U.ι).paste_vert h2
  have hpb := isAlgebraicSpace_pullback B S hS f U.ι hX hU.1 hA
  have hpb₂ := isAlgebraicSpace_pullback B S hS (f ≫ e.hom) (U.preimage e.inv).ι hX hV.1 hA₂
  rw [← hP1.isoPullback_inv_snd]
  exact hcomp _ _ hpb₂ hpb hV.1 (hetale _ (isEtale_of_isIso B S hS _))
    (hcomp _ _ hpb hU.1 hV.1 h (hetale _ (isEtale_of_isIso B S hS _)))

/-- **Flattening by blowing up over a base represented by a quasi-compact and quasi-separated
scheme.**  Let `A` be an algebraic space isomorphic to the space of a quasi-compact and
quasi-separated scheme `Q`, let `f : X ⟶ A` be of finite type and quasi-separated, and let
`U ⊆ A` be a quasi-compact open subspace over which `f` is flat and locally of finite
presentation.  Then `f` is flattened over `U` by a `U`-admissible blowup. -/
theorem flattensByBlowup_of_iso_schemeSpace (Q : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj Q)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Q)] {A X : AlgebraicSpaces B S hS}
    (e : A ≅ schemeSpace Q) (f : X ⟶ A) (U : OpenSubspaces B S hS A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor) (hft : IsFiniteType B S hS f.hom)
    (_hqs : IsQuasiSeparated B S hS f.hom) (hfl : IsFlat B S hS (pullback.snd f.hom U.1.ι))
    (hlfp : IsLocallyOfFinitePresentation B S hS (pullback.snd f.hom U.1.ι)) :
    FlattensByBlowup f U := by
  have hQ := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Q
  let eF : A.1 ≅ yoneda.obj Q := (ObjectProperty.ι _).mapIso e
  have hAqc : IsQuasiCompactSpace B S hS A.1 :=
    IsQuasiCompactSpace.of_iso B S hS
      (isQuasiCompactSpace_yoneda_of_compactSpace B S hS Q inferInstance)
      eF.symm
  have hXqc := isQuasiCompactSpace_source_of_isQuasiCompact B S hS A.2 hAqc hft.2
  obtain ⟨V₀, a, hV₀, has, hae⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hXqc
  have := hV₀
  obtain ⟨g, hg⟩ : ∃ g : V₀ ⟶ Q, yoneda.map g = a ≫ f.hom ≫ eF.hom :=
    ⟨yoneda.preimage (a ≫ f.hom ≫ eF.hom), by simp⟩
  set U₂ := U.1.preimage eF.inv
  have hU₂ : IsOpenSubspace B S hS U₂ := isOpenSubspace_preimage B S hS eF.inv U.1 A.2 hQ U.2
  obtain ⟨O, hO⟩ := exists_opens_eq_openSubspaceOfPoints Q U₂ hU₂
  have hcompF : ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (c : G ⟶ H),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G → IsAlgebraicSpace B S hS H →
        IsFlat B S hS a → IsFlat B S hS c → IsFlat B S hS (a ≫ c) :=
    fun a c hF hG hH ha hc => isFlat_comp B S hS hF hG hH a c ha hc
  have hcompL : ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (c : G ⟶ H),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G → IsAlgebraicSpace B S hS H →
        IsLocallyOfFinitePresentation B S hS a → IsLocallyOfFinitePresentation B S hS c →
          IsLocallyOfFinitePresentation B S hS (a ≫ c) :=
    fun a c hF hG hH ha hc => isLocallyOfFinitePresentation_comp B S hS hF hG hH a c ha hc
  have hfl₂ : IsFlat B S hS (pullback.snd (f.hom ≫ eF.hom) U₂.ι) :=
    holdsOnEveryEtaleChart_pullback_snd_comp_iso hcompF (fun a ha => isFlat_of_isEtale B S hS ha)
      X.2 A.2 hQ f.hom eF U.1 U.2 hfl
  have hlfp₂ : IsLocallyOfFinitePresentation B S hS (pullback.snd (f.hom ≫ eF.hom) U₂.ι) :=
    holdsOnEveryEtaleChart_pullback_snd_comp_iso hcompL
      (fun a ha => isLocallyOfFinitePresentation_of_isEtale B S hS ha)
      X.2 A.2 hQ f.hom eF U.1 U.2 hlfp
  rw [hO] at hfl₂ hlfp₂
  have hV₀a := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₀
  have hlftg : IsLocallyOfFiniteType B S hS (yoneda.map g) := by
    rw [hg]
    exact isLocallyOfFiniteType_comp' B S hS _ _ X.2 hQ
      (isLocallyOfFiniteType_of_isEtale' B S hS a hae)
      (isLocallyOfFiniteType_comp' B S hS _ _ A.2 hQ hft.1
        (isLocallyOfFiniteType_of_isEtale' B S hS _ (isEtale_of_isIso B S hS eF.hom)))
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) :=
    (isLocallyOfFiniteType_yoneda_map_iff B S hS g).1 hlftg
  have : QuasiSeparated ((BigFppfOver.toScheme B S hS).map g) := inferInstance
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map g) := inferInstance
  have hgu : a ≫ (f.hom ≫ eF.hom) = yoneda.map g := hg.symm
  have hflO : Flat ((BigFppfOver.toScheme B S hS).map g ∣_ O) :=
    prop_morphismRestrict_of_holdsOnEveryEtaleChart Flat.isEtaleLocalOnSourceAndTarget hcompF
      (fun a ha => isFlat_of_isEtale B S hS ha) O X.2 _ hfl₂ a hae g hgu
  have hlfpO : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g ∣_ O) :=
    prop_morphismRestrict_of_holdsOnEveryEtaleChart
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hcompL
      (fun a ha => isLocallyOfFinitePresentation_of_isEtale B S hS ha) O X.2 _ hlfp₂ a hae g hgu
  have hOc : IsCompact (O : Set ((BigFppfOver.toScheme B S hS).obj Q)) := by
    have hsq := Subfunctor.isPullback_preimage eF.inv U.1
    have : IsIso (U.1.fromPreimage eF.inv) := hsq.isIso_fst_of_isIso
    have hU₂qc : IsQuasiCompactSpace B S hS U₂.toFunctor :=
      IsQuasiCompactSpace.of_iso B S hS hUqc (asIso (U.1.fromPreimage eF.inv)).symm
    rw [hO, openSubspaceOfPoints_preimage_pointsToScheme] at hU₂qc
    have := mono_yoneda_map_openSubHom (B := B) (hS := hS) Q O
    have hc := compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (IsQuasiCompactSpace.of_iso B S hS hU₂qc
        (asIso (Subfunctor.toRange (yoneda.map (openSubHom Q O)))).symm)
    have h := isCompact_range ((BigFppfOver.toScheme B S hS).map (openSubHom Q O)).continuous
    have hr : Set.range ((BigFppfOver.toScheme B S hS).map (openSubHom Q O)) = (O : Set _) := by
      rw [← Scheme.Opens.range_ι O]
      exact congrArg (fun k : (BigFppfOver.toScheme B S hS).obj (openSub Q O) ⟶
        (BigFppfOver.toScheme B S hS).obj Q => Set.range k) (toScheme_map_openSubHom B S hS Q O)
    exact hr ▸ h
  obtain ⟨ℐ, hℐfp, hdisj, -, hstfl, hstfp⟩ :=
    exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase
      ((BigFppfOver.toScheme B S hS).map g) O hOc hflO hlfpO
  obtain ⟨A'', b'', hb''⟩ := exists_isBlowupAlong_of_isFinitePresentation
    (closedSubspaceOfIdeal Q ℐ) (isFinitePresentation_closedSubspaceOfIdeal Q ℐ hℐfp)
  obtain ⟨eb, heb⟩ := exists_iso_schemeSpace_blowUpObj_of_isBlowupAlong Q ℐ hℐfp hb''
  have hb₀ : IsBlowupAlong B S hS (closedSubspaceOfIdeal Q ℐ)
      (schemeSpaceMap (blowUpObjHom Q ℐ)) := by
    have h := hb''.of_iso_over eb.symm
    rwa [← heb, Iso.symm_hom, Iso.inv_hom_id_assoc] at h
  have hlfpst : LocallyOfFinitePresentation
      (strictTransformToBlowUp ((BigFppfOver.toScheme B S hS).map g) ℐ) := hstfp.1
  obtain ⟨hC1, hC2⟩ := isFlat_and_isLocallyOfFinitePresentation_strictTransform_schemeSpaceMap g ℐ
    hb₀ hstfl hlfpst
  refine flattensByBlowup_of_iso e f U ⟨U₂, hU₂⟩ ?_ ?_
  · show U.1 = (U.1.preimage eF.inv).preimage eF.hom
    rw [← Subfunctor.preimage_comp, eF.hom_inv_id, Subfunctor.preimage_id]
  refine ⟨_, schemeSpaceMap (blowUpObjHom Q ℐ), closedSubspaceOfIdeal Q ℐ,
    isFinitePresentation_closedSubspaceOfIdeal Q ℐ hℐfp, ?_, hb₀, ?_⟩
  · show Disjoint (Set.range (pointsMap B S hS U₂.toFunctor U₂.ι))
      (subspacePointSet B S hS (yoneda.obj Q) (closedSubspaceOfIdeal Q ℐ).1)
    rw [subspacePointSet_closedSubspaceOfIdeal, hO, range_pointsMap_ι_openSubspaceOfPoints]
    exact hdisj.preimage _
  · have : Mono (𝟙 (schemeSpace Q) : schemeSpace Q ⟶ schemeSpace Q).hom := by
      show Mono (𝟙 (yoneda.obj Q))
      infer_instance
    exact isFlat_and_isLocallyOfFinitePresentation_strictTransform_of_etaleCover (f ≫ e.hom)
      (schemeSpaceMap (blowUpObjHom Q ℐ)) (schemeSpaceMap g) (schemeSpaceMap (blowUpObjHom Q ℐ))
      (𝟙 (schemeSpace Q)) (ObjectProperty.homMk a : schemeSpace V₀ ⟶ X) hae
      ((presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 V₀ a).1 has)
      (by
        show yoneda.map g ≫ 𝟙 _ = a ≫ f.hom ≫ eF.hom
        rw [Category.comp_id, hg])
      rfl (preimageClosedSubspace (schemeSpaceMap (blowUpObjHom Q ℐ)) (closedSubspaceOfIdeal Q ℐ))
      hb₀.isPullbackDefined hC1 hC2

end AlgebraicGeometry.Space

end
