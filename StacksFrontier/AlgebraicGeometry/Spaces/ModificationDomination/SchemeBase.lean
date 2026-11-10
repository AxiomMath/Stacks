module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.LocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.BlowupRepresentableScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.SchemeFlatteningCentreFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound

/-!
# A proper modification of a quasi-compact quasi-separated scheme is dominated by a blowup

Let `W` be an object of the big fppf site over `S` whose underlying scheme is quasi-compact and
quasi-separated, let `U₀ ⊆ W` be a quasi-compact open and `U ⊆ W` the open subspace of the points
over `U₀`. Let `f : X ⟶ W` be a proper morphism of algebraic spaces which is an isomorphism over
`U`. Then there is a `U`-admissible blowup `b : W' ⟶ W` which dominates `X`: `b` factors through
`f`. Moreover `b⁻¹(U)` is scheme-theoretically dense in `W'`.

This is Stacks 087G for a base which is a scheme, along the route of Stacks 087E and 0GUW, and it
generalizes `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_dominating_of_isAffine` (a
Noetherian affine base) to an arbitrary quasi-compact quasi-separated scheme:

* an affine étale chart `V ⟶ X` is a scheme of finite type and quasi-separated over `W`, étale
  over `U₀`, so the flatness half of Stacks 081R in the form
  `AlgebraicGeometry.exists_supportSet_eq_compl_flat_strictTransformToBlowUp_of_finiteType` gives
  a centre `K` cutting out exactly `W ∖ U₀` along which the strict transform of `V` is flat over
  the blowup `Bl_K W`;
* `Bl_K W ⟶ W` is the `U`-admissible blowup of the algebraic space
  (`AlgebraicGeometry.Space.isBlowupAlong_closedSubspaceOfIdeal_schemeSpaceMap`);
* the scheme-theoretic closure of the open part of `X ×_W Bl_K W` is flat over `Bl_K W`, being
  so on the chart
  (`AlgebraicGeometry.Space.isFlat_modificationSection_of_flat_strictTransformToBlowUp`), hence
  is `Bl_K W` (`AlgebraicGeometry.Space.exists_comp_eq_of_isFlat`, Stacks 0B4J and 0879).

## Main results

* `AlgebraicGeometry.Space.etale_morphismRestrict_of_isEtale`: an étale chart of a modification
  is étale over the open part of the base.
* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_dominating_of_qcqs_scheme`.

## References

* [Stacks Project, Tag 087G](https://stacks.math.columbia.edu/tag/087G)
* [Stacks Project, Tag 0GUW](https://stacks.math.columbia.edu/tag/0GUW)
* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The Yoneda image of the inclusion of an open of the underlying scheme is a monomorphism. -/
private theorem mono_yoneda_map_openSubHom (Q : BigFppfOver B S hS)
    (U₀ : ((BigFppfOver.toScheme B S hS).obj Q).Opens) : Mono (yoneda.map (openSubHom Q U₀)) := by
  have : Mono (openSubHom Q U₀) := (BigFppfOver.toScheme B S hS).mono_of_mono_map (by
    rw [toScheme_map_openSubHom B S hS]
    exact inferInstanceAs (Mono U₀.ι))
  exact Functor.map_mono yoneda _

/-- **An étale chart of a modification is étale over the open part of the base.** -/
theorem etale_morphismRestrict_of_isEtale {Q : BigFppfOver B S hS}
    (U₀ : ((BigFppfOver.toScheme B S hS).obj Q).Opens)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj Q)
    [IsIso (pullback.snd f (openSubspaceOfPoints B S hS (yoneda.obj Q)
      (pointsToScheme B S hS Q ⁻¹' (U₀ : Set _))).ι)]
    {V : BigFppfOver B S hS} (u : yoneda.obj V ⟶ X) (hu : IsEtale B S hS u) (g : V ⟶ Q)
    (hg : u ≫ f = yoneda.map g) :
    Etale ((BigFppfOver.toScheme B S hS).map g ∣_ U₀) := by
  set U := openSubspaceOfPoints B S hS (yoneda.obj Q) (pointsToScheme B S hS Q ⁻¹' (U₀ : Set _))
    with hUdef
  have hUr : U = Subfunctor.range (yoneda.map (openSubHom Q U₀)) :=
    openSubspaceOfPoints_preimage_pointsToScheme Q U₀
  let t : yoneda.obj (openSub Q U₀) ⟶ U.toFunctor :=
    Subfunctor.lift (yoneda.map (openSubHom Q U₀)) hUr.ge
  have ht : t ≫ U.ι = yoneda.map (openSubHom Q U₀) := Subfunctor.lift_ι _ _
  have := mono_yoneda_map_openSubHom Q U₀
  have : Mono t := mono_of_mono_fac ht
  set h := openSubHomOfRestrict g U₀
  let a := yoneda.map (openSubHom V ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ U₀)) ≫ u
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
  have hht : IsEtale B S hS (yoneda.map h ≫ t) := by
    rw [← pullback.lift_snd a (yoneda.map h ≫ t) ha]
    exact isEtale_comp B S hS hâ (isEtale_of_isIso B S hS _)
  have hh : IsEtale B S hS (yoneda.map h) := isEtale_of_comp_mono B S hS _ t hht
  exact etale_of_isEtale_yoneda_map B S hS hh

/-- **Stacks 087G over a quasi-compact quasi-separated scheme.** Let `W` be an object of the site
whose underlying scheme is quasi-compact and quasi-separated, let `U₀` be a quasi-compact open of
it and `U ⊆ W` the open subspace of the points over `U₀`. Let `f : X ⟶ W` be a proper morphism of
algebraic spaces which is an isomorphism over `U`. Then there is a `U`-admissible blowup
`b : W' ⟶ W` which dominates `X`, that is, `b` factors through `f`; moreover the inverse image
`b⁻¹(U)` has quasi-compact inclusion and is scheme-theoretically dense in `W'`. -/
theorem exists_isAdmissibleBlowup_dominating_of_qcqs_scheme (W : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj W)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj W)]
    (U₀ : ((BigFppfOver.toScheme B S hS).obj W).Opens)
    (hU₀ : IsCompact (U₀ : Set ((BigFppfOver.toScheme B S hS).obj W)))
    (X : Over (yoneda.obj W)) (hX : IsAlgebraicSpace B S hS X.left)
    (hiso : IsIso (pullback.snd X.hom (openSubspaceOfPoints B S hS (yoneda.obj W)
      (pointsToScheme B S hS W ⁻¹' (U₀ : Set _))).ι))
    (hf : IsProper B S hS X.hom) :
    ∃ (S' : AlgebraicSpaces B S hS) (b : S' ⟶ schemeSpace W),
      IsAdmissibleBlowup B S hS
        ⟨openSubspaceOfPoints B S hS (yoneda.obj W) (pointsToScheme B S hS W ⁻¹' (U₀ : Set _)),
          isOpenSubspace_openSubspaceOfPoints_preimage_pointsToScheme W U₀⟩ b ∧
        IsQuasiCompact B S hS ((openSubspaceOfPoints B S hS (yoneda.obj W)
          (pointsToScheme B S hS W ⁻¹' (U₀ : Set _))).preimage b.hom).ι ∧
        IsSchemeTheoreticallyDense B S hS ((openSubspaceOfPoints B S hS (yoneda.obj W)
          (pointsToScheme B S hS W ⁻¹' (U₀ : Set _))).preimage b.hom) ∧
        ∃ g : S'.obj ⟶ X.left, g ≫ X.hom = b.hom := by
  have := hiso
  set U := openSubspaceOfPoints B S hS (yoneda.obj W) (pointsToScheme B S hS W ⁻¹' (U₀ : Set _))
    with hUdef
  have hU : IsOpenSubspace B S hS U :=
    isOpenSubspace_openSubspaceOfPoints_preimage_pointsToScheme W U₀
  have hQ := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W
  -- an affine étale chart of `X`
  have hqcX : IsQuasiCompactSpace B S hS X.left :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS hQ
      (isQuasiCompactSpace_yoneda B S hS W inferInstance) X.hom hf.2.1.2
  obtain ⟨V, u, hVaff, husp, hue⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.left hX).1 hqcX
  have hus : IsSurjective B S hS u :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.left hX V u).1 husp
  obtain ⟨g, hg⟩ : ∃ g : V ⟶ W, u ≫ X.hom = yoneda.map g :=
    ⟨yoneda.preimage (u ≫ X.hom), (yoneda.map_preimage _).symm⟩
  -- the scheme-level input: the chart is of finite type and quasi-separated, étale over `U₀`
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := by
    refine (isLocallyOfFiniteType_yoneda_map_iff B S hS g).1 ?_
    rw [← hg]
    exact isLocallyOfFiniteType_comp' B S hS u X.hom hX hQ
      (isLocallyOfFiniteType_of_isEtale' B S hS u hue) hf.2.1.1
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) := inferInstance
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map g) := quasiCompact_of_compactSpace _
  have : QuasiSeparated ((BigFppfOver.toScheme B S hS).map g) := inferInstance
  have : Etale ((BigFppfOver.toScheme B S hS).map g ∣_ U₀) :=
    etale_morphismRestrict_of_isEtale U₀ X.hom u hue g hg
  obtain ⟨K, hKfp, hKsupp, hKflat⟩ :=
    exists_supportSet_eq_compl_flat_strictTransformToBlowUp_of_finiteType
      ((BigFppfOver.toScheme B S hS).map g) U₀ hU₀ inferInstance inferInstance
  -- the blowup of `W` in `K` is the blowup of the algebraic space along `Z_K`
  have hbl := isBlowupAlong_closedSubspaceOfIdeal_schemeSpaceMap W K hKfp
  have hZpts : subspacePointSet B S hS (yoneda.obj W) (closedSubspaceOfIdeal W K).1 =
      (subspacePointSet B S hS (yoneda.obj W) U)ᶜ := by
    rw [subspacePointSet_closedSubspaceOfIdeal, subspacePointSet,
      range_pointsMap_ι_openSubspaceOfPoints, ← Set.preimage_compl]
    congr 1
  have hP := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (blowUpObj W K)
  have hdense : IsSchemeTheoreticallyDense B S hS
      (U.preimage (yoneda.map (blowUpObjHom W K))) :=
    isSchemeTheoreticallyDense_preimage_of_isBlowupAlong (X := schemeSpace W) ⟨U, hU⟩
      (closedSubspaceOfIdeal W K) hbl hZpts
  have hUqc : IsQuasiCompact B S hS U.ι := by
    have hUr : U = Subfunctor.range (yoneda.map (openSubHom W U₀)) :=
      openSubspaceOfPoints_preimage_pointsToScheme W U₀
    have := mono_yoneda_map_openSubHom W U₀
    have hι : (Subfunctor.range (yoneda.map (openSubHom W U₀))).ι =
        inv (Subfunctor.toRange (yoneda.map (openSubHom W U₀))) ≫ yoneda.map (openSubHom W U₀) :=
      (IsIso.eq_inv_comp _).2 (Subfunctor.toRange_ι _).symm
    rw [hUr, hι]
    refine isQuasiCompact_isIso_comp B S hS _
      (Space.isQuasiCompact_yoneda_map_of_quasiCompact B S hS _ ?_)
    have : CompactSpace ((BigFppfOver.toScheme B S hS).obj (openSub W U₀)) :=
      isCompact_iff_compactSpace.mp hU₀
    exact quasiCompact_of_compactSpace _
  have hqc : IsQuasiCompact B S hS (U.preimage (yoneda.map (blowUpObjHom W K))).ι :=
    isQuasiCompact_of_isPullback B S hS (Subfunctor.isPullback_preimage _ _) hUqc
  refine ⟨schemeSpace (blowUpObj W K), schemeSpaceMap (blowUpObjHom W K),
    ⟨closedSubspaceOfIdeal W K, isFinitePresentation_closedSubspaceOfIdeal W K hKfp,
      by
        change Disjoint (subspacePointSet B S hS (yoneda.obj W) U)
          (subspacePointSet B S hS (yoneda.obj W) (closedSubspaceOfIdeal W K).1)
        rw [hZpts]
        exact disjoint_compl_right, hbl⟩, hqc, hdense, ?_⟩
  exact exists_comp_eq_of_isFlat hQ hP hX X.hom hf U hU _ hqc hdense
    (isFlat_modificationSection_of_flat_strictTransformToBlowUp U₀ hX X.hom u hue hus g hg K
      hKsupp hKflat hqc)

end AlgebraicGeometry.Space

end
