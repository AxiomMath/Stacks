module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.ChartFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.SchemeFlatteningCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.Modifications
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms

/-!
# A proper modification of a Noetherian local ring is dominated by an admissible blowup

Let `(A, 𝔪, κ)` be a Noetherian local ring, let `U = Spec(A) ∖ V(𝔪)` be the punctured spectrum
and let `f : X ⟶ Spec(A)` be an object of the category of Stacks 0AS2 for `(A, 𝔪)` — an
algebraic space, locally of finite type over `Spec(A)`, with `f⁻¹(U) ⟶ U` an isomorphism — such
that `f` is proper. Then there is a `U`-admissible blowup `S' ⟶ Spec(A)` which dominates `X`:
it factors as `S' ⟶ X ⟶ Spec(A)`. This is Stacks 0AE6.

The source proves it as a special case of Stacks 087G. That lemma is proved here for the base of
the situation, the spectrum of a Noetherian ring and an arbitrary open `U₀` of it
(`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_dominating_of_isAffine`), along the route of
Stacks 087E and 0GUW:

* an affine étale chart `V ⟶ X` is a scheme of finite type over the base which is étale over
  `U₀`, so the Raynaud–Gruson flattening theorem, Stacks 0815, in the form
  `AlgebraicGeometry.exists_supportSet_eq_compl_flat_strictTransformToBlowUp`, gives a centre
  `K` cutting out exactly the complement of `U₀` along which the strict transform of `V` is
  flat over the blowup `Bl_K`;
* `Bl_K ⟶ Spec(A)` is the `U₀`-admissible blowup of the algebraic space
  (`AlgebraicGeometry.Space.isBlowupAlong_schemeSpaceMap_blowUpObjHom`, through Stacks 085R);
* the scheme-theoretic closure `X'` of the open part of `X ×_{Spec A} Bl_K` is flat over `Bl_K`,
  being so on the chart, where it is the strict transform of `V`
  (`AlgebraicGeometry.Space.isFlat_modificationSection_of_flat_strictTransformToBlowUp`, the
  content of Stacks 0863 here);
* so `X' ⟶ Bl_K` is finite by Stacks 0B4J and an open immersion by Stacks 0879, hence an
  isomorphism, and its inverse dominates `X`
  (`AlgebraicGeometry.Space.exists_comp_eq_of_isFlat`).

## Main results

* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_dominating_of_isAffine`: Stacks 087G over a
  Noetherian affine scheme of the site.
* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_dominating_of_isLocalRing`:
  **Stacks 0AE6**.

## References

* [Stacks Project, Tag 0AE6](https://stacks.math.columbia.edu/tag/0AE6)
* [Stacks Project, Tag 087G](https://stacks.math.columbia.edu/tag/087G)
* [Stacks Project, Tag 0GUW](https://stacks.math.columbia.edu/tag/0GUW)
* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 0AS2](https://stacks.math.columbia.edu/tag/0AS2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_LocalRing :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_LocalRing
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Two morphisms into a space over `W` which is an isomorphism over `U` agree once they agree
over `W` through `U`. -/
theorem eq_of_comp_eq_of_isIso_pullback_snd {X W T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ W) (U : Subfunctor W) [IsIso (pullback.snd f U.ι)] {p q : T ⟶ X}
    (r : T ⟶ U.toFunctor) (hp : p ≫ f = r ≫ U.ι) (hq : q ≫ f = r ≫ U.ι) : p = q := by
  have : Mono (pullback.snd f U.ι) := IsIso.mono_of_iso _
  have h : pullback.lift p r hp = pullback.lift q r hq := by
    rw [← cancel_mono (pullback.snd f U.ι), pullback.lift_snd, pullback.lift_snd]
  simpa only [pullback.lift_fst] using congrArg (· ≫ pullback.fst f U.ι) h

/-- The Yoneda image of the inclusion of an open of a scheme of the site is a monomorphism. -/
private theorem mono_yoneda_map_openSubHom (Q : BigFppfOver B S hS)
    (U₀ : ((BigFppfOver.toScheme B S hS).obj Q).Opens) :
    Mono (yoneda.map (openSubHom Q U₀)) := by
  have : Mono (openSubHom Q U₀) := (BigFppfOver.toScheme B S hS).mono_of_mono_map (by
    rw [toScheme_map_openSubHom B S hS]
    exact inferInstanceAs (Mono U₀.ι))
  exact Functor.map_mono yoneda _

/-- **An étale chart of a modification is étale over the open part of the base.** -/
theorem flat_morphismRestrict_of_isEtale {Q : BigFppfOver B S hS}
    (U₀ : ((BigFppfOver.toScheme B S hS).obj Q).Opens)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj Q)
    [IsIso (pullback.snd f (openSubspaceOfPoints B S hS (yoneda.obj Q)
      (pointsToScheme B S hS Q ⁻¹' (U₀ : Set _))).ι)]
    {V : BigFppfOver B S hS} (u : yoneda.obj V ⟶ X) (hu : IsEtale B S hS u) (g : V ⟶ Q)
    (hg : u ≫ f = yoneda.map g) :
    Flat ((BigFppfOver.toScheme B S hS).map g ∣_ U₀) := by
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
  have : Etale ((BigFppfOver.toScheme B S hS).map h) := etale_of_isEtale_yoneda_map B S hS hh
  exact inferInstanceAs (Flat ((BigFppfOver.toScheme B S hS).map h))

/-- **Stacks 087G over a Noetherian affine scheme.** Let `W` be an object of the site whose
underlying scheme is affine and Noetherian, let `U₀` be an open of it and `U ⊆ W` the open
subspace of the points over `U₀`. Let `f : X ⟶ W` be a proper morphism of algebraic spaces which
is an isomorphism over `U`. Then there is a `U`-admissible blowup `b : S' ⟶ W` which dominates
`X`: `b` factors through `f`. -/
theorem exists_isAdmissibleBlowup_dominating_of_isAffine (W : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj W)]
    (U₀ : ((BigFppfOver.toScheme B S hS).obj W).Opens) (X : Over (yoneda.obj W))
    (hX : IsAlgebraicSpace B S hS X.left)
    [IsIso (pullback.snd X.hom (openSubspaceOfPoints B S hS (yoneda.obj W)
      (pointsToScheme B S hS W ⁻¹' (U₀ : Set _))).ι)]
    (hf : IsProper B S hS X.hom) :
    ∃ (S' : AlgebraicSpaces B S hS) (b : S' ⟶ schemeSpace W),
      IsAdmissibleBlowup B S hS
        ⟨openSubspaceOfPoints B S hS (yoneda.obj W) (pointsToScheme B S hS W ⁻¹' (U₀ : Set _)),
          isOpenSubspace_openSubspaceOfPoints_preimage_pointsToScheme W U₀⟩ b ∧
        ∃ g : S'.obj ⟶ X.left, g ≫ X.hom = b.hom := by
  set U := openSubspaceOfPoints B S hS (yoneda.obj W) (pointsToScheme B S hS W ⁻¹' (U₀ : Set _))
    with hUdef
  have hU : IsOpenSubspace B S hS U :=
    isOpenSubspace_openSubspaceOfPoints_preimage_pointsToScheme W U₀
  have hQ := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W
  have hqcX : IsQuasiCompactSpace B S hS X.left :=
    isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS W inferInstance hX hQ X.hom hf.2.2
  obtain ⟨V, u, hVaff, husp, hue⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.left hX).1 hqcX
  have hus : IsSurjective B S hS u :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.left hX V u).1 husp
  have hV := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V
  obtain ⟨g, hg⟩ : ∃ g : V ⟶ W, u ≫ X.hom = yoneda.map g :=
    ⟨yoneda.preimage (u ≫ X.hom), (yoneda.map_preimage _).symm⟩
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := by
    refine (isLocallyOfFiniteType_yoneda_map_iff B S hS g).1 ?_
    rw [← hg]
    exact isLocallyOfFiniteType_comp' B S hS u X.hom hX hQ
      (isLocallyOfFiniteType_of_isEtale' B S hS u hue) hf.2.1.1
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) := inferInstance
  have : Flat ((BigFppfOver.toScheme B S hS).map g ∣_ U₀) :=
    flat_morphismRestrict_of_isEtale U₀ X.hom u hue g hg
  obtain ⟨K, hKfp, hKsupp, hKflat⟩ :=
    exists_supportSet_eq_compl_flat_strictTransformToBlowUp ((BigFppfOver.toScheme B S hS).map g)
      U₀ (TopologicalSpace.NoetherianSpace.isCompact _)
  have hbl := isBlowupAlong_schemeSpaceMap_blowUpObjHom W K hKfp
  have hZpts : subspacePointSet B S hS (yoneda.obj W) (closedSubspaceOfIdeal W K).1 =
      (subspacePointSet B S hS (yoneda.obj W) U)ᶜ := by
    rw [subspacePointSet_closedSubspaceOfIdeal, subspacePointSet,
      range_pointsMap_ι_openSubspaceOfPoints, ← Set.preimage_compl]
    congr 1
  refine ⟨schemeSpace (blowUpObj W K), schemeSpaceMap (blowUpObjHom W K),
    ⟨closedSubspaceOfIdeal W K, isFinitePresentation_closedSubspaceOfIdeal W K hKfp,
      by
        show Disjoint (subspacePointSet B S hS (yoneda.obj W) U)
          (subspacePointSet B S hS (yoneda.obj W) (closedSubspaceOfIdeal W K).1)
        rw [hZpts]
        exact disjoint_compl_right, hbl⟩, ?_⟩
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
    have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) := inferInstance
    rw [toScheme_map_openSubHom B S hS]
    exact inferInstanceAs (QuasiCompact U₀.ι)
  have hqc : IsQuasiCompact B S hS (U.preimage (yoneda.map (blowUpObjHom W K))).ι :=
    isQuasiCompact_of_isPullback B S hS (Subfunctor.isPullback_preimage _ _) hUqc
  exact exists_comp_eq_of_isFlat hQ hP hX X.hom hf U hU _ hqc hdense
    (isFlat_modificationSection_of_flat_strictTransformToBlowUp U₀ hX X.hom u hue hus g hg K
      hKsupp hKflat hqc)

/-- The open subspace `U = Spec(A) ∖ V(I)` of the algebraic space represented by `Spec(A)`. -/
theorem isOpenSubspace_compl_zeroLocusPoints {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A))) (s : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsOpenSubspace B S hS (openSubspaceOfPoints B S hS
      (yoneda.obj (FormalSpace.affineOver B S hS hA s))
      (FormalSpace.zeroLocusPoints B S hS hA s I)ᶜ) := by
  rw [FormalSpace.zeroLocusPoints_eq_preimage_pointsToScheme]
  exact isOpenSubspace_openSubspaceOfPoints_preimage_pointsToScheme
    (FormalSpace.affineOver B S hS hA s)
    ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- **Stacks 0AE6.** Let `(A, 𝔪, κ)` be a Noetherian local ring, let `U = Spec(A) ∖ V(𝔪)` and let
`f : X ⟶ Spec(A)` be an object of the category of Stacks 0AS2 for `(A, 𝔪)` — an algebraic space,
locally of finite type over `Spec(A)`, with `f⁻¹(U) ⟶ U` an isomorphism — such that `f` is
proper. Then there exists a `U`-admissible blowup `S' ⟶ Spec(A)` which dominates `X`, that is,
the blowup morphism factors as `S' ⟶ X ⟶ Spec(A)`.

The algebraic spaces are those over an arbitrary base scheme `S` of the big fppf site, with
`Spec(A)` an object of the site over `S`; the source's category is that of algebraic spaces over
`Spec(A)`, which is the case `S = Spec(A)`. Being a `U`-admissible blowup is Stacks 086B,
`AlgebraicGeometry.Space.IsAdmissibleBlowup`. -/
@[stacks 0AE6]
theorem exists_isAdmissibleBlowup_dominating_of_isLocalRing {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (hA : B.Contains (Spec (.of A))) (s : Spec (.of A) ⟶ S)
    (X : Over (yoneda.obj (FormalSpace.affineOver B S hS hA s)))
    (hX : IsFiniteTypeModification B S hS
      (openSubspaceOfPoints B S hS (yoneda.obj (FormalSpace.affineOver B S hS hA s))
        (FormalSpace.zeroLocusPoints B S hS hA s (IsLocalRing.maximalIdeal A))ᶜ) X)
    (hf : IsProper B S hS X.hom) :
    ∃ (S' : AlgebraicSpaces B S hS) (b : S' ⟶ schemeSpace (FormalSpace.affineOver B S hS hA s)),
      IsAdmissibleBlowup B S hS
        ⟨openSubspaceOfPoints B S hS (yoneda.obj (FormalSpace.affineOver B S hS hA s))
          (FormalSpace.zeroLocusPoints B S hS hA s (IsLocalRing.maximalIdeal A))ᶜ,
          isOpenSubspace_compl_zeroLocusPoints hA s _⟩ b ∧
        ∃ g : S'.obj ⟶ X.left, g ≫ X.hom = b.hom := by
  let U₀ : ((BigFppfOver.toScheme B S hS).obj (FormalSpace.affineOver B S hS hA s)).Opens :=
    ⟨(PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal A : Ideal A) : Set A))ᶜ,
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩
  have hUeq : openSubspaceOfPoints B S hS (yoneda.obj (FormalSpace.affineOver B S hS hA s))
      (FormalSpace.zeroLocusPoints B S hS hA s (IsLocalRing.maximalIdeal A))ᶜ =
      openSubspaceOfPoints B S hS (yoneda.obj (FormalSpace.affineOver B S hS hA s))
        (pointsToScheme B S hS (FormalSpace.affineOver B S hS hA s) ⁻¹' (U₀ : Set _)) := by
    rw [FormalSpace.zeroLocusPoints_eq_preimage_pointsToScheme]
    rfl
  have : AlgebraicGeometry.IsNoetherian
      ((BigFppfOver.toScheme B S hS).obj (FormalSpace.affineOver B S hS hA s)) :=
    inferInstanceAs (AlgebraicGeometry.IsNoetherian (Spec (.of A)))
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (FormalSpace.affineOver B S hS hA s)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  have hiso := hX.isIso_pullback_snd
  rw [hUeq] at hiso
  obtain ⟨S', b, ⟨Z, hZfp, hZdisj, hZbl⟩, g, hg⟩ :=
    exists_isAdmissibleBlowup_dominating_of_isAffine (FormalSpace.affineOver B S hS hA s) U₀ X
      hX.source_isAlgebraicSpace hf
  refine ⟨S', b, ⟨Z, hZfp, ?_, hZbl⟩, g, hg⟩
  show Disjoint (subspacePointSet B S hS (yoneda.obj (FormalSpace.affineOver B S hS hA s))
      (openSubspaceOfPoints B S hS (yoneda.obj (FormalSpace.affineOver B S hS hA s))
      (FormalSpace.zeroLocusPoints B S hS hA s (IsLocalRing.maximalIdeal A))ᶜ))
    (subspacePointSet B S hS (yoneda.obj (FormalSpace.affineOver B S hS hA s)) Z.1)
  rw [hUeq]
  exact hZdisj

end AlgebraicGeometry.Space

end
