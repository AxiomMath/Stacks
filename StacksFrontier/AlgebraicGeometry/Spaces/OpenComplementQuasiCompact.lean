module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Sheaves.SectionsWithSupport.QuasiCompactOpenIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback

/-!
# The complement of the zero locus of a finite type ideal sheaf is retrocompact

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`ℐ ⊆ 𝒪_X` be a sheaf of ideals on its small étale site which is cartesian on affine charts and
whose sections over every affine étale chart form a finitely generated ideal.  The unit locus
`X ∖ V(ℐ)` of `ℐ` then meets every affine étale chart in a quasi-compact open: that is the
scheme-level statement `AlgebraicGeometry.isCompact_of_isFiniteType_of_support_eq_compl`, the
implication (4) ⟹ (2) of Stacks 01PH, applied to the Zariski sheaf of ideals
`AlgebraicGeometry.Space.idealSheafDataOfChart` which the chart inherits.

For the Fitting ideal sheaf of a quasi-coherent module of finite presentation this gives
**quasi-compactness of the inclusion `X ∖ Z_r ⟶ X`**, which is the hypothesis the remaining
morphisms of Stacks 0CZ9 and 0CZA need.  Quasi-compactness is tested on affine test objects by
`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine`, and an affine
test object `T ⟶ X` is *not* an étale chart of `X`; what makes the test affine-chart-local all
the same is the base change of Fitting ideals, Stacks 0CZ4, in the point-set form
`AlgebraicGeometry.Space.idealUnitLocus_fittingIdeal_modulePullback`: the preimage of the unit
locus in `T` is the unit locus of the Fitting ideal sheaf of the pulled back module on the
represented algebraic space `T`, whose identity chart is affine.

## Main results

* `AlgebraicGeometry.Space.isFiniteType_idealSheafDataOfChart_of_fg_chartIdeal`: the Zariski
  sheaf of ideals a chart inherits from a sheaf of ideals with finitely generated sections over
  affine charts is of finite type.
* `AlgebraicGeometry.Space.isCompact_chartUnitLocusPreimage`: the unit locus meets an affine
  étale chart in a quasi-compact open.
* `AlgebraicGeometry.Space.isCompact_idealUnitLocus_of_isAffine`: on an algebraic space
  represented by an affine scheme of the site the whole unit locus is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompact_ι_openComplement_fittingClosedSubspace`: **the
  inclusion of `X ∖ Z_r` is a quasi-compact morphism**, for the Fitting closed subspaces of a
  quasi-coherent module of finite presentation.

## Implementation notes

The finite-type statement is the one place where the transport
`AlgebraicGeometry.Space.openChartIdeal` is unwound: the ideal which
`AlgebraicGeometry.Space.idealSheafDataOfChart` assigns to an affine open `V` of the chart is
the image of the sections of `ℐ` over the étale chart `V` cuts out along a ring isomorphism, and
the image of a finitely generated ideal is finitely generated.  Finite generation of those
sections is read off from the chartwise Fitting ideal by
`AlgebraicGeometry.Space.fittingIdeal_obj_eq_fittingIdealOnChart` and
`AlgebraicGeometry.Space.fg_fittingIdealOnChart`, which is Stacks 07ZA; this is the same input
as the finite type of the Fitting ideal sheaf, Stacks 0CZ5, and no new finiteness enters.

The identity chart `AlgebraicGeometry.Space.idChart` of a represented algebraic space has the
representing object as its scheme, and the point comparison of clause (1) of Stacks 03BX is its
map to the points of the space; so the unit locus of a sheaf of ideals on a represented space is
the homeomorphic image of the preimage of that unit locus in the representing scheme.

Quasi-compactness of the morphism is assembled from compactness of that preimage through the
representability of an open immersion: the base change of `(X ∖ Z_r).ι` along an affine test
object is represented by an open immersion of schemes whose image is exactly the preimage of the
point set of `X ∖ Z_r`, by
`AlgebraicGeometry.Space.preimage_range_pointsMap_eq_range_pointsMap_snd` and
`AlgebraicGeometry.Space.mem_range_pointsMap_yoneda_map_iff`; an open immersion of schemes with
compact image has compact source, and a represented algebraic space with compact scheme is
quasi-compact by Stacks 03E3.

## References

* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
* [Stacks Project, Tag 0CZ4](https://stacks.math.columbia.edu/tag/0CZ4)
* [Stacks Project, Tag 0CZ5](https://stacks.math.columbia.edu/tag/0CZ5)
* [Stacks Project, Tag 0CZ9](https://stacks.math.columbia.edu/tag/0CZ9)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Finite type of the sheaf of ideals a chart inherits -/

section ChartIdeal

variable (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)

/-- **The Zariski sheaf of ideals which an étale chart inherits from a sheaf of ideals with
finitely generated sections over the affine charts is of finite type.**

The ideal it assigns to an affine open `V` of the chart's scheme is the image, along the
comparison ring isomorphism of `AlgebraicGeometry.Space.openChartTopRingHom`, of the sections of
the sheaf of ideals over the étale chart which `V` cuts out; the image of a finitely generated
ideal is generated by the images of its generators. -/
theorem isFiniteType_idealSheafDataOfChart_of_fg_chartIdeal
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    (hfg : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
        (chartIdeal B S hS X N A).FG)
    (A : SmallEtale B S hS X.1) :
    Scheme.IdealSheafData.IsFiniteType (idealSheafDataOfChart B S hS X N hN A) := by
  classical
  intro V
  rw [ideal_idealSheafDataOfChart B S hS X N hN A V]
  obtain ⟨s, hs⟩ := hfg (openChart B S hS X.1 A V.1) V.2
  refine ⟨s.image (openChartTopRingHom B S hS X A V.1), ?_⟩
  rw [Finset.coe_image, ← Ideal.map_span, hs]
  rfl

/-- **The unit locus of a sheaf of ideals of finite type meets an affine étale chart in a
quasi-compact open.**

The complement of the support of the chartwise sheaf of ideals is the preimage of the unit locus
by `AlgebraicGeometry.Space.support_compl_eq_chartUnitLocusPreimage`, and on a quasi-compact
scheme the complement of the support of a sheaf of ideals of finite type is quasi-compact: that
is the implication (4) ⟹ (2) of Stacks 01PH. -/
theorem isCompact_chartUnitLocusPreimage
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    (hfg : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
        (chartIdeal B S hS X N A).FG)
    (A : SmallEtale B S hS X.1)
    (hA : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A)) :
    IsCompact (chartUnitLocusPreimage B S hS X N A) := by
  have _ : IsAffine (chartScheme A) := hA
  have _ : CompactSpace (chartScheme A) :=
    isCompact_univ_iff.1 (by simpa using (isAffineOpen_top (chartScheme A)).isCompact)
  rw [← support_compl_eq_chartUnitLocusPreimage B S hS X N hN A]
  exact isCompact_of_isFiniteType_of_support_eq_compl _ _
    (isFiniteType_idealSheafDataOfChart_of_fg_chartIdeal B S hS X N hN hfg A) (by simp)

end ChartIdeal

/-! ### The identity chart of a represented algebraic space -/

/-- A set whose preimage under a continuous surjection is compact is compact. -/
private theorem isCompact_of_isCompact_preimage_of_surjective {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hcont : Continuous f) (hsurj : Function.Surjective f)
    {s : Set β} (h : IsCompact (f ⁻¹' s)) : IsCompact s := by
  simpa [hsurj.image_preimage] using h.image hcont

/-- The point of the represented algebraic space carried by a point of the scheme of the
identity chart is the point comparison of clause (1) of Stacks 03BX. -/
theorem chartSchemeToPoints_idChart (T : BigFppfOver B S hS) :
    chartSchemeToPoints B S hS (yoneda.obj T) (idChart B S hS T) =
      (pointsEquivScheme B S hS T).symm := by
  funext x
  rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]
  exact congrFun (pointsMap_id B S hS (yoneda.obj T)) _

/-- **On an algebraic space represented by an affine object of the site the unit locus of a
sheaf of ideals of finite type is quasi-compact.**  The identity chart has that affine
object as its scheme and is surjective on points, so the unit locus is the image of its
preimage in that scheme, which is quasi-compact. -/
theorem isCompact_idealUnitLocus_of_isAffine (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (N : (SheafOfModules.unit (structureRingSheaf B S hS
      (schemeSpace T))).Submodule)
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    (hfg : ∀ A : SmallEtale B S hS (yoneda.obj T),
      IsAffine ((SmallEtale.toOver B S hS (yoneda.obj T) ⋙
          BigFppfOver.toScheme B S hS).obj A) →
        (chartIdeal B S hS (schemeSpace T) N A).FG) :
    IsCompact (idealUnitLocus B S hS
      (schemeSpace T) N) := by
  have heq := chartSchemeToPoints_idChart B S hS T
  have hsurj : Function.Surjective
      (chartSchemeToPoints B S hS (yoneda.obj T) (idChart B S hS T)) := by
    rw [heq]; exact (pointsEquivScheme B S hS T).symm.surjective
  have hcont : Continuous
      (chartSchemeToPoints B S hS (yoneda.obj T) (idChart B S hS T)) := by
    rw [heq]; exact (schemePointsHomeomorph B S hS T).symm.continuous
  exact isCompact_of_isCompact_preimage_of_surjective hcont hsurj
    (isCompact_chartUnitLocusPreimage B S hS _ N hN hfg (idChart B S hS T) hT)

/-! ### Quasi-compactness of the inclusion of an open subspace -/

/-- **An open subspace whose point set has compact preimage in every affine test object has
quasi-compact inclusion.**

Quasi-compactness is tested on affine test objects by Stacks 03KG, and the base change of the
inclusion along such a test object is represented by an open immersion of schemes whose image is
the preimage of the point set; an open immersion with compact image has compact source, and a
represented algebraic space whose scheme is compact is quasi-compact by Stacks 03E3. -/
theorem isQuasiCompact_ι_of_forall_isCompact_preimage {V : Subfunctor X.1}
    (hV : IsOpenSubspace B S hS V)
    (hc : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ a : yoneda.obj T ⟶ X.1, IsCompact (pointsMap B S hS (yoneda.obj T) a ⁻¹'
        Set.range (pointsMap B S hS V.toFunctor V.ι))) :
    IsQuasiCompact B S hS V.ι := by
  refine isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS hV.1 X.2 V.ι
    fun T hT a ↦ ?_
  have _ : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd a)) := hV.2.property_snd a
  have hpre : pointsMap B S hS (yoneda.obj T) a ⁻¹'
      Set.range (pointsMap B S hS V.toFunctor V.ι) =
        pointsToScheme B S hS T ⁻¹'
          Set.range ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd a)) := by
    rw [preimage_range_pointsMap_eq_range_pointsMap_snd B S hS hV.2.rep a]
    ext w
    exact mem_range_pointsMap_yoneda_map_iff B S hS (hV.2.rep.snd a) w
  have hrange : IsCompact
      (Set.range ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd a))) :=
    isCompact_of_isCompact_preimage_of_surjective (schemePointsHomeomorph B S hS T).continuous
      (surjective_pointsToScheme B S hS T) (hpre ▸ hc T hT a)
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj (hV.2.rep.pullback a)) :=
    isCompact_univ_iff.1 (by
      refine (Scheme.Hom.isOpenEmbedding
        ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd a))).isEmbedding.isCompact_iff.2 ?_
      rwa [Set.image_univ])
  exact isQuasiCompactSpace_of_iso B S hS (hV.2.rep.isPullback a).flip.isoPullback
    (isQuasiCompact_yoneda_of_compact B S hS _ inferInstance)

/-! ### The Fitting case -/

/-- The sections of the `r`-th Fitting ideal sheaf over an affine étale chart form a finitely
generated ideal: over an affine chart they are the chartwise Fitting ideal, and that is finitely
generated by Stacks 07ZA. -/
theorem fg_chartIdeal_fittingIdeal (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : IsCartesianOnAffineCharts G)
    (hfp : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.FinitePresentation (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)))
    (r : ℕ) (A : SmallEtale B S hS X.1)
    (hA : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A)) :
    (chartIdeal B S hS X (fittingIdeal B S hS X.1 X.2 G r) A).FG := by
  have hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)) := by
    intro W hW
    have := hfp W hW
    infer_instance
  have _ := hfin A hA
  rw [show chartIdeal B S hS X (fittingIdeal B S hS X.1 X.2 G r) A =
      @fittingIdealOnChart B S hS X.1 X.2 G r A (hfin A hA) from
    fittingIdeal_obj_eq_fittingIdealOnChart G hG hfin r hA]
  exact fg_fittingIdealOnChart G r (hfp A hA)

/-- **The inclusion of the complement of the `r`-th Fitting closed subspace is a quasi-compact
morphism**, for a quasi-coherent `𝒪_X`-module of finite presentation.

The point set of `X ∖ Z_r` is the unit locus of the `r`-th Fitting ideal sheaf, and its preimage
in an affine test object `T ⟶ X` is, by the base change of Fitting ideals in the point-set form
of Stacks 0CZ4, the unit locus of the `r`-th Fitting ideal sheaf of the pulled back module on
the algebraic space represented by `T`; that unit locus is quasi-compact because the Fitting
ideal sheaf is of finite type, Stacks 0CZ5, and `T` is affine. -/
theorem isQuasiCompact_ι_openComplement_fittingClosedSubspace
    (G : Modules.{u, u} B S hS X.1 X.2) (hGqc : G.IsQuasicoherentOnSite)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r) (r : ℕ) :
    IsQuasiCompact B S hS (openComplement B S hS (Z r).1).ι := by
  have hGft : SheafOfModules.IsFiniteTypeOnSite G := by
    have := hGfp
    infer_instance
  have hrange : Set.range (pointsMap B S hS
      (openComplement B S hS (Z r).1).toFunctor (openComplement B S hS (Z r).1).ι) =
        idealUnitLocus B S hS X (fittingIdeal B S hS X.1 X.2 G r) := by
    rw [openComplement_eq_openSubspaceOfPoints_idealUnitLocus B S hS X (Z r),
      range_pointsMap_ι_openSubspaceOfPoints, hZ r]
  refine isQuasiCompact_ι_of_forall_isCompact_preimage B S hS X
    (isOpenSubspace_openComplement B S hS X.2 (Z r).1 (Z r).2) fun T hT a ↦ ?_
  let T' : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let f : T' ⟶ X := ObjectProperty.homMk a
  have hpbqc : ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hGqc
  have hpbfp : SheafOfModules.IsFinitePresentationOnSite ((modulePullback B S hS f).obj G) :=
    isFinitePresentationOnSite_modulePullback B S hS f G hGfp
  have hpbcart : IsCartesianOnAffineCharts ((modulePullback B S hS f).obj G) :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS T'.1 T'.2 _ hpbqc
  have hpbsec := module_finitePresentation_sections_of_isFinitePresentationOnSite
    ((modulePullback B S hS f).obj G) hpbqc hpbfp
  have hcomp : IsCompact (idealUnitLocus B S hS T'
      (fittingIdeal B S hS T'.1 T'.2 ((modulePullback B S hS f).obj G) r)) :=
    isCompact_idealUnitLocus_of_isAffine B S hS T hT _
      (fittingIdeal_isCartesianOnAffineCharts _ hpbcart
        (fun W hW => by have := hpbsec W hW; infer_instance) r)
      (fg_chartIdeal_fittingIdeal B S hS T' ((modulePullback B S hS f).obj G)
        hpbcart hpbsec r)
  rw [idealUnitLocus_fittingIdeal_modulePullback B S hS G hGqc hGft f r] at hcomp
  rw [hrange]
  exact hcomp

end AlgebraicGeometry.Space

end
