module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Generic flatness for a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`F` be an `𝒪_X`-module which is quasi-coherent of finite type on charts. If `f` is of finite
type and `Y` is reduced, then there is a dense open subspace `W` of `Y` over which `f` becomes
flat, locally of finite presentation and quasi-compact, and over which `F` becomes flat over
`Y` and of finite presentation. This is Stacks 06QS, and it is proved here in the three steps
of the source: a reduced affine base, a reduced scheme, and a general reduced algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.finitePresentationLocus` is the set of points of an algebraic space
  at which a module is of finite presentation, read on a Zariski open of an étale scheme chart.

## Main results

* `AlgebraicGeometry.Space.exists_dense_open_genericFlatness_chart` is the one-chart core: the
  scheme-level generic flatness of Stacks 052B read on a commuting square of affine étale
  charts.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_pullback_snd_openSiteObject` transfers a
  property of the chart morphism over a dense open of the base to the base change of the
  morphism of algebraic spaces over that open.
* `AlgebraicGeometry.Space.exists_dense_open_genericFlatness_of_isAffine`: **Stacks 06QS** for
  a reduced affine base, which is step 3 of the source.
* `AlgebraicGeometry.Space.exists_dense_open_genericFlatness_of_isScheme`: **Stacks 06QS** for
  a reduced scheme base, which is step 2.
* `AlgebraicGeometry.Space.exists_dense_open_genericFlatness`: **Stacks 06QS**, step 1 and the
  statement of the tag.

## Implementation notes

The affine case is where the content lies. Quasi-compactness of `f` and of the affine base make
`X` quasi-compact, so Stacks 03H6 gives an affine scheme `U` of the site with `U → X` surjective
étale; Yoneda is full, so `U → X → Y` is the Yoneda image of a morphism `a` of the site whose
morphism of schemes `g` is of finite type — it is one commuting square of étale charts of `f` —
and quasi-compact, both ends being affine. Stacks 052B applied to `g` and to the chart
restriction `F|_U` produces the dense open, and that is
`AlgebraicGeometry.Space.exists_dense_open_genericFlatness_chart`, which is stated for an
arbitrary commuting square of affine étale charts rather than only for a surjective one,
because the two reductions use it over charts that dominate only part of the base.

An open `W` of an affine scheme of the site is again an object of the site, by
`AlgebraicGeometry.Space.openSiteObject`, and the base change of `f` over it is
`pullback.snd f (yoneda.map (openSiteObjectHom B S hS Z W))`, which is the idiom this
development uses for the restriction of a morphism over an open subspace. Flatness and local
finite presentation of that base change are the every-chart conditions of Stacks 03ML and
Stacks 03XP; each is obtained from the one surjective étale chart `U ×_Y W → X_W` of its source
by `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_surjectiveEtale_source`, the leg of
Stacks 03MM and Stacks 0410 making those properties étale local on the source. On that chart
the morphism of schemes is a base change of `g`, hence isomorphic to the restriction `g ∣_ W`
for which Stacks 052B supplies the property. Quasi-compactness of the base change needs none of
this: it is stability of quasi-compactness under base change, Stacks 03KG.

The two reductions are carried out together, in
`AlgebraicGeometry.Space.exists_dense_open_genericFlatness`. For each affine open `V` of a
reduced scheme chart of `Y` the base change of `f` over `V` is quasi-compact, so the affine
argument applies to it and yields a dense open `W_V` of `V`; the open subspace cut out by the
union of the point sets of the `W_V` is dense in `Y`, because an étale chart is open and
surjective on points. The two morphism conclusions are then assembled by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_openSubspace_cover_target`, the Zariski
locality on the target of the every-chart condition, which is the leg (9) implies (1) of
Stacks 03MM; the comparison of the base change over a member of that covering with the base
change over `W_V` is Stacks 03MJ read through
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_etaleChart`, the covering member and `W_V`
having the same point set. The scheme case is the general case for a representable base, where
the chart may be taken to be the identity.

The two conclusions about the module are stated pointwise, as the containment of the points of
`X` lying over `W` in `AlgebraicGeometry.Space.flatLocus` of Stacks 0DLR and in
`AlgebraicGeometry.Space.finitePresentationLocus`. This is the faithful rendering available
here. The source states them as properties of the restriction `F|_{X_W}` as a module on the
algebraic space `X_W`, which in this development would be
`AlgebraicGeometry.Space.modulePullback` along the projection, and nothing compares the chart
restriction `AlgebraicGeometry.Space.restrictToChart` of such a pullback with the pullback of a
chart restriction *in the generality this statement needs* — the comparison recorded as missing
under Tag 05VP in `StacksFrontier/AlgebraicGeometry/Spaces/GeometricStalkBaseChange.lean`. What is
available is `AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, the comparison for a
quasi-coherent module across a commuting square of *charts*, in the shape
`AlgebraicGeometry.Space.ChartRestrictionBaseChange` names; it compares the chart restriction of
a pullback with the Zariski pullback of a chart restriction and not with the chart restriction of
a module on the base change, which is what the restatement asks for. The pointwise form loses
nothing for a quasi-coherent module: membership of the flat locus is flatness of the geometric
stalk, by `AlgebraicGeometry.Space.mem_flatLocus_iff_isFlatOverAtGeometricPoint`, and
`AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV is flatness at every geometric point by
`AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtGeometricPoint`; flatness over `Y`
at a point over `W` is flatness over `W` because `W → Y` is an open immersion. It is the
precedent Tag 0DLR already sets in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatFiniteTypeModuleLocus.lean`, and it is also the form
that survives the two reductions, both of which only cover the base.

The hypotheses on the module are the chartwise ones,
`AlgebraicGeometry.Space.IsQuasicoherentOnCharts` and
`AlgebraicGeometry.Space.IsFiniteTypeOnCharts`, for the same reason and with the same
precedent: they are the weaker hypotheses, and they are what a result whose input is a module on
a scheme chart can consume directly. The site-local predicates
`SheafOfModules.IsQuasicoherentOnSite` and `SheafOfModules.IsFiniteTypeOnSite` do pass to the
chart restriction, by `AlgebraicGeometry.Space.isQuasicoherent_restrictToChart` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionSections.lean` and
`AlgebraicGeometry.Space.isFiniteType_restrictToChart` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionFromSite.lean`, so a consumer holding them
can supply the chartwise hypotheses below. Reducedness of the
base is `AlgebraicGeometry.Space.HasEtaleLocalProperty` at reducedness of schemes, Stacks 03E6,
which is the one surjective étale chart with reduced source that the argument consumes.

## References

* [Stacks Project, Tag 06QS](https://stacks.math.columbia.edu/tag/06QS)
* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The locus of points of an algebraic space at which a module is of finite presentation:
the points admitting an étale scheme chart with a Zariski open neighbourhood of a preimage
point on which the restriction of the module is of finite presentation. -/
def finitePresentationLocus (hX : IsAlgebraicSpace B S hS X)
    (F : Modules.{u, u} B S hS X hX) : Set (points B S hS X) :=
  {x | ∃ (U : SmallEtale B S hS X) (u : etaleChartScheme B S hS U)
      (V : (etaleChartScheme B S hS U).Opens), pointOfEtaleChart B S hS U u = x ∧ u ∈ V ∧
    ((chartModule B S hS hX F U).restrict V.ι).IsFinitePresentation}

/-- **Stacks 06QS, the one-chart core.** On a commuting square of étale charts of `f` whose
source and target charts are affine and whose target chart is reduced, the chart morphism
becomes flat and locally of finite presentation over a dense open of the target chart, over
which the module becomes flat over the target and of finite presentation. -/
@[stacks 06QS "the one-chart core of the proof: Tag 052B read on a commuting square of
affine étale charts"]
theorem exists_dense_open_genericFlatness_chart
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX)
    (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hft : IsFiniteTypeOnCharts B S hS hX F)
    {U V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsReduced ((BigFppfOver.toScheme B S hS).obj V)]
    {p : yoneda.obj U ⟶ X} {b : yoneda.obj V ⟶ Y} (a : U ⟶ V)
    (hpE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hbE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : p ≫ f = yoneda.map a ≫ b)
    (hLFT : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map a)) :
    ∃ W : ((BigFppfOver.toScheme B S hS).obj V).Opens,
      Dense (W : Set ((BigFppfOver.toScheme B S hS).obj V)) ∧
      AlgebraicGeometry.Flat (((BigFppfOver.toScheme B S hS).map a) ∣_ W) ∧
      AlgebraicGeometry.LocallyOfFinitePresentation
        (((BigFppfOver.toScheme B S hS).map a) ∣_ W) ∧
      ∀ u : (BigFppfOver.toScheme B S hS).obj U,
        ((BigFppfOver.toScheme B S hS).map a) u ∈ W →
          pointOfEtaleChart B S hS ⟨CostructuredArrow.mk p, hpE⟩ u ∈
              flatLocus B S hS hX f F ∧
            pointOfEtaleChart B S hS ⟨CostructuredArrow.mk p, hpE⟩ u ∈
              finitePresentationLocus B S hS hX F := by
  classical
  set Uc : SmallEtale B S hS X := ⟨CostructuredArrow.mk p, hpE⟩ with hUc
  set Vc : SmallEtale B S hS Y := ⟨CostructuredArrow.mk b, hbE⟩ with hVc
  set d : ChartDiagram B S hS X Y f := { U := Uc, V := Vc, g := a, comm := hcomm } with hd
  set g : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj V :=
    (BigFppfOver.toScheme B S hS).map a with hg
  have : AlgebraicGeometry.LocallyOfFiniteType g := hLFT
  have : AlgebraicGeometry.QuasiCompact g := inferInstance
  have := hqc Uc
  have := hft Uc
  obtain ⟨W, hWdense, hWflat, hWfp, hWmodflat, hWmodfp⟩ :=
    AlgebraicGeometry.exists_dense_open_flat_finitePresentation g
      (chartModule B S hS hX F Uc)
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at hWflat hWfp hWmodflat
  refine ⟨W, hWdense, hWflat, hWfp.1, fun u hu => ?_⟩
  refine ⟨⟨d, u, rfl, ?_⟩, ⟨Uc, u, g ⁻¹ᵁ W, rfl, hu, hWmodfp⟩⟩
  have h4 := hWmodflat ⟨u, hu⟩
  have : ((chartModule B S hS hX F Uc).restrict (g ⁻¹ᵁ W).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (g ⁻¹ᵁ W).ι
      (chartModule B S hS hX F Uc)
  rw [← AlgebraicGeometry.isFlatOverAt_comp_iff_of_etale (g ∣_ W) W.ι
      ((chartModule B S hS hX F Uc).restrict (g ⁻¹ᵁ W).ι) ⟨u, hu⟩,
    AlgebraicGeometry.morphismRestrict_ι] at h4
  exact (AlgebraicGeometry.isFlatOverAt_restrict_iff (g ⁻¹ᵁ W).ι g
    (chartModule B S hS hX F Uc) ⟨u, hu⟩).mp h4

/-- A property of morphisms of schemes which is étale local on the source and target, stable
under composition and base change and implied by étaleness holds on every étale chart of the
base change of `f : X ⟶ h_Z` over an open of `Z`, as soon as it holds of the restriction over
that open of the chart morphism of one surjective étale affine chart of `X`. -/
theorem holdsOnEveryEtaleChart_pullback_snd_openSiteObject
    (Q : MorphismProperty Scheme.{u}) (hQ : IsEtaleLocalOnSourceAndTarget Q)
    (hQcomp : Q.IsStableUnderComposition) (hQbc : Q.IsStableUnderBaseChange)
    (hX : IsAlgebraicSpace B S hS X) (Z : BigFppfOver B S hS) (f : X ⟶ yoneda.obj Z)
    {U : BigFppfOver B S hS} {p : yoneda.obj U ⟶ X} (a : U ⟶ Z)
    (hpE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (ha : yoneda.map a = p ≫ f)
    (W : ((BigFppfOver.toScheme B S hS).obj Z).Opens)
    (hQW : Q (((BigFppfOver.toScheme B S hS).map a) ∣_ W)) :
    HoldsOnEveryEtaleChart B S hS Q
      (pullback.snd f (yoneda.map (openSiteObjectHom B S hS Z W))) := by
  have := hQcomp
  have := hQbc
  set iW : openSiteObject B S hS Z W ⟶ Z := openSiteObjectHom B S hS Z W with hiW
  set j : yoneda.obj (openSiteObject B S hS Z W) ⟶ yoneda.obj Z := yoneda.map iW with hj
  set kW : pullback a iW ⟶ U := pullback.fst a iW with hkW
  set aW : pullback a iW ⟶ openSiteObject B S hS Z W := pullback.snd a iW with haW
  have hcomm : (yoneda.map kW ≫ p) ≫ f = yoneda.map aW ≫ j := by
    rw [Category.assoc, ← ha, hj, ← Functor.map_comp, ← Functor.map_comp, hkW, haW]
    exact congrArg yoneda.map pullback.condition
  set pW : yoneda.obj (pullback a iW) ⟶ pullback f j :=
    pullback.lift (yoneda.map kW ≫ p) (yoneda.map aW) hcomm with hpW
  have hpWfst : pW ≫ pullback.fst f j = yoneda.map kW ≫ p := pullback.lift_fst _ _ _
  have hpWsnd : pW ≫ pullback.snd f j = yoneda.map aW := pullback.lift_snd _ _ _
  have hsq : IsPullback (yoneda.map kW) pW p (pullback.fst f j) := by
    refine IsPullback.of_bot ?_ hpWfst.symm (IsPullback.of_hasPullback f j)
    rw [hpWsnd, ← ha, hkW, haW, hj]
    exact (IsPullback.of_hasPullback a iW).map yoneda
  have hpWE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf pW :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq hpE
  have hpWS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf pW :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq hpS
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hsqS : IsPullback ((BigFppfOver.toScheme B S hS).map aW)
      ((BigFppfOver.toScheme B S hS).map kW) W.ι
      ((BigFppfOver.toScheme B S hS).map a) := by
    have h := (IsPullback.of_hasPullback a iW).map (BigFppfOver.toScheme B S hS)
    rw [hiW, map_openSiteObjectHom] at h
    rw [hkW, haW]
    exact h.flip
  have hQaW : Q ((BigFppfOver.toScheme B S hS).map aW) := by
    have hiso := IsPullback.isoIsPullback_hom_fst _ _
      (AlgebraicGeometry.isPullback_morphismRestrict
        ((BigFppfOver.toScheme B S hS).map a) W) hsqS
    rw [← hiso] at hQW
    exact (Q.cancel_left_of_respectsIso _ _).mp hQW
  have hXW : IsAlgebraicSpace B S hS (pullback f j) :=
    isAlgebraicSpace_pullback B S hS f j hX
      (isAlgebraicSpace_yoneda B S hS (openSiteObject B S hS Z W))
      (isAlgebraicSpace_yoneda B S hS Z)
  refine holdsOnEveryEtaleChart_of_surjectiveEtale_source B S hS Q hQ hXW
    (isAlgebraicSpace_yoneda B S hS (openSiteObject B S hS Z W)) (pullback.snd f j) pW
    hpWS hpWE ?_
  rw [hpWsnd]
  exact holdsOnEveryEtaleChart_yoneda_map B S hS hQ aW hQaW

/-- Generic flatness over one reduced affine étale chart of the base: the base change of `f`
over a dense open of that chart is flat and locally of finite presentation, and every point of
`X` lying over that open is in the flat and finite presentation loci of the module. -/
private theorem exists_dense_open_genericFlatness_etaleAffine
    (hX : IsAlgebraicSpace B S hS X) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsFiniteType B S hS f)
    (F : Modules.{u, u} B S hS X hX)
    (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hft : IsFiniteTypeOnCharts B S hS hX F)
    (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsReduced ((BigFppfOver.toScheme B S hS).obj V)]
    (b : yoneda.obj V ⟶ Y)
    (hbE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ W : ((BigFppfOver.toScheme B S hS).obj V).Opens,
      Dense (W : Set ((BigFppfOver.toScheme B S hS).obj V)) ∧
      (∀ c : yoneda.obj (openSiteObject B S hS V W) ⟶ Y,
        c = yoneda.map (openSiteObjectHom B S hS V W) ≫ b →
          IsFlat B S hS (pullback.snd f c) ∧
            IsLocallyOfFinitePresentation B S hS (pullback.snd f c)) ∧
      ∀ (x : points B S hS X) (v : points B S hS (yoneda.obj V)),
        pointsMap B S hS X f x = pointsMap B S hS (yoneda.obj V) b v →
        pointsEquivScheme B S hS V v ∈ W →
          x ∈ flatLocus B S hS hX f F ∧ x ∈ finitePresentationLocus B S hS hX F := by
  classical
  have hmulEtale := isMultiplicative_presheaf_etale B S hS
  have hVy : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hPb : IsAlgebraicSpace B S hS (pullback f b) :=
    isAlgebraicSpace_pullback B S hS f b hX hVy hY
  have hgQC : IsQuasiCompact B S hS (pullback.snd f b) :=
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback f b) hf.2
  have hVcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) := inferInstance
  obtain ⟨Ua, pU, hUaaff, hpUS, hpUE0⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (pullback f b) hPb).mp
      (isQuasiCompactSpace_source_of_isQuasiCompact B S hS hVy
        (isQuasiCompactSpace_yoneda_obj B S hS hVcpt) hgQC)
  have hpUE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf pU :=
    (isEtale_iff_presheaf_of_yoneda B S hS pU).mp hpUE0
  obtain ⟨aV, haV⟩ := yoneda.map_surjective (pU ≫ pullback.snd f b)
  have hfstE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst f b) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback f b).flip hbE
  have hpE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pU ≫ pullback.fst f b) :=
    MorphismProperty.comp_mem _ pU (pullback.fst f b) hpUE hfstE
  have hcomm : (pU ≫ pullback.fst f b) ≫ f = yoneda.map aV ≫ b := by
    rw [haV, Category.assoc, Category.assoc, pullback.condition]
  have hVE1 : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj V)) :=
    MorphismProperty.id_mem _ _
  have hgLFT : IsLocallyOfFiniteType B S hS (pullback.snd f b) :=
    holdsOnEveryEtaleChart_pullback_snd_of_isAlgebraicSpace B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u})
      AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget inferInstance
      hX hY hVy f b hf.1
  have hLFT : AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map aV) :=
    hgLFT Ua V pU (𝟙 (yoneda.obj V)) aV hpUE hVE1 (by rwa [Category.comp_id])
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Ua) := hUaaff
  obtain ⟨W, hWdense, hWflat, hWlfp, hWpt⟩ :=
    exists_dense_open_genericFlatness_chart B S hS hX f F hqc hft aV hpE hbE hcomm hLFT
  have hAy : IsAlgebraicSpace B S hS (yoneda.obj (openSiteObject B S hS V W)) :=
    isAlgebraicSpace_yoneda B S hS (openSiteObject B S hS V W)
  refine ⟨W, hWdense, fun c hc => ?_, fun x v hxv hvW => ?_⟩
  · subst hc
    refine ⟨?_, ?_⟩
    · refine (holdsOnEveryEtaleChart_pullback_snd_comp_iff B S hS
        (@AlgebraicGeometry.Flat.{u}) AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget
        inferInstance (fun _ hk => have := hk; inferInstance) hX hY hVy hAy f b _).mpr ?_
      exact holdsOnEveryEtaleChart_pullback_snd_openSiteObject B S hS
        (@AlgebraicGeometry.Flat.{u}) AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget
        inferInstance inferInstance hPb V (pullback.snd f b) aV hpUE hpUS haV W hWflat
    · refine (holdsOnEveryEtaleChart_pullback_snd_comp_iff B S hS
        (@AlgebraicGeometry.LocallyOfFinitePresentation.{u})
        AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
        inferInstance (fun _ hk => have := hk; inferInstance) hX hY hVy hAy f b _).mpr ?_
      exact holdsOnEveryEtaleChart_pullback_snd_openSiteObject B S hS
        (@AlgebraicGeometry.LocallyOfFinitePresentation.{u})
        AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
        inferInstance inferInstance hPb V (pullback.snd f b) aV hpUE hpUS haV W hWlfp
  · obtain ⟨w, hwX, hwV⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback f b) x v hxv
    obtain ⟨uu, huu⟩ :=
      (surjective_iff_surjective_pointsMap B S hS (pullback f b) hPb Ua pU).mp hpUS w
    have hmapaV : pointsMap B S hS (yoneda.obj Ua) (yoneda.map aV) uu = v := by
      simp only [haV, pointsMap_comp, Function.comp_apply, huu, hwV]
    have hau : (BigFppfOver.toScheme B S hS).map aV (pointsEquivScheme B S hS Ua uu) ∈ W := by
      rwa [← pointsEquivScheme_pointsMap_yoneda, hmapaV]
    have hpu : pointOfEtaleChart B S hS
        ⟨CostructuredArrow.mk (pU ≫ pullback.fst f b), hpE⟩
        (pointsEquivScheme B S hS Ua uu) = x := by
      show pointsMap B S hS (yoneda.obj Ua) (pU ≫ pullback.fst f b)
        ((pointsEquivScheme B S hS Ua).symm (pointsEquivScheme B S hS Ua uu)) = x
      simp only [Equiv.symm_apply_apply, pointsMap_comp, Function.comp_apply, huu, hwX]
    rw [← hpu]
    exact hWpt (pointsEquivScheme B S hS Ua uu) hau

/-- **Stacks 06QS for a reduced affine base**, step 3 of the source. A finite-type morphism of
algebraic spaces to a reduced affine scheme of the site, together with a module which is
quasi-coherent of finite type on charts, becomes flat, locally of finite presentation and
quasi-compact, and the module flat over the base and of finite presentation, over a dense open
of the base. -/
@[stacks 06QS "step 3 of the proof: the case of a reduced affine base"]
theorem exists_dense_open_genericFlatness_of_isAffine
    (hX : IsAlgebraicSpace B S hS X) (Z : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsReduced ((BigFppfOver.toScheme B S hS).obj Z)]
    (f : X ⟶ yoneda.obj Z) (hf : IsFiniteType B S hS f)
    (F : Modules.{u, u} B S hS X hX)
    (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hft : IsFiniteTypeOnCharts B S hS hX F) :
    ∃ W : ((BigFppfOver.toScheme B S hS).obj Z).Opens,
      Dense (W : Set ((BigFppfOver.toScheme B S hS).obj Z)) ∧
      IsFlat B S hS (pullback.snd f (yoneda.map (openSiteObjectHom B S hS Z W))) ∧
      IsLocallyOfFinitePresentation B S hS
        (pullback.snd f (yoneda.map (openSiteObjectHom B S hS Z W))) ∧
      IsQuasiCompact B S hS (pullback.snd f (yoneda.map (openSiteObjectHom B S hS Z W))) ∧
      ∀ x : points B S hS X,
        pointsEquivScheme B S hS Z (pointsMap B S hS X f x) ∈ W →
          x ∈ flatLocus B S hS hX f F ∧ x ∈ finitePresentationLocus B S hS hX F := by
  have hmulEtale := isMultiplicative_presheaf_etale B S hS
  obtain ⟨W, hWdense, hWflat, hWpt⟩ :=
    exists_dense_open_genericFlatness_etaleAffine B S hS hX
      (isAlgebraicSpace_yoneda B S hS Z) f hf F hqc hft Z (𝟙 (yoneda.obj Z))
      (MorphismProperty.id_mem _ _)
  obtain ⟨hWflat', hWlfp'⟩ := hWflat (yoneda.map (openSiteObjectHom B S hS Z W))
    (Category.comp_id _).symm
  refine ⟨W, hWdense, hWflat', hWlfp',
    isQuasiCompact_pullback_snd_of_isQuasiCompact B S hS hf.2 _ _, fun x hx => ?_⟩
  refine hWpt x (pointsMap B S hS X f x) ?_ hx
  have h := pointsMap_comp B S hS X f (𝟙 (yoneda.obj Z))
  rw [Category.comp_id] at h
  exact congrFun h x

/-- The étale covering of a reduced scheme chart of the base by dense opens of its affine
opens, together with the two morphism conclusions over each member and the module conclusions
for the points of `X` lying over it. -/
private theorem exists_etaleCover_genericFlatness
    (hX : IsAlgebraicSpace B S hS X) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsFiniteType B S hS f)
    (F : Modules.{u, u} B S hS X hX)
    (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hft : IsFiniteTypeOnCharts B S hS hX F)
    (V₀ : BigFppfOver B S hS) [IsReduced ((BigFppfOver.toScheme B S hS).obj V₀)]
    (q : yoneda.obj V₀ ⟶ Y)
    (hqS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    ∃ (I : Type u) (A : I → BigFppfOver B S hS) (c : ∀ i, yoneda.obj (A i) ⟶ Y),
      (∀ i, (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (c i)) ∧
      (∀ (i : I) (c' : yoneda.obj (A i) ⟶ Y), c' = c i →
        IsFlat B S hS (pullback.snd f c') ∧
          IsLocallyOfFinitePresentation B S hS (pullback.snd f c')) ∧
      Dense (⋃ i, Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i))) ∧
      (∀ (i : I) (x : points B S hS X),
        pointsMap B S hS X f x ∈ Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i)) →
          x ∈ flatLocus B S hS hX f F ∧
            x ∈ finitePresentationLocus B S hS hX F) := by
  classical
  have hmulEtale := isMultiplicative_presheaf_etale B S hS
  have hbE : ∀ i : ((BigFppfOver.toScheme B S hS).obj V₀).affineOpens,
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (openSiteObjectHom B S hS V₀ i.1) ≫ q) := by
    intro i
    exact MorphismProperty.comp_mem _ _ _
      (presheaf_etale_yonedaMap_openSiteObjectHom B S hS V₀ i.1) hqE
  have hdata : ∀ i : ((BigFppfOver.toScheme B S hS).obj V₀).affineOpens,
      ∃ W : ((BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS V₀ i.1)).Opens,
        Dense (W : Set ((BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS V₀ i.1))) ∧
        (∀ c : yoneda.obj (openSiteObject B S hS (openSiteObject B S hS V₀ i.1) W) ⟶ Y,
          c = yoneda.map (openSiteObjectHom B S hS (openSiteObject B S hS V₀ i.1) W) ≫
              (yoneda.map (openSiteObjectHom B S hS V₀ i.1) ≫ q) →
            IsFlat B S hS (pullback.snd f c) ∧
              IsLocallyOfFinitePresentation B S hS (pullback.snd f c)) ∧
        ∀ (x : points B S hS X)
            (v : points B S hS (yoneda.obj (openSiteObject B S hS V₀ i.1))),
          pointsMap B S hS X f x =
              pointsMap B S hS (yoneda.obj (openSiteObject B S hS V₀ i.1))
                (yoneda.map (openSiteObjectHom B S hS V₀ i.1) ≫ q) v →
            pointsEquivScheme B S hS (openSiteObject B S hS V₀ i.1) v ∈ W →
              x ∈ flatLocus B S hS hX f F ∧
                x ∈ finitePresentationLocus B S hS hX F := by
    intro i
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (openSiteObject B S hS V₀ i.1)) := i.2
    have : IsReduced ((BigFppfOver.toScheme B S hS).obj
      (openSiteObject B S hS V₀ i.1)) := inferInstanceAs (IsReduced i.1.toScheme)
    exact exists_dense_open_genericFlatness_etaleAffine B S hS hX hY f hf F hqc hft
      (openSiteObject B S hS V₀ i.1) _ (hbE i)
  choose Wo hWdense hWmor hWpt using hdata
  refine ⟨((BigFppfOver.toScheme B S hS).obj V₀).affineOpens,
    fun i => openSiteObject B S hS (openSiteObject B S hS V₀ i.1) (Wo i),
    fun i => yoneda.map (openSiteObjectHom B S hS (openSiteObject B S hS V₀ i.1) (Wo i)) ≫
      (yoneda.map (openSiteObjectHom B S hS V₀ i.1) ≫ q),
    fun i => MorphismProperty.comp_mem _ _ _
      (presheaf_etale_yonedaMap_openSiteObjectHom B S hS
        (openSiteObject B S hS V₀ i.1) (Wo i)) (hbE i),
    fun i => hWmor i, ?_, ?_⟩
  · rw [dense_iff_inter_open]
    intro O hOopen hOne
    obtain ⟨y, hyO⟩ := hOne
    obtain ⟨v₀, hv₀⟩ := (surjective_iff_surjective_pointsMap B S hS Y hY V₀ q).mp hqS y
    have hO₁open : IsOpen ((pointsEquivScheme B S hS V₀).symm ⁻¹'
        (pointsMap B S hS (yoneda.obj V₀) q ⁻¹' O)) :=
      (hOopen.preimage (continuous_pointsMap B S hS q)).preimage
        (schemePointsHomeomorph B S hS V₀).symm.continuous
    have hzO₁ : pointsEquivScheme B S hS V₀ v₀ ∈
        (pointsEquivScheme B S hS V₀).symm ⁻¹'
          (pointsMap B S hS (yoneda.obj V₀) q ⁻¹' O) := by
      show pointsMap B S hS (yoneda.obj V₀) q
        ((pointsEquivScheme B S hS V₀).symm (pointsEquivScheme B S hS V₀ v₀)) ∈ O
      rw [Equiv.symm_apply_apply, hv₀]
      exact hyO
    obtain ⟨-, ⟨Aff, hAffmem, rfl⟩, hzAff, hAffsub⟩ :=
      ((BigFppfOver.toScheme B S hS).obj V₀).isBasis_affineOpens.exists_subset_of_mem_open
        hzO₁ hO₁open
    obtain ⟨i, rfl⟩ : ∃ i : ((BigFppfOver.toScheme B S hS).obj V₀).affineOpens,
        i.1 = Aff := ⟨⟨Aff, hAffmem⟩, rfl⟩
    have hNe : Nonempty ((BigFppfOver.toScheme B S hS).obj
        (openSiteObject B S hS V₀ i.1)) := ⟨⟨pointsEquivScheme B S hS V₀ v₀, hzAff⟩⟩
    obtain ⟨w, hw⟩ := (hWdense i).nonempty
    obtain ⟨t, htw⟩ : ∃ t, pointsEquivScheme B S hS (openSiteObject B S hS
        (openSiteObject B S hS V₀ i.1) (Wo i)) t = ⟨w, hw⟩ :=
      ⟨_, Equiv.apply_symm_apply _ _⟩
    have h1 : pointsEquivScheme B S hS (openSiteObject B S hS V₀ i.1)
        (pointsMap B S hS _ (yoneda.map
          (openSiteObjectHom B S hS (openSiteObject B S hS V₀ i.1) (Wo i))) t) = w := by
      rw [pointsEquivScheme_pointsMap_yoneda, map_openSiteObjectHom, htw]
      rfl
    have h3 : (BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS V₀ i.1) w ∈
        (i.1 : Set ((BigFppfOver.toScheme B S hS).obj V₀)) := by
      rw [map_openSiteObjectHom]
      exact w.2
    refine ⟨pointsMap B S hS _
      (yoneda.map (openSiteObjectHom B S hS (openSiteObject B S hS V₀ i.1) (Wo i)) ≫
        yoneda.map (openSiteObjectHom B S hS V₀ i.1) ≫ q) t, ?_, ?_⟩
    · simp only [pointsMap_comp, Function.comp_apply]
      have h4 : pointsMap B S hS _ (yoneda.map (openSiteObjectHom B S hS V₀ i.1))
          (pointsMap B S hS _ (yoneda.map
            (openSiteObjectHom B S hS (openSiteObject B S hS V₀ i.1) (Wo i))) t) =
          (pointsEquivScheme B S hS V₀).symm
            ((BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS V₀ i.1) w) := by
        refine (Equiv.eq_symm_apply _).mpr ?_
        rw [pointsEquivScheme_pointsMap_yoneda, h1]
      rw [h4]
      exact hAffsub h3
    · exact Set.mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
  · intro i x hx
    obtain ⟨t, ht⟩ := hx
    refine hWpt i x (pointsMap B S hS _
      (yoneda.map (openSiteObjectHom B S hS (openSiteObject B S hS V₀ i.1) (Wo i))) t)
      ?_ ?_
    · simp only [← ht, pointsMap_comp, Function.comp_apply]
    · rw [pointsEquivScheme_pointsMap_yoneda, map_openSiteObjectHom]
      exact (pointsEquivScheme B S hS _ t).2

/-- The range on points of an étale morphism from a representable presheaf is open. -/
private theorem isOpen_range_pointsMap_of_presheaf_etale
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS} (c : yoneda.obj V ⟶ Y)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c) :
    IsOpen (Set.range (pointsMap B S hS (yoneda.obj V) c)) := by
  have h := isOpenMap_pointsMap_of_presheafEtale B S hS c hc Set.univ isOpen_univ
  rwa [Set.image_univ] at h

/-- The every-chart condition for the base change of `f` over the open subspace swept out by a
family of étale morphisms to the target, given that condition over each member of the family.

Each member factors through the open subspace, and its factorization is a surjective étale
chart of the open subspace cut out by its point image, so the condition descends by
Stacks 03MJ; the open subspaces so cut out cover, so Zariski locality on the target
assembles them. -/
private theorem holdsOnEveryEtaleChart_pullback_snd_etaleFamily
    (Q : MorphismProperty Scheme.{u}) (hQ : IsEtaleLocalOnSourceAndTarget Q)
    (hQcomp : Q.IsStableUnderComposition) (hQbc : Q.IsStableUnderBaseChange)
    (hQetale : ∀ {Z' W' : Scheme.{u}} (k : Z' ⟶ W'), AlgebraicGeometry.Etale k → Q k)
    (hX : IsAlgebraicSpace B S hS X) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {I : Type u} (A : I → BigFppfOver B S hS) (c : ∀ i, yoneda.obj (A i) ⟶ Y)
    (hcE : ∀ i, (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c i))
    (hQc : ∀ (i : I) (c' : yoneda.obj (A i) ⟶ Y), c' = c i →
      HoldsOnEveryEtaleChart B S hS Q (pullback.snd f c')) :
    HoldsOnEveryEtaleChart B S hS Q
      (pullback.snd f (openSubspaceOfPoints B S hS Y
        (⋃ i, Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i)))).ι) := by
  classical
  have := hQcomp
  have := hQbc
  have hΩi : ∀ i, IsOpen (Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i))) :=
    fun i => isOpen_range_pointsMap_of_presheaf_etale B S hS (c i) (hcE i)
  set W : Subfunctor Y := openSubspaceOfPoints B S hS Y
    (⋃ i, Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i))) with hWdef
  have hWo : IsOpenSubspace B S hS W :=
    isOpenSubspace_openSubspaceOfPoints B S hS hY _ (isOpen_iUnion hΩi)
  have hWr : Set.range (pointsMap B S hS W.toFunctor W.ι) =
      ⋃ i, Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i)) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  set D : I → Subfunctor W.toFunctor := fun i => openSubspaceOfPoints B S hS W.toFunctor
    (pointsMap B S hS W.toFunctor W.ι ⁻¹'
      Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i))) with hDdef
  have hDo : ∀ i, IsOpenSubspace B S hS (D i) := fun i =>
    isOpenSubspace_openSubspaceOfPoints B S hS hWo.1 _
      ((hΩi i).preimage (continuous_pointsMap B S hS W.ι))
  have hDr : ∀ i, Set.range (pointsMap B S hS (D i).toFunctor (D i).ι) =
      pointsMap B S hS W.toFunctor W.ι ⁻¹'
        Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i)) :=
    fun i => range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hOIcomp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition := by
    have : MorphismProperty.IsStableUnderComposition
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    exact MorphismProperty.relative_isStableUnderComposition _
  refine holdsOnEveryEtaleChart_of_openSubspace_cover_target B S hS Q hQ hQcomp hQbc
    hQetale (isAlgebraicSpace_pullback B S hS f W.ι hX hWo.1 hY) hWo.1
    (pullback.snd f W.ι) D hDo (fun w => ?_) (fun i => ?_)
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (show pointsMap B S hS W.toFunctor W.ι w ∈
        ⋃ i, Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i)) from hWr ▸ ⟨w, rfl⟩)
    exact ⟨i, by rwa [hDr i]⟩
  · have hd : IsOpenImmersion B S hS ((D i).ι ≫ W.ι) :=
      MorphismProperty.comp_mem _ _ _ (hDo i).2 hWo.2
    have hdmono : Mono ((D i).ι ≫ W.ι) := mono_of_presheaf_isOpenImmersion hd
    have hdrange : Set.range (pointsMap B S hS (D i).toFunctor ((D i).ι ≫ W.ι)) =
        Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i)) := by
      rw [pointsMap_comp, Set.range_comp, hDr i, Set.image_preimage_eq_inter_range, hWr]
      exact Set.inter_eq_left.mpr (Set.subset_iUnion
        (fun j => Set.range (pointsMap B S hS (yoneda.obj (A j)) (c j))) i)
    obtain ⟨θ, hθ⟩ := (factorsThrough_isOpenImmersion_iff_points B S hS (hDo i).1 hY
      (isAlgebraicSpace_yoneda B S hS (A i)) ((D i).ι ≫ W.ι) hd (c i)).mpr hdrange.ge
    have hθE : IsEtale B S hS θ := by
      refine isEtale_of_comp_mono B S hS θ ((D i).ι ≫ W.ι) ?_
      rw [hθ]
      exact (isEtale_iff_presheaf_of_yoneda B S hS (c i)).mpr (hcE i)
    have hθS : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf θ := by
      refine (surjective_iff_surjective_pointsMap B S hS (D i).toFunctor (hDo i).1
        (A i) θ).mpr (fun z => ?_)
      obtain ⟨tt, htt⟩ : pointsMap B S hS (D i).toFunctor ((D i).ι ≫ W.ι) z ∈
          Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i)) := hdrange ▸ ⟨z, rfl⟩
      refine ⟨tt, pointsMap_injective_of_mono B S hS ((D i).ι ≫ W.ι) ?_⟩
      calc pointsMap B S hS (D i).toFunctor ((D i).ι ≫ W.ι)
            (pointsMap B S hS (yoneda.obj (A i)) θ tt)
          = pointsMap B S hS (yoneda.obj (A i)) (θ ≫ (D i).ι ≫ W.ι) tt := by
            simp only [pointsMap_comp, Function.comp_apply]
        _ = pointsMap B S hS (yoneda.obj (A i)) (c i) tt := by rw [hθ]
        _ = _ := htt
    refine (holdsOnEveryEtaleChart_pullback_snd_comp_iff B S hS Q hQ hQcomp hQetale
      hX hY hWo.1 (hDo i).1 f W.ι (D i).ι).mp ?_
    refine holdsOnEveryEtaleChart_of_etaleChart B S hS Q hQ
      (isAlgebraicSpace_pullback B S hS f ((D i).ι ≫ W.ι) hX (hDo i).1 hY) (hDo i).1
      (pullback.snd f ((D i).ι ≫ W.ι)) hθS
      ((isEtale_iff_presheaf_of_yoneda B S hS θ).mp hθE) ?_
    refine (holdsOnEveryEtaleChart_pullback_snd_comp_iff B S hS Q hQ hQcomp hQetale
      hX hY (hDo i).1 (isAlgebraicSpace_yoneda B S hS (A i)) f ((D i).ι ≫ W.ι) θ).mp ?_
    exact hQc i (θ ≫ (D i).ι ≫ W.ι) hθ

/-- **Stacks 06QS.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` of finite type
with `Y` reduced, and let `F` be an `𝒪_X`-module which is quasi-coherent of finite type on
charts. Then there is a dense open subspace `W` of `Y` such that the base change of `f` over
`W` is flat, locally of finite presentation and quasi-compact, and such that `F` is flat over
`Y` and of finite presentation at every point of `X` lying over `W`. -/
@[stacks 06QS]
theorem exists_dense_open_genericFlatness
    (hX : IsAlgebraicSpace B S hS X) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hYred : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (f : X ⟶ Y) (hf : IsFiniteType B S hS f)
    (F : Modules.{u, u} B S hS X hX)
    (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hft : IsFiniteTypeOnCharts B S hS hX F) :
    ∃ W : Subfunctor Y, IsDenseOpenSubspace B S hS hY W ∧
      IsFlat B S hS (pullback.snd f W.ι) ∧
      IsLocallyOfFinitePresentation B S hS (pullback.snd f W.ι) ∧
      IsQuasiCompact B S hS (pullback.snd f W.ι) ∧
      ∀ x : points B S hS X,
        pointsMap B S hS X f x ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) →
          x ∈ flatLocus B S hS hX f F ∧
            x ∈ finitePresentationLocus B S hS hX F := by
  classical
  obtain ⟨V₀, q, hqS, hqE, hV₀red⟩ := hYred
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj V₀) := hV₀red
  obtain ⟨I, A, c, hcE, hcmor, hcdense, hcpt⟩ :=
    exists_etaleCover_genericFlatness B S hS hX hY f hf F hqc hft V₀ q hqS hqE
  have hΩi : ∀ i, IsOpen (Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i))) :=
    fun i => isOpen_range_pointsMap_of_presheaf_etale B S hS (c i) (hcE i)
  refine ⟨openSubspaceOfPoints B S hS Y
      (⋃ i, Set.range (pointsMap B S hS (yoneda.obj (A i)) (c i))),
    ⟨isOpenSubspace_openSubspaceOfPoints B S hS hY _ (isOpen_iUnion hΩi), ?_⟩, ?_, ?_,
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback f _) hf.2, ?_⟩
  · rw [range_pointsMap_ι_openSubspaceOfPoints]
    exact hcdense
  · exact holdsOnEveryEtaleChart_pullback_snd_etaleFamily B S hS
      (@AlgebraicGeometry.Flat.{u}) AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget
      inferInstance inferInstance (fun _ hk => have := hk; inferInstance) hX hY f A c hcE
      (fun i c' hc' => (hcmor i c' hc').1)
  · exact holdsOnEveryEtaleChart_pullback_snd_etaleFamily B S hS
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u})
      AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
      inferInstance inferInstance (fun _ hk => have := hk; inferInstance) hX hY f A c hcE
      (fun i c' hc' => (hcmor i c' hc').2)
  · intro x hx
    rw [range_pointsMap_ι_openSubspaceOfPoints] at hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hcpt i x hi

/-- **Stacks 06QS for a reduced scheme base**, step 2 of the source. This is the general
statement for a base which is represented by an object of the site, where the identity may be
taken as the surjective étale chart witnessing reducedness. -/
@[stacks 06QS "step 2 of the proof: the case of a reduced scheme base"]
theorem exists_dense_open_genericFlatness_of_isScheme
    (hX : IsAlgebraicSpace B S hS X) (Z : BigFppfOver B S hS)
    [IsReduced ((BigFppfOver.toScheme B S hS).obj Z)]
    (f : X ⟶ yoneda.obj Z) (hf : IsFiniteType B S hS f)
    (F : Modules.{u, u} B S hS X hX)
    (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hft : IsFiniteTypeOnCharts B S hS hX F) :
    ∃ W : Subfunctor (yoneda.obj Z),
      IsDenseOpenSubspace B S hS (isAlgebraicSpace_yoneda B S hS Z) W ∧
      IsFlat B S hS (pullback.snd f W.ι) ∧
      IsLocallyOfFinitePresentation B S hS (pullback.snd f W.ι) ∧
      IsQuasiCompact B S hS (pullback.snd f W.ι) ∧
      ∀ x : points B S hS X,
        pointsMap B S hS X f x ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) →
          x ∈ flatLocus B S hS hX f F ∧
            x ∈ finitePresentationLocus B S hS hX F :=
  exists_dense_open_genericFlatness B S hS hX (isAlgebraicSpace_yoneda B S hS Z)
    (hasEtaleLocalProperty_of_representable B S hS (yoneda.obj Z)
      (fun T : Scheme.{u} => IsReduced T) Z (Iso.refl _) inferInstance) f hf F
    hqc hft

end AlgebraicGeometry.Space

end
