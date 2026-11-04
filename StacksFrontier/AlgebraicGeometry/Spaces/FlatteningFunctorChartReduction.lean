module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleEtaleChartTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFunctor

/-!
# The flattening condition of Stacks 0CWX read on one étale scheme chart

In Situation 0CWX — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` of a big fppf
site together with a quasi-coherent `𝒪_X`-module `F` — the condition tested by the functor
`F_flat` of equation 0CWY at a test scheme `T` over `Y` is flatness of the base change `F_T`
over `T`, `AlgebraicGeometry.Space.FlatnessSituation.IsFlatAfterBaseChange`.  That condition is
the chartwise one of Stacks 05VV, quantified over *every* commuting square of étale scheme
charts of `X_T ⟶ T`.  This file reads it on a *single* square instead, and transports that
reading along a morphism of test schemes.

The target of the morphism being tested is the represented algebraic space of `T`, so the target
chart of a square may be taken to be the identity chart of `T`, and a square is then just a
surjective étale chart `U ⟶ X_T` of the source together with the induced morphism `U ⟶ T` of
objects of the site; that package is
`AlgebraicGeometry.Space.FlatnessSituation.TestChart`.  Along a morphism `T' ⟶ T` of test
schemes a test chart base changes to one of `X_{T'}`, with chart object the fibre product
`U ×_T T'` taken in the site, and the chart restriction of `F_{T'}` to it is the Zariski inverse
image of the chart restriction of `F_T` to `U`.

## Main definitions

* `AlgebraicGeometry.Space.FlatnessSituation.TestChart`: a surjective étale scheme chart of
  `X_T` lying over the test scheme `T`.
* `AlgebraicGeometry.Space.FlatnessSituation.TestChart.baseChange`: its base change along a
  morphism of test schemes.

## Main results

* `AlgebraicGeometry.Space.FlatnessSituation.isFlatAfterBaseChange_iff_isFlatOverOnChartDiagram`
  and `AlgebraicGeometry.Space.FlatnessSituation.TestChart.isFlatAfterBaseChange_iff`: **the
  flattening condition at a test scheme is flatness of the chart restriction on one surjective
  étale scheme chart**, in the ringed-space sense of Stacks 08KT.
* `AlgebraicGeometry.Space.FlatnessSituation.TestChart.isPullback_bcChart`: the base-changed
  chart is the base change of the chart along `X_{T'} ⟶ X_T`.
* `AlgebraicGeometry.Space.FlatnessSituation.TestChart.restrictToChartBaseChange`: **the chart
  restriction of `F_{T'}` to the base-changed chart is the Zariski inverse image of the chart
  restriction of `F_T`.**
* `AlgebraicGeometry.isFlatOver_pullbackIso_iff` and
  `AlgebraicGeometry.isFlatOver_pullbackIso_iff'`: flatness over a common target is invariant
  under pulling a module back along an isomorphism of the sources.
* `AlgebraicGeometry.Space.FlatnessSituation.TestChart.isFlatAfterBaseChange_baseChange_iff`:
  **the flattening condition at a base-changed test scheme, in the shape Stacks 05LY tests** —
  flatness over the second projection of the fibre product of the chart scheme with the test
  scheme *taken in schemes*, of the Zariski inverse image of the chart restriction along the
  first projection.

## Implementation notes

The chart diagram of a test chart is
`AlgebraicGeometry.Space.etaleChartDiagramOfFactorization` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleEtaleChartTransport.lean`, which is exactly the
square with the identity chart of the represented target.  That one square suffices because
`F_T` is quasi-coherent — Stacks 03GA along the projection `X_T ⟶ X`,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` — so
`AlgebraicGeometry.Space.isFlatOver_of_isFlatOverOnChartDiagram_of_surjective` together with
`AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtGeometricPoint`, both Stacks 05VU
read through Stacks 05VV, turn the condition on the one square into the condition on all of
them.  Surjectivity of the chart is carried as `AlgebraicGeometry.Space.IsSurjective` and
converted to surjectivity of the map of point sets by Stacks 03H5.

The base-changed chart is produced by the universal property of the cartesian square
`AlgebraicGeometry.Space.isPullback_baseChangeMap` read in presheaves, through
`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`; that it is again étale and surjective is
base-change stability of the relatively representable properties,
`CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange`, which is why
`AlgebraicGeometry.Space.FlatnessSituation.TestChart.isPullback_bcChart` is proved first.  The
fibre product of the chart object with the test scheme is taken in the site, which has
pullbacks by `AlgebraicGeometry.hasPullbacks_bigFppfOver`.

The comparison of the chart restrictions is
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChange.lean`, the compatibility of
Stacks 03M0 with Stacks 03LW for a quasi-coherent module, applied to the comparison morphism
`X_{T'} ⟶ X_T` on the square joining the two charts, followed by the identification of `F_{T'}`
with the pullback of `F_T` by the composition comparison
`AlgebraicGeometry.Space.modulePullbackTriangle` of Stacks 03LU.  That comparison assumes no
square cartesian; the square here happens to be, but only its commutation
`AlgebraicGeometry.Space.FlatnessSituation.TestChart.bcChart_comp_map` is used.

The two flatness-transport lemmas are stated for schemes and are the plumbing between this
reading and the scheme-level descent statement of Stacks 05LY,
`AlgebraicGeometry.eventually_isFlatOver_modulePullback` of
`StacksFrontier/AlgebraicGeometry/Limits/RelativeApproximation/FlatDescent.lean`: that statement
tests flatness over the second projection of a fibre product *of schemes*, whereas the chart
restriction above lives on the scheme of the fibre product *of the site*, and the two differ by
the comparison isomorphism of the pullback-preserving functor
`AlgebraicGeometry.BigFppfOver.toScheme` —
`AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme` of
`StacksFrontier/AlgebraicGeometry/Topologies/Fppf/FibreProducts.lean`.  The two readings are
identified across that isomorphism by
`AlgebraicGeometry.Space.FlatnessSituation.TestChart.isFlatAfterBaseChange_baseChange_iff`.

That identification is assembled in three steps, none of which asks the unifier to see through
the fibre product of the site: the comparison isomorphism is *named* as
`AlgebraicGeometry.Space.FlatnessSituation.TestChart.bcSchemeIso` rather than inferred; the
transport of the module along it is
`AlgebraicGeometry.Space.FlatnessSituation.TestChart.bcPullbackCompIso`, which composes the
comparison of a composite inverse image with a rewrite along
`CategoryTheory.Limits.PreservesPullback.iso_hom_fst`; and quasi-coherence of the module
Stacks 05LY tests is `isQuasicoherent_bcPullbackModule`, stated separately because instance
search for it has to be handed the structure ring of the chart scheme in the spelling
`structureSheafRing _.toRingedSpace` — handed `Scheme.ringCatSheaf` instead, the local
instance does not match the goal and the search diverges.

## References

* [Stacks Project, Tag 0CWX](https://stacks.math.columbia.edu/tag/0CWX)
* [Stacks Project, Tag 0CWZ](https://stacks.math.columbia.edu/tag/0CWZ)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The inverse image of a sheaf of modules along an isomorphism of schemes over a common
target is flat over that target exactly when the module is. -/
theorem isFlatOver_pullbackIso_iff {A A' Z : Scheme.{u}} (ε : A ≅ A') (s : A' ⟶ Z)
    (N : SheafOfModules.{u} (structureSheafRing A'.toRingedSpace))
    (hN : N.IsQuasicoherent) :
    AlgebraicGeometry.IsFlatOver (ε.hom ≫ s).toLRSHom.toShHom
        ((RingedSpaceModuleAdjunction.modulePullback ε.hom.toLRSHom.toShHom).obj N) ↔
      AlgebraicGeometry.IsFlatOver s.toLRSHom.toShHom N := by
  have := hN
  have : ((RingedSpaceModuleAdjunction.modulePullback
      ε.hom.toLRSHom.toShHom).obj N).IsQuasicoherent :=
    SheafOfModules.modulePullback_isQuasicoherent ε.hom.toLRSHom.toShHom N
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine isFlatOver_of_moduleIso s.toLRSHom.toShHom ?_
      (modulePullback_isFlatOver (f := ε.hom ≫ s) (g := 𝟙 Z) (g' := ε.inv) (f' := s)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) _ h)
    exact (schemeModulePullbackCompIso ε.inv ε.hom).app N ≪≫
      (Scheme.Modules.pullbackCongr ε.inv_hom_id).app N ≪≫
      (Scheme.Modules.pullbackId A').app N
  · exact modulePullback_isFlatOver (f := s) (g := 𝟙 Z) (g' := ε.hom) (f' := ε.hom ≫ s)
      (IsPullback.of_horiz_isIso ⟨by simp⟩) N h

/-- `isFlatOver_pullbackIso_iff` with the structure morphism of the source presented through the
isomorphism. -/
theorem isFlatOver_pullbackIso_iff' {A A' Z : Scheme.{u}} (ε : A ≅ A') (s : A ⟶ Z) (s' : A' ⟶ Z)
    (hs : ε.hom ≫ s' = s)
    (N : SheafOfModules.{u} (structureSheafRing A'.toRingedSpace))
    (hN : N.IsQuasicoherent) :
    AlgebraicGeometry.IsFlatOver s.toLRSHom.toShHom
        ((RingedSpaceModuleAdjunction.modulePullback ε.hom.toLRSHom.toShHom).obj N) ↔
      AlgebraicGeometry.IsFlatOver s'.toLRSHom.toShHom N := by
  subst hs
  exact isFlatOver_pullbackIso_iff ε s' N hN

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

namespace FlatnessSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The module `F_T` is quasi-coherent on the site. -/
private theorem isQuasicoherentOnSite_baseChangeModule (D : FlatnessSituation.{u} B S hS)
    (T : SchemesOver D.Y) : (D.baseChangeModule T).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (baseChangeProjection D.f T) D.F D.quasicoherent

/-- Flatness of `F_T` over a test scheme `T`, read on one surjective étale scheme chart. -/
theorem isFlatAfterBaseChange_iff_isFlatOverOnChartDiagram
    (D : FlatnessSituation.{u} B S hS) (T : SchemesOver D.Y)
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ (baseChangeSpace D.f T).1)
    (ha : IsEtale B S hS a)
    (hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a))
    (α : U ⟶ T.left) (hcomm : a ≫ (baseChangeInclusion D.f T).hom = yoneda.map α) :
    D.IsFlatAfterBaseChange T ↔
      IsFlatOverOnChartDiagram B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
        (etaleChartDiagramOfFactorization B S hS (baseChangeInclusion D.f T) a ha α hcomm) := by
  have := isQuasicoherentOnSite_baseChangeModule D T
  refine ⟨fun h => h _, fun h => ?_⟩
  exact (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS
    (baseChangeInclusion D.f T) (D.baseChangeModule T)).mpr
    (isFlatOver_of_isFlatOverOnChartDiagram_of_surjective B S hS
      (baseChangeInclusion D.f T) (D.baseChangeModule T) _ hsurj h)

/-- A surjective étale scheme chart of `X_T` lying over the test scheme `T`. -/
structure TestChart (D : FlatnessSituation.{u} B S hS) (T : SchemesOver D.Y) where
  /-- The object of the site charting `X_T`. -/
  obj : BigFppfOver B S hS
  /-- The chart. -/
  chart : yoneda.obj obj ⟶ (baseChangeSpace D.f T).1
  /-- The induced morphism of schemes to the test scheme. -/
  down : obj ⟶ T.left
  /-- The chart is étale. -/
  etale : IsEtale B S hS chart
  /-- The chart is surjective. -/
  surjective : IsSurjective B S hS chart
  /-- The chart lies over the test scheme. -/
  comm : chart ≫ (baseChangeInclusion D.f T).hom = yoneda.map down

namespace TestChart

variable {D : FlatnessSituation.{u} B S hS} {T : SchemesOver D.Y}

/-- The chart diagram of a test chart: the chart on the source, the identity chart of the test
scheme on the target. -/
def chartDiagram (C : TestChart D T) :
    ChartDiagram B S hS (baseChangeSpace D.f T).1
      ((schemeSpaceFunctor B S hS).obj T.left).1 (baseChangeInclusion D.f T).hom :=
  etaleChartDiagramOfFactorization B S hS (baseChangeInclusion D.f T) C.chart C.etale C.down
    C.comm

/-- The chart of a test chart is surjective in the sense of presheaves. -/
private theorem presheafSurjective_chart (C : TestChart D T) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf C.chart :=
  (presheafSurjective_iff_isSurjective_yoneda B S hS _ (baseChangeSpace D.f T).2 C.obj
    C.chart).mpr C.surjective

/-- Flatness of `F_T` over the test scheme `T` is flatness of `F_T` on the chart diagram of a
test chart. -/
theorem isFlatAfterBaseChange_iff (C : TestChart D T) :
    D.IsFlatAfterBaseChange T ↔
      IsFlatOverOnChartDiagram B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
        C.chartDiagram :=
  D.isFlatAfterBaseChange_iff_isFlatOverOnChartDiagram T C.chart C.etale
    ((surjective_iff_surjective_pointsMap B S hS _ (baseChangeSpace D.f T).2 C.obj
      C.chart).mp C.presheafSurjective_chart)
    C.down C.comm

/-- Flatness of `F_T` over the test scheme `T`, read as scheme-level flatness of the chart
restriction over the chart's structure morphism. -/
theorem isFlatAfterBaseChange_iff_isFlatOver (C : TestChart D T) :
    D.IsFlatAfterBaseChange T ↔
      AlgebraicGeometry.IsFlatOver
        ((BigFppfOver.toScheme B S hS).map C.down).toLRSHom.toShHom
        (restrictToChart B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
          (etaleChartOfIsEtale B S hS C.chart C.etale)) :=
  C.isFlatAfterBaseChange_iff

section BaseChange

variable {T' : SchemesOver D.Y}

/-- The site `BigFppfOver B S hS` has pullbacks. -/
instance : HasPullbacks (BigFppfOver B S hS) := inferInstance

/-- The chart of `X_{T'}` obtained by base changing a test chart of `X_T` along a morphism
`T' ⟶ T` of test schemes. -/
def bcChart (C : TestChart D T) (g : T' ⟶ T) :
    yoneda.obj (pullback C.down g.left) ⟶ (baseChangeSpace D.f T').1 :=
  (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f g)).lift
    (yoneda.map (pullback.fst C.down g.left) ≫ C.chart)
    (yoneda.map (pullback.snd C.down g.left))
    (by
      rw [Category.assoc, C.comm]
      change yoneda.map (pullback.fst C.down g.left) ≫ yoneda.map C.down =
        yoneda.map (pullback.snd C.down g.left) ≫ yoneda.map g.left
      rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition])

/-- The base-changed chart lies over `T'` through the second projection. -/
@[reassoc]
theorem bcChart_comp_inclusion (C : TestChart D T) (g : T' ⟶ T) :
    C.bcChart g ≫ (baseChangeInclusion D.f T').hom =
      yoneda.map (pullback.snd C.down g.left) :=
  (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f g)).lift_snd _ _ _

/-- The base-changed chart followed by `X_{T'} ⟶ X_T` is the first projection followed by the
chart. -/
@[reassoc]
theorem bcChart_comp_map (C : TestChart D T) (g : T' ⟶ T) :
    C.bcChart g ≫ (baseChangeMap D.f g).hom =
      yoneda.map (pullback.fst C.down g.left) ≫ C.chart :=
  (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f g)).lift_fst _ _ _

/-- The base-changed chart is the base change of the chart along `X_{T'} ⟶ X_T`. -/
theorem isPullback_bcChart (C : TestChart D T) (g : T' ⟶ T) :
    IsPullback (yoneda.map (pullback.fst C.down g.left)) (C.bcChart g) C.chart
      (baseChangeMap D.f g).hom := by
  have h : IsPullback (yoneda.map (pullback.snd C.down g.left))
      (yoneda.map (pullback.fst C.down g.left)) (yoneda.map g.left) (yoneda.map C.down) :=
    ((IsPullback.of_hasPullback C.down g.left).flip).map yoneda
  rw [← C.bcChart_comp_inclusion g, ← C.comm] at h
  exact (IsPullback.of_right h (C.bcChart_comp_map g)
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f g)).flip).flip

/-- The base-changed chart is étale. -/
theorem bcChart_etale (C : TestChart D T) (g : T' ⟶ T) : IsEtale B S hS (C.bcChart g) := by
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact (isEtale_iff_presheaf_of_yoneda B S hS _).mpr
    (MorphismProperty.of_isPullback (C.isPullback_bcChart g)
      ((isEtale_iff_presheaf_of_yoneda B S hS C.chart).mp C.etale))

/-- The base-changed chart is surjective. -/
theorem bcChart_surjective (C : TestChart D T) (g : T' ⟶ T) :
    IsSurjective B S hS (C.bcChart g) := by
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact (presheafSurjective_iff_isSurjective_yoneda B S hS _ (baseChangeSpace D.f T').2 _
    _).mp (MorphismProperty.of_isPullback (C.isPullback_bcChart g)
      C.presheafSurjective_chart)

/-- The base change of a test chart along a morphism of test schemes. -/
def baseChange (C : TestChart D T) (g : T' ⟶ T) : TestChart D T' where
  obj := pullback C.down g.left
  chart := C.bcChart g
  down := pullback.snd C.down g.left
  etale := C.bcChart_etale g
  surjective := C.bcChart_surjective g
  comm := C.bcChart_comp_inclusion g

/-- The chart restriction of `F_{T'}` to the base-changed chart is the Zariski inverse image of
the chart restriction of `F_T`. -/
def restrictToChartBaseChange (C : TestChart D T) (g : T' ⟶ T) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
        (pullback.fst C.down g.left))).obj
        (restrictToChart B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
          (etaleChartOfIsEtale B S hS C.chart C.etale)) ≅
      restrictToChart B S hS (baseChangeSpace D.f T').2 (D.baseChangeModule T')
        (etaleChartOfIsEtale B S hS (C.bcChart g) (C.bcChart_etale g)) :=
  restrictToChartBaseChangeIso B S hS (baseChangeMap D.f g) (D.baseChangeModule T)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (baseChangeProjection D.f T) D.F D.quasicoherent)
      (etaleChartOfIsEtale B S hS C.chart C.etale)
      (etaleChartOfIsEtale B S hS (C.bcChart g) (C.bcChart_etale g))
      (pullback.fst C.down g.left) (C.bcChart_comp_map g).symm ≪≫
    restrictToChartIso B S hS (baseChangeSpace D.f T').2
      ((modulePullbackTriangle B S hS (baseChangeMap_comp_projection D.f g)).app D.F).symm _

/-- The chart restriction of `F_T` to a test chart is quasi-coherent. -/
theorem isQuasicoherent_restrictToChartModule (C : TestChart D T) :
    SheafOfModules.IsQuasicoherent
      (restrictToChart B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
        (etaleChartOfIsEtale B S hS C.chart C.etale)) :=
  isQuasicoherent_restrictToChart B S hS (baseChangeSpace D.f T) (D.baseChangeModule T)
    (isQuasicoherentOnSite_baseChangeModule D T) _

/-- Flatness of `F_{T'}` over a base-changed test scheme, read on the base-changed chart. -/
theorem isFlatAfterBaseChange_bcChart_iff (C : TestChart D T) (g : T' ⟶ T) :
    D.IsFlatAfterBaseChange T' ↔
      AlgebraicGeometry.IsFlatOver
        ((BigFppfOver.toScheme B S hS).map (pullback.snd C.down g.left)).toLRSHom.toShHom
        (restrictToChart B S hS (baseChangeSpace D.f T').2 (D.baseChangeModule T')
          (etaleChartOfIsEtale B S hS (C.bcChart g) (C.bcChart_etale g))) :=
  (C.baseChange g).isFlatAfterBaseChange_iff

/-! #### Passing to the fibre product formed in schemes

The chart object of the base-changed chart is the fibre product taken in the site, whereas the
scheme-level statement of Stacks 05LY tests flatness over the second projection of the fibre
product taken in schemes.  The two are identified by the comparison isomorphism of the
pullback-preserving functor to schemes. -/

/-- The comparison isomorphism between the scheme of the fibre product of a test chart with a
test scheme, formed in the site, and the fibre product of their schemes, formed in schemes. -/
def bcSchemeIso (C : TestChart D T) (g : T' ⟶ T) :
    (BigFppfOver.toScheme B S hS).obj (pullback C.down g.left) ≅
      pullback ((BigFppfOver.toScheme B S hS).map C.down)
        ((BigFppfOver.toScheme B S hS).map g.left) :=
  PreservesPullback.iso (BigFppfOver.toScheme B S hS) C.down g.left

/-- The comparison isomorphism `bcSchemeIso` commutes with the first projections. -/
@[reassoc]
theorem bcSchemeIso_hom_fst (C : TestChart D T) (g : T' ⟶ T) :
    (C.bcSchemeIso g).hom ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map C.down)
        ((BigFppfOver.toScheme B S hS).map g.left) =
      (BigFppfOver.toScheme B S hS).map (pullback.fst C.down g.left) :=
  PreservesPullback.iso_hom_fst _ _ _

/-- The comparison isomorphism `bcSchemeIso` commutes with the second projections. -/
@[reassoc]
theorem bcSchemeIso_hom_snd (C : TestChart D T) (g : T' ⟶ T) :
    (C.bcSchemeIso g).hom ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map C.down)
        ((BigFppfOver.toScheme B S hS).map g.left) =
      (BigFppfOver.toScheme B S hS).map (pullback.snd C.down g.left) :=
  PreservesPullback.iso_hom_snd _ _ _

/-- Pulling the chart restriction back to the fibre product formed in schemes and then along
the comparison isomorphism is pulling it back along the first projection of the fibre product
formed in the site. -/
def bcPullbackCompIso (C : TestChart D T) (g : T' ⟶ T) :
    (Scheme.Modules.pullback (C.bcSchemeIso g).hom).obj
        ((Scheme.Modules.pullback (pullback.fst
            ((BigFppfOver.toScheme B S hS).map C.down)
            ((BigFppfOver.toScheme B S hS).map g.left))).obj
          (restrictToChart B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
            (etaleChartOfIsEtale B S hS C.chart C.etale))) ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
          (pullback.fst C.down g.left))).obj
        (restrictToChart B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
          (etaleChartOfIsEtale B S hS C.chart C.etale)) := by
  refine (schemeModulePullbackCompIso (C.bcSchemeIso g).hom
    (pullback.fst ((BigFppfOver.toScheme B S hS).map C.down)
      ((BigFppfOver.toScheme B S hS).map g.left))).app _ ≪≫ ?_
  rw [C.bcSchemeIso_hom_fst g]
  exact Iso.refl _

/-- The chart restriction of `F_{T'}` to the base-changed chart is the Zariski inverse image,
along the comparison isomorphism and the first projection of the fibre product formed in
schemes, of the chart restriction of `F_T`. -/
def bcModuleIso (C : TestChart D T) (g : T' ⟶ T) :
    (Scheme.Modules.pullback (C.bcSchemeIso g).hom).obj
        ((Scheme.Modules.pullback (pullback.fst
            ((BigFppfOver.toScheme B S hS).map C.down)
            ((BigFppfOver.toScheme B S hS).map g.left))).obj
          (restrictToChart B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
            (etaleChartOfIsEtale B S hS C.chart C.etale))) ≅
      restrictToChart B S hS (baseChangeSpace D.f T').2 (D.baseChangeModule T')
        (etaleChartOfIsEtale B S hS (C.bcChart g) (C.bcChart_etale g)) :=
  C.bcPullbackCompIso g ≪≫ C.restrictToChartBaseChange g

/-- The Zariski inverse image of the chart restriction of `F_T` to the fibre product formed in
schemes is quasi-coherent. -/
theorem isQuasicoherent_bcPullbackModule (C : TestChart D T) (g : T' ⟶ T) :
    SheafOfModules.IsQuasicoherent
      ((Scheme.Modules.pullback (pullback.fst
          ((BigFppfOver.toScheme B S hS).map C.down)
          ((BigFppfOver.toScheme B S hS).map g.left))).obj
        (restrictToChart B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
          (etaleChartOfIsEtale B S hS C.chart C.etale))) := by
  have : SheafOfModules.IsQuasicoherent
      (R := _root_.structureSheafRing
        ((BigFppfOver.toScheme B S hS).obj C.obj).toRingedSpace)
      (restrictToChart B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
        (etaleChartOfIsEtale B S hS C.chart C.etale)) :=
    C.isQuasicoherent_restrictToChartModule
  exact SheafOfModules.modulePullback_isQuasicoherent
    (pullback.fst ((BigFppfOver.toScheme B S hS).map C.down)
      ((BigFppfOver.toScheme B S hS).map g.left)).toLRSHom.toShHom
    (restrictToChart B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
      (etaleChartOfIsEtale B S hS C.chart C.etale))

/-- **The flattening condition at a base-changed test scheme, in the shape Stacks 05LY tests.**
Flatness of `F_{T'}` over `T'` is flatness, over the second projection of the fibre product of
the chart scheme with `T'` *taken in schemes*, of the Zariski inverse image of the chart
restriction of `F_T` along the first projection.

This is `isFlatAfterBaseChange_bcChart_iff` carried across the comparison isomorphism
`bcSchemeIso` of the two fibre products, along which flatness is invariant by
`AlgebraicGeometry.isFlatOver_pullbackIso_iff'`. -/
theorem isFlatAfterBaseChange_baseChange_iff (C : TestChart D T) (g : T' ⟶ T) :
    D.IsFlatAfterBaseChange T' ↔
      AlgebraicGeometry.IsFlatOver
        (pullback.snd ((BigFppfOver.toScheme B S hS).map C.down)
          ((BigFppfOver.toScheme B S hS).map g.left)).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst
            ((BigFppfOver.toScheme B S hS).map C.down)
            ((BigFppfOver.toScheme B S hS).map g.left))).obj
          (restrictToChart B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
            (etaleChartOfIsEtale B S hS C.chart C.etale))) :=
  (C.isFlatAfterBaseChange_bcChart_iff g).trans
    (((AlgebraicGeometry.isFlatOver_iff_of_moduleIso _ (C.bcModuleIso g)).symm).trans
      (AlgebraicGeometry.isFlatOver_pullbackIso_iff' (C.bcSchemeIso g) _ _
        (C.bcSchemeIso_hom_snd g) _ (C.isQuasicoherent_bcPullbackModule g)))

end BaseChange

end TestChart

end FlatnessSituation

end AlgebraicGeometry.Space

end
