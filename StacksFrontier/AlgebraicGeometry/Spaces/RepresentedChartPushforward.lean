module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePushforwardRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedPushforwardQuasicoherent

/-!
# The chart restriction of a direct image of represented algebraic spaces

Let `B` be a big fppf site containing a scheme `S` and let `g : T' ⟶ T` be a morphism of the big
fppf category over `S`.  The direct image of Stacks 03LU along the morphism of representable
algebraic spaces `g` represents, restricted to the Zariski site of `T` along the identity chart,
is the scheme-level direct image of the restriction:

`(φ_*F)|_T = r_*(F|_{T'})`,

where `r` is the morphism of schemes underlying `g`.  This is the identification that the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Divisors/MorphismWeaklyAssociated/SpaceFiniteDirectImage.lean`
name as one of the two inputs the affine case of Stacks 0CU9 needs, and the one that is formal.

## Main definitions

* `AlgebraicGeometry.Space.restrictToChartSchemePushforwardIdEtaleChartIso`: the identification,
  for a module presented as the reading of a module on the small étale site of the scheme.
* `AlgebraicGeometry.Space.restrictToChartSchemePushforwardIdEtaleChartIso'`: the same for an
  arbitrary `𝒪`-module on the source.

## Implementation notes

Three library identifications compose, with no new geometry:

* `AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso` reads the restriction along the
  identity chart as `AlgebraicGeometry.SmallEtale.restrictModule` of the module's avatar on the
  small étale site of the scheme;
* `AlgebraicGeometry.Space.representedModulePushforwardObjIso` identifies the direct image of
  Stacks 03LU along a morphism of represented spaces with the small étale direct image of the
  underlying morphism of schemes;
* `AlgebraicGeometry.SmallEtale.restrictModulePushforwardObjIso` carries that small étale direct
  image past the restriction to the small Zariski site.

The unit and counit of `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` move
between a module and its avatar; both are isomorphisms, which is what makes the second form
follow from the first.

**This is not the whole of the affine case of Stacks 0CU9.**  That case also needs the direct
image to be quasi-coherent *on the site*, and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_representedSpaceMap_iff` shows
that this is exactly the statement that the direct image on the small étale site of a scheme
along an affine morphism preserves quasi-coherence — Stacks 02KG (1) read on the small étale
site, which no declaration here states, though both of its ingredients are proved; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedPushforwardQuasicoherent.lean`.  What the
square above gives on the quasi-coherence question is only the Zariski half,
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule_pushforward`, and restriction to
the small Zariski site does not reflect quasi-coherence.

No `@[stacks]` attribute is carried: each component is already registered where it belongs, and
the composite is not a covering set for a tag of its own.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 0CU9](https://stacks.math.columbia.edu/tag/0CU9)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- **The chart restriction of the direct image along a morphism of represented algebraic spaces
is the scheme-level direct image of the chart restriction.**  Restricting along the identity
chart, the direct image of Stacks 03LU along the morphism represented by `g` becomes
`AlgebraicGeometry.Scheme.Modules.pushforward` of the morphism of schemes underlying `g`. -/
noncomputable def restrictToChartSchemePushforwardIdEtaleChartIso
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T')) :
    restrictToChartScheme B S hS (yoneda.obj T)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
        ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj
          (representedSmallEtaleModule B S hS T' M)) (idEtaleChart B S hS T) ≅
      (Scheme.Modules.pushforward
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).obj
        (restrictToChartScheme B S hS (yoneda.obj T')
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T')
          (representedSmallEtaleModule B S hS T' M) (idEtaleChart B S hS T')) :=
  restrictToChartSchemeIdEtaleChartIso B S hS T _ ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso
          (representedModulePushforwardObjIso B S hS g M).symm ≪≫
        ((representedSmallEtaleModuleEquivalence B S hS T).unitIso.app
          ((SheafOfModules.pushforward.{u}
            (representedSchemeStructureMapRing B S hS g)).obj M)).symm) ≪≫
    _root_.AlgebraicGeometry.SmallEtale.restrictModulePushforwardObjIso
      (associatedBigEtaleSite B) g.left M ≪≫
    (Scheme.Modules.pushforward
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).mapIso
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).mapIso
          ((representedSmallEtaleModuleEquivalence B S hS T').unitIso.app M) ≪≫
        (restrictToChartSchemeIdEtaleChartIso B S hS T'
          (representedSmallEtaleModule B S hS T' M)).symm)

/-- **The chart restriction of the direct image along a morphism of represented algebraic spaces
is the scheme-level direct image of the chart restriction**, for an arbitrary `𝒪`-module on the
source.

The module is replaced by the reading of its avatar on the small étale site of the scheme
through the counit of `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, which is
an isomorphism. -/
noncomputable def restrictToChartSchemePushforwardIdEtaleChartIso'
    (F : Modules.{u, u} B S hS (yoneda.obj T')
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T')) :
    restrictToChartScheme B S hS (yoneda.obj T)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
        ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj F)
        (idEtaleChart B S hS T) ≅
      (Scheme.Modules.pushforward
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).obj
        (restrictToChartScheme B S hS (yoneda.obj T')
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T') F (idEtaleChart B S hS T')) :=
  let e : representedSmallEtaleModule B S hS T'
      ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj F) ≅ F :=
    (representedSmallEtaleModuleEquivalence B S hS T').counitIso.app F
  (restrictToChartSchemeFunctor B S hS (yoneda.obj T)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) (idEtaleChart B S hS T)).mapIso
      ((modulePushforward B S hS (representedSpaceMap B S hS g)).mapIso e).symm ≪≫
    restrictToChartSchemePushforwardIdEtaleChartIso B S hS g
      ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj F) ≪≫
    (Scheme.Modules.pushforward
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).mapIso
      ((restrictToChartSchemeFunctor B S hS (yoneda.obj T')
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T')
        (idEtaleChart B S hS T')).mapIso e)

end AlgebraicGeometry.Space

end
