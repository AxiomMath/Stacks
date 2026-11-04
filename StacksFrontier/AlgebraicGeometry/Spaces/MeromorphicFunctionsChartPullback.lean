module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.StructureSheafLocalizationPushforward
import StacksCore.Tactic.StacksAttribute

/-!
# The chartwise pullback of meromorphic functions on the sheaves

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` for which pullbacks of
meromorphic functions are defined (Stacks 0EN8).  Over a commuting square of étale charts `U` of
`X` above `V` of `Y` this file builds a homomorphism of commutative rings

`𝒦_Y(V) ⟶ 𝒦_X(U)`

on the sections of the *sheaves* of meromorphic functions, and shows that the chartwise
homomorphisms form an `f`-map of Stacks 03G3.

The comparison `𝒦_Y ⟶ f_*𝒦_X` of
`AlgebraicGeometry.Space.meromorphicFunctionSheafComparison` is defined for an arbitrary `f`;
this file reads it chartwise.  Its target is the direct image of
Stacks 03G8, whose sections over a chart `V` of `Y` are a limit over the étale scheme charts of
`X` above `X ×_Y V`, so the comparison projects to each such chart, and the chart diagrams over
`V` are exactly those charts by `AlgebraicGeometry.Space.indexOfChartDiagram`.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicDirectImageRan` is `f_*𝒦_X` with the direct image in its
  right Kan extension form, and `AlgebraicGeometry.Space.meromorphicComparisonRan` the
  comparison into it.
* `AlgebraicGeometry.Space.meromorphicChartProjection` is a chart projection of that direct
  image, as a homomorphism of commutative rings.
* `AlgebraicGeometry.Space.chartMeromorphicFunctionPullback` is the chartwise homomorphism
  `𝒦_Y(V) ⟶ 𝒦_X(U)`, and `AlgebraicGeometry.Space.fmapMeromorphicFunctionSheaf` the `f`-map
  they form.

## Main results

* `AlgebraicGeometry.Space.chartMeromorphicFunctionPullback_comp` is the compatibility with
  simultaneous étale restriction of the two charts of a diagram.
* `AlgebraicGeometry.Space.chartMeromorphicFunctionPullback_toSheafify` identifies the chartwise
  homomorphism on a fraction with the fraction rule `a/b ↦ f^♯a/f^♯b` of
  `AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions`, and
  `AlgebraicGeometry.Space.chartMeromorphicFunctionPullback_toMeromorphicFunctionSheaf` is the
  resulting compatibility with `𝒪 ⟶ 𝒦`.

## Implementation notes

The direct image is taken in the Kan-extension form `smallEtaleDirectImageRan` rather than the
form `AlgebraicGeometry.Space.meromorphicFunctionSheafDirectImage` uses, so that the transported
ring structure on its sections over `V` is the one
`AlgebraicGeometry.Space.chartProjection` is a natural transformation out of: the chart
projections are then homomorphisms of rings by `CategoryTheory.Sheaf.ringAddObj_naturality` and
its siblings, with no transport along `AlgebraicGeometry.Space.smallEtaleDirectImageRanIso`.
`AlgebraicGeometry.Space.meromorphicLocalizationMapRan` already lands in that form, so the
comparison is obtained from it by the same sheafification adjunction.

The compatibility with restriction of both charts needs no computation: the comparison is a
morphism of sheaves into the direct image, so Stacks 03G4 in the form
`AlgebraicGeometry.Space.ranFmap` turns it into an `f`-map, whose components are the chart
projections and whose naturality is therefore the one wanted.

## References

* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback (pullbackCommRingSheaf commRingSheaf_mul_comm)
open Stacks.Sheaves.RingedToposModules (inverseImageSectionsCommRing)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- `f_*𝒦_X`, with the direct image taken in its right Kan extension form. -/
noncomputable abbrev meromorphicDirectImageRan :
    Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u} :=
  pullbackCommRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
    (smallEtaleDirectImageRan B S hS f) (meromorphicFunctionSheaf B S hS X.1 X.2)

variable (hf : PullbacksMeromorphicSections B S hS f.hom)

/-- The comparison `𝒦_Y ⟶ f_*𝒦_X` into the Kan-extension form of the direct image. -/
noncomputable def meromorphicComparisonRan :
    meromorphicFunctionSheaf B S hS Y.1 Y.2 ⟶ meromorphicDirectImageRan B S hS f :=
  ((sheafificationAdjunction (SmallEtale.topology B S hS Y.1) CommRingCat.{u}).homEquiv
      (regularLocalizationPresheaf B S hS Y) _).symm (meromorphicLocalizationMapRan B S hS f hf)

/-- The chart projection of the direct image of the sheaf of meromorphic functions, as a
homomorphism of commutative rings. -/
noncomputable def meromorphicChartProjection (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (meromorphicDirectImageRan B S hS f).obj.obj (op V) →+*
      (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj j.right where
  toFun := (chartProjection B S hS f V j).app (meromorphicSetSheaf B S hS X)
  map_add' x y := (ringAddObj_naturality (meromorphicRingSheaf B S hS X)
      (chartProjection B S hS f V j) x y).trans
    (sectionsFunctor_map_ringAddHom (meromorphicRingSheaf B S hS X) j.right _ _)
  map_mul' x y := (ringMulObj_naturality (meromorphicRingSheaf B S hS X)
      (chartProjection B S hS f V j) x y).trans
    (sectionsFunctor_map_ringMulHom (meromorphicRingSheaf B S hS X) j.right _ _)
  map_zero' := (ringZeroObj_naturality (meromorphicRingSheaf B S hS X)
      (chartProjection B S hS f V j)).trans
    (sectionsFunctor_map_ringZeroHom (meromorphicRingSheaf B S hS X) j.right _)
  map_one' := (ringOneObj_naturality (meromorphicRingSheaf B S hS X)
      (chartProjection B S hS f V j)).trans
    (sectionsFunctor_map_ringOneHom (meromorphicRingSheaf B S hS X) j.right _)

/-- The comparison `𝒦_Y ⟶ f_*𝒦_X` on underlying sheaves of sets. -/
noncomputable def meromorphicSetComparisonRan :
    meromorphicSetSheaf B S hS Y ⟶
      (smallEtaleDirectImageRan B S hS f).obj (meromorphicSetSheaf B S hS X) :=
  (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
    ((sheafCompose (SmallEtale.topology B S hS Y.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (meromorphicComparisonRan B S hS f hf))

/-- **The chartwise pullback of meromorphic functions on the sheaves.**  Over a commuting square
of étale charts `U` of `X` above `V` of `Y` the comparison `𝒦_Y ⟶ f_*𝒦_X` projects to a
homomorphism of commutative rings `𝒦_Y(V) ⟶ 𝒦_X(U)`. -/
@[stacks 0ENC "part (1), chartwise on the SHEAVES of meromorphic functions: the fraction rule \
a/b ↦ f♯a/f♯b over an étale chart diagram as a homomorphism 𝒦_Y(V) ⟶ 𝒦_X(U), where \
AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions is the same rule on the presheaves of \
sectionwise localizations. This is the coefficient rule for part (1) read through the second of \
the two descriptions of 𝒦(F) in Stacks 0EN5, the sheafification of F ⊗_𝒪 𝒦, which is the one \
AlgebraicGeometry.Space.MeromorphicSection and hence part (2) use. The global map \
Γ(Y, 𝒦_Y(F)) ⟶ Γ(X, 𝒦_X(f^*F)) of part (1) is asserted for the first description by \
AlgebraicGeometry.Space.pullbackSheafifiedRegularSections, and for the second by \
AlgebraicGeometry.Space.pullbackMeromorphicSection, which is built over this rule. Part (2) is \
proved for an invertible module by \
AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection, over that same \
description, and is not asserted here"]
noncomputable def chartMeromorphicFunctionPullback (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V) →+*
      (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op d.U) :=
  (meromorphicChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).comp
    ((meromorphicComparisonRan B S hS f hf).hom.app (op d.V)).hom

/-- The chartwise pullback is the component at the cartesian form of the chart diagram of the
`f`-map that the comparison determines by Stacks 03G4. -/
theorem chartMeromorphicFunctionPullback_eq_ranFmap (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V)) :
    chartMeromorphicFunctionPullback B S hS f hf d s =
      (ranFmap B S hS f (meromorphicSetSheaf B S hS X) (meromorphicSetSheaf B S hS Y)
        (meromorphicSetComparisonRan B S hS f hf)).app d s :=
  chartProjection_app B S hS f (meromorphicSetSheaf B S hS X) d.V
    (indexOfChartDiagram B S hS f d) _

/-- **The chartwise pullback of meromorphic functions is compatible with simultaneous étale
restriction of the two charts of a diagram.** -/
theorem chartMeromorphicFunctionPullback_comp (d d' : ChartDiagram B S hS X.1 Y.1 f.hom)
    (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Y.1).map j)
    (s : (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V)) :
    chartMeromorphicFunctionPullback B S hS f hf d'
        (((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.map j.op).hom s) =
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map i.op).hom
        (chartMeromorphicFunctionPullback B S hS f hf d s) :=
  ((chartMeromorphicFunctionPullback_eq_ranFmap B S hS f hf d' _).trans
      ((ranFmap B S hS f (meromorphicSetSheaf B S hS X) (meromorphicSetSheaf B S hS Y)
        (meromorphicSetComparisonRan B S hS f hf)).naturality d d' i j h s)).trans
    (congrArg ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map i.op).hom
      (chartMeromorphicFunctionPullback_eq_ranFmap B S hS f hf d s).symm)

/-- **The chartwise pullbacks of meromorphic functions form an `f`-map of Stacks 03G3** on the
sheaves of meromorphic functions.  This is the sheafified form of
`AlgebraicGeometry.Space.fmapMeromorphicFunctions`, which is the same rule on the presheaves of
sectionwise localizations. -/
noncomputable def fmapMeromorphicFunctionSheaf :
    FMap B S hS X.1 Y.1 f.hom (meromorphicSetSheaf B S hS X).obj
      (meromorphicSetSheaf B S hS Y).obj where
  app d := chartMeromorphicFunctionPullback B S hS f hf d
  naturality d d' i j h s := chartMeromorphicFunctionPullback_comp B S hS f hf d d' i j h s

/-! ### The chartwise pullback extends the pullback of regular functions -/

/-- The comparison restricts along the sheafification map to the chartwise fraction rule on the
presheaf of sectionwise localizations. -/
theorem toSheafify_comp_meromorphicComparisonRan :
    toSheafify (SmallEtale.topology B S hS Y.1) (regularLocalizationPresheaf B S hS Y) ≫
        (sheafToPresheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}).map
          (meromorphicComparisonRan B S hS f hf) =
      meromorphicLocalizationMapRan B S hS f hf :=
  ((sheafificationAdjunction (SmallEtale.topology B S hS Y.1) CommRingCat.{u}).homEquiv_unit
      (f := meromorphicComparisonRan B S hS f hf)).symm.trans (Equiv.apply_symm_apply _ _)

/-- The comparison on a section of the presheaf of sectionwise localizations, read through the
sheafification map. -/
theorem meromorphicComparisonRan_app_toSheafify (V : SmallEtale B S hS Y.1)
    (x : (regularLocalizationPresheaf B S hS Y).obj (op V)) :
    ((meromorphicComparisonRan B S hS f hf).hom.app (op V)).hom
        (((toSheafify (SmallEtale.topology B S hS Y.1)
          (regularLocalizationPresheaf B S hS Y)).app (op V)).hom x) =
      meromorphicLocalizationMapApp B S hS f hf V x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_comp_meromorphicComparisonRan B S hS f hf) (op V)) x

/-- The chartwise fraction rule on the presheaf of sectionwise localizations at equal chart
diagrams agrees.  The two sides have the same type, the charts being the same, but the statement
is phrased with `HEq` because the type mentions the diagram. -/
theorem chartPullbackMeromorphicFunctions_heq
    {d d' : ChartDiagram B S hS X.1 Y.1 f.hom} (h : d = d')
    {x : (regularLocalizationPresheaf B S hS Y).obj (op d.V)}
    {x' : (regularLocalizationPresheaf B S hS Y).obj (op d'.V)} (hx : HEq x x') :
    HEq (chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf d x)
      (chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf d' x') := by
  subst h
  obtain rfl := eq_of_heq hx
  rfl

/-- **The chartwise pullback on the sheaves extends the chartwise fraction rule on the presheaf
of sectionwise localizations**: a fraction over `V`, viewed as a meromorphic function, goes to
the image under the fraction rule of the diagram, viewed as a meromorphic function. -/
theorem chartMeromorphicFunctionPullback_toSheafify (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : (regularLocalizationPresheaf B S hS Y).obj (op d.V)) :
    chartMeromorphicFunctionPullback B S hS f hf d
        (((toSheafify (SmallEtale.topology B S hS Y.1)
          (regularLocalizationPresheaf B S hS Y)).app (op d.V)).hom x) =
      ((toSheafify (SmallEtale.topology B S hS X.1)
          (regularLocalizationPresheaf B S hS X)).app (op d.U)).hom
        (chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf d x) := by
  refine Eq.trans (congrArg
    (meromorphicChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d))
      (meromorphicComparisonRan_app_toSheafify B S hS f hf d.V x)) ?_
  refine (chartProjection_meromorphicLocalizationMapApp B S hS f hf d.V
    (indexOfChartDiagram B S hS f d) x).trans ?_
  exact congrArg ((toSheafify (SmallEtale.topology B S hS X.1)
      (regularLocalizationPresheaf B S hS X)).app (op d.U)).hom
    (eq_of_heq (chartPullbackMeromorphicFunctions_heq B S hS f hf
      (chartDiagramOfIndex_indexOfChartDiagram B S hS f d) HEq.rfl))

/-- The canonical map `𝒪_Z ⟶ 𝒦_Z` on sections, written as the sectionwise localization map
followed by sheafification. -/
theorem toMeromorphicFunctionSheaf_app_apply (Z : AlgebraicSpaces B S hS)
    (U : SmallEtale B S hS Z.1) (r : (structurePresheaf B S hS Z.1).obj (op U)) :
    ((toMeromorphicFunctionSheaf B S hS Z.1 Z.2).hom.app (op U)).hom r =
      ((toSheafify (SmallEtale.topology B S hS Z.1)
            (regularLocalizationPresheaf B S hS Z)).app (op U)).hom
        (((regularSubpresheaf B S hS Z).toLocalizationPresheaf.app (op U)).hom r) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (RingedSite.MultiplicativeSubpresheaf.toLocalizationSheaf_hom
      (regularSubpresheaf B S hS Z)) (op U)) r

/-- **The chartwise pullback of meromorphic functions extends the pullback of regular
functions**: a regular function on `V`, viewed as meromorphic, goes to its pullback along the
vertical scheme morphism of the diagram, viewed as meromorphic. -/
theorem chartMeromorphicFunctionPullback_toMeromorphicFunctionSheaf
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (r : (structurePresheaf B S hS Y.1).obj (op d.V)) :
    chartMeromorphicFunctionPullback B S hS f hf d
        (((toMeromorphicFunctionSheaf B S hS Y.1 Y.2).hom.app (op d.V)).hom r) =
      ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op d.U)).hom
        ((chartSectionPullback B S hS d).hom r) := by
  refine Eq.trans (congrArg (chartMeromorphicFunctionPullback B S hS f hf d)
    (toMeromorphicFunctionSheaf_app_apply B S hS Y d.V r)) ?_
  refine Eq.trans (chartMeromorphicFunctionPullback_toSheafify B S hS f hf d _) ?_
  refine Eq.trans ?_ (toMeromorphicFunctionSheaf_app_apply B S hS X d.U _).symm
  exact congrArg _ (chartPullbackMeromorphicFunctions_toLocalizationPresheaf
    B S hS X.2 Y.2 hf d r)

end AlgebraicGeometry.Space

end
