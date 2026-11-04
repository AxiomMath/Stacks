module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.Mates
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.PastedSquare
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.UnitRestrict
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.OuterSquare
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.SourceBridge
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.MergeCounit
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.SpecCorner

/-!
# The cube at a chart, read against the comparison of the four local rings

Let `ch` be a Cartesian affine-open chart for a base-change square of schemes and `y` a point of
`Spec 𝒪_{X'}(U')`, with image `x'` in `X'`. The chart's square of coordinate rings, with its two
target corners `𝒪_{S'}(V')`, `𝒪_{X'}(U')` pushed to the local rings `𝒪_{S', f' x'}`,
`𝒪_{X', x'}`, is again a commuting square, the chart's *outer rectangle*. The source
identification `AlgebraicGeometry.BaseChangeChart.localRingsSourceIso` followed by the Tag 065Z
comparison of the four local rings is the Tag 065Z comparison of the outer rectangle, followed by
the two identifications of its target corner. From this, the comparison of the four local rings
on cohomology, read on the source identification of the cube, is the chart's own comparison
inserted at the germ generator of the `𝒪_{X'}(U')`-localization.

The file also proves coherences of derived extension and restriction of scalars in the generality
they belong to: the mate relations of the composition isomorphism, the compatibility of the
homology comparison of an exact functor with a composition isomorphism, the comparison of a pasted
square on the generators of a flat localization, and the naturality of the localization of the
derived sections over an affine open.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryCompNatIso_homologyIso_hom_app`: the homology
  comparison of an exact functor is compatible with a composition isomorphism `F ⋙ G ≅ H`, on
  the derived category.
* `RingTheory.TorIndependence.squareComparison_pasted_flatComp_inv`: the comparison of the outer
  rectangle of two stacked squares, precomposed with the inverse of
  `RingTheory.TorIndependence.flatCompDerivedHomologyIso`, is the top square's comparison on
  cohomology followed by the bottom square's.
* `RingTheory.TorIndependence.derivedRestrictScalarsSquareIso_homologyIso_apply`: around a
  commuting square of rings, the two readings of the homology comparison of restriction of
  scalars agree.
* `RingTheory.TorIndependence.squareComparison_unit_one_tmul`: the Tag 065Z comparison of a
  square `(R', A', R₃, A₃)` on cohomology, evaluated on `1 ⊗ z`, is the unit of the derived
  change-of-rings adjunction along `A' → A₃` at `z` read over `A'`.
* `AlgebraicGeometry.BaseChangeChart.outerSquare_comm`: the chart's outer rectangle commutes.
* `AlgebraicGeometry.BaseChangeChart.localRingsSourceIso_comp_squareComparison`: the
  identification of the source of the cube, at a complex of `𝒪_{X, g' x'}`-modules.
* `AlgebraicGeometry.BaseChangeChart.cohomologyComparisonMap_localRingsSourceIso`: the same
  identification read through `RingTheory.TorIndependence.cohomologyComparisonMapGeneral`.
* `AlgebraicGeometry.BaseChangeChart.localTail`: the two identifications of the outer
  rectangle's target corner followed by the pointwise morphism of Tag 0DJ7.
* `AlgebraicGeometry.BaseChangeChart.cohomologyComparisonMap_localRingsSourceMap_eq_germGenerator`:
  the pointwise comparison on the image of `AlgebraicGeometry.BaseChangeChart.localRingsSourceMap`
  is the comparison of the outer rectangle evaluated on the germ generator `1 ⊗ m`.
* `RingTheory.TorIndependence.flatDerivedHomologyIso_comp_inv_app_one_tmul`: the flat homology
  comparison along a composite of flat maps, on a generator.
* `RingTheory.TorIndependence.unit_comp_restrictHomologyIso_apply`: the same identification with
  both generators written as units of the derived change-of-rings adjunction.
* `RingTheory.TorIndependence.flatDerivedHomologyIso_inv_app_one_tmul_map`: a generator moved
  along a morphism of the base.
* `RingTheory.TorIndependence.squareComparison_pasted_unit_one_tmul`: the comparison of the outer
  rectangle of two stacked squares on the germ generator `1 ⊗ m₀` is the unit along `A' → A₃`
  applied to the top square's comparison of `m₀`.
* `AlgebraicGeometry.tildeDerivedSectionsIso_hom_naturality`,
  `AlgebraicGeometry.derivedStalkAffineSectionsIso_hom_naturality` and
  `AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso_hom_naturality`: the localization of
  the derived sections over an affine open is natural in the complex.
* `RingTheory.TorIndependence.map_unit_comp_restrictScalarsDerivedExtendCompIso_hom_app_map`: the
  passage `RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso` absorbs a unit of the
  derived change-of-rings adjunction followed by a morphism out of the localization.
* `AlgebraicGeometry.unit_comp_totalDerivedExtensionScalarsIsoRestrict`: the unit of the derived
  change-of-rings adjunction along an invertible `ε`, read against
  `AlgebraicGeometry.totalDerivedExtensionScalarsIsoRestrict`, is the transport unit of the
  restriction-of-scalars equivalence.
* `RingTheory.TorIndependence.unit_comp_map_restrictScalarsMerge`: the unit along a composite
  through a localization, against the unit along the localization.
* `AlgebraicGeometry.derivedStalkAffineSectionsCongrIso_eq`:
  `AlgebraicGeometry.derivedStalkAffineSectionsCongrIso` in terms of
  `AlgebraicGeometry.derivedStalkAffineSectionsIso`, with the point of `X` free.
* `RingTheory.TorIndependence.unit_comp_map_totalDerivedExtensionScalarsComp_hom` and
  `RingTheory.TorIndependence.totalDerivedExtensionScalarsComp_hom_app_comp_counit`: the mate
  relations of `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp` for the
  derived change-of-rings adjunctions.
* `AlgebraicGeometry.map_totalDerivedExtensionScalarsIsoRestrict_hom_comp_counit` and
  `AlgebraicGeometry.map_totalDerivedExtensionScalarsIsoRestrict_hom_comp_counit_eq`: the
  restriction model of derived extension of scalars along an isomorphism, met against the counit
  along its inverse.
* `AlgebraicGeometry.BaseChangeChart.unit_comp_localTail_of_specCorner` and
  `AlgebraicGeometry.BaseChangeChart.cohomologyComparisonMap_localRingsSourceMap_of_specCorner`:
  the identification of the chart's target corner and the commutation of the source bridge,
  under the hypothesis `AlgebraicGeometry.BaseChangeChart.SpecCornerComm`.
* `AlgebraicGeometry.totalDerivedExtensionScalarsCompIsoRestrict_hom_app` and
  `AlgebraicGeometry.map_totalDerivedExtensionScalarsCompIsoRestrict_hom_comp_counit`: the two
  factors of `AlgebraicGeometry.totalDerivedExtensionScalarsCompIsoRestrict`, and that
  isomorphism met against the counit along `ε'`.
* `RingTheory.TorIndependence.map_merge_comp_counit` and
  `RingTheory.TorIndependence.inv_comp_map_merge_comp_counit`: the passage through a
  localization absorbs the merge of two restrictions of scalars and the counit.
* `AlgebraicGeometry.derivedStalkAffineSections_extend_comp_obj_eq`,
  `AlgebraicGeometry.map_eqToHom_comp_comp_hom_extend` and
  `AlgebraicGeometry.comp_inv_comp_map_eqToHom_stalk`: transports along an equality of points and
  of morphisms of schemes, across the composition isomorphism.
* `AlgebraicGeometry.BaseChangeChart.stalkMap_comp_stalkCompAIso_inv`: the chart's comparison at
  `U` read backwards and then along `g'` is the stalk map of `Spec ch.c` read along `ε'`.
* `AlgebraicGeometry.BaseChangeChart.localTailMorphism_eq`: the chart's tail morphism, written
  without unit, counit or localization passage.
* `AlgebraicGeometry.BaseChangeChart.specCornerComm`: the reconciliation
  `AlgebraicGeometry.BaseChangeChart.SpecCornerComm` at the `Spec 𝒪_X(U)` corner holds.
* `AlgebraicGeometry.BaseChangeChart.cohomologyComparisonMap_localRingsSourceMap`: the
  commutation of the source bridge at a chart, with no hypothesis beyond the chart, the point,
  the complexes and the inverse germ comparison.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)

## Parts

The declarations live in the submodules `AffineChartSourceComparison.<Part>`, in this order:

* `Mates`: mate relations of composition isomorphisms, homology comparison.
* `PastedSquare`: a pasted square on the generators of a flat localization.
* `UnitRestrict`: units along composites, restriction model, naturality.
* `OuterSquare`: the chart's outer rectangle and the source identification.
* `SourceBridge`: the source bridge under `SpecCornerComm`.
* `MergeCounit`: transports and the merge counit.
* `SpecCorner`: the reconciliation at the `Spec 𝒪_X(U)` corner.
-/
