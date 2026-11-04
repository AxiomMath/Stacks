module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative flat locus of a module of finite presentation on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite presentation and let `F` be an `𝒪_X`-module which is quasi-coherent and of
finite presentation.  Then the locus of points of `X` at which `F` is flat over `Y` is open.
This is Stacks 05WV.

The locus is `AlgebraicGeometry.Space.flatLocus`, the set already used for Stacks 0DLR in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatFiniteTypeModuleLocus.lean`: a point of `X` lies in
it when some commuting square of étale scheme charts through that point witnesses flatness of
the restricted module over the target chart.  What this file adds over Stacks 0DLR is not a new
locus but a *different set of hypotheses* on the same one — see the implementation notes.

## Main definitions

No new definitions are introduced.  Finite presentation of a module on charts is
`AlgebraicGeometry.Space.IsFinitePresentationOnCharts` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleLocusOpen.lean`.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_flatLocusOpenSubspace_of_finitePresentation` reads
  the locus as an open subspace of `X` in the sense of Tag 03BZ.

## Implementation notes

The openness assertion itself is **Stacks 05WV**,
`AlgebraicGeometry.Space.isOpen_flatLocus_of_isFinitePresentationOnCharts` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleLocusOpen.lean`, which is where that tag is
registered; the chartwise statement it rests on is
`AlgebraicGeometry.Space.isOpen_chartFlatLocus_of_isFinitePresentationOnCharts` there.  What
this file adds is the reading of the locus as an open subspace of the source.

The difference between this and the openness assertion of Stacks 0DLR,
`AlgebraicGeometry.Space.isOpen_flatLocus`, is entirely in the hypotheses, the locus and its
reading being the same in both.  Stacks 0DLR asks the module to be of finite *type* and the
weakly associated points of the target to be locally finite on charts, because its chartwise
input is the scheme-level Stacks 05IK, `AlgebraicGeometry.isOpen_flatLocus`, which carries that
hypothesis.  Stacks 05WV asks instead for finite *presentation* of the module and imposes no
condition on the target, because its chartwise input is the scheme-level Stacks 0399,
`AlgebraicGeometry.isOpen_setOf_flatOverAt`.  Neither statement implies the other: finite
presentation is the stronger hypothesis on the module, local finiteness of the weakly
associated points the extra hypothesis on the target.  Both are recorded here and there against
one locus, so a consumer may use whichever of the two its data satisfies.

Finite presentation of the module is taken chartwise, as `AlgebraicGeometry.Space.IsFiniteType`
on charts and quasi-coherence on charts are taken in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatFiniteTypeModuleLocus.lean`, and for the same reason:
it is the form the source itself uses, by More on Morphisms of Spaces, Theorem 76.22.1, and it
is the weaker hypothesis.  The site-local predicate
`SheafOfModules.IsFinitePresentationOnSite` does pass to
`AlgebraicGeometry.Space.restrictToChart`, by
`AlgebraicGeometry.Space.isFinitePresentation_restrictToChart` of
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentationChartRestriction.lean`, so a consumer
holding the site-local hypothesis can supply the chartwise one; it needs quasi-coherence on the
small étale site as well, which the chartwise reading does not give.

The locus is the *some-source-chart* condition, which is clause (1) of Tag 05VU and hence the
source's own definition of flatness at a point, Tag 05VV (1).  That the condition does not
depend on the charts used to test it is Tag 05VU,
`AlgebraicGeometry.Space.isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint`, read
on the locus by `AlgebraicGeometry.Space.mem_flatLocus_iff_isFlatOverAtGeometricPoint` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleLocusOpen.lean`; it needs quasi-coherence of
the module on the small étale site, which neither this file nor Stacks 0DLR assumes, both
reading quasi-coherence on charts instead.  The source proves Stacks 05WV by taking one
commuting square of *surjective* étale charts and transporting the open chart locus forward;
taking the union over all squares, as `AlgebraicGeometry.Space.flatLocus_eq_iUnion_image` does,
describes the same set, and is open with no appeal to Tag 05VU at all.

The module universe is the universe of the structure rings, which is the convention of
`AlgebraicGeometry.Space.IsFlatOver` of Tag 05VV and the only universe at which
`AlgebraicGeometry.Space.restrictToChart` lands in `AlgebraicGeometry.Scheme.Modules` of the
chart.

`AlgebraicGeometry.Space.pointTopology` of Tag 03BY is a plain definition rather than an
instance and is made a local instance here.

## References

* [Stacks Project, Tag 05WV](https://stacks.math.columbia.edu/tag/05WV)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The relative flat locus of a quasi-coherent module of finite presentation is an open
subspace of the source, in the sense of Tag 03BZ. -/
@[ega "IV 11.3.1" "more general"]
theorem isOpenSubspace_flatLocusOpenSubspace_of_finitePresentation
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) (F : Modules.{u, u} B S hS X hX)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hfp : IsFinitePresentationOnCharts B S hS hX F) :
    IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS hX f F) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hX _
    (isOpen_flatLocus_of_isFinitePresentationOnCharts B S hS hX f F hf hqc hfp)

end AlgebraicGeometry.Space

end
