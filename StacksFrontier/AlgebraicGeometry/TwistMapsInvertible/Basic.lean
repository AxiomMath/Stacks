module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Absolute

/-!
# Tag 01O4: the twists on a relative `Proj` are invertible

Let `S` be a scheme and `A` a commutative, nonnegatively graded, quasi-coherent graded
`𝒪_S`-algebra — Situation 01NN, in the sheaf-level form
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` — and suppose that over every
affine open `U` of `S` the graded section ring `Γ(U, A)` is generated in degree one over its
degree-zero part. Tag 01O4 asserts that every integral twist `𝒪(n)` on the relative homogeneous
spectrum of `A` is an invertible sheaf of modules.

This file proves that, for an arbitrary family of chart identifications — Tag 01NR's
`Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData` — and hence in particular for any
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`, which carries one.

## Main results

* `Stacks.AlgebraicGeometry.TwistMapsInvertible.isInvertibleModule_piece`: **every homogeneous
  piece of a graded algebra on the relative `Proj` carrying chart identifications is an invertible
  `𝒪`-module**, in the `Stacks.Ample.IsInvertibleModule` spelling.
* `Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_isInvertible`: **Tag 01O4**, at the
  spelling of the tag's statement: the invertibility class
  `AlgebraicGeometry.SheafOfModules.IsInvertible` applied to the structure presheaf of the relative
  `Proj` and the sheaf condition `ringCatSheaf.2`.
* `Stacks.AlgebraicGeometry.TwistMapsInvertible.relativeProjTwists_isInvertible`: the same with
  the generation hypothesis as a `Fact` instance, which is how the tag's statement carries it.
  **This is the declaration the tag is attached to.**
* `Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_stacksIsInvertible`: the same conclusion
  for `Stacks.SheafOfModules.IsInvertible`, the repository's *other* class carrying the Tag 01CS
  label, so that a consumer holding either class is served.

## The route

Invertibility is local, and the relative `Proj` is covered by its charts, on which the twists are
the absolute twists. So the proof is three existing inputs and no new mathematics.

* The charts cover: `Stacks.AlgebraicGeometry.RelativeProjTwistGlue.iSup_toBase_preimage_eq_top`
  covers the relative `Proj` by the inverse images of the affine opens of the base, and
  `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.chart_range` identifies each of those with
  the image of a chart. So a point of the relative `Proj` is the image of a point of
  `Proj Γ(U, A)` for some affine `U`.
* On the chart the twists are trivial near every point:
  `exists_mem_restrict_isoUnit_twistingSheaf_of_adjoin` of `Absolute.lean`,
  which is the degree-one case of Tag 01MW's ratio trivialization.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.chartIso` transports that trivialization
  to the glued piece, and
  `isInvertibleModule_of_forall_exists_isoUnit_openImmersion` of `Local.lean`
  assembles the pointwise trivializations into invertibility. The trivializing neighbourhood of a
  point arrives as the image of the open immersion `V.ι ≫ chart U hU` from a standard open `V` of
  `Proj Γ(U, A)`, which is exactly the shape that lemma takes.

## What is used from the hypothesis, and what is not

Only `ChartData` is used: the open-immersion property of the charts, the identification of their
images with the inverse images of the affine opens, and the degreewise identification of the
restricted pieces with the absolute twists. Neither the multiplication nor the unit of the graded
algebra enters, nor quasi-coherence, nor the homogeneous-section map `ψ` and its chart formula, nor
either uniqueness assertion. That is why the result is stated for a `ChartData` first: it is
strictly more general than the `TwistData` form of the tag's statement, and that form is a
projection of it.

## Substitutions against the source statement, and why they are forced

Tag 01NR's `relativeProjTwists s` is the canonical twist datum, and
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` builds a `TwistData` from a
quasi-coherent graded algebra with no further hypothesis, so the type is inhabited for every
situation this file speaks about. The statements below quantify over an arbitrary `TwistData`,
which is the form Tag 01NR's own assertions `TwistData.chartIso_mul` and `TwistData.chartIso_one`
are proved in, and which therefore *implies* the conclusion for each particular datum. The
other substitutions are the standing library renamings: Tag 01NN's
`RelativeProjSituation` for `SheafGradedAlgebra`, `s.sectionRingGrading U` for `A.grading U`,
`s.sectionRing U` for `A.sectionRing U`, Tag 01NQ's `relativeProj s` for
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj A`, and Tag 01CS's `IsInvertible` for
`AlgebraicGeometry.SheafOfModules.IsInvertible`, which is the library class whose definition
matches Tag 01CS field for field.

## Implementation notes

The chart's open-immersion instance is taken from `ChartData.chart_isOpenImmersion` into the local
context, the same way the fields of `ChartData` take it, so that `ChartData.chartIso` is applied at
the instance its own type was elaborated with. The global instance
`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart` proves the same `Prop` and
would do as well.

`AlgebraicGeometry.Scheme.Modules.restrict` has the module before the morphism, with the target
scheme implicit, so applying it to an absolute twist — whose type is stated over the composite of
the structure sheaf with the forgetful functor rather than over `Scheme.ringCatSheaf` — leaves the
scheme as a metavariable that unification cannot solve. `Absolute.lean` names it explicitly for
that reason.

## References

* [Stacks Project, Lemma 27.15.6 (Tag 01O4)](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.TwistMapsInvertible

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- **Tag 01O4.** Every homogeneous piece of a graded algebra on the relative homogeneous spectrum
of `A` which carries Tag 01NR's chart identifications is an invertible `𝒪`-module, as soon as the
graded section ring of `A` over every affine open of the base is generated in degree one over its
degree-zero part.

Invertibility is local; the charts cover the relative `Proj`; on a chart the piece is the absolute
twist, which degree-one generation trivializes near every point. -/
theorem isInvertibleModule_piece
    {algebra : RelativeProjTwists.SchemeGradedAlgebra (relativeProj A).scheme}
    (D : RelativeProjTwists.ChartData A algebra)
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (n : ℤ) :
    Stacks.Ample.IsInvertibleModule (relativeProj A).scheme (algebra.piece n) := by
  refine isInvertibleModule_of_forall_exists_isoUnit_openImmersion (algebra.piece n) fun x => ?_
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((RelativeProjTwistGlue.iSup_toBase_preimage_eq_top (relativeProj A)).ge
      (TopologicalSpace.Opens.mem_top x))
  have := D.chart_isOpenImmersion U.1 U.2
  have hrange : x ∈ ((relativeProj A).chart U.1 U.2).opensRange := by
    rw [← Scheme.Hom.image_top_eq_opensRange, D.chart_range U.1 U.2]
    exact hxU
  obtain ⟨y, hy⟩ := hrange
  obtain ⟨V, hyV, ⟨eV⟩⟩ := exists_mem_restrict_isoUnit_twistingSheaf_of_adjoin
    (A.grading U.1) (hgen U.1 U.2) n y
  refine ⟨V.toScheme, V.ι ≫ (relativeProj A).chart U.1 U.2, inferInstance,
    ⟨⟨y, hyV⟩, hy⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.restrictFunctorComp V.ι ((relativeProj A).chart U.1 U.2)).app
      (algebra.piece n) ≪≫
    (Scheme.Modules.restrictFunctor V.ι).mapIso (D.chartIso U.1 U.2 n) ≪≫ eV

/-- **Tag 01O4**, at the spelling of the tag's statement: the invertibility class of Tag 01CS
applied to the structure presheaf of the relative homogeneous spectrum and the sheaf condition of
its `ringCatSheaf`, for the homogeneous pieces of the twist data of Tag 01NR, with the generation
hypothesis as an ordinary argument. -/
theorem twistData_isInvertible (D : RelativeProjTwists.TwistData A)
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (relativeProj A).scheme.presheaf
      (relativeProj A).scheme.ringCatSheaf.2 (D.algebra.piece n) :=
  isInvertibleModule_piece D.chartData hgen n

/-- **Tag 01O4.** Every integral twist on the relative homogeneous spectrum of a quasi-coherent
graded algebra is invertible when the algebra is generated in degree one over its degree-zero
part.

The generation hypothesis is a `Fact`, so that invertibility of the twists is available to
instance search, exactly as the tag's statement carries it. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   Also carried here: an arbitrary RelativeProjTwists.TwistData A rather than the canonical one;
--   at the canonical datum of Tag 01NR the same conclusion is
--   twistDataOfGradedAlgebra_isInvertible, which carries the tag too.
--   Outside the scope of this declaration, but proved elsewhere in this library: the tag's MAIN
--   clause, that X = Proj_S(A) REPRESENTS the functor F_1 of pairs (L, psi) with f^*A_1 -> L
--   surjective, up to strict equivalence. Its carriers are
--   ProjRepresentsF1.pairClassifyingHom_bijective (ProjRepresentsF1/PairFromQuadruple.lean:604),
--   the bijectivity of the classifying map from strict isomorphism classes to morphisms T ->
--   Proj_S(A) over S, and ProjRepresentsF1.f1Bundle
--   (ProjRepresentsF1/TensorPowerBridgeProof.lean:438), which builds the whole
--   ProjRepresentsF1.F1Bundle -- the universal pair, the representing bijections, their
--   normalisation at the identity, the pullback of classes and its naturality -- from the
--   degree-one generation alone. All three of the tag's assertions are stated together in
--   TwistMapsInvertible.f1Bundle_and_twists
--   (TwistMapsInvertible/RepresentsAndTwists.lean). What is still unassembled is the larger
--   structure ProjRepresentsF1.F1Representation (ProjRepresentsF1/Representation.lean), which
--   adds to the bundle the field universal_isCanonical identifying the universal pair with the
--   canonical twist pair of a twist datum; that pinning against Tag 01NR's twists is not one of
--   the tag's assertions. The absolute universal property
--   ProjDegreeOneRepresents.existsUnique_classifies (Tag 01NA) is the input the representation
--   descends from.
instance relativeProjTwists_isInvertible (D : RelativeProjTwists.TwistData A)
    [hgen : Fact (∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)]
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (relativeProj A).scheme.presheaf
      (relativeProj A).scheme.ringCatSheaf.2 (D.algebra.piece n) :=
  twistData_isInvertible D hgen.out n

/-- **Tag 01O4 for the repository's other class realising Tag 01CS.** The repository carries two
distinct classes with Tag 01CS's definition of invertibility and the same Tag 01CS label
— `AlgebraicGeometry.SheafOfModules.IsInvertible`, which the ampleness theory and the absolute
twist results use, and `Stacks.SheafOfModules.IsInvertible`, which Tags 0B8K and 0B8L are stated
for. They are not definitionally equal, so this records the conclusion for the second one as well,
through `Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`. -/
theorem twistData_stacksIsInvertible (D : RelativeProjTwists.TwistData A)
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible (relativeProj A).scheme.presheaf
      (relativeProj A).scheme.ringCatSheaf.2 (D.algebra.piece n) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    (relativeProj A).scheme.presheaf (relativeProj A).scheme.ringCatSheaf.2
    (D.algebra.piece n)).mpr (twistData_isInvertible D hgen n)

end Stacks.AlgebraicGeometry.TwistMapsInvertible

end
