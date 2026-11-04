module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RepresentativeIndependence

/-!
# Perfectness of a derived object is local on the space

An object of `D(O_X)` is perfect as soon as its restriction to each member of some open covering
of `X` is perfect. This is the reduction every local argument about perfectness starts from: the
source of Tag 08CQ phrases its converse direction as "the question is local on `X`, so we may
assume `E` has finite Tor dimension", which is legitimate only because perfectness is local.

## Main results

* `Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_forall_isPerfectComplex_restrict`: a
  complex whose restrictions to the members of an open covering are perfect complexes represents
  a perfect object of `D(O_X)`.
* `Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect`: an object of
  `D(O_X)` whose restriction to a neighbourhood of every point is perfect is perfect.

## Implementation notes

The argument takes place at the level of complexes. A representative `E` of the object is fixed;
over each open `U` of the covering, the restriction of `E` represents the restriction of the
object, so it is a perfect complex by Stacks 08CN
(`AlgebraicGeometry.RingedSpace.isPerfectComplex_of_isPerfect_representation`), and a complex
whose restrictions to a covering are perfect complexes is perfect
(`AlgebraicGeometry.RingedSpace.isPerfectComplex_of_forall_isPerfectComplex_restrict`).

The hypothesis of `Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect` is a
statement about the derived categories of the open subspaces, so it is stated for any model of
those as well as of `D(O_X)`; the complex-level form
`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_forall_isPerfectComplex_restrict` needs
only the model of `D(O_X)`.

The space, ring and module universes coincide, as they already must for the local models of
Tag 08CN.

## References

* [Stacks Project, Tag 08CN](https://stacks.math.columbia.edu/tag/08CN)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace Stacks.Cohomology.PerfectComplexTriangles

universe u d d'

variable {X : RingedSpace.{u, u}}

/-- **Perfectness is local on the space, at the level of complexes.** A complex of
`𝒪_X`-modules whose restrictions to the members of an open covering of `X` are perfect complexes
represents a perfect object of `D(𝒪_X)`. -/
theorem isPerfect_of_forall_isPerfectComplex_restrict [HasDerivedCategory.{d} (OXMod.{u} X)]
    (E : CochainComplex (OXMod.{u} X) ℤ)
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      Stacks.Cohomology.PerfectComplexes.IsPerfectComplex (X := X.restrict U.isOpenEmbedding)
        (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex E U)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (DerivedCategory.Q.obj E) :=
  ⟨E, AlgebraicGeometry.RingedSpace.isPerfectComplex_of_forall_isPerfectComplex_restrict h,
    ⟨Iso.refl _⟩⟩

open AlgebraicGeometry.RingedSpace.PseudoCoherence in
/-- **Perfectness is local on the space.** If every point of `X` has an open neighbourhood `U`
such that the restriction of `K` to the open subspace `X|_U` is perfect, then `K` is perfect.

The restriction of a representative `E` of `K` to `U` represents the restriction of `K`, so it is
a perfect complex by Stacks 08CN; these restrictions assemble by
`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_forall_isPerfectComplex_restrict`. -/
theorem isPerfect_of_local_isPerfect [HasDerivedCategory.{d} (OXMod.{u} X)]
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    (K : DerivedCategory (OXMod.{u} X))
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      Stacks.Cohomology.PerfectComplexes.IsPerfect
        ((restrictModules.{u} X U).mapDerivedCategory.obj K)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect K := by
  refine isPerfect_of_iso (DerivedCategory.Q.objObjPreimageIso K)
    (isPerfect_of_forall_isPerfectComplex_restrict _ fun x => ?_)
  obtain ⟨U, hxU, hU⟩ := h x
  exact ⟨U, hxU, AlgebraicGeometry.RingedSpace.isPerfectComplex_of_isPerfect_representation hU
    ⟨((restrictModules.{u} X U).mapDerivedCategoryFactors.app _).symm ≪≫
      (restrictModules.{u} X U).mapDerivedCategory.mapIso
        (DerivedCategory.Q.objObjPreimageIso K)⟩⟩

end Stacks.Cohomology.PerfectComplexTriangles

end
