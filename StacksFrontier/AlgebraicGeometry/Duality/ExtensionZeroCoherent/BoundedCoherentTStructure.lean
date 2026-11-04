module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedSerreInducedTStructure
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.BoundedCoherentTriangulated

/-!
# The t-structure on `D^b_{Coh}(𝒪_X)`

`AlgebraicGeometry.BoundedCoherentDerived X` is the full subcategory of `D(𝒪_X)` of
cohomologically bounded objects with coherent cohomology sheaves. The canonical t-structure of
`D(𝒪_X)` induces a t-structure on it: the truncations `τ^{≤0}A` and `τ^{≥1}A` of an object `A` of
`D^b_{Coh}(𝒪_X)` again lie in `D^b_{Coh}(𝒪_X)`, because coherent modules form a weak Serre
subcategory of `X.Modules` ([Stacks, Tag 01BY] (5)).

The derived category `D(𝒪_X)` is the one given by the local instance
`CategoryTheory.HasDerivedCategory.standard`, as in
`AlgebraicGeometry.isTriangulated_boundedCoherentDerived`; it is not the one given by
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.

## Main results

* `AlgebraicGeometry.hasInducedTStructure_boundedCoherentDerived`: the canonical t-structure on
  `D(𝒪_X)` induces one on `D^b_{Coh}(𝒪_X)`.
* `AlgebraicGeometry.boundedCoherentTStructure`: the t-structure on `D^b_{Coh}(𝒪_X)`.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 06UQ](https://stacks.math.columbia.edu/tag/06UQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- The canonical t-structure on `D(𝒪_X)` induces a t-structure on the full subcategory
`D^b_{Coh}(𝒪_X)` of cohomologically bounded objects with coherent cohomology sheaves. -/
public instance hasInducedTStructure_boundedCoherentDerived (X : Scheme.{u}) :
    (boundedCoherentDerived X).HasInducedTStructure
      (DerivedCategory.TStructure.t (C := X.Modules)) :=
  DerivedCategoryB.hasInducedTStructure_derivedCategoryBBounded _

/-- The t-structure on `D^b_{Coh}(𝒪_X)` induced by the canonical t-structure of `D(𝒪_X)`:
its truncation functors are those of `D(𝒪_X)`. -/
public def boundedCoherentTStructure (X : Scheme.{u}) :
    TStructure (BoundedCoherentDerived X) :=
  (boundedCoherentDerived X).tStructure (DerivedCategory.TStructure.t)

end AlgebraicGeometry

end
