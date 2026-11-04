module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CoheratorDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurjFromChart
public import StacksFrontier.AlgebraicGeometry.Size.CoveringsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# `D_QCoh(𝒪_X)` is a strictly full saturated triangulated subcategory

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`. The complexes
of `𝒪_X`-modules with quasi-coherent cohomology sheaves form a strictly full saturated
triangulated subcategory `D_QCoh(𝒪_X)` of `D(𝒪_X)` (Stacks 06UQ): quasi-coherent `𝒪_X`-modules
form a weak Serre subcategory of all `𝒪_X`-modules (Stacks 03M1), closure under extensions coming
from Descent, Proposition 03DW.

## Main results

* `AlgebraicGeometry.Space.qcohDerivedProp_isTriangulated_saturated`: the three properties.
* `AlgebraicGeometry.Space.qcohDerivedProp_isTriangulated`: the triangulated structure, as an
  instance.

## References

* [Stacks Project, Tag 06UQ](https://stacks.math.columbia.edu/tag/06UQ)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

-- A universe-polymorphic `Abelian` instance for sheaves of modules, in scope through the
-- import of the uniform form of Stacks 03DW, leaves the universe of the derived category
-- undetermined; the statements below are about the instance at the universe of the schemes.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`D_QCoh(𝒪_X)` is a strictly full saturated triangulated subcategory of `D(𝒪_X)`**, for every
algebraic space `X` (Stacks 06UQ): it is closed under isomorphisms, triangulated, and stable
under retracts. -/
theorem qcohDerivedProp_isTriangulated_saturated (X : AlgebraicSpaces B S hS) :
    (qcohDerivedProp B S hS X).IsClosedUnderIsomorphisms ∧
      (qcohDerivedProp B S hS X).IsTriangulated ∧
      (qcohDerivedProp B S hS X).IsStableUnderRetracts :=
  quasicoherentDerivedCategory_isTriangulated_saturated_of_h03DW B S hS X.1 X.2
    (fun q hq hk W hW =>
      surjective_val_app_of_epi_of_kernel_isCartesian_unconditional B S hS X q hq hk W hW)

/-- `D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`. -/
instance qcohDerivedProp_isTriangulated (X : AlgebraicSpaces B S hS) :
    (qcohDerivedProp B S hS X).IsTriangulated :=
  (qcohDerivedProp_isTriangulated_saturated B S hS X).2.1

/-- `D_QCoh(𝒪_X)` is closed under isomorphisms in `D(𝒪_X)`. -/
instance qcohDerivedProp_isClosedUnderIsomorphisms (X : AlgebraicSpaces B S hS) :
    (qcohDerivedProp B S hS X).IsClosedUnderIsomorphisms :=
  (qcohDerivedProp_isTriangulated_saturated B S hS X).1

end AlgebraicGeometry.Space

end
