module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# The derived tensor product of two perfect complexes, in the internal-Hom spelling

A ringed space carries two derived tensor products on `D(𝒪_X)`, and
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso` identifies them.
[Stacks, Tag 09J5] — the derived tensor product of two perfect objects is perfect — is stated
over the second of the two, as
`AlgebraicGeometry.RingedSpace.isPerfect_canonicalDerivedTensorProduct`.  This file reads it over
the first, which is the one the derived internal Hom and the tensor–internal-Hom bijection of
[Stacks, Tag 08J8] are stated over.

That is the form the general case of [Stacks, Tag 08EH] needs: the perfect object `E₁` produced
there is `I ⊗^L_{𝒪_X} E` for the derived tensor product Tag 08J8 is stated over, `I` being the
perfect object that [Stacks, Tag 08DD] supplies and `E` the perfect object of the statement.

## Main results

* `AlgebraicGeometry.RingedSpace.isPerfect_interfaceDerivedTensorProduct`: the derived tensor
  product of two perfect objects of `D(𝒪_X)` is perfect, over
  `Stacks.SheafOfModules.derivedTensorProductFunctor`.

## Implementation notes

No project tag is attached.  Tag 09J5 already sits on
`AlgebraicGeometry.RingedSpace.isPerfect_derivedTensorProduct`, and the content below is that
theorem transported along a comparison of two spellings of one bifunctor together with
`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso`, not a second account of the tag.

## References

* [Stacks Project, Tag 09J5](https://stacks.math.columbia.edu/tag/09J5)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- **The derived tensor product of two perfect objects of `D(𝒪_X)` is perfect**, for the derived
tensor product the derived internal Hom is stated over.  This is
`AlgebraicGeometry.RingedSpace.isPerfect_canonicalDerivedTensorProduct`, which is [Stacks,
Tag 09J5] at the derived tensor product of [Stacks, Tag 06YU], read across
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso`. -/
theorem isPerfect_interfaceDerivedTensorProduct (K L : DerivedCategory (OXMod.{u, u} X))
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) K)
    (hL : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) L) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X)
      (((Stacks.SheafOfModules.derivedTensorProductFunctor
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj K).obj L) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := X)
    (((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso
      (Stacks.SheafOfModules.ringedSite X.sheaf)).app K).app L).symm
    (isPerfect_canonicalDerivedTensorProduct X K L hK hL)

end AlgebraicGeometry.RingedSpace

end
