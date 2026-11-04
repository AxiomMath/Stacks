module

public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.Deformation.CofiberedPresentation.Criteria
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterionTangentSpaces

/-!
# The tangent-space hypothesis of Artin's criterion from finite-dimensional deformation categories

Artin's criterion (Stacks 07Y4), in the form
`AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms`, asks for the tangent-space half of
its axiom [3] as `AlgebraicGeometry.Stack.HasFiniteDimensionalTangentSpaces`: for every finite
type field `k` over `S`, every object `x₀` over `Spec(k)` and every presentation of the local ring
of `S` at the image point, the tangent space `T𝓕_{𝒳,k,x₀}` of the predeformation category, in the
unlifted model `Deformation.artinianTangentSpace` with its canonical vector space structure, is
finite dimensional.

The lemmas of the source verifying axiom [3] for a moduli stack (for instance Stacks 0D4S (1)
for polarized schemes) conclude instead that the predeformation category is a deformation
category with finite-dimensional tangent space and infinitesimal automorphisms, which is
`Deformation.IsFiniteDimensionalDeformationCategory`, phrased with the lifted model
`Deformation.tangentSpaceArtinian`. The second form implies the first, since the two models are
`k`-linearly equivalent by `Deformation.tangentSpaceArtinianLinearEquivUnlifted`; this is
`Stack.hasFiniteDimensionalTangentSpaces_of_isFiniteDimensionalDeformationCategory`.

## References

* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 07XJ](https://stacks.math.columbia.edu/tag/07XJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u uX

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end AlgebraicGeometry.Stack

end
