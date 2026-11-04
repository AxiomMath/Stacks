module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpTransfer
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.DominatedByFiniteOverBase
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ZeroSchemeSectionsNormalization

/-!
# Reduction to rational singularities goes up a finite separable extension

Let `A → B` be a finite injective local homomorphism of local normal Nagata domains of dimension
two whose extension of fraction fields is separable. If reduction to rational singularities is
possible for `A`, then it is possible for `B`. This is [Stacks, Tag 0AXL].

## Main results

* `AlgebraicGeometry.isReductionToRationalSingularitiesPossible_of_finite_of_isSeparable`:
  [Stacks, Tag 0AXL].

## Implementation notes

The proof of [Stacks, Tag 0AXL] has three ingredients:

* the reduction to a normal modification `Y` of `Spec B` finite over a normal modification `X` of
  `Spec A` — through [Stacks, Tag 0B49] and normalization — is
  `AlgebraicGeometry.isDominatedByFiniteOverBase`;
* the trace argument bounding `H¹(Y, 𝒪_Y)` by `n` copies of `H¹(X, 𝒪_X)` and the `d`-torsion of
  `H¹(Y, 𝒪_Y)`, with `d` the discriminant of a basis of the fraction field of `B` taken in `B`, is
  `AlgebraicGeometry.SeparableGoUp.isReductionToRationalSingularitiesPossible_of_isDominated`;
* the bound on that torsion, [Stacks, Tag 0AXJ] for `B` together with (0AXK), is
  `AlgebraicGeometry.exists_uniform_bound_length_quotient_baseToZeroSchemeSections`.

## References

* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
* [Stacks Project, Tag 0B49](https://stacks.math.columbia.edu/tag/0B49)
* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
-/


@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0AXL].** Let `A → B` be a finite injective local homomorphism of local normal
Nagata domains of dimension two such that the induced extension of fraction fields is separable.
If reduction to rational singularities is possible for `A`, then it is possible for `B`. -/
theorem isReductionToRationalSingularitiesPossible_of_finite_of_isSeparable (A B : Type u)
    [CommRing A] [IsLocalRing A] [IsNormalDomain A] [CommRing B] [IsLocalRing B]
    [IsNormalDomain B] [Algebra A B] [Module.Finite A B] [FaithfulSMul A B]
    [IsLocalHom (algebraMap A B)] (hA : IsNagataRing A) (hB : IsNagataRing B)
    (hdimA : ringKrullDim A = 2) (hdimB : ringKrullDim B = 2)
    (hsep : letI := FractionRing.liftAlgebra A (FractionRing B)
      Algebra.IsSeparable (FractionRing A) (FractionRing B))
    (hred : IsReductionToRationalSingularitiesPossible A) :
    IsReductionToRationalSingularitiesPossible B := by
  have : IsNagataRing B := hB
  exact SeparableGoUp.isReductionToRationalSingularitiesPossible_of_isDominated A B hsep
    (fun _ ha => exists_uniform_bound_length_quotient_baseToZeroSchemeSections hdimB ha)
    (isDominatedByFiniteOverBase A B hA hB hdimA hdimB) hred

end AlgebraicGeometry

end
