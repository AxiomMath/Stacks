module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Reduction
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# A scheme covered by finitely many affine closed subschemes is affine

[Stacks, Tag 09NL](https://stacks.math.columbia.edu/tag/09NL) reads: *let `X` be a scheme which
is set theoretically the union of finitely many affine closed subschemes; then `X` is affine*.
It puts no hypothesis on the ambient scheme, and neither does either statement proved here.

`StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Reduction` splits the tag into two facts. The
first, which it proves for every `X`, is that the reduced induced closed subscheme
`X.nilradical.subscheme` is affine; the second is that `X` is a thickening of that subscheme.
What joins them is [Stacks, Tag 06AD] — a thickening of an affine scheme is affine — in the
form `Stacks.Thickenings.isAffine_of_isThickening`, which
`StacksFrontier.AlgebraicGeometry.Thickenings.Affine` proves by exhibiting a thickening as a finite
surjective morphism, so with no cohomological input and no hypothesis of its own. Composing the
two gives the tag outright.

## Main results

* `Stacks.AffineClosedUnion.isAffine_of_isClosedImmersion_iUnion_unconditional`: [Stacks, Tag
  09NL], with the covering written as a union of the ranges of the closed immersions.
* `Stacks.AffineClosedUnion.isAffine_of_surjective_sigmaDesc_unconditional`: [Stacks, Tag 09NL],
  with the covering written as in the tag, as surjectivity of the morphism from the coproduct.

## Implementation notes

The two statements of `StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Reduction` reach the same
conclusion from the same covering together with a surjectivity of global sections along
`X.nilradical.subschemeι`. That surjectivity is what `Stacks.Thickenings.isAffine_of_isThickening`
supplies, so the statements here ask for the covering alone.

## References

* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 09NL](https://stacks.math.columbia.edu/tag/09NL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.AffineClosedUnion

variable {X : Scheme.{u}}

/-- **[Stacks, Tag 09NL].** A scheme which is set theoretically the union of finitely many
affine closed subschemes is affine. Nothing is assumed about the ambient scheme.

Its reduced induced closed subscheme is affine by
`Stacks.AffineClosedUnion.isAffine_nilradical_subscheme_of_isClosedImmersion_iUnion`, and `X` is
a thickening of that subscheme by
`Stacks.AffineClosedUnion.isThickening_subschemeι_nilradical`, so [Stacks, Tag 06AD] in the form
`Stacks.Thickenings.isAffine_of_isThickening` gives affineness of `X` itself. -/
@[stacks 09NL]
theorem isAffine_of_isClosedImmersion_iUnion_unconditional {ι : Type*} [Finite ι]
    {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    [∀ i, IsAffine (Z i)] (hcov : ⋃ i, Set.range (f i).base = Set.univ) : IsAffine X :=
  have := isAffine_nilradical_subscheme_of_isClosedImmersion_iUnion f hcov
  Stacks.Thickenings.isAffine_of_isThickening (isThickening_subschemeι_nilradical X)

/-- **[Stacks, Tag 09NL] in the tag's own vocabulary.** The covering is surjectivity of the
morphism from the coproduct of the affine closed subschemes, as the tag states it; it is the
same hypothesis as a union of ranges by
`Stacks.AffineClosedUnion.surjective_sigmaDesc_iff`. -/
@[stacks 09NL]
theorem isAffine_of_surjective_sigmaDesc_unconditional {ι : Type v} [Finite ι]
    {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ X) [∀ i, IsAffine (Z i)]
    [∀ i, IsClosedImmersion (f i)] [hsurj : Surjective (Sigma.desc f)] : IsAffine X :=
  have : Small.{u} ι := inferInstance
  isAffine_of_isClosedImmersion_iUnion_unconditional f ((surjective_sigmaDesc_iff f).mp hsurj)

end Stacks.AffineClosedUnion

end
