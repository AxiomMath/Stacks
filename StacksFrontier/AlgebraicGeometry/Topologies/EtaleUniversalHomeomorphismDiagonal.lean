module

public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleUniversalHomeomorphism

/-!
# The diagonal of a universal homeomorphism is a universal homeomorphism

`StacksFrontier.AlgebraicGeometry.Topologies.EtaleUniversalHomeomorphism` proves the two halves of
this separately — the diagonal of a universal homeomorphism is a closed immersion and it is
surjective on points, so that it is a thickening — and uses them through Stacks Project, Tag
025H to get the one consequence the proof of Tag 0BTY needs. This file records the conjunction
in the form of the class itself.

The point of doing so is that the library's results about universal homeomorphisms are stated
for the class, so without this they do not apply to a diagonal. In particular
`Stacks.Etale.existsUnique_hom_of_pullback_hom`,
`Stacks.Etale.etalePullback_full_of_universalHomeomorphism` and
`Stacks.Etale.etalePullback_faithful_of_universalHomeomorphism` become available for
`X ⟶ X ×_Y X`, as do stability of the class under base change and composition — which is what
identifies the iterated diagonals `X ⟶ X ×_Y X ×_Y X` of a cocycle argument as universal
homeomorphisms too.

## Main results

* `Stacks.Etale.universalHomeomorphism_diagonal` — the diagonal of a universal homeomorphism is
  a universal homeomorphism.

## Implementation notes

The proof reads the characterisation of Stacks Project, Tag 04DF in the direction
`integral + universally injective + surjective ⟹ universal homeomorphism`, and takes the three
inputs from the halves already in the library: the diagonal is a closed immersion, hence integral and a
monomorphism, hence universally injective; and it is surjective.

## References

* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
-/

@[expose] public section

namespace Stacks.Etale

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- **The diagonal of a universal homeomorphism is a universal homeomorphism.** A universal
homeomorphism is integral, hence affine, hence separated, so its diagonal is a closed immersion
and in particular integral and a monomorphism; and it is universally injective, which is exactly
surjectivity of its diagonal.

The two halves are `Stacks.Etale.isClosedImmersion_diagonal_of_universalHomeomorphism` and
`Stacks.Etale.surjective_diagonal_of_universalHomeomorphism`; this is their conjunction read
through the characterisation of Stacks Project, Tag 04DF. -/
theorem universalHomeomorphism_diagonal {S S' : Scheme.{u}} (g : S' ⟶ S)
    [UniversalHomeomorphism g] : UniversalHomeomorphism (pullback.diagonal g) := by
  have hci : IsClosedImmersion (pullback.diagonal g) :=
    isClosedImmersion_diagonal_of_universalHomeomorphism g
  rw [universalHomeomorphism_iff_integral_universallyInjective_surjective]
  exact ⟨inferInstance, inferInstance, ⟨surjective_diagonal_of_universalHomeomorphism g⟩⟩

end Stacks.Etale

end
