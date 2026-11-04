module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.RingedSpaceComorphism
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportSections

/-!
# A closed immersion of schemes, bundled as a closed quotient morphism of ringed spaces

The two conditions defining a closed quotient morphism of ringed spaces — a closed embedding of
underlying spaces and a surjective comorphism of structure sheaves — are proved for a closed
immersion of schemes in
`StacksFrontier.AlgebraicGeometry.ClosedImmersion.RingedSpaceComorphism`. This file does nothing
but package them into the structure that the adjunction between pushforward of sheaves of
modules and descent consumes.

## Main definitions

* `Stacks.ClosedImmersion.closedQuotientOfClosedImmersion`: the underlying morphism of ringed
  spaces of a closed immersion of schemes, as a
  `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.

## References

* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ClosedImmersion

/-- The underlying morphism of ringed spaces of a closed immersion of schemes, bundled as a
closed quotient morphism of ringed spaces. This is the input of the adjunction between
pushforward of sheaves of modules and descent, and it is the
`closedQuotientOfClosedImmersion` of the tagged statement. -/
def closedQuotientOfClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] :
    RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.{u} where
  X := X.toRingedSpace
  Z := Z.toRingedSpace
  i := i.toLRSHom.toShHom
  isClosedEmbedding := isClosedEmbedding_base_toShHom i
  isLocallySurjective := isLocallySurjective_c_toShHom i

end Stacks.ClosedImmersion

end
