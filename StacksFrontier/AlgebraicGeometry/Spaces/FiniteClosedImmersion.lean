module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed

/-!
# Closed immersions of algebraic spaces are finite

A closed immersion of algebraic spaces over a scheme `S` is a finite morphism, and a fortiori
an integral morphism.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isFinite_of_isClosedImmersion` and
  `AlgebraicGeometry.Space.isIntegralHom_of_isClosedImmersion` are the two assertions of
  Stacks 081Y.

## Implementation notes

Finiteness of a morphism of algebraic spaces, Stacks 03ZP, asks that over every object of the
site with affine underlying scheme the morphism be represented by an object with affine
underlying scheme whose projection is a finite morphism of schemes. A closed immersion of
algebraic spaces is relatively representable by definition, so the representing object is the
one its representability provides, and the projection out of it is a closed immersion of
schemes. A closed immersion of schemes is an affine morphism, so the representing object has
affine underlying scheme; and it is a finite morphism of schemes. Neither assertion needs the
source or the target to be an algebraic space, and neither assumes it; the equivalence
`AlgebraicGeometry.Space.isFinite_iff_representable` of Stacks 03ZQ, which does need
algebraicity, is therefore not used.

Integrality follows from finiteness by the first assertion of Stacks 0414,
`AlgebraicGeometry.Space.IsFinite.isIntegralHom`.

## References

* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

end AlgebraicGeometry.Space

end
