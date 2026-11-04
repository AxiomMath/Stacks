module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphisms

/-!
# Cartesian squares of a flat family of morphisms of schemes

A morphism of flat families of morphisms of schemes, in the sense of Example
[Stacks Project, Tag 0E3T], records two cartesian squares: the target of the smaller family is
the base change of the target of the larger one along the map of bases, and the source of the
smaller family is the base change of the source of the larger one along the map of *targets*.
The second square is the one that is awkward to produce, because a family of morphisms carries
flatness of its source over its base and nothing over its target.

This file records that the second square is implied by the first together with cartesianness of
the source square over the base, which is the form in which gluing arguments deliver it: both
the source and the target of a glued family are cartesian over the glued base, and nothing is
known a priori about the glued source over the glued target.

## Main results

* `Deformation.Examples.isPullback_morphism_of_isPullback_toBase`: cartesianness of the source
  square over the target, from cartesianness of the source and target squares over the base.

## Implementation notes

The proof is the cancellation of the bottom square, `CategoryTheory.IsPullback.of_right`, with
the two `SchemeMorphismFamily.over_base` fields identifying the composites through the targets
with the structure morphisms of the sources. The commutation of the two morphisms being
deformed is a genuine hypothesis and not implied by the other two: it is the statement that the
candidate pair of maps is a map of families at all, and in a gluing argument it is what the
universal property of the pushout of the sources supplies.

## References

* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Deformation.Examples

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Cartesianness of the source square over the **target** -- the field
`Deformation.Examples.SchemeMorphismFamily.Hom.source_pullback` -- follows from cartesianness of
the source and of the target squares over the **base**, together with the commutation of the two
morphisms being deformed.

This is the cancellation of the bottom square: from
`Q.source = P.source ×_{baseSpec P.base} baseSpec Q.base` and
`Q.target = P.target ×_{baseSpec P.base} baseSpec Q.base` it gives
`Q.source = P.source ×_{P.target} Q.target`. -/
theorem isPullback_morphism_of_isPullback_toBase
    {P Q : SchemeMorphismFamily.{u, v} Λ k} {base : P.base ⟶ Q.base}
    {src : Q.source ⟶ P.source} {tgt : Q.target ⟶ P.target}
    (htgt : IsPullback tgt Q.targetToBase P.targetToBase (baseSpecMap base))
    (hsrc : IsPullback src Q.sourceToBase P.sourceToBase (baseSpecMap base))
    (hcomm : Q.morphism ≫ tgt = src ≫ P.morphism) :
    IsPullback Q.morphism src tgt P.morphism := by
  refine IsPullback.of_right ?_ hcomm htgt.flip
  have hQ : Q.morphism ≫ Q.targetToBase = Q.sourceToBase := Q.over_base
  have hP : P.morphism ≫ P.targetToBase = P.sourceToBase := P.over_base
  rw [hQ, hP]
  exact hsrc.flip

end Deformation.Examples

end
