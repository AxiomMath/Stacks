module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic.CommonRefinement
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic.WellDefined
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic.ShortExact
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic.Additivity

/-!
# The Euler characteristic of a coherent triple: well-definedness and additivity

Let `A` be a Noetherian local ring, let `f` lie in its maximal ideal, and let `T` be a coherent
triple for `(A, f)`. A prepared extension `P` of `T` has a closed-fibre map whose kernel and
cokernel have finite length over `A`; the *Euler characteristic of `P`* is the length of the
cokernel minus the length of the kernel. This file proves that it is the same for any two
prepared extensions of the same triple, so that it is an invariant of the triple alone, and
that it is additive along a short exact sequence of coherent triples.

## Main definitions

* `Stacks.Algebraization.PreparedExtension.eulerCharacteristic`: the cokernel length minus the
  kernel length of the closed-fibre map of a prepared extension.
* `Stacks.Algebraization.CoherentTriple.Hom`: a morphism of coherent triples.
* `Stacks.Algebraization.CoherentTriple.Hom.comp`: the composition of two morphisms of coherent
  triples.
* `Stacks.Algebraization.CoherentTriple.ShortExact`: a short exact sequence of coherent
  triples, meaning one whose two component sequences are short exact.

## Main results

* `Stacks.Algebraization.PreparedExtension.eulerCharacteristic_eq`: **Stacks Tag 0F25**, two
  prepared extensions of the same coherent triple have the same Euler characteristic.
* `Stacks.Algebraization.preparedExtension_lengthIndex_eq`: the same statement with the two
  lengths written out, which is the form the proof produces.
* `Stacks.Algebraization.eulerCharacteristic_add_of_shortExact`: **Stacks Tag 0F26**, the Euler
  characteristic is additive along a short exact sequence of coherent triples.
* `Stacks.Algebraization.PreparedExtension.eulerCharacteristic_add_of_shortExact`: additivity
  for prepared extensions which already sit in a short exact sequence on `Spec A`, which is the
  last step of the proof of Tag 0F26.
* `Stacks.Algebraization.specSections_shortExact`: global sections on an affine scheme carry a
  short exact sequence of quasi-coherent modules to a short exact sequence of modules.

## Implementation notes

The source attaches the number to the triple, having first established that a prepared extension
exists (Stacks Tag 0F23) and chosen one. That existence statement is not in this library, so the
number is attached here to a prepared extension instead and the tag is carried by the statement
that the choice does not matter — which is exactly what the source's lemma asserts, and which
needs no existence input. Once Tag 0F23 lands, the Euler characteristic of the triple is the
`eulerCharacteristic` of any prepared extension and is well defined by the theorem below. For
the same reason additivity is stated for arbitrary prepared extensions of the three triples:
that form is equivalent to the source's equation between the three triples' invariants, and it
again needs no existence input.

Additivity is proved by replacing the given prepared extension of the middle triple by a better
one. The source shrinks it by a power of the maximal ideal and controls the intersection with
the kernel by Artin--Rees. That is not needed here: forming first the fibre product of the
middle prepared extension with the one of the third triple over the direct image of the third
triple's module turns the obstruction to filling in the closed-fibre ladder into a map defined
on the whole middle term, and such a map is killed by passing to the kernel of its adjoint --
the same device the proof of Tag 0F25 already uses. The kernel and the quotient by it then carry
prepared extensions of the outer two triples, and the three closed-fibre maps form a ladder of
short exact sequences of `A`-modules, on which `Module.lengthIndex_add_of_ladder` applies.

The proof compares two prepared extensions `P` and `Q` through a common coherent refinement: a
coherent module `G` mapping to both, agreeing with both over the punctured spectrum and over the
closed fibre. Passing to the closed fibre and to global sections turns each comparison map into a
map of `A`-modules with finite-length kernel and cokernel, and the length index is additive along
a composition (`Module.lengthIndex_comp`), so the two indices agree. The refinement is built as a
submodule of a biproduct, the corrections are controlled by the snake lemma, and finiteness of
the lengths involved comes from the modules being supported at the closed point.

## Files

* `CoherentTripleEulerCharacteristic.CommonRefinement`: the functors to the closed fibre, the
  auxiliary lemmas, and the common coherent refinement of two prepared extensions.
* `CoherentTripleEulerCharacteristic.WellDefined`: the Euler characteristic of a prepared
  extension, Tag 0F25, and the exactness of global sections and of reduction to the closed fibre.
* `CoherentTripleEulerCharacteristic.ShortExact`: morphisms and short exact sequences of coherent
  triples.
* `CoherentTripleEulerCharacteristic.Additivity`: the middle prepared extension of a short exact
  sequence and Tag 0F26.

## References

* [Stacks Project, Tag 0F25](https://stacks.math.columbia.edu/tag/0F25)
* [Stacks Project, Tag 0F26](https://stacks.math.columbia.edu/tag/0F26)
-/
