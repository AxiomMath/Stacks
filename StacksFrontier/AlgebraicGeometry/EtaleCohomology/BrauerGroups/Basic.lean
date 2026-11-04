module

public import StacksCore.Algebra.BrauerGroup.Basic
public import StacksCore.Algebra.Split.CentralSimple
public import StacksCore.Tactic.StacksAttribute

/-!
# Central simple algebras and the Brauer group of a field

The Brauer group of a field is the group of Brauer-equivalence classes of finite-dimensional
central simple algebras, with multiplication induced by tensor product. This file collects the
three basic facts that make that definition work: the equivalent characterizations of a finite
central simple algebra, the identification of the tensor product of such an algebra with its
opposite as a matrix algebra — which supplies the inverse class — and the group structure
itself.

## Main results

* `Algebra.isCentralSimple_tfae` gives the six equivalent characterizations of a finite central
  simple algebra: by its centre and two-sided ideals, by becoming a matrix algebra over an
  algebraic closure, over a separable closure, or over a finite Galois extension, and by being
  a matrix algebra over a finite central division algebra.
* `Algebra.IsSplit.matrix_size_eq_degree` identifies the matrix size in a splitting with the
  degree of the algebra.
* `mulLeftRight_bijective_of_simple` says that the canonical left-right multiplication map of a
  central simple algebra onto its linear endomorphisms is bijective.
* `BrauerGroup.instCommGroup` is the commutative group structure, `BrauerGroup.mk_mul_mk`
  records that the group law is tensor product, and `BrauerGroup.mk_self_eq_one`,
  `BrauerGroup.mk_matrix_eq_one` identify the neutral class.

## Implementation notes

The statements of all three results are already in the library, so this file registers the
existing declarations rather than restating them. A finite Galois extension is represented as
an intermediate field of a chosen algebraic closure. The displayed map of the inverse
construction is Mathlib's `AlgHom.mulLeftRight`; saying that this algebra homomorphism is an
isomorphism is expressed by bijectivity of its underlying function.

## References

* [Stacks Project, Tag 03R2](https://stacks.math.columbia.edu/tag/03R2)
* [Stacks Project, Tag 03R4](https://stacks.math.columbia.edu/tag/03R4)
* [Stacks Project, Tag 03R5](https://stacks.math.columbia.edu/tag/03R5)
* [Stacks Project, Tag 0753](https://stacks.math.columbia.edu/tag/0753)
-/

@[expose] public section

add_to_stacks 03R2 "the six equivalent characterizations" Algebra.isCentralSimple_tfae

add_to_stacks 03R2 "the integer d is the degree" Algebra.IsSplit.matrix_size_eq_degree

add_to_stacks 03R4 mulLeftRight_bijective_of_simple

add_to_stacks 03R5 BrauerGroup
add_to_stacks 03R5 BrauerGroup.mk
add_to_stacks 03R5 BrauerGroup.instCommGroup
add_to_stacks 03R5 BrauerGroup.mk_mul_mk
add_to_stacks 03R5 BrauerGroup.mk_self_eq_one
add_to_stacks 03R5 BrauerGroup.mk_matrix_eq_one
