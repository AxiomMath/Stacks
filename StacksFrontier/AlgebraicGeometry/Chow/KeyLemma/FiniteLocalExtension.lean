module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.FiniteLocalExtension.BoundedDenominator
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.FiniteLocalExtension.GluedSubalgebra
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.FiniteLocalExtension.PrescribedLocalizations

/-!
# Simultaneously preparing finite extensions at height-one primes

A finite collection of finite modifications of a Noetherian local ring at the prime ideals
above a nonzerodivisor can be obtained by localizing one finite local modification of the
original ring. The global modification has the same residue field and is supported on the
vanishing locus of the nonzerodivisor.

## Main results

* `exists_finite_local_extension_with_prescribed_localizations` constructs the simultaneous
  finite local extension.

## Implementation notes

An extension being killed modulo its base ring by a power of `t` is expressed without choosing
a cokernel: every element becomes an element of the base after multiplication by that power.
The identification of residue fields is expressed by bijectivity of the canonical residue-field
map. The prescribed isomorphisms after localization are stated by the universal property
`IsLocalization`; this retains their compatibility with the maps from the original ring.

The construction glues the prescribed local algebras inside the ambient product
`A[1/t] × ∏ᵢ Bᵢ`, cuts it down to the elements whose denominators are bounded by a fixed power
of `t`, and then enlarges a finite subalgebra of that until it localizes correctly at each of
the finitely many primes. Everything in this file apart from the main theorem is an auxiliary
step of that construction and is therefore `private`.

Since the statement concerns commutative rings rather than schemes, it is placed in the root
namespace, as a Mathlib file on local rings and localizations would be.

## References

* [Stacks Project, Tag 0EAV](https://stacks.math.columbia.edu/tag/0EAV)
-/
