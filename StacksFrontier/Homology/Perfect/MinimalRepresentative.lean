module

public import StacksFrontier.Homology.Perfect.MinimalRepresentative.ElementarySplitting
public import StacksFrontier.Homology.Perfect.MinimalRepresentative.TrivialSummands
public import StacksFrontier.Homology.Perfect.MinimalRepresentative.LocalRing
public import StacksFrontier.Homology.Perfect.MinimalRepresentative.HomEquations
public import StacksFrontier.Homology.Perfect.MinimalRepresentative.PrincipalNeighbourhood

/-!
# Minimal representatives of perfect and pseudo-coherent complexes

Let `R` be a commutative ring. An object of the derived category `D(R)` which is representable
by a bounded complex of finite projective `R`-modules is not representable by only one such
complex, and two representatives need not be isomorphic as complexes. This module measures the
failure and then exploits it: near a prime `p` any two representatives agree up to localization
and up to trivial summands, and among all representatives there is a rank-minimal one, whose
degreewise ranks are the dimensions of the cohomology of the derived fibre at `p`.

Concretely, let `M` and `N` be bounded complexes of finite projective `R`-modules whose images
in `D(R)` are isomorphic, and let `p` be a prime of `R`. Then there is an `f ∉ p` such that,
after extension of scalars to the principal localization `R_f`, the complexes `M` and `N` become
isomorphic once a finite direct sum of trivial two-term complexes is adjoined to each side. Over
the local ring `R_p` the two complexes are already homotopy equivalent, and a rank-minimal free
model is split off at the maximal ideal; the content of the result is that both the identification
and the trivial summands needed to achieve it are defined on a whole principal open around `p`,
not merely at `p` itself.

## Main results

* `StacksDraft.Perfect.exists_away_iso_biprod_trivial_complexes` ([stacks 0F9V]): two bounded
  complexes of finite projective modules with isomorphic images in `D(R)` become isomorphic over
  some principal localization away from a given prime, after adjoining finite direct sums of
  trivial two-term complexes to both sides.
* `StacksDraft.Perfect.exists_unique_boundedAbove_free_complex_representing` ([stacks 0BCC]): a
  pseudo-coherent object over a local ring has a bounded above representative whose term in degree
  `i` is free of rank `dim_κ Hⁱ(K ⊗ᴸ_R κ)`, and that representative is unique up to isomorphism of
  complexes.
* `StacksDraft.Perfect.exists_unique_boundedAbove_free_complex_representing_of_datum`: its general
  form, for an arbitrary total derived extension-of-scalars datum.
* `StacksDraft.Perfect.exists_away_bounded_free_complex_representing` ([stacks 0BCD]): the same
  for a perfect object over any ring, on a principal neighbourhood of a given prime, the ranks
  being the dimensions of the cohomology of the derived fibre at that prime.
* `StacksDraft.Perfect.exists_away_bounded_free_complex_representing_of_datum`: its general form,
  for arbitrary total derived extension-of-scalars data.
* `StacksDraft.Perfect.exists_away_bounded_free_complex_representing_of_fibre_vanishing_below`
  ([stacks 0BYP]): a bounded below pseudo-coherent object whose derived fibre at `p` has no
  cohomology below `a` becomes perfect on a principal neighbourhood of `p`, with a representative
  concentrated in degrees `≥ a` and the same prescribed ranks.
  Its general form, for arbitrary total derived extension-of-scalars data, is the same name
  suffixed `_of_datum`.

## Implementation notes

A trivial two-term complex in consecutive degrees is presented as the mapping cone of the
identity of a rank-one free module concentrated in one degree. Such a cone is contractible, so
adjoining it changes nothing in the derived category; presenting it as a cone rather than as an
ad hoc two-term complex makes the contracting homotopy available directly, which is what the
splitting argument consumes. The rank-one free module is written `ULift R` so that it lies in the
same module category as the given complexes.

Finite direct sums of complexes are the finite products of the preadditive category of complexes,
and are handled through the biproduct `⊞` together with `piComparison`; the recursion over the
number of trivial summands is therefore a recursion on `Fin n` via `Fin.cons`.

Localization appears in two guises. Extension of scalars `ModuleCat.extendScalars (algebraMap R S)`
is what makes the localized complexes complexes of honest `S`-modules, so that a comparison
between them is an isomorphism of complexes; `ModuleCat.localizedModuleFunctor` is what carries
the finite-presentation machinery that lifts a map defined after localization back to a map over
`R`. The two are identified by a natural isomorphism, and the proof passes between them rather
than committing to either.

Over the local ring the splitting off of a rank-minimal free model is organised through
`FreeComplex`, a complex of finite free modules recorded by a rank function together with its
differential matrices; `exists_splitOff_elementaryComplex_of_hasInvertibleCoeff` removes one
  invertible matrix coefficient at a time, and the
recursion terminates because the total rank over the finite support strictly decreases. The
resulting residual complex has all differential entries in the maximal ideal, which is what makes
its reduction have zero differentials and hence makes a homotopy equivalence between reductions an
isomorphism, by Nakayama.

The derived tensor product `K ⊗ᴸ_R A` is the canonical total derived extension of scalars
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` of [stacks 064H], and that
is what the tagged results of this module speak about. Only the comparison natural transformation
carried by such a datum enters the proofs, so each tagged result is deduced from a general form
which quantifies over an arbitrary datum
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars f` and is therefore
applicable to any construction of the derived tensor product; those general forms carry the datum
as an explicit argument and are untagged, following the convention of
`exists_boundedAbove_lift_representing_of_datum`. Where a result needs a datum for a ring that is
only produced during the proof, as `[stacks 0BYP]` does, the datum is quantified after the element
it depends on: `[stacks 0BYP]` assumes the existence of a datum for every homomorphism of rings in
the ambient universe.

Since a pseudo-coherent object is represented by a bounded above complex of finite free modules and
a perfect one by a bounded complex of finite projectives, both of which compute the derived tensor
product, the preservation statements needed here — pseudo-coherence and perfectness under derived
base change, and the comparison between successive base changes and base change along a composite
— follow from the datum's `comparison_isIso_of_projective` alone; they are proved as private
lemmas, and the tags for them stay with their owning modules.

Descending an identification from the local ring at `p` to a principal neighbourhood is organised
by `HomExpression`, a syntax for the composition-algebra identities that a homotopy equivalence
satisfies. Each homomorphism has a denominator and each identity fails only up to a denominator, so
clearing denominators uniformly — `HomExpression.numerator`, with `HomExpression.degree` recording
how many were cleared — makes one element of `R` suffice for the whole finite system.

## References

* [Stacks Project, Tag 0F9V](https://stacks.math.columbia.edu/tag/0F9V)
* [Stacks Project, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 0BYP](https://stacks.math.columbia.edu/tag/0BYP)
-/
