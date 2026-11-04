module

public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSections.PullbackBranch
public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSections.ClosedSupportEquiv
public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSections.LocallyClosed

/-!
# Sections of an étale sheaf supported on a locally closed subscheme

Let `B` be a big étale site containing a scheme `S`, let `F` be an abelian sheaf on the small
étale site of `S` inside `B`, and let `Z` be a closed subscheme of an object `U'` of that site
whose image in a second object `U` is again closed. Then the sections of `F` over `U`
supported on that image correspond bijectively to the sections over `U'` supported on `Z`, and
the bijection is restriction wherever the two subsets have the same inverse image. Taking `Z`
only locally closed and running the bijection between two Zariski opens in which `Z` is
relatively closed produces the abelian group `H_Z(F)` of sections supported on `Z`, which is
the group the colimit of Stacks 0F6M is formed from.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sectionsSupportedOn` — the subgroup of sections whose support
  lies in a prescribed subset.
* `AlgebraicGeometry.SmallEtale.supportedSectionsOnOpen` — sections over a Zariski open of an
  object of the site, supported on the inverse image of a given subset.
* `AlgebraicGeometry.SmallEtale.supportOpen` — the canonical Zariski open `coborder Z` in
  which a locally closed `Z` is relatively closed.
* `AlgebraicGeometry.SmallEtale.supportedSections` — `H_Z(F)`, the sections supported on a
  locally closed `Z`, realized on `supportOpen`.
* `AlgebraicGeometry.SmallEtale.supportedSectionsMap` — the injective transition map for an
  inclusion `Z ⊆ Z'` of locally closed subsets with `Z` closed in `Z'`.
* `AlgebraicGeometry.SmallEtale.supportedSectionsSheafMap` — the action of a morphism of
  abelian sheaves on supported sections.

## Main results

* `AlgebraicGeometry.SmallEtale.supportSection_restrict_subset_preimage` bounds the support of
  a restricted section by the inverse image of the support.
* `AlgebraicGeometry.SmallEtale.supportedSectionsEquiv` is the canonical bijection of
  supported sections, and
  `AlgebraicGeometry.SmallEtale.supportedSectionsEquiv_restrict` identifies it with
  restriction on every étale test object on which the two inverse images agree.
* `AlgebraicGeometry.SmallEtale.locallyClosedSupportEquiv` and
  `AlgebraicGeometry.SmallEtale.locallyClosedSupportEquiv_restrict` transport that bijection,
  as an isomorphism of abelian groups, between any two admissible Zariski opens.
* `AlgebraicGeometry.SmallEtale.supportedSectionsOpenEquiv` identifies `H_Z(F)` with the
  supported sections on any admissible open.
* `AlgebraicGeometry.SmallEtale.supportedSectionsMap_injective`,
  `AlgebraicGeometry.SmallEtale.supportedSectionsMap_refl`,
  `AlgebraicGeometry.SmallEtale.supportedSectionsMap_comp` and
  `AlgebraicGeometry.SmallEtale.supportedSectionsMap_naturality` are the laws making
  `supportedSectionsMap` a functorial system of injections, natural in the sheaf.

## Implementation notes

The bijection is constructed by hand from the sheaf axiom: the inverse image of the closed
subscheme under the étale map `U' ⟶ U` splits off the given closed subscheme as a clopen
branch of the pullback, and a section supported on that branch is cut down and extended again
across the complementary open. The pullback computations use the fibre products of the small
étale site of Stacks 021D and Mathlib's description of the points of a fibre product of
schemes.

For the locally closed statement only the underlying *subset* of a locally closed subscheme
matters, since the support condition does not see nilpotents; the closed subscheme actually
fed to the bijection is the one cut out by the vanishing ideal of that closed subset, which is
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`. The ambient object is an arbitrary
object `W` of the small étale site, which is the extension of the notation discussed after
Stacks 0F6I. The canonical open on which `H_Z(F)` is realized is `coborder Z`, the largest
open in which `Z` is closed; `supportedSectionsOpenEquiv` is what makes any other admissible
choice of open give a canonically isomorphic group.

The names in this file live in `AlgebraicGeometry.SmallEtale` and are *not*
`AlgebraicGeometry.SheafOfModules.supportedSections`, which is the Zariski analogue for a
sheaf on a topological space and a closed subset.

## References

* [Stacks Project, Tag 0F6F](https://stacks.math.columbia.edu/tag/0F6F)
-/
