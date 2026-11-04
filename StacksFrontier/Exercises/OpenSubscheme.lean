module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Geometry.RingedSpace.SheafedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction to an open subset, open subschemes and open immersions

An open subset of a ringed space, with the subspace topology and the restricted structure
sheaf, is again a ringed space, and it comes with a canonical morphism to the original space.
The same holds for locally ringed spaces and for schemes; an open subset of a scheme with its
restricted structure sheaf is an *open subscheme*, its canonical map to the ambient scheme is
an *open immersion*, and conversely every open immersion is isomorphic over its target to the
canonical map of an open subscheme.

Every assertion of the exercise is already a construction in Mathlib. A ringed space is a
sheafed space valued in commutative rings, and `AlgebraicGeometry.SheafedSpace.restrict` and
`AlgebraicGeometry.SheafedSpace.ofRestrict` construct the restriction and its canonical
morphism for sheafed spaces valued in any category and along any open embedding; the inclusion
of an open subset is an open embedding, so specializing gives the ringed-space statements.
`AlgebraicGeometry.LocallyRingedSpace.restrict` and `.ofRestrict` do the same for locally
ringed spaces, and `AlgebraicGeometry.Scheme.Opens.toScheme` and
`AlgebraicGeometry.Scheme.Opens.ι` for schemes.
`AlgebraicGeometry.Scheme.restrictFunctor` packages an open subscheme together with its
inclusion into the ambient scheme, and `AlgebraicGeometry.IsOpenImmersion.ofRestrict` says
those inclusions are open immersions. Mathlib's open-immersion predicate is stated in locally
ringed spaces; `AlgebraicGeometry.Scheme.Hom.isoOpensRange` and
`AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι` supply the factorization of an open
immersion through the open subscheme on its image, which is the source's description of open
immersions by an isomorphism with a canonical inclusion.

## References

* [Stacks Project, Tag 02EY](https://stacks.math.columbia.edu/tag/02EY)
-/

add_to_stacks 02EY "ringed_restriction" AlgebraicGeometry.SheafedSpace.restrict
add_to_sga "4 III 1.9.2" "more general" AlgebraicGeometry.SheafedSpace.restrict
add_to_ega "0 3.1.5" AlgebraicGeometry.SheafedSpace.restrict
add_to_ega "0 4.1.2" "special case" AlgebraicGeometry.SheafedSpace.restrict
add_to_stacks 02EY "canonical_morphism" AlgebraicGeometry.SheafedSpace.ofRestrict
add_to_ega "0 4.1.2" "special case" AlgebraicGeometry.SheafedSpace.ofRestrict
add_to_stacks 02EY "locally_ringed_restriction" AlgebraicGeometry.LocallyRingedSpace.restrict
add_to_sga "4 IV 14.1" "special case" AlgebraicGeometry.LocallyRingedSpace.restrict
add_to_ega "0 4.1.2" "special case" AlgebraicGeometry.LocallyRingedSpace.restrict
add_to_stacks 02EY "locally_ringed_restriction" AlgebraicGeometry.LocallyRingedSpace.ofRestrict
add_to_sga "4 IV 14.1" "special case" AlgebraicGeometry.LocallyRingedSpace.ofRestrict
add_to_ega "0 4.1.2" "special case" AlgebraicGeometry.LocallyRingedSpace.ofRestrict
add_to_ega "I 2.2.3" "more general" AlgebraicGeometry.LocallyRingedSpace.ofRestrict
add_to_ega "I 4.1.7" "special case" AlgebraicGeometry.LocallyRingedSpace.ofRestrict
add_to_stacks 02EY "scheme_restriction" AlgebraicGeometry.Scheme.Opens.toScheme
add_to_stacks 02EY "scheme_restriction" AlgebraicGeometry.Scheme.Opens.ι
add_to_stacks 02EY "open_terminology" AlgebraicGeometry.Scheme.restrictFunctor
add_to_stacks 02EY "open_terminology" AlgebraicGeometry.IsOpenImmersion
add_to_stacks 02EY "open_terminology" AlgebraicGeometry.IsOpenImmersion.ofRestrict
add_to_sga "2 XII 4.1" "i" AlgebraicGeometry.IsOpenImmersion.ofRestrict
add_to_sga "4 XVI 3.1" "more general" AlgebraicGeometry.IsOpenImmersion.ofRestrict
add_to_stacks 02EY "open_terminology" AlgebraicGeometry.Scheme.Hom.isoOpensRange
add_to_sga "6 VIII 1.3" AlgebraicGeometry.Scheme.Hom.isoOpensRange
add_to_ega "I 4.2.1" AlgebraicGeometry.Scheme.Hom.isoOpensRange
add_to_stacks 02EY "open_terminology" AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι
add_to_ega "I 4.2.1" "partial" AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι
