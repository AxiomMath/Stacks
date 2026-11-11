module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.QuasiSeparated
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib declarations carrying Stacks tags of Chapter 28 (Properties of Schemes)

This file records Stacks tags of Chapter 28 on the Mathlib declarations that state them.

* Mathlib defines a locally Noetherian scheme by condition (2) of Stacks 01OW (every affine
  open has Noetherian sections); the equivalence with the pointwise definition of Stacks 01OV
  is `AlgebraicGeometry.isLocallyNoetherian_iff_of_iSup_eq_top`.
* Mathlib has no separate notion of a Jacobson scheme: it is `JacobsonSpace X` on the
  underlying space, exactly as in Stacks 01P2.

## References

* [Stacks Project, Tag 01ON](https://stacks.math.columbia.edu/tag/01ON)
* [Stacks Project, Tag 01OV](https://stacks.math.columbia.edu/tag/01OV)
* [Stacks Project, Tag 01OW](https://stacks.math.columbia.edu/tag/01OW)
* [Stacks Project, Tag 01P2](https://stacks.math.columbia.edu/tag/01P2)
* [Stacks Project, Tag 01P3](https://stacks.math.columbia.edu/tag/01P3)
-/

@[expose] public section

add_to_stacks 01OK "Mathlib asks Γ(X, U) to be a domain for every nonempty open U; this is \
  equivalent to the affine-open condition by `AlgebraicGeometry.isIntegral_iff_forall_affineOpens`"
  AlgebraicGeometry.IsIntegral
add_to_stacks 01OL "(4): the definition of `IsReduced`, every Γ(X, U) is reduced"
  AlgebraicGeometry.IsReduced.component_reduced
add_to_stacks 01OL "(1) ⇒ (4): reduced local rings give reduced rings of sections"
  AlgebraicGeometry.isReduced_of_isReduced_stalk
add_to_stacks 01OL "(4) ⇒ (1): the local rings of a reduced scheme are reduced"
  AlgebraicGeometry.isReduced_stalk_of_isReduced
add_to_stacks 01OL "(2) ⇒ (4): reducedness can be checked on an open cover"
  AlgebraicGeometry.IsReduced.of_openCover
add_to_stacks 01OL "(2) ⇒ (4): an affine piece with reduced global sections is reduced"
  AlgebraicGeometry.isReduced_of_isAffine_isReduced

add_to_stacks 01ON "the equivalence for Mathlib's `IsIntegral`, which matches Stacks 01OK by \
  `AlgebraicGeometry.isIntegral_iff_forall_affineOpens`; the statement with the affine-open \
  condition is `AlgebraicGeometry.nonempty_and_forall_isDomain_iff_isReduced_and_irreducibleSpace`"
  AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced

add_to_stacks 01OV "part (1): Mathlib's definition is the equivalent condition 01OW (2)"
  AlgebraicGeometry.IsLocallyNoetherian
add_to_stacks 01OV "part (1): equivalence of Mathlib's definition with an affine cover, as in (1)"
  AlgebraicGeometry.isLocallyNoetherian_iff_of_iSup_eq_top
add_to_stacks 01OV "part (2): the definition of a Noetherian scheme" AlgebraicGeometry.IsNoetherian

add_to_stacks 01OW "part (1) ⇔ (2): Mathlib defines locally Noetherian by condition (2)"
  AlgebraicGeometry.IsLocallyNoetherian
add_to_stacks 01OW "part (1) ⇔ (3)" AlgebraicGeometry.isLocallyNoetherian_iff_of_iSup_eq_top
add_to_stacks 01OW "part (1) ⇔ (3), for an affine open cover"
  AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover
add_to_stacks 01OW "part (1) ⇔ (4)" AlgebraicGeometry.isLocallyNoetherian_iff_openCover
add_to_stacks 01OW "the `Moreover` clause, for any open immersion"
  AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion

add_to_stacks 01P2 "a Jacobson scheme is `JacobsonSpace` of its underlying space" JacobsonSpace

add_to_stacks 01P3 "the equivalence, on the underlying space of Spec R"
  PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace

-- On a quasi-compact and quasi-separated scheme, locally constructible subsets are constructible.
add_to_stacks 054E
  "stated for any topological space; on a qcqs scheme its hypotheses are instances"
  Topology.IsLocallyConstructible.isConstructible

end
