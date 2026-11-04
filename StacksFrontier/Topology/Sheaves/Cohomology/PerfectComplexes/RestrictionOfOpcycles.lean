module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.LocalRepresentationOfDerivedMaps

/-!
# Restriction to an open subspace commutes with the opcycles

Let `(X, O_X)` be a ringed space, let `U` be an open of `X` and let `P` be a complex of
`O_X`-modules. Restriction to `U` is exact, so it commutes with the opcycles of `P`: the
degree-`k` opcycles of the restricted complex is the restriction of the degree-`k` opcycles
of `P`.

This is the comparison that turns the local conclusion of Stacks 08BL, which is about the
restriction of `Coker(P^{a-1} ⟶ P^a)` as a single module -- namely
`Stacks.Cohomology.OpcyclesFiniteFreeSummand`
`.exists_isDirectSummandOfFiniteFree_restrict_of_isFlat` --
into the hypothesis of the truncation criterion of Tag 08CP
(`Stacks.Cohomology.PerfectCanonicalTruncation.isPerfect_of_local_approximation_of_opcycles`),
which asks for the degree-`a` opcycles of the *restricted complex*.

## Main definitions

* `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictOpcyclesIso`: the opcycles comparison
  for restriction to an open subspace.

## Main results

* `AlgebraicGeometry.RingedSpace.PseudoCoherence`
  `.isDirectSummandOfFiniteFree_opcycles_restrictComplex`: the direct-summand condition
  transported across that comparison, which is the shape the truncation criterion consumes.

## Implementation notes

`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex P U` and
`((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P` are the same term, and
so are `((P.sc k).map (restrictModules X U)).opcycles` and
`(restrictComplex P U).opcycles k`; but the latter pair is only definitionally equal, so
Mathlib's `CategoryTheory.ShortComplex.mapOpcyclesIso` is repackaged here with its source spelled
in the second form, which is the one both consumers use.

Restriction to an open subspace is exact (Stacks 08C9). Right exactness is found by instance
search, restriction being a left adjoint. Left exactness is
`Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteLimits`, which is not
registered as an instance where it is proved, so it is seated locally here, exactly as
`StacksFrontier/Topology/Sheaves/Cohomology/TorAmplitude/OnARingedSpace.lean` does.

This is the ringed-space counterpart of `Stacks.SheafOfModules.restrictOpcyclesAlongIso`, which
is the same repackaging for restriction along an arrow of a ringed site.

## References

* [Stacks Project, Tag 08C9](https://stacks.math.columbia.edu/tag/08C9)
* [Stacks Project, Tag 08BL](https://stacks.math.columbia.edu/tag/08BL)
* [Stacks Project, Tag 08CP](https://stacks.math.columbia.edu/tag/08CP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace.PseudoCoherence

universe u

variable {X : RingedSpace.{u, u}}

attribute [local instance]
  Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteLimits

/-- **An exact functor commutes with the opcycles of a complex**; here the comparison for
restriction to an open subspace `U`, with its source spelled as the opcycles of the restricted
complex rather than as the opcycles of a mapped short complex. -/
def restrictOpcyclesIso (P : CochainComplex (OXMod.{u, u} X) ℤ) (U : Opens X.carrier) (k : ℤ) :
    HomologicalComplex.opcycles (restrictComplex P U) k ≅
      (restrictModules.{u, u} X U).obj (HomologicalComplex.opcycles P k) :=
  ShortComplex.mapOpcyclesIso (P.sc k) (restrictModules.{u, u} X U)

/-- **The degree-`k` opcycles of a restricted complex is a direct summand of a finite free
module as soon as the restriction of the degree-`k` opcycles is**, the two being identified by
`restrictOpcyclesIso`.

This is the exact shape in which the local conclusion of Stacks 08BL is handed to the truncation
criterion of Tag 08CP. -/
theorem isDirectSummandOfFiniteFree_opcycles_restrictComplex
    (P : CochainComplex (OXMod.{u, u} X) ℤ) (U : Opens X.carrier) (k : ℤ)
    (h : IsDirectSummandOfFiniteFree
      ((restrictModules.{u, u} X U).obj (HomologicalComplex.opcycles P k))) :
    IsDirectSummandOfFiniteFree (HomologicalComplex.opcycles (restrictComplex P U) k) :=
  isDirectSummandOfFiniteFree_of_iso (restrictOpcyclesIso P U k) h

end AlgebraicGeometry.RingedSpace.PseudoCoherence

end
