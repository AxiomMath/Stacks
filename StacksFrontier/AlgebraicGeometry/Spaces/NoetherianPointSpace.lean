module

public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.Topology.Noetherian.Image
public import StacksFrontier.Topology.Noetherian.QuasiCompactLocally

/-!
# The point space of a (locally) Noetherian algebraic space

Tag 04ZF says that the space of points of a locally Noetherian algebraic space is a locally
Noetherian topological space, and that it is a Noetherian topological space as soon as the
algebraic space is in addition quasi-compact.

Both parts are proved in `StacksFrontier/AlgebraicGeometry/Spaces/NoetherianPoints.lean`, as
`AlgebraicGeometry.Space.isLocallyNoetherianSpace_of_isLocallyNoetherian` and
`AlgebraicGeometry.Space.noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian`.

What this file records is that the point space of a quasi-compact locally Noetherian
algebraic space has finitely many connected components, which is one of the two hypotheses of
`AlgebraicGeometry.Space.nonempty_componentwiseArtinianFactorization`;  the componentwise
factorization of Tag 0DMY is restated here with that hypothesis discharged.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.finite_connectedComponents_points`: the point space of a
  quasi-compact locally Noetherian algebraic space has finitely many connected components.
* `AlgebraicGeometry.Space.nonempty_componentwiseArtinianFactorization_of_isQuasiCompactSpace`
  is `AlgebraicGeometry.Space.nonempty_componentwiseArtinianFactorization` with the finiteness
  of the set of connected components replaced by the geometric hypotheses that Tag 0DMY draws
  it from.  Its remaining hypothesis, artinianness of the ring of global functions, is the
  part of Tag 0DMY that rests on Tag 08AS and is not available in this library.

## Implementation notes

Local Noetherianity of a topological space is
`TopologicalSpace.IsLocallyNoetherianSpace`, as Mathlib has no such notion;  Noetherianity is
Mathlib's `TopologicalSpace.NoetherianSpace`.

The point topology is `AlgebraicGeometry.Space.pointTopology`, installed as a local instance
as elsewhere in this directory, so that the statements are about the topology of Tag 03BX and
do not wait on the existence-and-uniqueness statement of that tag.

Local Noetherianity of an algebraic space is the étale-local scheme property
`AlgebraicGeometry.Space.HasEtaleLocalProperty` of `AlgebraicGeometry.IsLocallyNoetherian`, as
in `AlgebraicGeometry.Space.IsNoetherian`;  it is a some-chart condition, which is all that is
used, so no locality of the property for the étale precoverage is needed here.

## References

* [Stacks Project, Tag 04ZF](https://stacks.math.columbia.edu/tag/04ZF)
* [Stacks Project, Tag 04Z8](https://stacks.math.columbia.edu/tag/04Z8)
* [Stacks Project, Tag 04ZB](https://stacks.math.columbia.edu/tag/04ZB)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The space of points of a quasi-compact locally Noetherian algebraic space over `S` has
finitely many connected components, being a Noetherian topological space. -/
theorem finite_connectedComponents_points (hF : IsAlgebraicSpace B S hS F)
    (hqc : IsQuasiCompactSpace B S hS F)
    (hN : HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    Finite (ConnectedComponents (points B S hS F)) :=
  have _ : NoetherianSpace (points B S hS F) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS _ hF hqc hN
  NoetherianSpace.finite_connectedComponents _

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

section Factorization

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)

/-- **The componentwise factorization of Tag 0DMY, conditional only on artinianness of the
ring of global functions.**  The global functions of a quasi-compact locally Noetherian
algebraic space over a field split as the product of the rings of functions on the charts of
each connected component, each factor Artinian and local, and the splitting is simultaneous
restriction.

This is `AlgebraicGeometry.Space.nonempty_componentwiseArtinianFactorization` with its
finiteness hypothesis on the set of connected components replaced by the hypotheses Tag 0DMY
derives it from: Tag 04ZL makes a proper algebraic space over a field quasi-compact and
locally Noetherian, and Tag 04ZF then makes its point space Noetherian.

The remaining hypothesis is artinianness of the whole ring of global functions, which
Tag 0DMY gets from its own finite-dimensionality clause, hence from Tag 08AS;  that is the
part of Tag 0DMY this library does not have. -/
theorem nonempty_componentwiseArtinianFactorization_of_isQuasiCompactSpace
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X)
    (hqc : IsQuasiCompactSpace B (Spec (.of k)) hS X)
    (hN : HasEtaleLocalProperty B (Spec (.of k)) hS X
      (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hart : IsArtinianRing (globalFunctions B (Spec (.of k)) hS X)) :
    Nonempty (ComponentwiseArtinianFactorization k B hS X) :=
  have _ : Finite (ConnectedComponents (points B (Spec (.of k)) hS X)) :=
    finite_connectedComponents_points B (Spec (.of k)) hS hX hqc hN
  nonempty_componentwiseArtinianFactorization k B hS X hX hart

end Factorization

end AlgebraicGeometry.Space

end
