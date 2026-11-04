module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# The reduced sheaf of ideals cutting out a closed set of points

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`T ⊆ |X|` be a closed subset of its set of points.  This file produces a quasi-coherent sheaf of
ideals `ℐ ⊆ 𝒪_X` whose zero locus is exactly `T`: the defining ideal sheaf of the reduced closed
subspace supported on `T`.

Every statement about the support of a coherent module which is formulated through a sheaf of
ideals — for instance Stacks 07UK, in the form
`AlgebraicGeometry.Space.exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus` —
asks for such a sheaf of ideals, while the geometric input is a closed *set* of points.  This
file is the translation between the two.

## Main definitions

* `AlgebraicGeometry.Space.reducedIdealSheaf`: the defining ideal sheaf of the reduced closed
  subspace on a closed set of points.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_reducedIdealSheaf`: it is quasi-coherent on the
  small étale site.
* `AlgebraicGeometry.Space.idealZeroLocus_reducedIdealSheaf`: its zero locus is the given closed
  set.
* `AlgebraicGeometry.Space.exists_isQuasicoherentOnSite_idealZeroLocus_eq`: the two previous
  statements packaged as the existence of a quasi-coherent sheaf of ideals cutting out a given
  closed set of points.

## Implementation notes

Three known inputs are composed.  Stacks 03IQ,
`AlgebraicGeometry.Space.reducedClosedSubspace`, builds the reduced closed subspace on `T` and
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace` shows it is a closed subspace,
so it is an element of `AlgebraicGeometry.Space.ClosedSubspaces`; Stacks 03MB,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf`, makes the kernel of its
structure map a quasi-coherent sheaf of ideals; and
`AlgebraicGeometry.Space.range_pointsMap_ι_eq_idealZeroLocus` identifies the point set of a
closed subspace with the zero locus of its defining ideal sheaf, which for the reduced closed
subspace is `T` by `AlgebraicGeometry.Space.range_pointsMap_ι_reducedClosedSubspace`.

Reducedness of the subspace is not used; it enters only through the construction, which is the
one of Stacks 03IQ because that is the one producing a closed subspace from a closed set of
points with no further hypothesis.

## References

* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 07UK](https://stacks.math.columbia.edu/tag/07UK)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.pointTopology

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The reduced closed subspace on a closed set of points of an algebraic space, as an element
of the type of closed subspaces. -/
noncomputable def reducedClosedSubspaces (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) : ClosedSubspaces B S hS X.1 :=
  ⟨reducedClosedSubspace B S hS X.1 X.2 T hT,
    isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 T hT⟩

/-- The sheaf of ideals cutting out a closed set of points of an algebraic space: the defining
ideal sheaf of the reduced closed subspace supported on that set. -/
noncomputable def reducedIdealSheaf (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) :
    (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule :=
  definingIdealSheaf B S hS X (reducedClosedSubspaces B S hS X T hT)

/-- **The sheaf of ideals cutting out a closed set of points is quasi-coherent.**  It is the
defining ideal sheaf of a closed subspace, and those are quasi-coherent by Stacks 03MB. -/
theorem isQuasicoherentOnSite_reducedIdealSheaf (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) :
    (reducedIdealSheaf B S hS X T hT).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_definingIdealSheaf B S hS X (reducedClosedSubspaces B S hS X T hT)

/-- **The zero locus of the sheaf of ideals cutting out a closed set of points is that set.**
The point set of a closed subspace is the zero locus of its defining ideal sheaf, and the point
set of the reduced closed subspace on `T` is `T`. -/
theorem idealZeroLocus_reducedIdealSheaf (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) :
    idealZeroLocus B S hS X (reducedIdealSheaf B S hS X T hT) = T :=
  (range_pointsMap_ι_eq_idealZeroLocus B S hS X
    (reducedClosedSubspaces B S hS X T hT)).symm.trans
      (range_pointsMap_ι_reducedClosedSubspace B S hS X.1 X.2 T hT)

/-- **Every closed set of points of an algebraic space is the zero locus of a quasi-coherent
sheaf of ideals.** -/
@[stacks 03IP "a section, not a lemma: a closed set is cut out by a quasi-coherent sheaf of ideals"]
theorem exists_isQuasicoherentOnSite_idealZeroLocus_eq (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) :
    ∃ I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule,
      I.toSheafOfModules.IsQuasicoherentOnSite ∧ idealZeroLocus B S hS X I = T :=
  ⟨reducedIdealSheaf B S hS X T hT, isQuasicoherentOnSite_reducedIdealSheaf B S hS X T hT,
    idealZeroLocus_reducedIdealSheaf B S hS X T hT⟩

end AlgebraicGeometry.Space

end
