module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# Algebraic space structures on a closed set of points, and the reduction

Let `X` be an algebraic space over a scheme `S` and let `Z` be a closed subset of its space of
points. An *algebraic space structure* on `Z` is a closed subspace of `X` whose set of points is
`Z`; among these there is exactly one which is reduced, the *reduced induced structure*, and the
reduced induced structure on the whole of `|X|` is the *reduction* of `X`.

The reduced induced structure is the subspace constructed for Stacks 03IQ,
`AlgebraicGeometry.Space.reducedClosedSubspace`, and nothing is redefined here: this file names
the notion of a structure on `Z`, records that the subspace of Stacks 03IQ is one, and
introduces the reduction as its value at the whole point set.

## Main definitions

* `AlgebraicGeometry.Space.IsAlgebraicSpaceStructure`: a subfunctor is an algebraic space
  structure on a closed set of points when it is a closed subspace with that set of points.
* `AlgebraicGeometry.Space.reduction`: the reduction of an algebraic space.

## Main results

* `isAlgebraicSpaceStructure_reducedClosedSubspace`, in the namespace
  `AlgebraicGeometry.Space`: the subspace of Stacks 03IQ is an algebraic space structure on the
  closed set it is built from.
* `AlgebraicGeometry.Space.existsUnique_isAlgebraicSpaceStructure_isReduced`: a closed set of
  points carries exactly one reduced algebraic space structure, the reduced induced one.
* `AlgebraicGeometry.Space.range_pointsMap_ι_reduction` and
  `AlgebraicGeometry.Space.surjective_pointsMap_ι_reduction`: the reduction has the same points as
  the space.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_reduction`: the reduction is reduced.
* `AlgebraicGeometry.Space.eq_reduction` and
  `AlgebraicGeometry.Space.eq_of_isAlgebraicSpaceStructure_isReduced`: a reduced algebraic space
  structure on a closed set of points is the one of Stacks 03IQ, and on the whole point set it is
  the reduction.
* `AlgebraicGeometry.Space.existsUnique_reduction`: the reduction is the unique reduced algebraic
  space structure on the whole point set.

## Implementation notes

Every statement below is unconditional. The closed-subspace clause of the structure is the one
whose proof needs a
descent: representability of the inclusion is obtained by descending an ideal along a surjective
étale chart, which asks for effective descent at the closed immersions, and that is supplied by
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace`. The weaker variants which
instead take that descent as an argument, named `…_of_closedImmersionDescent`, are kept beside
the unconditional statements for consumers which already carry it, and, following
`StacksFrontier/AlgebraicGeometry/Spaces/ReducedClosedSubspace.lean`, none of them carries
`@[stacks 047X]`: the statement of that definition has no descent hypothesis.

Uniqueness is stated twice, once against the subspace of Stacks 03IQ and once against the
reduction, because the two are convenient in different places: the first is what identifies a
subspace one has constructed, the second is the form a consumer of the reduction wants.

The point topology is `AlgebraicGeometry.Space.pointTopology`, installed as a local instance as
in `StacksFrontier/AlgebraicGeometry/Spaces/ReducedClosedSubspace.lean`, so that `IsClosed` and
`isClosed_univ` read as ordinary topological statements.

## References

* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 047X.** An *algebraic space structure* on a closed set `Z` of points of an
algebraic space `X` over `S` is a closed subspace of `X` whose set of points is `Z`. -/
@[stacks 047X "algebraic space structure on a closed set of points"]
def IsAlgebraicSpaceStructure {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Z : Set (points B S hS X)) (Z' : Subfunctor X) : Prop :=
  IsClosedSubspace B S hS Z' ∧ Set.range (pointsMap B S hS Z'.toFunctor Z'.ι) = Z

/-- An algebraic space structure on a closed set of points is a closed subspace. -/
theorem IsAlgebraicSpaceStructure.isClosedSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z : Set (points B S hS X)} {Z' : Subfunctor X}
    (h : IsAlgebraicSpaceStructure B S hS Z Z') :
    IsClosedSubspace B S hS Z' :=
  h.1

/-- The set of points of an algebraic space structure on `Z` is `Z`. -/
theorem IsAlgebraicSpaceStructure.range_pointsMap_ι
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z : Set (points B S hS X)} {Z' : Subfunctor X}
    (h : IsAlgebraicSpaceStructure B S hS Z Z') :
    Set.range (pointsMap B S hS Z'.toFunctor Z'.ι) = Z :=
  h.2

/-- **Stacks 047X, the reduced induced structure.** The subspace of Stacks 03IQ on a closed set
of points is an algebraic space structure on that set. That it is moreover reduced is
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace`, and that it is
the only reduced one is
`AlgebraicGeometry.Space.existsUnique_isAlgebraicSpaceStructure_isReduced`. -/
@[stacks 047X "the reduced induced structure"]
theorem isAlgebraicSpaceStructure_reducedClosedSubspace
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (Z : Set (points B S hS X)) (hZ : IsClosed Z) :
    IsAlgebraicSpaceStructure B S hS Z (reducedClosedSubspace B S hS X hX Z hZ) :=
  ⟨isClosedSubspace_reducedClosedSubspace B S hS X hX Z hZ,
    range_pointsMap_ι_reducedClosedSubspace B S hS X hX Z hZ⟩

/-- The subspace of Stacks 03IQ is an algebraic space structure on the closed set it is built
from, with effective descent for closed immersions along the surjective étale morphisms of the
site taken as an argument. The statement to prefer is
`AlgebraicGeometry.Space.isAlgebraicSpaceStructure_reducedClosedSubspace`, which needs no such
argument.

This declaration does **not** carry `@[stacks 047X]`: the statement of that definition has no
descent hypothesis. -/
theorem isAlgebraicSpaceStructure_reducedClosedSubspace_of_closedImmersionDescent
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (Z : Set (points B S hS X)) (hZ : IsClosed Z)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})) :
    IsAlgebraicSpaceStructure B S hS Z (reducedClosedSubspace B S hS X hX Z hZ) :=
  ⟨isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent B S hS X hX Z hZ hdesc,
    range_pointsMap_ι_reducedClosedSubspace B S hS X hX Z hZ⟩

/-- A reduced algebraic space structure on a closed set of points is the subspace of
Stacks 03IQ. No descent hypothesis is needed: this is the uniqueness half of Stacks 03IQ. -/
theorem eq_of_isAlgebraicSpaceStructure_isReduced
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (Z : Set (points B S hS X)) (hZ : IsClosed Z) (Z' : Subfunctor X)
    (hZ' : IsAlgebraicSpaceStructure B S hS Z Z')
    (hred : HasEtaleLocalProperty B S hS Z'.toFunctor (fun Y : Scheme.{u} => IsReduced Y)) :
    Z' = reducedClosedSubspace B S hS X hX Z hZ :=
  eq_reducedClosedSubspace B S hS X hX Z hZ Z' hZ'.1 hZ'.2 hred

/-- **Stacks 047X, the reduced induced structure characterized.** A closed set of points of an
algebraic space carries exactly one reduced algebraic space structure, namely the subspace of
Stacks 03IQ. This is what makes *the* reduced induced structure well defined. -/
@[stacks 047X "the reduced induced structure is the unique reduced one"]
theorem existsUnique_isAlgebraicSpaceStructure_isReduced
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (Z : Set (points B S hS X)) (hZ : IsClosed Z) :
    ∃! Z' : Subfunctor X,
      IsAlgebraicSpaceStructure B S hS Z Z' ∧
        HasEtaleLocalProperty B S hS Z'.toFunctor (fun Y : Scheme.{u} => IsReduced Y) :=
  ⟨reducedClosedSubspace B S hS X hX Z hZ,
    ⟨isAlgebraicSpaceStructure_reducedClosedSubspace B S hS X hX Z hZ,
      hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX Z hZ⟩,
    fun Z' hZ' => eq_of_isAlgebraicSpaceStructure_isReduced B S hS X hX Z hZ Z' hZ'.1 hZ'.2⟩

/-- **Stacks 047X, the reduction.** The *reduction* `X_red` of an algebraic space `X` over `S` is
the reduced induced algebraic space structure on the whole of its space of points: the subspace
of Stacks 03IQ at the closed set `Set.univ`. -/
@[stacks 047X "the reduction"]
noncomputable def reduction (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) : Subfunctor X :=
  reducedClosedSubspace B S hS X hX Set.univ isClosed_univ

/-- The reduction has every point of the space. -/
theorem range_pointsMap_ι_reduction (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) :
    Set.range (pointsMap B S hS (reduction B S hS X hX).toFunctor
      (reduction B S hS X hX).ι) = Set.univ :=
  range_pointsMap_ι_reducedClosedSubspace B S hS X hX Set.univ isClosed_univ

/-- The inclusion of the reduction is surjective on points. -/
theorem surjective_pointsMap_ι_reduction (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) :
    Function.Surjective (pointsMap B S hS (reduction B S hS X hX).toFunctor
      (reduction B S hS X hX).ι) :=
  Set.range_eq_univ.1 (range_pointsMap_ι_reduction B S hS X hX)

/-- The reduction is reduced, in the étale-local sense of Stacks 03E6. -/
theorem hasEtaleLocalProperty_isReduced_reduction (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) :
    HasEtaleLocalProperty B S hS (reduction B S hS X hX).toFunctor
      (fun Y : Scheme.{u} => IsReduced Y) :=
  hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX Set.univ isClosed_univ

/-- The reduction is an algebraic space structure on the whole point set. -/
theorem isAlgebraicSpaceStructure_reduction (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) :
    IsAlgebraicSpaceStructure B S hS (Set.univ : Set (points B S hS X))
      (reduction B S hS X hX) :=
  isAlgebraicSpaceStructure_reducedClosedSubspace B S hS X hX Set.univ isClosed_univ

/-- The reduction is an algebraic space structure on the whole point set, with effective descent
for closed immersions taken as an argument. The statement to prefer is
`AlgebraicGeometry.Space.isAlgebraicSpaceStructure_reduction`. -/
theorem isAlgebraicSpaceStructure_reduction_of_closedImmersionDescent
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})) :
    IsAlgebraicSpaceStructure B S hS (Set.univ : Set (points B S hS X))
      (reduction B S hS X hX) :=
  isAlgebraicSpaceStructure_reducedClosedSubspace_of_closedImmersionDescent B S hS X hX
    Set.univ isClosed_univ hdesc

/-- A reduced closed subspace with every point of the space is the reduction. -/
theorem eq_reduction (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (Z' : Subfunctor X) (hZ'c : IsClosedSubspace B S hS Z')
    (hZ'pt : Set.range (pointsMap B S hS Z'.toFunctor Z'.ι) = Set.univ)
    (hred : HasEtaleLocalProperty B S hS Z'.toFunctor (fun Y : Scheme.{u} => IsReduced Y)) :
    Z' = reduction B S hS X hX :=
  eq_of_isAlgebraicSpaceStructure_isReduced B S hS X hX Set.univ isClosed_univ Z'
    ⟨hZ'c, hZ'pt⟩ hred

/-- **Stacks 047X, the reduction characterized.** The reduction is the unique reduced algebraic
space structure on the whole space of points. -/
@[stacks 047X "the reduction is the unique reduced structure on the whole point set"]
theorem existsUnique_reduction (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) :
    ∃! Z' : Subfunctor X,
      IsAlgebraicSpaceStructure B S hS (Set.univ : Set (points B S hS X)) Z' ∧
        HasEtaleLocalProperty B S hS Z'.toFunctor (fun Y : Scheme.{u} => IsReduced Y) :=
  existsUnique_isAlgebraicSpaceStructure_isReduced B S hS X hX Set.univ isClosed_univ

/-- The reduction is the unique reduced algebraic space structure on the whole space of points,
with effective descent for closed immersions taken as an argument; it is used only for
existence. The statement to prefer is `AlgebraicGeometry.Space.existsUnique_reduction`. -/
theorem existsUnique_reduction_of_closedImmersionDescent
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})) :
    ∃! Z' : Subfunctor X,
      IsAlgebraicSpaceStructure B S hS (Set.univ : Set (points B S hS X)) Z' ∧
        HasEtaleLocalProperty B S hS Z'.toFunctor (fun Y : Scheme.{u} => IsReduced Y) :=
  ⟨reduction B S hS X hX,
    ⟨isAlgebraicSpaceStructure_reduction_of_closedImmersionDescent B S hS X hX hdesc,
      hasEtaleLocalProperty_isReduced_reduction B S hS X hX⟩,
    fun Z' hZ' => eq_reduction B S hS X hX Z' hZ'.1.1 hZ'.1.2 hZ'.2⟩

end AlgebraicGeometry.Space

end
