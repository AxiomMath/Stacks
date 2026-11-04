module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Irreducible components of a closed subspace

An *irreducible component* of a closed subspace `Y` of an algebraic space is an integral
closed subspace `Z ⊂ Y` whose set of points is an irreducible component of `|Y|`, and its
*generic point* is the generic point of that set. This is the third of the three equivalent
descriptions of an irreducible component — the other two being an irreducible component of
`|Y|` and the generic point of one — and is the one the theory of cycles uses, since a cycle
is a formal sum of integral closed subspaces.

## Main definitions

* `AlgebraicGeometry.Space.IsIrreducibleComponent`: an integral closed subspace supported on
  an irreducible component of the ambient algebraic space.
* `AlgebraicGeometry.Space.IsGenericPointOf`: a point of the ambient space is the generic
  point of the support of a subspace.

## Main results

There are no propositional results. Both definitions are abbreviations, so
`AlgebraicGeometry.Space.IsClosedSubspace`, `AlgebraicGeometry.Space.IsIntegralSpace`,
`irreducibleComponents` and `IsGenericPoint` are available to consumers directly.

## Implementation notes

Neither definition needs the good-space condition or the dimension function of the standing
situation for cycles: recognising a component is a purely topological condition on the set of
points, which is `AlgebraicGeometry.Space.points` with the topology
`AlgebraicGeometry.Space.pointTopology` of Stacks 03BX. A closed subspace is a subfunctor, so
its set of points is the range of `AlgebraicGeometry.Space.pointsMap` along its inclusion
rather than a subset of a single type.

Integrality of the subspace is `AlgebraicGeometry.Space.IsIntegralSpace` of Stacks 0AD4,
which is stated for an arbitrary presheaf and so does not consume the algebraic-space
component of the closed-subspace hypothesis.

## References

* [Stacks Project, Tag 0EE8](https://stacks.math.columbia.edu/tag/0EE8)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **Stacks 0EE8.** An *irreducible component* of an algebraic space `Y` over `S` is a closed
subspace which is an integral algebraic space and whose set of points is an irreducible
component of `|Y|`. -/
@[stacks 0EE8 "irreducible_component_of_closed_subspace"]
abbrev IsIrreducibleComponent (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hY : IsAlgebraicSpace B S hS Y)
    (Z : Subfunctor Y) : Prop :=
  IsClosedSubspace B S hS Z ∧ IsIntegralSpace B S hS Z.toFunctor ∧
    Set.range (pointsMap B S hS Z.toFunctor Z.ι) ∈ irreducibleComponents (points B S hS Y)

/-- **Stacks 0EE8.** A point of an algebraic space `Y` over `S` is the *generic point* of a
subspace `Z` when it is the generic point of the set of points of `Z`. -/
@[stacks 0EE8 "irreducible_component_of_closed_subspace"]
abbrev IsGenericPointOf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hY : IsAlgebraicSpace B S hS Y)
    (Z : Subfunctor Y) (ξ : points B S hS Y) : Prop :=
  IsGenericPoint ξ (Set.range (pointsMap B S hS Z.toFunctor Z.ι))

end AlgebraicGeometry.Space

end
