module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordStackInSetoids
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids
public import StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace

/-!
# Algebraic stacks and algebraic spaces

An algebraic stack is an algebraic space exactly when the objects of its fibre categories have
no nontrivial automorphisms, that is, when it is a stack in setoids. Conversely algebraic spaces,
and categories fibred in groupoids representable by them, are Deligne-Mumford stacks.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_iff_isStackInSetoids`: an algebraic
  stack is representable by an algebraic space if and only if it is a stack in setoids.

## Implementation notes

The two implications are
`AlgebraicGeometry.Stack.isStackInSetoids_of_isRepresentableByAlgebraicSpace` and
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids`, the latter proved
through part (3) of Tag 04S6.

## References

* [Stacks Project, Tag 03YR](https://stacks.math.columbia.edu/tag/03YR)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- An algebraic stack over `S` is representable by an algebraic space if and only if it is a
stack in setoids, that is, objects of its fibre categories have no nontrivial automorphisms. -/
@[stacks 03YR "the main result: an algebraic stack is an algebraic space exactly when its fibre
  categories are setoids"]
theorem isRepresentableByAlgebraicSpace_iff_isStackInSetoids
    (halg : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsRepresentableByAlgebraicSpace B S hS 𝒳 ↔
      𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) :=
  ⟨isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒳, fun h ↦
    isRepresentableByAlgebraicSpace_of_isStackInSetoids B S hS 𝒳 halg h⟩

end AlgebraicGeometry.Stack

add_to_stacks 03YR "representable by an algebraic space implies Deligne-Mumford"
  AlgebraicGeometry.Stack.isDeligneMumfordStack_of_isRepresentableByAlgebraicSpace
add_to_stacks 03YR "the category associated with an algebraic space is Deligne-Mumford"
  AlgebraicGeometry.Stack.isDeligneMumfordStack_fibredCategory
add_to_stacks 03YR "trivial inertia: the inertia criterion"
  CategoryTheory.RelativeInertia.π_isEquivalence_iff
