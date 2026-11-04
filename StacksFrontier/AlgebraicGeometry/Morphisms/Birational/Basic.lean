module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Birational.Birational
public import StacksCore.Tactic.StacksAttribute

/-!
# Birational morphisms of schemes

A morphism of schemes is *birational* when it induces a bijection between the generic points
of the irreducible components of its source and those of its target, and an isomorphism on the
local ring at each of those points of the source.

Birationality of two *schemes*, rather than of a morphism, is the existence of an isomorphism
between dense open subschemes; over a base it additionally requires that isomorphism to
commute with the structure morphisms. Both are already in the library, as
`AlgebraicGeometry.Scheme.Birational` and `AlgebraicGeometry.Scheme.BirationalOver`.

## Main definitions

* `AlgebraicGeometry.IsBirational`: birationality of a morphism of schemes.

## Main results

* `AlgebraicGeometry.isBirational_iff`, `AlgebraicGeometry.IsBirational.bijOn`,
  `AlgebraicGeometry.IsBirational.isIso_stalkMap` and
  `AlgebraicGeometry.isBirational_of_bijOn_of_isIso_stalkMap` unfold the definition in both
  directions.

## Implementation notes

The generic points of the irreducible components of a space form the set `genericPoints`, so
the bijection in the definition is `Set.BijOn` for the underlying map of points. The condition
on local rings is `CategoryTheory.IsIso` for the induced map of stalks.

The source assumes that both schemes have finitely many irreducible components. Neither
condition in the definition uses that finiteness, so the predicate is defined for arbitrary
schemes; under the source's hypotheses it is exactly the stated notion.

For irreducible schemes, a partial isomorphism between dense open subschemes is equivalently
an isomorphism in the category whose morphisms are dominant rational maps. The library's
definitions use the partial-isomorphism description and are meaningful without irreducibility
hypotheses, so they are adopted here directly. `Scheme.Birational` already carries the tag for
part (1) of 0A20; this module registers `Scheme.BirationalOver` as part (2).

## References

* [EGA I, (2.2.9)]
* [Stacks Project, Tag 01RO](https://stacks.math.columbia.edu/tag/01RO)
* [Stacks Project, Tag 0A20](https://stacks.math.columbia.edu/tag/0A20)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is **birational** if it induces a bijection on the generic points of
irreducible components and an isomorphism on the local rings at every such point of its source.

This definition is meaningful without the finiteness hypotheses on the sets of irreducible
components imposed in [Stacks Project, Tag 01RO]. -/
@[stacks 01RO, ega "I 2.2.9", ega "IV 6.15.4" "finitely many comps", ega "I 6.5.5"]
def IsBirational {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Set.BijOn f (genericPoints X) (genericPoints Y) ∧
    ∀ x : X, x ∈ genericPoints X → IsIso (f.stalkMap x)

/-- The defining characterization of a birational morphism. -/
theorem isBirational_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsBirational f ↔ Set.BijOn f (genericPoints X) (genericPoints Y) ∧
        ∀ x : X, x ∈ genericPoints X → IsIso (f.stalkMap x) := Iff.rfl

/-- A birational morphism bijects the generic points of irreducible components. -/
theorem IsBirational.bijOn {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : IsBirational f) :
    Set.BijOn f (genericPoints X) (genericPoints Y) := hf.1

/-- The map on local rings induced by a birational morphism at a generic point is an
isomorphism. -/
theorem IsBirational.isIso_stalkMap {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirational f) (x : X) (hx : x ∈ genericPoints X) : IsIso (f.stalkMap x) := hf.2 x hx

/-- A morphism which bijects generic points and induces isomorphisms on their local rings is
birational. -/
theorem isBirational_of_bijOn_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hbij : Set.BijOn f (genericPoints X) (genericPoints Y))
    (hstalk : ∀ x : X, x ∈ genericPoints X → IsIso (f.stalkMap x)) :
    IsBirational f := ⟨hbij, hstalk⟩

add_to_stacks 0A20 "(2)" AlgebraicGeometry.Scheme.BirationalOver

end AlgebraicGeometry
