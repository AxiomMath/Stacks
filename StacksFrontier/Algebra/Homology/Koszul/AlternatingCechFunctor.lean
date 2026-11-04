module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplexFunctor

/-!
# Abelian presheaves on a space, as a preadditive category

The alternating Čech complex of Stacks 01FH is a functor of its coefficient presheaf,
`Stacks.Cech.alternatingCechComplexFunctor`, and the Koszul-complex comparison applies that
functor to presheaves written in the `TopCat.Presheaf` spelling rather than as functors out of
`(TopologicalSpace.Opens X)ᵒᵖ`. This file records the preadditive structure of that spelling,
which is the structure of the functor category it unfolds to, and makes the functor available
under it.

## Main definitions

* `Stacks.Cech.instPreadditiveTopCatPresheafAddCommGrpCat`: the abelian presheaves on a
  topological space form a preadditive category.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u w

namespace Stacks.Cech

/-- The category of abelian presheaves on a topological space is preadditive, being a
category of functors into an additive category. -/
instance instPreadditiveTopCatPresheafAddCommGrpCat {X : TopCat.{u}} :
    Preadditive (TopCat.Presheaf AddCommGrpCat.{w} X) :=
  inferInstanceAs (Preadditive ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}))

end Stacks.Cech
