module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Graded.Category

/-!
# Graded functors

A functor between categories graded over a ring `R` is *graded* when its maps on morphisms are
homomorphisms of graded `R`-modules: they are `R`-linear and send a homogeneous morphism of
degree `n` to a homogeneous morphism of degree `n`.

## Main definitions

* `CategoryTheory.Functor.Graded`: the property of a functor between graded categories of being
  graded.

## Implementation notes

That the maps on morphisms are homomorphisms of `R`-modules is recorded by extending both
`Functor.Additive` and `Functor.Linear R`; preservation of the grading is the single remaining
field `map_mem`. Being a property of an already bundled functor rather than a bundled structure
of its own, it lets clients use the ordinary functoriality API directly.

## References

* [Stacks Project, Tag 09L3](https://stacks.math.columbia.edu/tag/09L3)
-/

@[expose] public section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

/-- A functor between categories graded over `R` is graded if its maps on morphisms are
`R`-linear and preserve each homogeneous degree. -/
@[stacks 09L3]
class Functor.Graded (R : Type w) [Ring R] {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [GradedCategory R C] {D : Type u₂} [Category.{v₂} D] [Preadditive D] [GradedCategory R D]
    (F : C ⥤ D) : Prop extends F.Additive, F.Linear R where
  /-- A homogeneous morphism is sent to a homogeneous morphism of the same degree. -/
  map_mem {X Y : C} {n : ℤ} {f : X ⟶ Y} : f ∈ GradedCategory.grade (R := R) X Y n →
    F.map f ∈ GradedCategory.grade (R := R) (F.obj X) (F.obj Y) n

end CategoryTheory
