module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverseSeparator
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived sections over an open of a ringed space

Let `X` be a topological space and `O` a sheaf of rings on `X`. For an open `U ⊆ X` the
sections functor `Γ(U, -) : Mod(O) ⥤ Mod(O(U))`, `F ↦ F(U)`, is additive and left exact, and
the category `Mod(O)` of sheaves of `O`-modules has enough injectives. It therefore has a
right derived functor on bounded below derived categories,
`RΓ(U, -) : D⁺(O) ⥤ D⁺(O(U))`.

## Main definitions

* `Stacks.RingedSpaceCohomology.derivedSections`: the derived sections functor
  `RΓ(U, -) : D⁺(O) ⥤ D⁺(O(U))` over an open `U` of a ringed space.

## Implementation notes

A ringed space is here a topological space with a sheaf of rings on it in `RingCat`, not
necessarily commutative; a ringed space `X` in the sense of Mathlib's `RingedSpace` gives one by
forgetting commutativity of its structure sheaf. The sections functor is
`SheafOfModules.evaluation O (op U)` and the derived functor is Mathlib's
`CategoryTheory.Functor.rightDerivedFunctorPlus`, computed by injective resolutions. The
derived categories are those of any choice of `HasDerivedCategory` on the two abelian
categories. `derivedSections` is an abbreviation, so the API of `rightDerivedFunctorPlus`
(its unit `rightDerivedFunctorPlusUnit` and the instance that it is a right derived functor
with respect to the quasi-isomorphisms) applies to it directly.

## References

* [Stacks Project, Tag 0717](https://stacks.math.columbia.edu/tag/0717)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.RingedSpaceCohomology

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **The derived sections functor over an open of a ringed space**,
`RΓ(U, -) : D⁺(O) ⥤ D⁺(O(U))`: the right derived functor, on bounded below derived categories,
of the sections functor `Γ(U, -) = SheafOfModules.evaluation O (op U)` from sheaves of
`O`-modules to modules over the ring `O(U)` of sections of `O` over `U`. It is computed by
injective resolutions, sheaves of `O`-modules having enough injectives. -/
@[stacks 0717 "RΓ(U, -) : D⁺(X) → D⁺(𝒪_X(U))"]
abbrev derivedSections (U : Opens X) [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (ModuleCat.{u} (O.obj.obj (op U)))] :
    DerivedCategory.Plus (SheafOfModules.{u} O) ⥤
      DerivedCategory.Plus (ModuleCat.{u} (O.obj.obj (op U))) :=
  (SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus

end Stacks.RingedSpaceCohomology

end
