module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Topology.Sheaves.Modules.StalkSkyscraperAdjunction

/-!
# The skyscraper sheaf at a point with an injective value is an injective sheaf of modules

Let `X` be a topological space, `O` a sheaf of rings on the site of open subsets of `X`, and
`x : X`. Write `i_x : ({x}, O_x) ⟶ (X, O)` for the inclusion of the point. This file proves
that the direct image `i_{x,*} M` of an injective `O_x`-module `M` is an injective object of
the category of sheaves of `O`-modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.skyscraperFunctor_preservesInjectiveObjects`:
  `i_{x,*}` preserves injective objects.
* `AlgebraicGeometry.SheafOfModules.injective_skyscraperObj`: the same statement with the
  skyscraper sheaf spelled out as an object.

## The proof

`i_{x,*}` is the right adjoint of the stalk functor at `x`
(`AlgebraicGeometry.SheafOfModules.stalkSkyscraperAdjunction`), and the stalk functor preserves
monomorphisms, being left exact
(`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits`). The right adjoint of a
functor preserving monomorphisms preserves injective objects: a lift of a morphism into
`i_{x,*} M` along a monomorphism `A ⟶ B` is the adjunct of a lift of its adjunct along the
monomorphism `A_x ⟶ B_x`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

/-- **The direct image along the inclusion of a point preserves injective objects.** For a
point `x` of a topological space `X` carrying a sheaf of rings `O`, the skyscraper sheaf at `x`
with value an injective module over the stalk ring `O_x` is an injective object of the category
of sheaves of `O`-modules. -/
instance skyscraperFunctor_preservesInjectiveObjects :
    (skyscraperFunctor O x).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (stalkSkyscraperAdjunction O x)

/-- **The skyscraper sheaf at `x` with an injective value is injective.** This is
`skyscraperFunctor_preservesInjectiveObjects` with the object spelled out, so that instance
search finds it for the `skyscraperObj` form too. -/
instance injective_skyscraperObj
    (M : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))
    [Injective M] : Injective (skyscraperObj O x M) :=
  (skyscraperFunctor O x).injective_obj M

end AlgebraicGeometry.SheafOfModules

end
