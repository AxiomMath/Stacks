module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategoryLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.DGA.QuasiIsomorphisms
public import StacksFrontier.Algebra.DGA.DerivedCategory
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# Products in the derived category of a differential graded algebra

For a differential graded algebra `(A, d)` over a commutative ring `R`, the image of a product of
differential graded modules under the canonical functor to the derived category is a product of
their images. The derived category is the localization of the homotopy category at the
quasi-isomorphisms, so the functor in question is the composite of the quotient
`Mod_(A,d) ⥤ K(A,d)` with the localization `K(A,d) ⥤ D(A,d)`.

## Main results

* `DifferentialGradedModule.preservesProductsOfShape_quasiIsomorphismsQ`: the localization
  functor preserves `I`-indexed products.
* `DifferentialGradedModule.derivedProductIsLimit`: the image of the product cone of a family of
  differential graded modules is a limit cone in the derived category.

## Implementation notes

The two factors are handled separately. That the quotient to the homotopy category carries the
product cone of differential graded modules to a product cone is
`isLimitMapFanToHomotopyCategory`, stated there for an arbitrary product cone precisely so that
the categorical product `∏ᶜ M` supplied by `differentialGradedModule_hasLimits` can be used here
instead of the concrete degreewise product that lemma's file builds. That the localization
preserves products is the general localization statement
`Stacks.DerivedProducts.localizationPreservesProductsOfShape_of_leftCalculusOfFractions`, whose
  inputs are a
left calculus of fractions for the inverted class and stability of that class under `I`-indexed
products.

The first of those two inputs is available unconditionally:
`DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions` (Tag 09KX) inhabits it for
every `A`, by rewriting along `acyclic_trW_eq_quasiIsomorphisms` into Mathlib's instance for
`P.trW` of a triangulated subcategory `P` of a triangulated category — both of whose inputs,
`acyclic_isTriangulated` and `instIsTriangulatedHomotopyCategory`, are proved. So that hypothesis
is not carried by either statement here.

The second input, stability of the quasi-isomorphisms under `I`-indexed products for an arbitrary
`I : Type w`, is **not** available and remains an instance hypothesis, so **no `@[stacks 09QI]`
tag is placed**: a hypothesis the Stacks statement does not carry may not be tagged. Mathlib
supplies `P.trW.IsStableUnderFiniteProducts` from `P.IsTriangulated`, and that does fire here, but
its index type is restricted to `Finite`; the body of Mathlib's proof is shape-agnostic and the
only shape-dependent input it needs is `P.isoClosure.prop_pi`, i.e. closure of the acyclic objects
under `I`-indexed products. Nothing in the tree concludes that, and the route to it runs through a
degreewise description of the product of differential graded modules, which exists only inside the
`private` blocks of `StacksFrontier/Algebra/DifferentialGraded/Module/HomotopyCategoryLimits.lean` and of the Stacks Tag 09JJ development. The
report accompanying this file names the chain.

## References

* [Stacks Project, Tag 09QI](https://stacks.math.columbia.edu/tag/09QI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]

attribute [local instance] differentialGradedModule_hasLimits

/-- The localization of the homotopy category at the quasi-isomorphisms preserves `I`-indexed
products. The homotopy category has those products by `hasProducts_homotopyCategory` and the
quasi-isomorphisms have a left calculus of fractions by
`quasiIsomorphisms_hasLeftCalculusOfFractions`; the one remaining input, their stability under
`I`-indexed products, is a hypothesis. -/
theorem preservesProductsOfShape_quasiIsomorphismsQ
    (A : DifferentialGradedAlgebra.{u, v} R) (I : Type w)
    [(quasiIsomorphisms.{u, v, w} A).IsStableUnderProductsOfShape I] :
    PreservesLimitsOfShape (Discrete I) (quasiIsomorphisms.{u, v, w} A).Q :=
  Stacks.DerivedProducts.localizationPreservesProductsOfShape_of_leftCalculusOfFractions
    (quasiIsomorphisms.{u, v, w} A).Q (quasiIsomorphisms.{u, v, w} A)

/-- Products in the derived category of a differential graded algebra are obtained from products
of differential graded modules: the image of the product cone of a family `M` under the quotient
to the homotopy category followed by the localization at quasi-isomorphisms is a limit cone.

This carries one instance hypothesis that Stacks 09QI does not, so it is left untagged. -/
theorem derivedProductIsLimit (A : DifferentialGradedAlgebra.{u, v} R)
    {I : Type w} (M : I → DifferentialGradedModule.{u, v, w} A)
    [(quasiIsomorphisms.{u, v, w} A).IsStableUnderProductsOfShape I] :
    Nonempty (IsLimit
      (Fan.mk
        ((quasiIsomorphisms.{u, v, w} A).Q.obj ((toHomotopyCategory A).obj (∏ᶜ M)))
        (fun i => (quasiIsomorphisms.{u, v, w} A).Q.map
          ((toHomotopyCategory A).map (Pi.π M i))))) := by
  classical
  obtain ⟨hq⟩ := isLimitMapFanToHomotopyCategory M (Pi.π M) (productIsProduct M)
  have := preservesProductsOfShape_quasiIsomorphismsQ A I
  exact ⟨Fan.isLimitMapConeEquiv (quasiIsomorphisms.{u, v, w} A).Q _ _
    (isLimitOfPreserves (quasiIsomorphisms.{u, v, w} A).Q hq)⟩

end DifferentialGradedModule

end
