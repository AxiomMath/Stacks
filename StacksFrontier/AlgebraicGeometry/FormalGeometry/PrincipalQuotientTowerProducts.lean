module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalQuotientTowerDerivedCompletion
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts

/-!
# Countable products in the derived category of sheaves of modules on a scheme

The `r = 1` results of [Stacks, Tags 0H3D, 0H3E, 0BLD] in
`FormalGeometry/PrincipalQuotientTowerSections.lean` and
`FormalGeometry/PrincipalQuotientTowerDerivedCompletion.lean` carry the existence of the
countable products of the inverse systems `Csys` and `Ksys` as instance binders. Those products
exist, with no hypothesis: the derived category of sheaves of modules on any site has countable
products, by K-injective resolutions
(`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`). This file says
so at the model and the universe those results are stated at, so that a consumer can discharge
the binders rather than inherit them.

The universe levels are written out. `D(𝒪_X)` is there the standard model
`CategoryTheory.HasDerivedCategory.standard`, whose morphisms live one universe up, whereas
instance search left to itself answers with the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`; pinning the level is what selects the
model the `r = 1` results use. For the same reason this is a module of its own: in the import
closure of `FormalGeometry/Completion/CohomologyAdicCompletion.lean` the search for the standard
model no longer succeeds, so the statement has to be elaborated here and consumed as a term
there.

## Main results

* `Stacks.Algebraization.hasProductsOfShape_nat_derivedCategory_modules` — the derived category
  of sheaves of `𝒪_X`-modules on a scheme has countable products.

## References

* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Algebraization

/-- **Countable products in `D(𝒪_X)`**, at the standard model of the derived category and the
universe at which the `r = 1` results of [Stacks, Tag 0BLD] are stated.

This is `Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules` for the
structure sheaf of a scheme; no hypothesis on `X` is used. -/
public theorem hasProductsOfShape_nat_derivedCategory_modules (X : Scheme.{u}) :
    HasProductsOfShape.{0, u + 1, u + 1} ℕ
      (DerivedCategory.{u + 1, u, u + 1}
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :=
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules.{u + 1, u, u, u, u}
    (structureSheafRing X.toRingedSpace)

end Stacks.Algebraization

end
