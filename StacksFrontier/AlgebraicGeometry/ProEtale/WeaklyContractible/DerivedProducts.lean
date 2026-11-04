module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WeaklyContractibleProducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Situation

/-!
# Derived-category products of sheaves of modules are termwise

On a ringed site with a covering collection of weakly contractible objects, a product in the
derived category of sheaves of modules is computed by taking the termwise product of any
choice of representing complexes.

The general statement for an abelian category with exact products is
`Stacks.DerivedProducts.isLimit_productFanInDerivedCategory`: the image under the localisation
functor of the termwise product complex, with the localised projections as its legs, is a
product fan in the derived category. Its exactness hypothesis is exactly Stacks 0947(4),
supplied here by `Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete`
from the data of the situation. Because the legs of the fan are the canonical localised
projections, the product so obtained is independent of the chosen representatives up to a
unique isomorphism of fans.

## Main results

* `isLimit_productFanInDerivedCategory_of_weaklyContractibleObjectsSituation`:
  **Stacks 0947(5)**, the termwise product of representing complexes is the product in the
  derived category of sheaves of modules.
* `hasProductsOfShape_nat_derivedCategory`: countable products exist in that derived category.
  Parts (6) and (7) of the tag speak about `∏ₙ Kₙ` and about `R lim Kₙ`, which is defined by a
  triangle on that product; this is what lets them do so without assuming the product exists.

## Implementation notes

The index type is arbitrary, as in the source: no finiteness and no countability. The general
07KC statement `Stacks.DerivedProducts.isLimit_productFanInDerivedCategory` carries no
`Countable` hypothesis, and Stacks 0947(4) is now available at every index type with a
`t`-small model, so 0947(5) is obtained at that same generality.

The choice of derived category is left as an instance argument rather than fixed to
`HasDerivedCategory.standard`, so that the statement applies to any model.

## References

* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u t u₀

namespace Stacks.WeaklyContractible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- **Stacks 0947(5).** On a ringed site with a covering collection of weakly contractible
objects, products in the derived category of sheaves of modules are computed by termwise
products of representing complexes: for every family `K` of cochain complexes of sheaves of
modules indexed by an *arbitrary* type `ι`, the fan whose apex is the image of the termwise
product complex `∏ᶜ K` and whose legs are the images of the projections `Pi.π K i` is a limit
fan. -/
@[stacks 0947 "derived_products_termwise"]
theorem isLimit_productFanInDerivedCategory_of_weaklyContractibleObjectsSituation
    (S : WeaklyContractibleObjectsSituation.{w, v, u, t} C J)
    [HasDerivedCategory (SheafOfModules.{t} S.O)] (ι : Type u₀) [Small.{t} ι]
    (K : ι → CochainComplex (SheafOfModules.{t} S.O) ℤ) :
    Nonempty (IsLimit (Stacks.DerivedProducts.productFanInDerivedCategory K)) :=
  have : HasExactLimitsOfShape (Discrete ι) (SheafOfModules.{t} S.O) :=
    Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete ι
      S.B S.hasEnoughObjects S.isWeaklyContractible
  Stacks.DerivedProducts.isLimit_productFanInDerivedCategory K

/-- **Countable products exist in the derived category of sheaves of modules** on a ringed site
with a covering collection of weakly contractible objects. This is Stacks 07KC(1), whose
hypothesis — exactness of countable products on `Mod(O)` — is Stacks 0947(4); so the inverse
systems of parts (6) and (7) of the tag have products, and a consumer of those parts does not
have to assume one. -/
theorem hasProductsOfShape_nat_derivedCategory
    (S : WeaklyContractibleObjectsSituation.{w, v, u, t} C J)
    [HasDerivedCategory (SheafOfModules.{t} S.O)] :
    HasProductsOfShape ℕ (DerivedCategory (SheafOfModules.{t} S.O)) :=
  have : HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{t} S.O) :=
    Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete_nat
      S.B S.hasEnoughObjects S.isWeaklyContractible
  Stacks.DerivedProducts.hasProductsOfShape_nat

end Stacks.WeaklyContractible

end
