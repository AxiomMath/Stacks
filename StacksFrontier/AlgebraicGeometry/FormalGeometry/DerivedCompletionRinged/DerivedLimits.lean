module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Products
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit

/-!
# Derived limits on a ringed site

`R lim` exists on `D(𝒪)` for every ringed site: countable products exist there, and in a
pre-triangulated category an inverse system whose objects have a product has a derived limit.
This file records both statements.

## Main results

* `AlgebraicGeometry.RingedSite.hasProductsOfShape_nat_derivedCategory_ringSheaf`: the derived
  category of sheaves of modules on a ringed site has countable products.
* `AlgebraicGeometry.RingedSite.exists_isDerivedLimit_ringSheaf`: every inverse system in
  `D(𝒪)` indexed by `ℕᵒᵖ` has a derived limit.

## Implementation notes

The countable products come from
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`, which is stated
for the sheaves of modules over an arbitrary sheaf of rings on an arbitrary site and needs *no*
exactness of the countable products of the abelian category — Grothendieck's axiom AB4*, the
usual hypothesis ([Stacks, Tag 07KC]) for products in a derived category, which fails for
sheaves of modules. The slicewise form of the same statement,
`AlgebraicGeometry.RingedSite.hasProductsOfShape_nat_derivedCategory_over`, is what the
derived-completeness predicate of [Stacks, Tag 0999] consumes; this is its form on the ringed
site itself.

### What this does and does not give

It gives: for each inverse system `F : ℕᵒᵖ ⥤ D(𝒪)` an object `K` and a distinguished triangle
`K ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ K⟦1⟧` whose middle map is the Milnor difference, i.e. a value of `R lim`
for that system, unique up to isomorphism.

It does **not** give a *functor* `R lim : (ℕᵒᵖ ⥤ D(𝒪)) ⥤ D(𝒪)`, and the reason is intrinsic:
`CategoryTheory.Pretriangulated.IsDerivedLimit` is a predicate precisely because the cone
completing the Milnor difference to a distinguished triangle is determined only up to
non-unique isomorphism, so there is no canonical choice to be functorial in. Statements about
derived limits are therefore phrased with the predicate, as [Stacks, Tag 0A0E] and
[Stacks, Tag 099M] are.

## References

* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v})

/-- **Countable products in the derived category of sheaves of modules on a ringed site.**
Obtained from K-injective resolutions, so with no exactness hypothesis on the countable
products of the abelian category. -/
theorem hasProductsOfShape_nat_derivedCategory_ringSheaf :
    HasProductsOfShape ℕ (DerivedCategory (SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules _

/-- **`R lim` exists on `D(𝒪)`.** Every inverse system of objects of the derived category of
sheaves of modules on a ringed site has a derived limit: the countable product exists, and
completing the Milnor difference map to a distinguished triangle gives the derived limit. -/
theorem exists_isDerivedLimit_ringSheaf
    (F : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ (_ : HasProduct fun n : ℕ => F.obj ⟨n⟩)
      (K : DerivedCategory (SheafOfModules.{max u v w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))), IsDerivedLimit F K :=
  have : HasProductsOfShape ℕ (DerivedCategory (SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
    hasProductsOfShape_nat_derivedCategory_ringSheaf.{u, v, w} X
  ⟨inferInstance, exists_isDerivedLimit F⟩

end AlgebraicGeometry.RingedSite

end
