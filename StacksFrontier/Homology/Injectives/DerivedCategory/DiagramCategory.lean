module

public import StacksFrontier.CategoryTheory.Abelian.GrothendieckAxioms.PresheafCategory
public import StacksFrontier.Homology.Injectives.DerivedCategory.Existence
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts

/-!
# The derived category of a category of diagrams

Let `C` be a small category and let `D` be an abelian category which is Grothendieck abelian
relative to the universe `u` of the objects of `C`. Then `Cᵒᵖ ⥤ D` is Grothendieck abelian
relative to `u` (`CategoryTheory.isGrothendieckAbelian_presheafCategory`), so it has enough
injectives by Mathlib's instance `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`, and this
file records the two consequences for its derived category that a dévissage along compact
generators needs: `D(Cᵒᵖ ⥤ D)` has direct sums indexed by `Type u`, and it has a model whose
morphisms live in `Type u`.

The second is what makes the first usable. Compactness of an object of a triangulated category is
tested at a universe, and the cell presentation of
`CategoryTheory.Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated` tests it at the
*hom* universe of the category; at `CategoryTheory.HasDerivedCategory.standard` the morphisms of
`D(Cᵒᵖ ⥤ D)` live one level above the coefficients, where direct sums indexed by `Type u` are no
longer enough. The model of [Stacks, Tag 079Q] has its morphisms in `Type u` exactly, so there the
two universes agree. This is the same arrangement as the hypothesis
`[HasDerivedCategory.{u} (ModuleCat.{u} R)]` of
`StacksDraft.CompactDevissage.isIso_of_isIso_app_regularModule`.

## Main results

* `Stacks.Injectives.hasCoproducts_derivedCategory_diagrams`: `D(Cᵒᵖ ⥤ D)` has direct sums indexed
  by any type in `Type u`, at any model of the derived category.
* `Stacks.Injectives.hasDerivedCategory_diagrams`: the model of [Stacks, Tag 079Q] for `Cᵒᵖ ⥤ D`,
  whose morphisms live in `Type u`.

## References

* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uD vD z u

namespace Stacks.Injectives

variable (C : Type u) [SmallCategory C] (D : Type uD) [Category.{vD} D] [Abelian D]
  [IsGrothendieckAbelian.{u} D]

/-- **Direct sums in the derived category of a category of diagrams.** For any choice of model,
`D(Cᵒᵖ ⥤ D)` has direct sums indexed by any type in `Type u`. -/
theorem hasCoproducts_derivedCategory_diagrams [HasDerivedCategory.{z} (Cᵒᵖ ⥤ D)] :
    HasCoproducts.{u} (DerivedCategory (Cᵒᵖ ⥤ D)) :=
  hasCoproducts_derivedCategory (Cᵒᵖ ⥤ D)

/-- **The locally `u`-small model of the derived category of a category of diagrams**, given by
[Stacks, Tag 079Q]. Its morphisms live in `Type u`, the universe at which
`Stacks.Injectives.hasCoproducts_derivedCategory_diagrams` supplies direct sums. -/
@[instance_reducible]
def hasDerivedCategory_diagrams : HasDerivedCategory.{u} (Cᵒᵖ ⥤ D) :=
  hasDerivedCategory_of_isGrothendieckAbelian.{u} (Cᵒᵖ ⥤ D)

end Stacks.Injectives

end
