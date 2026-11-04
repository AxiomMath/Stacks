module

public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Monoidal
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianUnivLE
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Countable products in the derived category of sheaves of modules on a site

Let `(C, J)` be a site and `Λ` a ring, the sections of the sheaves of `Λ`-modules lying in a
universe containing those of the site. The sheaves of `Λ`-modules form a Grothendieck abelian
category, so every complex has a K-injective resolution, and the derived category
`D(C, Λ)` has countable products: a termwise product of K-injective complexes represents the
product ([Stacks, Tag 0BK6]). This is what makes derived limits of countable inverse systems
available in `D(C, Λ)` on an arbitrary site.

## Main results

* `Stacks.ModuleSheaf.isGrothendieckAbelian`: sheaves of `Λ`-modules form a Grothendieck abelian
  category.
* `Stacks.ModuleSheaf.hasProductsOfShape_derivedCategory`: countable products in `D(C, Λ)`.

## Implementation notes

The Grothendieck property is recorded as a theorem rather than an instance: as an instance it
diverts the search for limits of sheaves of modules into universe constraints that cannot be
solved.

## References

* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t w v u

namespace Stacks.ModuleSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}]

/-- **Sheaves of `Λ`-modules form a Grothendieck abelian category**, in the universe of their
sections. -/
@[sga "4 II 6.7" "special case"]
theorem isGrothendieckAbelian : IsGrothendieckAbelian.{w} (Sheaf J (ModuleCat.{w} Λ)) := by
  have : UnivLE.{u, w} := UnivLE.trans.{u, max u v, w}
  have : UnivLE.{v, w} := UnivLE.trans.{v, max u v, w}
  have : HasCoproducts.{v} (ModuleCat.{w} Λ) := fun J ↦ ModuleCat.hasColimitsOfShape Λ (Discrete J)
  have : HasCoproducts.{u} (ModuleCat.{w} Λ) := fun J ↦ ModuleCat.hasColimitsOfShape Λ (Discrete J)
  exact (CategoryTheory.Sheaf.isGrothendieckAbelian_of_small J (ModuleCat.{w} Λ) :
    IsGrothendieckAbelian.{w} (Sheaf J (ModuleCat.{w} Λ)))

/-- **The derived category of sheaves of `Λ`-modules on a site has countable products**, at any
model of the derived category. -/
instance hasProductsOfShape_derivedCategory [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))] :
    HasProductsOfShape ℕ (DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) := by
  have : HasLimitsOfShape (Discrete ℕ) (ModuleCat.{w} Λ) := inferInstance
  have : HasLimitsOfShape (Discrete ℕ) (Cᵒᵖ ⥤ ModuleCat.{w} Λ) :=
    functorCategoryHasLimitsOfShape
  have : HasProductsOfShape ℕ (Sheaf J (ModuleCat.{w} Λ)) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J _)
  have := isGrothendieckAbelian J Λ
  exact Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_of_exists_quasiIso_isKInjective
    fun K ↦ ⟨(Stacks.Injectives.kInjectiveResolutionFunctor.{w} (Sheaf J (ModuleCat.{w} Λ))).obj K,
      (Stacks.Injectives.kInjectiveResolutionInclusion.{w} (Sheaf J (ModuleCat.{w} Λ))).app K,
      inferInstance, inferInstance⟩

end Stacks.ModuleSheaf
