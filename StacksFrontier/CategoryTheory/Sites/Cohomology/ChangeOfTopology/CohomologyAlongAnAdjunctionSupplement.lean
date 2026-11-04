module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CohomologyAlongAnAdjunction

/-!
# The comparison of cohomology along an adjunction as an isomorphism of functors

The comparison of cohomology along an adjunction, as an isomorphism of cohomology functors as
soon as the comparison map is bijective in the given degree.

## Main definitions

* `Stacks.ExtAdjunction.functorHComparisonIsoOfBijective`: the comparison on cohomology as an
  isomorphism `L ⋙ H^n(K, -) ≅ H^n(J, -)` of cohomology functors.
-/

@[expose] public noncomputable section

universe t a u₁ v₁ u₂ v₂

namespace Stacks.ExtAdjunction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  {L : Sheaf J AddCommGrpCat.{t} ⥤ Sheaf K AddCommGrpCat.{t}}
  {R : Sheaf K AddCommGrpCat.{t} ⥤ Sheaf J AddCommGrpCat.{t}}
variable [HasExt.{a} (Sheaf J AddCommGrpCat.{t})] [HasExt.{a} (Sheaf K AddCommGrpCat.{t})]
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (θ : constantSheaf J AddCommGrpCat.{t} ⋙ L ≅ constantSheaf K AddCommGrpCat.{t})

/-- The comparison on cohomology as an isomorphism of cohomology functors, as soon as the
comparison map is bijective in the given degree. -/
def functorHComparisonIsoOfBijective (n : ℕ) (h : ∀ F, Function.Bijective (hComparison θ n F)) :
    L ⋙ Sheaf.functorH K n ≅ Sheaf.functorH J n :=
  (NatIso.ofComponents
    (fun F ↦ (AddEquiv.ofBijective (hComparison θ n F) (h F)).toAddCommGrpIso)
    fun f ↦ by ext e; exact hComparison_naturality θ n f e).symm

end Stacks.ExtAdjunction

end
