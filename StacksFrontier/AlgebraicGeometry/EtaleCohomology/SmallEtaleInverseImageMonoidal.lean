module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.CategoryTheory.Sites.SheafPullbackMonoidal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inverse image of étale sheaves of modules is monoidal

For a morphism of schemes `f : X ⟶ Y` and a commutative ring `Λ`, the inverse image
`f⁻¹ : EtaleModules Λ Y ⥤ EtaleModules Λ X` of sheaves of `Λ`-modules on Mathlib's small étale
sites is a monoidal functor for the tensor products `CategoryTheory.Sheaf.monoidalCategory`.
Base change of small étale sites is representably flat, so the comma categories computing the
left Kan extension are filtered, and the tensor product of modules commutes with all colimits in
each variable; `CategoryTheory.Functor.sheafPullbackMonoidal` applies.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleInverseImageSheafPullbackMonoidal`: the monoidal structure on
  the inverse image `f⁻¹` of étale sheaves of `Λ`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The category of `Λ`-modules in `Type (u + 1)` has colimits indexed by categories in
`Type (u + 1)`. -/
local instance : HasColimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} Λ) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ

attribute [local instance] Sheaf.monoidalCategory
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorLeft
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorRight

/-- **The inverse image of étale sheaves of modules is a monoidal functor**: the monoidal structure
on `etaleModuleInverseImage Λ f` for the sheaf tensor products on the small étale sites. -/
@[instance_reducible, sga "4 IV 3.1.2" "special case"]
def etaleModuleInverseImageSheafPullbackMonoidal
    [(X.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]
    [(Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal] :
    (etaleModuleInverseImage.{u, 0} Λ f).Monoidal :=
  haveI : ∀ Z : X.Etaleᵒᵖ, IsFiltered (CostructuredArrow (smallEtaleBaseChange f).op Z) :=
    fun Z => IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (smallEtaleBaseChange f) (Opposite.unop Z))
  haveI : ∀ (Z : X.Etaleᵒᵖ) (M : ModuleCat.{u + 1} Λ),
      PreservesColimitsOfShape (CostructuredArrow (smallEtaleBaseChange f).op Z)
        ((curriedTensor (ModuleCat.{u + 1} Λ)).obj M) :=
    fun _ M => inferInstanceAs (PreservesColimitsOfShape _ (tensorLeft M))
  haveI : ∀ (Z : X.Etaleᵒᵖ) (M : ModuleCat.{u + 1} Λ),
      PreservesColimitsOfShape (CostructuredArrow (smallEtaleBaseChange f).op Z)
        ((curriedTensor (ModuleCat.{u + 1} Λ)).flip.obj M) :=
    fun _ M =>
      haveI : PreservesColimitsOfSize.{u, u + 1} (tensorRight M) :=
        preservesColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} (tensorRight M)
      inferInstanceAs (PreservesColimitsOfShape _ (tensorRight M))
  Functor.sheafPullbackMonoidal (smallEtaleBaseChange f) (ModuleCat.{u + 1} Λ)
    Y.smallEtaleTopology X.smallEtaleTopology

end Stacks.EtaleCohomology

end
