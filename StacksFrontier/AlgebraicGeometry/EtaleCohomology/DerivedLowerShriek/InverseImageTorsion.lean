module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleForgetBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage

/-!
# Inverse image preserves `D⁺_tors`

For a morphism of schemes `e : W ⟶ X` and `K ∈ D⁺(X_étale, Λ)` with torsion cohomology sheaves,
the inverse image `e⁻¹ K` has torsion cohomology sheaves: inverse image is exact, so
`Hⁱ(e⁻¹ K) = e⁻¹ Hⁱ(K)`, and the inverse image of a torsion sheaf is torsion
(`Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage`, through the underlying
abelian sheaves).

## Main results

* `Stacks.EtaleCohomology.isTorsionEtaleModule_etaleModuleInverseImage_obj`.
* `Stacks.EtaleCohomology.isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ]

/-- **The inverse image of a torsion sheaf of `Λ`-modules is torsion.** -/
theorem isTorsionEtaleModule_etaleModuleInverseImage_obj {W X : Scheme.{u}} (e : W ⟶ X)
    (M : EtaleModules.{u, 0} Λ X) (hM : IsTorsionEtaleModule.{u, 0} Λ X M) :
    IsTorsionEtaleModule.{u, 0} Λ W ((etaleModuleInverseImage.{u, 0} Λ e).obj M) :=
  Stacks.Torsion.torsionSheafProperty_of_iso W.smallEtaleTopology
    ((etaleModuleForgetInverseImageIso.{u, 0} Λ e).app M)
    (torsionSheafProperty_etaleAbelianInverseImage.{u, 0} e _ hM)

/-- **Inverse image preserves `D⁺_tors`.** -/
theorem isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj {W X : Scheme.{u}} (e : W ⟶ X)
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (hK : isTorsionPlus.{u, 0} Λ X K) :
    isTorsionPlus.{u, 0} Λ W ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ e).obj K) := fun q =>
  IsTorsionEtaleModule.of_iso Λ W (etaleModuleDerivedInverseImagePlusHomologyIso Λ e K q).symm
    (isTorsionEtaleModule_etaleModuleInverseImage_obj Λ e _ (hK q))

end Stacks.EtaleCohomology
