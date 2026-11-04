module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ForgetSupportsBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionByZeroToDirectImageMono
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelChange

/-!
# Forgetting supports on a curve when the local terms at the boundary are bounded

Let `j : U ⟶ Y` be an open immersion and `G` a sheaf of `ℤ/N`-modules on `U_étale`. The
*forget supports* map `H¹_c(U, G) = Ext¹_Y(ℤ/N, j_! G) → H¹(U, G) = Ext¹_U(j^{-1} ℤ/N, G)` is
`w ↦ extMap (w ∘ (j_! G ↪ j_* G))` for the adjunction `j^{-1} ⊣ j_*`. If `K₁` kills the cokernel
of `j_! G ↪ j_* G` and `K₂` kills `R¹j_* G`, its kernel is killed by `K₁` and its cokernel by
`K₁ K₂` (`Stacks.EtaleCohomology.forgetSupports_bounds_extensionByZero`, from
`Stacks.ExtAdjunction.forgetSupports_bounds`). For the levels of an ℓ-adic sheaf on a curve
these are the two local terms of `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy`
(`Stacks.EtaleCohomology.LAdicSheaf.forgetSupports_bounds_of_localTermsKilledBy`).

## Main results

* `Stacks.EtaleCohomology.forgetSupports_bounds_extensionByZero`.
* `Stacks.EtaleCohomology.LAdicSheaf.forgetSupports_bounds_of_localTermsKilledBy`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- **Forgetting supports along an open immersion, up to the local terms.** -/
theorem forgetSupports_bounds_extensionByZero {N : ℕ} {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (G : EtaleModules.{u, 0} (ZMod N) U) {K₁ K₂ : ℕ}
    (h₁ : K₁ • 𝟙 (cokernel ((etaleModuleExtensionByZeroToDirectImage.{u, 0} (ZMod N) j).app G)) = 0)
    (h₂ : K₂ • 𝟙 (((etaleModuleDirectImage.{u, 0} (ZMod N) j).rightDerived 1).obj G) = 0) :
    (∀ w : Ext (unitSheaf (X := Y) N) ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj G) 1,
      Stacks.ExtAdjunction.extMap (etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod N) j) _ G 1
        (w.comp (Ext.mk₀ ((etaleModuleExtensionByZeroToDirectImage.{u, 0} (ZMod N) j).app G))
          (add_zero 1)) = 0 → K₁ • w = 0) ∧
      ∀ x : Ext ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj (unitSheaf (X := Y) N)) G 1,
        ∃ w : Ext (unitSheaf (X := Y) N) ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj G) 1,
          Stacks.ExtAdjunction.extMap (etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod N) j) _ G
            1 (w.comp (Ext.mk₀ ((etaleModuleExtensionByZeroToDirectImage.{u, 0} (ZMod N) j).app G))
              (add_zero 1)) = (K₁ * K₂) • x := by
  let adj := etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod N) j
  have : (etaleModuleRestriction.{u, 0} (ZMod N) j).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (etaleModuleDirectImage.{u, 0} (ZMod N) j).Additive := adj.right_adjoint_additive
  have : PreservesLimitsOfSize.{0, 0} (etaleModuleDirectImage.{u, 0} (ZMod N) j) :=
    adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (etaleModuleDirectImage.{u, 0} (ZMod N) j) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  have := mono_etaleModuleExtensionByZeroToDirectImage_app (ZMod N) j G
  exact Stacks.ExtAdjunction.forgetSupports_bounds adj _ G _ h₁ h₂

end Stacks.EtaleCohomology

end
