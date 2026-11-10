module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientMateLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GroupRingInvariantsLimit
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero

/-!
# The sheaf of invariants of a sheaf of `Λ[G]`-modules

Let `Λ` be a commutative ring and `G` a finite group.  For a sheaf `𝒩` of `Λ[G]`-modules on the
small étale site of a scheme, its sheaf of invariants `𝒩^G` is coextension of scalars along the
augmentation `Λ[G] → Λ`, sectionwise `Hom_{Λ[G]}(Λ, 𝒩(U)) = 𝒩(U)^G`.  This file shows that taking
invariants commutes with inverse image along any morphism of schemes and with extension by zero
along any étale morphism.

Invariants are not right exact, so this is not the formal commutation of an exact change of
coefficients with a left adjoint.  It holds because invariants of a finite group are a *finite*
limit of restriction of scalars with `G` acting
(`Stacks.EtaleCohomology.isLimitGroupRingInvariantsCone`), restriction of scalars commutes with
both functors (`Stacks.EtaleCohomology.etaleModuleInverseImageRestrictScalars`,
`Stacks.EtaleCohomology.etaleModuleExtensionByZeroRestrictScalars`), and both functors are left
exact (`Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits`, Tag 03S5); the
comparison of a finite limit of coefficient functors is then invertible by
`Stacks.EtaleCohomology.isIso_coefficientMate_of_isLimit`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleInvariants`: the functor `𝒩 ↦ 𝒩^G`.
* `Stacks.EtaleCohomology.etaleModuleInverseImageInvariants`: `f^{-1}(𝒩^G) ≅ (f^{-1} 𝒩)^G`.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroInvariants`: `j_!(𝒩^G) ≅ (j_! 𝒩)^G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ] (G : Type) [Group G] [Fintype G]

/-- **The sheaf of invariants** of a sheaf of `Λ[G]`-modules on the small étale site: coextension
of scalars along the augmentation, sectionwise `𝒩(U)^G`. -/
abbrev etaleModuleInvariants (X : Scheme.{u}) :
    EtaleModules.{u, 0} (MonoidAlgebra Λ G) X ⥤ EtaleModules.{u, 0} Λ X :=
  etaleModuleCoextendScalars (groupRingAugmentation Λ G) X

/-- The comparison of a coefficient functor with inverse image along `f`. -/
abbrev inverseImageSheafComposeCoefficientMate {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Gf : ModuleCat.{u + 1} (MonoidAlgebra Λ G) ⥤ ModuleCat.{u + 1} Λ)
    [Y.smallEtaleTopology.HasSheafCompose Gf] [X.smallEtaleTopology.HasSheafCompose Gf] :=
  sheafComposeCoefficientMate (smallEtaleBaseChange f) Y.smallEtaleTopology X.smallEtaleTopology
    (etaleModuleInverseImageAdj.{u, 0} (MonoidAlgebra Λ G) f)
    (etaleModuleInverseImageAdj.{u, 0} Λ f) Gf

omit [Fintype G] in
variable [Finite G] in
/-- **Inverse image commutes with invariants**: the comparison `f^{-1}(𝒩^G) ⟶ (f^{-1} 𝒩)^G` is
invertible. -/
instance isIso_inverseImageCoefficientMate_invariants {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (inverseImageSheafComposeCoefficientMate Λ G f
      (ModuleCat.coextendScalars (groupRingAugmentation Λ G))) := by
  have := Fintype.ofFinite G
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} Λ f
  have : ∀ i, Y.smallEtaleTopology.HasSheafCompose ((groupRingActionDiagram Λ G).obj i) :=
    fun _ => inferInstanceAs (Y.smallEtaleTopology.HasSheafCompose
      (ModuleCat.restrictScalars.{u + 1} (groupRingScalars Λ G)))
  have : ∀ i, X.smallEtaleTopology.HasSheafCompose ((groupRingActionDiagram Λ G).obj i) :=
    fun _ => inferInstanceAs (X.smallEtaleTopology.HasSheafCompose
      (ModuleCat.restrictScalars.{u + 1} (groupRingScalars Λ G)))
  exact isIso_coefficientMate_of_isLimit _ _ _ _ _ (groupRingActionDiagram Λ G) _
    (groupRingInvariantsCone.{u + 1} Λ G) (isLimitGroupRingInvariantsCone Λ G) fun _ =>
      isIso_coefficientSheafPullbackTwoSquare (smallEtaleBaseChange f) Y.smallEtaleTopology
        X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} (groupRingScalars Λ G))

/-- **`f^{-1}(𝒩^G) ≅ (f^{-1} 𝒩)^G`.** -/
def etaleModuleInverseImageInvariants {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleModuleInvariants Λ G Y ⋙ etaleModuleInverseImage.{u, 0} Λ f ≅
      etaleModuleInverseImage.{u, 0} (MonoidAlgebra Λ G) f ⋙ etaleModuleInvariants Λ G X :=
  asIso (inverseImageSheafComposeCoefficientMate Λ G f
    (ModuleCat.coextendScalars (groupRingAugmentation Λ G)))

/-- The comparison of a coefficient functor with extension by zero along an étale `j`. -/
abbrev extensionByZeroCoefficientMate {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (Gf : ModuleCat.{u + 1} (MonoidAlgebra Λ G) ⥤ ModuleCat.{u + 1} Λ)
    [U.smallEtaleTopology.HasSheafCompose Gf] [X.smallEtaleTopology.HasSheafCompose Gf] :=
  sheafComposeCoefficientMate (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology
    X.smallEtaleTopology
    (etaleModuleExtensionByZeroAdj.{u, 0} (MonoidAlgebra Λ G) j)
    (etaleModuleExtensionByZeroAdj.{u, 0} Λ j) Gf

omit [Fintype G] in
variable [Finite G] in
/-- **Extension by zero commutes with invariants**: the comparison `j_!(𝒩^G) ⟶ (j_! 𝒩)^G` is
invertible. -/
instance isIso_extensionByZeroCoefficientMate_invariants {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] :
    IsIso (extensionByZeroCoefficientMate Λ G j
      (ModuleCat.coextendScalars (groupRingAugmentation Λ G))) := by
  have := Fintype.ofFinite G
  have : ∀ i, U.smallEtaleTopology.HasSheafCompose ((groupRingActionDiagram Λ G).obj i) :=
    fun _ => inferInstanceAs (U.smallEtaleTopology.HasSheafCompose
      (ModuleCat.restrictScalars.{u + 1} (groupRingScalars Λ G)))
  have : ∀ i, X.smallEtaleTopology.HasSheafCompose ((groupRingActionDiagram Λ G).obj i) :=
    fun _ => inferInstanceAs (X.smallEtaleTopology.HasSheafCompose
      (ModuleCat.restrictScalars.{u + 1} (groupRingScalars Λ G)))
  exact isIso_coefficientMate_of_isLimit _ _ _ _ _ (groupRingActionDiagram Λ G) _
    (groupRingInvariantsCone.{u + 1} Λ G) (isLimitGroupRingInvariantsCone Λ G) fun _ =>
      isIso_coefficientPullbackTwoSquare (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology
        X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} (groupRingScalars Λ G))

/-- **`j_!(𝒩^G) ≅ (j_! 𝒩)^G`** for an étale morphism `j`. -/
def etaleModuleExtensionByZeroInvariants {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleModuleInvariants Λ G U ⋙ etaleModuleExtensionByZero.{u, 0} Λ j ≅
      etaleModuleExtensionByZero.{u, 0} (MonoidAlgebra Λ G) j ⋙ etaleModuleInvariants Λ G X :=
  asIso (extensionByZeroCoefficientMate Λ G j
    (ModuleCat.coextendScalars (groupRingAugmentation Λ G)))

end Stacks.EtaleCohomology

end
