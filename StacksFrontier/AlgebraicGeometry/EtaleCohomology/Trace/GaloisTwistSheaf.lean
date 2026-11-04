module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisTwistDual
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleGroupInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientFrobeniusTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero

/-!
# The twist functor on sheaves commutes with inverse image and extension by zero

Let `k₀` be a finite commutative ring, `G` a finite group, `Λ` a commutative `k₀`-algebra and `E` a
finite `Λ`-module with a `Λ`-linear action `ρ` of `G`.  The coefficient functor
`Ψ = Hom_{k₀[G]}(E^∨, -)` (`Stacks.EtaleCohomology.twistFunctor`) commutes with inverse image
along any morphism of schemes and with extension by zero along any étale morphism, on sheaves of
modules on small étale sites.

## Main results

* `Stacks.EtaleCohomology.isIso_inverseImageMate_twistFunctor`: `Ψ` commutes with inverse image.
* `Stacks.EtaleCohomology.isIso_extensionByZeroMate_twistFunctor`: `Ψ` commutes with extension by
  zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (k₀ : Type) [CommRing k₀] (G : Type) [Group G] (Λ : Type) [CommRing Λ] [Algebra k₀ Λ]
  (E : Type (u + 1)) [AddCommGroup E] [Module Λ E] [Module k₀ E] [IsScalarTower k₀ Λ E]
  (ρ : Representation Λ G E)

/-- After restriction of scalars along `k₀ → Λ`, the twist functor is `Hom_{k₀[G]}(E^∨, -)` with
`k₀` acting through `E^∨`. -/
def twistFunctorRestrictScalarsIso :
    sourceHomFunctor (MonoidAlgebra k₀ G) k₀ (TwistDual k₀ G Λ E ρ) ≅
      twistFunctor k₀ G Λ E ρ ⋙ ModuleCat.restrictScalars.{u + 1} (algebraMap k₀ Λ) :=
  NatIso.ofComponents
    (fun N => LinearEquiv.toModuleIso
      ({ toFun := fun φ => (SourceHom.ofLinearMap φ.toLinearMap : SourceHom _ Λ _ N)
         invFun := fun φ => SourceHom.ofLinearMap (SourceHom.toLinearMap (Λ := Λ) φ)
         map_add' := fun _ _ => rfl
         map_smul' := fun c φ => SourceHom.ext fun d => by
          change φ.toLinearMap (c • d) = φ.toLinearMap (algebraMap k₀ Λ c • d)
          rw [algebraMap_smul]
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl } :
        SourceHom (MonoidAlgebra k₀ G) k₀ (TwistDual k₀ G Λ E ρ) N ≃ₗ[k₀]
          (ModuleCat.restrictScalars.{u + 1} (algebraMap k₀ Λ)).obj
            ((twistFunctor k₀ G Λ E ρ).obj N)))
    (fun _ => rfl)

variable [Finite k₀] [Finite G] [Finite E]

/-- The group algebra `k₀[G]` of a finite group over a finite ring is finite. -/
instance : Finite (MonoidAlgebra k₀ G) :=
  Finite.of_injective (fun a : MonoidAlgebra k₀ G => (a.coeff : G → k₀))
    fun _ _ h => MonoidAlgebra.coeffEquiv.injective (Finsupp.ext (congrFun h))

/-- The dual `E^∨` of a finite module `E` over a finite ring `k₀` is finite. -/
instance : Finite (TwistDual k₀ G Λ E ρ) :=
  Finite.of_injective (fun ξ : TwistDual k₀ G Λ E ρ => (ξ.toDual : E → k₀))
    fun _ _ h => TwistDual.ext fun e => congrFun h e

/-- The dual `E^∨` is a finitely presented `k₀[G]`-module. -/
instance : Module.FinitePresentation (MonoidAlgebra k₀ G) (TwistDual k₀ G Λ E ρ) :=
  Module.finitePresentation_of_finite _ _

/-- The comparison for the twist functor is invertible as soon as those for restriction of scalars
along `k₀ → k₀[G]` and `k₀ → Λ` are, for any compatible left adjoints of direct image. -/
private theorem isIso_mate_twistFunctor_of_restrictScalars {C D : Type (u + 1)} [Category.{u} C]
    [Category.{u} D] (uf : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [uf.IsContinuous J K]
    {LA : Sheaf J (ModuleCat.{u + 1} (MonoidAlgebra k₀ G)) ⥤
      Sheaf K (ModuleCat.{u + 1} (MonoidAlgebra k₀ G))}
    {LB : Sheaf J (ModuleCat.{u + 1} Λ) ⥤ Sheaf K (ModuleCat.{u + 1} Λ)}
    {LC : Sheaf J (ModuleCat.{u + 1} k₀) ⥤ Sheaf K (ModuleCat.{u + 1} k₀)}
    (adjA : LA ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} (MonoidAlgebra k₀ G)) J K)
    (adjB : LB ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} Λ) J K)
    (adjC : LC ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} k₀) J K)
    [PreservesFiniteLimits LC]
    (hres₁ : IsIso (sheafComposeCoefficientMate uf J K adjA adjC
      (ModuleCat.restrictScalars.{u + 1} (algebraMap k₀ (MonoidAlgebra k₀ G)))).natTrans)
    (hres₂ : IsIso (sheafComposeCoefficientMate uf J K adjB adjC
      (ModuleCat.restrictScalars.{u + 1} (algebraMap k₀ Λ))).natTrans) :
    IsIso (sheafComposeCoefficientMate uf J K adjA adjB (twistFunctor k₀ G Λ E ρ)).natTrans :=
  isIso_coefficientMate_of_comp uf J K adjA adjB adjC (twistFunctor k₀ G Λ E ρ)
    (ModuleCat.restrictScalars.{u + 1} (algebraMap k₀ Λ))
    (isIso_sheafComposeCoefficientMate_of_iso uf J K adjA adjC
      (twistFunctorRestrictScalarsIso k₀ G Λ E ρ)
      (isIso_coefficientMate_sourceHomFunctor uf J K k₀ (MonoidAlgebra k₀ G) adjA adjC
        (TwistDual k₀ G Λ E ρ) hres₁))
    hres₂

/-- **Inverse image commutes with the twist functor**: the comparison
`g^{-1}(Ψ 𝒩) ⟶ Ψ(g^{-1} 𝒩)` is invertible. -/
theorem isIso_inverseImageMate_twistFunctor {X Y : Scheme.{u}} (g : X ⟶ Y) :
    IsIso (sheafComposeCoefficientMate (smallEtaleBaseChange g) Y.smallEtaleTopology
      X.smallEtaleTopology (etaleModuleInverseImageAdj.{u, 0} (MonoidAlgebra k₀ G) g)
      (etaleModuleInverseImageAdj.{u, 0} Λ g) (twistFunctor k₀ G Λ E ρ)).natTrans := by
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} k₀ g
  exact isIso_mate_twistFunctor_of_restrictScalars k₀ G Λ E ρ _ _ _
    (etaleModuleInverseImageAdj.{u, 0} (MonoidAlgebra k₀ G) g)
    (etaleModuleInverseImageAdj.{u, 0} Λ g) (etaleModuleInverseImageAdj.{u, 0} k₀ g)
    (isIso_coefficientSheafPullbackTwoSquare _ _ _ _)
    (isIso_coefficientSheafPullbackTwoSquare _ _ _ _)

/-- **Extension by zero commutes with the twist functor**: the comparison
`j_!(Ψ 𝒩) ⟶ Ψ(j_! 𝒩)` is invertible. -/
theorem isIso_extensionByZeroMate_twistFunctor {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    IsIso (sheafComposeCoefficientMate (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology
      X.smallEtaleTopology (etaleModuleExtensionByZeroAdj.{u, 0} (MonoidAlgebra k₀ G) j)
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j) (twistFunctor k₀ G Λ E ρ)).natTrans := by
  exact isIso_mate_twistFunctor_of_restrictScalars k₀ G Λ E ρ _ _ _
    (etaleModuleExtensionByZeroAdj.{u, 0} (MonoidAlgebra k₀ G) j)
    (etaleModuleExtensionByZeroAdj.{u, 0} Λ j) (etaleModuleExtensionByZeroAdj.{u, 0} k₀ j)
    (isIso_coefficientPullbackTwoSquare _ _ _ _) (isIso_coefficientPullbackTwoSquare _ _ _ _)

end Stacks.EtaleCohomology

end
