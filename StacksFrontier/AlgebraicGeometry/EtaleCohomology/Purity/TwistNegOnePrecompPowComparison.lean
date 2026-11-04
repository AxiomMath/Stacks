module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.TwistNegOneTowerInverseImage

/-!
# Precomposition with the `ℓ`-th power map, as a precomposition across a change of rings

Let `N' = ℓN`. Precomposition with the `ℓ`-th power map `p : μ_{N'} ⟶ μ_N`,
`𝓗om_{ℤ/N}(μ_N, G) ⟶ 𝓗om_{ℤ/N'}(μ_{N'}, G)` (`Stacks.Kummer.twistNegOnePrecompPow`, defined on
sections), is the precomposition across the change of rings `ℤ/N' → ℤ/N` characterized by its
evaluation `(α, m) ↦ α(p m)` (`Stacks.EtaleCohomology.etaleModuleRestrictScalarsHomPrecomp`):
`Stacks.Kummer.twistNegOnePrecompPow_eq_etaleModuleRestrictScalarsHomPrecomp`. This is what lets
the comparison `f⁻¹ 𝓗om(μ, H) ⟶ 𝓗om(f⁻¹ μ, f⁻¹ H)` be moved across the transitions of the Tate
twist in the tower form of cohomological purity of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The file also records the functoriality of the internal hom `𝓗om(-, -)` of sheaves of modules
under composition (`Stacks.ConstantSheaf.moduleSheafHomMap_comp_moduleSheafHomMap`) and the
naturality of the precomposition in its target
(`Stacks.EtaleCohomology.etaleModuleRestrictScalarsHomPrecomp_naturality`).

## Main results

* `Stacks.ConstantSheaf.moduleSheafHomMap_comp_moduleSheafHomMap`.
* `Stacks.EtaleCohomology.etaleModuleRestrictScalarsHomPrecomp_naturality`.
* `Stacks.Kummer.twistNegOnePrecompPow_eq_etaleModuleRestrictScalarsHomPrecomp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Stacks.ConstantSheaf

universe u v w x

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]

/-- **The internal hom is functorial**: `𝓗om(a, b) ≫ 𝓗om(a', b') = 𝓗om(a' ≫ a, b ≫ b')`. -/
theorem moduleSheafHomMap_comp_moduleSheafHomMap
    {F F' F'' G G' G'' : Sheaf J (ModuleCat.{x} Λ)} (a : F' ⟶ F) (b : G ⟶ G') (a' : F'' ⟶ F')
    (b' : G' ⟶ G'') :
    moduleSheafHomMap J Λ a b ≫ moduleSheafHomMap J Λ a' b' =
      moduleSheafHomMap J Λ (a' ≫ a) (b ≫ b') := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  show (J.overPullback (ModuleCat.{x} Λ) V.unop).map a' ≫
      ((J.overPullback (ModuleCat.{x} Λ) V.unop).map a ≫ α ≫
        (J.overPullback (ModuleCat.{x} Λ) V.unop).map b) ≫
      (J.overPullback (ModuleCat.{x} Λ) V.unop).map b' =
    (J.overPullback (ModuleCat.{x} Λ) V.unop).map (a' ≫ a) ≫ α ≫
      (J.overPullback (ModuleCat.{x} Λ) V.unop).map (b ≫ b')
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun t => _ ≫ _ ≫ t) (Category.assoc α _ _)

end Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

section Precomp

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {Y : Scheme.{u}}

/-- **Precomposition across a change of rings is natural in the target**:
`res_ρ 𝓗om(1, w) ≫ p^* = p^* ≫ 𝓗om(1, res_ρ w)`. -/
theorem etaleModuleRestrictScalarsHomPrecomp_naturality {M : EtaleModules.{u, 0} Λ' Y}
    {M' : EtaleModules.{u, 0} Λ Y} (p : M' ⟶ (etaleModuleRestrictScalars ρ Y).obj M)
    {H H' : EtaleModules.{u, 0} Λ' Y} (w : H ⟶ H') :
    (etaleModuleRestrictScalars ρ Y).map (moduleSheafHomMap Y.smallEtaleTopology Λ' (𝟙 M) w) ≫
        etaleModuleRestrictScalarsHomPrecomp ρ p H' =
      etaleModuleRestrictScalarsHomPrecomp ρ p H ≫
        moduleSheafHomMap Y.smallEtaleTopology Λ (𝟙 M')
          ((etaleModuleRestrictScalars ρ Y).map w) := by
  refine (tensorHomBijective_moduleSheafHomEvaluation Y.smallEtaleTopology Λ M'
    ((etaleModuleRestrictScalars ρ Y).obj H') _).injective ?_
  show _ ▷ M' ≫ _ = _ ▷ M' ≫ _
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
    etaleModuleRestrictScalarsHomPrecomp_spec,
    moduleSheafHomMap_whiskerRight_comp_moduleSheafHomEvaluation,
    etaleModuleRestrictScalarsHomPrecomp_spec_assoc, ← whisker_exchange_assoc,
    whiskerRight_comp_etaleModuleRestrictScalarsTensorHom_assoc, ← Functor.map_comp,
    moduleSheafHomMap_whiskerRight_comp_moduleSheafHomEvaluation, Functor.map_comp]

end Precomp

end Stacks.EtaleCohomology

namespace Stacks.Kummer

open Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable (X : Scheme.{u}) (ℓ N N' : ℕ) (hN : ℓ * N = N') [NeZero N] [NeZero N']

/-- **Precomposition with the `ℓ`-th power map is precomposition across the change of rings
`ℤ/ℓN → ℤ/N`**: both have evaluation `(α, m) ↦ α(p m)`. -/
theorem twistNegOnePrecompPow_eq_etaleModuleRestrictScalarsHomPrecomp
    (G : EtaleModules.{u, 0} (ZMod N) X) :
    twistNegOnePrecompPow.{u, 0} X ℓ N N' hN G =
      etaleModuleRestrictScalarsHomPrecomp (ZMod.castHom (dvd_of_mul_eq hN) (ZMod N))
        (rootsOfUnityModulePowMap.{u, 0} X ℓ N N' hN) G := by
  refine (tensorHomBijective_moduleSheafHomEvaluation X.smallEtaleTopology (ZMod N')
    (rootsOfUnityModule.{u, 0} X N')
    ((etaleModuleRestrictScalars (ZMod.castHom (dvd_of_mul_eq hN) (ZMod N)) X).obj G)
      _).injective ?_
  refine Eq.trans ?_ (etaleModuleRestrictScalarsHomPrecomp_spec
    (ZMod.castHom (dvd_of_mul_eq hN) (ZMod N)) (rootsOfUnityModulePowMap.{u, 0} X ℓ N N' hN) G).symm
  refine sheafTensor_hom_ext fun U α m => ?_
  refine (sheafTensorBilinear_whiskerRight_comp _ _ U α m).trans ?_
  refine Eq.trans ?_ (sheafTensorBilinear_whiskerLeft_comp _ _ U α m).symm
  refine Eq.trans ?_ (sheafTensorBilinear_comp _ _ U α _).symm
  refine (tensorBilinear_moduleSheafHomEvaluation _ _ _ _ U _ m).trans ?_
  refine Eq.trans ?_ (congrArg (((etaleModuleRestrictScalars (ZMod.castHom (dvd_of_mul_eq hN)
    (ZMod N)) X).map (moduleSheafHomEvaluation X.smallEtaleTopology (ZMod N)
      (rootsOfUnityModule.{u, 0} X N) G)).hom.app U).hom
    (tensorBilinear_etaleModuleRestrictScalarsTensorHom _ _ _ U α _).symm)
  refine Eq.trans ?_ (sheafTensorBilinear_eq_app (moduleSheafHomEvaluation X.smallEtaleTopology
    (ZMod N) (rootsOfUnityModule.{u, 0} X N) G) U α _)
  refine Eq.trans ?_ (tensorBilinear_moduleSheafHomEvaluation _ _ _ _ U α _).symm
  rfl

end Stacks.Kummer

end
