module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.HigherDirectImageClassMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerDivisorSection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineStalkCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ModuleSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleZariskiCohomology

/-!
# The purity map `𝓗om(μ_N, H) ⟶ R¹ j_*(j⁻¹ H)` of an effective Cartier divisor

Let `i : Z ⟶ U` be a closed immersion with local equations everywhere, `j : U₀ ⟶ U` an open
immersion into the complement of `Z`, and `N` invertible on `U`. The fundamental class of `Z`
(`Stacks.EtaleCohomology.Purity.kummerDivisorSection`) is a global section of `R¹ j_* μ_N`; read
through `j⁻¹ μ_N ≅ μ_N` (`Stacks.EtaleCohomology.Purity.pullbackRootsOfUnityIso`) it is a global
section `s` of `R¹ j_*(j⁻¹ μ_N)` (`Stacks.EtaleCohomology.Purity.kummerDivisorPullbackSection`).

For a sheaf `H` of `ℤ/N`-modules on `U`, a section of the Tate twist `H(-1) = 𝓗om(μ_N, H)` over
`V` is a morphism `α : μ_N|_V ⟶ H|_V`, and `α ↦ α_* s` is a morphism of abelian sheaves
`𝓗om(μ_N, H) ⟶ R¹ j_*(j⁻¹ H)` (`Stacks.EtaleCohomology.higherDirectImageClassMap`). Since
both sides are killed by `N`, it is `ℤ/N`-linear: this is the purity map
`Stacks.EtaleCohomology.Purity.kummerClassMap` of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), from the twist to `R¹ j_*(j⁻¹ H)` of
sheaves of `ℤ/N`-modules. It is natural in `H`
(`Stacks.EtaleCohomology.Purity.twistNegOneModuleMap_comp_kummerClassMap`).

## Main definitions

* `Stacks.EtaleCohomology.Purity.kummerDivisorPullbackSection`.
* `Stacks.EtaleCohomology.Purity.kummerClassMapAb`.
* `Stacks.EtaleCohomology.Purity.kummerClassMap`.

## Main results

* `Stacks.EtaleCohomology.Purity.etaleModuleForgetAb_map_kummerClassMap`.
* `Stacks.EtaleCohomology.Purity.twistNegOneModuleMap_comp_kummerClassMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe w u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

variable {U₀ U : Scheme.{u}} (j : U₀ ⟶ U) [IsOpenImmersion j]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U) Ab.{u + 1})] (N : ℕ) [NeZero N]
  (hN : IsUnit ((N : ℕ) : Γ(U₀, ⊤))) (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤))) {Z : Scheme.{u}}
  (i : Z ⟶ U) [IsClosedImmersion i] (hj : Set.range j.base ⊆ (Set.range i.base)ᶜ)
  (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t)

/-- **The fundamental class of `Z` in `R¹ j_*(j⁻¹ μ_N)`**: the fundamental class
`Stacks.EtaleCohomology.Purity.kummerDivisorSection` in `R¹ j_* μ_N`, carried along
`μ_N ≅ j⁻¹ μ_N`, as a global section of `R¹ j_*` of the inverse image of the underlying abelian
sheaf of `μ_N` as a sheaf of `ℤ/N`-modules. -/
def kummerDivisorPullbackSection :
    ToType ((((smallEtalePushforwardAb j).rightDerived 1).obj ((smallEtalePullbackAb j).obj
      (smallEtaleModuleSheafForgetAb (ZMod N) (rootsOfUnityModule.{u, 0} U N)))).obj.obj
        (op ((opensToEtale U).obj ⊤))) :=
  (((smallEtalePushforwardAb j).rightDerived 1).map
      (pullbackRootsOfUnityIso j N hNU).inv).hom.app (op ((opensToEtale U).obj ⊤))
    (kummerDivisorSection j (NeZero.ne N) hN hNU i hj hcov)

/-- **The purity map on underlying abelian sheaves**: `𝓗om(μ_N, H) ⟶ R¹ j_*(j⁻¹ H)`,
`α ↦ α_* s`, for `s` the fundamental class of `Z`. -/
def kummerClassMapAb (H : Sheaf (smallEtaleTopology U) (ModuleCat.{u + 1} (ZMod N))) :
    smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N H) ⟶
      ((smallEtalePushforwardAb j).rightDerived 1).obj
        ((smallEtalePullbackAb j).obj (smallEtaleModuleSheafForgetAb (ZMod N) H)) :=
  higherDirectImageClassMap j 1 (isTerminal_opensToEtale_top U)
    (kummerDivisorPullbackSection j N hN hNU i hj hcov)

/-- The underlying abelian sheaf of `R¹ j_*(j⁻¹ H)`, for `H` a sheaf of `ℤ/N`-modules, is
`R¹ j_*` of the inverse image of the underlying abelian sheaf of `H`. -/
def etaleModuleForgetRightDerivedRestrictionIso
    (H : Sheaf (smallEtaleTopology U) (ModuleCat.{u + 1} (ZMod N))) :
    (etaleModuleForgetAb.{u, 0} (ZMod N) U).obj
        (((etaleModuleDirectImage.{u, 0} (ZMod N) j).rightDerived 1).obj
          ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H)) ≅
      ((smallEtalePushforwardAb j).rightDerived 1).obj
        ((smallEtalePullbackAb j).obj (smallEtaleModuleSheafForgetAb (ZMod N) H)) :=
  etaleModuleForgetRightDerivedDirectImageIso (ZMod N) j _ 1 ≪≫
    ((smallEtalePushforwardAb j).rightDerived 1).mapIso
      ((smallEtalePullbackAbIsoEtaleRestriction j).app
        (smallEtaleModuleSheafForgetAb (ZMod N) H)).symm

/-- **The purity map `𝓗om(μ_N, H) ⟶ R¹ j_*(j⁻¹ H)`** of sheaves of `ℤ/N`-modules,
`α ↦ α_* s` for `s` the fundamental class of `Z`: the map
`Stacks.EtaleCohomology.Purity.kummerClassMapAb` of underlying abelian sheaves, which is
`ℤ/N`-linear since both sides are killed by `N`. -/
def kummerClassMap (H : Sheaf (smallEtaleTopology U) (ModuleCat.{u + 1} (ZMod N))) :
    twistNegOneModule.{u, 0} U N H ⟶
      ((etaleModuleDirectImage.{u, 0} (ZMod N) j).rightDerived 1).obj
        ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H) :=
  (Stacks.ArtinSchreier.etaleModuleForgetZModFullyFaithful U N).preimage
    (kummerClassMapAb j N hN hNU i hj hcov H ≫
      (etaleModuleForgetRightDerivedRestrictionIso j N H).inv)

/-- The purity map on underlying abelian sheaves is `α ↦ α_* s`. -/
theorem etaleModuleForgetAb_map_kummerClassMap
    (H : Sheaf (smallEtaleTopology U) (ModuleCat.{u + 1} (ZMod N))) :
    (etaleModuleForgetAb.{u, 0} (ZMod N) U).map (kummerClassMap j N hN hNU i hj hcov H) =
      kummerClassMapAb j N hN hNU i hj hcov H ≫
        (etaleModuleForgetRightDerivedRestrictionIso j N H).inv :=
  (Stacks.ArtinSchreier.etaleModuleForgetZModFullyFaithful U N).map_preimage _

end Stacks.EtaleCohomology.Purity

end
