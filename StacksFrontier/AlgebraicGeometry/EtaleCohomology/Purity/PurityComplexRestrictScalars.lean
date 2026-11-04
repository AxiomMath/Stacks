module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LowerShriekGysin
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusNatIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# `R g_!(R j_*(j⁻¹ H))` commutes with restriction of scalars

Let `ρ : Λ ⟶ Λ'` be a homomorphism of commutative rings, `j : U₀ ⟶ U` an open immersion and
`g : U ⟶ W` with a compactification. For a sheaf `H` of `Λ'`-modules on `U`,

`R g_!(R j_*(j⁻¹ res_ρ H)) ≅ res_ρ R g_!(R j_*(j⁻¹ H))`

in `D⁺(W_étale, Λ)`, where `res_ρ` acts on `D⁺` degreewise. Restriction along `j` and extension
by zero commute with `res_ρ` already on sheaves, and the derived direct images commute with
`res_ρ` (`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageRestrictScalars`). Hence the
vanishing of a cohomology sheaf of `R g_!(R j_*(j⁻¹ H))` may be checked over `Λ'`: this lets the
vanishing behind the Gysin map of the Leray step of the reduction of the weight bound of Weil II
to curves ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) be proved with the
coefficients `ℤ/ℓⁿ⁺¹` of cohomological purity rather than `ℤ_ℓ`.

## Main results

* `Stacks.EtaleCohomology.nonempty_derivedLowerShriek_purityComplex_restrictScalars_iso`.
* `Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_purityComplex_restrictScalars`.

## Implementation notes

The statements are made in the standard model `HasDerivedCategory.standard`, in which
`Stacks.EtaleCohomology.derivedLowerShriek` is defined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

universe u

namespace Stacks.EtaleCohomology

open Stacks.DerivedFunctor

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- **`R g_!(R j_*(j⁻¹ -))` commutes with restriction of scalars.** -/
theorem nonempty_derivedLowerShriek_purityComplex_restrictScalars_iso {U U₀ W : Scheme.{u}}
    (j : U₀ ⟶ U) [IsOpenImmersion j] (g : U ⟶ W) (jg : CompactificationOf (Over.mk g))
    (H : EtaleModules.{u, 0} Λ' U) :
    Nonempty ((derivedLowerShriek.{u, 0} g jg Λ).obj
        ((purityComplex Λ j).obj ((etaleModuleRestrictScalars ρ U).obj H)) ≅
      (etaleModuleRestrictScalars ρ W).mapDerivedCategoryPlus.obj
        ((derivedLowerShriek.{u, 0} g jg Λ').obj ((purityComplex Λ' j).obj H))) := by
  let e := jg.immersion
  let e1 : (etaleModuleRestriction.{u, 0} Λ j).obj ((etaleModuleRestrictScalars ρ U).obj H) ≅
      (etaleModuleRestrictScalars ρ U₀).obj ((etaleModuleRestriction.{u, 0} Λ' j).obj H) :=
    ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).app _).symm ≪≫
      (etaleModuleInverseImageRestrictScalars ρ j).app H ≪≫
      (etaleModuleRestrictScalars ρ U₀).mapIso
        ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ' j).app H)
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((etaleModuleRestriction.{u, 0} Λ' j).obj H)
  let e2 : (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleRestriction.{u, 0} Λ j).obj ((etaleModuleRestrictScalars ρ U).obj H)) ≅
      (etaleModuleRestrictScalars ρ U₀).mapDerivedCategoryPlus.obj K :=
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso e1 ≪≫
      ((etaleModuleRestrictScalars ρ U₀).mapDerivedCategoryPlusObjSingleIso _).symm
  let L := (etaleModuleDerivedDirectImage.{u, 0} Λ' j).obj K
  let e3 : (etaleModuleDerivedDirectImage.{u, 0} Λ j).obj
        ((etaleModuleRestrictScalars ρ U₀).mapDerivedCategoryPlus.obj K) ≅
      (etaleModuleRestrictScalars ρ U).mapDerivedCategoryPlus.obj L :=
    (etaleModuleDerivedDirectImageRestrictScalars ρ j).symm.app K
  let M := (etaleModuleDerivedExtensionByZero.{u, 0} Λ' e).obj L
  let e4 : (etaleModuleDerivedExtensionByZero.{u, 0} Λ e).obj
        ((etaleModuleRestrictScalars ρ U).mapDerivedCategoryPlus.obj L) ≅
      (etaleModuleRestrictScalars ρ jg.space).mapDerivedCategoryPlus.obj M :=
    (exactMapDerivedCategoryPlusIso (etaleModuleExtensionByZero.{u, 0} Λ e)).symm.app _ ≪≫
      (mapDerivedCategoryPlusCompIso (etaleModuleRestrictScalars ρ U)
        (etaleModuleExtensionByZero.{u, 0} Λ e)).app L ≪≫
      (mapDerivedCategoryPlusNatIso (etaleModuleExtensionByZeroRestrictScalars ρ e)).app L ≪≫
      (mapDerivedCategoryPlusCompIso (etaleModuleExtensionByZero.{u, 0} Λ' e)
        (etaleModuleRestrictScalars ρ jg.space)).symm.app L ≪≫
      (etaleModuleRestrictScalars ρ jg.space).mapDerivedCategoryPlus.mapIso
        ((exactMapDerivedCategoryPlusIso (etaleModuleExtensionByZero.{u, 0} Λ' e)).app L)
  let e5 : (etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase).obj
        ((etaleModuleRestrictScalars ρ jg.space).mapDerivedCategoryPlus.obj M) ≅
      (etaleModuleRestrictScalars ρ W).mapDerivedCategoryPlus.obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ' jg.toBase).obj M) :=
    (etaleModuleDerivedDirectImageRestrictScalars ρ jg.toBase).symm.app M
  exact ⟨(etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase).mapIso
    ((etaleModuleDerivedExtensionByZero.{u, 0} Λ e).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ j).mapIso e2 ≪≫ e3) ≪≫ e4) ≪≫ e5⟩

/-- **The vanishing of a cohomology sheaf of `R g_!(R j_*(j⁻¹ H))` may be checked before
restricting scalars.** -/
theorem isZero_homology_derivedLowerShriek_purityComplex_restrictScalars {U U₀ W : Scheme.{u}}
    (j : U₀ ⟶ U) [IsOpenImmersion j] (g : U ⟶ W) (jg : CompactificationOf (Over.mk g))
    (H : EtaleModules.{u, 0} Λ' U) (q : ℤ)
    (h : IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedLowerShriek.{u, 0} g jg Λ').obj ((purityComplex Λ' j).obj H)))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedLowerShriek.{u, 0} g jg Λ).obj
        ((purityComplex Λ j).obj ((etaleModuleRestrictScalars ρ U).obj H)))) := by
  obtain ⟨e⟩ := nonempty_derivedLowerShriek_purityComplex_restrictScalars_iso ρ j g jg H
  let c : (etaleModuleRestrictScalars ρ W).mapDerivedCategoryPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ q ≅
      DerivedCategory.Plus.homologyFunctor _ q ⋙ etaleModuleRestrictScalars ρ W :=
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (Stacks.Homology.derivedHomologyIso (etaleModuleRestrictScalars ρ W) q)
  exact ((etaleModuleRestrictScalars ρ W).map_isZero h).of_iso
    ((DerivedCategory.Plus.homologyFunctor _ q).mapIso e ≪≫ c.app _)

end Stacks.EtaleCohomology

end
