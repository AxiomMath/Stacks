module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TwoTermTruncationConnecting
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsComparison
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimensionPlus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologySequence

/-!
# The Gysin map of `R² g_!` from the higher direct images along the complement of a divisor

Let `j : U₀ ⟶ U` be an open immersion, `g : U ⟶ V` a morphism with a compactification `j_g`,
and `Λ` a ring. For a sheaf `H` of `Λ`-modules on `U_étale`, the complex
`X_H = R j_*(j⁻¹ H)` (`Stacks.EtaleCohomology.purityComplex`) has `H⁰(X_H) = j_* j⁻¹ H` and
`H¹(X_H) = R¹ j_*(j⁻¹ H)`. The connecting map of its truncation triangle carried by `Rg_!`
(`DerivedCategory.Plus.truncationConnecting`) is a map

`R⁰ g_!(R¹ j_*(j⁻¹ H)) ⟶ R² g_!(j_* j⁻¹ H)`,

natural in `H` (`Stacks.EtaleCohomology.lowerShriekGysin`). When `j` is the complement of a
smooth divisor `i : Z ⟶ U` of a relative curve and `H` is locally constant, cohomological purity
identifies `j_* j⁻¹ H` with `H` and `R¹ j_*(j⁻¹ H)` with `i_*` of the Tate twist of `i⁻¹ H`, and the
map is the Gysin map of the Leray step of the reduction of the weight bound of Weil II to curves
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)). It is an epimorphism as soon as
`R^q j_*(j⁻¹ H) = 0` for `q ≥ 2` and `H²(Rg_! X_H) = 0`
(`Stacks.EtaleCohomology.epi_lowerShriekGysin_app`).

## Main definitions

* `Stacks.EtaleCohomology.purityComplex`: `H ↦ R j_*(j⁻¹ H)`.
* `Stacks.EtaleCohomology.lowerShriekGysin`: the natural map
  `R⁰ g_!(R¹ j_*(j⁻¹ H)) ⟶ R² g_!(j_* j⁻¹ H)`.

## Main results

* `Stacks.EtaleCohomology.epi_lowerShriekGysin_app`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`, and so do the statements here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable (Λ : Type) [Ring Λ] {U U₀ V : Scheme.{u}} (j : U₀ ⟶ U) [IsOpenImmersion j] (g : U ⟶ V)
  (jg : CompactificationOf (Over.mk g))

/-- **The complex `R j_*(j⁻¹ H)`** of the higher direct images along `j` of the restriction of
`H`, functorially in `H`. -/
abbrev purityComplex :
    EtaleModules.{u, 0} Λ U ⥤ DerivedCategory.Plus (EtaleModules.{u, 0} Λ U) :=
  etaleModuleRestriction.{u, 0} Λ j ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
    etaleModuleDerivedDirectImage.{u, 0} Λ j

/-- `R^q g_!` of a sheaf, read through the single functor into `D⁺`: the identification of
`Stacks.EtaleCohomology.lowerShriekHomology` with `G ↦ H^q(Rg_!(G[0]))` for the single functor
`DerivedCategory.Plus.singleFunctor`. -/
def lowerShriekHomologyIsoSingle (q : ℤ) :
    lowerShriekHomology Λ g jg q ≅ DerivedCategory.Plus.singleFunctor _ 0 ⋙
      derivedLowerShriek.{u, 0} g jg Λ ⋙ DerivedCategory.Plus.homologyFunctor _ q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (StacksDraft.DerivedSectionsComparison.singlePlusQIso (EtaleModules.{u, 0} Λ U))
      (derivedLowerShriek.{u, 0} g jg Λ ⋙ DerivedCategory.Plus.homologyFunctor _ q)

/-- The identification of the source: `R⁰ g_!(R¹ j_*(j⁻¹ H)) ≅ H⁰(Rg_!(H¹(X_H)[0]))`. -/
def lowerShriekGysinSourceIso :
    etaleModuleRestriction.{u, 0} Λ j ⋙ (etaleModuleDirectImage.{u, 0} Λ j).rightDerived 1 ⋙
        lowerShriekHomology Λ g jg 0 ≅
      purityComplex Λ j ⋙ DerivedCategory.Plus.homologyFunctor _ 1 ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙ derivedLowerShriek.{u, 0} g jg Λ ⋙
          DerivedCategory.Plus.homologyFunctor _ 0 :=
  Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (Stacks.DerivedIndexing.rightDerivedIso
        (etaleModuleDirectImage.{u, 0} Λ j) 1) _ ≪≫
        Functor.isoWhiskerLeft _ (lowerShriekHomologyIsoSingle Λ g jg 0))

/-- The identification of the target: `H²(Rg_!(H⁰(X_H)[0])) ≅ R² g_!(j_* j⁻¹ H)`. -/
def lowerShriekGysinTargetIso :
    purityComplex Λ j ⋙ DerivedCategory.Plus.homologyFunctor _ 0 ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙ derivedLowerShriek.{u, 0} g jg Λ ⋙
          DerivedCategory.Plus.homologyFunctor _ 2 ≅
      etaleModuleRestriction.{u, 0} Λ j ⋙ etaleModuleDirectImage.{u, 0} Λ j ⋙
        lowerShriekHomology Λ g jg 2 :=
  Functor.isoWhiskerLeft (etaleModuleRestriction.{u, 0} Λ j)
    (Functor.isoWhiskerRight
        ((etaleModuleDirectImage.{u, 0} Λ j).isoRightDerivedPlusSingle 0).symm _ ≪≫
      Functor.isoWhiskerLeft _ (lowerShriekHomologyIsoSingle Λ g jg 2).symm)

/-- **The Gysin map** `R⁰ g_!(R¹ j_*(j⁻¹ H)) ⟶ R² g_!(j_* j⁻¹ H)`, natural in `H`: the connecting
map of the truncation triangle of `R j_*(j⁻¹ H)` carried by `Rg_!`. -/
def lowerShriekGysin :
    etaleModuleRestriction.{u, 0} Λ j ⋙ (etaleModuleDirectImage.{u, 0} Λ j).rightDerived 1 ⋙
        lowerShriekHomology Λ g jg 0 ⟶
      etaleModuleRestriction.{u, 0} Λ j ⋙ etaleModuleDirectImage.{u, 0} Λ j ⋙
        lowerShriekHomology Λ g jg 2 :=
  (lowerShriekGysinSourceIso Λ j g jg).hom ≫
    Functor.whiskerLeft (purityComplex Λ j)
      (DerivedCategory.Plus.truncationConnecting (derivedLowerShriek.{u, 0} g jg Λ)) ≫
    (lowerShriekGysinTargetIso Λ j g jg).hom

/-- **The Gysin map is an epimorphism** at `H` when the higher direct images `R^q j_*(j⁻¹ H)`,
`q ≥ 2`, vanish and `Rg_!(R j_*(j⁻¹ H))` has no `H²`. -/
theorem epi_lowerShriekGysin_app (H : EtaleModules.{u, 0} Λ U)
    (h2 : ∀ q : ℕ, 2 ≤ q → IsZero (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj
      ((etaleModuleRestriction.{u, 0} Λ j).obj H)))
    (hX : IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} g jg Λ).obj ((purityComplex Λ j).obj H)))) :
    Epi ((lowerShriekGysin Λ j g jg).app H) := by
  let X := (purityComplex Λ j).obj H
  have : X.IsGE 0 := Functor.isGE_rightDerivedFunctorPlus_obj _ _ 0
  have : X.IsLE 1 := by
    have h := Stacks.BoundedCohomologicalDimension.isLE_rightDerivedFunctorPlus_single
      (etaleModuleDirectImage.{u, 0} Λ j)
      ((etaleModuleRestriction.{u, 0} Λ j).obj H) 1 0 (fun p hp => h2 p (by omega))
    rw [zero_add] at h
    exact (DerivedCategory.Plus.isLE_ι_obj_iff X 1).1 h
  have := DerivedCategory.Plus.epi_truncationConnecting_app (derivedLowerShriek.{u, 0} g jg Λ) X hX
  simp only [lowerShriekGysin, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

end Stacks.EtaleCohomology

end
