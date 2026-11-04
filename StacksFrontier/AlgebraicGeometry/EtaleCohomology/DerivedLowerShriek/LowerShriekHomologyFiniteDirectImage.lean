module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.FiniteComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LowerShriekHomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LowerShriekGysin

/-!
# `R⁰ g_!` of a direct image along a finite morphism

Let `i : Z ⟶ U` be finite and `g : U ⟶ V` separated of finite type with a compactification `j_g`,
over a quasi-compact quasi-separated `V`, such that `g ∘ i` is proper. For a sheaf `M` of
`Λ`-modules on `Z_étale` killed by a positive integer,

`R⁰ g_!(i_* M) ≅ (g ∘ i)_* M`,

naturally in `M`.

## Main definitions

* `Stacks.EtaleCohomology.lowerShriekHomologyZeroFiniteDirectImageIso`: the natural isomorphism
  `R⁰ g_!(i_* M) ≅ (g ∘ i)_* M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable (Λ : Type) [Ring Λ] {Z U V : Scheme.{u}} (i : Z ⟶ U) [IsFinite i] (g : U ⟶ V)
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [CompactSpace V]
  [QuasiSeparatedSpace V] (jg : CompactificationOf (Over.mk g)) [IsProper (i ≫ g)]
  (P : ObjectProperty (EtaleModules.{u, 0} Λ Z)) (hP : ∀ Q, P Q → ∃ m : ℕ, 0 < m ∧ m • 𝟙 Q = 0)

/-- The isomorphism `R⁰ g_!(i_* M) ≅ (g ∘ i)_* M`, natural in `M`, for a finite `i` and sheaves `M`
killed by a positive integer. -/
def lowerShriekHomologyZeroFiniteDirectImageIso :
    P.ι ⋙ etaleModuleDirectImage.{u, 0} Λ i ⋙ lowerShriekHomology Λ g jg 0 ≅
      P.ι ⋙ etaleModuleDirectImage.{u, 0} Λ (i ≫ g) :=
  let S := singleTorsionPlus Λ P hP
  let Φ := derivedLowerShriek.{u, 0} g jg Λ
  let H₀ := DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ V) 0
  let D₀ := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ Z) 0
  let e₁ : P.ι ⋙ etaleModuleDirectImage.{u, 0} Λ i ⋙ lowerShriekHomology Λ g jg 0 ≅
      P.ι ⋙ etaleModuleDirectImage.{u, 0} Λ i ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙ Φ ⋙ H₀ :=
    Functor.isoWhiskerLeft (P.ι ⋙ etaleModuleDirectImage.{u, 0} Λ i)
      (lowerShriekHomologyIsoSingle Λ g jg 0)
  let e₂ : P.ι ⋙ etaleModuleDirectImage.{u, 0} Λ i ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        Φ ⋙ H₀ ≅ P.ι ⋙ D₀ ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ i ⋙ Φ ⋙ H₀ :=
    Functor.isoWhiskerLeft P.ι (Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (etaleModuleDirectImage.{u, 0} Λ i) 0) (Φ ⋙ H₀))
  let e₃ : P.ι ⋙ D₀ ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ i ⋙ Φ ⋙ H₀ ≅
      S ⋙ (isTorsionPlus.{u, 0} Λ Z).ι ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ i ⋙ Φ ⋙ H₀ :=
    Iso.refl _
  let e₄ : S ⋙ (isTorsionPlus.{u, 0} Λ Z).ι ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ i ⋙ Φ ⋙ H₀ ≅
      S ⋙ (isTorsionPlus.{u, 0} Λ Z).ι ⋙
        derivedLowerShriek.{u, 0} (i ≫ g) (CompactificationOf.ofProper (i ≫ g)) Λ ⋙ H₀ :=
    Functor.isoWhiskerLeft S (Functor.isoWhiskerRight
      (derivedLowerShriekCompDirectImageIsoOfIsFinite Λ i g jg
        (CompactificationOf.ofProper (i ≫ g))).symm H₀)
  let e₅ : S ⋙ (isTorsionPlus.{u, 0} Λ Z).ι ⋙
        derivedLowerShriek.{u, 0} (i ≫ g) (CompactificationOf.ofProper (i ≫ g)) Λ ⋙ H₀ ≅
      P.ι ⋙ D₀ ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ (i ≫ g) ⋙ H₀ :=
    Functor.isoWhiskerLeft (S ⋙ (isTorsionPlus.{u, 0} Λ Z).ι)
      (Functor.isoWhiskerRight (derivedLowerShriekOfProperIso Λ (i ≫ g)) H₀)
  let e₆ : P.ι ⋙ D₀ ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ (i ≫ g) ⋙ H₀ ≅
      P.ι ⋙ etaleModuleDirectImage.{u, 0} Λ (i ≫ g) :=
    Functor.isoWhiskerLeft P.ι
      ((etaleModuleDirectImage.{u, 0} Λ (i ≫ g)).isoRightDerivedPlusSingle 0).symm
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆

end Stacks.EtaleCohomology

end
