module

public import StacksFrontier.Cotangent.ChartSiteDifferentialsPresheaf
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SchemeOverRingComparison
public import StacksFrontier.Cotangent.SchemeOverRingSectionwise
public import StacksFrontier.Cotangent.ChartSiteLiftedModules
public import StacksFrontier.Cotangent.ChartSiteStandardResolutionEvaluation
public import StacksFrontier.Cotangent.StandardResolutionChartsModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleLevelSheafification

/-!
# The cotangent complex of a scheme over a ring as a derived lower shriek

Let `Λ` be a ring and `X` a scheme over `Λ`. Let `C_{X/Λ}` be the site of polynomial charts of
Tag 08VA: the diagrams `U ⟶ A` with `U ⊆ X` open and `A` an affine space over `Spec Λ`, with the
topology inherited from the Zariski site, its sheaves of rings `𝒪 : (U ⟶ A) ↦ Γ(A, 𝒪_A)` and
`𝒪̲_X = π⁻¹𝒪_X`, the projection `π : Sh(C_{X/Λ}) ⟶ Sh(X_Zar)` and the morphism of ringed topoi
`i : (Sh(C_{X/Λ}), 𝒪̲_X) ⟶ (Sh(C_{X/Λ}), 𝒪)`. This file proves Tag 08T9:

`L_{X/Λ} = Lπ_!(Li^*Ω_{𝒪/Λ̲}) = Lπ_!(i^*Ω_{𝒪/Λ̲}) = Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)` in `D(𝒪_X)`.

The proof is the source's. `Ω_{𝒪/Λ̲}` is flat, so `Li^*Ω = i^*Ω`, and `i^*` is extension of scalars
along `i♯` (`StacksFrontier/Cotangent/ChartSiteFlatDifferentials.lean`). By Tag 08VB at module
coefficients `Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)` is the sheafification of `U ↦ (Ω ⊗ 𝒪̲_X)(A_{•,U})` for the
charts `A_{n,U} = Spec(P_{n,U})` of the standard resolutions of the `𝒪_X(U)` over `Λ`; that complex
is the sheafification of `U ↦ Ω_{P_{•,U}/Λ} ⊗_{P_{•,U}} 𝒪_X(U) = L_{𝒪_X(U)/Λ}`, which is
`L_{𝒪_X/Λ̲}` by Tag 08SX, and that is `L_{X/Λ} = L_{X/Spec Λ}` by Tag 08V6.

## Universes

A chart records a `Type u` of variables, so `C_{X/Λ}` has objects in `Type (u + 1)` and its sheaves
are formed in the coefficient universe `u + 1`; the derived lower shriek `Lπ_!` lands in the
derived category of sheaves of `𝒪_X`-modules in that universe, where `𝒪_X` is presented by the
`ULift` of its section rings. `L_{X/Λ}`, formed in the universe `u` of `X`, is read there through
the exact lift `AlgebraicGeometry.PolynomialChart.chartBaseLift` of sections.

## Main definitions

* `AlgebraicGeometry.PolynomialChart.chartDerivedLowerShriek`: `Lπ_! : D(π⁻¹𝒪_X) ⥤ D(𝒪_X)` on
  sheaves of modules.
* `AlgebraicGeometry.PolynomialChart.chartBaseLift`: sheaves of `𝒪_X`-modules read in the
  coefficient universe of the chart topos.

## Main results

* `AlgebraicGeometry.PolynomialChart.cotangentComplexIsoDerivedLowerShriekInverseImage`,
  `AlgebraicGeometry.PolynomialChart.derivedLowerShriekInverseImageDifferentialsIso` and
  `AlgebraicGeometry.PolynomialChart.derivedLowerShriekPulledBackDifferentialsIso`: the three
  isomorphisms of **Stacks 08T9**, built from the canonical maps of the proof.

## References

* [Stacks Project, Tag 08T9](https://stacks.math.columbia.edu/tag/08T9)
* [Stacks Project, Tag 08VA](https://stacks.math.columbia.edu/tag/08VA)
* [Stacks Project, Tag 08VB](https://stacks.math.columbia.edu/tag/08VB)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08V6](https://stacks.math.columbia.edu/tag/08V6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sites.FibredCategory.FibredCategorySituation Stacks.Cohomology.DerivedLowerShriek

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
  (structureMap : X ⟶ Spec (CommRingCat.of Λ))

attribute [local instance] HasDerivedCategory.standard hasSheafify_addCommGrpCat_topology_succ
  wEqualsLocallyBijective_topology_succ

/-- `𝒪_X` presented in the coefficient universe of the chart topos, as a sheaf of rings on the base
site of the fibred category situation of Tag 08P8. -/
abbrev chartBaseRing : Sheaf (fibredCategorySituation Λ X structureMap).base.J RingCat.{u + 1} :=
  ringSheaf (liftedStructureSheaf.{u, u} X)

/-- The equivalence between `π⁻¹𝒪_X`-modules in the two presentations of `π⁻¹𝒪_X` on the chart
site: restriction of scalars along `chartStructureRingIso`. -/
abbrev chartStructureModulesEquivalence :
    SheafOfModules.{u + 1} (ringSheaf (chartStructureSheaf.{u, u + 1} Λ X structureMap)) ≌
      SheafOfModules.{u + 1} (chartStructureRing Λ X structureMap) :=
  Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (chartStructureRingIso Λ X structureMap)

/-- The comparison of the two presentations of `π⁻¹𝒪_X`-modules is additive, being an equivalence
of preadditive categories. -/
instance additive_chartStructureModulesEquivalence_functor :
    (chartStructureModulesEquivalence Λ X structureMap).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `Lπ_! : D(π⁻¹𝒪_X) ⥤ D(𝒪_X)` for the projection `π` of the site of polynomial charts to the
Zariski site of `X`, on sheaves of modules over `π⁻¹𝒪_X`: the derived lower shriek of the fibred
category situation of Tag 08P8, with `𝒪_X` presented in the coefficient universe. -/
abbrev chartDerivedLowerShriek :
    DerivedCategory (SheafOfModules.{u + 1}
        (ringSheaf (chartStructureSheaf.{u, u + 1} Λ X structureMap))) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (chartBaseRing Λ X structureMap)) :=
  (chartStructureModulesEquivalence Λ X structureMap).functor.mapDerivedCategory ⋙
    (fibredCategorySituation Λ X structureMap).derivedModuleLowerShriek
      (chartBaseRing Λ X structureMap)

/-- Degreewise sheafification of complexes of presheaves of `𝒪_X`-modules, in the coefficient
universe of the chart topos. -/
abbrev chartBaseSheafification :
    CochainComplex (PresheafOfModules.{u + 1} (chartBaseRing Λ X structureMap).obj) ℤ ⥤
      CochainComplex (SheafOfModules.{u + 1} (chartBaseRing Λ X structureMap)) ℤ :=
  (PresheafOfModules.sheafification.{u + 1}
    (𝟙 (chartBaseRing Λ X structureMap).obj)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The complex of presheaves `U ↦ G(A_{•,U})` of the standard resolution charts. -/
abbrev chartPointMooreCochain :
    PresheafOfModules.{u + 1} (chartStructureRing Λ X structureMap).obj ⥤
      CochainComplex (PresheafOfModules.{u + 1} (chartBaseRing Λ X structureMap).obj) ℤ :=
  modulePointMooreCochain (fibredCategorySituation Λ X structureMap)
    (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
    (chartBaseRing Λ X structureMap).obj

/-- **`Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X)` is computed by the standard resolutions** (Stacks 08VB at module
coefficients): it is the complex of sheaves whose term in degree `-n` is the sheafification of
`U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X)(A_{n,U})`. The isomorphism is `derivedModuleLowerShriekIso`, after the
canonical identification of the two presentations of `π⁻¹𝒪_X`. -/
def chartDerivedLowerShriekBaseChangeIso :
    (chartDerivedLowerShriek Λ X structureMap).obj
        ((DerivedCategory.singleFunctor _ 0).obj (chartDifferentialsBaseChange Λ X structureMap)) ≅
      DerivedCategory.Q.obj (modulePointSheafComplex (chartBaseRing Λ X structureMap)
        (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
          (chartDifferentialsBaseChangeRestricted Λ X structureMap)) :=
  ((fibredCategorySituation Λ X structureMap).derivedModuleLowerShriek
      (chartBaseRing Λ X structureMap)).mapIso
        ((Functor.mapDerivedCategorySingleFunctor
          (chartStructureModulesEquivalence Λ X structureMap).functor 0).app
            (chartDifferentialsBaseChange Λ X structureMap)) ≪≫
    derivedModuleLowerShriekIso (chartBaseRing Λ X structureMap)
      (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
      (exists_homotopyEquivalences_standardResolutionChart Λ X structureMap)
      (chartDifferentialsBaseChangeRestricted Λ X structureMap)

/-- The canonical map from `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` to the sections of
`Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`, read over `𝒪̲_X`. -/
def chartBaseChangePresheafToSections :
    chartBaseChangePresheaf Λ X structureMap ⟶
      (chartDifferentialsBaseChangeRestricted Λ X structureMap).val :=
  chartBaseChangePresheafMap Λ X structureMap ≫
    (PresheafOfModules.isoMk (fun _ => ModuleCat.restrictScalarsId'App _ rfl _)
      (fun _ _ _ => rfl)).hom

/-- The canonical map is inverted by sheafification. -/
theorem W_chartBaseChangePresheafToSections :
    (topology Λ X structureMap).W
      ((PresheafOfModules.toPresheaf _).map
        (chartBaseChangePresheafToSections Λ X structureMap)) := by
  refine (congrArg (fun g => (topology Λ X structureMap).W g)
    ((PresheafOfModules.toPresheaf _).map_comp _ _)).mpr ?_
  exact MorphismProperty.comp_mem _ _ _ (W_chartBaseChangePresheafMap Λ X structureMap)
    (ObjectProperty.isLocal_of_isIso _ ((PresheafOfModules.toPresheaf _).mapIso
      (PresheafOfModules.isoMk (fun P => ModuleCat.restrictScalarsId'App _ rfl _)
        (fun _ _ _ => rfl))).hom)

/-- **The complex computing `Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X)` is the sheafification of
`U ↦ (𝒪_X(U) ⊗_{Γ(A_{•,U})} Ω_{Γ(A_{•,U})/Λ})`**, evaluated on the charts of the standard
resolutions before any sheafification on the chart site. -/
def chartModulePointSheafComplexIso :
    (chartBaseSheafification Λ X structureMap).obj
        ((chartPointMooreCochain Λ X structureMap).obj (chartBaseChangePresheaf Λ X structureMap)) ≅
      modulePointSheafComplex (chartBaseRing Λ X structureMap)
        (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
          (chartDifferentialsBaseChangeRestricted Λ X structureMap) :=
  have := isIso_sheafification_map_modulePointMooreCochain_map
    (fibredCategorySituation Λ X structureMap)
    (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
    (chartBaseRing Λ X structureMap) (chartBaseChangePresheafToSections Λ X structureMap)
    (W_chartBaseChangePresheafToSections Λ X structureMap)
  asIso ((chartBaseSheafification Λ X structureMap).map
    ((chartPointMooreCochain Λ X structureMap).map
      (chartBaseChangePresheafToSections Λ X structureMap)))

/-- The lift of sheaves of `𝒪_X`-modules to the coefficient universe of the chart topos, read over
`𝒪_X` as the base ring of the fibred category situation. -/
abbrev chartBaseLift :
    SheafOfModules.{u} (ringSheaf X.sheaf) ⥤
      SheafOfModules.{u + 1} (chartBaseRing Λ X structureMap) :=
  liftStructureModules.{u, u} X

/-- The lift is additive. -/
instance additive_chartBaseLift : (chartBaseLift Λ X structureMap).Additive :=
  additive_liftStructureModules.{u, u} X

/-- The lift is exact. -/
instance preservesFiniteLimits_chartBaseLift :
    PreservesFiniteLimits (chartBaseLift Λ X structureMap) :=
  preservesFiniteLimits_liftStructureModules.{u, u} X

/-- The lift is exact. -/
instance preservesFiniteColimits_chartBaseLift :
    PreservesFiniteColimits (chartBaseLift Λ X structureMap) :=
  preservesFiniteColimits_liftStructureModules.{u, u} X

/-- **Tag 08V6, lifted**: `L_{𝒪_X/Λ̲} ⟶ L_{X/Spec Λ}` stays a quasi-isomorphism after lifting to
the coefficient universe of the chart topos. -/
theorem quasiIso_chartBaseLift_constantComparison :
    QuasiIso (((chartBaseLift Λ X structureMap).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (SchemeOverRing.constantComparison Λ structureMap)) := by
  have hq := SchemeOverRing.quasiIso_constantComparison Λ structureMap
  have : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat.{u, u, u + 1} _
  have : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat.{u, u, u + 1} _
  exact @quasiIso_liftStructureModules_map.{u, u} X _ _ _ _
    (SchemeOverRing.constantComparison Λ structureMap) hq

/-- `L_{𝒪_X/Λ̲}`, lifted to the coefficient universe of the chart topos, is the sheafification of
the lift of `U ↦ L_{𝒪_X(U)/Λ}` (Tag 08SX over the constant presheaf `Λ`). -/
def chartLiftedSectionwiseCotangentComplexIso :
    (chartBaseSheafification Λ X structureMap).obj
        (((liftStructurePresheafModules.{u, u} X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (SchemeOverRing.sectionwiseCotangentComplexConstant Λ structureMap)) ≅
      ((chartBaseLift Λ X structureMap).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SchemeOverRing.cotangentComplexConstant Λ structureMap) :=
  have : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat.{u, u, u + 1} _
  have : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat.{u, u, u + 1} _
  sheafificationLiftComplexIso.{u, u} X
      (SchemeOverRing.sectionwiseCotangentComplexConstant Λ structureMap) ≪≫
    ((chartBaseLift Λ X structureMap).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (SchemeOverRing.sheafifiedSectionwiseCotangentComplexConstantIso Λ structureMap)

/-- **The complex computing `Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X)` is the lift of `L_{𝒪_X/Λ̲}`.** By the
proof of Tag 08T9: on the chart `A_{n,U}` the presheaf `𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` is the degree
`-n` term `Ω_{P_{n,U}/Λ} ⊗_{P_{n,U}} 𝒪_X(U)` of `L_{𝒪_X(U)/Λ}`, and the sheafification of
`U ↦ L_{𝒪_X(U)/Λ}` is `L_{𝒪_X/Λ̲}` (Tag 08SX). -/
def chartModulePointSheafComplexCotangentIso :
    modulePointSheafComplex (chartBaseRing Λ X structureMap)
        (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
          (chartDifferentialsBaseChangeRestricted Λ X structureMap) ≅
      ((chartBaseLift Λ X structureMap).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SchemeOverRing.cotangentComplexConstant Λ structureMap) :=
  (chartModulePointSheafComplexIso Λ X structureMap).symm ≪≫
    (chartBaseSheafification Λ X structureMap).mapIso
      (chartBaseChangePresheafMooreCochainIso Λ X structureMap) ≪≫
    chartLiftedSectionwiseCotangentComplexIso Λ X structureMap

/-- **Stacks Project, Tag 08T9, the second isomorphism** `Lπ_!(Li^*Ω_{𝒪/Λ̲}) ≅ Lπ_!(i^*Ω_{𝒪/Λ̲})`:
`Lπ_!` applied to the canonical map `Li^*Ω_{𝒪/Λ̲} ⟶ i^*Ω_{𝒪/Λ̲}`, an isomorphism because
`Ω_{𝒪/Λ̲}` is a flat `𝒪`-module (`derivedHorizontalInverseImageDifferentialsIso`). -/
@[stacks 08T9 "second isomorphism Lπ_!(Li^*Ω_{𝒪/Λ̲}) = Lπ_!(i^*Ω_{𝒪/Λ̲}), induced by the canonical
map Li^*Ω ⟶ i^*Ω, an isomorphism since Ω_{𝒪/Λ̲} is flat"]
def derivedLowerShriekInverseImageDifferentialsIso :
    (chartDerivedLowerShriek Λ X structureMap).obj
        ((derivedHorizontalInverseImage Λ X structureMap).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (chartDifferentials.{u, u + 1} Λ X structureMap))) ≅
      (chartDerivedLowerShriek Λ X structureMap).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (pulledBackDifferentials.{u, u + 1} Λ X structureMap)) :=
  (chartDerivedLowerShriek Λ X structureMap).mapIso
    (derivedHorizontalInverseImageDifferentialsIso Λ X structureMap)

/-- **Stacks Project, Tag 08T9, the third isomorphism**
`Lπ_!(i^*Ω_{𝒪/Λ̲}) ≅ Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)`: `Lπ_!` applied to the canonical identification of
the pullback `i^*Ω_{𝒪/Λ̲}` with the extension of scalars of `Ω_{𝒪/Λ̲}` along `i♯`
(`pulledBackDifferentialsIsoBaseChange`). -/
@[stacks 08T9 "third isomorphism Lπ_!(i^*Ω_{𝒪/Λ̲}) = Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X), induced by the
canonical identification of i^* with extension of scalars along i♯"]
def derivedLowerShriekPulledBackDifferentialsIso :
    (chartDerivedLowerShriek Λ X structureMap).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (pulledBackDifferentials.{u, u + 1} Λ X structureMap)) ≅
      (chartDerivedLowerShriek Λ X structureMap).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (chartDifferentialsBaseChange Λ X structureMap)) :=
  (chartDerivedLowerShriek Λ X structureMap).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso
      (pulledBackDifferentialsIsoBaseChange Λ X structureMap))

/-- **Stacks Project, Tag 08T9, the first isomorphism** `L_{X/Λ} ≅ Lπ_!(Li^*Ω_{𝒪/Λ̲})` in `D(𝒪_X)`,
for the site of polynomial charts of Tag 08VA of a scheme `X` over a ring `Λ`. Here
`L_{X/Λ} = L_{X/Spec Λ}` is the cotangent complex of the structure morphism
(`SchemeOverRing.cotangentComplexRelative`, Tag 08UU), read in the coefficient universe of the
chart topos through `chartBaseLift`; `Ω_{𝒪/Λ̲}` is `chartDifferentials`; `Li^*` is
`derivedHorizontalInverseImage`; and `Lπ_!` is `chartDerivedLowerShriek`.

It is the composite of the canonical maps of the source's proof, read from right to left:
`Li^*Ω ⟶ i^*Ω` (an isomorphism because `Ω_{𝒪/Λ̲}` is flat), `i^*Ω ≅ Ω ⊗_𝒪 𝒪̲_X`, the
identification of `Lπ_!(Ω ⊗_𝒪 𝒪̲_X)` with the complex of the standard resolutions (Tag 08VB at
module coefficients), the identification of that complex with the sheafification of
`U ↦ L_{𝒪_X(U)/Λ}` and with `L_{𝒪_X/Λ̲}` (Tag 08SX), and the comparison map
`L_{𝒪_X/Λ̲} ⟶ L_{X/Spec Λ}`, a quasi-isomorphism by Tag 08V6. -/
@[stacks 08T9 "first isomorphism L_{X/Λ} = Lπ_!(Li^*Ω_{𝒪/Λ̲}) in D(𝒪_X), for the site of polynomial
charts of a scheme X over a ring Λ, with L_{X/Λ} the cotangent complex of X ⟶ Spec Λ and D(𝒪_X)
taken in the coefficient universe of the chart topos; built from the canonical maps of the proof:
flatness of Ω, Tag 08VB, Tag 08SX and the Tag 08V6 comparison"]
def cotangentComplexIsoDerivedLowerShriekInverseImage :
    DerivedCategory.Q.obj (((chartBaseLift Λ X structureMap).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (SchemeOverRing.cotangentComplexRelative Λ structureMap)) ≅
      (chartDerivedLowerShriek Λ X structureMap).obj
        ((derivedHorizontalInverseImage Λ X structureMap).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (chartDifferentials.{u, u + 1} Λ X structureMap))) :=
  have := quasiIso_chartBaseLift_constantComparison Λ X structureMap
  (asIso (DerivedCategory.Q.map (((chartBaseLift Λ X structureMap).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (SchemeOverRing.constantComparison Λ structureMap)))).symm ≪≫
    DerivedCategory.Q.mapIso (chartModulePointSheafComplexCotangentIso Λ X structureMap).symm ≪≫
    (chartDerivedLowerShriekBaseChangeIso Λ X structureMap).symm ≪≫
    (derivedLowerShriekPulledBackDifferentialsIso Λ X structureMap).symm ≪≫
    (derivedLowerShriekInverseImageDifferentialsIso Λ X structureMap).symm

/-- `L_{X/Λ}` is isomorphic to `Lπ_!(Li^*Ω_{𝒪/Λ̲})`, `Lπ_!(i^*Ω_{𝒪/Λ̲})` and
`Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)`: the isomorphisms `cotangentComplexIsoDerivedLowerShriekInverseImage`,
`derivedLowerShriekInverseImageDifferentialsIso` and `derivedLowerShriekPulledBackDifferentialsIso`
of Tag 08T9. -/
theorem nonempty_cotangentComplex_iso_derivedLowerShriek :
    Nonempty (DerivedCategory.Q.obj (((chartBaseLift Λ X structureMap).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (SchemeOverRing.cotangentComplexRelative Λ structureMap)) ≅
        (chartDerivedLowerShriek Λ X structureMap).obj
          ((derivedHorizontalInverseImage Λ X structureMap).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (chartDifferentials.{u, u + 1} Λ X structureMap)))) ∧
    Nonempty ((chartDerivedLowerShriek Λ X structureMap).obj
          ((derivedHorizontalInverseImage Λ X structureMap).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (chartDifferentials.{u, u + 1} Λ X structureMap))) ≅
        (chartDerivedLowerShriek Λ X structureMap).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (pulledBackDifferentials.{u, u + 1} Λ X structureMap))) ∧
    Nonempty ((chartDerivedLowerShriek Λ X structureMap).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (pulledBackDifferentials.{u, u + 1} Λ X structureMap)) ≅
        (chartDerivedLowerShriek Λ X structureMap).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (chartDifferentialsBaseChange Λ X structureMap))) :=
  ⟨⟨cotangentComplexIsoDerivedLowerShriekInverseImage Λ X structureMap⟩,
    ⟨derivedLowerShriekInverseImageDifferentialsIso Λ X structureMap⟩,
    ⟨derivedLowerShriekPulledBackDifferentialsIso Λ X structureMap⟩⟩

end AlgebraicGeometry.PolynomialChart
