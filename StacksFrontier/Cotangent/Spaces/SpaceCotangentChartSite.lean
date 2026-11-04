module

public import StacksFrontier.Cotangent.Spaces.ChartSiteDifferentialsPresheaf
public import StacksFrontier.Cotangent.Spaces.ChartSiteFlatDifferentials
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleLevelSheafification
public import StacksFrontier.Cotangent.Spaces.ChartSiteStandardResolutionEvaluation
public import StacksFrontier.Cotangent.Spaces.ConstantBaseRingPresheaf
public import StacksFrontier.Cotangent.Spaces.SpaceOverRingSectionwise
import StacksCore.Tactic.StacksAttribute

/-!
# The cotangent complex of an algebraic space over a ring as a derived lower shriek

Let `Λ` be a ring and `X` an algebraic space over `Λ`. Let `C_{X/Λ}` be the site of polynomial
charts of Section 08VJ: the diagrams `U ⟶ A` with `U` an object of `X_étale` and `A` an affine
space over `Spec Λ`, with the topology inherited from `X_étale`, its sheaves of rings
`𝒪 : (U ⟶ A) ↦ Γ(A, 𝒪_A)` and `𝒪̲_X = π⁻¹𝒪_X`, the projection `π : Sh(C_{X/Λ}) ⟶ Sh(X_étale)`
and the morphism of ringed topoi `i : (Sh(C_{X/Λ}), 𝒪̲_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` of Tag 08VK. This
file proves Tag 08VM:

`L_{X/Λ} = Lπ_!(Li^*Ω_{𝒪/Λ̲}) = Lπ_!(i^*Ω_{𝒪/Λ̲}) = Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)` in `D(𝒪_X)`.

The proof is the source's. `Ω_{𝒪/Λ̲}` is flat, so `Li^*Ω = i^*Ω`, and `i^*` is extension of
scalars along `i♯` (`StacksFrontier/Cotangent/Spaces/ChartSiteFlatDifferentials.lean`). By Tag 08VL
at module coefficients `Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)` is the sheafification of
`U ↦ (Ω ⊗ 𝒪̲_X)(𝐀_{•,U})` for the charts `𝐀_{n,U} = Spec(P_{n,U})` of the standard resolutions
of the `𝒪_X(U)` over `Λ`. That complex is the sheafification of
`U ↦ Ω_{P_{•,U}/Λ} ⊗_{P_{•,U}} 𝒪_X(U) = L_{𝒪_X(U)/Λ}`, which is `L_{𝒪_X/Λ̲}` by Tag 08SX, and
that is `L_{X/Λ} = L_{X/Spec Λ}` by Tag 08VG.

## Universes

A chart records a `Type u` of variables, so `C_{X/Λ}` has objects in `Type (u + 1)` and its
sheaves are formed in the coefficient universe `u + 1`. There `𝒪_X` is presented by the `ULift`
of its section rings, `AlgebraicGeometry.Space.smallEtaleStructureSheafULift`, which is the ring
sheaf of the cotangent complex of Tag 08VD; so `L_{X/Λ}` needs no further lift.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.chartDerivedLowerShriek`:
  `Lπ_! : D(π⁻¹𝒪_X) ⥤ D(𝒪_X)` on sheaves of modules.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.cotangentComplexIsoDerivedLowerShriekInverseImage`,
  `AlgebraicGeometry.Space.PolynomialChart.derivedLowerShriekInverseImageDifferentialsIso` and
  `AlgebraicGeometry.Space.PolynomialChart.derivedLowerShriekPulledBackDifferentialsIso`: the
  three isomorphisms of **Stacks 08VM**.

## References

* [Stacks Project, Tag 08VM](https://stacks.math.columbia.edu/tag/08VM)
* [Stacks Project, Tag 08VL](https://stacks.math.columbia.edu/tag/08VL)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08VG](https://stacks.math.columbia.edu/tag/08VG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sites.FibredCategory.FibredCategorySituation Stacks.Cohomology.DerivedLowerShriek

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

attribute [local instance] HasDerivedCategory.standard hasSheafify_addCommGrpCat_topology
  wEqualsLocallyBijective_topology

/-- `𝒪_X` presented in the coefficient universe of the chart topos, as a sheaf of rings on the
base site of the fibred category situation of Tag 08P8. -/
abbrev chartBaseRing : Sheaf (fibredCategorySituation Λ B hS X hX).base.J RingCat.{u + 1} :=
  ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)

/-- The equivalence between `π⁻¹𝒪_X`-modules in the two presentations of `π⁻¹𝒪_X` on the chart
site: restriction of scalars along `chartStructureRingIso`. -/
abbrev chartStructureModulesEquivalence :
    SheafOfModules.{u + 1} (ringSheaf (chartStructureSheaf Λ B hS X hX)) ≌
      SheafOfModules.{u + 1} (chartStructureRing Λ B hS X hX) :=
  Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (chartStructureRingIso Λ B hS X hX)

/-- The comparison of the two presentations of `π⁻¹𝒪_X`-modules is additive, being an
equivalence of preadditive categories. -/
instance additive_chartStructureModulesEquivalence_functor :
    (chartStructureModulesEquivalence Λ B hS X hX).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `Lπ_! : D(π⁻¹𝒪_X) ⥤ D(𝒪_X)` for the projection `π` of the site of polynomial charts to the
small étale site of `X`, on sheaves of modules over `π⁻¹𝒪_X`: the derived lower shriek of the
fibred category situation of Tag 08P8, with `𝒪_X` presented in the coefficient universe. -/
abbrev chartDerivedLowerShriek :
    DerivedCategory (SheafOfModules.{u + 1}
        (ringSheaf (chartStructureSheaf Λ B hS X hX))) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (chartBaseRing Λ B hS X hX)) :=
  (chartStructureModulesEquivalence Λ B hS X hX).functor.mapDerivedCategory ⋙
    (fibredCategorySituation Λ B hS X hX).derivedModuleLowerShriek
      (chartBaseRing Λ B hS X hX)

/-- Degreewise sheafification of complexes of presheaves of `𝒪_X`-modules, in the coefficient
universe of the chart topos. -/
abbrev chartBaseSheafification :
    CochainComplex (PresheafOfModules.{u + 1} (chartBaseRing Λ B hS X hX).obj) ℤ ⥤
      CochainComplex (SheafOfModules.{u + 1} (chartBaseRing Λ B hS X hX)) ℤ :=
  (PresheafOfModules.sheafification.{u + 1}
    (𝟙 (chartBaseRing Λ B hS X hX).obj)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The complex of presheaves `U ↦ G(𝐀_{•,U})` of the standard resolution charts. -/
abbrev chartPointMooreCochain :
    PresheafOfModules.{u + 1} (chartStructureRing Λ B hS X hX).obj ⥤
      CochainComplex (PresheafOfModules.{u + 1} (chartBaseRing Λ B hS X hX).obj) ℤ :=
  modulePointMooreCochain (fibredCategorySituation Λ B hS X hX)
    (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
    (chartBaseRing Λ B hS X hX).obj

/-- **`Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X)` is computed by the standard resolutions** (Tag 08VL at module
coefficients): it is the complex of sheaves whose term in degree `-n` is the sheafification of
`U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X)(𝐀_{n,U})`. The isomorphism is `derivedModuleLowerShriekIso`, after the
canonical identification of the two presentations of `π⁻¹𝒪_X`. -/
def chartDerivedLowerShriekBaseChangeIso :
    (chartDerivedLowerShriek Λ B hS X hX).obj
        ((DerivedCategory.singleFunctor _ 0).obj (chartDifferentialsBaseChange Λ B hS X hX)) ≅
      DerivedCategory.Q.obj (modulePointSheafComplex (chartBaseRing Λ B hS X hX)
        (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
          (chartDifferentialsBaseChangeRestricted Λ B hS X hX)) :=
  ((fibredCategorySituation Λ B hS X hX).derivedModuleLowerShriek
      (chartBaseRing Λ B hS X hX)).mapIso
        ((Functor.mapDerivedCategorySingleFunctor
          (chartStructureModulesEquivalence Λ B hS X hX).functor 0).app
            (chartDifferentialsBaseChange Λ B hS X hX)) ≪≫
    derivedModuleLowerShriekIso (chartBaseRing Λ B hS X hX)
      (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
      (exists_homotopyEquivalences_standardResolutionChart Λ B hS X hX)
      (chartDifferentialsBaseChangeRestricted Λ B hS X hX)

/-- The canonical map from `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` to the sections of
`Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`, read over `𝒪̲_X`. -/
def chartBaseChangePresheafToSections :
    chartBaseChangePresheaf Λ B hS X hX ⟶
      (chartDifferentialsBaseChangeRestricted Λ B hS X hX).val :=
  chartBaseChangePresheafMap Λ B hS X hX ≫
    (PresheafOfModules.isoMk (fun _ => ModuleCat.restrictScalarsId'App _ rfl _)
      (fun _ _ _ => rfl)).hom

/-- The canonical map is inverted by sheafification. -/
theorem W_chartBaseChangePresheafToSections :
    (topology Λ B hS X hX).W
      ((PresheafOfModules.toPresheaf _).map
        (chartBaseChangePresheafToSections Λ B hS X hX)) := by
  refine (congrArg (fun g => (topology Λ B hS X hX).W g)
    ((PresheafOfModules.toPresheaf _).map_comp _ _)).mpr ?_
  exact MorphismProperty.comp_mem _ _ _ (W_chartBaseChangePresheafMap Λ B hS X hX)
    (ObjectProperty.isLocal_of_isIso _ ((PresheafOfModules.toPresheaf _).mapIso
      (PresheafOfModules.isoMk (fun P => ModuleCat.restrictScalarsId'App _ rfl _)
        (fun _ _ _ => rfl))).hom)

/-- **The complex computing `Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X)` is the sheafification of
`U ↦ (𝒪_X(U) ⊗_{Γ(𝐀_{•,U})} Ω_{Γ(𝐀_{•,U})/Λ})`**, evaluated on the charts of the standard
resolutions before any sheafification on the chart site. -/
def chartModulePointSheafComplexIso :
    (chartBaseSheafification Λ B hS X hX).obj
        ((chartPointMooreCochain Λ B hS X hX).obj (chartBaseChangePresheaf Λ B hS X hX)) ≅
      modulePointSheafComplex (chartBaseRing Λ B hS X hX)
        (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
          (chartDifferentialsBaseChangeRestricted Λ B hS X hX) :=
  have := isIso_sheafification_map_modulePointMooreCochain_map
    (fibredCategorySituation Λ B hS X hX)
    (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
    (chartBaseRing Λ B hS X hX) (chartBaseChangePresheafToSections Λ B hS X hX)
    (W_chartBaseChangePresheafToSections Λ B hS X hX)
  asIso ((chartBaseSheafification Λ B hS X hX).map
    ((chartPointMooreCochain Λ B hS X hX).map
      (chartBaseChangePresheafToSections Λ B hS X hX)))

/-- **Stacks Project, Tag 08VM, the second isomorphism**
`Lπ_!(Li^*Ω_{𝒪/Λ̲}) ≅ Lπ_!(i^*Ω_{𝒪/Λ̲})`: `Lπ_!` applied to the canonical map
`Li^*Ω_{𝒪/Λ̲} ⟶ i^*Ω_{𝒪/Λ̲}`, an isomorphism because `Ω_{𝒪/Λ̲}` is a flat `𝒪`-module
(`derivedHorizontalInverseImageDifferentialsIso`). -/
@[stacks 08VM "second isomorphism Lπ_!(Li^*Ω_{𝒪/Λ̲}) = Lπ_!(i^*Ω_{𝒪/Λ̲}) for an algebraic space X
over Λ, induced by the canonical map Li^*Ω ⟶ i^*Ω, an isomorphism since Ω_{𝒪/Λ̲} is flat"]
def derivedLowerShriekInverseImageDifferentialsIso :
    (chartDerivedLowerShriek Λ B hS X hX).obj
        ((derivedHorizontalInverseImage Λ B hS X hX).obj
          ((DerivedCategory.singleFunctor _ 0).obj (chartDifferentials Λ B hS X hX))) ≅
      (chartDerivedLowerShriek Λ B hS X hX).obj
        ((DerivedCategory.singleFunctor _ 0).obj (pulledBackDifferentials Λ B hS X hX)) :=
  (chartDerivedLowerShriek Λ B hS X hX).mapIso
    (derivedHorizontalInverseImageDifferentialsIso Λ B hS X hX)

/-- **Stacks Project, Tag 08VM, the third isomorphism**
`Lπ_!(i^*Ω_{𝒪/Λ̲}) ≅ Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)`: `Lπ_!` applied to the canonical identification of
the pullback `i^*Ω_{𝒪/Λ̲}` with the extension of scalars of `Ω_{𝒪/Λ̲}` along `i♯`
(`pulledBackDifferentialsIsoBaseChange`). -/
@[stacks 08VM "third isomorphism Lπ_!(i^*Ω_{𝒪/Λ̲}) = Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X) for an algebraic
space X over Λ, induced by the canonical identification of i^* with extension of scalars along i♯"]
def derivedLowerShriekPulledBackDifferentialsIso :
    (chartDerivedLowerShriek Λ B hS X hX).obj
        ((DerivedCategory.singleFunctor _ 0).obj (pulledBackDifferentials Λ B hS X hX)) ≅
      (chartDerivedLowerShriek Λ B hS X hX).obj
        ((DerivedCategory.singleFunctor _ 0).obj (chartDifferentialsBaseChange Λ B hS X hX)) :=
  (chartDerivedLowerShriek Λ B hS X hX).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso
      (pulledBackDifferentialsIsoBaseChange Λ B hS X hX))

/-- The sheafification of `U ↦ L_{𝒪_X(U)/Λ}`, for the `Λ`-algebra structure given by `φ`, read as
a complex of sheaves of modules over the base ring of the fibred category situation. It is the
sheafification of the presheaf complex of Tag 08SX over the base `U ↦ Λ`, and is `L_{𝒪_X/Λ̲}` by
`sheafifiedSectionwiseCotangentComplexConstantIso`. -/
abbrev chartSheafifiedSectionwiseCotangentComplex
    (φ : (constantSheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
      CommRingCat.{u}).obj (CommRingCat.of Λ) ⟶
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O) :
    CochainComplex (SheafOfModules.{u + 1} (chartBaseRing Λ B hS X hX)) ℤ :=
  (chartBaseSheafification Λ B hS X hX).obj (sectionwiseCotangentComplexConstant φ)

/-- **The complex computing `Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X)` is the sheafification of
`U ↦ L_{𝒪_X(U)/Λ}`.** By the proof of Tag 08VM: on the chart `𝐀_{n,U}` the presheaf
`𝒪_X(U) ⊗_{Γ(𝐀)} Ω_{Γ(𝐀)/Λ}` is the degree `-n` term `Ω_{P_{n,U}/Λ} ⊗_{P_{n,U}} 𝒪_X(U)` of
`L_{𝒪_X(U)/Λ}`, for any structure map `φ : Λ̲ ⟶ 𝒪_X` restricting on sections to the structure
maps `Λ → Γ(U, 𝒪_U)` of the étale charts. -/
def chartModulePointSheafComplexSectionwiseIso
    (φ : (constantSheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
      CommRingCat.{u}).obj (CommRingCat.of Λ) ⟶
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O)
    (hφ : toSheafify (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
        ((Functor.const _).obj (CommRingCat.of Λ)) ≫ φ.hom =
      etaleConstantStructurePresheafMap Λ B hS X) :
    modulePointSheafComplex (chartBaseRing Λ B hS X hX)
        (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
          (chartDifferentialsBaseChangeRestricted Λ B hS X hX) ≅
      chartSheafifiedSectionwiseCotangentComplex Λ B hS X hX φ :=
  (chartModulePointSheafComplexIso Λ B hS X hX).symm ≪≫
    (chartBaseSheafification Λ B hS X hX).mapIso
      (chartBaseChangePresheafMooreCochainIsoConstant φ hφ)

/-- **Stacks Project, Tag 08VM, the first isomorphism** `L_{X/Λ} ≅ Lπ_!(Li^*Ω_{𝒪/Λ̲})` in `D(𝒪_X)`,
for the site of polynomial charts of Section 08VJ of an algebraic space `X` over a ring `Λ`. Here
`L_{X/Λ} = L_{X/Spec Λ}` is the cotangent complex of the structure morphism
(`AlgebraicGeometry.Space.cotangentComplexDerived`, Tag 08VD); `Ω_{𝒪/Λ̲}` is `chartDifferentials`;
`Li^*` is `derivedHorizontalInverseImage`; and `Lπ_!` is `chartDerivedLowerShriek`.

It is the composite of the canonical maps of the source's proof, read from right to left:
`Li^*Ω ⟶ i^*Ω` (an isomorphism because `Ω_{𝒪/Λ̲}` is flat), `i^*Ω ≅ Ω ⊗_𝒪 𝒪̲_X`, the
identification of `Lπ_!(Ω ⊗_𝒪 𝒪̲_X)` with the complex of the standard resolutions (Tag 08VL at
module coefficients), the identification of that complex with the sheafification of
`U ↦ L_{𝒪_X(U)/Λ}` and with `L_{𝒪_X/Λ̲}` (Tag 08SX), and the isomorphism
`L_{𝒪_X/Λ̲} ≅ L_{X/Spec Λ}` of Tag 08VG for the canonical map `Λ̲ ⟶ 𝒪_X`, which restricts on
sections to the structure maps of the étale charts (`toSheafify_comp_constantStructureMapOfSpace`).
-/
@[stacks 08VM "first isomorphism L_{X/Λ} = Lπ_!(Li^*Ω_{𝒪/Λ̲}) in D(𝒪_X), for the site of polynomial
charts of an algebraic space X over a ring Λ, with L_{X/Λ} the cotangent complex of X ⟶ Spec Λ
(Tag 08VD, sections lifted to the universe of the site); built from the canonical maps of the
proof: flatness of Ω, Tag 08VL, Tag 08SX and Tag 08VG"]
def cotangentComplexIsoDerivedLowerShriekInverseImage :
    cotangentComplexDerived B (Spec (CommRingCat.of Λ)) hS (structureToSpec Λ B hS ⟨X, hX⟩) ≅
      (chartDerivedLowerShriek Λ B hS X hX).obj
        ((derivedHorizontalInverseImage Λ B hS X hX).obj
          ((DerivedCategory.singleFunctor _ 0).obj (chartDifferentials Λ B hS X hX))) :=
  (cotangentComplexOverConstantSheafIso Λ B hS ⟨X, hX⟩).symm ≪≫
    DerivedCategory.Q.mapIso (sheafifiedSectionwiseCotangentComplexConstantIso
      (constantStructureMapOfSpace Λ B hS ⟨X, hX⟩)).symm ≪≫
    DerivedCategory.Q.mapIso (chartModulePointSheafComplexSectionwiseIso Λ B hS X hX
      (constantStructureMapOfSpace Λ B hS ⟨X, hX⟩)
      (toSheafify_comp_constantStructureMapOfSpace Λ B hS ⟨X, hX⟩)).symm ≪≫
    (chartDerivedLowerShriekBaseChangeIso Λ B hS X hX).symm ≪≫
    (derivedLowerShriekPulledBackDifferentialsIso Λ B hS X hX).symm ≪≫
    (derivedLowerShriekInverseImageDifferentialsIso Λ B hS X hX).symm

end AlgebraicGeometry.Space.PolynomialChart

end
