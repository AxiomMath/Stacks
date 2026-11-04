module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCupSingleShift
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.TotalCupPairingLaws

/-!
# The class of a global section placed in degree `0`, through the unit complex

A global section `u` of a sheaf of modules `G` is a chain map `𝒪[0] ⟶ G[0]` out of the unit
complex (`unitComplexSectionMap`). The image under it of the class of `1` is the class of `u`
(`hgroupModuleShiftIso_sectionClass`), and the cup product with that image is right
multiplication by `u` (`canonicalPairingModule_unitComplexSectionMap`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace multiplicationInt)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}}

/-- **A global section as a chain map out of the unit complex**: the global section `u` of `G`,
as the morphism `𝒪 ⟶ G` it determines, placed in degree `0`, read into the extension by zero of
`G[0]`. -/
def unitComplexSectionMap
    (G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (u : G.val.sections) :
    Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR X ⟶
      (singleNat G 0).extend ComplexShape.embeddingUpNat :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (G.unitHomEquiv.symm u) ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl).inv

end Stacks.DeRham.GysinCupHodge
