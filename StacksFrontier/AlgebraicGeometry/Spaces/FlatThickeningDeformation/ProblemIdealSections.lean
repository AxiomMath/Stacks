module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSectionUnitValue
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalInverseImageGlobalSectionSets
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.IdealCompatibility

/-!
# Sections of the ideal of the extension problem of a flat deformation

Let `Z ⊂ Y'` be a first order thickening of algebraic spaces and `g : X ⟶ Z`. The extension
problem of [Stacks, Tag 0D17] attached to `g`
(`AlgebraicGeometry.Space.FlatThickeningDeformation.problem`) has ideal `g⁻¹𝒞_{Z/Y'}` and
prescribed map the unit `c : g⁻¹𝒞 ⟶ g^*𝒞` of extension of scalars.
A global section `t` of the conormal module `𝒞` gives the section `g⁻¹t` of the ideal
(`AlgebraicGeometry.Space.FlatThickeningDeformation.problemIdealSection`). This file computes it
on the two maps out of the ideal:

* the prescribed map carries `g⁻¹t` to the pulled-back section `g^*t`
  (`AlgebraicGeometry.Space.FlatThickeningDeformation.problem_c_problemIdealSection`);
* the inclusion into `g⁻¹(t⁻¹𝒪_{Y'})` carries it to the inverse image of the image of `t` in
  `t⁻¹𝒪_{Y'}`, on underlying sheaves of sets, and for `t` the class of a global section `s` of the
  ideal of `Z`, to the inverse image of `s` read as a function on `Y'`
  (`AlgebraicGeometry.Space.FlatThickeningDeformation.ringOneHom_comp_map_problemIdealSection_comp_map_inclSheafSets`).

These are the generators through which the prescribed maps of the problems at a chart are
compared along a morphism of thickenings in Remark 0D1P.

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules Stacks.SheafOfModules.ChangeOfRings
  Stacks.Sheaves.FinitePresentation Stacks.Sheaves.ToposPullback

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

/-- File-local shortcut: the inverse image of a morphism of topoi preserves finite products
(instance search through the generic paths times out). -/
local instance (priority := high) preservesFiniteProducts_inverseImage_problemIdealSections
    {E : Type*} [Category E] {F : Type*} [Category F] (f : MorphismOfTopoi E F) :
    PreservesFiniteProducts f.inverseImage :=
  haveI := f.preservesFiniteLimits
  inferInstance

/-- File-local shortcut: the inverse image of a morphism of topoi preserves the terminal
object (instance search through the generic paths times out). -/
local instance (priority := high) isIso_terminalComparison_inverseImage_problemIdealSections
    {E : Type*} [Category E] {F : Type*} [Category F] [HasTerminal E] [HasTerminal F]
    (f : MorphismOfTopoi E F) : IsIso (terminalComparison f.inverseImage) :=
  haveI := f.preservesFiniteLimits
  inferInstance

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}
  (g : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_ProblemIdealSections
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits indexed by `Type` of presheaves of sets on the small étale site (instance
search times out without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete₀_ProblemIdealSections
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type) :
    HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits of sheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasDiscreteLimits_topos_ProblemIdealSections
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type) :
    HasLimitsOfShape (Discrete J) (Sheaf (SmallEtale.topology B S hS F) (Type u)) :=
  letI : HasLimitsOfShape (Discrete J) (Type u) := inferInstance
  letI : HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
    hasLimitsOfShape_discrete₀_ProblemIdealSections F J
  letI : CreatesLimitsOfShape (Discrete J)
      (sheafToPresheaf (SmallEtale.topology B S hS F) (Type u)) :=
    Sheaf.createsLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS F) (Type u))

/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high) hasTerminal_topos_ProblemIdealSections
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasTerminal (Sheaf (SmallEtale.topology B S hS F) (Type u)) :=
  hasDiscreteLimits_topos_ProblemIdealSections F PEmpty

/-- **The section `g⁻¹t` of the ideal of the problem** attached to a global section `t` of the
conormal module: the inverse image of `t`, read through `g⁻¹𝒪_Z = g⁻¹(1) ⟶ g⁻¹𝒞`. -/
def problemIdealSection
    (t : SheafOfModules.unit (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ :
      AlgebraicSpaces B S hS)) ⟶ conormalModule B S hS Y' Z) :
    SheafOfModules.unit (pullbackRingSheaf (SmallEtale.topology B S hS X.1)
        (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)) ⟶
      (problem g hZ).I :=
  (pullbackModuleUnitIso (SmallEtale.topology B S hS X.1)
      (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)).hom ≫
    (pullbackModuleFunctor (SmallEtale.topology B S hS X.1)
      (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)).map t

/-- **The prescribed map on the section `g⁻¹t`**: it is the pulled-back section `g^*t`, on the unit
section over every object (Stacks 03CZ). -/
theorem problem_c_problemIdealSection
    (t : SheafOfModules.unit (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ :
      AlgebraicSpaces B S hS)) ⟶ conormalModule B S hS Y' Z)
    (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    (problem g hZ).c.val.app V ((problemIdealSection hZ g t).val.app V
        (1 : (pullbackRingSheaf (SmallEtale.topology B S hS X.1)
          (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)).obj.obj V)) =
      (modulePullbackGlobalSection B S hS g t).val.app V
        (1 : (structureRingSheaf B S hS X).obj.obj V) := by
  have h := congrArg (fun m => m.val.app V (1 : (pullbackRingSheaf (SmallEtale.topology B S hS X.1)
          (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)).obj.obj V))
    (inverseImageModulesUnitIso_hom_comp_map_comp_extendScalarsFSharpAdjunction_unit B S hS g t)
  refine h.trans ?_
  exact congrArg (fun y => (modulePullbackGlobalSection B S hS g t).val.app V y)
    (unitToRestrictScalarsUnit_val_app_one _ V)

/-- **The prescribed map of the problem on the section `g⁻¹t`**, as morphisms out of the free
module of rank one: `g⁻¹t` followed by `c` is the pulled-back section `g^*t`, read over
`g⁻¹𝒪_Z` (`AlgebraicGeometry.Space.FlatThickeningDeformation.problem_c_problemIdealSection` on
sections). -/
theorem problemIdealSection_comp_problem_c
    (t : SheafOfModules.unit (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ :
      AlgebraicSpaces B S hS)) ⟶ conormalModule B S hS Y' Z) :
    problemIdealSection hZ g t ≫ (problem g hZ).c =
      unitToRestrictScalarsUnit ((sheafCompose (smallEtaleRingedTopos B S hS X).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map (problem g hZ).f.fSharpInverseImage) ≫
        (SheafOfModules.restrictScalars ((sheafCompose (smallEtaleRingedTopos B S hS X).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map (problem g hZ).f.fSharpInverseImage)).map
          (modulePullbackGlobalSection B S hS g t) :=
  (Category.assoc _ _ _).trans
    (inverseImageModulesUnitIso_hom_comp_map_comp_extendScalarsFSharpAdjunction_unit B S hS g t)

/-- **The inclusion of the ideal on the section `g⁻¹t`**, on underlying sheaves of sets: the
inverse image along `g` of the image of `t` in `t⁻¹𝒪_{Y'}`. -/
theorem ringOneHom_comp_map_problemIdealSection_comp_map_inclSheafSets
    (t : SheafOfModules.unit (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ :
      AlgebraicSpaces B S hS)) ⟶ conormalModule B S hS Y' Z) :
    ringOneHom (pullbackRingSheaf (SmallEtale.topology B S hS X.1)
        (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)) ≫
      (moduleSheafFunctor (pullbackRingSheaf (SmallEtale.topology B S hS X.1)
        (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O))).map
        ((pullbackModuleUnitIso (SmallEtale.topology B S hS X.1)
          (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)).hom ≫
          (pullbackModuleFunctor (SmallEtale.topology B S hS X.1)
            (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedTopos B S hS
                (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)).map t) ≫
      (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map
        (baseExtension hZ).inclSheafSets =
    (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.globalSectionMap
      (ringOneHom (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map t ≫
        (baseExtension hZ).inclSheafSets) := by
  have h₁ := ringOneHom_comp_map_pullbackModuleUnitIso_hom_comp_map (SmallEtale.topology B S hS X.1)
    (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O) t
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h₁).trans ?_
  exact Functor.globalSectionMap_comp
    (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage _ _

end AlgebraicGeometry.Space.FlatThickeningDeformation
