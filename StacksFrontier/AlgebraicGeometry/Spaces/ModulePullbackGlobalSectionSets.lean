module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageUnitSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSectionUnitValue
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit

/-!
# The pullback of a global section, on underlying sheaves of sets

A global section `t : O_D ⟶ N` of a sheaf of modules is read on underlying sheaves of sets as
the unit section followed by `t`, a morphism `⊤ ⟶ N` from the terminal sheaf of sets. Along a
morphism of ringed topoi `f`, the pulled-back section `f^*t : O_C ≅ f^*O_D ⟶ f^*N`
(Stacks 03LU) is then the image `⊤ ≅ f⁻¹⊤ ⟶ f⁻¹N` of that global section of sets along the
inverse image of sheaves of sets (`CategoryTheory.Functor.globalSectionMap`), followed by the
unit `c : f⁻¹N ⟶ f^*N` of extension of scalars along `f♯` (Stacks 03CZ). For `N = O_D`, the
pulled-back section followed by `f^*O_D ≅ O_C` is the image of the global section followed by
`f♯ : f⁻¹O_D ⟶ O_C`.

## Main results

* `RingedToposModules.ringOneHom_comp_map_pullbackModulesObjUnitIso_hom_comp_map`
* `Space.ringOneHom_comp_map_modulePullbackGlobalSection`
* `RingedToposModules.ringOneHom_comp_map_pullbackModulesObjUnitIso_hom_comp_map_comp_inv`
* `Space.ringOneHom_comp_map_modulePullbackGlobalSection_comp_structureModulePullbackMap`

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

namespace Stacks.Sheaves.RingedToposModules

open Stacks.SheafOfModules.ChangeOfRings Stacks.Sheaves.FinitePresentation
  Stacks.Sheaves.ToposPushforward

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [HasWeakSheafify X.J AddCommGrpCat]
  [X.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Y.J AddCommGrpCat]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The unit section of `f⁻¹O_D` followed by `f♯ : f⁻¹O_D ⟶ O_C`, read as a morphism of
`f⁻¹O_D`-modules, is the unit section of `O_C`. -/
theorem ringOneHom_comp_map_unitToRestrictScalarsUnit :
    ringOneHom (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        (moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          (unitToRestrictScalarsUnit f.fSharpInverseImage) =
      ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  hom_ext_sections fun U _ ↦ unitToRestrictScalarsUnit_val_app_one f.fSharpInverseImage U

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The pullback of a global section, on underlying sheaves of sets** (Stacks 03CZ, 03LU): for
`t : O_D ⟶ N`, the unit section followed by `f^*t : O_C ≅ f^*O_D ⟶ f^*N` is the image along
`f⁻¹` of the global section `⊤ ⟶ O_D ⟶ N`, followed by the unit `c : f⁻¹N ⟶ f^*N` of extension
of scalars along `f♯`. -/
theorem ringOneHom_comp_map_pullbackModulesObjUnitIso_hom_comp_map
    {N : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (t : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶ N) :
    ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≫
        (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          ((pullbackModulesObjUnitIso f).hom ≫ f.pullbackModules.map t) =
      f.toToposHom.inverseImage.globalSectionMap
          (ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≫
            (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map t) ≫
        (moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((fSharpAdjunction f).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj N)) := by
  have hl := Stacks.Sheaves.ToposPullback.ringOneHom_comp_map_pullbackModuleUnitIso_hom_comp_map
    X.J f.toToposHom.inverseImage (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) t
  have h0 := inverseImageModulesUnitIso_hom_comp_map_comp_fSharpAdjunction_unit f t
  rw [← hl]
  refine hom_ext_sections fun U p ↦ ?_
  refine Eq.trans ?_ (congrArg (fun m ↦ m.val.app U (1 : (inverseImageRingSheaf f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj.obj U)) h0).symm
  exact (congrArg (fun x ↦ (((pullbackModulesObjUnitIso f).hom ≫ f.pullbackModules.map t).val.app
    U) x) (unitToRestrictScalarsUnit_val_app_one f.fSharpInverseImage U)).symm

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The pullback of an endomorphism of the structure sheaf, on underlying sheaves of sets**:
for `r : O_D ⟶ O_D`, the unit section followed by `O_C ≅ f^*O_D ⟶ f^*O_D ≅ O_C` is the image along
`f⁻¹` of the global section `⊤ ⟶ O_D ⟶ O_D`, followed by `f♯ : f⁻¹O_D ⟶ O_C`. -/
theorem ringOneHom_comp_map_pullbackModulesObjUnitIso_hom_comp_map_comp_inv
    (r : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≫
        (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          (((pullbackModulesObjUnitIso f).hom ≫ f.pullbackModules.map r) ≫
            (pullbackModulesObjUnitIso f).inv) =
      f.toToposHom.inverseImage.globalSectionMap
          (ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≫
            (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map r) ≫
        (sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage := by
  have hC := (congrArg (moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((fSharpAdjunction f).homEquiv_unit _ _ (pullbackModulesObjUnitIso f).inv)).symm.trans
      (moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv f)
  have hA : ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≫
        (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          (((pullbackModulesObjUnitIso f).hom ≫ f.pullbackModules.map r) ≫
            (pullbackModulesObjUnitIso f).inv) =
      (ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≫
        (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          ((pullbackModulesObjUnitIso f).hom ≫ f.pullbackModules.map r)) ≫
        (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          (pullbackModulesObjUnitIso f).inv :=
    (congrArg (ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≫ ·)
      ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map_comp _ _)).trans
      (Category.assoc _ _ _).symm
  rw [hA, ringOneHom_comp_map_pullbackModulesObjUnitIso_hom_comp_map f r]
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  exact hom_ext_sections fun U p ↦ sectionsFunctor_map_congr hC U p

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules Stacks.SheafOfModules.ChangeOfRings
  Stacks.Sheaves.FinitePresentation Stacks.Sheaves.ToposPushforward

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the small étale site is deep (see the docstring)
/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_ModulePullbackGlobalSectionSets
    (Z : AlgebraicSpaces B S hS) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((smallEtaleRingedTopos B S hS Z).Cᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the small étale site is deep (see the docstring)
/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high) hasTerminal_topos_ModulePullbackGlobalSectionSets
    (Z : AlgebraicSpaces B S hS) : HasTerminal (smallEtaleRingedTopos B S hS Z).Topos :=
  haveI : HasLimitsOfShape (Discrete PEmpty.{1})
      ((SmallEtale B S hS Z.1)ᵒᵖ ⥤ Type u) :=
    functorCategoryHasLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type u))

/-- **The pullback of a global section of an `𝒪_Y`-module, on underlying sheaves of sets**: for
`f : X ⟶ Y` and `t : 𝒪_Y ⟶ N`, the unit section followed by `f^*t`
(`AlgebraicGeometry.Space.modulePullbackGlobalSection`) is the image along `f⁻¹` of the global
section `⊤ ⟶ 𝒪_Y ⟶ N`, followed by the unit `c : f⁻¹N ⟶ f^*N` of extension of scalars along
`f♯`. -/
theorem ringOneHom_comp_map_modulePullbackGlobalSection (f : X ⟶ Y)
    {N : Modules.{u, u} B S hS Y.1 Y.2}
    (t : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ N) :
    ringOneHom (structureRingSheaf B S hS X) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (modulePullbackGlobalSection B S hS f t) =
      (smallEtaleRingedToposModulesHom B S hS f).toToposHom.inverseImage.globalSectionMap
          (ringOneHom (structureRingSheaf B S hS Y) ≫
            (moduleSheafFunctor (structureRingSheaf B S hS Y)).map t) ≫
        (moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposModulesHom B S hS f).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O))).map
          ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).obj
              N)) :=
  ringOneHom_comp_map_pullbackModulesObjUnitIso_hom_comp_map
    (smallEtaleRingedToposModulesHom B S hS f) t

/-- **The pullback of an endomorphism of the structure sheaf, on underlying sheaves of sets**:
for `g : X ⟶ Y` and `r : 𝒪_Y ⟶ 𝒪_Y`, the unit section followed by
`𝒪_X ≅ g^*𝒪_Y ⟶ g^*𝒪_Y ⟶ 𝒪_X` (the pulled-back section followed by
`AlgebraicGeometry.Space.structureModulePullbackMap`) is the image along `g⁻¹` of the global
section `⊤ ⟶ 𝒪_Y ⟶ 𝒪_Y`, followed by `g♯ : g⁻¹𝒪_Y ⟶ 𝒪_X`. -/
theorem ringOneHom_comp_map_modulePullbackGlobalSection_comp_structureModulePullbackMap
    (g : X ⟶ Y)
    (r : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS Y)) :
    ringOneHom (structureRingSheaf B S hS X) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (modulePullbackGlobalSection B S hS g r ≫ structureModulePullbackMap B S hS g) =
      (smallEtaleRingedToposModulesHom B S hS g).toToposHom.inverseImage.globalSectionMap
          (ringOneHom (structureRingSheaf B S hS Y) ≫
            (moduleSheafFunctor (structureRingSheaf B S hS Y)).map r) ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
          (smallEtaleRingedToposModulesHom B S hS g).fSharpInverseImage := by
  rw [structureModulePullbackMap_eq_modulePullbackUnitIso_hom]
  exact ringOneHom_comp_map_pullbackModulesObjUnitIso_hom_comp_map_comp_inv
    (smallEtaleRingedToposModulesHom B S hS g) r

end AlgebraicGeometry.Space

end
