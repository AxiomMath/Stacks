module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedConormalGlobalSectionSets
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleRangeSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealBaseRingTensor

/-!
# The class of a pulled-back function in the conormal module of a preimage, on sheaves of sets

Let `g : W ⟶ T` be a morphism to a scheme, `Z ⊆ T` a closed subspace and `a` a function on `T`
vanishing on `Z`, so that `g^♯a` is a global section of the ideal of `g⁻¹(Z) ⊆ W`. When
`g⁻¹(Z) ⊆ W` is a first order thickening, the class of `g^♯a` in the conormal module, included
into `i⁻¹𝒪_W` by the extension of the thickening, is the inverse image along `i` of the global
function `g^♯a`, on underlying sheaves of sets.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `ringOneHom_comp_map_modulePullbackGlobalSection_comp_inclSheafSets_of_comp_ι`: the class of a
  global section of the ideal of a first order thickening, on sheaves of sets, is the inverse
  image of the function it multiplies by.
* `ringOneHom_comp_map_modulePullbackGlobalSection_preimageIdealSection_comp_inclSheafSets`:
  the class of `g^♯a` in the conormal module of `g⁻¹(Z) ⊆ W` is the inverse image of `g^♯a`.
* `ringOneHom_comp_map_rangeConormalSection_comp_inclSheafSets`: the class of a function
  vanishing on `T` in the conormal module of a first order thickening `T ⊆ T'` is its inverse
  image.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits of presheaves on the small étale site times out
/-- Discrete limits indexed by `Type` of presheaves of sets on the small étale site (instance
search times out without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete₀_PreimageIdealGlobalSectionSets
    (Z : AlgebraicSpaces B S hS) (J : Type) :
    HasLimitsOfShape (Discrete J) ((smallEtaleRingedTopos B S hS Z).Cᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits of presheaves on the small étale site times out
/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_PreimageIdealGlobalSectionSets
    (Z : AlgebraicSpaces B S hS) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((smallEtaleRingedTopos B S hS Z).Cᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits of presheaves on the small étale site times out
/-- Discrete limits indexed by `Type` of presheaves of sets on the small étale site of a sheaf
(instance search times out without this shortcut). -/
local instance (priority := high)
    hasLimitsOfShape_discrete₀_smallEtale_PreimageIdealGlobalSectionSets
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type) :
    HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits of presheaves on the small étale site times out
/-- Discrete limits of presheaves of sets on the small étale site of a sheaf (instance search
times out without this shortcut). -/
local instance (priority := high)
    hasLimitsOfShape_discrete_smallEtale_PreimageIdealGlobalSectionSets
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the terminal sheaf on the small étale site times out
/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high) hasTerminal_topos_PreimageIdealGlobalSectionSets
    (Z : AlgebraicSpaces B S hS) : HasTerminal (smallEtaleRingedTopos B S hS Z).Topos :=
  haveI : HasLimitsOfShape (Discrete PEmpty.{1})
      ((SmallEtale B S hS Z.1)ᵒᵖ ⥤ Type u) :=
    functorCategoryHasLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type u))

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the terminal sheaf on the small étale site times out
/-- The terminal sheaf of sets on the small étale site of a sheaf (instance search times out
without this shortcut). -/
local instance (priority := high) hasTerminal_sheaf_smallEtale_PreimageIdealGlobalSectionSets
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasTerminal (Sheaf (SmallEtale.topology B S hS F) (Type u)) :=
  haveI : HasLimitsOfShape (Discrete PEmpty.{1})
      ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
    functorCategoryHasLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS F) (Type u))

/-- **The class of a global section of the ideal in the conormal module, on sheaves of sets**:
for a first order thickening `i : Z ⟶ X` and a global section `s` of its ideal whose image in
`𝒪_X` is multiplication by `r`, the unit section followed by `i^*s` and the inclusion of the
ideal of the extension into `i⁻¹𝒪_X` is the image along `i⁻¹` of the global section `r` of
`𝒪_X`. -/
theorem ringOneHom_comp_map_modulePullbackGlobalSection_comp_inclSheafSets_of_comp_ι
    {X Y : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsFirstOrderThickening B S hS X Z.1) (h : X ⟶ Y)
    (s : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      (definingIdealSheaf B S hS X Z).toSheafOfModules)
    {r : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X)}
    (hs : s ≫ (definingIdealSheaf B S hS X Z).ι = r) :
    ringOneHom (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map
          (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS X Z) s :
            SheafOfModules.unit _ ⟶ conormalModule B S hS X Z) ≫
        (firstOrderAlgebraExtension B S hS Z hZ h).inclSheafSets =
      (thickeningToposHom B S hS Z).inverseImage.globalSectionMap
        (ringOneHom (structureRingSheaf B S hS X) ≫
          (moduleSheafFunctor (structureRingSheaf B S hS X)).map r) :=
  (ringOneHom_comp_map_comp_firstOrderAlgebraExtension_inclSheafSets B S hS Z hZ h _).trans
    ((ringOneHom_comp_map_conormalInverseImageι_modulePullbackGlobalSection B S hS Z hZ s).trans
      (congrArg (fun m : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
          SheafOfModules.unit (structureRingSheaf B S hS X) =>
        (thickeningToposHom B S hS Z).inverseImage.globalSectionMap
          (ringOneHom (structureRingSheaf B S hS X) ≫
            (moduleSheafFunctor (structureRingSheaf B S hS X)).map m)) hs))

variable {W Y : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS} (g : W ⟶ schemeSpace T)
  (Z : ClosedSubspaces B S hS (schemeSpace T).1)

/-- **The class of a pulled-back function in the conormal module of a preimage, on sheaves of
sets**: for a first order thickening `i : g⁻¹(Z) ⟶ W` and a function `a` on `T` vanishing on `Z`,
the unit section followed by the class `i^*(g^♯a)` in `𝒞_{g⁻¹(Z)/W}` and the inclusion of the
ideal of the extension into `i⁻¹𝒪_W` is the image along `i⁻¹` of the global function `g^♯a`. -/
theorem ringOneHom_comp_map_modulePullbackGlobalSection_preimageIdealSection_comp_inclSheafSets
    (hZ : IsFirstOrderThickening B S hS W (preimageSubspace B S hS g Z).1) (h : W ⟶ Y)
    (a : closedSubspaceBaseIdeal B S hS Z) :
    ringOneHom (structureRingSheaf B S hS (⟨(preimageSubspace B S hS g Z).1.toFunctor,
        (preimageSubspace B S hS g Z).2.1⟩ : AlgebraicSpaces B S hS)) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS (⟨(preimageSubspace B S hS g Z).1.toFunctor,
          (preimageSubspace B S hS g Z).2.1⟩ : AlgebraicSpaces B S hS))).map
          (modulePullbackGlobalSection B S hS
            (subspaceInclusion B S hS W (preimageSubspace B S hS g Z))
            (preimageIdealSection B S hS g Z a) :
            SheafOfModules.unit _ ⟶ conormalModule B S hS W (preimageSubspace B S hS g Z)) ≫
        (firstOrderAlgebraExtension B S hS (preimageSubspace B S hS g Z) hZ h).inclSheafSets =
      (thickeningToposHom B S hS (preimageSubspace B S hS g Z)).inverseImage.globalSectionMap
        (ringOneHom (structureRingSheaf B S hS W) ≫
          (moduleSheafFunctor (structureRingSheaf B S hS W)).map
            (unitModuleMul B S hS W (globalFunctionsOfMap g a.1))) :=
  ringOneHom_comp_map_modulePullbackGlobalSection_comp_inclSheafSets_of_comp_ι B S hS
    (preimageSubspace B S hS g Z) hZ h (preimageIdealSection B S hS g Z a)
    (preimageIdealSection_ι B S hS g Z a)

/-- The ideal sheaves of equal closed subspaces have the same inclusion into `𝒪_X`. -/
theorem eqToHom_comp_definingIdealSheaf_ι {X : AlgebraicSpaces B S hS}
    {Z₁ Z₂ : ClosedSubspaces B S hS X.1} (hZ : Z₁ = Z₂) :
    eqToHom (congrArg (fun Z => (definingIdealSheaf B S hS X Z).toSheafOfModules) hZ) ≫
        (definingIdealSheaf B S hS X Z₂).ι = (definingIdealSheaf B S hS X Z₁).ι := by
  subst hZ
  exact Category.id_comp _

variable {T' : BigFppfOver B S hS} (j : T ⟶ T')
  (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))

/-- The global section `c` of the ideal of `T ⊆ T'`, followed by the inclusion into `𝒪_{T'}`, is
multiplication by `c`. -/
theorem rangeIdealSection_comp_ι (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    rangeIdealSection B S hS j hj c ≫
        (definingIdealSheaf B S hS (schemeSpace T') (rangeSubspace B S hS j hj)).ι =
      unitModuleMul B S hS (schemeSpace T') (globalFunctionsOfMap (𝟙 (schemeSpace T')) c.1) :=
  (Category.assoc _ _ _).trans ((congrArg (preimageIdealSection B S hS (𝟙 (schemeSpace T'))
      (rangeSubspace B S hS j hj) c ≫ ·)
    (eqToHom_comp_definingIdealSheaf_ι B S hS (preimageSubspace_id B S hS
      (rangeSubspace B S hS j hj)))).trans
    (preimageIdealSection_ι B S hS (𝟙 (schemeSpace T')) (rangeSubspace B S hS j hj) c))

/-- **The class of a function vanishing on `T` in the conormal module of `T ⊆ T'`, on sheaves of
sets**: when `T ⊆ T'` is a first order thickening, the unit section followed by the class of `c`
(`AlgebraicGeometry.Space.rangeConormalSection`) and the inclusion of the ideal of the extension
into `i⁻¹𝒪_{T'}` is the image along `i⁻¹` of the
global function `c`. -/
theorem ringOneHom_comp_map_rangeConormalSection_comp_inclSheafSets
    (hZ : IsFirstOrderThickening B S hS (schemeSpace T') (rangeSubspace B S hS j hj).1)
    (h : schemeSpace T' ⟶ Y) (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    ringOneHom (structureRingSheaf B S hS (⟨(rangeSubspace B S hS j hj).1.toFunctor,
        (rangeSubspace B S hS j hj).2.1⟩ : AlgebraicSpaces B S hS)) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS (⟨(rangeSubspace B S hS j hj).1.toFunctor,
          (rangeSubspace B S hS j hj).2.1⟩ : AlgebraicSpaces B S hS))).map
          (modulePullbackGlobalSection B S hS
            (subspaceInclusion B S hS (schemeSpace T') (rangeSubspace B S hS j hj))
            (rangeIdealSection B S hS j hj c) :
            SheafOfModules.unit _ ⟶
              conormalModule B S hS (schemeSpace T') (rangeSubspace B S hS j hj)) ≫
        (firstOrderAlgebraExtension B S hS (rangeSubspace B S hS j hj) hZ h).inclSheafSets =
      (thickeningToposHom B S hS (rangeSubspace B S hS j hj)).inverseImage.globalSectionMap
        (ringOneHom (structureRingSheaf B S hS (schemeSpace T')) ≫
          (moduleSheafFunctor (structureRingSheaf B S hS (schemeSpace T'))).map
            (unitModuleMul B S hS (schemeSpace T')
              (globalFunctionsOfMap (𝟙 (schemeSpace T')) c.1))) :=
  ringOneHom_comp_map_modulePullbackGlobalSection_comp_inclSheafSets_of_comp_ι B S hS
    (rangeSubspace B S hS j hj) hZ h (rangeIdealSection B S hS j hj c)
    (rangeIdealSection_comp_ι B S hS j hj c)

end AlgebraicGeometry.Space

end
