module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationTensorExtensionGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.PreimageIdealGlobalSectionSets
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedFirstOrderExtension

/-!
# Classes of functions in the restricted extension of a first order thickening, on sheaves of sets

Let `i : Z ⟶ X` be a first order thickening, `ρ : U ≅ Z` an isomorphism and `s` a global section
of the ideal of `Z` whose image in `𝒪_X` is multiplication by `r`. In the extension
`0 → 𝒞_{Z/X} → ι⁻¹𝒪_X → 𝒪_Z → 0` restricted to `U` along `ρ`
(`AlgebraicGeometry.Space.restrictedFirstOrderExtension`), the class of `s` restricted to `U` is
included into the middle term as the restriction along `ρ` of the inverse image of the global
function `r`, on underlying sheaves of sets.

## Main results

* `ringOneHom_comp_map_comp_restrictedFirstOrderExtension_inclSheafSets`: the class of a global
  section `s` of the ideal, restricted to `U` and included into the middle term, is the
  restriction along `ρ` of the inverse image of `r`.
* `ringOneHom_comp_map_comp_castBase_restrictedFirstOrderExtension_inclSheafSets`: the same, for
  the extension over a base map changed along an equality.
* `ringOneHom_comp_map_rangeConormalSection_comp_restrictedFirstOrderExtension_inclSheafSets`:
  the same, for the class of a function on `T'` vanishing on a closed subscheme `T`.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y U : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (hZ : IsFirstOrderThickening B S hS X Z.1)
  (ρ : U ≅ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) (h : X ⟶ Y)

/-- The postcomposition functor along `ρ` between small étale sites is continuous. -/
local instance instIsContinuousSmallEtalePostcompRestrictedFirstOrderExtensionSectionSets :
    (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS _)).IsContinuous
    (SmallEtale.topology B S hS U.1)
    (SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) :=
  smallEtalePostcomp_isContinuous B S hS _ _

/-- **The class of a global section of the ideal in the restricted extension, sectionwise**: for
a first order thickening `i : Z ⟶ X`, `ρ : U ≅ Z` and a global section `s` of the ideal of `Z`
whose image in `𝒪_X` is multiplication by `r`, the inclusion into the middle term of the value
at `1` of the class `ρ^*i^*s` is, over every object, the restriction along `ρ` of the inverse
image along `i` of the global section `r`. -/
theorem restrictedFirstOrderExtension_incl_modulePullbackGlobalSection
    (s : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      (definingIdealSheaf B S hS X Z).toSheafOfModules)
    {r : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X)}
    (hs : s ≫ (definingIdealSheaf B S hS X Z).ι = r)
    (V : (SmallEtale B S hS U.1)ᵒᵖ)
    (p : (sectionsFunctor _ V).obj (⊤_ Sheaf (SmallEtale.topology B S hS U.1) (Type u))) :
    (restrictedFirstOrderExtension B S hS Z hZ ρ h).incl
        ((modulePullbackGlobalSection B S hS ρ.hom
            (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS X Z) s :
              SheafOfModules.unit _ ⟶ conormalModule B S hS X Z) ≫
          ((modulePullbackIsoEtaleRestrictionModule B S hS ρ.hom
            (isEtale_hom_of_iso B S hS _)).app (conormalModule B S hS X Z)).hom).val.app V
          (1 : (structureRingSheaf B S hS U).obj.obj V)) =
      (sectionsFunctor _ V).map
        ((smallEtaleSetRestriction B S hS ρ.hom (isEtale_hom_of_iso B S hS _)).globalSectionMap
          ((thickeningToposHom B S hS Z).inverseImage.globalSectionMap
            (ringOneHom (structureRingSheaf B S hS X) ≫
              (moduleSheafFunctor (structureRingSheaf B S hS X)).map r))) p := by
  refine Eq.trans ?_ (sectionsFunctor_map_globalSectionMap_smallEtaleSetRestriction B S hS
    ρ.hom (isEtale_hom_of_iso B S hS _) ((thickeningToposHom B S hS Z).inverseImage.globalSectionMap
      (ringOneHom (structureRingSheaf B S hS X) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS X)).map r)) V p).symm
  refine Eq.trans ?_
    (Deformation.AlgebraExtension.incl_eq_of_ringOneHom_comp_map_comp_inclSheafSets_eq
      (firstOrderAlgebraExtension B S hS Z hZ h) _ _
      (ringOneHom_comp_map_modulePullbackGlobalSection_comp_inclSheafSets_of_comp_ι B S hS Z hZ h
        s hs) _ _)
  refine (etaleRestrictionFunctor_obj_incl B S hS ρ.hom (isEtale_hom_of_iso B S hS _) _
    (firstOrderAlgebraExtension B S hS Z hZ h) _).trans ?_
  exact congrArg (firstOrderAlgebraExtension B S hS Z hZ h).incl
    (modulePullbackGlobalSection_comp_modulePullbackIsoEtaleRestrictionModule_hom_val_app_one B S hS
      ρ.hom (isEtale_hom_of_iso B S hS _) _ V)

/-- **The class of a global section of the ideal in the restricted extension, on sheaves of
sets**: for a first order thickening `i : Z ⟶ X`, `ρ : U ≅ Z` and a global section `s` of the
ideal of `Z` whose image in `𝒪_X` is multiplication by `r`, the unit section followed by the class
`ρ^*i^*s` and the inclusion of the ideal into the middle term `(ι⁻¹𝒪_X)|_U` is the restriction
along `ρ` of the inverse image along `i` of the global section `r`. -/
theorem ringOneHom_comp_map_comp_restrictedFirstOrderExtension_inclSheafSets
    (s : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      (definingIdealSheaf B S hS X Z).toSheafOfModules)
    {r : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X)}
    (hs : s ≫ (definingIdealSheaf B S hS X Z).ι = r) :
    ringOneHom (structureRingSheaf B S hS U) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS U)).map
          (modulePullbackGlobalSection B S hS ρ.hom
            (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS X Z) s :
              SheafOfModules.unit _ ⟶ conormalModule B S hS X Z) ≫
          ((modulePullbackIsoEtaleRestrictionModule B S hS ρ.hom
            (isEtale_hom_of_iso B S hS _)).app (conormalModule B S hS X Z)).hom) ≫
        (restrictedFirstOrderExtension B S hS Z hZ ρ h).inclSheafSets =
      (smallEtaleSetRestriction B S hS ρ.hom (isEtale_hom_of_iso B S hS _)).globalSectionMap
        ((thickeningToposHom B S hS Z).inverseImage.globalSectionMap
          (ringOneHom (structureRingSheaf B S hS X) ≫
            (moduleSheafFunctor (structureRingSheaf B S hS X)).map r)) :=
  Deformation.AlgebraExtension.ringOneHom_comp_map_comp_inclSheafSets_eq_of_forall
    (restrictedFirstOrderExtension B S hS Z hZ ρ h) _ _
    (restrictedFirstOrderExtension_incl_modulePullbackGlobalSection B S hS Z hZ ρ h s hs)

/-- `AlgebraicGeometry.Space.ringOneHom_comp_map_comp_restrictedFirstOrderExtension_inclSheafSets`
for the extension over a base map changed along an equality `ρ ≫ ι ≫ h = f'`. -/
theorem ringOneHom_comp_map_comp_castBase_restrictedFirstOrderExtension_inclSheafSets
    {f' : U ⟶ Y} (hf : ρ.hom ≫ subspaceInclusion B S hS X Z ≫ h = f')
    (s : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      (definingIdealSheaf B S hS X Z).toSheafOfModules)
    {r : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X)}
    (hs : s ≫ (definingIdealSheaf B S hS X Z).ι = r) :
    ringOneHom (structureRingSheaf B S hS U) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS U)).map
          (modulePullbackGlobalSection B S hS ρ.hom
            (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS X Z) s :
              SheafOfModules.unit _ ⟶ conormalModule B S hS X Z) ≫
          ((modulePullbackIsoEtaleRestrictionModule B S hS ρ.hom
            (isEtale_hom_of_iso B S hS _)).app (conormalModule B S hS X Z)).hom) ≫
        (castBase B S hS hf (restrictedFirstOrderExtension B S hS Z hZ ρ h)).inclSheafSets =
      (smallEtaleSetRestriction B S hS ρ.hom (isEtale_hom_of_iso B S hS _)).globalSectionMap
        ((thickeningToposHom B S hS Z).inverseImage.globalSectionMap
          (ringOneHom (structureRingSheaf B S hS X) ≫
            (moduleSheafFunctor (structureRingSheaf B S hS X)).map r)) := by
  subst hf
  exact ringOneHom_comp_map_comp_restrictedFirstOrderExtension_inclSheafSets B S hS Z hZ ρ h s hs

section Range

variable {T T' : BigFppfOver B S hS} (j : T ⟶ T')
  (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))
  (hZr : IsFirstOrderThickening B S hS (schemeSpace T') (rangeSubspace B S hS j hj).1)
  (ρr : U ≅ (⟨(rangeSubspace B S hS j hj).1.toFunctor, (rangeSubspace B S hS j hj).2.1⟩ :
    AlgebraicSpaces B S hS)) (hr : schemeSpace T' ⟶ Y)

/-- The class of `c` restricted to `U ≅ (T ⊆ T')` is the restriction of the pullback of the
section `c` of the ideal of `T ⊆ T'`, `AlgebraicGeometry.Space.rangeConormalSection` unfolded. -/
theorem
  modulePullbackGlobalSection_rangeConormalSection_comp_modulePullbackIsoEtaleRestrictionModule_hom
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    modulePullbackGlobalSection B S hS ρr.hom (rangeConormalSection B S hS j hj c) ≫
        ((modulePullbackIsoEtaleRestrictionModule B S hS ρr.hom
          (isEtale_hom_of_iso B S hS _)).app (rangeConormalModule B S hS j hj)).hom =
      modulePullbackGlobalSection B S hS ρr.hom
          (modulePullbackGlobalSection B S hS
            (subspaceInclusion B S hS (schemeSpace T') (rangeSubspace B S hS j hj))
            (rangeIdealSection B S hS j hj c) :
              SheafOfModules.unit _ ⟶
                conormalModule B S hS (schemeSpace T') (rangeSubspace B S hS j hj)) ≫
        ((modulePullbackIsoEtaleRestrictionModule B S hS ρr.hom
          (isEtale_hom_of_iso B S hS _)).app
            (conormalModule B S hS (schemeSpace T') (rangeSubspace B S hS j hj))).hom := by
  have h1 : modulePullbackGlobalSection B S hS ρr.hom (rangeConormalSection B S hS j hj c) ≫
        ((modulePullbackIsoEtaleRestrictionModule B S hS ρr.hom
          (isEtale_hom_of_iso B S hS _)).app (rangeConormalModule B S hS j hj)).hom =
      modulePullbackGlobalSection B S hS ρr.hom
          (rangeConormalSection B S hS j hj c :
            SheafOfModules.unit _ ⟶
              conormalModule B S hS (schemeSpace T') (rangeSubspace B S hS j hj)) ≫
        ((modulePullbackIsoEtaleRestrictionModule B S hS ρr.hom
          (isEtale_hom_of_iso B S hS _)).app
            (conormalModule B S hS (schemeSpace T') (rangeSubspace B S hS j hj))).hom := rfl
  have h2 : (rangeConormalSection B S hS j hj c :
        SheafOfModules.unit _ ⟶
          conormalModule B S hS (schemeSpace T') (rangeSubspace B S hS j hj)) =
      modulePullbackGlobalSection B S hS
        (subspaceInclusion B S hS (schemeSpace T') (rangeSubspace B S hS j hj))
        (rangeIdealSection B S hS j hj c) := rfl
  exact h1.trans (congrArg (fun s : SheafOfModules.unit (structureRingSheaf B S hS
      (⟨(rangeSubspace B S hS j hj).1.toFunctor, (rangeSubspace B S hS j hj).2.1⟩ :
        AlgebraicSpaces B S hS)) ⟶
        conormalModule B S hS (schemeSpace T') (rangeSubspace B S hS j hj) =>
    modulePullbackGlobalSection B S hS ρr.hom s ≫
      ((modulePullbackIsoEtaleRestrictionModule B S hS ρr.hom
        (isEtale_hom_of_iso B S hS _)).app
          (conormalModule B S hS (schemeSpace T') (rangeSubspace B S hS j hj))).hom) h2)

/-- **The class of a function vanishing on `T` in the restricted extension of `T ⊆ T'`, on
sheaves of sets**: for a function `c` on `T'` vanishing on `T` and `ρ : U ≅ (T ⊆ T')`, the unit
section followed by the class of `c` (`AlgebraicGeometry.Space.rangeConormalSection`) restricted
to `U` and the inclusion of the ideal into the middle term `(ι⁻¹𝒪_{T'})|_U` is the restriction
along `ρ` of the inverse image of the global function `c`. -/
theorem ringOneHom_comp_map_rangeConormalSection_comp_restrictedFirstOrderExtension_inclSheafSets
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    ringOneHom (structureRingSheaf B S hS U) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS U)).map
          (modulePullbackGlobalSection B S hS ρr.hom (rangeConormalSection B S hS j hj c) ≫
            ((modulePullbackIsoEtaleRestrictionModule B S hS ρr.hom
              (isEtale_hom_of_iso B S hS _)).app (rangeConormalModule B S hS j hj)).hom) ≫
        (restrictedFirstOrderExtension B S hS (rangeSubspace B S hS j hj) hZr ρr hr).inclSheafSets =
      (smallEtaleSetRestriction B S hS ρr.hom (isEtale_hom_of_iso B S hS _)).globalSectionMap
        ((thickeningToposHom B S hS (rangeSubspace B S hS j hj)).inverseImage.globalSectionMap
          (ringOneHom (structureRingSheaf B S hS (schemeSpace T')) ≫
            (moduleSheafFunctor (structureRingSheaf B S hS (schemeSpace T'))).map
              (unitModuleMul B S hS (schemeSpace T')
                (globalFunctionsOfMap (𝟙 (schemeSpace T')) c.1)))) :=
  (congrArg (fun σ : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
      restrictedConormalModule B S hS (rangeSubspace B S hS j hj) ρr =>
    ringOneHom (structureRingSheaf B S hS U) ≫
      (moduleSheafFunctor (structureRingSheaf B S hS U)).map σ ≫
        (restrictedFirstOrderExtension B S hS (rangeSubspace B S hS j hj) hZr ρr hr).inclSheafSets)
  (modulePullbackGlobalSection_rangeConormalSection_comp_modulePullbackIsoEtaleRestrictionModule_hom
      B S hS j hj ρr c)).trans
    (ringOneHom_comp_map_comp_restrictedFirstOrderExtension_inclSheafSets B S hS
      (rangeSubspace B S hS j hj) hZr ρr hr (rangeIdealSection B S hS j hj c)
      (rangeIdealSection_comp_ι B S hS j hj c))

end Range

end AlgebraicGeometry.Space

end
