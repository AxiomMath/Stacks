module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSectionSets

/-!
# The pullback of a global function, on underlying sheaves of sets

For a morphism `g : X ⟶ T` from an algebraic space to an object of the site and a global
function `a ∈ Γ(T, 𝒪_T)`, multiplication by the pulled-back function
`AlgebraicGeometry.Space.globalFunctionsOfMap g a` is the pullback along `g` of multiplication by
`a`, followed by `g^*𝒪_T ≅ 𝒪_X`. On underlying sheaves of sets, its global section `g^♯a` is
therefore the image along `g⁻¹` of the global section `a` of `𝒪_T`, followed by the structure map
`g^♯ : g⁻¹𝒪_T ⟶ 𝒪_X`. This is how the functions of the base of a deformation are read in its
structure sheaf in the proof of Stacks 0D1K.

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `modulePullbackGlobalSection_unitModuleMul_comp_structureModulePullbackMap`: multiplication
  by `g^♯a` is the pullback along `g` of multiplication by `a`, followed by `g^*𝒪_T ≅ 𝒪_X`.
* `ringOneHom_comp_map_unitModuleMul_globalFunctionsOfMap`: on underlying sheaves of sets, the
  global section `g^♯a` is the image along `g⁻¹` of `a`, followed by `g^♯ : g⁻¹𝒪_T ⟶ 𝒪_X`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}

/-- **Multiplication by a pulled-back function is the pullback of multiplication**: for
`g : X ⟶ T` and `a ∈ Γ(T, 𝒪_T)`, the pullback along `g` of the section `a` of `𝒪_T`, followed by
`g^*𝒪_T ≅ 𝒪_X`, is multiplication by `g^♯a`. -/
theorem modulePullbackGlobalSection_unitModuleMul_comp_structureModulePullbackMap
    (g : X ⟶ schemeSpace T) (a : baseRing B S hS T) :
    modulePullbackGlobalSection B S hS g
        (unitModuleMul B S hS (schemeSpace T) (globalFunctionsOfMap (𝟙 (schemeSpace T)) a)) ≫
        structureModulePullbackMap B S hS g =
      unitModuleMul B S hS X (globalFunctionsOfMap g a) := by
  have h := modulePullbackUnitIso_inv_comp_map_unitModuleMul B S hS g a
  refine (congrArg (modulePullbackGlobalSection B S hS g
    (unitModuleMul B S hS (schemeSpace T) (globalFunctionsOfMap (𝟙 (schemeSpace T)) a)) ≫ ·)
    (structureModulePullbackMap_eq_modulePullbackUnitIso_hom B S hS g)).trans ?_
  refine (congrArg (· ≫ (modulePullbackUnitIso B S hS g).hom) h).trans ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (modulePullbackUnitIso B S hS g).inv_hom_id).trans (Category.comp_id _))

/-- **The global section `g^♯a` on underlying sheaves of sets**: for `g : X ⟶ T` and
`a ∈ Γ(T, 𝒪_T)`, the unit section followed by multiplication by `g^♯a` is the image along `g⁻¹`
of the global section `a` of `𝒪_T`, followed by `g^♯ : g⁻¹𝒪_T ⟶ 𝒪_X`. -/
theorem ringOneHom_comp_map_unitModuleMul_globalFunctionsOfMap (g : X ⟶ schemeSpace T)
    (a : baseRing B S hS T) :
    ringOneHom (structureRingSheaf B S hS X) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (unitModuleMul B S hS X (globalFunctionsOfMap g a)) =
      (smallEtaleRingedToposModulesHom B S hS g).toToposHom.inverseImage.globalSectionMap
          (ringOneHom (structureRingSheaf B S hS (schemeSpace T)) ≫
            (moduleSheafFunctor (structureRingSheaf B S hS (schemeSpace T))).map
              (unitModuleMul B S hS (schemeSpace T)
                (globalFunctionsOfMap (𝟙 (schemeSpace T)) a))) ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
          (smallEtaleRingedToposModulesHom B S hS g).fSharpInverseImage := by
  refine (congrArg (fun m : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X) =>
      ringOneHom (structureRingSheaf B S hS X) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS X)).map m)
    (modulePullbackGlobalSection_unitModuleMul_comp_structureModulePullbackMap
      B S hS g a).symm).trans ?_
  exact ringOneHom_comp_map_modulePullbackGlobalSection_comp_structureModulePullbackMap B S hS g _

end AlgebraicGeometry.Space

end
