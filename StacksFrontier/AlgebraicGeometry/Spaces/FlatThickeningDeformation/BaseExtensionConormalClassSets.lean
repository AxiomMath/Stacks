module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalInverseImageGlobalSectionSets
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.IdealCompatibility
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationTensorExtensionGlobalSection

/-!
# The class of a section of the ideal of a thickening, in the middle term of its extension

For a first order thickening `Z ⊂ Y'` and a global section `s` of its ideal `𝓘`, the class
`i^*s` of `s` in the conormal module `𝒞_{Z/Y'}`, read in `t⁻¹𝒪_{Y'}` through the kernel
inclusion of the extension `0 → 𝒞 → t⁻¹𝒪_{Y'} → 𝒪_Z → 0` of the thickening
(`AlgebraicGeometry.Space.FlatThickeningDeformation.baseExtension`), is the inverse image of `s`
read as a function on `Y'`, on underlying sheaves of sets.

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1)

/-- **The class of a section of the ideal, read in `t⁻¹𝒪_{Y'}`**: for a global section `s` of
the ideal `𝓘` of `Z ⊂ Y'`, the image of its class `i^*s ∈ 𝒞` in the middle term of the extension
of the thickening is the inverse image along `i : Z ⟶ Y'` of `s`, read as a function on `Y'`,
on underlying sheaves of sets. -/
theorem ringOneHom_comp_map_modulePullbackGlobalSection_comp_inclSheafSets
    (s : SheafOfModules.unit (structureRingSheaf B S hS Y') ⟶
      (definingIdealSheaf B S hS Y' Z).toSheafOfModules) :
    ringOneHom (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map
          (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS Y' Z) s) ≫
        (baseExtension hZ).inclSheafSets =
      (thickeningToposHom B S hS Z).inverseImage.globalSectionMap
        (ringOneHom (structureRingSheaf B S hS Y') ≫
          (moduleSheafFunctor (structureRingSheaf B S hS Y')).map
            (s ≫ (definingIdealSheaf B S hS Y' Z).ι)) := by
  have h := ringOneHom_comp_map_conormalInverseImageι_modulePullbackGlobalSection B S hS Z hZ s
  refine Eq.trans ?_ h
  exact Deformation.AlgebraExtension.ringOneHom_comp_map_comp_inclSheafSets_eq_of_incl
    (baseExtension hZ) (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS Y' Z) s)
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS Y' Z))
    (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS Y' Z) s)
    (conormalInverseImageι B S hS Z hZ)
    (fun U => firstOrderAlgebraExtension_incl Z hZ (𝟙 Y') _)

end AlgebraicGeometry.Space.FlatThickeningDeformation
