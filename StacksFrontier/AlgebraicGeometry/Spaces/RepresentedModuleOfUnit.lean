module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedChartRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite

/-!
# The associated module of the structure sheaf of a scheme, on the small étale site

For an object `Z` of the big fppf site with underlying scheme `Z₀`, the associated module
`(𝒪_{Z₀})ᵃ` read on the small étale site of the algebraic space `h_Z`
(`AlgebraicGeometry.Space.representedModuleOf`) is the structure sheaf of `h_Z`.

## Main definitions

* `AlgebraicGeometry.Space.representedSmallEtaleModuleUnitIso`: the comparison equivalence of
  module categories carries the unit to the unit (definitionally).
* `AlgebraicGeometry.Space.representedModuleOfUnitIso`: `(𝒪_{Z₀})ᵃ ≅ 𝒪_{h_Z}`.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison equivalence of module categories
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` carries the structure sheaf to
the structure sheaf (definitionally). -/
def representedSmallEtaleModuleUnitIso (Z : BigFppfOver B S hS) :
    (representedSmallEtaleModuleEquivalence B S hS Z).functor.obj
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS Z)) ≅
      SheafOfModules.unit (representedStructureRingSheaf B S hS Z) :=
  Iso.refl _

/-- **The associated module of the structure sheaf is the structure sheaf**: the associated
module `(𝒪_{Z₀})ᵃ`, read on the small étale site of `h_Z`, is isomorphic to the structure sheaf
`𝒪_{h_Z}`. -/
def representedModuleOfUnitIso (Z : BigFppfOver B S hS) :
    representedModuleOf B S hS Z
        (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj Z).ringCatSheaf) ≅
      SheafOfModules.unit (structureRingSheaf B S hS (schemeSpace Z)) :=
  (representedSmallEtaleModuleEquivalence B S hS Z).functor.mapIso
      (@asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u}
        (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj Z) Z.left.property))
        (_root_.AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj Z) Z.left.property)) ≪≫
    representedSmallEtaleModuleUnitIso B S hS Z

end AlgebraicGeometry.Space

end
