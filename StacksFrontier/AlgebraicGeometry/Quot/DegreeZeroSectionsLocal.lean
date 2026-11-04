module

public import StacksFrontier.AlgebraicGeometry.Quot.DegreeZeroSectionsDerived

/-!
# Restricting the degree-zero sections functor to the test schemes over an algebraic space

For a morphism `k : Y ⟶ X` of algebraic spaces and a complex `P` of `𝒪_X`-modules, the
degree-zero sections functor of `P`, restricted to the test schemes over `Y`, is the degree-zero
sections functor of the inverse image `k^*P`.  This is what reduces a statement about the
functor of Stacks 08JX, part (1), to a statement over the members of a covering of the base.

## Main definitions

* `AlgebraicGeometry.Space.degreeZeroSectionsPrecompIso`: the identification.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local irreducible] modulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The degree-zero sections functor of `P`, restricted to the test schemes over `Y`, is the
degree-zero sections functor of `k^*P`.** -/
def degreeZeroSectionsPrecompIso {X Y : AlgebraicSpaces B S hS} (k : Y ⟶ X)
    (P : CochainComplex (toposModules B S hS X) ℤ) :
    (CostructuredArrow.map k).op ⋙ degreeZeroSectionsFunctor (schemesOverCone X) P ≅
      degreeZeroSectionsFunctor (schemesOverCone Y)
        ((((toposModulePullbackData B S hS).pull k).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  (kerSectionsPrecompIso k (SheafOfModules.unit _) (P.fromOpcycles 0 1)).symm ≪≫
    (toposModulePullbackData B S hS).relKerIso (toposModulePullbackData_isCoherent B S hS)
      (schemesOverConeMap k) (modulePullbackUnitIsoTopos k).symm _ _
      (P.mapOpcyclesIsoOfPreservesCokernel ((toposModulePullbackData B S hS).pull k) (-1) 0
        (by norm_num))
      (Iso.refl _)
      (by
        rw [Iso.refl_hom, Category.comp_id, HomologicalComplex.mapOpcyclesIso_hom_fromOpcycles])

end AlgebraicGeometry.Space

end
