module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages

/-!
# `R¹f_*𝒪_X` of a family of curves as a cohomology sheaf of `Rf_*𝒪_X`

For a family of curves `f : X → S`, the first cohomology sheaf of the derived direct image
`Rf_*(𝒪_X[0])` (Stacks 0E6B, 0CTM) is the module `AlgebraicGeometry.CurveFamily.firstDirectImage`,
the first right derived functor of the direct image of modules. The derived categories are those
of the standard model `HasDerivedCategory.standard`.

## Main definitions

* `AlgebraicGeometry.CurveFamily.homologyDerivedPushforwardIsoFirstHigherDirectImage`:
  `H¹(Rf_*(𝒪_X[0])) ≅ R¹f_*𝒪_X`, with `Rf_*` the derived direct image
  `AlgebraicGeometry.Space.smallEtaleDerivedModulePushforward` of the morphism of small étale
  ringed topoi.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **`H¹(Rf_*(𝒪_X[0])) ≅ R¹f_*𝒪_X` for a family of curves.** The first cohomology sheaf of the
derived direct image of the structure sheaf, placed in degree `0`, is the first higher direct
image of the structure sheaf. -/
def homologyDerivedPushforwardIsoFirstHigherDirectImage (X : CurveFamily B hZ) :
    letI := HasDerivedCategory.standard
      (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    letI := HasDerivedCategory.standard
      (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
    (DerivedCategory.homologyFunctor
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
        1).obj
      ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
        ((DerivedCategory.singleFunctor
          (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
          (Space.structureSheafModule B integerBase hZ X.total))) ≅
      (X.firstDirectImage B hZ) :=
  letI := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
  letI := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
  (DerivedCategory.homologyFunctor _ 1).mapIso
      ((Space.smallEtaleDerivedModulePushforwardIso B integerBase hZ X.toBase).app _) ≪≫
    Space.homologyDerivedModulePushforwardSingleIso B integerBase hZ X.toBase
      (Space.structureSheafModule B integerBase hZ X.total) 0 1 1 (by norm_num)

end CurveFamily

end AlgebraicGeometry

end
