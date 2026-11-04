module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraExtensionPushoutQcqs

/-!
# The cohomology sheaves of the naive cotangent complex on the model, back on `X`

Let `f : X ⟶ Y` be a morphism of algebraic spaces. The naive cotangent complex `NL_{X/Y}` used
for the deformation classes of [Stacks Project, Tag 0D1K] lives on the model of the small étale
site of `X` (`AlgebraicGeometry.Space.modelNaiveCotangentComplex`). Its cohomology sheaves,
carried back to `X` by the Comparison Lemma, are the `𝒪_X`-modules
`AlgebraicGeometry.Space.modelNaiveCotangentHomology`; they are the cohomology objects of
`NL_{X/Y}` in any model of the derived category of the model
(`AlgebraicGeometry.Space.modelNaiveCotangentHomologyIso`), and they are quasi-coherent
([Stacks Project, Tag 0D0Y], through
`AlgebraicGeometry.Space.qcohDerivedProp_modelNaiveCotangentComplex`).

## Main definitions

* `AlgebraicGeometry.Space.modelNaiveCotangentHomology`
* `AlgebraicGeometry.Space.modelNaiveCotangentHomologyIso`

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modelNaiveCotangentHomology`

## References

* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y)

/-- **The `i`-th cohomology sheaf of `NL_{X/Y}` on the model, carried back to `X`.** -/
abbrev modelNaiveCotangentHomology (i : ℤ) : Modules.{u, u} B S hS X.1 X.2 :=
  (modelModulesEquiv B S hS X).inverse.obj ((modelNaiveCotangentComplex B S hS f).homology i)

/-- **The cohomology objects of `NL_{X/Y}` in the derived category of the model** are the
restrictions of `AlgebraicGeometry.Space.modelNaiveCotangentHomology`, for any model of the
derived category. -/
def modelNaiveCotangentHomologyIso [HasDerivedCategory.{w} (RestrictedModelModules B S hS X)]
    (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj
        (DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS f)) ≅
      (modelModulesEquiv B S hS X).functor.obj (modelNaiveCotangentHomology B S hS f i) :=
  (DerivedCategory.homologyFunctorFactors _ i).app _ ≪≫
    ((modelModulesEquiv B S hS X).counitIso.app _).symm

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
attribute [local instance] hasWeakSheafify_commRingCat_smallEtale

/-- **The cohomology sheaves of `NL_{X/Y}` on the model are quasi-coherent on `X`**
([Stacks Project, Tag 0D0Y]). -/
theorem isQuasicoherentOnSite_modelNaiveCotangentHomology (i : ℤ) :
    (modelNaiveCotangentHomology B S hS f i).IsQuasicoherentOnSite := by
  let : HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2) := HasDerivedCategory.standard _
  have h := qcohDerivedProp_modelNaiveCotangentComplex B S hS f i
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((modelModulesEquiv B S hS X).inverse.mapDerivedCategoryCompHomologyFunctorIso i).app _ ≪≫
      (modelModulesEquiv B S hS X).inverse.mapIso
        ((DerivedCategory.homologyFunctorFactors _ i).app _)) h

end AlgebraicGeometry.Space

end
