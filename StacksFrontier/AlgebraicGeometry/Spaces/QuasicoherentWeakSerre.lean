module

public import StacksFrontier.AlgebraicGeometry.Spaces.CommonLemmas
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurjFromChart

/-!
# Quasi-coherent modules on an algebraic space form a weak Serre subcategory

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  The
quasi-coherent `𝒪_F`-modules on the small étale site of `F`, with sections in the universe of the
schemes, form a weak Serre subcategory of all `𝒪_F`-modules (Stacks 0754): they contain `0` and
are closed under isomorphisms, kernels, cokernels and extensions.  Consequently `D_QCoh(𝒪_F)` is
a triangulated subcategory of `D(𝒪_F)`.

## Main results

* `AlgebraicGeometry.Space.instIsClosedUnderExtensionsQuasicoherentSheavesSchemeUniverse`: the
  quasi-coherent modules, with sections in the universe of the schemes, are closed under
  extensions (Stacks 03M1).
* `AlgebraicGeometry.Space.isTriangulated_quasicoherentDerivedCategory`: the property of having
  quasi-coherent cohomology sheaves is triangulated, so that
  `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` is a triangulated subcategory.

## Implementation notes

The module universe is `u`, the universe of the structure rings, where the two sheafification
binders of `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` are instances. The local
instance `SheafOfModules.instAbelian` at priority 5000 makes instance search find the abelian
structure directly: through `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` it stalls on a
universe constraint.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 06UQ](https://stacks.math.columbia.edu/tag/06UQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The quasi-coherent modules on the small étale site of `F`, with sections in the universe of
the schemes, are closed under extensions (Stacks 03M1). -/
instance instIsClosedUnderExtensionsQuasicoherentSheavesSchemeUniverse :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderExtensions :=
  isClosedUnderExtensions_quasicoherentSheaves B S hS ⟨F, hF⟩

/-- The quasi-coherent modules on the small étale site of `F`, with sections in the universe of
the schemes, are closed under kernels (Stacks 03M1). -/
instance isClosedUnderKernels_quasicoherentSheaves_schemeUniverse' :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderKernels :=
  isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF

/-- The quasi-coherent modules on the small étale site of `F`, with sections in the universe of
the schemes, are closed under cokernels (Stacks 03M1). -/
instance isClosedUnderCokernels_quasicoherentSheaves' :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels :=
  isClosedUnderCokernels_quasicoherentSheaves B S hS F hF

/-- `D_QCoh(𝒪_F)` is a triangulated subcategory of `D(𝒪_F)` (Stacks 06UQ). -/
instance isTriangulated_quasicoherentDerivedCategory :
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)))).IsTriangulated := by
  set P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
  exact DerivedCategoryB.derivedCategoryB_isTriangulated P
    ⟨inferInstance, P.exists_prop_of_isWeakSerreClass, fun E h₀ h₁ h₃ h₄ =>
      ObjectProperty.prop_mid_of_exact₄ P.prop_obj₂_of_exact E.zero₀ E.zero₁ E.zero₂
        E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄⟩

end AlgebraicGeometry.Space

end
