module

public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageBaseChangeAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMapHorizontal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated

/-!
# Stacks 073K, part (1), over affine bases, in the bounded below derived category

For the cartesian square of **Stacks 073J** with `Y` and `Y'` affine, `g` flat and `f`
quasi-compact and quasi-separated, the base change map `g^*Rf_* ⟶ Rf'_*(g')^*` of
**Stacks 0736**, `AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap`, is invertible at a
quasi-coherent `𝓕` placed in degree zero.

## Main results

* `Space.BaseChangeDiagram.isIso_toposModuleDerivedBaseChangeMap_app_single_of_affine`:
  the base change map of **Stacks 0736** is invertible at `𝓕[0]`.

## Implementation notes

The cohomology of the morphism of complexes is invertible in every degree by
`AlgebraicGeometry.Space.BaseChangeDiagram.isIso_homologyMap_baseChange_affine`, which is stated
for the base change map at the modules development's direct image
`AlgebraicGeometry.Space.modulePushforward`. The base change map of **Stacks 0736** is seated at
`AlgebraicGeometry.Space.toposModulePushforward`; the two degree-zero base change maps differ by
the comparisons `AlgebraicGeometry.Space.modulePushforwardIso` at `f` and `f'`
(`AlgebraicGeometry.Space.toposModuleBaseChangeMap_eq_moduleBaseChangeMap`), and the criterion
`Stacks.Cohomology.RightDerivedCoEdge.isIso_derived_app_single_of_quasiIso_baseChangeComplexMap`
carries the quasi-isomorphism across them and concludes.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace BaseChangeDiagram

variable (D : BaseChangeDiagram B S hS)

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] spaceModulesAbelianWrittenOut
attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules
attribute [local instance] degreewiseBaseChangeHasDerivedCategory

/-- **Stacks 073K, part (1), over affine bases.**  For a cartesian square of algebraic spaces
with `Y` and `Y'` affine — witnessed by étale charts with invertible structure morphism and affine
underlying scheme — `g` flat and `f` quasi-compact and quasi-separated, the base change map
`g^*Rf_* ⟶ Rf'_*(g')^*` of **Stacks 0736** is invertible at the quasi-coherent `𝓕` placed in
degree zero. -/
theorem isIso_toposModuleDerivedBaseChangeMap_app_single_of_affine
    [PreservesFiniteLimits (modulePullback B S hS D.g)]
    [PreservesFiniteColimits (modulePullback B S hS D.g)]
    (hg : IsFlat B S hS D.g.hom)
    (hqc : IsQuasiCompact B S hS D.f.hom) (hqs : IsQuasiSeparated B S hS D.f.hom)
    (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom] [IsAffine (chartScheme V₀)]
    (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom] [IsAffine (chartScheme V₀')] :
    IsIso ((toposModuleDerivedBaseChangeMap D.f D.g D.f' D.g' D.isPullback.w).app
      ((DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS D.X.1 D.X.2) 0).obj D.F)) := by
  have := D.preservesFiniteLimits_pullback_g' hg
  have := preservesFiniteColimits_modulePullback_smallEtale B S hS D.g'
  have := D.quasiIso_resolutionComparison hg
  have hq : QuasiIso (Stacks.Cohomology.RightDerivedCoEdge.baseChangeComplexMap
      (modulePullbackAdjunction B S hS D.g) (modulePullbackAdjunction B S hS D.g')
      (modulePushforwardSquareComparisonIso D.f D.g D.f' D.g' D.isPullback.w)
      (injectiveResolution D.F).cocomplex (D.resolutionComparison hg)) :=
    ⟨fun n ↦ (quasiIsoAt_iff_isIso_homologyMap _ n).2
      (D.isIso_homologyMap_baseChange_affine (BigFppfSite.contains_terminal B) hg hqc hqs
        V₀ V₀' n)⟩
  exact
    Stacks.Cohomology.RightDerivedCoEdge.isIso_derived_app_single_of_quasiIso_baseChangeComplexMap
      (toposModulePushforward D.f) (toposModulePushforward D.f') (modulePullback B S hS D.g)
      (modulePullback B S hS D.g') (toposModuleBaseChangeMap D.f D.g D.f' D.g' D.isPullback.w)
      (asIso (modulePullback B S hS D.g).rightDerivedFunctorPlusUnith)
      (modulePullbackAdjunction B S hS D.g) (modulePullbackAdjunction B S hS D.g')
      (modulePushforwardSquareComparisonIso D.f D.g D.f' D.g' D.isPullback.w)
      (toposModulePushforwardIsoModulePushforward D.f)
      (toposModulePushforwardIsoModulePushforward D.f')
      (by rw [toposModuleBaseChangeMap_eq_moduleBaseChangeMap, moduleBaseChangeMap_eq_mate]; rfl)
      D.F (injectiveResolution D.pulledBack) (D.resolutionComparison hg) hq

end BaseChangeDiagram

end AlgebraicGeometry.Space

end
