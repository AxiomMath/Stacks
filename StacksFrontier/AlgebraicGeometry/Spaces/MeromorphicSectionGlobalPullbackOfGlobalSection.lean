module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackValue
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionOfGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSheafModuleMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue

/-!
# The pullback of the meromorphic section of a global section

Let `f : X ⟶ Y` be a morphism of algebraic spaces along which meromorphic sections pull back
(Stacks 0EN8), let `M` be an `𝒪_Y`-module and let `σ` be a global section of `M`. A global
section is a meromorphic section (`AlgebraicGeometry.Space.globalSectionMeromorphic`), and both
global sections and meromorphic sections pull back along `f`. This file proves that the two
pullbacks agree:

`f^*(σ as a meromorphic section) = (f^*σ) as a meromorphic section`.

Over a commuting square `d` of étale scheme charts the left-hand side is the chartwise rule
`a ⊗ m ↦ f^♯a ⊗ f^*m` applied to `1 ⊗ σ|_{d.V}`
(`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_chartDiagram`), which is
`1 ⊗ (f^*σ)|_{d.U}` because the chartwise pullback of a section of `M` is the value of the
pulled-back global section (`AlgebraicGeometry.Space.modulePullbackSections_val`); the charts of
such squares cover every chart of `X`.

The meromorphic section of a global section is also natural in the module: a morphism
`φ : M ⟶ N` carries the meromorphic section of `σ` to that of `φ(σ)`.

## Main results

* `AlgebraicGeometry.Space.pullbackMeromorphicSection_globalSectionMeromorphic`: the identity.
* `AlgebraicGeometry.Space.sectionsMap_meromorphicSectionSheafMap_globalSectionMeromorphic`:
  naturality in the module.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The meromorphic section of a global section is natural in the module**: a morphism
`φ : M ⟶ N` of `𝒪_F`-modules carries the meromorphic section of a global section `σ` of `M` to
the meromorphic section of `φ(σ)`. Over a chart both are `1 ⊗ φ(σ|_V)`
(`AlgebraicGeometry.Space.meromorphicSectionSheafMap_toMeromorphicSectionSheaf`). -/
theorem sectionsMap_meromorphicSectionSheafMap_globalSectionMeromorphic
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N) (σ : M.sections) :
    SheafOfModules.sectionsMap (meromorphicSectionSheafMap B S hS F hF φ)
        (globalSectionMeromorphic B S hS hF M σ) =
      globalSectionMeromorphic B S hS hF N (SheafOfModules.sectionsMap φ σ) := by
  refine PresheafOfModules.sections_ext _ _ fun V => ?_
  induction V using Opposite.rec with | op V => ?_
  change ((meromorphicSectionSheafMap B S hS F hF φ).val.app (op V)).hom
      ((globalSectionMeromorphic B S hS hF M σ).eval (op V)) =
    (globalSectionMeromorphic B S hS hF N (SheafOfModules.sectionsMap φ σ)).eval (op V)
  rw [globalSectionMeromorphic_eval, globalSectionMeromorphic_eval]
  refine (meromorphicSectionSheafMap_toMeromorphicSectionSheaf B S hS F hF φ V _).trans ?_
  rw [meromorphicSectionModuleMap_tmul]
  rfl

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hf : PullbacksMeromorphicSections B S hS f.hom)

/-- The pullback of the meromorphic section of a global section, over the chart of `X` of a
commuting square of étale scheme charts, is the meromorphic section of the pulled-back global
section there. -/
theorem pullbackMeromorphicSection_globalSectionMeromorphic_eval_chartDiagram (σ : M.sections)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (pullbackMeromorphicSection B S hS f M hf
        (globalSectionMeromorphic B S hS Y.2 M σ)).eval (op d.U) =
      (globalSectionMeromorphic B S hS X.2 ((modulePullback B S hS f).obj M)
        (modulePullbackSections B S hS f M σ)).eval (op d.U) := by
  rw [pullbackMeromorphicSection_eval_chartDiagram B S hS f M hf _ d _
      (globalSectionMeromorphic_eval B S hS Y.2 M σ d.V),
    chartPullbackMeromorphicSectionsSheaf_tmul, map_one, globalSectionMeromorphic_eval,
    modulePullbackChartFMap_app]
  congr 2
  exact (modulePullbackSections_val B S hS f M σ d).symm

/-- **The pullback of the meromorphic section of a global section is the meromorphic section of
the pulled-back global section**: `f^*(σ) = (f^*σ)` in `Γ(X, 𝒦_X(f^*M))`, for a global section
`σ` of `M`. -/
theorem pullbackMeromorphicSection_globalSectionMeromorphic (σ : M.sections) :
    pullbackMeromorphicSection B S hS f M hf (globalSectionMeromorphic B S hS Y.2 M σ) =
      globalSectionMeromorphic B S hS X.2 ((modulePullback B S hS f).obj M)
        (modulePullbackSections B S hS f M σ) := by
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  obtain ⟨I, W, a, d, hdU, -, -, hcov⟩ := exists_affine_chartDiagram_ofArrows B S hS f U.unop
  refine meromorphicSectionSheaf_eq_of_cover B S hS X.1 X.2
    ((modulePullback B S hS f).obj M) U.unop W a hcov _ _ fun i => ?_
  rw [PresheafOfModules.sections_property _ (a i).op,
    PresheafOfModules.sections_property _ (a i).op]
  have key := pullbackMeromorphicSection_globalSectionMeromorphic_eval_chartDiagram B S hS f M hf
    σ (d i)
  rw [hdU i] at key
  exact key

end AlgebraicGeometry.Space

end
