module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartSchemeBourbakiTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeIdEtaleChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor

/-!
# Chart restriction of a tensor product with an inverse image

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `𝓕` be a quasi-coherent
`𝒪_X`-module and `𝓖` a quasi-coherent `𝒪_Y`-module, and let `d` be a commuting square of étale
scheme charts over `f`, with source chart `U`, target chart `V` and vertical morphism of chart
schemes `q`.  This file proves the comparison

`(𝓕 ⊗_{𝒪_X} f^*𝓖)|_U ≅ 𝓕|_U ⊗_{𝒪_U} q^*(𝓖|_V)`.

## Main results

* `AlgebraicGeometry.Space.nonempty_restrictToChart_tensor_modulePullback_chartDiagram`: the
  comparison above, for quasi-coherent `𝓕` and `𝓖` on a chart diagram.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 0CV1](https://stacks.math.columbia.edu/tag/0CV1)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- Let `d` be a commuting square of étale scheme charts over `f : X ⟶ Y`, with vertical morphism
of chart schemes `q`, and let `𝓕` and `𝓖` be quasi-coherent. Then

`(𝓕 ⊗_{𝒪_X} f^*𝓖)|_U ≅ 𝓕|_U ⊗_{𝒪_U} q^*(𝓖|_V)`. -/
theorem nonempty_restrictToChart_tensor_modulePullback_chartDiagram (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hF : F.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite)
    (hFG : (F ⊗ (modulePullback B S hS f).obj G).IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    Nonempty (restrictToChart B S hS X.2 (F ⊗ (modulePullback B S hS f).obj G) d.U ≅
      chartDiagramTensorPullback B S hS f F G d) := by
  have hcomm : (chartToSpace B S hS X d.U ≫ f : chartSpace B S hS X d.U ⟶ Y) =
      representedSpaceMap B S hS d.g ≫ chartToSpace B S hS Y d.V :=
    ObjectProperty.hom_ext _ d.comm
  have hPF : ((modulePullback B S hS (chartToSpace B S hS X d.U)).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (chartToSpace B S hS X d.U) F hF
  have hPG : ((modulePullback B S hS (chartToSpace B S hS Y d.V)).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (chartToSpace B S hS Y d.V) G hG
  have hQG : ((modulePullback B S hS (representedSpaceMap B S hS d.g)).obj
      ((modulePullback B S hS (chartToSpace B S hS Y d.V)).obj G)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (representedSpaceMap B S hS d.g) _ hPG
  have e2 : (modulePullback B S hS (chartToSpace B S hS X d.U)).obj
        (F ⊗ (modulePullback B S hS f).obj G) ≅
      (modulePullback B S hS (chartToSpace B S hS X d.U)).obj F ⊗
        (modulePullback B S hS (representedSpaceMap B S hS d.g)).obj
          ((modulePullback B S hS (chartToSpace B S hS Y d.V)).obj G) :=
    modulePullbackTensorCompIso B S hS (chartToSpace B S hS X d.U) f F G ≪≫
      whiskerLeftIso _
        (eqToIso (congrArg
            (fun k : chartSpace B S hS X d.U ⟶ Y => (modulePullback B S hS k).obj G) hcomm) ≪≫
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS d.g)
            (chartToSpace B S hS Y d.V)).app G).symm)
  obtain ⟨e4⟩ := nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent d.g
    ((modulePullback B S hS (chartToSpace B S hS Y d.V)).obj G) hPG
  let tensorComparison :=
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((chartScheme d.U)).presheaf, ((chartScheme d.U)).IsSheaf⟩)).mapIso
      (Iso.prod (restrictToChartIsoChartSpaceIdEtaleChart B S hS X d.U F hF).symm
        (e4 ≪≫ (Scheme.Modules.pullback (chartDiagramSchemeMap B S hS f d)).mapIso
          (restrictToChartIsoChartSpaceIdEtaleChart B S hS Y d.V G hG).symm))
  refine ⟨restrictToChartIsoChartSpaceIdEtaleChart B S hS X d.U
      (F ⊗ (modulePullback B S hS f).obj G) hFG ≪≫
    (restrictToChartSchemeFunctor B S hS (chartSpace B S hS X d.U).1
      (chartSpace B S hS X d.U).2
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj d.U))).mapIso e2 ≪≫
    restrictToChartSchemeIdEtaleChartTensorIso B S hS
      ((SmallEtale.toOver B S hS X.1).obj d.U) _ _ hPF hQG ≪≫
    tensorComparison⟩

end AlgebraicGeometry.Space

end
