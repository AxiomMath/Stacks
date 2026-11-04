module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartNonvanishingGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeIdEtaleChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The restriction to an étale chart of the tensor powers of a module

Let `X` be an algebraic space and `L` a quasi-coherent `𝒪_X`-module. The tensor powers
`L^{⊗ n}` of `L` for the tensor product of `𝒪_X`-modules
(`AlgebraicGeometry.Space.modulesMonoidalCategory`) are quasi-coherent, and their restriction to
the scheme of an étale chart `V` of `X` is the `n`-th tensor power of the restriction `L|_V`:

`(L^{⊗ n})|_V ≅ (L|_V)^{⊗ n}`.

This is the identification of the powers of `L` on `X` with the powers of its pullback to a
chart used in the proof of [Stacks, Tag 0D35].

## Main results

* `AlgebraicGeometry.Space.restrictToChartTensorIso`: the restriction of a tensor product of
  quasi-coherent modules is the tensor product of the restrictions.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_natTensorPow`: the tensor powers of a
  quasi-coherent module are quasi-coherent.
* `AlgebraicGeometry.Space.chartRestrictionSchemeModuleNatTensorPowIso`: the restriction of the
  `n`-th tensor power is the `n`-th tensor power of the restriction, in the sense of
  `Stacks.Ample.tensorPowModule`.

## References

* [Stacks Project, Tag 0D35](https://stacks.math.columbia.edu/tag/0D35)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The restriction of a tensor product of quasi-coherent modules to an étale chart is the
tensor product of the restrictions.** The restriction to a chart is the identity-chart
restriction of the inverse image to the chart space
(`AlgebraicGeometry.Space.restrictToChartIsoChartSpaceIdEtaleChart`); the inverse image is
monoidal (`AlgebraicGeometry.Space.modulePullbackTensorIso`), and the identity-chart restriction
is monoidal on quasi-coherent modules
(`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartTensorIso`). -/
noncomputable def restrictToChartTensorIso (A : SmallEtale B S hS X.1)
    (F G : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite] :
    chartRestrictionSchemeModule B S hS X (F ⊗ G) A ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(chartScheme A).toRingedSpace.presheaf, (chartScheme A).toRingedSpace.IsSheaf⟩).obj
          (chartRestrictionSchemeModule B S hS X F A)).obj
            (chartRestrictionSchemeModule B S hS X G A) := by
  have hPF : ((modulePullback B S hS (chartToSpace B S hS X A)).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (chartToSpace B S hS X A) F inferInstance
  have hPG : ((modulePullback B S hS (chartToSpace B S hS X A)).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (chartToSpace B S hS X A) G inferInstance
  have hFG : (F ⊗ G).IsQuasicoherentOnSite := isQuasicoherentOnSite_tensorObj B S hS X.1 X.2 F G
  let e₁ := restrictToChartIsoChartSpaceIdEtaleChart B S hS X A (F ⊗ G) hFG
  let e₂ := (restrictToChartSchemeFunctor B S hS (chartSpace B S hS X A).1
      (chartSpace B S hS X A).2
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj A))).mapIso
        (modulePullbackTensorIso B S hS (chartToSpace B S hS X A) F G)
  let e₃ := restrictToChartSchemeIdEtaleChartTensorIso B S hS
    ((SmallEtale.toOver B S hS X.1).obj A) _ _ hPF hPG
  let e₄ := (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(chartScheme A).toRingedSpace.presheaf, (chartScheme A).toRingedSpace.IsSheaf⟩)).mapIso
      (Iso.prod (restrictToChartIsoChartSpaceIdEtaleChart B S hS X A F inferInstance).symm
        (restrictToChartIsoChartSpaceIdEtaleChart B S hS X A G inferInstance).symm)
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- **The tensor powers of a quasi-coherent module are quasi-coherent.** -/
theorem isQuasicoherentOnSite_natTensorPow (L : Modules.{u, u} B S hS X.1 X.2)
    [L.IsQuasicoherentOnSite] :
    ∀ n : ℕ, (Stacks.TensorPowers.natTensorPow L n).IsQuasicoherentOnSite
  | 0 => SheafOfModules.isQuasicoherentOnSite_unit _
  | n + 1 =>
    have := isQuasicoherentOnSite_natTensorPow L n
    isQuasicoherentOnSite_tensorObj B S hS X.1 X.2 _ L

/-- **The restriction of the `n`-th tensor power of a quasi-coherent module to an étale chart is
the `n`-th tensor power of the restriction**, for the tensor powers
`Stacks.Ample.tensorPowModule` of the invertible module `L|_V` of the chart's scheme. -/
noncomputable def chartRestrictionSchemeModuleNatTensorPowIso (A : SmallEtale B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2) [L.IsQuasicoherentOnSite]
    [Stacks.Ample.IsInvertibleModule (chartScheme A) (chartRestrictionSchemeModule B S hS X L A)] :
    ∀ n : ℕ, chartRestrictionSchemeModule B S hS X (Stacks.TensorPowers.natTensorPow L n) A ≅
      Stacks.Ample.tensorPowModule (chartScheme A) (chartRestrictionSchemeModule B S hS X L A)
        (n : ℤ)
  | 0 =>
    eqToIso (restrictToChart_eq_restrictToChartScheme B S hS X.2 _ A) ≪≫
      restrictToChartSchemeUnitIso B S hS X.1 X.2 A ≪≫
      (Stacks.Ample.tensorPowModuleZeroIso (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A)).symm
  | n + 1 => by
    haveI := isQuasicoherentOnSite_natTensorPow B S hS X L n
    let T := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(chartScheme A).toRingedSpace.presheaf, (chartScheme A).toRingedSpace.IsSheaf⟩
    let e₁ := restrictToChartTensorIso B S hS X A (Stacks.TensorPowers.natTensorPow L n) L
    let e₂ := (T.mapIso (chartRestrictionSchemeModuleNatTensorPowIso A L n)).app
      (chartRestrictionSchemeModule B S hS X L A)
    let e₃ := (AlgebraicGeometry.SheafOfModules.tensorIso (chartScheme A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme A))
      (Stacks.Ample.tensorPowModule (chartScheme A) (chartRestrictionSchemeModule B S hS X L A) n)
      (chartRestrictionSchemeModule B S hS X L A)).symm
    let e₄ := (AlgebraicGeometry.SheafOfModules.tensorPowSuccIso (chartScheme A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme A))
      (chartRestrictionSchemeModule B S hS X L A) (n : ℤ)).symm
    let e₅ := eqToIso (congrArg (Stacks.Ample.tensorPowModule (chartScheme A)
      (chartRestrictionSchemeModule B S hS X L A))
      (show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; rfl))
    exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅

end AlgebraicGeometry.Space

end
